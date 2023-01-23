module Typechecker (typecheck) where

import AbsLatte
import Data.Map
import Data.Set

showPos :: BNFC'Position -> ShowS
showPos pos = case pos of
    Just (line, col) -> showString "(line:" . shows line . showString ", col:" . shows col . showString ")"
    Nothing -> id

--------------------- GRAF WYWOŁAŃ FUNKCJI --------------------------------

type Calls = Map Ident (Set Ident)

--------------------- ŚRODOWISKA --------------------------------

type VType = Map Ident Type
type FType = Map Ident (Type, [Arg])
type IType = Map Ident (Type, [Arg])

--------------------- PORÓWNYWANIE TYPÓW --------------------------------

eqTypes :: Type -> Type -> Bool
eqTypes t1 t2 = case (t1, t2) of
    (Int _, Int _) -> True
    (Str _, Str _) -> True
    (Bool _, Bool _) -> True
    (Void _, Void _) -> True
    (_, _) -> False

--------------------- TYPECKECK ARGUMENTÓW WYWOŁANIA FUNKCJI --------------------------------

checkArgs :: BNFC'Position -> (Type, [Arg]) -> [Expr] -> VType -> FType -> IType -> Maybe Ident -> Calls -> Either String (Type, Calls)
checkArgs pos (ft, args) exps gV gF gI inl calls =
    case (args, exps) of
        ([], []) -> Right (ft, calls)
        (h : _, []) -> Left (showPos pos ": not enough arguments")
        ([], h : _) -> Left (showPos pos ": too many arguments")
        ((Arg _ argt _) : argRest, exp : expRest) ->
            case checkE exp gV gF gI inl calls of
                Left error -> Left error
                Right (t, calls') ->
                    if eqTypes t argt then checkArgs pos (ft, argRest) expRest gV gF gI inl calls'
                    else Left (showPos (hasPosition exp) ": wrong type of argument")

--------------------- TYPECHECK WYRAŻEŃ --------------------------------

addCall :: Ident -> Ident -> (Map Ident (Set Ident)) -> (Map Ident (Set Ident))
addCall src dest calls =
    case Data.Map.lookup src calls of
        Nothing -> Data.Map.insert src (Data.Set.fromList [dest]) calls
        Just list -> Data.Map.insert src (Data.Set.insert dest list) calls

checkE :: Expr -> VType -> FType -> IType -> Maybe Ident -> Calls -> Either String (Type, Calls)

checkE (EVar pos id) gV gF gI inl calls =
    if Data.Map.member id gV then Right ((gV ! id), calls)
    else Left (showPos pos ": undefined variable")

checkE (ELitInt pos val) gV gF gI inl calls = Right ((Int pos), calls)

checkE (ELitTrue pos) gV gF gI inl calls = Right ((Bool pos), calls)
checkE (ELitFalse pos) gV gF gI inl calls = Right ((Bool pos), calls)

checkE (EApp pos id exps) gV gF gI inl calls =
    if Data.Map.member id gF then
        checkArgs pos (gF ! id) exps gV gF gI inl calls
    else if Data.Map.member id gI then
        case inl of
            Nothing -> checkArgs pos (gI ! id) exps gV gF gI inl calls
            Just fid -> checkArgs pos (gI ! id) exps gV gF gI inl (addCall fid id calls) -- jesteśmy w inline funkcji i wołamy inline funkcję
    else Left (showPos pos ": unknown function")

checkE (EString pos str) gV gF gI inl calls = Right (Str pos, calls)

checkE (Not pos exp) gV gF gI inl calls = -- negacja binarna
    case checkE exp gV gF gI inl calls of
        Left error -> Left error
        Right (Bool _, calls') -> Right (Bool pos, calls')
        Right _ -> Left (showPos pos ": expected type bool")

checkE (Neg pos exp) gV gF gI inl calls = -- minus
    case checkE exp gV gF gI inl calls of
        Left error -> Left error
        Right (Int _, calls') -> Right (Int pos, calls')
        Right _ -> Left (showPos pos ": expected type int")

checkE (EMul pos exp1 op exp2) gV gF gI inl calls =
    case checkE exp1 gV gF gI inl calls of
        Left error -> Left error
        Right (Int _, calls1) ->
            case checkE exp2 gV gF gI inl calls1 of
                Left error -> Left error
                Right (Int _, calls2) -> Right (Int pos, calls2)
                Right _ -> Left (showPos (hasPosition exp2) ": expected type int")
        Right _ -> Left (showPos (hasPosition exp1) ": expected type int")

checkE (EAdd pos exp1 op exp2) gV gF gI inl calls =
    case (op, checkE exp1 gV gF gI inl calls) of
        (_, Left error) -> Left error
        (_, Right (Int _, calls1)) ->
            case checkE exp2 gV gF gI inl calls1 of
                Left error -> Left error
                Right (Int _, calls2) -> Right (Int pos, calls2)
                Right _ -> Left (showPos (hasPosition exp2) ": expected type int")
        (Minus _, _) -> Left (showPos (hasPosition exp1) ": expected type int")
        (Plus _, Right (Str _, calls1)) ->
            case checkE exp2 gV gF gI inl calls1 of
                Left error -> Left error
                Right (Str _, calls2) -> Right (Str pos, calls2)
                Right _ -> Left (showPos (hasPosition exp2) ": expected type string")
        (Plus _, Right _) -> Left (showPos (hasPosition exp1) ": expected type int or string")

-- typechecker przewiduje porównywanie wszystkich typów poza void
checkE (ERel pos exp1 op exp2) gV gF gI inl calls =
    case checkE exp1 gV gF gI inl calls of
        Left error -> Left error
        Right (t1, calls1) ->
            case checkE exp2 gV gF gI inl calls1 of
                Left error -> Left error
                Right (t2, calls2) ->
                    if eqTypes t1 t2 then
                        if eqTypes (Void Nothing) t1 then
                            Left (showPos (hasPosition exp1) ": operator undefined for type void")
                        else Right (Bool pos, calls2)
                    else Left (showPos (hasPosition op) ": incompatybile types")

checkE (EAnd pos exp1 exp2) gV gF gI inl calls =
    case checkE exp1 gV gF gI inl calls of
        Left error -> Left error
        Right (Bool _, calls1) ->
            case checkE exp2 gV gF gI inl calls1 of
                Left error -> Left error
                Right (Bool _, calls2) -> Right (Bool pos, calls2)
                Right _ -> Left (showPos (hasPosition exp2) ": expected type bool")
        Right _ -> Left (showPos (hasPosition exp1) ": expected type bool")

checkE (EOr pos exp1 exp2) gV gF gI inl calls = checkE (EAnd pos exp1 exp2) gV gF gI inl calls

--------------------- TYPECHECK BLOKÓW --------------------------------
-- chcemy uniknąć sytacji
-- {
--     return 7;
--     return "xd";
-- }

data Ret = Always | Sometimes
type RetType = (Type, Ret)

checkB :: Block -> VType -> FType -> IType -> VType -> Maybe RetType -> Maybe Ident -> Calls -> Either String (Maybe RetType, Calls)

checkB block gV gF gI gB mT inl calls = case block of
    Block pos (stmt : rest) -> case checkS stmt gV gF gI gB inl calls of
        Left error -> Left error
        Right (gB', mT', calls') ->
            case (mT, mT') of
                (Nothing, Nothing) -> checkB (Block pos rest) gV gF gI gB' Nothing inl calls'
                (Nothing, Just (t, ret)) -> checkB (Block pos rest) gV gF gI gB' (Just (t, ret)) inl calls'
                (Just (t, ret), Nothing) -> checkB (Block pos rest) gV gF gI gB' (Just (t, ret)) inl calls'
                (Just (t1, ret1), Just (t2, ret2)) ->
                    if eqTypes t1 t2 then case (ret1, ret2) of
                        (Sometimes, Sometimes) -> checkB (Block pos rest) gV gF gI gB' (Just (t1, Sometimes)) inl calls'
                        _ -> checkB (Block pos rest) gV gF gI gB' (Just (t1, Always)) inl calls'
                    else Left ((showPos (hasPosition t1) . showPos (hasPosition t2)) ": ambigous return type")
    Block _ [] -> Right (mT, calls)

--------------------- TYPECHECK INSTRUKCJI --------------------------------

checkS :: Stmt -> VType -> FType -> IType -> VType -> Maybe Ident -> Calls -> Either String (VType, (Maybe RetType), Calls)

checkS (Empty _) gV gF gI gB inl calls = Right (gB, Nothing, calls)

checkS (BStmt _ block) gV gF gI gB inl calls =
    case checkB block (Data.Map.union gB gV) gF gI Data.Map.empty Nothing inl calls of
        Left error -> Left error
        Right (mT, calls') -> Right (gB, mT, calls')

checkS (Decl pos t items) gV gF gI gB inl calls =
    case items of
        [] -> Right (gB, Nothing, calls)
        (NoInit p id : rest) ->
            if Data.Map.member id gB then Left (showPos p ": redeclaration of a variable")
            else checkS (Decl pos t rest) gV gF gI (Data.Map.insert id t gB) inl calls
        (Init p id exp : rest) ->
            if Data.Map.member id gB then Left (showPos p ": redeclaration of a variable")
            else case checkE exp (Data.Map.union gB gV) gF gI inl calls of
                Left error -> Left error
                Right (t', calls') ->
                    if eqTypes t t' then checkS (Decl pos t rest) gV gF gI (Data.Map.insert id t gB) inl calls'
                    else Left (showPos (hasPosition exp) ": incompatybile types")

checkS (Ass pos id exp1) gV gF gI gB inl calls =
    let gVB = Data.Map.union gB gV in
        if Data.Map.member id gVB then
            case (checkE exp1 gVB gF gI inl calls, gVB ! id) of
                (Left error, _) -> Left error
                (Right (t1, calls'), t2) ->
                    if eqTypes t1 t2 then Right (gB, Nothing, calls')
                    else Left (showPos pos ": incopatibile types")
        else Left (showPos pos ": undefined variable")

checkS (Incr pos id) gV gF gI gB inl calls =
    let gVB = Data.Map.union gB gV in
        if Data.Map.member id gVB then
            case gVB ! id of
                (Int _) -> Right (gB, Nothing, calls)
                _ -> Left (showPos pos ": expected type int")
        else Left (showPos pos ": undefined variable")

checkS (Decr pos id) gV gF gI gB inl calls =
    let gVB = Data.Map.union gB gV in
        if Data.Map.member id gVB then
            case gVB ! id of
                (Int _) -> Right (gB, Nothing, calls)
                _ -> Left (showPos pos ": expected type int")
        else Left (showPos pos ": undefined variable")

checkS (Ret _ exp) gV gF gI gB inl calls =
    case checkE exp (Data.Map.union gB gV) gF gI inl calls of
        Left error -> Left error
        Right (t, calls') -> Right (gB, Just (t, Always), calls')

checkS (VRet pos) gV gF gI gB inl calls = Right (gB, Just (Void pos, Always), calls)

checkS (Cond _  exp stmt) gV gF gI gB inl calls =
    case checkE exp (Data.Map.union gB gV) gF gI inl calls of
        Left error -> Left error
        Right (Bool _, calls') -> case checkS stmt gV gF gI gB inl calls' of
            Left error -> Left error
            Right (_, Nothing, calls'') -> Right (gB, Nothing, calls'')
            Right (_, Just (t, ret), calls'') -> case exp of
                ELitTrue _ -> Right (gB, Just (t, ret), calls'')
                _ -> Right (gB, Just (t, Sometimes), calls'')
        Right _ -> Left (showPos (hasPosition exp) ": expected condition type bool")

checkS (CondElse pos exp stmt1 stmt2) gV gF gI gB inl calls =
    let gVB = Data.Map.union gB gV in
        case checkE exp gVB gF gI inl calls of
            Left error -> Left error
            Right (Bool _, calls') ->
                case checkS stmt1 gV gF gI gB inl calls' of
                    Left error -> Left error
                    Right (_, Nothing, calls1) ->
                        case checkS stmt2 gV gF gI gB inl calls1 of
                            Right (_, Nothing, calls2) -> Right (gB, Nothing, calls2)
                            Right (_, Just (t, ret), calls2) -> case exp of
                                ELitFalse _ -> Right (gB, Just (t, ret), calls2)
                                _ -> Right (gB, Just (t, Sometimes), calls2)
                    Right (_, Just (t1, ret1), calls1) ->
                        case checkS stmt2 gV gF gI gB inl calls1 of
                            Right (_, Nothing, calls2) -> case exp of
                                ELitTrue _ -> Right (gB, Just (t1, ret1), calls2)
                                _ -> Right (gB, Just (t1, Sometimes), calls2)
                            Right (_, Just (t2, ret2), calls2) ->
                                if eqTypes t1 t2 then case (exp, ret1, ret2) of
                                    (ELitTrue _, _, _) -> Right (gB, Just (t1, ret1), calls2)
                                    (ELitFalse _, _, _) -> Right (gB, Just (t2, ret2), calls2)
                                    (_, Always, Always) -> Right (gB, Just (t1, Always), calls2)
                                    _ -> Right (gB, Just (t1, Sometimes), calls2)
                                else Left ((showPos (hasPosition t1) . showPos (hasPosition t2)) ": ambigous return type")
            Right _ -> Left (showPos (hasPosition exp) ": expected condition type bool")

checkS (While _ exp stmt) gV gF gI gB inl calls =
    case checkE exp (Data.Map.union gB gV) gF gI inl calls of
        Left error -> Left error
        Right (Bool _, calls') -> case checkS stmt gV gF gI gB inl calls' of
            Left error -> Left error
            Right (_, Nothing, calls'') -> Right (gB, Nothing, calls'')
            Right (_, Just (t, _), calls'') -> case exp of
                ELitTrue _ -> Right (gB, Just (t, Always), calls'') -- jedyny sposób wyjścia z pętli
                _ -> Right (gB, Just (t, Sometimes), calls'')
        Right _ -> Left (showPos (hasPosition exp) ": expected condition type bool")

checkS (SExp _ exp) gV gF gI gB inl calls =
    case checkE exp (Data.Map.union gB gV) gF gI inl calls of
        Left error -> Left error
        Right (_, calls') -> Right (gB, Nothing, calls')

--------------------- TYPECHECK DEKLARACJI FUNKCJI --------------------------------

mapArgs :: [Arg] -> VType -> Either String VType
mapArgs args gV = case args of
    [] -> Right gV
    (Arg pos t id : rest) ->
        if Data.Map.member id gV then Left (showPos pos ": repeated argument name")
        else mapArgs rest (Data.Map.insert id t gV)

checkDF :: [TopDef] -> FType -> IType -> Calls -> Either String Calls
checkDF defs gF gI calls = case defs of
    [] -> Right calls
    (FnDef pos t id args block : rest) ->
        case mapArgs args Data.Map.empty of
            Left error -> Left error
            Right argMap ->
                case checkB block Data.Map.empty gF gI argMap Nothing Nothing calls of
                    Left error -> Left error
                    Right (Nothing, calls') ->
                        if eqTypes (Void Nothing) t then checkDF rest gF gI calls'
                        else Left (showPos pos ": missing return")
                    Right (Just (t', Sometimes), calls') ->
                        if eqTypes t t' then
                            if eqTypes (Void Nothing) t then checkDF rest gF gI calls'
                            else Left (showPos pos ": missing return")
                        else Left (showPos (hasPosition t') ": wrong return type")
                    Right (Just (t', Always), calls') ->
                        if eqTypes t t' then checkDF rest gF gI calls'
                        else Left (showPos (hasPosition t') ": wrong return type")
    (InlFnDef pos t id args block : rest) ->
        case mapArgs args Data.Map.empty of
            Left error -> Left error
            Right argMap ->
                case checkB block Data.Map.empty gF gI argMap Nothing (Just id) calls of
                    Left error -> Left error
                    Right (Nothing, calls') ->
                        if eqTypes (Void Nothing) t then checkDF rest gF gI calls'
                        else Left (showPos pos ": missing return")
                    Right ((Just (t', Sometimes)), calls') ->
                        if eqTypes t t' then
                            if eqTypes (Void Nothing) t then checkDF rest gF gI calls'
                            else Left (showPos pos ": missing return")
                        else Left (showPos (hasPosition t') ": wrong return type")
                    Right ((Just (t', Always)), calls') ->
                        if eqTypes t t' then checkDF rest gF gI calls'
                        else Left (showPos (hasPosition t') ": wrong return type")

--------------------- TYPECHECK PROGRAMU --------------------------------

storeDF :: [TopDef] -> FType -> IType -> Either String (FType, IType)

storeDF defs gF gI = case defs of
    (FnDef pos t id args block : rest) ->
        if Data.Map.member id gF || Data.Map.member id gI then Left (showPos pos ": function name must be unique")
        else storeDF rest (Data.Map.insert id (t, args) gF) gI
    (InlFnDef pos t id args block : rest) ->
        if Data.Map.member id gF  || Data.Map.member id gI then Left (showPos pos ": function name must be unique")
        else storeDF rest gF (Data.Map.insert id (t, args) gI)
    [] -> Right (gF, gI)

pushNeighbours :: [Ident] -> [Ident] -> Set Ident -> ([Ident], Set Ident)
pushNeighbours neigh stack reach =
    case neigh of
        [] -> (stack, reach)
        (id : rest) ->
            if Data.Set.member id reach then pushNeighbours rest stack reach
            else pushNeighbours rest (id : stack) (Data.Set.insert id reach)

reachable :: [Ident] -> Calls -> Set Ident -> Set Ident
reachable stack calls reach =
    case stack of
        [] -> reach
        (id : rest) ->
            case Data.Map.lookup id calls of
                Just neigh ->
                    let (stack', reach') = pushNeighbours (Data.Set.toList neigh) rest reach in
                        reachable stack' calls reach'
                Nothing -> reachable rest calls reach

checkRec :: [Ident] -> Calls -> Maybe String
checkRec ids calls =
    case ids of
        [] -> Nothing
        (Ident id : rest) ->
            let reach = reachable [Ident id] calls Data.Set.empty in
                if Data.Set.member (Ident id) reach then Just ("inline function " ++ show id ++ " must not be recursive")
                else checkRec rest calls
    
typecheck :: Program -> Maybe String

typecheck (Program _ defs) = case storeDF defs initFType initIType of
    Left error -> Just error
    Right (gF, gI) ->
        if Data.Map.member (Ident "main") gF then
            let (t, args) = gF ! (Ident "main") in
                if eqTypes t (Int Nothing) && args == [] then
                    case checkDF defs gF gI Data.Map.empty of
                        Left error -> Just error
                        Right calls -> checkRec (Data.Map.keys gI) calls
                else Just "missing function int main()"
        else Just "missing function int main()"

initFType :: FType
initFType = Data.Map.fromList [
    (Ident "printInt", (Void Nothing, [Arg Nothing (Int Nothing) (Ident "x")])),
    (Ident "printString", (Void Nothing, [Arg Nothing (Str Nothing) (Ident "x")])),
    (Ident "error", (Void Nothing, [])),
    (Ident "readInt", (Int Nothing, [])),
    (Ident "readString", (Str Nothing, []))
    ]

initIType :: IType
initIType = Data.Map.empty
