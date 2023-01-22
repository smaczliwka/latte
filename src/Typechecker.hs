module Typechecker (typecheck) where

import AbsLatte
import Data.Map

testExp = (EAdd (Just (2,1)) (ELitInt (Just (2,1)) 123) (Plus (Just (2,5))) (EMul (Just (2,7)) (EOr (Just (2,8)) (ERel (Just (2,8)) (EString (Just (2,8)) "ala") (GTH (Just (2,14))) (EString (Just (2,16)) "ela")) (ERel (Just (2,25)) (EString (Just (2,25)) "ela") (LTH (Just (2,31))) (EString (Just (2,33)) "ola"))) (Div (Just (2,40))) (EApp (Just (2,42)) (Ident "g") [EVar (Just (2,44)) (Ident "x")])))

showPos :: BNFC'Position -> ShowS
showPos pos = case pos of
    Just (line, col) -> showString "(line:" . shows line . showString ", col:" . shows col . showString ")"
    Nothing -> id

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

checkArgs :: BNFC'Position -> (Type, [Arg]) -> [Expr] -> VType -> FType -> IType -> Either String Type
checkArgs pos (ft, args) exps gV gF gI =
    case (args, exps) of
        ([], []) -> Right ft
        (h : _, []) -> Left (showPos pos ": not enough arguments")
        ([], h : _) -> Left (showPos pos ": too many arguments")
        ((Arg _ argt _) : argRest, exp : expRest) ->
            case checkE exp gV gF gI False of
                Left error -> Left error
                Right t ->
                    if eqTypes t argt then checkArgs pos (ft, argRest) expRest gV gF gI
                    else Left (showPos (hasPosition exp) ": wrong type of argument")

--------------------- TYPECHECK WYRAŻEŃ --------------------------------

checkE :: Expr -> VType -> FType -> IType -> Bool -> Either String Type

checkE (EVar pos id) gV gF gI inl =
    if member id gV then Right (gV ! id)
    else Left (showPos pos ": undefined variable")

checkE (ELitInt pos val) gV gF gI inl = Right (Int pos)

checkE (ELitTrue pos) gV gF gI inl = Right (Bool pos)
checkE (ELitFalse pos) gV gF gI inl = Right (Bool pos)

checkE (EApp pos id exps) gV gF gI inl =
    if inl then
        Left (showPos pos ": inline functions must not call another functions")
    else
        if member id gF then
            checkArgs pos (gF ! id) exps gV gF gI
        else if member id gI then
            checkArgs pos (gI ! id) exps gV gF gI
        else Left (showPos pos ": unknown function")

checkE (EString pos str) gV gF gI inl = Right (Str pos)

checkE (Not pos exp) gV gF gI inl = -- negacja binarna
    case checkE exp gV gF gI inl of
        Left error -> Left error
        Right (Bool _) -> Right (Bool pos)
        Right _ -> Left (showPos pos ": expected type bool")

checkE (Neg pos exp) gV gF gI inl = -- minus
    case checkE exp gV gF gI inl of
        Left error -> Left error
        Right (Int _) -> Right (Int pos)
        Right _ -> Left (showPos pos ": expected type int")

checkE (EMul pos exp1 op exp2) gV gF gI inl =
    case (checkE exp1 gV gF gI inl, checkE exp2 gV gF gI inl) of
        (Left error, _) -> Left error
        (Right (Int _), Left error) -> Left error
        (Right (Int _), Right (Int _)) -> Right (Int pos)
        (Right (Int _), Right _) -> Left (showPos (hasPosition exp2) ": expected type int")
        (Right _, _) -> Left (showPos (hasPosition exp1) ": expected type int")

checkE (EAdd pos exp1 op exp2) gV gF gI inl =
    case (op, checkE exp1 gV gF gI inl, checkE exp2 gV gF gI inl) of
        (_, Left error, _) -> Left error
        (_, Right (Int _), Left error) -> Left error
        (_, Right (Int _), Right (Int _)) -> Right (Int pos)
        (_, Right (Int _), Right _) -> Left (showPos (hasPosition exp2) ": expected type int")
        (Plus _, Right (Str _), Right (Str _)) -> Right (Str pos)
        (Plus _, Right (Str _), Right _) -> Left (showPos (hasPosition exp2) ": expected type string")
        (Plus _, Right _, _) -> Left (showPos (hasPosition exp1) ": expected type int or string")
        (Minus _, Right _, _) -> Left (showPos (hasPosition exp1) ": expected type int")

-- typechecker przewiduje porównywanie wszystkich typów poza void
checkE (ERel pos exp1 op exp2) gV gF gI inl =
    case (checkE exp1 gV gF gI inl, checkE exp2 gV gF gI inl) of
        (Left error, _) -> Left error
        (Right _, Left error) -> Left error
        (Right t1, Right t2) ->
            if eqTypes t1 t2 then
                if eqTypes (Void Nothing) t1 then
                    Left (showPos (hasPosition exp1) ": operator undefined for type void")
                else Right (Bool pos)
            else Left (showPos (hasPosition op) ": incompatybile types")

checkE (EAnd pos exp1 exp2) gV gF gI inl =
    case (checkE exp1 gV gF gI inl, checkE exp2 gV gF gI inl) of
        (Left error, _) -> Left error
        (Right (Bool _), Left error) -> Left error
        (Right (Bool _), Right (Bool _)) -> Right (Bool pos)
        (Right (Bool _), Right _) -> Left (showPos (hasPosition exp2) ": expected type bool")
        (Right _, _) -> Left (showPos (hasPosition exp1) ": expected type bool")

checkE (EOr pos exp1 exp2) gV gF gI inl = checkE (EAnd pos exp1 exp2) gV gF gI inl

--------------------- TYPECHECK BLOKÓW --------------------------------
-- chcemy uniknąć sytacji
-- {
--     return 7;
--     return "xd";
-- }

data Ret = Always | Sometimes
type RetType = (Type, Ret)

checkB :: Block -> VType -> FType -> IType -> VType -> Maybe RetType -> Bool -> Either String (Maybe RetType)

checkB block gV gF gI gB mT inl = case block of
    Block pos (stmt : rest) -> case checkS stmt gV gF gI gB inl of
        Left error -> Left error
        Right (gB', mT') ->
            case (mT, mT') of
                (Nothing, Nothing) -> checkB (Block pos rest) gV gF gI gB' Nothing inl
                (Nothing, Just (t, ret)) -> checkB (Block pos rest) gV gF gI gB' (Just (t, ret)) inl
                (Just (t, ret), Nothing) -> checkB (Block pos rest) gV gF gI gB' (Just (t, ret)) inl
                (Just (t1, ret1), Just (t2, ret2)) ->
                    if eqTypes t1 t2 then case (ret1, ret2) of
                        (Sometimes, Sometimes) -> checkB (Block pos rest) gV gF gI gB' (Just (t1, Sometimes)) inl
                        _ -> checkB (Block pos rest) gV gF gI gB' (Just (t1, Always)) inl
                    else Left ((showPos (hasPosition t1) . showPos (hasPosition t2)) ": ambigous return type")
    Block _ [] -> Right mT

--------------------- TYPECHECK INSTRUKCJI --------------------------------

checkS :: Stmt -> VType -> FType -> IType -> VType -> Bool -> Either String (VType, (Maybe RetType))

checkS (Empty _) gV gF gI gB inl = Right (gB, Nothing)

checkS (BStmt _ block) gV gF gI gB inl =
    case checkB block (union gB gV) gF gI empty Nothing inl of
        Left error -> Left error
        Right mT -> Right (gB, mT)

checkS (Decl pos t items) gV gF gI gB inl =
    case items of
        [] -> Right (gB, Nothing)
        (NoInit p id : rest) ->
            if member id gB then Left (showPos p ": redeclaration of a variable")
            else checkS (Decl pos t rest) gV gF gI (insert id t gB) inl
        (Init p id exp : rest) ->
            if member id gB then Left (showPos p ": redeclaration of a variable")
            else case checkE exp (union gB gV) gF gI inl of
                Left error -> Left error
                Right t' ->
                    if eqTypes t t' then checkS (Decl pos t rest) gV gF gI (insert id t gB) inl
                    else Left (showPos (hasPosition exp) ": incompatybile types")

checkS (Ass pos id exp1) gV gF gI gB inl =
    let gVB = union gB gV in
        if member id gVB then
            case (checkE exp1 gVB gF gI inl, gVB ! id) of
                (Left error, _) -> Left error
                (Right t1, t2) ->
                    if eqTypes t1 t2 then Right (gB, Nothing)
                    else Left (showPos pos ": incopatibile types")
        else Left (showPos pos ": undefined variable")

checkS (Incr pos id) gV gF gI gB inl =
    let gVB = union gB gV in
        if member id gVB then
            case gVB ! id of
                (Int _) -> Right (gB, Nothing)
                _ -> Left (showPos pos ": expected type int")
        else Left (showPos pos ": undefined variable")

checkS (Decr pos id) gV gF gI gB inl =
    let gVB = union gB gV in
        if member id gVB then
            case gVB ! id of
                (Int _) -> Right (gB, Nothing)
                _ -> Left (showPos pos ": expected type int")
        else Left (showPos pos ": undefined variable")

checkS (Ret _ exp) gV gF gI gB inl =
    case checkE exp (union gB gV) gF gI inl of
        Left error -> Left error
        Right t -> Right (gB, Just (t, Always))

checkS (VRet pos) gV gF gI gB inl = Right (gB, Just (Void pos, Always))

checkS (Cond _  exp stmt) gV gF gI gB inl =
    case checkE exp (union gB gV) gF gI inl of
        Left error -> Left error
        Right (Bool _) -> case checkS stmt gV gF gI gB inl of
            Left error -> Left error
            Right (_, Nothing) -> Right (gB, Nothing)
            Right (_, Just (t, ret)) -> case exp of
                ELitTrue _ -> Right (gB, Just (t, ret))
                _ -> Right (gB, Just (t, Sometimes))
        Right _ -> Left (showPos (hasPosition exp) ": expected condition type bool")

checkS (CondElse pos exp stmt1 stmt2) gV gF gI gB inl =
    let gVB = union gB gV in
        case checkE exp gVB gF gI inl of
            Left error -> Left error
            Right (Bool _) ->
                case (checkS stmt1 gV gF gI gB inl, checkS stmt2 gV gF gI gB inl) of
                    (Left error, _) -> Left error
                    (_, Left error) -> Left error
                    (Right (_, Nothing), Right (_, Nothing)) -> Right (gB, Nothing)
                    (Right (_, Nothing), Right (_, Just (t, ret))) -> case exp of
                        ELitFalse _ -> Right (gB, Just (t, ret))
                        _ -> Right (gB, Just (t, Sometimes))
                    (Right (_, Just (t, ret)), Right (_, Nothing)) -> case exp of
                        ELitTrue _ -> Right (gB, Just (t, ret))
                        _ -> Right (gB, Just (t, Sometimes))
                    (Right (_, Just (t1, ret1)), Right (_, Just (t2, ret2))) ->
                        if eqTypes t1 t2 then case (exp, ret1, ret2) of
                            (ELitTrue _, _, _) -> Right (gB, Just (t1, ret1))
                            (ELitFalse _, _, _) -> Right (gB, Just (t2, ret2))
                            (_, Always, Always) -> Right (gB, Just (t1, Always))
                            _ -> Right (gB, Just (t1, Sometimes))
                        else Left ((showPos (hasPosition t1) . showPos (hasPosition t2)) ": ambigous return type")
            Right _ -> Left (showPos (hasPosition exp) ": expected condition type bool")

checkS (While _ exp stmt) gV gF gI gB inl =
    case checkE exp (union gB gV) gF gI inl of
        Left error -> Left error
        Right (Bool _) -> case checkS stmt gV gF gI gB inl of
            Left error -> Left error
            Right (_, Nothing) -> Right (gB, Nothing)
            Right (_, Just (t, _)) -> case exp of
                ELitTrue _ -> Right (gB, Just (t, Always)) -- jedyny sposób wyjścia z pętli
                _ -> Right (gB, Just (t, Sometimes))
        Right _ -> Left (showPos (hasPosition exp) ": expected condition type bool")

checkS (SExp _ exp) gV gF gI gB inl =
    case checkE exp (union gB gV) gF gI inl of
        Left error -> Left error
        Right _ -> Right (gB, Nothing)

--------------------- TYPECHECK DEKLARACJI FUNKCJI --------------------------------

mapArgs :: [Arg] -> VType -> Either String VType
mapArgs args gV = case args of
    [] -> Right gV
    (Arg pos t id : rest) ->
        if member id gV then Left (showPos pos ": repeated argument name")
        else mapArgs rest (insert id t gV)

checkDF :: [TopDef] -> FType -> IType -> Maybe String
checkDF defs gF gI = case defs of
    [] -> Nothing
    (FnDef pos t id args block : rest) ->
        case mapArgs args empty of
            Left error -> Just error
            Right argMap ->
                case checkB block empty gF gI argMap Nothing False of
                    Left error -> Just error
                    Right Nothing ->
                        if eqTypes (Void Nothing) t then checkDF rest gF gI
                        else Just (showPos pos ": missing return")
                    Right (Just (t', Sometimes)) ->
                        if eqTypes t t' then
                            if eqTypes (Void Nothing) t then  checkDF rest gF gI
                            else Just (showPos pos ": missing return")
                        else Just (showPos (hasPosition t') ": wrong return type")
                    Right (Just (t', Always)) ->
                        if eqTypes t t' then checkDF rest gF gI
                        else Just (showPos (hasPosition t') ": wrong return type")
    (InlFnDef pos t id args block : rest) ->
        case mapArgs args empty of
            Left error -> Just error
            Right argMap ->
                case checkB block empty gF gI argMap Nothing True of
                    Left error -> Just error
                    Right Nothing ->
                        if eqTypes (Void Nothing) t then checkDF rest gF gI
                        else Just (showPos pos ": missing return")
                    Right (Just (t', Sometimes)) ->
                        if eqTypes t t' then
                            if eqTypes (Void Nothing) t then  checkDF rest gF gI
                            else Just (showPos pos ": missing return")
                        else Just (showPos (hasPosition t') ": wrong return type")
                    Right (Just (t', Always)) ->
                        if eqTypes t t' then checkDF rest gF gI
                        else Just (showPos (hasPosition t') ": wrong return type")

--------------------- TYPECHECK PROGRAMU --------------------------------

storeDF :: [TopDef] -> FType -> IType -> Either String (FType, IType)

storeDF defs gF gI = case defs of
    (FnDef pos t id args block : rest) ->
        if member id gF || member id gI then Left (showPos pos ": function name must be unique")
        else storeDF rest (insert id (t, args) gF) gI
    (InlFnDef pos t id args block : rest) ->
        if member id gF  || member id gI then Left (showPos pos ": function name must be unique")
        else storeDF rest gF (insert id (t, args) gI)
    [] -> Right (gF, gI)
    
typecheck :: Program -> Maybe String

typecheck (Program _ defs) = case storeDF defs initFType initIType of
    Left error -> Just error
    Right (gF, gI) ->
        if member (Ident "main") gF then
            let (t, args) = gF ! (Ident "main") in
                if eqTypes t (Int Nothing) && args == [] then checkDF defs gF gI
                else Just "missing function int main()"
        else Just "missing function int main()"

initFType :: FType
initFType = fromList [
    (Ident "printInt", (Void Nothing, [Arg Nothing (Int Nothing) (Ident "x")])),
    (Ident "printString", (Void Nothing, [Arg Nothing (Str Nothing) (Ident "x")])),
    (Ident "error", (Void Nothing, [])),
    (Ident "readInt", (Int Nothing, [])),
    (Ident "readString", (Str Nothing, []))
    ]

initIType :: IType
initIType = empty
