module Emiter where

import AbsLatte
import Data.Map

data RegType = RegInt | RegStr | RegBool | RegVoid
    deriving (Eq, Ord)

type RegNum = Integer
type Reg = (RegType, RegNum)

typeRegType :: Type -> RegType
typeRegType t = case t of
    Int _ -> RegInt
    Str _ -> RegStr
    Bool _ -> RegBool
    Void _ -> RegVoid

data Const = ConstInt Integer | ConstBool Bool | ConstVoid
    deriving (Eq, Ord)

typeDefault :: Type -> Res
typeDefault t = case t of
    Int _ -> Left (ConstInt 0)
    Bool _ -> Left (ConstBool False)
    Void _ -> Left ConstVoid

type Res = Either Const Reg

resRegType :: Res -> RegType
resRegType res = case res of
    Left (ConstInt _) -> RegInt
    Left (ConstBool _) -> RegBool
    Left ConstVoid -> RegVoid
    Right (regType, _) -> regType

type Label = Integer

data Op 
    = PlusOp Reg Res Res
    | MinusOp Reg Res Res
    | TimesOp Reg Res Res
    | DivOp Reg Res Res
    | ModOp Reg Res Res
    | LTHOp Reg Res Res
    | LEOp Reg Res Res
    | GTHOp Reg Res Res
    | GEOp Reg Res Res
    | EQUOp Reg Res Res
    | NEOp Reg Res Res
    | AndOp Reg Res Res
    | OrOp Reg Res Res
    | NotOp Reg Res
    | NegOp Reg Res
    | GoOp Label
    | CondGoOp Res Label Label
    | CallOp Reg Ident [Res]
    | RetOp Res
    | LabelOp Label
    | PhiOp Reg [(Res, Label)]
    | FunOp Ident RegType [Reg]
    | BitcastOp Reg Integer StrNum
    | EndFunOp
    | CallVoidOp Ident [Res]
    deriving (Eq, Ord)

opCode :: Op -> [Op] -> [Op]
opCode op rest = op : rest

noCode :: [Op] -> [Op]
noCode rest = rest

type Code = [Op] -> [Op]
type VEnv = Map Ident Res
type FEnv = Map Ident RegType
type IEnv = Map Ident (Type, [Arg], Block)

type StrNum = Integer
type SEnv = Map String StrNum

emitArgs :: [Expr] -> VEnv -> FEnv -> IEnv -> ([Res], Code, RegNum, Label, SEnv) -> ([Res], Code, RegNum, Label, SEnv)
emitArgs exps gV gF gI (args, codes, nextReg, nextLab, gS) = case exps of
    [] -> (reverse args, codes, nextReg, nextLab, gS)
    (exp : rest) ->
        let (arg, code, nextReg', nextLab', gS') = emitE exp gV gF gI nextReg nextLab gS in
            emitArgs rest gV gF gI (arg : args, codes . code, nextReg', nextLab', gS')

emitE :: Expr -> VEnv -> FEnv -> IEnv -> RegNum -> Label -> SEnv -> (Res, Code, RegNum, Label, SEnv)

emitE (EVar pos id) gV gF gI nextReg nextLab gS = (gV ! id, noCode, nextReg, nextLab, gS)

emitE (ELitInt pos val) gV gF gI nextReg nextLab gS = (Left (ConstInt val), noCode, nextReg, nextLab, gS)

emitE (ELitTrue pos) gV gF gI nextReg nextLab gS = (Left (ConstBool True), noCode, nextReg, nextLab, gS)
emitE (ELitFalse pos) gV gF gI nextReg nextLab gS = (Left (ConstBool False), noCode, nextReg, nextLab, gS)

emitE (EApp pos id exps) gV gF gI nextReg nextLab gS =
    let (results, codes, nextReg', nextLab', gS') = emitArgs exps gV gF gI ([], noCode, nextReg, nextLab, gS) in
        if Data.Map.member id gF then
            let regType = gF ! id in
                case regType of
                    RegVoid -> (Left ConstVoid, codes . opCode (CallVoidOp id results), nextReg', nextLab', gS')
                    _ ->
                        let dest = (regType, nextReg') in
                            (Right dest, codes . opCode (CallOp dest id results), nextReg' + 1, nextLab', gS')
        else
            let (t, args, block) = gI ! id in
                let gB = mapArgsInl args results Data.Map.empty in
                    let (_, _, _, phiLab, _, _, _) = emitB block Data.Map.empty gF gI gB nextReg' nextLab' gS' Nothing [] in
                        let (_, _, nextReg'', _, code'', gS'', phiPairs) = emitB block Data.Map.empty gF gI gB nextReg' nextLab' gS' (Just (Right phiLab)) [] in
                            let regType = typeRegType t in
                                case t of
                                    Void _ ->
                                        (Right (regType, nextReg''),
                                        codes
                                        . code''
                                        . opCode (GoOp phiLab)
                                        . opCode (LabelOp phiLab),
                                        nextReg'' + 1, phiLab + 1, gS'')

                                    Str _ ->
                                        if Data.Map.member "" gS'' then
                                            (Right (regType, nextReg'' + 1),
                                            codes
                                            . code''
                                            . opCode (BitcastOp (RegStr, nextReg'') 0 (gS'' ! ""))
                                            . opCode (GoOp phiLab)
                                            . opCode (LabelOp phiLab)
                                            . opCode (PhiOp (RegStr, nextReg'' + 1) ((Right (RegStr, nextReg''), phiLab - 1) : phiPairs)),
                                            nextReg'' + 2, phiLab + 1, gS'')
                                        else
                                            let idx = toInteger (Data.Map.size gS'') in
                                                (Right (regType, nextReg'' + 1),
                                                codes
                                                . code''
                                                . opCode (BitcastOp (RegStr, nextReg'') 0 idx)
                                                . opCode (GoOp phiLab)
                                                . opCode (LabelOp phiLab)
                                                . opCode (PhiOp (RegStr, nextReg'' + 1) ((Right (RegStr, nextReg''), phiLab - 1) : phiPairs)),
                                                nextReg'' + 2, phiLab + 1, Data.Map.insert "" idx gS'')
                                    _ ->
                                        (Right (regType, nextReg''),
                                        codes
                                        . code''
                                        . opCode (GoOp phiLab)
                                        . opCode (LabelOp phiLab)
                                        . opCode (PhiOp (typeRegType t, nextReg'') ((typeDefault t, phiLab - 1) : phiPairs)),
                                        nextReg'' + 1, phiLab + 1, gS'')

emitE (EString pos str) gV gF gI nextReg nextLab gS =
    let dest = (RegStr, nextReg) in
        let len = toInteger (length str) in
            if Data.Map.member str gS then
                (Right dest, opCode (BitcastOp dest len (gS ! str)), nextReg + 1, nextLab, gS)
            else
                let idx = toInteger (Data.Map.size gS) in
                    (Right dest, opCode (BitcastOp dest len idx), nextReg + 1, nextLab, Data.Map.insert str idx gS)

emitE (Not pos exp) gV gF gI nextReg nextLab gS = -- negacja binarna
    let (res, code, nextReg', nextLab', gS') = emitE exp gV gF gI nextReg nextLab gS in
        (Right (RegBool, nextReg'), code . opCode (NotOp (RegBool, nextReg') res), nextReg' + 1, nextLab', gS')

emitE (Neg pos exp) gV gF gI nextReg nextLab gS = -- minus
    let (res, code, nextReg', nextLab', gS') = emitE exp gV gF gI nextReg nextLab gS in
        (Right (RegInt, nextReg'), code . opCode (NegOp (RegInt, nextReg') res), nextReg' + 1, nextLab', gS')

emitE (EMul pos exp1 op exp2) gV gF gI nextReg nextLab gS =
    let (res1, code1, nextReg1, nextLab1, gS1) = emitE exp1 gV gF gI nextReg nextLab gS in
        let (res2, code2, nextReg2, nextLab2, gS2) = emitE exp2 gV gF gI nextReg1 nextLab1 gS1 in
            let dest = (RegInt, nextReg2) in
                case op of
                    Times _ -> (Right dest, code1 . code2 . opCode (TimesOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    Div _ -> (Right dest, code1 . code2 . opCode (DivOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    Mod _ -> (Right dest, code1 . code2 . opCode (ModOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)

emitE (EAdd pos exp1 op exp2) gV gF gI nextReg nextLab gS =
    let (res1, code1, nextReg1, nextLab1, gS1) = emitE exp1 gV gF gI nextReg nextLab gS in
        let (res2, code2, nextReg2, nextLab2, gS2) = emitE exp2 gV gF gI nextReg1 nextLab1 gS1 in
            let dest = (resRegType res1, nextReg2) in
                case op of
                    Plus _ -> (Right dest, code1 . code2 . opCode (PlusOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    Minus _ -> (Right dest, code1 . code2 . opCode (MinusOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)

-- przewiduje porównywanie wszystkich typów poza void
emitE (ERel pos exp1 op exp2) gV gF gI nextReg nextLab gS =
    let (res1, code1, nextReg1, nextLab1, gS1) = emitE exp1 gV gF gI nextReg nextLab gS in
        let (res2, code2, nextReg2, nextLab2, gS2) = emitE exp2 gV gF gI nextReg1 nextLab1 gS1 in
            let dest = (RegBool, nextReg2) in
                case op of
                    LTH _ -> (Right dest, code1 . code2 . opCode (LTHOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    LE _ -> (Right dest, code1 . code2 . opCode (LEOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    GTH _ -> (Right dest, code1 . code2 . opCode (GTHOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    GE _ -> (Right dest, code1 . code2 . opCode (GEOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    EQU _ -> (Right dest, code1 . code2 . opCode (EQUOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    NE _ -> (Right dest, code1 . code2 . opCode (NEOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)

emitE (EAnd pos exp1 exp2) gV gF gI nextReg nextLab gS =
    let (lTrue, lFalse) = (nextLab, nextLab + 1) in
        let (code, nextReg', nextLab', gS') = emitL (EAnd pos exp1 exp2) gV gF gI nextReg (nextLab + 2) gS lTrue lFalse in
            (Right (RegBool, nextReg'),
            code
            . opCode (LabelOp lTrue)
            . opCode (GoOp nextLab')
            . opCode (LabelOp lFalse)
            . opCode (GoOp nextLab')
            . opCode (LabelOp nextLab')
            . opCode (PhiOp (RegBool, nextReg') [(Left (ConstBool True), lTrue), (Left (ConstBool False), lFalse)]),
            nextReg' + 1, nextLab' + 1, gS')

emitE (EOr pos exp1 exp2) gV gF gI nextReg nextLab gS =
    let (lTrue, lFalse) = (nextLab, nextLab + 1) in
        let (code, nextReg', nextLab', gS') = emitL (EOr pos exp1 exp2) gV gF gI nextReg (nextLab + 2) gS lTrue lFalse in
            (Right (RegBool, nextReg'),
            code
            . opCode (LabelOp lTrue)
            . opCode (GoOp nextLab')
            . opCode (LabelOp lFalse)
            . opCode (GoOp nextLab')
            . opCode (LabelOp nextLab')
            . opCode (PhiOp (RegBool, nextReg') [(Left (ConstBool True), lTrue), (Left (ConstBool False), lFalse)]),
            nextReg' + 1, nextLab' + 1, gS')

---------------------------------------------------------------------------------

emitL :: Expr -> VEnv -> FEnv -> IEnv -> RegNum -> Label -> SEnv -> Label -> Label -> (Code, RegNum, Label, SEnv)

emitL (EVar pos id) gV gF gI nextReg nextLab gS lTrue lFalse =
    (opCode (CondGoOp (gV ! id) lTrue lFalse), nextReg, nextLab, gS)

emitL (ELitTrue pos) gV gF gI nextReg nextLab gS lTrue lFalse =
    (opCode (GoOp lTrue), nextReg, nextLab, gS)

emitL (ELitFalse pos) gV gF gI nextReg nextLab gS lTrue lFalse =
    (opCode (GoOp lTrue), nextReg, nextLab, gS)

emitL (EApp pos id exps) gV gF gI nextReg nextLab gS lTrue lFalse =
    let (results, codes, nextReg', nextLab', gS') = emitArgs exps gV gF gI ([], noCode, nextReg, nextLab, gS) in
        if Data.Map.member id gF then
            let dest = (gF ! id, nextReg') in
                (codes
                . opCode (CallOp dest id results)
                . opCode (CondGoOp (Right dest) lTrue lFalse),
                nextReg' + 1, nextLab', gS')
        else -------------------------------------------------------- APLIKACJA FUNKCJI INLINE
            let (t, args, block) = gI ! id in
                let gB = mapArgsInl args results Data.Map.empty in
                    let (_, _, nextReg'', nextLab'', code'', gS'', _) = emitB block Data.Map.empty gF gI gB nextReg' nextLab' gS' (Just (Left (lTrue, lFalse))) [] in
                            (codes
                            . code''
                            . opCode (GoOp lFalse),
                            nextReg'', nextLab'', gS'')

emitL (Not pos exp) gV gF gI nextReg nextLab gS lTrue lFalse = -- negacja binarna
    emitL exp gV gF gI nextReg nextLab gS lFalse lTrue

emitL (ERel pos exp1 op exp2) gV gF gI nextReg nextLab gS lTrue lFalse =
    let (res1, code1, nextReg1, nextLab1, gS1) = emitE exp1 gV gF gI nextReg nextLab gS in
        let (res2, code2, nextReg2, nextLab2, gS2) = emitE exp2 gV gF gI nextReg1 nextLab1 gS1 in
            let dest = (RegBool, nextReg2) in
                let condGoCode = opCode (CondGoOp (Right dest) lTrue lFalse) in
                    case op of
                        LTH _ -> (code1 . code2 . opCode (LTHOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)
                        LE _ -> (code1 . code2 . opCode (LEOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)
                        GTH _ -> (code1 . code2 . opCode (GTHOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)
                        GE _ -> (code1 . code2 . opCode (GEOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)
                        EQU _ -> (code1 . code2 . opCode (EQUOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)
                        NE _ -> (code1 . code2 . opCode (NEOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)

emitL (EAnd pos exp1 exp2) gV gF gI nextReg nextLab gS lTrue lFalse =
    -- lP = nextLab
    let (code1, nextReg1, nextLab1, gS1) = emitL exp1 gV gF gI nextReg (nextLab + 1) gS nextLab lFalse in
        let (code2, nextReg2, nextLab2, gS2) = emitL exp2 gV gF gI nextReg1 nextLab1 gS1 lTrue lFalse in
            (code1
            . opCode (LabelOp nextLab)
            . code2,
            nextReg2, nextLab2, gS2)

emitL (EOr pos exp1 exp2) gV gF gI nextReg nextLab gS lTrue lFalse =
    -- lP = nextLab
    let (code1, nextReg1, nextLab1, gS1) = emitL exp1 gV gF gI nextReg (nextLab + 1) gS lTrue nextLab in
        let (code2, nextReg2, nextLab2, gS2) = emitL exp2 gV gF gI nextReg1 nextLab1 gS1 lTrue lFalse in
            (code1
            . opCode (LabelOp nextLab)
            . code2,
            nextReg2, nextLab2, gS2)

---------------------------------------------------------------------------------

emitB :: Block -> VEnv -> FEnv -> IEnv -> VEnv -> RegNum -> Label -> SEnv -> Maybe (Either (Label, Label) Label) -> [(Res, Label)] -> (VEnv, VEnv, RegNum, Label, Code, SEnv, [(Res, Label)])

emitB block gV gF gI gB nextReg nextLab gS phiLab phiList = case block of
    Block pos (stmt : rest) ->
        let (gV', gB', nextReg', nextLab', code', gS', phiList') = emitS stmt gV gF gI gB nextReg nextLab gS phiLab phiList in
            let (gV'', gB'', nextReg'', nextLab'', code'', gS'', phiList'') = emitB (Block pos rest) gV' gF gI gB' nextReg' nextLab' gS' phiLab phiList' in
                (gV'', gB'', nextReg'', nextLab'', code' . code'', gS'', phiList'')
    Block pos [] -> (gV, gB, nextReg, nextLab, noCode, gS, phiList)


phi :: [(Ident, Res)] -> (Label, VEnv) -> (Label, VEnv) -> RegNum -> Code -> VEnv -> (RegNum, Code, VEnv)
phi vars (label1, gV1) (label2, gV2) nextReg code gV =
    case vars of
        [] -> (nextReg, code, gV)
        ((id, res) : rest) ->
            if gV1 ! id == gV2 ! id then
                phi rest (label1, gV1) (label2, gV2) nextReg code (Data.Map.insert id (gV1 ! id) gV)
            else
                let dest = (resRegType res, nextReg) in
                    phi rest (label1, gV1) (label2, gV2) (nextReg + 1) (code . opCode (PhiOp dest [(gV1 ! id, label1), (gV2 ! id, label2)])) (Data.Map.insert id (Right dest) gV)

emitS :: Stmt -> VEnv -> FEnv -> IEnv -> VEnv -> RegNum -> Label -> SEnv -> Maybe (Either (Label, Label) Label) -> [(Res, Label)] -> (VEnv, VEnv, RegNum, Label, Code, SEnv, [(Res, Label)])

emitS (Empty _) gV gF gI gB nextReg nextLab gS phiLab phiList = (gV, gB, nextReg, nextLab, noCode, gS, phiList)

emitS (BStmt _ block) gV gF gI gB nextReg nextLab gS phiLab phiList =
    let (gV', gB', nextReg', nextLab', code', gS', phiList') = emitB block (Data.Map.union gB gV) gF gI Data.Map.empty nextReg nextLab gS phiLab phiList in
        (Data.Map.union (Data.Map.difference gV' gB) gV, Data.Map.intersection gV' gB, nextReg', nextLab', code', gS', phiList')

emitS (Decl pos t items) gV gF gI gB nextReg nextLab gS phiLab phiList =
    case (t, items) of
        (_, []) -> (gV, gB, nextReg, nextLab, noCode, gS, phiList)

        (_, Init p id exp : rest) ->
            let (res, code', nextReg', nextLab', gS') = emitE exp (Data.Map.union gB gV) gF gI nextReg nextLab gS in
                let (gV'', gB'', nextReg'', nextLab'', code'', gS'', phiList'') = emitS (Decl pos t rest) gV gF gI (Data.Map.insert id res gB) nextReg' nextLab' gS' phiLab phiList in
                    (gV'', gB'', nextReg'', nextLab'', code' . code'', gS'', phiList'')

        (Str _, NoInit p id : rest) ->
            if Data.Map.member "" gS then
                let code' = opCode (BitcastOp (RegStr, nextReg) 0 (gS ! "")) in
                    let (gV'', gB'', nextReg'', nextLab'', code'', gS'', phiList'') = emitS (Decl pos t rest) gV gF gI (Data.Map.insert id (Right (RegStr, nextReg)) gB) (nextReg + 1) nextLab gS phiLab phiList in
                        (gV'', gB'', nextReg'', nextLab'', code' . code'', gS'', phiList'')
            else
                let idx = toInteger (Data.Map.size gS) in
                    let code' = opCode (BitcastOp (RegStr, nextReg) 0 idx) in
                        let (gV'', gB'', nextReg'', nextLab'', code'', gS'', phiList'') = emitS (Decl pos t rest) gV gF gI (Data.Map.insert id (Right (RegStr, nextReg)) gB) (nextReg + 1) nextLab (Data.Map.insert "" idx gS) phiLab phiList in
                            (gV'', gB'', nextReg'', nextLab'', code' . code'', gS'', phiList'')

        (_, NoInit p id : rest) ->
            emitS (Decl pos t rest) gV gF gI (Data.Map.insert id (typeDefault t) gB) nextReg nextLab gS phiLab phiList


emitS (Ass pos id exp) gV gF gI gB nextReg nextLab gS phiLab phiList =
    let (res, code', nextReg', nextLab',gS') = emitE exp (Data.Map.union gB gV) gF gI nextReg nextLab gS in
        if Data.Map.member id gB then (gV, Data.Map.insert id res gB, nextReg', nextLab', code', gS', phiList)
        else (Data.Map.insert id res gV, gB, nextReg', nextLab', code', gS', phiList)

emitS (Incr pos id) gV gF gI gB nextReg nextLab gS phiLab phiList =
    let dest = (RegInt, nextReg) in
        if Data.Map.member id gB then
            (gV, Data.Map.insert id (Right dest) gB, nextReg + 1, nextLab, opCode (PlusOp dest (gB ! id) (Left (ConstInt 1))), gS, phiList)
        else
            (Data.Map.insert id (Right dest) gV, gB, nextReg + 1, nextLab, opCode (PlusOp dest (gV ! id) (Left (ConstInt 1))), gS, phiList)

emitS (Decr pos id) gV gF gI gB nextReg nextLab gS phiLab phiList =
    let dest = (RegInt, nextReg) in
        if Data.Map.member id gB then
            (gV, Data.Map.insert id (Right dest) gB, nextReg + 1, nextLab, opCode (MinusOp dest (gB ! id) (Left (ConstInt 1))), gS, phiList)
        else
            (Data.Map.insert id (Right dest) gV, gB, nextReg + 1, nextLab, opCode (MinusOp dest (gV ! id) (Left (ConstInt 1))), gS, phiList)

emitS (Ret _ exp) gV gF gI gB nextReg nextLab gS phiLab phiList =
    let (res, code', nextReg', nextLab', gS') = emitE exp (Data.Map.union gB gV) gF gI nextReg nextLab gS in
        case phiLab of
            Nothing -> (gV, gB, nextReg', nextLab' + 1, code' . opCode (RetOp res) . opCode (LabelOp nextLab'), gS', phiList)
            Just (Right label) -> (gV, gB, nextReg', nextLab' + 1, code' . opCode (GoOp label) . opCode (LabelOp nextLab'), gS', ((res, nextLab' - 1) : phiList))
            Just (Left (lTrue, lFalse)) -> (gV, gB, nextReg', nextLab' + 1, code' . opCode (CondGoOp res lTrue lFalse) . opCode (LabelOp nextLab'), gS', phiList)
        -- (gV, gB, nextReg', nextLab, code' . opCode (RetOp res), gS')

emitS (VRet pos) gV gF gI gB nextReg nextLab gS phiLab phiList =
    case phiLab of
        Nothing -> (gV, gB, nextReg, nextLab + 1, opCode (RetOp (Left ConstVoid)) . opCode (LabelOp nextLab), gS, phiList)
        Just (Right label) -> (gV, gB, nextReg, nextLab + 1, opCode (GoOp label) . opCode (LabelOp nextLab), gS, phiList)
        -- Just (Left (lTrue, lFalse)) -> nie powinno się stać

emitS (Cond _ exp stmt) gV gF gI gB nextReg nextLab gS phiLab phiList =
    let (resExp, codeExp, nextRegExp, nextLabExp, gSExp) = emitE exp (Data.Map.union gB gV) gF gI nextReg (nextLab + 1) gS in
        let (gVStmt, gBStmt, nextRegStmt, nextLabStmt, codeStmt, gSStmt, phiListStmt) = emitS stmt gV gF gI gB nextRegExp nextLabExp gSExp phiLab phiList in
            let (nextRegPhiV, codePhiV, gVPhi) = phi (Data.Map.toList gV) (nextLab - 1, gV) (nextLabStmt - 1, gVStmt) nextRegStmt noCode Data.Map.empty in
                let (nextRegPhiB, codePhiB, gBPhi) = phi (Data.Map.toList gB) (nextLab - 1, gB) (nextLabStmt - 1, gBStmt) nextRegPhiV noCode Data.Map.empty in

                    (gVPhi, gBPhi, nextRegPhiB, nextLabStmt + 1,
                    codeExp
                    . opCode (CondGoOp resExp nextLab nextLabStmt)  -- if res goto LTrue else goto LFalse

                    . opCode (LabelOp nextLab)                      -- LTrue (potrzebne tylko dla LLVM)
                    . codeStmt                                      -- stmt
                    . opCode (GoOp nextLabStmt)                     -- goto LFalse

                    . opCode (LabelOp nextLabStmt)                  -- LFalse
                    . codePhiV . codePhiB,
                    gSStmt, phiListStmt)

emitS (CondElse pos exp stmt1 stmt2) gV gF gI gB nextReg nextLab gS phiLab phiList =
    let (res, code', nextReg', nextLab', gS') = emitE exp (Data.Map.union gB gV) gF gI nextReg (nextLab + 1) gS in
        let (gV1, gB1, nextReg1, nextLab1, code1, gS1, phiList1) = emitS stmt1 gV gF gI gB nextReg' nextLab' gS' phiLab phiList in
            let (gV2, gB2, nextReg2, nextLab2, code2, gS2, phiList2) = emitS stmt2 gV gF gI gB nextReg1 (nextLab1 + 1) gS1 phiLab phiList1 in

                let (nextRegPhiV, codePhiV, gVPhi) = phi (Data.Map.toList gV) (nextLab1 - 1, gV1) (nextLab2 - 1, gV2) nextReg2 noCode Data.Map.empty in
                    let (nextRegPhiB, codePhiB, gBPhi) = phi (Data.Map.toList gB) (nextLab1 - 1, gB1) (nextLab2 - 1, gB2) nextRegPhiV noCode Data.Map.empty in

                        (gVPhi, gBPhi, nextRegPhiB, nextLab2 + 1,
                        code'
                        . opCode (CondGoOp res nextLab nextLab1)    -- if res goto LTrue else goto LFalse

                        . opCode (LabelOp nextLab)                  -- LTrue:
                        . code1                                     -- stmt1
                        . opCode (GoOp nextLab2)                    -- goto LEnd (potrzebne tylko dla LLVM)

                        . opCode (LabelOp nextLab1)                 -- LFalse: (potrzebne tylko dla LLVM)
                        . code2                                     -- stmt2
                        . opCode (GoOp nextLab2)                    -- goto LEnd

                        . opCode (LabelOp nextLab2)                 -- LEnd:
                        . codePhiV . codePhiB,
                        gS2, phiList2)

emitS (While _ exp stmt) gV gF gI gB nextReg nextLab gS phiLab phiList =
            let (resExp, codeExp, nextRegExp, nextLabExp, gSExp) = emitE exp (Data.Map.union gB gV) gF gI nextReg (nextLab + 1) gS in
                let (gVStmt, gBStmt, nextRegStmt, nextLabStmt, codeStmt, gSStmt, phiListStmt) = emitS stmt gV gF gI gB nextRegExp (nextLabExp + 1) gSExp phiLab phiList in

            let (nextRegPhiV, codePhiV, gVPhi) = phi (Data.Map.toList gV) (nextLab - 1, gV) (nextLabStmt - 1, gVStmt) nextRegStmt noCode Data.Map.empty in
                let (nextRegPhiB, codePhiB, gBPhi) = phi (Data.Map.toList gB) (nextLab - 1, gB) (nextLabStmt - 1, gBStmt) nextRegPhiV noCode Data.Map.empty in

            let (resExp', codeExp', nextRegExp', _, _) = emitE exp (Data.Map.union gBPhi gVPhi) gF gI nextReg (nextLab + 1) gS in
                let (gVStmt', gBStmt', nextRegStmt', nextLabStmt', codeStmt', _, phiListStmt') = emitS stmt gVPhi gF gI gBPhi nextRegExp (nextLabExp + 1) gSExp phiLab phiList in

            (gVPhi, gBPhi, nextRegPhiB, nextLabStmt + 1,
            opCode (GoOp nextLab)                               -- goto L2

            . opCode (LabelOp nextLab)                          -- L2:
            . codePhiV
            . codePhiB
            . codeExp'                                          -- condition code
            . opCode (CondGoOp resExp nextLabExp nextLabStmt)   -- if res goto L1 else goto LEnd

            . opCode (LabelOp nextLabExp)                       -- L1:
            . codeStmt'                                         -- body
            . opCode (GoOp nextLab)                             -- goto L2 (potrzebne tylko dla LLVM)

            . opCode (LabelOp nextLabStmt),                     -- LEnd (potrzebne tylko dla LLVM)
            gSExp, phiListStmt')

emitS (SExp _ exp) gV gF gI gB nextReg nextLab gS phiLab phiList =
    let (res, code', nextReg', nextLab', gS') = emitE exp (Data.Map.union gB gV) gF gI nextReg nextLab gS in
        (gV, gB, nextReg', nextLab', code', gS', phiList)

---------------------------------------------------------------------------------

storeDFS :: [TopDef] -> FEnv -> IEnv -> (FEnv, IEnv)
storeDFS defs gF gI = case defs of
    [] -> (gF, gI)
    (FnDef pos t id args block : rest) ->
        storeDFS rest (Data.Map.insert id (typeRegType t) gF) gI
    (InlFnDef pos t id args block : rest) ->
        storeDFS rest gF (Data.Map.insert id (t, args, block) gI)

mapArgs :: [Arg] -> VEnv -> RegNum -> [Reg] -> (VEnv, RegNum, [Reg])
mapArgs args gV nextReg argList = case args of
    [] -> (gV, nextReg, reverse argList)
    (Arg pos t id : rest) ->
        let dest = (typeRegType t, nextReg) in
            mapArgs rest (Data.Map.insert id (Right dest) gV) (nextReg + 1) (dest : argList)

mapArgsInl :: [Arg] -> [Res] -> VEnv -> VEnv
mapArgsInl args results gV =
    case (args, results) of
        ([], _) -> gV
        ((Arg pos t id) : restArgs, res : restRes) ->
            mapArgsInl restArgs restRes (Data.Map.insert id res gV)

emitDF :: TopDef -> FEnv -> IEnv -> Label -> SEnv -> (Label, Code, SEnv)
emitDF (FnDef pos t id args block) gF gI nextLab gS =
    let (gB, nextReg, argList) = mapArgs args Data.Map.empty 0 [] in
        let (gV', gB', nextReg', nextLab', code', gS', _) = emitB block Data.Map.empty gF gI gB nextReg (nextLab + 1) gS Nothing [] in
            case t of
                Str _ -> let dest = (RegStr, nextReg') in
                    if Data.Map.member "" gS' then
                        (nextLab',
                        opCode (FunOp id (typeRegType t) argList)
                        . opCode (LabelOp nextLab)
                        . code'
                        . opCode (BitcastOp dest 0 (gS'! ""))
                        . opCode (RetOp (Right (RegStr, nextReg')))
                        . opCode EndFunOp,
                        gS')
                    else
                        let idx = toInteger (Data.Map.size gS') in
                            (nextLab',
                            opCode (FunOp id (typeRegType t) argList)
                            . opCode (LabelOp nextLab)
                            . code'
                            . opCode (BitcastOp dest 0 idx)
                            . opCode (RetOp (Right (RegStr, nextReg')))
                            . opCode EndFunOp,
                            Data.Map.insert "" idx gS')
                _ ->
                    (nextLab',
                    opCode (FunOp id (typeRegType t) argList)
                    . opCode (LabelOp nextLab)
                    . code'
                    . opCode (RetOp (typeDefault t))
                    . opCode EndFunOp,
                    gS')

emitDF (InlFnDef pos t id args block) gF gI nextLab gS = (nextLab, noCode, gS)
    -- let (nextLab', code', gS') = emitDF (FnDef pos t id args block) gF gI nextLab gS in
    --     (nextLab, noCode, gS') -- spamiętuję napisy, ale nie generuję kodu

emitDFS :: [TopDef] -> FEnv -> IEnv -> Label -> SEnv -> (Code, SEnv)
emitDFS defs gF gI nextLab gS = case defs of
    [] -> (noCode, gS)
    (def : rest) ->
        let (nextLab', code', gS') = emitDF def gF gI nextLab gS in
            let (code'', gS'') = emitDFS rest gF gI nextLab' gS' in
                (code' . code'', gS'')

---------------------------------------------------------------------------------

emitP :: Program -> ([Op], SEnv)
emitP (Program _ defs) =
    let (gF, gI) = storeDFS defs initFEnv initIEnv in
        let (code, gS) = emitDFS defs gF gI 1 Data.Map.empty in
            (code [], gS)

initFEnv :: FEnv
initFEnv = Data.Map.fromList [
    (Ident "printInt", RegVoid),
    (Ident "printString", RegVoid),
    (Ident "error", RegVoid),
    (Ident "readInt", RegInt),
    (Ident "readString", RegStr)
    ]

initIEnv :: IEnv
initIEnv = Data.Map.empty
