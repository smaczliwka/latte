module Emiter where

import AbsLatte
import Data.Map
import Data.Set (Set, fromList, member)

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

type StrNum = Integer
type SEnv = Map String StrNum

emitArgs :: [Expr] -> VEnv -> FEnv -> ([Res], Code, RegNum, Label, SEnv) -> ([Res], Code, RegNum, Label, SEnv)
emitArgs exps gV gF (args, codes, nextReg, nextLab, gS) = case exps of
    [] -> (reverse args, codes, nextReg, nextLab, gS)
    (exp : rest) ->
        let (arg, code, nextReg', nextLab', gS') = emitE exp gV gF nextReg nextLab gS in
            emitArgs rest gV gF (arg : args, codes . code, nextReg', nextLab', gS')

emitE :: Expr -> VEnv -> FEnv -> RegNum -> Label -> SEnv -> (Res, Code, RegNum, Label, SEnv)

emitE (EVar pos id) gV gF nextReg nextLab gS = (gV ! id, noCode, nextReg, nextLab, gS)

emitE (ELitInt pos val) gV gF nextReg nextLab gS = (Left (ConstInt val), noCode, nextReg, nextLab, gS)

emitE (ELitTrue pos) gV gF nextReg nextLab gS = (Left (ConstBool True), noCode, nextReg, nextLab, gS)
emitE (ELitFalse pos) gV gF nextReg nextLab gS = (Left (ConstBool False), noCode, nextReg, nextLab, gS)

emitE (EApp pos id exps) gV gF nextReg nextLab gS =
    let (args, codes, nextReg', nextLab', gS') = emitArgs exps gV gF ([], noCode, nextReg, nextLab, gS) in
        let regType = gF ! id in
            case regType of
                RegVoid -> (Left ConstVoid, codes . opCode (CallVoidOp id args), nextReg', nextLab', gS')
                _ ->
                    let dest = (regType, nextReg') in
                        (Right dest, codes . opCode (CallOp dest id args), nextReg' + 1, nextLab', gS')

emitE (EString pos str) gV gF nextReg nextLab gS =
    let dest = (RegStr, nextReg) in
        let len = toInteger (length str) in
            if Data.Map.member str gS then
                (Right dest, opCode (BitcastOp dest len (gS ! str)), nextReg + 1, nextLab, gS)
            else
                let idx = toInteger (Data.Map.size gS) in
                    (Right dest, opCode (BitcastOp dest len idx), nextReg + 1, nextLab, Data.Map.insert str idx gS)

emitE (Not pos exp) gV gF nextReg nextLab gS = -- negacja binarna
    let (res, code, nextReg', nextLab', gS') = emitE exp gV gF nextReg nextLab gS in
        (Right (RegBool, nextReg'), code . opCode (NotOp (RegBool, nextReg') res), nextReg' + 1, nextLab', gS')

emitE (Neg pos exp) gV gF nextReg nextLab gS = -- minus
    let (res, code, nextReg', nextLab', gS') = emitE exp gV gF nextReg nextLab gS in
        (Right (RegInt, nextReg'), code . opCode (NegOp (RegInt, nextReg') res), nextReg' + 1, nextLab', gS')

emitE (EMul pos exp1 op exp2) gV gF nextReg nextLab gS =
    let (res1, code1, nextReg1, nextLab1, gS1) = emitE exp1 gV gF nextReg nextLab gS in
        let (res2, code2, nextReg2, nextLab2, gS2) = emitE exp2 gV gF nextReg1 nextLab1 gS1 in
            let dest = (RegInt, nextReg2) in
                case op of
                    Times _ -> (Right dest, code1 . code2 . opCode (TimesOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    Div _ -> (Right dest, code1 . code2 . opCode (DivOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    Mod _ -> (Right dest, code1 . code2 . opCode (ModOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)

emitE (EAdd pos exp1 op exp2) gV gF nextReg nextLab gS =
    let (res1, code1, nextReg1, nextLab1, gS1) = emitE exp1 gV gF nextReg nextLab gS in
        let (res2, code2, nextReg2, nextLab2, gS2) = emitE exp2 gV gF nextReg1 nextLab1 gS1 in
            let dest = (resRegType res1, nextReg2) in
                case op of
                    Plus _ -> (Right dest, code1 . code2 . opCode (PlusOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    Minus _ -> (Right dest, code1 . code2 . opCode (MinusOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)

-- przewiduje porównywanie wszystkich typów poza void
emitE (ERel pos exp1 op exp2) gV gF nextReg nextLab gS =
    let (res1, code1, nextReg1, nextLab1, gS1) = emitE exp1 gV gF nextReg nextLab gS in
        let (res2, code2, nextReg2, nextLab2, gS2) = emitE exp2 gV gF nextReg1 nextLab1 gS1 in
            let dest = (RegBool, nextReg2) in
                case op of
                    LTH _ -> (Right dest, code1 . code2 . opCode (LTHOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    LE _ -> (Right dest, code1 . code2 . opCode (LEOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    GTH _ -> (Right dest, code1 . code2 . opCode (GTHOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    GE _ -> (Right dest, code1 . code2 . opCode (GEOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    EQU _ -> (Right dest, code1 . code2 . opCode (EQUOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)
                    NE _ -> (Right dest, code1 . code2 . opCode (NEOp dest res1 res2), nextReg2 + 1, nextLab2, gS2)

emitE (EAnd pos exp1 exp2) gV gF nextReg nextLab gS =
    let (lTrue, lFalse) = (nextLab, nextLab + 1) in
        let (code, nextReg', nextLab', gS') = emitL (EAnd pos exp1 exp2) gV gF nextReg (nextLab + 2) gS lTrue lFalse in
            (Right (RegBool, nextReg'),
            code
            . opCode (LabelOp lTrue)
            . opCode (GoOp nextLab')
            . opCode (LabelOp lFalse)
            . opCode (GoOp nextLab')
            . opCode (LabelOp nextLab')
            . opCode (PhiOp (RegBool, nextReg') [(Left (ConstBool True), lTrue), (Left (ConstBool False), lFalse)]),
            nextReg' + 1, nextLab' + 1, gS')

emitE (EOr pos exp1 exp2) gV gF nextReg nextLab gS =
    let (lTrue, lFalse) = (nextLab, nextLab + 1) in
        let (code, nextReg', nextLab', gS') = emitL (EOr pos exp1 exp2) gV gF nextReg (nextLab + 2) gS lTrue lFalse in
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

emitL :: Expr -> VEnv -> FEnv -> RegNum -> Label -> SEnv -> Label -> Label -> (Code, RegNum, Label, SEnv)

emitL (EVar pos id) gV gF nextReg nextLab gS lTrue lFalse =
    (opCode (CondGoOp (gV ! id) lTrue lFalse), nextReg, nextLab, gS)

emitL (ELitTrue pos) gV gF nextReg nextLab gS lTrue lFalse =
    (opCode (GoOp lTrue), nextReg, nextLab, gS)

emitL (ELitFalse pos) gV gF nextReg nextLab gS lTrue lFalse =
    (opCode (GoOp lTrue), nextReg, nextLab, gS)

emitL (EApp pos id exps) gV gF nextReg nextLab gS lTrue lFalse =
    let (args, codes, nextReg', nextLab', gS') = emitArgs exps gV gF ([], noCode, nextReg, nextLab, gS) in
        let dest = (gF ! id, nextReg') in
            (codes
            . opCode (CallOp dest id args)
            . opCode (CondGoOp (Right dest) lTrue lFalse),
            nextReg' + 1, nextLab', gS')

emitL (Not pos exp) gV gF nextReg nextLab gS lTrue lFalse = -- negacja binarna
    emitL exp gV gF nextReg nextLab gS lFalse lTrue

emitL (ERel pos exp1 op exp2) gV gF nextReg nextLab gS lTrue lFalse =
    let (res1, code1, nextReg1, nextLab1, gS1) = emitE exp1 gV gF nextReg nextLab gS in
        let (res2, code2, nextReg2, nextLab2, gS2) = emitE exp2 gV gF nextReg1 nextLab1 gS1 in
            let dest = (RegBool, nextReg2) in
                let condGoCode = opCode (CondGoOp (Right dest) lTrue lFalse) in
                    case op of
                        LTH _ -> (code1 . code2 . opCode (LTHOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)
                        LE _ -> (code1 . code2 . opCode (LEOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)
                        GTH _ -> (code1 . code2 . opCode (GTHOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)
                        GE _ -> (code1 . code2 . opCode (GEOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)
                        EQU _ -> (code1 . code2 . opCode (EQUOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)
                        NE _ -> (code1 . code2 . opCode (NEOp dest res1 res2) . condGoCode, nextReg2 + 1, nextLab2, gS2)

emitL (EAnd pos exp1 exp2) gV gF nextReg nextLab gS lTrue lFalse =
    -- lP = nextLab
    let (code1, nextReg1, nextLab1, gS1) = emitL exp1 gV gF nextReg (nextLab + 1) gS nextLab lFalse in
        let (code2, nextReg2, nextLab2, gS2) = emitL exp2 gV gF nextReg1 nextLab1 gS1 lTrue lFalse in
            (code1
            . opCode (LabelOp nextLab)
            . code2,
            nextReg2, nextLab2, gS2)

emitL (EOr pos exp1 exp2) gV gF nextReg nextLab gS lTrue lFalse =
    -- lP = nextLab
    let (code1, nextReg1, nextLab1, gS1) = emitL exp1 gV gF nextReg (nextLab + 1) gS lTrue nextLab in
        let (code2, nextReg2, nextLab2, gS2) = emitL exp2 gV gF nextReg1 nextLab1 gS1 lTrue lFalse in
            (code1
            . opCode (LabelOp nextLab)
            . code2,
            nextReg2, nextLab2, gS2)

---------------------------------------------------------------------------------

emitB :: Block -> VEnv -> FEnv -> VEnv -> RegNum -> Label -> SEnv -> (VEnv, VEnv, RegNum, Label, Code, SEnv)

emitB block gV gF gB nextReg nextLab gS = case block of
    Block pos (stmt : rest) ->
        let (gV', gB', nextReg', nextLab', code', gS') = emitS stmt gV gF gB nextReg nextLab gS in
            let (gV'', gB'', nextReg'', nextLab'', code'', gS'') = emitB (Block pos rest) gV' gF gB' nextReg' nextLab' gS' in
                (gV'', gB'', nextReg'', nextLab'', code' . code'', gS'')
    Block pos [] -> (gV, gB, nextReg, nextLab, noCode, gS)


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

emitS :: Stmt -> VEnv -> FEnv -> VEnv -> RegNum -> Label -> SEnv -> (VEnv, VEnv, RegNum, Label, Code, SEnv)

emitS (Empty _) gV gF gB nextReg nextLab gS = (gV, gB, nextReg, nextLab, noCode, gS)

emitS (BStmt _ block) gV gF gB nextReg nextLab gS =
    let (gV', gB', nextReg', nextLab', code', gS') = emitB block (Data.Map.union gB gV) gF Data.Map.empty nextReg nextLab gS in
        (Data.Map.union (Data.Map.difference gV' gB) gV, Data.Map.intersection gV' gB, nextReg', nextLab', code', gS')

emitS (Decl pos t items) gV gF gB nextReg nextLab gS =
    case (t, items) of
        (_, []) -> (gV, gB, nextReg, nextLab, noCode, gS)

        (_, Init p id exp : rest) ->
            let (res, code', nextReg', nextLab', gS') = emitE exp (Data.Map.union gB gV) gF nextReg nextLab gS in
                let (gV'', gB'', nextReg'', nextLab'', code'', gS'') = emitS (Decl pos t rest) gV gF (Data.Map.insert id res gB) nextReg' nextLab' gS' in
                    (gV'', gB'', nextReg'', nextLab'', code' . code'', gS'')

        (Str _, NoInit p id : rest) ->
            if Data.Map.member "" gS then
                let code' = opCode (BitcastOp (RegStr, nextReg) 0 (gS ! "")) in
                    let (gV'', gB'', nextReg'', nextLab'', code'', gS'') = emitS (Decl pos t rest) gV gF (Data.Map.insert id (Right (RegStr, nextReg)) gB) (nextReg + 1) nextLab gS in
                        (gV'', gB'', nextReg'', nextLab'', code' . code'', gS'')
            else
                let idx = toInteger (Data.Map.size gS) in
                    let code' = opCode (BitcastOp (RegStr, nextReg) 0 idx) in
                        let (gV'', gB'', nextReg'', nextLab'', code'', gS'') = emitS (Decl pos t rest) gV gF (Data.Map.insert id (Right (RegStr, nextReg)) gB) (nextReg + 1) nextLab (Data.Map.insert "" idx gS) in
                            (gV'', gB'', nextReg'', nextLab'', code' . code'', gS'')

        (_, NoInit p id : rest) ->
            emitS (Decl pos t rest) gV gF (Data.Map.insert id (typeDefault t) gB) nextReg nextLab gS


emitS (Ass pos id exp) gV gF gB nextReg nextLab gS =
    let (res, code', nextReg', nextLab',gS') = emitE exp (Data.Map.union gB gV) gF nextReg nextLab gS in
        if Data.Map.member id gB then (gV, Data.Map.insert id res gB, nextReg', nextLab', code', gS')
        else (Data.Map.insert id res gV, gB, nextReg', nextLab', code', gS')

emitS (Incr pos id) gV gF gB nextReg nextLab gS =
    let dest = (RegInt, nextReg) in
        if Data.Map.member id gB then
            (gV, Data.Map.insert id (Right dest) gB, nextReg + 1, nextLab, opCode (PlusOp dest (gB ! id) (Left (ConstInt 1))), gS)
        else
            (Data.Map.insert id (Right dest) gV, gB, nextReg + 1, nextLab, opCode (PlusOp dest (gV ! id) (Left (ConstInt 1))), gS)

emitS (Decr pos id) gV gF gB nextReg nextLab gS =
    let dest = (RegInt, nextReg) in
        if Data.Map.member id gB then
            (gV, Data.Map.insert id (Right dest) gB, nextReg + 1, nextLab, opCode (MinusOp dest (gB ! id) (Left (ConstInt 1))), gS)
        else
            (Data.Map.insert id (Right dest) gV, gB, nextReg + 1, nextLab, opCode (MinusOp dest (gV ! id) (Left (ConstInt 1))), gS)

emitS (Ret _ exp) gV gF gB nextReg nextLab gS =
    let (res, code', nextReg', nextLab', gS') = emitE exp (Data.Map.union gB gV) gF nextReg nextLab gS in
        (gV, gB, nextReg', nextLab' + 1, code' . opCode (RetOp res) . opCode (LabelOp nextLab'), gS')
        -- (gV, gB, nextReg', nextLab, code' . opCode (RetOp res), gS')

emitS (VRet pos) gV gF gB nextReg nextLab gS = (gV, gB, nextReg, nextLab, opCode (RetOp (Left ConstVoid)), gS)

emitS (Cond _  exp stmt) gV gF gB nextReg nextLab gS =
    let (resExp, codeExp, nextRegExp, nextLabExp, gSExp) = emitE exp (Data.Map.union gB gV) gF nextReg (nextLab + 1) gS in
        let (gVStmt, gBStmt, nextRegStmt, nextLabStmt, codeStmt, gSStmt) = emitS stmt gV gF gB nextRegExp nextLabExp gSExp in
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
                    gSStmt)

emitS (CondElse pos exp stmt1 stmt2) gV gF gB nextReg nextLab gS =
    let (res, code', nextReg', nextLab', gS') = emitE exp (Data.Map.union gB gV) gF nextReg (nextLab + 1) gS in
        let (gV1, gB1, nextReg1, nextLab1, code1, gS1) = emitS stmt1 gV gF gB nextReg' nextLab' gS' in
            let (gV2, gB2, nextReg2, nextLab2, code2, gS2) = emitS stmt2 gV gF gB nextReg1 (nextLab1 + 1) gS1 in

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
                        gS2)

emitS (While _ exp stmt) gV gF gB nextReg nextLab gS =
            let (gVStmt, gBStmt, nextRegStmt, nextLabStmt, codeStmt, gSStmt) = emitS stmt gV gF gB nextReg (nextLab + 1) gS in
                let (resExp, codeExp, nextRegExp, nextLabExp, gSExp) = emitE exp (Data.Map.union gB gV) gF nextRegStmt (nextLabStmt + 1) gSStmt in

            let (nextRegPhiV, codePhiV, gVPhi) = phi (Data.Map.toList gV) (nextLab - 1, gV) (nextLabStmt - 1, gVStmt) nextRegExp noCode Data.Map.empty in
                let (nextRegPhiB, codePhiB, gBPhi) = phi (Data.Map.toList gB) (nextLab - 1, gB) (nextLabStmt - 1, gBStmt) nextRegPhiV noCode Data.Map.empty in

            let (gVStmt', gBStmt', nextRegStmt', nextLabStmt', codeStmt', _) = emitS stmt gVPhi gF gBPhi nextReg (nextLab + 1) gS in
                let (resExp', codeExp', nextRegExp', _, _) = emitE exp (Data.Map.union gBPhi gVPhi) gF nextRegStmt (nextLabStmt + 1) gS in

            (gVPhi, gBPhi, nextRegPhiB, nextLabExp + 2,
            opCode (GoOp nextLabStmt)                               -- goto L2

            . opCode (LabelOp nextLab)                              -- L1:
            . codeStmt'                                             -- body
            . opCode (GoOp nextLabStmt)                             -- goto L2 (potrzebne tylko dla LLVM)

            . opCode (LabelOp nextLabStmt)                          -- L2:
            . codePhiV
            . codePhiB
            . codeExp'                                              -- condition code
            . opCode (CondGoOp resExp nextLab (nextLabExp + 1))    -- if res goto L1 else goto LEnd

            . opCode (LabelOp (nextLabExp + 1)),                   -- LEnd (potrzebne tylko dla LLVM)
            gSExp)

emitS (SExp _ exp) gV gF gB nextReg nextLab gS =
    let (res, code', nextReg', nextLab', gS') = emitE exp (Data.Map.union gB gV) gF nextReg nextLab gS in
        (gV, gB, nextReg', nextLab', code', gS')

---------------------------------------------------------------------------------

storeDFS :: [TopDef] -> FEnv -> FEnv
storeDFS defs gF = case defs of
    [] -> gF
    (FnDef pos t id args block : rest) ->
        storeDFS rest (Data.Map.insert id (typeRegType t) gF)

mapArgs :: [Arg] -> VEnv -> RegNum -> [Reg] -> (VEnv, RegNum, [Reg])
mapArgs args gV nextReg argList = case args of
    [] -> (gV, nextReg, reverse argList)
    (Arg pos t id : rest) ->
        let dest = (typeRegType t, nextReg) in
            mapArgs rest (Data.Map.insert id (Right dest) gV) (nextReg + 1) (dest : argList)

emitDF :: TopDef -> FEnv -> Label -> SEnv -> (Label, Code, SEnv)
emitDF (FnDef pos t id args block) gF nextLab gS =
    let (gB, nextReg, argList) = mapArgs args Data.Map.empty 0 [] in
        let (gV', gB', nextReg', nextLab', code', gS') = emitB block Data.Map.empty gF gB nextReg (nextLab + 1) gS in
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
                        let idx = toInteger (size gS') in
                            (nextLab',
                            opCode (FunOp id (typeRegType t) argList)
                            . opCode (LabelOp nextLab)
                            . code'
                            . opCode (BitcastOp dest 0 idx)
                            . opCode (RetOp (Right (RegStr, nextReg')))
                            . opCode EndFunOp,
                            insert "" idx gS')
                _ ->
                    (nextLab',
                    opCode (FunOp id (typeRegType t) argList)
                    . opCode (LabelOp nextLab)
                    . code'
                    . opCode (RetOp (typeDefault t))
                    . opCode EndFunOp,
                    gS')

emitDFS :: [TopDef] -> FEnv -> Label -> SEnv -> (Code, SEnv)
emitDFS defs gF nextLab gS = case defs of
    [] -> (noCode, gS)
    (def : rest) ->
        let (nextLab', code', gS') = emitDF def gF nextLab gS in
            let (code'', gS'') = emitDFS rest gF nextLab' gS' in
                (code' . code'', gS'')

removeRets :: [Op] -> [Op] -> [Op]
removeRets ops acc = case (ops, acc) of
    ([], _) -> reverse acc
    (RetOp _ : restOps, RetOp _ : restAcc) -> removeRets restOps acc
    (op : restOps, _) -> removeRets restOps (op : acc)

reacheable :: [Op] -> [Label] -> Set Label
reacheable ops acc =
    case ops of
        [] -> Data.Set.fromList acc
        (GoOp label : rest) -> reacheable rest (label : acc)
        (CondGoOp _ label1 label2 : rest) -> reacheable rest (label1 : label2 : acc)
        (_ : rest) -> reacheable rest acc

removeUnreachable :: [Op] -> Bool -> Set Label -> [Op] -> [Op]
removeUnreachable ops last reach acc =
    case (ops, last) of
        ([], _) -> reverse acc
        (FunOp id regType regs : LabelOp label : rest, _) ->
            removeUnreachable rest True reach (LabelOp label : FunOp id regType regs : acc)
        (EndFunOp : rest, _) -> removeUnreachable rest last reach (EndFunOp : acc)
        (LabelOp label : rest, _) ->
            if Data.Set.member label reach then removeUnreachable rest True reach (LabelOp label : acc)
            else removeUnreachable rest False reach acc
        (op : rest, True) -> removeUnreachable rest last reach (op : acc)
        (op : rest, False) -> removeUnreachable rest last reach acc

replacement :: Map Reg Reg -> Res -> Res
replacement repl res =
    case res of
        Left const -> Left const
        Right reg ->
            if Data.Map.member reg repl then Right (repl ! reg)
            else Right reg

replacementPhi :: Map Reg Reg -> (Res, Label) -> (Res, Label)
replacementPhi repl (res, label) = (replacement repl res, label)

replace :: Map Reg Reg -> Op -> Op
replace repl op =
    case op of
        PlusOp reg res1 res2 -> PlusOp reg (replacement repl res1) (replacement repl res2)
        MinusOp reg res1 res2 -> MinusOp reg (replacement repl res1) (replacement repl res2)
        TimesOp reg res1 res2 -> TimesOp reg (replacement repl res1) (replacement repl res2)
        DivOp reg res1 res2 -> DivOp reg (replacement repl res1) (replacement repl res2)
        ModOp reg res1 res2 -> ModOp reg (replacement repl res1) (replacement repl res2)
        LTHOp reg res1 res2 -> LTHOp reg (replacement repl res1) (replacement repl res2)
        LEOp reg res1 res2 -> LEOp reg (replacement repl res1) (replacement repl res2)
        GTHOp reg res1 res2 -> GTHOp reg (replacement repl res1) (replacement repl res2)
        GEOp reg res1 res2 -> GEOp reg (replacement repl res1) (replacement repl res2)
        EQUOp reg res1 res2 -> EQUOp reg (replacement repl res1) (replacement repl res2)
        NEOp reg res1 res2 -> NEOp reg (replacement repl res1) (replacement repl res2)
        -- AndOp i
        -- OrOp nieużywane
        NotOp reg res -> NotOp reg (replacement repl res)
        NegOp reg res -> NegOp reg (replacement repl res)
        -- GoOp nie korzysta z rejestrów
        CondGoOp res label1 label2 -> CondGoOp (replacement repl res) label1 label2
        CallOp reg id results -> CallOp reg id (Prelude.map (replacement repl) results)
        RetOp res -> RetOp (replacement repl res)
        -- LabelOp nie korzysta z rejestrów
        PhiOp reg pairs -> PhiOp reg (Prelude.map (replacementPhi repl) pairs) -- trzeba jeszcze usuwać powtórzenia
        -- FunOp nie korzysta z rejestrów
        -- BitcastOp nie korzysta z rejestrów
        -- EndFunOp nie korzysta z rejestrów
        CallVoidOp id results -> CallVoidOp id (Prelude.map (replacement repl) results)
        op -> op -- cała reszta

fakeReg :: Reg
fakeReg = (RegVoid, -1)

fakeDest :: Op -> Maybe (Op, Reg)
fakeDest op =
    case op of
        PlusOp reg res1 res2 -> Just (PlusOp fakeReg res1 res2, reg)
        MinusOp reg res1 res2 -> Just (MinusOp fakeReg res1 res2, reg)
        TimesOp reg res1 res2 -> Just (TimesOp fakeReg res1 res2, reg)
        DivOp reg res1 res2 -> Just (DivOp fakeReg res1 res2, reg)
        ModOp reg res1 res2 -> Just (ModOp fakeReg res1 res2, reg)
        LTHOp reg res1 res2 -> Just (LTHOp fakeReg res1 res2, reg)
        LEOp reg res1 res2 -> Just (LEOp fakeReg res1 res2, reg)
        GTHOp reg res1 res2 -> Just (GTHOp fakeReg res1 res2, reg)
        GEOp reg res1 res2 -> Just (GEOp fakeReg res1 res2, reg)
        EQUOp reg res1 res2 -> Just (EQUOp fakeReg res1 res2, reg)
        NEOp reg res1 res2 -> Just (NEOp fakeReg res1 res2, reg)
        -- AndOp i
        -- OrOp nieużywane
        NotOp reg res -> Just (NotOp fakeReg res, reg)
        NegOp reg res -> Just (NegOp fakeReg res, reg)
        -- GoOp nie umieszcza wyniku w rejestrze
        -- CondGoOp nie umieszcza wyniku w rejestrze
        -- CallOp reg id results -> Just (CallOp fakeReg id results, reg) <----------- nie chcemy spamiętywać wyników calli
        -- RetOp nie umieszcza wyniku w rejestrze
        -- LabelOp nie umieszcza wyniku w rejestrze
        PhiOp reg pairs -> Just (PhiOp fakeReg pairs, reg)
        -- FunOp nie umieszcza wyniku w rejestrze
        BitcastOp reg len idx -> Just (BitcastOp fakeReg len idx, reg)
        -- EndFunOp nie umieszcza wyniku w rejestrze
        -- CallVoidOp nie umieszcza wyniku w rejestrze
        op -> Nothing -- cała reszta nie umieszcza wyniku w rejestrze

lcse :: Map Op Reg -> Map Reg Reg -> [Op] -> [Op] -> [Op]
lcse comp repl acc ops =
    case ops of

        [FunOp id regType regs] -> [FunOp id regType regs]
        [EndFunOp] -> [EndFunOp]

        [] -> reverse acc
        (op : rest) ->
            let opRepl = replace repl op in
                case fakeDest opRepl of
                    Nothing -> lcse comp repl (opRepl : acc) rest -- operacja nie umieszcza wyniku w rejestrze
                    Just (opRepl', dest) ->
                        case Data.Map.lookup opRepl' comp of
                            Just dest' -> lcse comp (insert dest dest' repl) acc rest -- wyrażenie policzone wcześniej i wynik w dest'
                            Nothing -> lcse (insert opRepl' dest comp) repl (opRepl : acc) rest -- wyrażenie nie policzone wcześniej

optimize :: [Op] -> [Op]
optimize ops =
    let reach = reacheable ops [] in
        removeUnreachable ops True reach []

splitIntoFunctions :: [Op] -> [[Op]] -> [Op] -> [[Op]]
splitIntoFunctions fun acc ops =
    case ops of
        [] -> reverse acc
        (EndFunOp : rest) -> splitIntoFunctions [] ((reverse (EndFunOp : fun)) : acc) rest
        (op : rest) -> splitIntoFunctions (op : fun) acc rest

splitIntoBlocks :: [Op] -> [[Op]] -> [Op] -> [[Op]]
splitIntoBlocks block acc ops =
    case ops of
        [] -> reverse acc
        (GoOp label : rest) -> splitIntoBlocks [] ((reverse (GoOp label : block)) : acc) rest
        (CondGoOp res label1 label2 : rest) -> splitIntoBlocks [] ((reverse (CondGoOp res label1 label2 : block)) : acc)  rest
        (RetOp res : rest) -> splitIntoBlocks [] ((reverse (RetOp res : block)) : acc) rest

        (FunOp id regType regs : rest) -> splitIntoBlocks [] ([FunOp id regType regs] : acc) rest
        (EndFunOp : rest) -> splitIntoBlocks [] ([EndFunOp] : acc) rest

        (op : rest) -> splitIntoBlocks (op : block) acc rest

emitP :: Program -> ([Op], SEnv)
emitP (Program _ defs) =
    let gF = storeDFS defs initFEnv in
        let (code, gS) = emitDFS defs gF 1 Data.Map.empty in
            let code' = Prelude.map (splitIntoBlocks [] []) (splitIntoFunctions [] [] (optimize (code []))) in
                (concat (Prelude.map (lcse Data.Map.empty Data.Map.empty []) (concat code')), gS)
                -- (concat (concat code'), gS)

            -- let code' = splitIntoFunctions [] [] (optimize (code [])) in
            --     (concat code', gS)

            -- (optimize (code []), gS)
            -- (removeRets (code []) [], gS)

initFEnv :: FEnv
initFEnv = Data.Map.fromList [
    (Ident "printInt", RegVoid),
    (Ident "printString", RegVoid),
    (Ident "error", RegVoid),
    (Ident "readInt", RegInt),
    (Ident "readString", RegStr)
    ]

