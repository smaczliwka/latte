module Printer where

import Emiter
import AbsLatte
import Data.Map

instance Show RegType where
    show t = case t of
        RegInt -> "i32"
        RegStr -> "i8*"
        RegBool -> "i1"
        RegVoid -> "void"

showRegType :: Reg -> ShowS
showRegType (t, _) = shows t

showReg :: Reg -> ShowS
showReg (_, i) = showString "%r" . shows i

showRegWithType :: Reg -> ShowS
showRegWithType (t, i) = shows t . showString " %r" . shows i

showLabel :: Label -> ShowS
showLabel i = showString "%l" . shows i

showArgs :: [Reg] -> ShowS
showArgs args = case args of
    [] -> showString ""
    [arg] -> showRegWithType arg
    (arg : rest) -> showRegWithType arg . showString ", " . showArgs rest

showConst :: Const -> ShowS
showConst const = case const of
    ConstInt val -> shows val
    ConstBool True -> shows 1
    ConstBool False -> shows 0
    ConstVoid -> showString ""

showRes :: Res -> ShowS
showRes res = case res of
    Left const -> showConst const
    Right reg -> showReg reg

showResults :: [Res] -> ShowS
showResults results = case results of
    [] -> showString ""
    [res] -> shows (resRegType res) . showChar ' ' . showRes res
    (res : rest) -> shows (resRegType res) . showChar ' ' . showRes res . showString ", " . showResults rest

showPhiNodes :: [(Res, Label)] -> ShowS
showPhiNodes nodes = case nodes of
    [] -> showString ""
    [(res, label)] -> showString "[" . showRes res . showString ", " . showLabel label . showString "]"
    ((res, label) : rest) -> showString "[" . showRes res . showString ", " . showLabel label . showString "], " . showPhiNodes rest

showsOp :: ShowS -> Op -> ShowS
showsOp acc op = case op of
    -- argumenty typu int lub string
    PlusOp dest arg1 arg2 -> case resRegType arg1 of
        RegStr -> acc . showReg dest . showString " = call i8* @_strCat(i8* " . showRes arg1 . showString ", i8* " . showRes arg2 . showString ")\n"
        _ -> acc . showReg dest . showString " = add i32 " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'

    -- argumenty typu int
    MinusOp dest arg1 arg2 -> acc . showReg dest . showString " = sub i32 " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    TimesOp dest arg1 arg2 -> acc . showReg dest . showString " = mul i32 " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    DivOp dest arg1 arg2 -> acc . showReg dest . showString " = sdiv i32 " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    ModOp dest arg1 arg2 -> acc . showReg dest . showString " = srem i32 " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    NegOp dest arg -> acc . showReg dest . showString " = sub i32 0, " . showRes arg . showChar '\n'

    -- argumenty dowolnego typu poza void
    LTHOp dest arg1 arg2 -> case resRegType arg1 of
        RegStr -> acc . showReg dest . showString " = call i1 @_strLTH(i8* " . showRes arg1 . showString ", i8* " . showRes arg2 . showString ")\n"
        RegBool ->  acc . showReg dest . showString " = icmp ult i1 " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
        _ -> acc . showReg dest . showString " = icmp slt " . shows (resRegType arg1) . showString " " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    LEOp dest arg1 arg2 -> case resRegType arg1 of
        RegStr -> acc . showReg dest . showString " = call i1 @_strLE(i8* " . showRes arg1 . showString ", i8* " . showRes arg2 . showString ")\n"
        RegBool ->  acc . showReg dest . showString " = icmp ule i1 " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
        _ -> acc . showReg dest . showString " = icmp sle " . shows (resRegType arg1) . showString " " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    GTHOp dest arg1 arg2 -> case resRegType arg1 of
        RegStr -> acc . showReg dest . showString " = call i1 @_strGTH(i8* " . showRes arg1 . showString ", i8* " . showRes arg2 . showString ")\n"
        RegBool ->  acc . showReg dest . showString " = icmp ugt i1 " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
        _ -> acc . showReg dest . showString " = icmp sgt " . shows (resRegType arg1) . showString " " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    GEOp dest arg1 arg2 ->  case resRegType arg1 of
        RegStr -> acc . showReg dest . showString " = call i1 @_strGE(i8* " . showRes arg1 . showString ", i8* " . showRes arg2 . showString ")\n"
        RegBool ->  acc . showReg dest . showString " = icmp uge i1 " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
        _ -> acc . showReg dest . showString " = icmp sge " . shows (resRegType arg1) . showString " " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    EQUOp dest arg1 arg2 ->  case resRegType arg1 of
        RegStr -> acc . showReg dest . showString " = call i1 @_strEQU(i8* " . showRes arg1 . showString ", i8* " . showRes arg2 . showString ")\n"
        _ -> acc . showReg dest . showString " = icmp eq " . shows (resRegType arg1) . showString " " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    NEOp dest arg1 arg2 ->  case resRegType arg1 of
        RegStr -> acc . showReg dest . showString " = call i1 @_strNE(i8* " . showRes arg1 . showString ", i8* " . showRes arg2 . showString ")\n"
        _ -> acc . showReg dest . showString " = icmp ne " . shows (resRegType arg1) . showString " " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    
    -- argumenty typu bool
    AndOp dest arg1 arg2 -> acc . showReg dest . showString " = and i1 " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    OrOp dest arg1 arg2 -> acc . showReg dest . showString " = or i1 " . showRes arg1 . showString ", " . showRes arg2 . showChar '\n'
    NotOp dest arg -> acc . showReg dest . showString " = xor i1 1, " . showRes arg . showChar '\n'

    CondGoOp arg label1 label2 -> acc . showString "br i1 " . showRes arg . showString ", label " . showLabel label1 . showString ", label " . showLabel label2 . showChar '\n'
    GoOp label -> acc . showString "br label " . showLabel label . showChar '\n'
    CallOp dest (Ident id) args -> acc . showReg dest . showString " = call " . showRegType dest . showString " @". showString id . showString "(" . showResults args . showString ")\n"
    RetOp arg -> acc . showString "ret " . shows (resRegType arg) . showString " " . showRes arg . showChar '\n'
    LabelOp label -> acc . showChar 'l' . shows label . showString ":\n"
    PhiOp dest args -> acc . showReg dest . showString " = phi " . showRegType dest . showString " " . showPhiNodes args . showChar '\n'
    FunOp (Ident id) t args -> acc . showString "define " . shows t . showString " @" . showString id . showString "(" . showArgs args . showString ") {\n"
    BitcastOp dest len num -> acc . showReg dest . showString " = bitcast [" . shows (len + 1) . showString " x i8]* @str" . shows num . showString " to i8*\n"
    EndFunOp -> acc . showString "}\n"
    CallVoidOp (Ident id) args -> acc . showString "call void " . showString " @". showString id . showString "(" . showResults args . showString ")\n"

showsStrLLVM :: ShowS -> (String, Integer) -> ShowS
showsStrLLVM acc (str, num) =
    acc . showString "@str" . shows num . showString " = private constant [" . shows (length str + 1) . showString " x i8] c\"" . showString str . showString "\\00\"\n"

declarations :: ShowS
declarations = showString 
    "declare void @printInt(i32)\n\
    \declare void @printString(i8*)\n\
    \declare void @error()\n\
    \declare i32 @readInt()\n\
    \declare i8* @readString()\n\
    \declare i8* @_strCat(i8*, i8*)\n\
    \declare i1 @_strLTH(i8*, i8*)\n\
    \declare i1 @_strLE(i8*, i8*)\n\
    \declare i1 @_strGTH(i8*, i8*)\n\
    \declare i1 @_strGE(i8*, i8*)\n\
    \declare i1 @_strEQU(i8*, i8*)\n\
    \declare i1 @_strNE(i8*, i8*)\n\
    \"

printLLVM :: ([Op], SEnv) -> String
printLLVM (ops, gS) =
    let prologue = Prelude.foldl showsStrLLVM declarations (toList gS) in
        Prelude.foldl showsOp prologue ops ""
