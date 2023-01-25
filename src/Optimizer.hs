module Optimizer(optimize) where

import Data.Map
import Data.Set
import Emiter

type Descs = Map Label [Label]

splitIntoFunctions :: [Op] -> [[Op]] -> [Op] -> [[Op]]
splitIntoFunctions fun acc ops =
    case ops of
        [] -> reverse acc
        (EndFunOp : rest) -> splitIntoFunctions [] ((reverse (EndFunOp : fun)) : acc) rest
        (op : rest) -> splitIntoFunctions (op : fun) acc rest

addDesc :: Label -> Label -> Descs -> Descs
addDesc src dest descs =
    case Data.Map.lookup src descs of
        Nothing -> Data.Map.insert src [dest] descs
        Just list -> Data.Map.insert src (dest : list) descs

splitIntoBlocks :: Descs -> Label -> [Op] -> [[Op]] -> [Op] -> ([[Op]], Descs)
splitIntoBlocks descs current block acc ops =
    case ops of
        [] -> (reverse acc, descs)

        (GoOp label : rest) -> splitIntoBlocks (addDesc current label descs) current [] ((reverse (GoOp label : block)) : acc) rest
        (CondGoOp res label1 label2 : rest) ->
            splitIntoBlocks (addDesc current label2 (addDesc current label1 descs)) current [] ((reverse (CondGoOp res label1 label2 : block)) : acc)  rest
        (RetOp res : rest) -> splitIntoBlocks descs current [] ((reverse (RetOp res : block)) : acc) rest

        (LabelOp label : rest) -> splitIntoBlocks descs label (LabelOp label : block) acc rest

        (FunOp id regType regs : rest) -> splitIntoBlocks descs current [] ([FunOp id regType regs] : acc) rest
        (EndFunOp : rest) -> splitIntoBlocks descs current [] ([EndFunOp] : acc) rest

        (op : rest) -> splitIntoBlocks descs current (op : block) acc rest

---------------------------------------------------------------------------------

pushNeighbours :: [Label] -> [Label] -> Set Label -> ([Label], Set Label)
pushNeighbours neigh stack reach =
    case neigh of
        [] -> (stack, reach)
        (label : rest) ->
            if Data.Set.member label reach then pushNeighbours rest stack reach
            else pushNeighbours rest (label : stack) (Data.Set.insert label reach)

reachable :: [Label] -> Descs -> Set Label -> Set Label
reachable stack descs reach =
    case stack of
        [] -> reach
        (label : rest) ->
            case Data.Map.lookup label descs of
                Just neigh ->
                    let (stack', reach') = pushNeighbours neigh rest reach in
                        reachable stack' descs reach'
                Nothing -> reachable rest descs reach

predReach :: Set Label -> (Res, Label) -> Bool
predReach reach (res, label) = Data.Set.member label reach

removePhi :: Set Label -> [Op] -> [Op] -> [Op]
removePhi reach ops acc =
    case ops of
        [] -> reverse acc
        (PhiOp reg pairs : rest) -> removePhi reach rest (PhiOp reg (Prelude.filter (predReach reach) pairs) : acc)
        (op : rest) -> removePhi reach rest (op : acc)

remove :: [[Op]] -> Set Label -> [[Op]] -> [[Op]]
remove blocks reach acc =
    case blocks of
        [] -> reverse acc
        ([FunOp id regType regs] : rest) -> remove rest reach ([FunOp id regType regs] : acc)
        ([EndFunOp] : rest) -> remove rest reach ([EndFunOp] : acc)
        ((LabelOp label : restBlock) : rest) ->
            if Data.Set.member label reach then remove rest reach ((removePhi reach (LabelOp label : restBlock) []) : acc)
            else remove rest reach acc

removeUnreachable :: ([[Op]], Descs) -> [[Op]]
removeUnreachable (blocks, descs) =
    let ([FunOp _ _ _] : (LabelOp first : _) : _) = blocks in
        let reach = reachable [first] descs (Data.Set.fromList [first]) in
            remove blocks reach []

---------------------------------------------------------------------------------

replacement :: Repl -> Res -> Res
replacement repl res =
    case res of
        Left const -> Left const
        Right reg ->
            case Data.Map.lookup reg repl of
                Just res' -> res'
                Nothing -> Right reg

replace :: Repl -> Op -> Op
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
        NotOp reg res -> NotOp reg (replacement repl res)
        NegOp reg res -> NegOp reg (replacement repl res)
        CondGoOp res label1 label2 -> CondGoOp (replacement repl res) label1 label2
        CallOp reg id results -> CallOp reg id (Prelude.map (replacement repl) results)
        RetOp res -> RetOp (replacement repl res)
        CallVoidOp id results -> CallVoidOp id (Prelude.map (replacement repl) results)
        op -> op

fakeReg :: Reg
fakeReg = (RegVoid, -1)

fakeDest :: Op -> Maybe (Op, Reg)
fakeDest op =
    case op of
        PlusOp reg res1 res2 -> Just (PlusOp fakeReg (min res1 res2) (max res1 res2), reg)
        MinusOp reg res1 res2 -> Just (MinusOp fakeReg res1 res2, reg)
        TimesOp reg res1 res2 -> Just (TimesOp fakeReg (min res1 res2) (max res1 res2), reg)
        DivOp reg res1 res2 -> Just (DivOp fakeReg res1 res2, reg)
        ModOp reg res1 res2 -> Just (ModOp fakeReg res1 res2, reg)
        LTHOp reg res1 res2 -> Just (LTHOp fakeReg res1 res2, reg)
        LEOp reg res1 res2 -> Just (LEOp fakeReg res1 res2, reg)
        GTHOp reg res1 res2 -> Just (GTHOp fakeReg res1 res2, reg)
        GEOp reg res1 res2 -> Just (GEOp fakeReg res1 res2, reg)
        EQUOp reg res1 res2 -> Just (EQUOp fakeReg (min res1 res2) (max res1 res2), reg)
        NEOp reg res1 res2 -> Just (NEOp fakeReg (min res1 res2) (max res1 res2), reg)
        NotOp reg res -> Just (NotOp fakeReg res, reg)
        NegOp reg res -> Just (NegOp fakeReg res, reg)
        PhiOp reg pairs -> Just (PhiOp fakeReg pairs, reg)
        BitcastOp reg len idx -> Just (BitcastOp fakeReg len idx, reg)
        op -> Nothing

trivialPhi :: Reg -> [(Res, Label)] -> Maybe Res -> Maybe (Maybe Res)
trivialPhi reg pairs acc =
    case pairs of
        [] -> Just acc
        ((res, label) : rest) ->
            if res == Right reg then trivialPhi reg rest acc
            else case acc of
                Nothing -> trivialPhi reg rest (Just res)
                Just res' ->
                    if res == res' then trivialPhi reg rest acc
                    else Nothing

type Preds = Map Label (Set Label)
type Comp = Map Op Reg
type Repl = Map Reg Res

addPred :: Label -> Label -> Preds -> Preds
addPred src dest preds =
    case Data.Map.lookup dest preds of
        Nothing -> Data.Map.insert dest (Data.Set.fromList [src]) preds
        Just list -> Data.Map.insert dest (Data.Set.insert src list) preds

-- lcse nie podmienia rejestrów używanych po prawej stronie przez phi
lcse :: Label -> Preds -> Comp -> Repl -> [Op] -> [Op] -> ([Op], Preds, Comp, Repl)
lcse current preds comp repl acc ops =
    case ops of

        [FunOp id regType regs] -> ([FunOp id regType regs], preds, comp, repl)
        [EndFunOp] -> ([EndFunOp], preds, comp, repl)

        [] -> (reverse acc, preds, comp, repl)

        (GoOp label : rest) ->
            lcse current (addPred current label preds) comp repl (GoOp label : acc) rest
        (CondGoOp res label1 label2 : rest) ->
            lcse current (addPred current label2 (addPred current label1 preds)) comp repl (replace repl (CondGoOp res label1 label2) : acc) rest

        (PhiOp reg pairs : rest) ->
            case trivialPhi reg pairs Nothing of
                Nothing -> lcse current preds comp repl (PhiOp reg pairs : acc) rest -- zostawiamy phi i nie zastępujemy reg
                Just (Just res) -> lcse current preds comp (Data.Map.insert reg res repl) acc rest -- usuwamy phi i zastępujemy reg przez res
                Just (Nothing) -> lcse current preds comp repl acc rest -- usuwamy phi i nie zastępujemy reg

        (op : rest) ->
            let opRepl = replace repl op in
                case fakeDest opRepl of
                    Nothing -> lcse current preds comp repl (opRepl : acc) rest -- operacja nie umieszcza wyniku w rejestrze
                    Just (opRepl', dest) ->
                        case Data.Map.lookup opRepl' comp of
                            Just dest' -> lcse current preds comp (Data.Map.insert dest (Right dest') repl) acc rest -- wyrażenie policzone wcześniej i wynik w dest'
                            Nothing -> lcse current preds (Data.Map.insert opRepl' dest comp) repl (opRepl : acc) rest -- wyrażenie nie policzone wcześniej


replacementPhi :: Map Label Repl -> (Res, Label) -> (Res, Label)
replacementPhi predRepl (res, label) = (replacement (predRepl ! label) res, label)

-- adjustPhi podmienia rejestry używane po prawej stronie przez phi
adjustPhi :: Map Label Repl -> [Op] -> [Op] -> [Op]
adjustPhi predRepl acc ops =
    case ops of
        [] -> reverse acc
        (PhiOp reg pairs : rest) -> adjustPhi predRepl (PhiOp reg (Prelude.map (replacementPhi predRepl) pairs) : acc) rest
        (op : rest) -> adjustPhi predRepl (op : acc) rest

combineLists :: Ord a => [a] -> [a] -> [a] -> [a]
combineLists l1 l2 acc =
    case (l1, l2) of
        ([], _) -> acc
        (_, []) -> acc
        (e1 : rest1, e2 : rest2) ->
            if (e1 < e2) then combineLists rest1 l2 acc
            else
                if (e1 > e2) then combineLists l1 rest2 acc
                else combineLists rest1 rest2 (e1 : acc)

combineMaps :: Ord a => Ord b => Map a b -> Map a b -> Map a b
combineMaps m1 m2 = Data.Map.fromList (combineLists (Data.Map.toList m1) (Data.Map.toList m2) [])

gcse :: Preds -> Map Label Comp -> Map Label Repl -> [[Op]] -> [[Op]] -> [[Op]]
gcse preds predComp predRepl acc blocks =
    case blocks of
        [] -> Prelude.map (adjustPhi predRepl []) (reverse acc)
        ([FunOp id regType regs] : rest) -> gcse preds predComp predRepl ([FunOp id regType regs] : acc) rest
        ([EndFunOp] : rest) -> gcse preds predComp predRepl ([EndFunOp] : acc) rest
        ((LabelOp label : restBlock) : rest) ->
            case Data.Map.lookup label preds of
                Nothing ->
                    let (block', preds', comp', repl') = lcse label preds Data.Map.empty Data.Map.empty [] (LabelOp label : restBlock) in
                        gcse preds' (Data.Map.insert label comp' predComp) (Data.Map.insert label repl' predRepl) (block' : acc) rest
                Just ps ->
                    let (p : restP) = Data.Set.toList ps in
                        let comp = Prelude.foldl combineMaps (predComp ! p) (Prelude.map (predComp !) restP) in
                            let repl = Prelude.foldl combineMaps (predRepl ! p) (Prelude.map (predRepl !) restP) in
                                let (block', preds', comp', repl') = lcse label preds comp repl [] (LabelOp label : restBlock) in
                                    gcse preds' (Data.Map.insert label comp' predComp) (Data.Map.insert label repl' predRepl) (block' : acc) rest

gcseRepeat :: [[Op]] -> [[Op]]
gcseRepeat ops =
    let ops' = gcse Data.Map.empty Data.Map.empty Data.Map.empty [] ops in
        if ops' == ops then ops'
        else gcseRepeat ops'

---------------------------------------------------------------------------------

fakeLabel :: Label
fakeLabel = -1

optimize :: [Op] -> [Op]
optimize ops =
    let x = Prelude.map (splitIntoBlocks Data.Map.empty fakeLabel [] []) (splitIntoFunctions [] [] ops) in
        let y = Prelude.map removeUnreachable x in
            let z = Prelude.map gcseRepeat y in
                concat (concat z)
