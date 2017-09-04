import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Tree
import Data.String.Utils (splitWs)

import Text.ParserCombinators.Parsec

purgeWhitespace = intercalate " " . splitWs

combinationElements :: [[a]] -> [[a]]
combinationElements (x:[]) = [[i] | i <- x]
combinationElements (x:xs) = [i : nc | i <- x, nc <- combinationElements xs]

lpad :: Char -> Int -> String -> String
lpad c l s
    | length s >= l = s
    | otherwise = replicate (l - length s) c ++ s

replace :: Eq a => [a] -> [a] -> [a] -> [a]
replace search rep vs = replace' vs
    where replace' [] = []
          replace' check@(x:xs)
            | search `isPrefixOf` check = rep ++ (replace' $ drop (length search) check)
            | otherwise = x : replace' xs

-- Implies
(-->) :: Bool -> Bool -> Bool
True --> True = True
True --> False = False
False --> _ = True

-- If and only if (Iff)
(<->) :: Bool -> Bool -> Bool
True <-> True = True
True <-> False = False
False <-> True = False
False <-> False = True

necessary :: Prop -> Bool
necessary = and . map snd . getAllValues

possible :: Prop -> Bool
possible = or . map snd . getAllValues

data Operator = And | Or | Implies | Iff | Equivalent
    deriving Eq
data PropOperator = Necessary | Possible
    deriving Eq
data Prop = Statement String |
            Neg Prop |
            Exp Prop Operator Prop |
            Modal PropOperator Prop |
            Pred Prop Prop -- Only the rows where the second prop is true will be shown.
    -- deriving Show

-- For easier writing of propositions in ghci
p = Statement "P"
q = Statement "Q"
r = Statement "R"
s = Statement "S"
t = Statement "T"
u = Statement "U"
v = Statement "V"
w = Statement "W"
x = Statement "X"
y = Statement "Y"
z = Statement "Z"

instance Eq Prop where
    Statement a == Statement b = a == b
    Neg a == Neg b = a == b
    Exp a1 op1 b1 == Exp a2 op2 b2 = (a1 == a2) && (op1 == op2) && (b1 == b2)
    Modal op1 a1 == Modal op2 a2 = (op1 == op2) && (a1 == a2)
    Pred a1 b1 == Pred a2 b2 = a1 == a2 && b1 == b2
    _ == _ = False

instance Show Prop where
    show (Statement s) = s
    show (Neg a) = "!" ++ show a
    show (Exp a op b) = "(" ++ show a ++ show op ++ show b ++ ")"
    show (Modal pop a) = show pop ++ "(" ++ show a ++ ")"
    show (Pred a b) = show a ++ " where " ++ show b

instance Show Operator where
    show And = "&"
    show Or = "|"
    show Implies = "->"
    show Iff = "<->"

instance Show PropOperator where
    show Necessary = "[]"
    show Possible = "<>"

land a b = Exp a And b
a & b = Exp a And b
lor a b = Exp a Or b
implies a b = Exp a Implies b
iff a b = Exp a Iff b
lnot a = Neg a

getOp :: Operator -> (Bool -> Bool -> Bool)
getOp And = (&&)
getOp Or = (||)
getOp Implies = (-->)
getOp Iff = (<->)

getPropOp :: PropOperator -> (Prop -> Bool)
getPropOp Necessary = necessary
getPropOp Possible = possible

isEquiv :: Prop -> Prop -> Bool
isEquiv a b = all testVals mapVals
    where testVals vs = (a `evalWith` vs) == (b `evalWith` vs)
          mapVals = map (Map.fromList . zip props) vals
          props = getProps a
          vals = combinationElements (replicate (length props) [True,False])

evalWith :: Prop -> Map.Map String Bool -> Maybe Bool
evalWith (Statement s) vals = Map.lookup s vals
evalWith (Neg prop) vals = not <$> (prop `evalWith` vals)
evalWith (Exp a operator b) vals = op <$> (a `evalWith` vals) <*> (b `evalWith` vals)
    where op = getOp operator
evalWith (Modal propOperator prop) _ = Just (propOp prop)
    where propOp = getPropOp propOperator

getAllValues :: Prop -> [(Map.Map String Bool, Bool)]
getAllValues prop = map (\vs -> (vs, prop `evalWith` vs == Just True)) mapVals
    where mapVals = map (Map.fromList . zip props) vals
          props = getProps prop
          vals = combinationElements (replicate (length props) [True,False])

truthTable :: Prop -> [[Bool]]
truthTable (Pred a b) = map (\(vs, res) -> Map.elems vs ++ [res]) vals
    where resultVals = getAllValues a
          -- Only if the predicate is also true with these values do we want to show it.
          vals = filter (\(vs, _) -> b `evalWith` vs == Just True) resultVals

truthTable prop = map (\(vs, res) -> Map.elems vs ++ [res]) resultVals
    where resultVals = getAllValues prop

getProps :: Prop -> [String]
getProps = nub . getProps'
    where getProps' (Statement s) = [s]
          getProps' (Neg a) = getProps' a
          getProps' (Exp a _ b) = getProps' a ++ getProps' b
          getProps' (Modal propOp prop) = getProps' prop
          getProps' (Pred a b) = getProps' a ++ getProps' b

-- I'm sorry.
showTable :: Prop -> [String]
showTable prop = intercalate " | " topLine : (replicate (3 * length topLine + sum (map length topLine) - 3) '-') : lines
    where topLine = map (lpad ' ' 5) $ map (\v -> " " ++ v ++ " ") props ++ [show prop]
          lines = map (\row -> intercalate " | " $ zipWith (\row top -> lpad ' ' (length top) $ show row) row topLine) rows
          props = getProps prop
          rows = truthTable prop

-- Takes two lists and returns a list containing all the elements from both.
-- Which list the element is from will alternate.
-- Ex: interleave [1..5] [6,7,8,9] == [1,6,2,7,3,8,4,9,5]
interleave :: [a] -> [a] -> [a]
interleave [] [] = []
interleave a [] = a
interleave [] b = b
interleave (a:as) bs = a : interleave' as bs
    where interleave' [] [] = []
          interleave' a [] = a
          interleave' [] b = b
          interleave' a (b:bs) = b : interleave a bs

-- Replaces the propositions inside the first prop one by one with the second prop
-- Returns a list of all the new propositions
replacements :: Prop -> Prop -> [Prop]
replacements a@(Statement _) b = [a, b]
replacements a@(Neg a1) b = [a, Neg b]
replacements a@(Exp a1 op b1) b = [a, Exp b op b1, Exp a1 op b, Exp b op b]
replacements a@(Modal op a1) b = [a, Modal op b]

-- Replaces the propositions inside the first prop one by one with the second prop
-- Will then recursively do the same to all sub propositions
-- Returns a list of all the new propositions
allReplacements a b = nub $ allReplacements' a b

allReplacements' :: Prop -> Prop -> [Prop]
allReplacements' a@(Statement _) b = replacements a b
allReplacements' a@(Neg a1) b = replacements a b ++ map Neg (allReplacements a1 b)
allReplacements' a@(Exp a1 op b1) b = replacements a b ++
                                     concat (map (replacements a) (allReplacements a1 b)) ++
                                     concat (map (replacements a) (allReplacements b1 b))
allReplacements' a@(Modal op a1) b = replacements a b ++ map (Modal op) (allReplacements a1 b)

-- Checks whether any of the expressions are of the form a `op` a.
-- We don't want these, as they are generaly uninteresting.
operandsEq :: Prop -> Bool
operandsEq (Statement _) = False
operandsEq (Neg a) = operandsEq a
operandsEq (Exp a _ b) = a == b || operandsEq a || operandsEq b
operandsEq (Modal _ a) = operandsEq a

-- Returns a list of (TODO: all) propositions that are logically equivalent
-- to the input (but also aren't literally the same thing).
findEquiv :: Prop -> [Prop]
findEquiv prop = nub $ filter (\p -> prop /= p && isEquiv prop p) allProps
    where statements = map Statement $ getProps prop
          allProps = filter (not . operandsEq) $ listAll statements
          listAll xs = xs ++ new ++ listAll new
            where new = concat $ map (\rep -> concat $ map (allReplacements rep) newBase) newBase
                  newBase = concat (map makeProps xs)
                  makeProps curProp = negated ++ applyOperators ++ applyModals
                    where
                      -- Don't negate twice
                      negated =
                        case curProp of
                            Neg _ -> []
                            _ -> [Neg curProp]
                      operators = [And, Or, Implies, Iff]
                      modals = [Necessary, Possible]
                      applyOperators = concat $ map (\op -> map (Exp curProp op) statements) operators
                      applyModals = map (\m -> Modal m curProp) modals

---------------------------------------------------------
-- Parsing
---------------------------------------------------------
topLevelParser :: CharParser st Prop
topLevelParser = try tryExpr <|>
                 try predicate <|>
                 propParser
    where tryExpr = do
            spaces
            first <- propParser
            spaces
            op <- opParser
            spaces
            second <- propParser
            spaces

            return $ Exp first op second

propParser = try (Neg <$> negatedPropParser) <|>
             try modalParser <|>
             try expParser <|>
             try (between (char '(') (char ')') propParser) <|>
             Statement <$> statementParser

statementParser = many1 letter

expParser = do
    spaces
    char '('
    spaces
    first <- propParser
    spaces
    op <- opParser
    spaces
    second <- propParser
    spaces
    char ')'

    return $ Exp first op second

predicate = do
    spaces
    first <- propParser
    spaces
    string "where"
    spaces
    second <- propParser

    return $ Pred first second

opParser = do
    spaces
    op <- choice [string "->", string "&", string "|", string "<->", string "="]

    return $ case op of
        "->" -> Implies
        "&" -> And
        "|" -> Or
        "<->" -> Iff
        "=" -> Equivalent

modalParser = do
    spaces
    op <- propOpParser
    spaces
    prop <- propParser

    return $ Modal op prop

propOpParser = do
    spaces
    op <- choice [string "[]", string "<>"]

    return $ case op of
        "[]" -> Necessary
        "<>" -> Possible

negatedPropParser = do
    spaces
    char '!'
    spaces
    propParser

parseProp :: String -> Prop
parseProp str =
    case parse topLevelParser "Error: " $ purgeWhitespace str of
        Left err -> error $ show err
        Right prop -> prop

-- A test prop that is true.
-- (((P <-> Q) & ((S | T) -> Q)) & ((!P) | ((!T) & R))) -> (T -> U)
main = do
    l <- getLine

    if length (purgeWhitespace l) == 0 then do
        putStrLn "Please enter some text."
        main
    else do
        case parseProp l of
            Exp a Equivalent b -> do
                let aTable = showTable a
                let bTable = showTable b

                let outTable = zipWith (\a b -> a ++ "    " ++ b) (showTable a) (showTable b)

                mapM_ putStrLn outTable

                print $ isEquiv a b

            prop -> mapM_ putStrLn $ showTable prop
        main

