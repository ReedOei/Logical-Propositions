import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import Data.Tree
import Data.String.Utils (splitWs)

import System.Environment

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
necessary prop = and [ truthVal valuation prop | valuation <- valuations vs ]
    where
        vs = getProps prop

possible :: Prop -> Bool
possible prop = or [ truthVal valuation prop | valuation <- valuations vs ]
    where
        vs = getProps prop

data Operator = And | Or | Implies | Iff | Equivalent
    deriving (Eq, Ord)
data PropOperator = Necessary | Possible
    deriving (Eq, Ord)
data Prop = Statement String |
            ConstTrue | ConstFalse |
            Neg Prop |
            Exp Prop Operator Prop |
            Modal PropOperator Prop |
            Pred Prop Prop -- Only the rows where the second prop is true will be shown.
    deriving (Eq, Ord)

-- For easier writing of propositions in ghci
a = Statement "A"
b = Statement "B"
c = Statement "C"
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

instance Show Prop where
    show ConstFalse = "\\false"
    show ConstTrue = "\\true"
    show (Statement s) = s
    show (Neg a) = "\\neg " ++ show a
    show (Exp a op b) = "(" ++ show a ++ " " ++ show op ++ " " ++ show b ++ ")"
    show (Modal pop a) = show pop ++ "(" ++ show a ++ ")"
    show (Pred a b) = show a ++ " where " ++ show b

instance Show Operator where
    show And = "\\land"
    show Or = "\\lor"
    show Implies = "\\imp"
    show Iff = "\\iff"

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

evalWith :: Prop -> Map String Bool -> Maybe Bool
evalWith ConstTrue _ = Just True
evalWith ConstFalse _ = Just False
evalWith (Statement s) vals = Map.lookup s vals
evalWith (Neg prop) vals = not <$> (prop `evalWith` vals)
evalWith (Exp a operator b) vals = op <$> (a `evalWith` vals) <*> (b `evalWith` vals)
    where op = getOp operator
evalWith (Modal propOperator prop) _ = Just (propOp prop)
    where propOp = getPropOp propOperator

truthVal :: Map String Bool -> Prop -> Bool
truthVal valuation prop = prop `evalWith` valuation == Just True

-- TODO: Make a catamorphism thing for this?
-- Can parameterize on the statement type or something, idk.
subProps :: Prop -> Set Prop
subProps s@(Statement _)    = Set.singleton s
subProps n@(Neg p)          = Set.insert n $ subProps p
subProps e@(Exp p1 op p2)   = Set.insert e $ Set.union (subProps p1) $ subProps p2
subProps m@(Modal propOp p) = Set.insert m $ subProps p
subProps w@(Pred p1 p2)     = Set.insert w $ Set.union (subProps p1) $ subProps p2
subProps ConstFalse         = Set.empty
subProps ConstTrue          = Set.empty

height :: Prop -> Integer
height s@(Statement _)    = 1
height n@(Neg p)          = 1 + height p
height e@(Exp p1 op p2)   = 1 + max (height p1) (height p2)
height m@(Modal propOp p) = 1 + height p
height w@(Pred p1 p2)     = 1 + max (height p1) (height p2)
height ConstTrue          = 0
height ConstFalse         = 0

valuations :: [String] -> [Map String Bool]
valuations vs = [Map.fromList $ zip vs valuation | valuation <- combinationElements $ replicate (length vs) [True, False]]

propList :: Prop -> [Prop]
propList = sortBy (comparing height) . Set.toList . subProps

truthTable :: Prop -> [[Bool]]
truthTable (Pred a b) = [ map (truthVal valuation) props | valuation <- valuations vs, truthVal valuation b]
    where
        props = propList a
        vs = getProps a ++ getProps b

truthTable prop = [ map (truthVal valuation) props | valuation <- valuations vs]
    where
        props = propList prop
        vs = getProps prop

getProps :: Prop -> [String]
getProps = nub . getProps'
    where getProps' (Statement s) = [s]
          getProps' (Neg a) = getProps' a
          getProps' (Exp a _ b) = getProps' a ++ getProps' b
          getProps' (Modal propOp prop) = getProps' prop
          getProps' (Pred a b) = getProps' a ++ getProps' b
          getProps' ConstFalse = []
          getProps' ConstTrue = []

-- I'm sorry.
showTable :: Prop -> [String]
showTable prop = intercalate " | " topLine : (replicate (3 * length topLine + sum (map length topLine) - 3) '-') : lines
    where topLine = map (lpad ' ' 5) $ map (\p -> " " ++ show p ++ " ") props
          lines = map (\row -> intercalate " | " $ zipWith (\row top -> lpad ' ' (length top) $ show row) row topLine) rows
          props = propList prop
          rows = truthTable prop

showLatexTable :: Prop -> String
showLatexTable prop =
    "\\begin{tabular}{" ++ alignStr ++ "}\n" ++
    intercalate " \\\\\n\\hline\n" (map (intercalate " & ") rows) ++ "\n" ++
    "\\end{tabular}"
    where
        alignStr = intercalate "|" $ replicate (length props) "c"
        props = propList prop
        rowVals = truthTable prop
        headerRow = map (\p -> "$" ++ show p ++ "$") props
        rows = headerRow : map (map showBool) (truthTable prop)

        showBool True = "\\true"
        showBool False = "\\false"

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
            first <- try propParser
            spaces
            op <- try opParser
            spaces
            second <- try propParser
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

data IfExp = If String IfExp IfExp
           | T
           | F
    deriving (Eq, Ord)

instance Show IfExp where
    show T = "\\true"
    show F = "\\false"
    show (If v t e) = "(if $" ++ v ++ "$ then " ++ show t ++ " else " ++ show e ++ ")"

substitute :: (String -> Prop) -> Prop -> Prop
substitute theta ConstTrue = ConstTrue
substitute theta ConstFalse = ConstFalse
substitute theta (Statement s) = theta s
substitute theta (Neg p) = Neg $ substitute theta p
substitute theta (Exp a op b) = Exp (substitute theta a) op (substitute theta b)
substitute theta (Modal op p) = Modal op $ substitute theta p
substitute theta (Pred a b) = Pred (substitute theta a) (substitute theta b)

shannonExpansion :: Prop -> IfExp
shannonExpansion ConstTrue = T
shannonExpansion ConstFalse = F
shannonExpansion p =
    case getProps p of
        [] -> if (p `evalWith` Map.empty == Just True) then T else F
        v:vs -> If v (go v ConstTrue) (go v ConstFalse)
    where
        go v new = shannonExpansion $ substitute (\w -> if w == v then new else Statement w) p

simplifyExpansion :: IfExp -> IfExp
simplifyExpansion T = T
simplifyExpansion F = F
simplifyExpansion (If v t e) =
    let t' = simplifyExpansion t
        e' = simplifyExpansion e
    in if t' == e' then t' else If v t' e'

-- A test prop that is true.
-- (((P <-> Q) & ((S | T) -> Q)) & ((!P) | ((!T) & R))) -> (T -> U)
main = do
    args <- getArgs

    let useLatex = if not (null args) then head args == "--latex" else False
    let shannonExpand = if not (null args) then head args == "--shannon-expand" else False

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

            prop ->
                if shannonExpand then
                    putStrLn $ show $ shannonExpansion prop
                else if useLatex then
                    putStrLn $ showLatexTable prop
                else
                    mapM_ putStrLn $ showTable prop
        main

