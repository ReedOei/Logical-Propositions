import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Tree
import Data.String.Utils (splitWs)

import Text.ParserCombinators.Parsec

purgeWhitespace = intercalate "" . splitWs

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
necessary = and . getAllValues

possible :: Prop -> Bool
possible = or . getAllValues

data Operator = And | Or | Implies | Iff | Equivalent
    -- deriving Show
data PropOperator = Necessary | Possible
    -- deriving Show
data Prop = Statement String | 
            Neg Prop | 
            Exp Prop Operator Prop | 
            Modal PropOperator Prop 
    -- deriving Show
data Argument = Argument [Prop] Prop

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

instance Show Prop where
    show (Statement s) = s
    show (Neg a) = "!" ++ show a
    show (Exp a op b) = "(" ++ show a ++ show op ++ show b ++ ")"
    show (Modal pop a) = show pop ++ "(" ++ show a ++ ")"

instance Show Operator where
    show And = "&"
    show Or = "V"
    show Implies = "->"
    show Iff = "<->"

instance Show PropOperator where
    show Necessary = "[]"
    show Possible = "<>"

instance Show Argument where
    show (Argument givens conclusion) = intercalate "\n" givenStrings ++ "\n" ++ (replicate longestGiven '-') ++ "\n" ++ show conclusion
        where givenStrings = map show givens
              longestGiven = maximum $ map length givenStrings

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

evalWith :: Prop -> Map.Map String Bool -> Maybe Bool
evalWith (Statement s) vals = Map.lookup s vals
evalWith (Neg prop) vals = case evalWith prop vals of
                                Nothing -> Nothing
                                Just v -> Just (not v)
evalWith (Exp a operator b) vals = case evalWith a vals of
                                    Nothing -> Nothing
                                    Just aVal -> case evalWith b vals of
                                                Nothing -> Nothing
                                                Just bVal -> Just (aVal `op` bVal)
    where op = getOp operator
evalWith (Modal propOperator prop) _ = Just (propOp prop)
    where propOp = getPropOp propOperator

getAllValues :: Prop -> [Bool]
getAllValues prop = map fromJust $ filter isJust $ map (prop `evalWith`) mapVals
    where mapVals = map (Map.fromList . zip props) vals
          props = getProps prop
          vals = combinationElements (replicate (length props) [True,False])

truthTable :: Prop -> [[Bool]]
truthTable prop = zipWith (\vs res -> vs ++ [res]) vals resultVals
    where resultVals = getAllValues prop
          props = getProps prop
          vals = combinationElements (replicate (length props) [True,False])

getProps :: Prop -> [String]
getProps = nub . truthTable'
    where truthTable' (Statement s) = [s]
          truthTable' (Neg a) = truthTable' a
          truthTable' (Exp a _ b) = (truthTable' a) ++ (truthTable' b)
          truthTable' (Modal propOp prop) = truthTable' prop

-- I'm sorry.
showTable :: Prop -> [String]
showTable prop = intercalate " | " topLine : (replicate (3 * length topLine + sum (map length topLine) - 3) '-') : lines
    where topLine = map (lpad ' ' 5) $ map (\v -> " " ++ v ++ " ") props ++ [show prop]
          lines = map (\row -> intercalate " | " $ zipWith (\row top -> lpad ' ' (length top) $ show row) row topLine) rows
          props = getProps prop
          rows = truthTable prop

---------------------------------------------------------
-- Parsing
---------------------------------------------------------
topLevelParser :: CharParser st Prop
topLevelParser = try tryExpr <|> propParser
    where tryExpr = do
            first <- propParser
            op <- opParser
            second <- propParser
            return $ Exp first op second

propParser = try (Neg <$> negatedPropParser) <|>
             try modalParser <|>
             try expParser <|>
             try (between (char '(') (char ')') propParser) <|>
             Statement <$> statementParser

statementParser = many1 letter

expParser = do
    char '('
    first <- propParser
    op <- opParser
    second <- propParser
    char ')'

    return $ Exp first op second

opParser = do
    op <- choice [string "->", string "&", string "|", string "<->", string "="]

    return $ case op of
        "->" -> Implies
        "&" -> And
        "|" -> Or
        "<->" -> Iff
        "=" -> Equivalent

modalParser = do
    op <- propOpParser
    prop <- propParser

    return $ Modal op prop

propOpParser = do
    op <- choice [string "[]", string "<>"]
    
    return $ case op of
        "[]" -> Necessary
        "<>" -> Possible

negatedPropParser = do
    char '!'
    propParser

parseProp :: String -> Prop
parseProp str = 
    case parse topLevelParser "Error: " str of
        Left err -> error $ show err
        Right prop -> prop

-- A test prop that is true.
-- (((P <-> Q) & ((S | T) -> Q)) & ((!P) | ((!T) & R))) -> (T -> U)
main = do 
    l <- getLine >>= (return . purgeWhitespace)

    if length l == 0 then do
        putStrLn "Please enter some text."
        main
    else do
        case parseProp l of
            Exp a Equivalent b -> do
                let aTable = showTable a
                let bTable = showTable b
                
                let outTable = zipWith (\a b -> a ++ "    " ++ b) (showTable a) (showTable b)

                mapM_ putStrLn outTable

                print $ sort (truthTable a) == sort (truthTable b)
            prop -> mapM_ putStrLn $ showTable prop
        main

