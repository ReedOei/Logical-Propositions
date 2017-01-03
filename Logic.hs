import Lib (combinationElements)

import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Tree

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

data Operator = And | Or | Implies | Iff
data PropOperator = Necessary | Possible
data Prop = Statement String | Neg Prop | Exp Prop Operator Prop | Modal PropOperator Prop
data Argument = Argument [Prop] Prop

-- For easier writing of propositions
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

isValid :: Argument -> Bool
isValid (Argument givens conclusion) = and (getAllValues (foldl1 land givens `implies` conclusion))

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

showTable :: Prop -> IO ()
showTable prop = mapM_ putStrLn $ (show prop : (intercalate " | " $ map (lpad ' ' 5) props) : (replicate (8 * length props + 8) '-') : lines)
    where lines = map (intercalate " | " . map (lpad ' ' 5 . show)) rows
          props = getProps prop
          rows = truthTable prop

opStrs = ["&", "!", "|", "->", "<->", "<>", "[]"]

isAlpha :: Char -> Bool
isAlpha c = (c `elem` ['A'..'Z']) || (c `elem` ['a'..'z'])

findInfix :: Eq a => [a] -> [a] -> Maybe (Int, [a])
findInfix search vs = findInfix' vs 0
    where findInfix' [] _ = Nothing
          findInfix' xs i
            | search `isPrefixOf` xs = Just (i, search)
            | otherwise = findInfix' (tail xs) (i + 1)

safeMinimum :: Ord a => [a] -> Maybe a
safeMinimum [] = Nothing
safeMinimum xs = Just $ minimum xs

tokenize :: String -> [String]
tokenize s = filter (not . null) $ tokenize' s 0 0 0
    where tokenize' [] groupPos _ i = case groupPos of
                                            -- To make sure we don't miss the first character
                                            0 -> getTokens s
                                            _ -> getTokens $ drop (groupPos + 1) $ take i s
          tokenize' (x:xs) groupPos depth i
            | '(' == x = case depth of
                                0 -> case groupPos of
                                        -- To make sure we don't miss the first character
                                        0 -> (getTokens $ drop groupPos $ take i s) ++ tokenize' xs i (depth + 1) (i + 1)
                                        _ -> (getTokens $ drop (groupPos + 1) $ take i s) ++ tokenize' xs i (depth + 1) (i + 1)
                                _ -> tokenize' xs groupPos (depth + 1) (i + 1)
            | ')' == x && depth == 1 = (drop (groupPos + 1) $ take i s) : tokenize' xs i 0 (i + 1)
            | ')' == x = tokenize' xs groupPos (depth - 1) (i + 1)
            | otherwise = tokenize' xs groupPos depth (i + 1)
          getTokens str
            | not (null operator) && not (null identifier) = case length opRest > length alphaRest of
                                                                True -> operator : getTokens opRest
                                                                False -> identifier : getTokens alphaRest
            | not (null operator) = operator : getTokens opRest
            | not (null identifier) = identifier : getTokens alphaRest
            | otherwise = []
            where (identifier, alphaRest) = case findIndex (not . isAlpha) str of
                                                Nothing -> (str, "")
                                                Just i -> splitAt i str
                  (operator, opRest) = case safeMinimum $ map fromJust $ filter isJust (map (`findInfix` str) opStrs) of
                                        Nothing -> ("", str)
                                        Just (i, op) -> splitAt (i + length op) str

parseArgument :: [String] -> Argument
parseArgument ls = Argument (map parseProp $ init $ init ls) (parseProp $ last ls)

isValidStatement :: String -> Bool
isValidStatement str@(s:ss)
    | not $ isAlpha s = False
    | otherwise = all (\i -> not (i `elem` "!@#$%^&*()<->")) str

parseProp :: String -> Prop
parseProp str = parseExp nothing groups
    where groups = tokenize $ replace " " "" str
          nothing = Statement "Nothing"
          parseExp prev gs = case gs of
                                ("!":x:xs) -> parseExp (Neg (parseProp x)) xs
                                (a:"->":xs) -> Exp (parseProp a) Implies (parseExp nothing xs)
                                ("->":xs) -> Exp prev Implies (parseExp nothing xs)
                                (a:"&":xs) -> Exp (parseProp a) And (parseExp nothing xs)
                                ("&":xs) -> Exp prev And (parseExp nothing xs)
                                (a:"|":xs) -> Exp (parseProp a) Or (parseExp nothing xs)
                                ("|":xs) -> Exp prev Or (parseExp nothing xs)
                                (a:"<->":xs) -> Exp (parseProp a) Iff (parseExp nothing xs)
                                ("<->":xs) -> Exp prev Iff (parseExp nothing xs)
                                ("[]":xs) -> Modal Necessary (parseExp nothing xs)
                                ("<>":xs) -> Modal Possible (parseExp nothing xs)
                                (_:op:_) -> error ("Unknown operator: " ++ show op)
                                (a:xs) -> let next = case isValidStatement a of
                                                          True -> Statement a
                                                          False -> case length a < length str of
                                                                      True -> parseProp a
                                                                      False -> error "Could not parse input."
                                              in parseExp next xs
                                [] -> prev
--                                _ -> error ("No match for for groups: " ++ show groups)
-- A test proof:
-- (((P<->Q)&((S|T)->Q))&((!P)|((!T)&R)))->(T->U)
main = do
    l <- getLine
    showTable $ parseProp l
    main