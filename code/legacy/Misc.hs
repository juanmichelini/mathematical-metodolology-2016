module Misc where
import Data.Maybe
import Data.List

lookup2 :: Eq a => a -> [(a,b,c)] -> Maybe (b,c)
lookup2 x [] = Nothing
lookup2 x ((a,b,c):xs) = if x==a then Just (b,c) else lookup2 x xs

repetir :: a -> (a -> Maybe a) -> Maybe a
repetir x f = case f x of {
                Nothing -> Nothing;
                Just y -> case repetir y f of {
                               Nothing -> Just y;
                               Just z -> Just z; }} 

repetirc :: a -> (a -> Maybe a) -> a
repetirc x f = case repetir x f of {
                    Nothing -> x;
                    Just z -> z;
                    }

repetirL :: a -> (a -> Maybe a) -> [a]
repetirL x f = [x] ++ case f x of {
                        Nothing -> [];
                        Just u -> repetirL u f;
                        }

firstJust :: [Maybe a] -> Maybe a
firstJust = listToMaybe . catMaybes

enPos :: Int -> [a] -> Maybe a
enPos 0 [] = Nothing
enPos 0 (x:xs) = Just x
enPos n (x:xs) = enPos (n-1) xs

firstJustF :: [a -> Maybe b] -> a -> Maybe b
firstJustF fs x = firstJust (map (\f -> f x) fs)

try :: (a -> Maybe a) -> a -> a
try f x = case f x of { Just y -> y; Nothing -> x} 

anyJust :: [Maybe a] -> [a]
anyJust xs = map (fromJust) $ filter (isJust) xs

allJust :: [Maybe a] -> Maybe [a]
allJust [] = Just []
allJust (Nothing:_) = Nothing
allJust ((Just u):xs) = case allJust xs of {
                            Just us -> Just (u:us);
                            Nothing -> Nothing;
                            }

isFunction :: Eq a => Eq b => [(a,b)] -> Bool
isFunction [] = True
isFunction ((x,y):xs) = case lookup x xs of{
                            Just z -> (z==y)&&(isFunction xs);
                            Nothing -> isFunction xs;
                            }

zipFunction :: Eq a => [(a,b)] -> [(a,c)] -> [(a,b,c)]
zipFunction [] _ = []
zipFunction ((a,b):xs) ys = case lookup a ys of {
                                    Just c -> (a,b,c):(zipFunction xs ys);
                                    Nothing -> error "zipFunction mal formada";
                                    }

matchLookup :: Eq a => Eq b => [(a,b)] -> [(a,b)] -> Bool
matchLookup [] ys = True
matchLookup ((a,b):xs) ys = case lookup a ys of {
                                Just w -> w==b && (matchLookup xs ys);
                                Nothing -> False;
                                }

removeFromFunction :: Eq a => a -> [(a,b)] -> [(a,b)]
removeFromFunction a xs = filter ((/=a) . fst) xs
