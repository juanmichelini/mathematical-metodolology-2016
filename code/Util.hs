module Util where
import Data.Maybe
import Data.List
import Debug.Trace

-- Listas de Pares

fsts :: [(a,b)] -> [a]
fsts = fst . unzip

snds :: [(a,b)] -> [b]
snds = snd . unzip

flippair :: (a,b) -> (b,a)
flippair (a,b) = (b,a)

mapFst :: (a -> c) -> [(a,b)] -> [(c,b)]
mapFst f xs = map (\(fst,snd)->(f fst, snd)) xs

mapSnd :: (b -> c) -> [(a,b)] -> [(a,c)]
mapSnd f xs = map (\(fst,snd)->(fst,f snd)) xs

mapFstSnd :: (a -> c) -> (b -> d) -> [(a,b)] -> [(c,d)]
mapFstSnd f1 f2 xs = map (\(fst,snd)->(f1 fst,f2 snd)) xs

mapBoth :: (a -> b) -> [(a,a)] -> [(b,b)]
mapBoth f = mapFstSnd f f 

cartesianprod :: [a] -> [b] -> [(a,b)]
cartesianprod [] _ = []
cartesianprod (x:xs) ys = (map (\y -> (x,y)) ys) ++ cartesianprod xs ys




allJust :: [Maybe a] -> Maybe [a]
allJust [] = Just []
allJust (Nothing:_) = Nothing
allJust ((Just x):xs) = case allJust xs of
                            Nothing -> Nothing
                            Just ys -> Just (x:ys)

anyJust :: [Maybe a] ->  [a]
anyJust [] = []
anyJust (Nothing:xs) = anyJust xs
anyJust ((Just x):xs) = x:(anyJust xs)


while :: (a -> (Bool, a)) -> a -> a
while f a = case f a of {
                (False, b) -> b;
                (True, b) -> while f b;
                }

whileMaybe :: (a -> Maybe (Bool, a)) -> a -> Maybe a
whileMaybe f a = case f a of {
                    Just (False, b) -> Just b;
                    Just (True, b) -> whileMaybe f b;
                    Nothing -> Nothing;
                }

revapply :: a -> (a -> b) -> b
revapply a f = f a


whileMaybes :: [a -> Maybe (Bool, a)] -> a -> Maybe a
whileMaybes fs a = case filter (\y -> (isJust y) && fst(fromJust y)) fsa of{
                            [] -> case all isJust fsa of {
                                            True -> Just a;
                                            False -> Nothing;
                                            };
                            ((Just(True,b)):_) -> whileMaybes fs b;
                            }
                            where fsa = map (revapply a) fs

parens :: String -> String
parens s = "("++s++")"

separar :: a -> [a] -> [a]
separar a [] = []
separar a (x:xs) = x:(concat $ zipWith (\u b -> [u,b]) (repeat a) xs)

hilar :: [[a]] -> [[a]] 
hilar [] = [[]]
hilar (xs:xss) = [ x:hs | hs <- hilar xss, x <- xs]

--xss finite, xs infinite
hilarI :: [[a]] -> [[a]] 
hilarI [] = []
hilarI [xs] = map (:[]) xs
hilarI (xs:ys:yss) = map (\(a,b) -> a:b) (comb xs (hilarI (ys:yss)))

comb :: [a] -> [b] -> [(a,b)]
comb (xs) (ys) = diag $ map (\x -> map (\y -> (x,y)) ys) xs

dist :: Int -> [a] -> [[[a]]]
dist 0 xs = []
dist 1 xs = [[xs]] 
dist n [] = [take n (repeat [])] 
dist n xs = [(take m xs):ys | m <- [0..(length xs)], ys <- dist (n-1) (drop m xs) ]

distO :: Int -> [a] -> [[[a]]]
distO 0 xs = []
distO 1 xs = [[xs]] 
distO n [] = [take n (repeat [])] 
distO n xs = [ (j):rec | m <- [0..(length xs)], (j,k) <- postake m xs, rec <- distO (n-1) k]

postake :: Int -> [a] -> [([a],[a])]
postake 0 xs = [([],xs)]
postake n [] = []
postake n (x:xs) =  mapFst (x:) (postake (n-1) xs) ++ mapSnd (x:) (postake n xs)

armarParejas :: [a] -> [(a,a)]
armarParejas [] = []
armarParejas (x:xs) = (map (\y->(x,y)) xs) ++ (armarParejas xs)



lookup2 :: Eq a => a -> [(a,b,c)] -> Maybe (b,c)
lookup2 x [] = Nothing
lookup2 x ((a,b,c):xs) = if x==a then Just (b,c) else lookup2 x xs

repetir :: (a -> Maybe a) -> a -> Maybe a
repetir f x = case f x of {
                Nothing -> Nothing;
                Just y -> case repetir f y of {
                               Nothing -> Just y;
                               Just z -> Just z; }} 

repetirc :: (a -> Maybe a) -> a -> a
repetirc f x = case repetir f x of {
                    Nothing -> x;
                    Just z -> z;
                    }

repetirc' :: Show a => (a -> Maybe a) -> a -> a
repetirc' f x = foldr1 (trace . show) ls
            where ls = repetirL f x

repetirL :: (a -> Maybe a) -> a -> [a]
repetirL f x = [x] ++ case f x of {
                        Nothing -> [];
                        Just u -> repetirL f u;
                        }

firstJust :: [Maybe a] -> Maybe a
firstJust = listToMaybe . catMaybes

enPos :: Int -> [a] -> Maybe a
enPos _ [] = Nothing
enPos 0 (x:xs) = Just x
enPos n (x:xs) = enPos (n-1) xs

firstJustF :: [a -> Maybe b] -> a -> Maybe b
firstJustF fs x = firstJust (map (\f -> f x) fs)

try :: (a -> Maybe a) -> a -> a
try f x = case f x of { Just y -> y; Nothing -> x} 


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

appFst :: (a -> c) -> (a,b) -> (c,b)
appFst f  (a,b) = (f a, b)

appSnd :: (b -> c) -> (a,b) -> (a,c)
appSnd f  (a,b) = (a, f b)

appBoth :: (a -> c) -> (b -> d) -> (a,b) -> (c,d)
appBoth f g (a,b) = (f a, g b)

appBoth2 :: (a -> b) -> (a,a) -> (b,b)
appBoth2 f (a1,a2) = (f a1, f a2)

oppOrd :: Ordering -> Ordering
oppOrd LT = GT
oppOrd GT = LT
oppOrd EQ = EQ

compWith :: (a -> Int) -> (a -> a -> Ordering)
compWith f x y = compare (f x) (f y)

deleteFstThat :: (a -> Bool) -> [a] -> [a]
deleteFstThat p [] = []
deleteFstThat p (x:xs) = if p x then xs else x:(deleteFstThat p xs)

diag  :: [[a]] -> [a]
diag xs = diag' 1 xs

diag' :: Int -> [[a]] -> [a]
diag' n xs =  (map head ys) ++ (diag' (n+1) (filter (not . null) ((map tail ys) ++ zs)))
             where (ys, zs) = splitAt n xs

infiniteMatrix = ([0..]):(map (map (+1)) infiniteMatrix)

-- diag infiniteMatrix = [0, 1, 1, 2, 2, 2 ...]

