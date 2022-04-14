module Syntax where
import Data.List
import qualified Data.Set as Set
import Util

data Term = Atm Atm | App Term Term | Abs Var Term | Cas Term [((Con, [Var]), Term)]
         deriving (Ord, Show)

data Atm = Var Var | Con Con
    deriving (Show, Eq, Ord)

type Var = String -- Variables
type Con = String -- Constructors


isACon (Atm (Con _)) = True
isACon _ = False

isCon (Con _) = True
isCon _ = False

{- ## SHOW ## -}




{- ## EQUALITY ## -}
{- ## ALPHA RULE ## -}

instance Eq Term where -- intensional equality (with alpha rule)
    (Atm a) == (Atm b) = a == b
    (App x y) == (App a b) = x == a && y == b
    (Abs w y) == (Abs v z) = (swapVars w (fvar) y) == (swapVars w (fvar) z)  
        where { fvar = fresh [(Abs w y), (Abs v z)]}
    (Cas x xs) == (Cas y ys) = x == y && xs == ys
    _ == _ = False

swapVars :: Var -> Var -> Term -> Term
swapVars a b (Atm (Var w)) = Atm (Var (swap a b w))
swapVars a b (Atm (Con c)) = Atm (Con c)
swapVars a b (App x y) = App (swapVars a b x) (swapVars a b y)
swapVars a b (Abs w y) = Abs (swap a b w) (swapVars a b y)
swapVars a b (Cas x xs) = Cas (swapVars a b x) (mapSnd (swapVars a b) xs)

swap :: Eq a => a -> a -> a -> a
swap x y z = if x == z then y else (if y == z then x else z)

usedVars :: Term -> [Var]
usedVars (Atm (Var w)) = [w]
usedVars (Atm (Con _)) = []
usedVars (App x y) = usedVars x ++ usedVars y 
usedVars (Abs w x) = w:(usedVars x)
usedVars (Cas x xs) =  usedVars x ++ (concat (map (usedVars . snd) xs))

freeVars :: Term -> [Var]
freeVars (Atm (Var w)) = [w]
freeVars (Atm (Con _)) = []
freeVars (App x y) = freeVars x ++ freeVars y 
freeVars (Abs w x) = filter (/=w) (freeVars x)
freeVars (Cas x xs) =  freeVars x ++ (concat (map (\((c,vs),t) -> filter (not.(`elem`vs)) (freeVars t)) xs))

infiniteVars :: [Var]
infiniteVars = concat$ map (\x -> map (++x) goodVars) $ "":(map show [0..])
            where goodVars = map (:[]) ['a'..'z']

fresh :: [Term] -> Var
fresh xs = head $ freshs xs

freshs :: [Term] -> [Var]
freshs xs = (filter (\ w -> not ( w `elem` (concatMap (usedVars) xs))) infiniteVars)

{- ## Parameters Params ##-}
listParams :: Term -> (Term, [Term])
listParams (App x y) =  case listParams x of { (h, hs) -> (h, hs++[y])} 
listParams h = (h, [])

appParams :: (Term, [Term]) -> Term
appParams  (h, x:xs) = appParams ((App h x), xs)
appParams  (h, []) = h

{- ## BETA RULE ## -}

applyBetaRule :: Term -> Maybe Term
applyBetaRule (App (Abs w y) a) = Just $ substitute w a y
applyBetaRule _ = Nothing

substitute :: Var -> Term -> Term -> Term
substitute v e t = multisubstitute [(v,e)] t

multisubstitute :: [(Var, Term)] -> Term -> Term
multisubstitute as (Atm (Var w)) = case lookup w as of {
                                        Nothing -> Atm (Var w);
                                        Just y -> y;
                                        }
multisubstitute as (Atm (Con c)) = Atm (Con c)
multisubstitute as (App x y) = App (multisubstitute as x) (multisubstitute as y)
multisubstitute as (Abs w y) = Abs h (multisubstitute ((w,Atm (Var h)):as) y)  
                              where (_, h) = head (refresh [w] [y] as)
multisubstitute as (Cas x xs) = Cas (multisubstitute as x)
                                    (map (\((c,vs), exp) -> let hs = refresh vs [exp] as 
                                                                ths = mapSnd (Atm . Var) hs
                                                            in ((c, snds hs), multisubstitute (ths++as) exp)) xs)
    
                              

refresh :: [Var] -> [Term] -> [(Var, Term)] -> [(Var, Var)]
refresh vs ts sus = zip vs $ freshs (concat [map (Atm . Var) vs, ts, map (Atm . Var . fst) sus, snds sus])

{- ## DATA TYPE DEFINITION ## -}

applyCase :: Term -> Maybe Term
applyCase (Cas w xs) = do (c, ys) <- getHeadCon w;
                          ((_,vars), exp)  <- head' $ filter ((==c).fst.fst) xs; 
                          return $ multisubstitute (zip vars ys) exp
applyCase _ = Nothing

head' [] = Nothing
head' (x:xs) = Just x

getHead :: Term -> Maybe (Atm, [Term])
getHead (Atm c) = Just (c, [])
getHead (App x y) = do (c, xs) <- getHead x
                       return (c, xs++[y])
getHead _ = Nothing

getHeadCon :: Term -> Maybe (Con, [Term])
getHeadCon (Atm (Con c)) = Just (c, [])
getHeadCon (App x y) = do (c, xs) <- getHeadCon x
                          return (c, y:xs)
getHeadCon _ = Nothing

subsHead :: Term -> Term -> Term
subsHead t (Atm c)   = t
subsHead t (App x y) = App (subsHead t x) y
subsHead t g = g

args :: Term -> [Term]
args (App x y) = args x ++ [y]
args _ = []

paramsWithCase :: Term -> [Bool]
paramsWithCase (Abs w b) = (caseOn w b):(paramsWithCase b)
paramsWithCase _ = []

caseOn :: Var -> Term -> Bool
caseOn x (App y b) = caseOn x y || caseOn x b
caseOn x (Abs y b) = x/=y && caseOn x b
caseOn x (Cas y b) = (Atm (Var x))==y || any ((caseOn x) . snd )  b
caseOn _ _ = False


{- ## CONSTANT DEFINITIONS ## -}

applyDef :: Term -> [(Var, Term)] -> Maybe Term
applyDef (Atm (Var w)) xs = lookup w xs
applyDef _ _ = Nothing

{- ## LAZY APPLY ## -}

lazyApply :: (Term -> Maybe Term) -> Term -> Maybe Term
lazyApply f (Atm x) =  f (Atm x)
lazyApply f (App x y) = case f (App x y) of {
                            Just a -> Just a;
                            Nothing -> fmap  (flip App y) (lazyApply f x)
                            }
lazyApply f (Abs w y) = f (Abs w y)
lazyApply f (Cas x xs) = case f (Cas x xs) of {
                            Just a -> Just a;
                            Nothing -> fmap (flip Cas xs) (lazyApply f x)
                            }

altura :: Term -> Int
altura (Atm _) = 0
altura (App x y) = 1 + (max (altura x) (altura y))
altura (Abs w x) = 1 + (altura x)
altura (Cas x xs) = 1 + ((foldl1 max ) $ map altura (x:(snds xs))) 

alturas :: Term -> [Int]
alturas (Atm _) = [0]
alturas (App x y)  = map (+1) $ concat [alturas x, alturas y]
alturas (Abs w x)  = map (+1) $ alturas x
alturas (Cas x xs) = map (+1) $ concatMap alturas (x:(snds xs))

tamaño :: Term -> Int
tamaño (Atm _) = 0
tamaño (App x y) = 1 + (tamaño x) + (tamaño y)
tamaño (Abs w x) = 1 + (tamaño x)
tamaño (Cas x xs) = 1 + (sum $ map tamaño (x:(snds xs))) 

contiene :: Atm -> Term -> Bool
contiene a (Atm x) = a == x
contiene a (App x y) = (contiene a x) || (contiene a y)
contiene a (Abs w x) = (contiene a x)
contiene a (Cas x xs) = (contiene a x) || any ((contiene a).snd) xs

atmsNotInTerm :: [Atm] -> Term -> [Atm]
atmsNotInTerm as (Atm e) = delete e as
atmsNotInTerm as (App x y) = intersect (atmsNotInTerm as x) (atmsNotInTerm as y)
atmsNotInTerm as (Abs w x) = (atmsNotInTerm as x)
atmsNotInTerm as (Cas x xs) = foldl1 intersect $ (atmsNotInTerm as x):(map ((atmsNotInTerm as) . snd) xs)


termToAtm :: Term -> [Atm]
termToAtm (App x y) = (termToAtm x) ++ (termToAtm y)
termToAtm (Abs w x) = (termToAtm x)
termToAtm (Cas x xs) =  (concatMap termToAtm (x:(snds xs))) 
termToAtm (Atm e) = [e]

termToAtmCas :: Term -> [Atm]
termToAtmCas (App x y) = (termToAtmCas x) ++ (termToAtmCas y)
termToAtmCas (Abs w x) = (termToAtmCas x)
termToAtmCas (Cas x xs) =  (map (Con . fst . fst ) xs)  ++ (concatMap termToAtmCas (x:(snds xs))) 
termToAtmCas (Atm e) = [e]

termToFreeAtm :: Term -> [Atm]
termToFreeAtm (App x y) = (termToFreeAtm x) ++ (termToFreeAtm y)
termToFreeAtm (Abs w x) = filter (/=(Var w)) (termToFreeAtm x)
termToFreeAtm (Cas x xs) =  (termToFreeAtm x) ++ concatMap (\((c,vs),t) -> filter (not .(`elem`(map (Var) vs))) (termToFreeAtm t)) xs
termToFreeAtm (Atm e) = [e]

termToFreeAtmCas :: Term -> [Atm]
termToFreeAtmCas (App x y) = (termToFreeAtmCas x) ++ (termToFreeAtmCas y)
termToFreeAtmCas (Abs w x) = filter (/=(Var w)) (termToFreeAtmCas x)
termToFreeAtmCas (Cas x xs) = (termToFreeAtmCas x) ++ concatMap (\((c,vs),t) -> [Con c] ++ filter (not .(`elem`(map (Var) vs))) (termToFreeAtmCas t)) xs
termToFreeAtmCas (Atm e) = [e]

termToAtmArgs :: Term -> [Atm]
termToAtmArgs (App (Atm _) y) = (termToAtmArgs y)
termToAtmArgs (App x y) = (termToAtmArgs x) ++ (termToAtmArgs y)
termToAtmArgs (Abs w x) = (termToAtmArgs x)
termToAtmArgs (Cas x xs) =  (concatMap termToAtmArgs (x:(snds xs))) 
termToAtmArgs (Atm e) = [e]
