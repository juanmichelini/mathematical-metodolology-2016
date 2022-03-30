module Tactic  where
import Syntax
import Compute
import SimpleSubst
import Type
import Misc

import Data.Maybe
import Data.List

data Afirm a = EQA [(Name, SimpleType)] a a -- | And [Obj a] | Or [Obj a] | If [Obj a] (Obj a) | Bot
            deriving (Eq)

instance Show a => Show (Afirm a) where
    show (EQA vs x y) = case vs of {
                            [] -> "";
                            _ -> "(All "++ concat ( map (\(v,t) -> show v ++ "::" ++ show t ++ " ") vs) ++ ")";
                            } ++ show x ++ "==="  ++ show y
    -- show (And xs) = "(" ++ intercalate "/\\" (map show xs) ++ ")"
    -- show (Or xs) = "(" ++ intercalate "\\/" (map show xs) ++ ")"
    -- show (If xs x) = "(" ++ show (And xs) ++"=>"++ show x ++ ")"
    -- show (Bot) = "_|_"

type Obj a = ([a], a)

type Tactic a = Obj a -> Maybe [Obj a]

type AHExp = Afirm HExp

composeT :: Tactic a -> Tactic a -> Tactic a
composeT f g x = case g x of {
                    Nothing -> Nothing;
                    Just ys ->  Just $ concat $ map ((try (f . head)) . (:[])) ys
                    }

triv :: Tactic AHExp
triv  (xs, EQA vs y z) | y == z = Just []
                       | otherwise = Nothing

--dispatch :: Tactic AHExp -> Tactic AHExp
--dispatch t (xs, A (Equ y z)) = Nothing
--dispatch t (xs, And y z) = case (t (xs, y), t (xs, z)) of {
--                                (Just v, Just w) -> Just (And v w);
--                                (Nothing, Just w) -> Just (And y w);
--                                (Just v, Nothing) -> Just (And v z);
--                                _ -> Nothing;
--                                }
--dispatch t (xs, Or y z) = case catMaybes [t (xs, y), t (xs, z)] of {
--                                v:_ -> Just v;
--                                [] -> Nothing;
--                                }
--dispatch t (xs, If y z) = case t ((y:xs), z) of { Just u -> Just$ If y u; Nothing -> Nothing;}
--dispatch t (xs, Bot) = Nothing
compute :: Env -> Tactic AHExp
compute env (xs, EQA vs y z) = case (flip repetir (cWideLazy env) y, flip repetir (cWideLazy env) z) of {
                                (Just v, Just w)  -> Just [(xs, EQA vs v w)];
                                (Just v, Nothing) -> Just [(xs, EQA vs v z)];
                                (Nothing, Just w) -> Just [(xs, EQA vs y w)];
                                _ -> Nothing;
                                }

computeDontEndInCas :: Env -> Tactic AHExp
computeDontEndInCas env (xs, EQA vs y z) = case ((cRepeatButDontEndInCas $ (cWideLazy env)) y, (cRepeatButDontEndInCas $ (cWideLazy env)) z) of {
                                (Just v, Just w)  -> Just [(xs, EQA vs v w)];
                                (Just v, Nothing) -> Just [(xs, EQA vs v z)];
                                (Nothing, Just w) -> Just [(xs, EQA vs y w)];
                                _ -> Nothing;
                                }

-- todavía no verifico si vale la pena hacer inducción justo en esa variable...
indc :: [Data] -> Env -> Tactic AHExp
indc ds env (xs, e@(EQA vs y z)) = case vs of {
                                    [] -> Nothing;
                                    (v, t):_ -> Just $ map (appFst(++xs)) $ instanciarPpio v e $ armarPpio $ nombrarPar (env')  $ marcarHip $ lkupData t ds
                                    }where env' = (hexpsA e) ++ (concat (map hexpsA xs)) ++ (map ((Atm Var) . fst) env)  ++  (map (snd) env) 
                                           hexpsA (EQA vs y z) = (map ((Atm Var) . fst) vs) ++ [y,z] 



varsfrescas :: [HExp] -> [Name]
varsfrescas obs = filter (\u -> all (isFresh u) obs) infinitevars 


nombrarPar :: [HExp] -> [(Name, [Bool])] -> [(Name, [(Name, Bool)])]
nombrarPar env cs = map (\(c, bs) -> (c,  zip (varsfrescas (env)) bs)) cs

armarPpio :: [(Name, [(Name, Bool)])] ->  [([HExp], HExp)]
armarPpio ppio = map (\(c,vs) -> ((map ((Atm Var) .fst)) $ filter snd vs, appParams (Atm Con c, (map ((Atm Var) . fst) vs)))) ppio   
 
instanciarPpio :: Name -> Afirm HExp -> [([HExp], HExp)] -> [([Afirm HExp], Afirm HExp)]
instanciarPpio v (EQA vs y z) ppio = map (\(hs,t) -> (map (substA e' v) hs, substA e' v t)) ppio  
                                    where vs' =  filter ((/=v).fst) vs
                                          e' = EQA vs' y z


appFst :: (a -> c) -> (a,b) -> (c,b)
appFst f  (a,b) = (f a,b)

appSnd :: (b -> c) -> (a,b) -> (a,c)
appSnd f  (a,b) = (a,f b)

substA :: Afirm HExp -> Name -> HExp -> Afirm HExp
substA (EQA vs e f) v g = EQA vs (subst e v g) (subst f v g) 


lema :: Tactic AHExp
lema (ls, EQA vs y z) = case applyLemmas ls (map fst vs) y of {
                             Just (t,v) -> Just [(delete t ls, EQA vs v z)];
                             Nothing -> case applyLemmas ls (map fst vs) z of {
                                            Just (t, w) -> Just [(delete t ls, EQA vs y w)];
                                            Nothing -> Nothing;
                                            }
                             }
                               
-- devuelve el lema que aplico y la expresión resultante de aplicarlo
applyLemmas :: [Afirm HExp] -> [Name] -> HExp -> Maybe (Afirm HExp, HExp)
applyLemmas ls vs e = firstJust $ map (\ u -> case aWideLemma u vs e of {Just w -> Just (u, w); Nothing -> Nothing;}) ls


aLemma :: Afirm HExp -> [Name] -> HExp -> Maybe HExp 
aLemma l@(EQA vs f1 f2) ws e =  case instanciar (map fst vs) f1 ws e of{
                                                Just a -> Just $ multisubst f2 (cleanSndNothing a);
                                                Nothing ->  case instanciar (map fst vs) f2 ws e of {
                                                                Just a ->  Just $ multisubst f1 (cleanSndNothing a);
                                                                Nothing -> Nothing}}

aWideLemma l ws = cWide (aLemma l ws)

cleanSndNothing :: [(a, Maybe b)] -> [(a,b)]
cleanSndNothing xs = catMaybes $ map (\(a,b) -> case b of { Nothing -> Nothing; Just y -> Just (a,y)}) xs
-- ignora tipos de las variables ... :(
-- ignora lemas con case
instanciar :: [Name] -> HExp -> [Name] -> HExp -> Maybe [(Name, Maybe HExp)]
instanciar vs e@(Atm Var v) ws f@(Atm Var w) = case (v `elem` vs, w `elem` ws) of {
                                           (True, True) -> Just [(v, Nothing)];
                                           (True, False) -> Just [(v, Just f)];
                                           (False, True) -> Nothing;
                                           (False, False) -> if v == w then Just [] else Nothing;
                                           }
instanciar vs e@(Atm Con c) ws f@(Atm Con k) = if c == k then Just [] else Nothing
instanciar vs e@(App a b) ws f@(App c d) = case allJust [instanciar vs a ws c, instanciar vs b ws d] of {
                                                Just xs ->  if isFunction (concat xs) then Just (concat xs) else Nothing;
                                                Nothing -> Nothing;
                                                }
instanciar vs (Abs x b) ws (Abs y g) = case instanciar (x:vs) b (y:ws) g of{
                                            Just xs -> case lookup x xs of {
                                                        Just u -> case u of {
                                                                    Nothing -> Just (removeFromFunction x xs);
                                                                    Just _ -> Nothing;};
                                                        Nothing -> Just xs};
                                            Nothing -> Nothing;
                                            }
instanciar vs (Cas e cs) ws (Cas f gs) =  Nothing
instanciar _ _ _ _ = Nothing



mainTactic:: [Data] -> Env -> Tactic AHExp
mainTactic ds es objs = firstJustF [comptriv es, triv, computeDontEndInCas es, lema, indc ds es, compute es] objs
--mainTactic ds es objs = firstJust [triv objs, compute es objs, lema objs, indc ds es objs]

comptriv  es objs = case compute es objs of {
                            Just [a] -> triv a;
                            _ -> Nothing;
                            }
                             


data Trace a = Fin | Incompleto | Paso a (Trace a) | Casos [([a],  Trace a)]    
    deriving (Eq)

traceTactic :: Tactic AHExp -> Obj AHExp -> Trace AHExp
traceTactic t o@(ho, to) =  Paso to $ case t o of {
                       Nothing ->  Incompleto;
                       Just [] -> Fin;
                       Just [(xs, x)] -> traceTactic t (xs, x);
                       Just xs -> Casos ( map (\  (hs, tes)  -> (hs \\ ho, traceTactic t (hs, tes) )) xs )
                            }

cutSingleStepCycles :: Trace AHExp -> Trace AHExp
cutSingleStepCycles (Paso x e@(Paso y (Paso u zs))) = if x==u then Paso x (Paso y (Paso u Incompleto)) else Paso x (cutSingleStepCycles e)
cutSingleStepCycles (Paso x (Paso y zs)) = if x==y then Paso x (Paso y Incompleto) else Paso x (cutSingleStepCycles (Paso y zs))
cutSingleStepCycles (Paso x a) = Paso x (cutSingleStepCycles a)
cutSingleStepCycles (Casos xs) = Casos (map (\(hs,t) -> (hs, cutSingleStepCycles t)) xs)
cutSingleStepCycles a = a

hojas :: Trace a -> [([a], a)]
hojas Fin = []
hojas Incompleto = []
hojas (Paso x xs) = case hojas xs of {[] ->[([],x)]; a ->a}
hojas (Casos xs) = concat $ map (\(hs, x) -> map (\(hs',t) -> (hs++hs',t)) (hojas x)) xs


instance Show a => Show (Trace a) where
    show Fin = "Fin"
    show Incompleto = "Incompleto"
    show (Paso x xs) = show x ++ "\n" ++ show xs
    show (Casos xs) = "\nInduccion\n" ++ concat (map (\ (hs, t) -> (concat (map (\ u -> "\n\nH)" ++ show u ++ "\n") hs) 
                        ++ "\nTesis\n" ++ (indentar $ show t) ++ "\n" )) xs)  

indentar = concat . map ("\n    "++)  . lines


