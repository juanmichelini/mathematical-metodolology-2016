module Type where 
import Syntax
import Util
import Data.Maybe
import Data.List

{- ## TYPES ## -}
data Type = TAtm TAtm | TBin TBin Type Type 
            deriving (Eq, Ord, Show) 

data TAtm = TVar TVar | TCon TCon
            deriving (Eq, Ord, Show) 

data MType = MType [TVar] Type

type TVar = String -- Variables
type TCon = String -- Variables

data TBin = TCom | TApp
            deriving (Eq, Ord, Show) 

{- ## SHOW ## -}

{- ## EQUALITY ## -}
{- ## ALPHA RULE ## -}

instance Eq MType where 
    x == y = (normalForm x) == (normalForm y)

extractTVars :: Type -> [TVar]
extractTVars (TAtm (TVar x)) = [x]
extractTVars (TAtm (TCon x)) = []
extractTVars (TBin b x y) = nub (concatMap extractTVars [x,y])

normalForm :: MType -> MType
normalForm (MType vs t) = MType newvars (multiSubs subst t)
                where extractLigatedVars = filter (`elem` vs) $ extractTVars t
                      subst = zip extractLigatedVars (map (TAtm . TVar) infiniteTVars)
                      newvars = sort $ fsts subst

multiSubs :: [(TVar, Type)] -> Type -> Type
multiSubs xs (TAtm (TVar x)) = case lookup x xs of { Just y -> y; Nothing -> TAtm $ TVar x}
multiSubs xs (TAtm (TCon x)) = (TAtm (TCon x))
multiSubs xs (TBin b x y) = TBin b (multiSubs xs x) (multiSubs xs y)
 
infiniteTVars :: [TVar]
infiniteTVars =  ["a", "b", "c", "d", "e"] ++ map (show) [0..]

inferirConDatasC :: DatasC -> Term -> Maybe (Type, [(Atm, Type)])
inferirConDatasC datas x = 
    case inferir x of {
        Nothing -> Nothing;
        Just (tipo,contexto) -> 
                let sustHig = renombrar2 (snds datas) (tipo:(snds contexto))
                    tipoh = multiSubs sustHig tipo 
                    contextoh = mapSnd (multiSubs sustHig) contexto
                    cs =  (mapFst  Con datas) ++ (contextoh)
                    eqs = contextToEquations cs
                in case unificar1 eqs of{
                            Nothing -> Nothing;
                            Just sust ->  Just (multiSubs sust tipoh, 
                                            filter (\(a,b) -> not (a `elem` (map (Con . fst) datas))) $
                                            --cosmetic filter
                                            mapSnd (multiSubs sust) contextoh);
                                };
        }

inferir :: Term -> Maybe (Type, [(Atm, Type)])
inferir (Atm x) = Just ((TAtm . TVar) "t0", [(x, (TAtm . TVar) "t0")])
inferir (Abs w b) = case inferir b of {
                    Nothing -> Nothing;
                    Just (t, c) -> case lookup (Var w) c of{
                                        Just s -> Just (TBin TCom s t, filter ((/= (Var w)) . fst) c);
                                        Nothing -> Just (TBin TCom ((TAtm . TVar) (mFresh (t: (map (snd) c) ))) t, c) ;
                                    };
                    }
inferir (App x y) = case (inferir x, inferir y) of {
                         (Just (t0,c0), Just (t1,c1)) ->
                                let sustHig = renombrar2 (t0:(snds c0)) (t1:(snds c1))
                                    t1h = multiSubs sustHig t1
                                    c1h = mapSnd (multiSubs sustHig) c1
                                    t0h = t0
                                    c0h = c0
                                    cs = c0h ++ c1h
                                    eqs = contextToEquations cs
                                    fvars = mFreshs (t0h:t1h:(snds cs))
                                    ti = (TAtm . TVar) (fvars!!0)
                                    td = (TAtm . TVar) (fvars!!1)
                                    neqs = ((t0h, TBin TCom ti td):(ti, t1h):eqs)
                                in case unificar1 neqs of{
                                                Nothing -> Nothing;
                                                Just sustUni -> Just (multiSubs sustUni td, mapSnd (multiSubs sustUni) cs);
                                             };
                         _ -> Nothing;
                         }

renombrar2 :: [Type] -> [Type] -> [(TVar,Type)]
renombrar2 xs ys = zip varsYs (map (TAtm . TVar) (mFreshs (xs++ys)))
                where varsYs = nub (concatMap extractTVars ys)



contextToEquations :: Eq a => [(a, b)] -> [(b,b)]
contextToEquations [] = []
contextToEquations ((v,t):xs) = case lookup v xs of {
                                    Nothing -> contextToEquations xs;
                                    Just y -> (t,y):(contextToEquations xs);
                                 }



mFresh :: [Type] -> TVar
mFresh xs = head $ mFreshs xs   

mFreshs :: [Type] -> [TVar]
mFreshs xs = filter (not . (flip elem (concatMap extractTVars xs))) infiniteTVars

                         
singleVar :: Type -> Maybe TVar
singleVar (TAtm (TVar x)) = Just x
singleVar _ = Nothing


reps :: Eq a => [a] -> [a]
reps [] = []
reps (x:xs) = case x `elem` xs of {
                False -> repsxs;
                True -> x:repsxs;
                }
                where repsxs = reps xs 


unificar1 :: [(Type,Type)] -> Maybe [(TVar, Type)]
unificar1 xs = (whileMaybes [ descomp1s, despejarD] xs) >>= equationsASubs

equationsASubs :: [(Type,Type)] -> Maybe [(TVar, Type)]
equationsASubs [] = Just []
equationsASubs ((TAtm (TVar x), t):xs) = (equationsASubs xs) >>= (Just . ((x,t):))
equationsASubs ((t, TAtm (TVar x)):xs) = (equationsASubs xs) >>= (Just . ((x,t):))
equationsASubs _ =  error "unificar mal"


descomp1  :: (Type, Type) -> Maybe (Bool, [(Type, Type)])
descomp1  (TBin j x y, TBin k a b) = if j==k then Just (True, [(x,a),(y,b)]) else Nothing
descomp1  (TAtm (TVar x), TAtm (TVar y)) = if x == y then Just (True, []) else Just (False, [(TAtm (TVar x), TAtm (TVar y))])
descomp1  (TAtm (TVar x), y)  = if x `elem` (extractTVars y) then Nothing else Just (False, [(TAtm (TVar x), y)])
descomp1  (y, TAtm (TVar x))  = if x `elem` (extractTVars y) then Nothing else Just (False, [(TAtm (TVar x), y)])
descomp1  (x, y) = if x == y then Just (True, []) else Nothing

descomp1s  :: [(Type, Type)] -> Maybe (Bool, [(Type, Type)])
descomp1s xs = case allJust (map descomp1 xs) of{
                    Nothing -> Nothing;
                    Just as -> case any fst as of {
                                    False -> Just (False, xs);
                                    True  -> Just (True, (concat . snds) as);
                                };
                                }

filterSingleVars :: [(Type,Type)] -> [(TVar, Type)]
filterSingleVars ((TAtm (TVar x), a):xs) =  (x,a):(filterSingleVars xs)
filterSingleVars ((a, TAtm (TVar x)):xs) =  (x,a):(filterSingleVars xs)
filterSingleVars ((a, b):xs) =  (filterSingleVars xs)
filterSingleVars [] =  []

despejarD :: [(Type, Type)] -> Maybe (Bool, [(Type, Type)])
despejarD xs = case singlevarsrep of {
                    ((x,t):_) -> case x `elem` (extractTVars t) of {
                                 True -> Nothing;
                                 False -> Just (True, (TAtm (TVar x), t):( map (\(a,b) -> (multiSubs [(x, t)] a, multiSubs [(x, t)] b)) xs));
                                 };
                    [] -> Just (False, xs) 
                    ;}
                    where singlevars = filterSingleVars xs
                          allvars  =  concatMap (\(a,b)-> extractTVars a ++ extractTVars b) xs
                          allvarsrep =  reps allvars
                          singlevarsrep = filter ((flip elem allvarsrep) . fst) singlevars


-- ENUMERAR
type DatasH = (TVar, [(Con, [Type])]) -- estilo haskell abreviado
type DatasC = [(Con, Type)] -- estilo expandido

datasH2C :: DatasH -> DatasC
datasH2C (t, xs) = mapSnd  ((foldr (TBin TCom)  (TAtm (TCon t)))) xs

datasH2rec :: DatasH -> DatasC
datasH2rec (t, xs) = [(t ++ "prim", 
                       foldr ((TBin TCom) . (foldr (TBin  TCom) (TAtm (TVar varnueva)))) (TAtm (TVar varnueva)) (snds xs) )]
                       where varnueva =  (mFresh . snds . datasH2C) (t, xs)







primitiveRec :: DatasH -> Term
primitiveRec (n, xs) = undefined  



allPossibleEquations :: Eq a => [(a, b)] -> [(b,b)]
allPossibleEquations [] = []
allPossibleEquations ((v,t):xs) = map (\(w,s) -> (t,s)) (filter ((==v) . fst ) xs)  
                                    ++ allPossibleEquations xs


returnsType :: Type -> Type -> Bool
returnsType t (TAtm x) =  False
returnsType t (TBin TCom x y) = y == t || returnsType t y

returnsTypeM :: Type -> Type -> Maybe [Type]
returnsTypeM t o | t == o =  Just []
                 | otherwise = case o of {
                                (TBin TCom x y) -> case returnsTypeM t y of {
                                    Nothing -> Nothing;
                                    Just as -> Just (x:as);
                                    };
                                _ -> Nothing;
                                }

parsAndRet :: Type -> ([Type], Type)
parsAndRet (TAtm x) = ([], TAtm x)
parsAndRet (TBin TCom x (TAtm y)) = ([x], TAtm y)
parsAndRet (TBin TCom x ys) = case parsAndRet ys of {
                             (pars, ret) -> (x:pars, ret);
                             }


                  

cantApps :: Term -> Int
cantApps (Atm _) = 0
cantApps (App x y) = 1 + (cantApps x) + (cantApps y)


lastRet :: Type -> Type
lastRet (TAtm x) =  TAtm x
lastRet (TBin TCom x y) = lastRet y 

cantComs :: Type -> Int
cantComs (TAtm x) =  0
cantComs (TBin TCom x y) = 1 + cantComs y 

type TEnv =  [(Term, Type)]
