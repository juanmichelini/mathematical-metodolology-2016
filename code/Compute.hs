module Compute where
import Syntax
import Util

import Data.Maybe
import Data.List
import Control.Monad


type Env = [(Atm, Term)]

type ComputeRule = Term -> Maybe Term

cDef :: Env -> ComputeRule 
cDef env (Atm v) = lookup v env
cDef _ _ = Nothing

cApp :: ComputeRule
cApp (App (Abs x b) f) = Just $ multisubstitute [(x, f)] b;
cApp _ = Nothing

cCas :: ComputeRule
cCas (Cas e cs) = case listParams e of {
                        (Atm (Con c), hs) -> case listToMaybe (filter ((==c) . fst . fst) cs) of{
                                            Nothing -> error ("Case mal formado:"++c++" | " ++ (show (Cas e cs)));
                                            Just ((_,vs), g) -> Just $ multisubstitute (zip vs hs) g;
                                            };
                        _ -> Nothing;}
cCas _ = Nothing

cLeftAppCas :: ComputeRule -> ComputeRule
cLeftAppCas cr x = case cr x of {
                Just a -> Just a;
                Nothing -> case x of {
                                App e f -> case cLeftAppCas cr e of {
                                                Nothing -> Nothing;
                                                Just o -> Just $ App o f };
                                Cas e cs -> case cLeftAppCas cr e of{
                                                Nothing -> Nothing;
                                                Just h -> Just $ Cas h cs };
                                _ -> Nothing; }; }

cRightAppAbs :: ComputeRule -> ComputeRule
cRightAppAbs cr x = case cr x of {
                            Just a -> Just  a;
                            Nothing -> case x of {
                                        App e f -> case cRightAppAbs cr f of {
                                                        Nothing -> Nothing;
                                                        Just o -> Just $ App e o };
                                        Abs y b -> case cRightAppAbs cr b of {
                                                        Just o -> Just $ Abs y o;
                                                        Nothing -> Nothing;
                                                        };
                                        _ -> Nothing; }; }

cWide :: ComputeRule -> ComputeRule 
cWide cr x = listToMaybe $ cWideL cr x

cWideL :: ComputeRule -> Term -> [Term]
cWideL cr x = (maybeToList $ cr x) ++ case x of {
                                App e f -> map (\(j:k:[]) -> App j k) $ tail $ hilar [e:(cWideL cr e), f:(cWideL cr f)];
                                Cas e cs -> map (\h -> Cas h cs) $ cWideL cr e;
                                Abs y b -> map (Abs y) $ cWideL cr b ;
                                _ -> []; }

cBottomUp :: ComputeRule -> ComputeRule
cBottomUp cr (Atm x) = cr (Atm x)
cBottomUp cr (App x y) = listToMaybe $ anyJust [cBottomUp cr x >>= (return . (flip App y)), cBottomUp cr y>>= (return . (App x)), cr (App x y)]
cBottomUp cr x = error "se esperaban sólo aplicaciones"

cIf :: (Term -> Term -> Bool) -> ComputeRule -> ComputeRule
cIf p cr x = do y <- cr x
                if p x y then return y else Nothing

cLazy :: Env -> ComputeRule
cLazy env e = firstJust [cDef env e, cApp e, cCas e] 

cLeftLazy :: Env -> ComputeRule
cLeftLazy env = cLeftAppCas $ cLazy env

cWideLazy :: Env -> ComputeRule
cWideLazy env = cWide $ cLazy env

cRepeatButDontEndInCas :: ComputeRule -> ComputeRule
cRepeatButDontEndInCas f e = find (not . hasCas) $ reverse $ tail $ repetirL f e 

hasCas :: Term -> Bool
hasCas (Atm c)    = False
hasCas (App e f)  = (hasCas e)||(hasCas f)
hasCas (Abs y b)  = hasCas b
hasCas (Cas e cs) =  True

isJammedOnCase = isJust . jammedCase

jammedCase :: Term -> Maybe (Var, [(Con, [Var])])
jammedCase (Atm v)    = Nothing
jammedCase (App e f)  = jammedCase e
jammedCase (Abs y b)  = Nothing
jammedCase (Cas (Atm (Var x)) cs) = Just (x, fsts cs) 
jammedCase (Cas e cs) =  jammedCase e

cNotCase :: Env -> ComputeRule
cNotCase env e = do (h, p) <- getHead e 
                    x <- lookup h env 
                    ls <- allJust $ map getHead $ fsts $ filter (snd) $ zip p (paramsWithCase x)
                    a <- (repetir (\ u -> firstJust [cWide cApp u, cWide cCas u] )) (subsHead x e) 
                    if hasCas a then Nothing else return a 
                    where
                          isCon a = case a of { Con _ -> True; _ -> False}
                          


