module Compute where
import Syntax
import SimpleSubst
import Misc

import Data.Maybe
import Data.List

type Env = [(Name, HExp)]

type ComputeRule = HExp -> Maybe HExp

cDef :: Env -> ComputeRule 
cDef env (Atm Var v) = lookup v env
cDef _ _ = Nothing

cApp :: ComputeRule
cApp (App e f)  = case e of {
                        Abs x b -> Just $ subst b x f;
                        h -> Nothing}
cApp _ = Nothing

cCas :: ComputeRule
cCas (Cas e cs) = case listParams e of {
                        (Atm Con c, hs) -> case lookup2 c cs of{
                                            Nothing -> error "Case mal formado ";
                                            Just (vs, g) -> Just $ multisubst g (zip vs hs) 
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
cWide cr x = case cr x of {
                Just a -> Just a;
                Nothing -> case x of {
                                App e f -> case cWide cr e of {
                                                Just o -> Just $ App o f ;
                                                Nothing -> case cWide cr f of {
                                                            Just o -> Just $ App e o;
                                                            Nothing -> Nothing;
                                                            };};
                                Cas e cs -> case cWide cr e of{
                                                Nothing -> Nothing;
                                                Just h -> Just $ Cas h cs };
                                Abs y b -> case cWide cr b of {
                                                Just o -> Just $ Abs y o;
                                                Nothing -> Nothing;
                                                };
                                _ -> Nothing; }; }

cLazy :: Env -> ComputeRule
cLazy env e = firstJust [cDef env e, cApp e, cCas e] 

cLeftLazy :: Env -> ComputeRule
cLeftLazy env = cLeftAppCas $ cLazy env

cWideLazy :: Env -> ComputeRule
cWideLazy env = cWide $ cLazy env

cRepeatButDontEndInCas :: ComputeRule -> ComputeRule
cRepeatButDontEndInCas f e = find (not . hasCas) $ reverse $ tail $ repetirL e f 

hasCas :: HExp -> Bool
hasCas (Atm Var v)    = False
hasCas (Atm Con c)    = False
hasCas (App e f)  = (hasCas e)||(hasCas f)
hasCas (Abs y b)  = hasCas b
hasCas (Cas e cs) =  True

isJammedOnCase = isJust . jammedCase

jammedCase :: HExp -> Maybe (Name, [(Name, [Name])])
jammedCase (Atm Var v)    = Nothing
jammedCase (Atm Con c)    = Nothing
jammedCase (App e f)  = jammedCase e
jammedCase (Abs y b)  = Nothing
jammedCase (Cas (Atm Var x) cs) = Just (x, map (\(x,y,z) -> (x,y)) cs) 
jammedCase (Cas e cs) =  jammedCase e
