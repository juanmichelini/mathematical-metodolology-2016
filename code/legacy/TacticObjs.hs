module Tactic  where
import Syntax
import Compute
import SimpleSubst
import Type
import Data.Maybe

data Obj a = A a | And (Obj a) (Obj a) | Or (Obj a) (Obj a) | If (Obj a) (Obj a) | Bot 
            deriving (Eq)

instance Show a => Show (Obj a) where
    show (A a) = show a
    show (And x y) = "(" ++ show x ++"/\\"++ show y ++ ")"
    show (Or x y) = "(" ++ show x ++"\\/"++ show y ++ ")"
    show (If x y) = "(" ++ show x ++"=>"++ show y ++ ")"
    show (Bot) = "_|_"

data Equ a = Equ a a
        deriving (Eq)

instance Show a => Show (Equ a) where
        show (Equ x y) = show x ++ "==="  ++ show y

type Objs a = ([Obj a], Obj a)

type Tactic a = Objs a -> Res a 

type Res a = Maybe (Objs a)

triv :: Tactic (Equ HExp)
triv  (xs, A (Equ y z)) | y == z = Just ([], (A (Equ y z)))
                        | otherwise = Nothing
triv  _ = Nothing

dispatch :: Tactic (Equ HExp) -> Tactic (Equ HExp)
dispatch t (xs, A (Equ y z)) = Nothing
dispatch t (xs, And y z) = case (t (xs, y), t (xs, z)) of {
                                (Just ([], v), Just ([], w)) -> Just ([], (And v w));
                                (Nothing, Just ([], w)) -> Just ([], (And y w));
                                (Just ([], v), Nothing) -> Just ([], (And v z));
                                _ -> Nothing;
                                }
dispatch t (xs, Or y z) = case catMaybes [t (xs, y), t (xs, z)] of {
                                v:_ -> Just v;
                                [] -> Nothing;
                                }
dispatch t (xs, If y z) = t ((y:xs), z)
dispatch t (xs, Bot) = Nothing

compute :: Env -> Tactic (Equ HExp)
compute env (xs, A (Equ y z)) = case (evalWideM env y, evalWideM env z) of {
                                (Just v, Just w) -> Just ([], (A (Equ v w)));
                                (Just v, Nothing) -> Just ([], (A (Equ v z)));
                                (Nothing, Just w) -> Just ([], (A (Equ y w)));
                                _ -> Nothing;
                                }
compute env _ = Nothing

indc :: [Data] -> Tactic (Equ HExp)
indc ds (xs, e@(A (Equ y z))) = case catMaybes [caseTrancado y, caseTrancado z] of {
                                [] -> Nothing;
                                (v, cvs):_ -> Just $ ([], conj $ map (\ (c, ls) -> case hips c of {
                                                                            [] -> id;
                                                                            chips -> If (conj $ map (\ w -> substO e v (Var w)) (chips))}
                                                                            $ substO e v (reCon (c , map (Var) ls))) cvs)
                                                    where hips = \ c -> case lookup c (marcarHs cvs ds) of{ Just u -> u; Nothing -> error "case mal formado"}}
                                                    
                                                                        
indc _ _ = Nothing 


lema :: Tactic (Equ HExp)
lema (ls, (A (Equ y z))) = case (applyLemmas ls y, applyLemmas ls z) of {
                             (Just v, _) -> Just $ ([], A $ Equ v z);
                             (_, Just w) -> Just $ ([], A $ Equ y w);
                             _ -> Nothing;
                             }
                                
lema _ = Nothing;

applyLemmas :: [Obj (Equ HExp)] -> HExp -> Maybe HExp
applyLemmas ls e = case catMaybes $ map (flip applyLemma e) ls of {
                        k:_ -> Just k;
                        [] -> Nothing;
                        }

applyLemma :: Obj (Equ HExp) -> HExp -> Maybe HExp
applyLemma (A (Equ f g)) e@(Var v) = case e == f of {
                                True -> Just g;
                                False -> case e == g of {
                                            True -> Just f;
                                            False -> Nothing;}}
applyLemma (A (Equ f g)) e@(Con c) = case e == f of {
                                True -> Just g;
                                False -> case e == g of {
                                            True -> Just f;
                                            False -> Nothing;}}
applyLemma l@(A (Equ f g)) e@(App a b) = case e == f of {
                                True -> Just g;
                                False -> case e == g of {
                                            True -> Just f;
                                            False -> case (applyLemma l a, applyLemma l b) of{
                                                       (Just v, _) -> Just (App v b);
                                                       (_, Just w) -> Just (App a w);
                                                       _ -> Nothing;
                                                       }}}
applyLemma l@(A (Equ f g)) e@(Cas c cs) = case e == f of {
                                True -> Just g;
                                False -> case e == g of {
                                            True -> Just f;
                                            False -> case (applyLemma l c) of{
                                                       Just v -> Just (Cas v cs);
                                                       Nothing -> Nothing;
                                                       }}}
applyLemma _ _ = Nothing

mainTacticSingle :: [Data] -> Env -> Tactic (Equ HExp)
mainTacticSingle ds es objs = case triv objs of {
                            Just _ -> Just (If Bot Bot);
                            Nothing -> case dispatch (mainTacticSingle ds es) objs of {
                                      Just r ->     Just r; 
                                      Nothing ->  case compute es objs of {
                                                    Just r -> Just r;
                                                    Nothing -> case indc ds objs of {
                                                                Just r -> Just r;
                                                                Nothing -> lema objs;
                                                        }}}}

                    
mainTactic :: [Data] -> Env -> Objs (Equ HExp) -> [Obj (Equ HExp)]
mainTactic ds es (ls, o) =  o:case mainTacticSingle ds es (ls, o) of {
                            Nothing -> [];
                            Just (hs,x) -> (mainTactic ds es (hs++ls, x))
                            }
        
    
conj :: [Obj a] -> Obj a
conj = foldr1 (And)

substO :: Obj (Equ HExp) -> Var -> HExp -> Obj (Equ HExp)
substO e v g = mapO (\x -> substE x v g) e

substE :: Equ HExp -> Var -> HExp -> Equ HExp
substE (Equ f g) v h = Equ (subst f v h) (subst g v h)

mapO :: (a -> b) -> Obj a -> Obj b 
mapO f (A a)  = A (f a) 
mapO f (And y z)  = And (mapO f y) (mapO f z)
mapO f (Or y z)  = Or (mapO f y) (mapO f z)
mapO f (If y z)  = If (mapO f y) (mapO f z)
mapO f (Bot)  = Bot
--fn :: Tactic (Equ HExp)
--fn (xs, A (Equ y z)) 
--fn (xs, And y z) 
--fn (xs, Or y z) 
--fn (xs, If y z) 
--fn Bot 

