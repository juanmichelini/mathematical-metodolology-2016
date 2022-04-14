module Prove  where 
import Syntax
import Compute
import Type
import Util
import Data.Maybe
import Data.List
import Debug.Trace
import Control.Monad
import Data.Ord

data Affirm = Affirm [(Var, Type)] Term Term 
            deriving (Ord, Show)



instance Eq Affirm where
    (Affirm vs1 y1 z1) == (Affirm vs2 y2 z2) = y1==y2 && z1==z2 && (sort vs1 == sort vs2)

type Imp a = ([a], a)


type Tactic a = Imp a -> Maybe [(Comment, Imp a)]


fund :: Env -> TEnv -> Term -> Int 
fund env tenv (Atm (Var x)) = case lookup (Var x) env of { Nothing -> 0; Just y -> fund (filter ((/=Var x).fst) env) tenv y}
fund env tenv (Atm (Con x)) = 1
fund env tenv (App x y) = if fx > fy  then fx + fy else fy
                        where (fx, fy) = (fund env tenv x, fund env tenv y)
fund env tenv (Abs x b) = 1 + (fund env tenv b)
fund env tenv (Cas t cts) =  (length . concat .  snds .fsts ) cts + ( (foldl1 max) $ (map (fund env tenv)) $ (t:(snds cts)))


substA :: Affirm -> Var -> Term -> Affirm
substA (Affirm vs e f) v g = Affirm vs (substitute v g e) (substitute v g f) 

compareDep :: Env -> Affirm -> Maybe Ordering
compareDep env (Affirm _ b c) = case (all (`elem` bd) cd, all (`elem` cd) bd) of{    
                                    (True, True)  -> Just EQ;
                                    (True, False) -> Just GT;
                                    (False, True) -> Just LT;
                                    (False, False) -> Nothing;
                                    } where bd = dependencies env b; 
                                            cd = dependencies env c;

compareDepInt :: Env -> Affirm -> Maybe Int
compareDepInt env (Affirm _ b c) = case (count (`elem` bd) cd, count (`elem` cd) bd) of{    
                                       (n, m)  -> if (n /= length bd) || (m /= length cd)
                                                  then Nothing
                                                  else Just (n-m);
                                       } where bd = dependencies env b; 
                                               cd = dependencies env c;
                                               count p = length . (filter p)

simplifies :: Env -> Affirm -> Bool
simplifies env a = (Just GT == compareDep env a)

simplifiesOrd :: Env -> Affirm -> Affirm -> Ordering 
simplifiesOrd env (Affirm a b c) (Affirm x y z) =  compare  (yd - zd) (bd - cd)
                                 where bd = length $ dependencies env b;  yd = length $ dependencies env y; 
                                       cd = length $ dependencies env c;  zd = length $ dependencies env z;

floatsDep :: Env -> Affirm -> Bool
floatsDep env (Affirm a b c) = (all (`elem` bd) cd) && ((==[GT]) $ take 1 $ filter (/=EQ) $  zipWith compare bo co)
                                 where bs = termToAtm b; bd = dependencies env b; bo = map (length .(dependenciesAtm env)) bs
                                       cs = termToAtm c; cd = dependencies env c; co = map (length .(dependenciesAtm env)) cs

soloFloatsDep :: Env -> Affirm -> Bool
soloFloatsDep env (Affirm a b c) = (sort bd == sort cd) && ((==[GT]) $ take 1 $ filter (/=EQ) $  zipWith compare bo co)
                                 where bs = termToAtm b; bd = dependencies env b; bo = map (length .(dependenciesAtm env)) bs
                                       cs = termToAtm c; cd = dependencies env c; co = map (length .(dependenciesAtm env)) cs

floatsDepOrd :: Env -> Affirm -> Affirm -> Ordering
floatsDepOrd env (Affirm a b c) (Affirm x y z) = case filter (/=EQ) $ zipWith compare (zipWith compare bo co) (zipWith compare yo zo) of {
                                                    [] -> EQ;
                                                    (x:_) -> x}
                                 where bs = termToAtm b; bo = map (length .(dependenciesAtm env)) bs
                                       cs = termToAtm c; co = map (length .(dependenciesAtm env)) cs
                                       ys = termToAtm y; yo = map (length .(dependenciesAtm env)) ys
                                       zs = termToAtm z; zo = map (length .(dependenciesAtm env)) zs

floatsEnv :: Env -> Affirm -> Bool
floatsEnv env (Affirm a b c) = (==[GT]) $ take 1 $ filter (/=EQ) $  zipWith (ordEnv env) bs cs
                                 where bs = termToAtm b;
                                       cs = termToAtm c; 

floatsEnvOrd :: Env -> Affirm -> Affirm -> Ordering
floatsEnvOrd env (Affirm a b c) (Affirm x y z) = undefined 
                                                                                                    
ordEnv :: Env -> Atm -> Atm -> Ordering
ordEnv env x y = case (elemIndex x env' , elemIndex y env' ) of {
                      (Nothing, Nothing) -> EQ; 
                      (Just _, Nothing) -> GT;
                      (Nothing, Just _) -> LT;
                      (Just x, Just y) -> compare x y; 
                      } where env' =  fsts env;


countDiff :: (Eq a) => [a] -> Int
countDiff xs = length (nub xs)

dependencies :: Env -> Term -> [Atm]
dependencies env t = nub $ concatMap (dependenciesAtm env) (nub $ termToFreeAtmCas t)

dependenciesAtm :: Env -> Atm -> [Atm]
dependenciesAtm env t =  (t:)$  case lookup t env of {
                            Nothing -> [];
                            Just  k->   nub $ ((concatMap (dependenciesAtm env)) . filter (/= t) . termToFreeAtmCas) k;
                            }

idependencies :: Env -> Term -> [Atm]
idependencies env t = nub $ concatMap (idependenciesAtm env) (nub $ termToFreeAtm t)
                            
idependenciesAtm :: Env -> Atm -> [Atm]
idependenciesAtm env t = case lookup t env of {
                            Nothing -> [];
                            Just  k->   nub $ (filter (/= t) . termToFreeAtm) k;
                            }

data Reason = Simp | Floe | Flod | Reor | Basu
                deriving (Eq,Show)

data SideComment = Compute | Lemma Reason Affirm 
                deriving (Eq,Show)
    
data Comment =   NoIdea 
               | Triv 
               | Loop
               | LeftComment SideComment | RightComment SideComment | BothComment SideComment SideComment
               | Induction Var 
               | Caso Var 
                deriving (Eq,Show)


data Proof = PFail | PDone | PStep Affirm Comment Proof | PInd Affirm Comment [(Comment, ([Affirm], Proof))]
                deriving (Eq,Show)

containsIndc :: Proof -> Bool
containsIndc (PInd _ _ _) = True
containsIndc _ = False

mapProof :: (Affirm -> Affirm) -> Proof -> Proof
mapProof f (PStep a c ps) = PStep (f a) c (mapProof f ps)
mapProof f (PInd  a c ps) = PInd (f a) c [ (c, (map f as, mapProof f qs)) | (c, (as, qs)) <-  ps]
mapProof f x = x


data Rec = Rec 
           { simp :: [Affirm]
           , flod :: [Affirm]
           , floe :: [Affirm]
           , reor :: [Affirm]
           , basu :: [Affirm]
           , todo :: [Affirm]
           } deriving (Eq, Show)
           
emptyRec  = Rec [] [] [] [] [] []

mainTactic :: [DatasH] -> Env -> Rec -> Affirm -> Proof
mainTactic ds env rec conj = 
    case triv conj of {
            True -> PStep conj Triv PDone;
            False -> case bothSides (computeDontEndInCas env) conj of{
                    Just (l,a) -> PStep conj l (mainTactic ds env rec a);
                    Nothing -> case applyRec env rec conj of {
                        (Just (l, nconj)) -> PStep conj (l) (mainTactic ds env rec nconj);
                        Nothing -> case indcFst ds env conj of {
                                        Just (com, xs) -> PInd conj com (map (\ (c, (hs, t)) -> (c, (hs, mainTactic ds env  (addAffirms env rec hs)  t) )) xs);
                                        Nothing -> PStep conj NoIdea PFail;
                                        }
                                };
    }
    }

applyRec :: Env -> Rec -> Affirm -> Maybe (Comment, Affirm)
applyRec env rec conj = firstJust 
                               [ (bothSides (\vs t -> addReason Simp (applyLemmasC cWide (simp rec) vs t)) conj)
                               , (bothSides (\vs t -> addReason Flod (applyLemmasC cWide (flod rec) vs t)) conj)
                               , (bothSides (\vs t -> addReason Floe (applyLemmasC cWide (floe rec) vs t)) conj)
                               
                               , (bothSides (\vs t -> addReason Reor (applyLemmasC (cBottomUp . cIf  (\ x y -> GT == masOrd x y)) (reor rec) vs t)) conj)
                               ] 

applyRecT :: Env -> Rec -> Term -> Maybe Term
applyRecT env rec t = fmap (snd) $ firstJust [ applyLemmasC cWide (simp rec) [] t
                                             , applyLemmasC cWide (flod rec) [] t
                                             , applyLemmasC cWide (floe rec) [] t 
                                             , applyLemmasC (cBottomUp . cIf  (\ x y -> GT == masOrd x y)) (reor rec) [] t
                                             ] 

triv (Affirm _ y z) = y == z

applyRecNC :: Env -> Rec -> Affirm -> Maybe (Affirm)
applyRecNC env rec conj = (applyRec env rec conj) >>= (Just . snd)

bothSides :: ([Var] -> Term -> Maybe (SideComment, Term)) -> Affirm -> Maybe (Comment, Affirm)
bothSides f (Affirm vs y z) = case (f (fsts vs) y, f (fsts vs) z) of {
                                 (Just (c,d), Just (k,j)) -> Just (BothComment c k, Affirm vs d j);
                                 (Nothing, Just (k,j)) -> Just (RightComment k, Affirm vs y j);
                                 (Just (c,d), Nothing) -> Just (LeftComment c, Affirm vs d z);
                                 (Nothing, Nothing) -> Nothing;
                                 }

computeDontEndInCas :: Env -> ([Var] -> Term -> Maybe (SideComment, Term))
computeDontEndInCas env vs y = case  cWide (cNotCase env) y of {
                                    Just h -> Just (Compute, h); 
                                    Nothing -> Nothing;
                                    }



applyLemmas :: [Affirm] -> [Var] -> Term -> Maybe (Affirm, Term)
applyLemmas ls vs e = enPos 0 $ anyJust $ map (\ u -> case aWideLemma u vs e of {Just w -> Just (u, w); Nothing -> Nothing;}) ls

applyLemmasC :: (ComputeRule -> ComputeRule) -> [Affirm] -> [Var] -> Term -> Maybe (Affirm, Term)
applyLemmasC cr ls vs e = enPos 0 $ anyJust $ map (\ u -> case cr (aLemma u vs) e of {Just w -> Just (u, w); Nothing -> Nothing;}) ls

addReason :: Reason -> Maybe (Affirm, Term) -> Maybe (SideComment, Term)
addReason r Nothing = Nothing
addReason r (Just (l, t)) = Just (Lemma r l, t)

aLemma :: Affirm -> [Var] -> Term -> Maybe Term 
aLemma l@(Affirm vs f1 f2) ws e =  case instanciar (fsts vs) f1 ws e of{
                                                Just a -> Just $ multisubstitute a f2 ;
                                                Nothing -> Nothing; }

aWideLemma  l ws = cWide  (aLemma l ws)
aWideLemmaL l ws = cWideL (aLemma l ws)

instanciar :: [Var] -> Term -> [Var] -> Term -> Maybe [(Var, Term)]
instanciar vs e@(Atm (Var v)) ws f = case (v `elem` vs, v `elem` ws) of {
                                           (True, _) -> Just [(v, f)]; 
                                           (False, False) -> if e == f  then Just [] else Nothing;
                                           (False, True)  -> Nothing;
                                           }

instanciar vs e@(Atm (Con c)) ws f@(Atm (Con k)) = if c == k then Just [] else Nothing
instanciar vs e@(App a b) ws f@(App c d) = case allJust [instanciar vs a ws c, instanciar vs b ws d] of {
                                                Just xs ->  if isFunction (concat xs) then Just (concat xs) else Nothing;
                                                Nothing -> Nothing;
                                                }
instanciar _ _ _ _ = Nothing


indc :: [DatasH] -> Env -> (Var, Type) -> Affirm -> Maybe (Comment, [(Comment, ([Affirm], Affirm))])
indc ds env (v,t) e@(Affirm vs y z) = case elem (v,t) vs of {
                                    False -> Nothing;
                                    True -> case lookup t (mapFst (TAtm . TCon) ds) of { 
                                                Nothing -> Nothing;
                                                Just a -> Just $ (Induction v, map (\x->(Caso v ,x)) {- $ map (appFst(++xs)) -}
                                                 $ instanciarPpio v e $ armarPpio $ nombrarPar (env')  $ marcarHip (extractCon t, a));};
                                    }where env' = (hexpsA e) ++ {- (concat (map hexpsA xs)) ++ -} (map (Atm . fst) env)  ++  (map (snd) env) 
                                           hexpsA (Affirm vs y z) = (map ((Atm . Var) . fst) vs) ++ [y,z] 
                                           extractCon (TAtm (TCon x)) = x;
                                          

indcFst :: [DatasH] -> Env -> Affirm -> Maybe (Comment, [(Comment, ([Affirm], Affirm))])
indcFst ds env e@(Affirm vs y z) = case vs of {
                                    [] -> Nothing;
                                    (v:_) -> indc ds env v e;
                                    }

nombrarPar :: [Term] -> [(Con, [Bool])] -> [(Con, [(Var, Bool)])]
nombrarPar env cs = map (\(c, bs) -> (c,  zip (freshs (env)) bs)) cs

armarPpio :: [(Con, [(Var, Bool)])] ->  [([Term], Term)]
armarPpio ppio = map (\(c,vs) -> ((map ((Atm . Var) .fst)) $ filter snd vs, appParams (Atm (Con c), (map ((Atm . Var) . fst) vs)))) ppio   
 
instanciarPpio :: Var -> Affirm -> [([Term], Term)] -> [([Affirm], Affirm)]
instanciarPpio v (Affirm vs y z) ppio = map (\(hs,t) -> (map (substA e' v) hs, substA e' v t)) ppio  
                                    where vs' =  filter ((/=v).fst) vs
                                          e' = Affirm vs' y z

marcarHip :: DatasH -> [(Con, [Bool])]
marcarHip (t, cvs) = mapSnd (map (== TAtm (TCon t))) cvs

-- Analyze lemmas --

permuta :: Affirm -> Bool
permuta (Affirm ws x y) = (sort (termToAtm x)) == (sort (termToAtm y))

soloPermuta :: Affirm -> Bool
soloPermuta (Affirm ws x y) = (head x') == (head y') && (sort x') == (sort y') 
                        where x' = termToAtm x; y' = termToAtm y

masOrd :: Term -> Term -> Ordering
masOrd t1 t2 =  case filter (/=EQ) $ zipWith (compare) (termToAtmArgs t1) (termToAtmArgs t2) of {
                     [] ->  case take 1 $ filter (/=EQ) $  zipWith (compare) (alturas t1) (alturas t2) of {
                                [] -> EQ;
                                (x:xs) -> x;
                                };
                     (LT:_) -> LT;
                     (GT:_) -> GT;;
                     }

flipAffirm (Affirm vs y z) = (Affirm vs z y)

data FlowAffirm = Swap | Float | Reord
                deriving (Eq, Ord, Show)

toJera :: Affirm -> Maybe FlowAffirm
toJera (Affirm vs x y) | (null sxs) && (null sys) && (head xs == head ys) = Just Reord
                      | (null sxs) && (null sys) && (head xs /= head ys) = Just Float
                      | not (null sxs) || not (null sys) = Just Swap
                      | otherwise = Nothing
                      where xs = nub $ termToAtm x;
                            ys = nub $ termToAtm y;
                            int = intersect xs ys;
                            sxs = xs \\ int;
                            sys = ys \\ int;

toJeraAtm :: Affirm -> [(Atm, (Int, Int, Int))]
toJeraAtm a@(Affirm vs x y) = case toJera a of{
                                (Just Swap ) -> map (\x -> (x,(1,0,0))) (nub ((termToAtm x) ++ (termToAtm y)));
                                (Just Float) -> map (\x -> (x,(0,1,0))) (nub ((termToAtm x) ++ (termToAtm y)));
                                (Just Reord) -> map (\x -> (x,(0,0,1))) (nub ((termToAtm x) ++ (termToAtm y)));
                                Nothing -> [];
                                }

                    

addAffirm :: Env -> Rec -> Affirm -> Rec
addAffirm env rec l@(Affirm vs a b) 
                   | fa > fb = rec {simp = insertBy (compF) l  (simp rec)}
                   | fa < fb = rec {simp = insertBy (compF) l' (simp rec)}
                   | permuta l         = rec {reor = insertBy compSnd l (insertBy compSnd l' (reor rec))}
                   | otherwise = rec { basu = l:(basu rec)}
                   where l' = flipAffirm l
                         compSnd (Affirm _ x y) (Affirm _ j k) = masOrd y k
                         compF (Affirm _ x y) (Affirm _ j k) = compare ((fund env [] x) - (fund env [] y)) ((fund env [] j) - (fund env [] k))
                         fa = fund env [] a
                         fb = fund env [] b
                         
addAffirms :: Env -> Rec -> [Affirm] -> Rec
addAffirms env rec ls = foldl (addAffirm env) rec ls 

countSub :: (Term -> Bool) -> Term -> Int
countSub p x =  case x of {
                    App e f  -> (if p x then 1 else 0) +(countSub p e) + (countSub p f);
                    Cas e cs -> (if p x then 1 else 0) +countSub p e;
                    Abs y b  -> (if p x then 1 else 0) +countSub p b ;
                    _ -> 0;}

headProof :: Proof -> Affirm
headProof (PStep x _ _) = x
headProof (PInd x _ _) = x

cutSingleStepCycles :: Proof -> Proof
cutSingleStepCycles (PStep x c e@(PStep y k (PStep u j zs))) = if x==u then PStep x c (PStep y k (PStep u Loop PFail)) 
                                                                       else PStep x c (cutSingleStepCycles e)
cutSingleStepCycles (PStep x c (PStep y k zs)) = if x==y then PStep x c (PStep y k PFail) else PStep x c (cutSingleStepCycles (PStep y k zs))
cutSingleStepCycles (PStep x c a) = PStep x c (cutSingleStepCycles a)
cutSingleStepCycles (PInd x s xs) = PInd x s (map (\(c,(hs,t)) -> (c,(hs, cutSingleStepCycles t))) xs)
cutSingleStepCycles a = a

giveUpAfter :: Int -> Proof -> Proof
giveUpAfter _ PDone = PDone
giveUpAfter _ PFail = PFail
giveUpAfter _ (PInd _ _ []) = error "casos mal formados"
giveUpAfter n (PStep x s xs) 
     | n == 0 = PFail
     | n >= 0 = PStep x s (giveUpAfter (n-1) xs)
giveUpAfter n (PInd x s xs) 
     | n == 0 = PFail
     | n >= 0 = PInd x s (map (\(c,(hs,t)) -> (c,(hs, giveUpAfter (n`div`2) t))) xs)
                                     where cant = length xs

giveUp :: Int -> Proof -> Maybe (Proof)
giveUp _ PDone = Nothing
giveUp _ PFail = Just PFail
giveUp _ (PInd _ _ []) = error "casos mal formados"
giveUp n (PStep x s xs) | n <= 0 = Just PFail
                        | n > 0 = do k <- (giveUp (n-1) xs);
                                     return (PStep x s k)
giveUp n (PInd x s xs) | n <= 0 = Just PFail
                       | n > 0 = do ks <- f (n-1) xs;
                                     return (PInd x s ks)
                          where f n [] = Just []
                                f n ((c, (hs,t)):xs) =
                                  case giveUp n t of{
                                    (Just a) -> Just [(c,(hs, a))];
                                    Nothing  -> case f (n - 1 - (largo t)) xs of {
                                                    Nothing -> Nothing;
                                                    Just [] -> Nothing;
                                                    Just (a:as) -> Just ((c, (hs,t)):a:as);
                                                    }}
largo :: Proof -> Int
largo PDone = 0
largo PFail = 0
largo (PInd x s xs) = 1 + ( sum (map (\(c,(hs,t)) -> largo t) xs) )
largo (PStep x _ xs) = 1 + (largo xs)

proofToList :: Proof -> [Affirm]
proofToList PDone = []
proofToList PFail = []
proofToList (PStep x _ xs) = x:(proofToList xs)
proofToList (PInd x _ xs) = (x:) $ concatMap (proofToList . snd . snd) xs


proofToHojas :: Proof -> [([Affirm], Affirm)]
proofToHojas PDone = []
proofToHojas PFail = []
proofToHojas (PStep x _ xs) = case proofToHojas xs of {[] ->[([],x)]; a -> a}
proofToHojas (PInd x _ xs) = (([], x):) $ concat $ map (\(c, (hs, x)) -> map (\(hs',t) -> (hs++hs',t)) (proofToHojas x)) xs

proofCompleto :: Proof -> Bool
proofCompleto PDone = True
proofCompleto PFail = False
proofCompleto (PStep x _ xs) = proofCompleto xs
proofCompleto (PInd x _ xs) = all (proofCompleto . snd . snd) xs




prove :: Int -> [DatasH] -> Env -> Rec -> Affirm -> Proof
prove n d env rec t = (try (giveUp n)) $ cutSingleStepCycles $ (mainTactic d env rec t)



provell :: Env -> TEnv -> [DatasH] -> Int -> Rec -> [[Affirm]] -> [Proof]
provell env tenv dats n rec (ls:lls) = case find proofCompleto $ 
                                         map (prove n dats env rec) $
                                         filter (isNothing . (applyRec env (rec)))  ls of {
                                       Nothing ->  provell env tenv dats n rec (lls); 
                                       Just k -> (k:) $ provell env tenv dats n (addAffirms env rec [headProof k]) (lls); 
                                      }
provell env tenv dats n rec [] = []
