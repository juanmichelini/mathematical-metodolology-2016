module Propose where
import Syntax
import Util
import Type
import Data.List
import Data.Maybe
import Compute
import Prove (Affirm(Affirm), Rec, Proof, simplifies, soloPermuta, masOrd, provell, idependencies, dependencies, computeDontEndInCas, applyRec, applyRecT, emptyRec, fund)
import Debug.Trace
import PrettyPrint

-- Proposing data types:
enumSimpleFiniteTypes :: Int -> DatasH
enumSimpleFiniteTypes n =   ("F"++(show n), [( "F"++(show n)++"."++(show m) , [] )  | m<-[1..n]] )

enumContainerFiniteTypes :: Int -> Int -> [DatasH]
enumContainerFiniteTypes n c = [ ("C"++(most2 d) , [("C"++(most2 d)++"."++(most1 e), (map (TAtm . TVar) e)) | e <- d ]) | d <- dist n  (take c (infiniteTVars))]

enumRecursiveTypes :: Int -> Int -> [DatasH]
enumRecursiveTypes n r = [("C"++(most2 d), [("C"++(most2 d)++"."++(show $ fromJust (elemIndex e d)), map (TAtm . TVar) e) | e <- d]) | d <- dist n (take r (repeat "rec"))]

enumContainerRecTypes :: Int -> Int -> Int -> [DatasH]
enumContainerRecTypes n c r = [("C"++(most2 d), [("C"++(most2 d)++"."++ k, e) | (e,k) <- d''])
                              | rs <- nub $ map sort $ dist n (take r (repeat "R")),
                                cs <- nub $ map sort $ dist n (take c (infiniteTVars)),
                                d <- [zipWith (++) cs rs],
                                d' <- [map (map (swap (TAtm (TVar "R")) (TAtm (TCon ("C"++(most2 d)))))) (map (map (TAtm . TVar)) d)],
                                d'' <- [zip d' (map (show) [0..])]]

most1 :: [String] -> String
most1 [] = "_"
most1 xs = filter (/= 't') $ concat $ (intersperse "_") xs

most2 :: [[String]] -> String
most2 xs = concat $ (intersperse ",") $ map (most1) xs

-- Proposing function types:
armarTip :: Int -> [Type] -> [Type]
armarTip n xs | n==0 = xs
              | n/=0 = [ TBin TCom x t | x <- xs, t <- armarTip (n-1) xs]

armarPar :: Type -> (Term -> Term, [(Var, Type)])
armarPar (TAtm x) = ( id, [])
armarPar (TBin TCom x y) = ( (Abs var) . a, (var, x):b)
        where  var  = head $ filter (not . (`elem` fb)) infiniteVars
               (a,b) = armarPar y
               fb = fsts b

-- Proposing recursion schemes:

dataAEsquema :: DatasH -> [Var] -> (Term, Type) -> (Term -> [Term] -> Term, [[(Term, Type)]])
dataAEsquema (o, ds) vs (f, TBin TCom a b) = (\t ts -> Cas t (zip consvarpara ts), disp)
                where cons    = fsts ds
                      tipopara   = snds ds
                      para      = map (zip vs) tipopara
                      varpara   = map fsts para
                      tvarpara  = map (mapFst (Atm . Var)) para
                      recs = if (TAtm (TCon o))  == a 
                               then map (map ((\r -> (r,b)) . App f . fst) . filter ((==a). snd)) tvarpara
                               else error "rec call must match data"
                      disp = zipWith (++) recs tvarpara
                      consvarpara  = zip cons varpara


-- Proposing expresions of a type:

enumApp :: Int -> Type -> [(Term, Type)] -> [Term]
enumApp n s tts =  (fsts base) ++ if n == 0 then [] else {- nub $ filter (not .  (`elem` ( fsts tts)))-} d
               where rel = mapSnd fromJust $ filter (isJust . snd) $  mapSnd (returnsTypeM s) tts
                     (base, funs) = partition (null . snd) rel
                     fargs =  filter (not . (any null) . snd)$ mapSnd (map (\u -> enumApp (n-1) u tts)) funs
                     d   =     [appParams (f, cargs) | (f, args) <- fargs, cargs <- hilar args] 
                       
enumAppRec :: Rec -> Int -> Type -> [(Term, Type)] -> [Term]
enumAppRec rec n s tts =  filter (isNothing . (applyRecT [] (rec))) (enumApp n s tts)

enumValues :: Type -> TEnv -> [Term]
enumValues t tenv = enumApp  22 t (filter (isACon . fst) tenv)

enumAppStartingRec :: Rec -> (Term, Type) -> TEnv -> [Term]
enumAppStartingRec rec (e,t) tenv =  filter (isNothing . (applyRecT [] (rec))) (enumAppStarting (e,t) tenv)

enumAppStarting :: (Term, Type) -> TEnv -> [Term]
enumAppStarting (e,t) tenv = if null pars then [] else (if any null args then [] else d)   
                        where (pars, ret) =   parsAndRet t
                              args = map (\u -> enumApp (2) u tenv) pars
                              d   =  [appParams (e, cargs) |  cargs <- hilar args] 

armarUsarTodo :: Type -> [(Term, Type)] -> [Term]
armarUsarTodo s [(x,t)] = if s == t then [x] else []
armarUsarTodo s tts = llenar
                 where posraices = nub $ mapSnd fromJust $ filter (isJust . snd) $  mapSnd (returnsTypeM s) tts
                       distresto (a, b) = filter (not.([]`elem`)) $ filter (/=[]) $ distO (length b) (deleteFstThat ((==a) . fst) tts)
                       llenar = [ addApps a args | (a,b)<- posraices,  cs <- distresto (a,b), args <- hilar $ (zipWith (armarUsarTodo) b) cs]
                       addApps = foldl App

                
                  
armarUsarTodoHead :: Type -> (Term, Type) -> [(Term, Type)] -> [Term]
armarUsarTodoHead s h tts = takeWhile ((==(fst h)) . Atm . fst . fromJust . getHead) (armarUsarTodo s (h:tts))
                  
-- Proposing instance of schemes of recursion                  


repiteAtmHasta :: Int -> [Term] -> [Term]
repiteAtmHasta n ts = filter (\t -> null $ filter (>=n) $ map length $ group $ sort $ termToAtm t) ts


enumFun :: Rec -> Var -> Type -> [DatasH] -> [(Term, Type)] -> [Term]
enumFun rec f tipo@(TBin TCom (TAtm (TCon x)) y) datas ls = repiteAtmHasta 3 $ map par apps  
         where (par, vs) = armarPar (tipo)
               vs2 = mapFst (Atm . Var) vs
               dat = (x, fromJust $ lookup x datas)
               (dae, cas) = dataAEsquema dat (filter (not . (`elem` (fsts vs))) infiniteVars) (Atm (Var f), tipo)
               (_, res) = parsAndRet tipo
               cas' = [[ if (Atm (Var f)) == g 
                         then (appParams (Atm (Var f), gs ++ (fsts.tail) vs2) , res)
                         else (e,t) | (e, t) <- cs, (g, gs) <- [listParams e] ] | cs <- cas ] 
               apps = map (dae (fst (vs2!!0))) $ hilar $ map (\c ->  enumAppRec rec 2 (lastRet (tipo)) ((tail vs2) ++ c ++ ls)) cas'
               cant xs = sum $ map (uncurry (+)) $ map (\(a,b) -> (cantApps a, cantComs b)) xs




-- Proposing equations

conjeturasSimp :: Rec -> Env -> TEnv -> PartTypedTerm -> [Affirm]
conjeturasSimp rec env tenv a = filter (\ (Affirm _ a b) -> fund env tenv a > fund env tenv b) (conjeturasSoloConDep rec env tenv a)
                          
                          
conjeturasPerm :: Rec -> Env -> TEnv -> PartTypedTerm -> [Affirm]
conjeturasPerm rec env tenv a@((e,t), vts) =  filter (\(Affirm _ e f) -> e  /= f ) 
                                        $ filter (soloPermuta) 
                                        $ map (Affirm vts e)
                                        $ sortBy masOrd 
                                        $ take 100 -- cambiar
                                        $ enumAppRec rec 2 t 
                                        $ ((mapFst (Atm . Var) vts) ++)
                                        $ (\ q -> filter (\(g,_) -> g `elem` q) tenv)
                                        $ (map Atm (nub (termToAtm e)))

-- example Sum x y :: N [ x :: N, y :: N]
type PartTypedTerm = ((Term, Type), [(Var, Type)])

-- example f = \ x -> case x of { O -> h :: Bool []; S j -> k :: Bool [ f j :: Bool]} :: Bool
type Scheme = (Var, ((Term, Type), [(Var, [(Term, Type)])]))

saturateTerm :: (Term, Type) -> PartTypedTerm
saturateTerm (e, t) = ((foldl1 App (e:(map (Atm. Var) vars)), ret), typedvars)
                    where (pars, ret) = parsAndRet t
                          typedvars = map (\(a,b)->(b,a)) $ zip pars (freshs [e])
                          vars = fsts typedvars

allSaturations :: (Term, Type) -> [PartTypedTerm]
allSaturations (e, t) = [((foldl1 App (e:(map (Atm. Var) (vars n))), ret n), typedvars n) | n <- [0..length pars]]
                    where (pars, ret') = parsAndRet t
                          ret n = foldr (TBin TCom) ret' (drop n pars) 
                          typedvars n = take n $ map (\(a,b)->(b,a)) $ zip pars (freshs [e])
                          vars = fsts . typedvars

toPTT :: (Term, Type) -> PartTypedTerm
toPTT = head . allSaturations

joinVar :: Var -> PartTypedTerm -> [PartTypedTerm]
joinVar v ((e, t), vts) = case lookup v vts of {  
                            Nothing -> [];
                            Just s -> let vts' = delete (v,s) vts 
                                      in [ ((multisubstitute [(v, Atm (Var w))] e, t), vts')  |  (w, r) <- vts', r==s];
                                      }

permutVars :: Type -> PartTypedTerm -> [PartTypedTerm]
permutVars s ((e, t), vts) = let vs = (fsts (filter ((==s) . snd) vts));
                                 pts = permutations vs
                                 in case pts of {
                                         [] -> [];
                                         (x:xs) -> [ ((multisubstitute (zip x p) e, t), vts) | p <- map (map (Atm . Var)) xs]
                                         }
                            
substitutePTT :: Var -> PartTypedTerm -> PartTypedTerm -> PartTypedTerm                            
substitutePTT v ((e, t), vts) ((f, s), wts) 
          = case lookup v wts of {
                Nothing -> error $ "uninstantiable variable" ;
                Just r -> if r/=t 
                            then error $ "types do not match" 
                            else ((multisubstitute subs f , s) , vts'++wts')
                            }
                    where newvars = freshs $ concat $ [[e, f], map (Atm . Var . fst) vts, map (Atm . Var . fst) wts]
                          wtssinv = filter ((/=v).fst) wts
                          svts = zip (fsts vts) newvars
                          swts = zip (fsts wtssinv) (drop (length svts) newvars)
                          vts' = zip (snds svts) (snds vts)
                          wts' = zip (snds swts) (snds wtssinv)
                          e' = multisubstitute (mapSnd (Atm . Var) svts) e
                          subs = (v,e'):(mapSnd (Atm . Var) swts)



ampleDep :: Env -> TEnv -> Atm -> [PartTypedTerm]
ampleDep env tenv v = map renameReorderVars $ 
                      filter ((<=3).length.snd) $
                      a:[ ( substitutePTT w d a) | d@((_,r),_) <- sdep, (w, s) <- ets, s == r]
                    where a@((e,t), ets) =  saturateTerm (Atm v, fromJust (lookup (Atm v) tenv))  
                          deps = sortBy (\x y -> compare (length (dependencies env (Atm x))) (length (dependencies env (Atm y)))) $ (++ [v]) $ (delete v) $ dependencies env (Atm v)
                          depst = map (\x -> (Atm x, fromJust (lookup (Atm x) tenv))) deps
                          sdep =  map saturateTerm depst

amplePerm :: Env -> TEnv -> [Atm] -> [PartTypedTerm]
amplePerm env tenv vs = map renameReorderVars $ 
                        filter ((<=3).length.snd) res
                        where vst = map (\x -> (Atm x, fromJust (lookup (Atm x) tenv))) vs
                              svs = map saturateTerm vst
                              res = concatMap (instanceAny env tenv svs) svs

ampleAll :: Env -> TEnv -> [Atm] -> [PartTypedTerm]
ampleAll env tenv as = map renameReorderVars res
                    where ast = map (\x -> (Atm x, fromJust (lookup (Atm x) tenv))) as
                          svs = map (\x -> (x, saturateTerm x)) ast
                          res = concatMap (\ (x,s) -> tail $ instanceAny env tenv (snds (filter ((/=x).fst) svs)) s) svs


conjeturasSoloConDep :: Rec -> Env -> TEnv -> PartTypedTerm -> [Affirm]
conjeturasSoloConDep rec env tenv ((e,t), vts) = map (Affirm vts e)  (enumAppRec rec 2 t (vts' ++ depst))
                   where deps  =  sortBy (compWith (length . (dependencies env))) $  map Atm $ dependencies env e
                         depst = filter (\(g,_) -> g `elem` deps) tenv 
                         vts' = mapFst (Atm . Var) vts
                          
conjeturasFloatsDep :: Rec -> Env -> TEnv -> PartTypedTerm -> [Affirm]
conjeturasFloatsDep rec env tenv ((e,t), vts) = map (Affirm vts e)
                                            $ concat
                                            $ filter (not . null)
                                            $ map (filter ((tamaño e + 3 >=) . tamaño))
                                            $ map (take 1000) -- change
                                            $ [ enumAppStartingRec rec (a, b) (vts' ++ ((e',t'):depst)) | (a,b) <- depst ]
                                            where 
                                                    e'' = fst $ fromJust (getHead e) 
                                                    e' =  Atm $ e''
                                                    t' = fromJust $ lookup e' tenv
                                                    id = idependencies env e'
                                                    deps  = map Atm $ id
                                                    depst = filter (\(g,_) -> g `elem` deps) tenv 
                                                    vts'  = mapFst (Atm . Var) vts
                                                    vtsid = e'':((map Var (fsts vts)) ++ id)
                          

conjeturasAll :: Rec -> Env -> TEnv -> PartTypedTerm -> [Affirm]
conjeturasAll rec env tenv a@((e,t), vts) =  filter (\(Affirm _ e f) -> e /= f ) 
                                        $ map (Affirm vts e)
                                        $ take 1000 -- cambiar
                                        $ enumAppRec rec 2 t 
                                        $ ((mapFst (Atm . Var) vts) ++)
                                        $ (\ q -> filter (\(g,_) -> g `elem` q) tenv)
                                        $ (map Atm (nub (termToAtm e)))

renameReorderVars :: PartTypedTerm -> PartTypedTerm
renameReorderVars ((e,t),vts) = ((multisubstitute z e, t), w) 
                        where f = nub $ freeVars e
                              o = filter (`elem`(fsts vts)) f --ligadas
                              s = sort $ take (length o) (freshs [e]) --nuevas
                              z = zip o (map (Atm . Var) s) -- subs
                              w = [(k,t) | (v,t) <- vts, (w, Atm (Var k)) <- z, w==v]

                            

instanceAll :: Env -> TEnv -> [PartTypedTerm] -> PartTypedTerm -> [PartTypedTerm]
instanceAll env tenv ins q@((e,t), []) = [((e,t), [])]
instanceAll env tenv ins q@((e,t), (v,r):vts) = concat [ map ((substitutePTT v y) . (\ (a,b) -> (a,(v,r):b) )) (instanceAll env tenv ins ((e,t),vts)) | y <- (filter ((==r) . snd . fst) ins)]
                            
instanceAny :: Env -> TEnv -> [PartTypedTerm] -> PartTypedTerm -> [PartTypedTerm]
instanceAny env tenv ins q@((e,t), []) = [((e,t), [])]
instanceAny env tenv ins q@((e,t), (v,r):vts) = concat [ [(a,(v,r):b), substitutePTT v y (a, (v,r):b) ] | y <- (filter ((==r) . snd . fst) ins),  (a,b) <- (instanceAny env tenv ins ((e,t),vts))]
                            



disprove :: Env -> TEnv -> Affirm -> Maybe Affirm
disprove env tenv (Affirm vs xs ys) = undefined -- instanciar vs con enumvalues, computar hasta que sea solo cons todo, comparar. 




findlemas :: Env -> TEnv -> [DatasH] -> Int -> Rec -> Atm -> [Proof]
findlemas env tenv datas n rec a = provell env tenv datas n rec $ concat $
                                   (map (conjeturasSimp rec env tenv) (ampleDep env tenv a)):
                                   (map (conjeturasSimp rec env tenv) (ampleDep env tenv a)):
                                   (map (conjeturasPerm rec env tenv) (amplePerm env tenv [a])):
                                   []

plemas :: Env -> TEnv -> [DatasH] -> Int -> Rec -> Atm -> [[Affirm]]
plemas env tenv datas n rec a = concat $
                                   (map (conjeturasSimp rec env tenv) (ampleDep env tenv a)):
                                   (map (conjeturasSimp rec env tenv) (ampleDep env tenv a)):
                                   (map (conjeturasPerm rec env tenv) (amplePerm env tenv [a])):
                                   []

findlemasAll :: Env -> TEnv -> [DatasH] -> Int -> Rec -> [Atm] -> [Proof]
findlemasAll env tenv datas n rec as = provell env tenv datas n rec $ (map (conjeturasAll rec env tenv) (ampleAll env tenv as))

pfindlemasAll :: Env -> TEnv -> [DatasH] -> Int -> Rec -> [Atm] -> [Affirm]
pfindlemasAll env tenv datas n rec as =  concat (map (conjeturasAll rec env tenv) (ampleAll env tenv as))

