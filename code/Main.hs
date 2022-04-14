module Main where
import Syntax
import Util
import Type
import Data.List
import Data.Maybe
import Compute
import Prove
import Debug.Trace
import Propose
import PrettyPrint

main = putStrLn $ "\\section{First Search}" ++ 
                        (concatMap (\(((nom, def), t), ls) -> 
                            ("\n\n % Ini Fun \n\n" ++ 
                                "\\subsection{$" ++ toLatex (Atm nom) ++ " = " ++ (toLatex def) ++ "$}\n\n" ++ 
                                "$" ++ (toLatex t) ++ "$\n\n" ++ 
                                (concatMap (\l -> "\\subsubsection{"++toLatex (headProof l) ++ "}\n\n" ++ toLatex l ++ "\n\n") ls) ++ 
                            "\n\n % Fin Fun \n\n ")) namedFstSel) 
                           ++
                     "\\section{Second Search}" ++
                       (concatMap (\(((nom, def), t), ls) -> 
                           ("\n\n % Ini Fun \n\n" ++ 
                               "\\subsection{$" ++ toLatex (Atm nom) ++ " = " ++ (toLatex def) ++ "$}\n\n" ++ 
                               "$" ++ (toLatex t) ++ "$\n\n" ++ 
                               (concatMap (\l -> "\\subsubsection{"++toLatex (headProof l) ++ "}\n\n" ++ toLatex l ++ "\n\n") ls) ++ 
                           "\n\n % Fin Fun \n\n ")) namedSndSel) 

datas :: [DatasH]
datas = concat [enumContainerRecTypes cantcons canrec canemb |  cantcons <- [2], canrec <-[0..1], canemb <- [0..1]]

tiposfununi =  armarTip 1 (map (TAtm . TCon . fst) datas)
tiposfunbin =  armarTip 2 (map (TAtm . TCon . fst) datas)

tipbb = tiposfununi!!0
tipnb = tiposfununi!!4
tipnn = tiposfununi!!5
tiplb = tiposfununi!!12
tipln = tiposfununi!!13
tipll = tiposfununi!!14

paciencia :: Int 
paciencia = 30

cerothTEnv :: TEnv
cerothTEnv = mapFst (Atm . Con) $ concatMap datasH2C datas

cerothRec :: Rec
cerothRec = emptyRec

candidatosFst :: [(Term, Type)]
candidatosFst = filter (\ (e,t) -> {- not (shouldContainRecursiveCall t) ||-} (contiene (Var "f") e))
                    [ (f, tipo) | aridad <- [1..2],
                                  tipo <- (armarTip aridad (map (TAtm . TCon . fst ) [datas!!1, datas!!3] )),
                                  f <- enumFun cerothRec "f" tipo datas cerothTEnv ]

shouldContainRecursiveCall :: Type -> Bool
shouldContainRecursiveCall t = 'R'`elem`(show t) --ugly hack


candidatosFstTeo :: [((Term, Type), [Proof])]
candidatosFstTeo =  [((f, t), findlemas [(Var "f", f)] ((Atm (Var "f"), t):cerothTEnv) datas paciencia cerothRec (Var "f")) | (f, t) <- candidatosFst]

candidatosFstSel ::  [((Term, Type), [Proof])]
candidatosFstSel = filter ((>3) . length  .  map headProof {- . filter containsIndc -}  . snd ) candidatosFstTeo
                        where transformLemas (Affirm _ _ c) = (Var "f") `elem` (termToAtm c)

namedFstSel ::  [(((Atm, Term), Type), [Proof])]
namedFstSel = map (\ (((def, typ), ls), n) -> let newf = (Var ("f" ++ (show n))) 
                                                  anewf = Atm newf
                                               in (((newf, substitute "f" anewf def), typ), map (substituteProof "f" anewf) ls))
                        $ zip candidatosFstSel [0,1..]
                            where substituteProof x y = mapProof (\ (Affirm a b c) -> Affirm a (substitute x y b) (substitute x y c))

fstEnv :: Env
fstEnv = [(nom, def) | (((nom, def), typ), ls) <- namedFstSel]

fstTEnv :: TEnv
fstTEnv = cerothTEnv ++ [ (Atm nom, typ) | (((nom, def), typ), ls) <- namedFstSel]

fstRec :: Rec
fstRec = addAffirms fstEnv cerothRec ( map headProof $ concat $ snds $ namedFstSel ) 

candidatosSnd :: [(Term, Type)]
candidatosSnd =  candidatosSndUni ++ candidatosSndBin

candidatosSndUni :: [(Term, Type)]
candidatosSndUni =  filter (\ (e,t) ->  (contiene (Var "f") e) && any (flip contiene e) (fsts fstEnv))
                           [ (f, tipo) | tipo <- armarTip 1 (map (TAtm . TCon . fst ) [ datas!!1, datas!!3] ),
                                         f <- enumFun fstRec "f" tipo datas fstTEnv ]

candidatosSndBin :: [(Term, Type)]
candidatosSndBin =  filter (\ (e,t) ->  (contiene (Var "f") e) && 
                                    case e of {(Abs _ (Abs y b))-> (==2) $ length  $ take 2 $ filter ((Var y)==) $ termToAtm b} && 
                                     any (flip contiene e) (fsts fstEnv))
                           [ (f, tipo) | tipo <- armarTip 2 (map (TAtm . TCon . fst ) [ datas!!1, datas!!3] ),
                                         f <- enumFun fstRec "f" tipo datas fstTEnv ]


candidatosSndTeo :: [((Term, Type), [Proof])]
candidatosSndTeo =  [((f, t), findlemas ((Var "f", f):fstEnv) ((Atm (Var "f"), t):fstTEnv) datas paciencia fstRec (Var "f"))  | (f, t) <- candidatosSnd]

candidatosSndSel ::  [((Term, Type), [Proof])]
candidatosSndSel = filter ((>=2) . length  .  map headProof . filter containsIndc  . snd) candidatosSndTeo
                        where transformLemas (Affirm _ _ c) = (Var "f") `elem` (termToAtm c)

namedSndSel ::  [(((Atm, Term), Type), [Proof])]
namedSndSel = map (\ (((def, typ), ls), n) -> let newf = (Var ("f" ++ (show n))) 
                                                  anewf = Atm newf
                                               in (((newf, substitute "f" anewf def), typ), map (substituteProof "f" anewf) ls))
                        $ zip candidatosSndSel [(length fstEnv)..]
                            where substituteProof x y = mapProof (\ (Affirm a b c) -> Affirm a (substitute x y b) (substitute x y c))

