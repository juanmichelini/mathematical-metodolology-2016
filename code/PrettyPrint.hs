module PrettyPrint where
import Syntax
--import Compute
import Type
import Prove
import Util
import Data.Maybe
import Data.List

class ToLatex a where 
    toLatex :: a -> String 

class ToLatexV a where 
    toLatexV :: [String] -> [String] -> [String] -> a -> String 
        -- vars  env       forall         lambda

class ToCLI a where 
    toCLI :: a -> String 

instance (ToCLI a, ToCLI b) => ToCLI (a,b) where
    toCLI (a,b) = "("++toCLI a++", "++ toCLI b ++ ")"

instance (ToCLI a) => ToCLI [a] where
    toCLI a = "[" ++ (concatMap ((++", ").toCLI) a) ++ "]"

instance ToCLI Char where
    toCLI a = [a]

instance ToCLI Atm where
    toCLI ((Var v)) = v
    toCLI ((Con c)) = c

{- # Term # -}
instance ToCLI Term where
    toCLI (Atm x) = toCLI x
    toCLI (App x (App y z)) = (toCLI x) ++ " " ++ (parens $ toCLI (App y z))
    toCLI (App (Abs w x) y) = (parens $ toCLI (Abs w x)) ++ " " ++ (toCLI y)
    toCLI (App x y) = (toCLI x) ++ " " ++ (toCLI y)
    toCLI (Abs w y) = "\\" ++  w ++ " -> " ++ (toCLI y)
    toCLI (Cas x xs) = "case " ++ (toCLI x) ++ " of { " ++ (concat (map (\ ((a, vs),b) -> a ++ (concat $ map (" "++) vs)  ++  " -> " ++ (toCLI b) ++ "; ") xs)) ++ "}"

instance ToLatex Term where
    toLatex x = toLatexV [] [] [] x

instance ToLatexV Term where
    toLatexV env fal lam (Atm (Var v)) = case (v `elem` env, v `elem` fal, v `elem` lam) of {
                                              (_, _, True) -> "\\variableL{"++v++"} ";
                                              (_, True, False) -> "\\variableF{"++v++"} ";
                                              (True, False, False) -> "\\variableE{"++v++"} ";
                                              (False, False, False) -> "\\variable{"++v++"} ";
                                              }
    toLatexV env fal lam (Atm (Con c)) = "\\constructor{"++(escapeConstructor c)++"} "
    toLatexV env fal lam (App x (App y z)) = "\\app{"++(toLatexV env fal lam x) ++ "}{\\parentesis{" ++ toLatexV env fal lam (App y z) ++ "}}"
    toLatexV env fal lam (App (Abs w x) y) = "\\app{\\parentesis{" ++  (toLatexV env fal lam (Abs w x)) ++ "}}{" ++ (toLatexV env fal lam y) ++"}"
    toLatexV env fal lam (App x y) = "\\app{" ++  (toLatexV env fal lam x) ++ "}{" ++ (toLatexV env fal lam y) ++ "}"
    toLatexV env fal lam (Abs w y) = "\\lambdaR{" ++  w ++ "}{" ++ (toLatexV env fal (w:lam) y) ++ "}"
    toLatexV env fal lam (Cas x xs) = "\\caseR{" ++ (toLatexV env fal lam x) ++ "}{" ++
                                    (foldr1 (\ a b -> "\\chainCaseBranchs{"++a++"}{"++b++"}") 
                                        (map (\ ((a, vs),b) -> "\\caseBranch{\\constructor{"++ (escapeConstructor a) ++ "}" ++ (concat $ map (" "++) vs)  ++  "}{" ++ (toLatexV env fal lam b) ++ "}") xs)) ++ "}"

{- # Type # -}
instance ToCLI TAtm where
    toCLI (TVar v) = "~"++( v)
    toCLI (TCon c) = ""++( c)

instance ToCLI Type where
    toCLI (TAtm x) = toCLI x
    toCLI (TBin b x@(TBin _ _ _) y) = (parens(toCLI x)) ++(toCLI b)++ ((toCLI y))
    toCLI (TBin b x y) = ((toCLI x)) ++(toCLI b)++ ((toCLI y))

instance ToCLI TBin where
    toCLI TCom = " -> "
    toCLI TApp = " @ "

instance ToCLI MType where
    toCLI (MType xs t) = "fall "++ (concat (intersperse "," (map show xs))) ++ "." ++ (toCLI t)

instance ToLatex TAtm where
    toLatex (TVar v) = "\\variable{"++ v ++"} "
    toLatex (TCon c) = "\\constructor{"++ (escapeConstructor c) ++"} "

escapeConstructor :: String -> String
escapeConstructor s = concatMap (\ x -> if x == '_' then "\\_" else [x]) s

instance ToLatex Type where
    toLatex (TAtm x) = toLatex x
    toLatex (TBin b x@(TBin _ _ _) y) = (parens(toLatex x)) ++(toLatex b)++ ((toLatex y))
    toLatex (TBin b x y) = ((toLatex x)) ++(toLatex b)++ ((toLatex y))

instance ToLatex TBin where
    toLatex TCom = "\\rightarrow "
    toLatex TApp = "\\application "

instance ToLatex MType where
    toLatex (MType xs t) = "\\forall "++ (concat (intersperse "," (map show xs))) ++ "." ++ (toLatex t)
instance ToCLI Affirm where
    toCLI (Affirm vs x y) = case vs of {
                            [] -> "";
                             _ -> "(All "++ concat ( map (\(v,t) -> v ++ "::" ++ toCLI t ++ " ") vs) ++ ")  ";
                            } ++ toCLI x ++ "  ===  "  ++ toCLI y

{- # Affirm # -}
instance ToLatex Affirm where
    toLatex (Affirm vs x y) = "\\affirm{" ++ case vs of {
                                            [] -> "";
                                            _ -> foldr1 (\ a b -> "\\chainVars{"++a++"}{"++b++"}") 
                                                    $ map (\(v,t) -> "\\hasType{"++v++"}{"++toLatex t++"}") vs }
                                    ++ "}{" ++ toLatex x ++ "}{"  ++ toLatex y ++ "}"

instance ToLatexV Affirm where
    toLatexV env [] [] (Affirm vs x y) = "\\affirm{" ++ case vs of {
                                                        [] -> "";
                                                        _ -> foldr1 (\ a b -> "\\chainVars{"++a++"}{"++b++"}") 
                                                                $ map (\(v,t) -> "\\hasType{\\variableF{"++v++"}}{"++toLatex t++"}") vs }
                                                ++ "}{" ++ toLatexV env (fsts vs) [] x ++ "}{"  ++ toLatexV env (fsts vs) [] y ++ "}"

{- # Proof # -}

instance ToCLI (Proof) where
    toCLI PDone = "Done"
    toCLI PFail = "Fail"
    toCLI (PStep x k xs) = toCLI x ++ "\n\t{ " ++ (toCLI k) ++ " }\n" ++ toCLI xs
    toCLI (PInd x s  xs) = toCLI x ++ "\n" ++ (toCLI s) ++ "\n" ++ concatMap (\ (c, (hs, t)) -> concatMap (\ u -> "\n \nH)" ++ toCLI u ++ "\n") hs 
                        ++ "\nTesis\n" ++ (indentar $ toCLI t) ++ "\n" ) xs  

indentar = concat . map ("\n    "++)  . lines

instance ToLatex (Proof) where
    toLatex x = toLatexV [] [] [] x

instance ToLatexV (Proof) where
    toLatexV env [] [] PDone = "\\done"
    toLatexV env [] [] PFail = "\\fail"
    toLatexV env [] [] (PStep x k xs) = toLatexV env [] [] x ++ "\n\n" ++ (toLatexV env [] [] k) ++ "\n\n" ++ toLatexV env [] [] xs
    toLatexV env [] [] (PInd  x k xs) = toLatexV env [] [] x ++ "\n\n" ++ (toLatexV env [] [] k) ++ "\n\n" ++ 
                                    concatMap (\ (c, (hs, t)) -> let (lt:lts) = filter (not . null) $ lines (toLatexV env [] [] t)
                                                                 in concatMap (\ u -> "\n  \n\n\\hypothesis" ++ toLatexV env [] [] u ++ "\n\n") hs ++ 
                                                                                         " \n\n\\thesis" ++ lt ++ "\n\n" ++ 
                                                                                          (concatMap ("\n\n\\indentProof"++) lts) ++ "\\\\\n" ) xs  

instance ToCLI Reason where 
        toCLI = show

instance ToCLI SideComment where 
        toCLI Compute = "Compute"
        toCLI (Lemma r a) = (toCLI r) ++ ": " ++ (toCLI a)

instance ToCLI Comment where 
        toCLI NoIdea  = "No Idea."
        toCLI Triv = "Triv."
        toCLI Loop = "Loop in the proof (apparent)."
        toCLI (LeftComment s) = "Left " ++ (toCLI s)
        toCLI (RightComment s) = "Right " ++ (toCLI s) 
        toCLI (BothComment l r) = "Left "  ++ (toCLI l) ++ " | " ++  "Right " ++ (toCLI r)
        toCLI (Induction v) =  "Induction " ++ v
        toCLI (Caso v) = "Case " ++  v


instance ToLatex Reason where 
        toLatex = show

instance ToLatex SideComment where 
        toLatex x = toLatexV [] [] [] x

instance ToLatex Comment where 
        toLatex x = toLatexV [] [] [] x

instance ToLatexV SideComment where 
        toLatexV env [] [] Compute = "Compute"
        toLatexV env [] [] (Lemma r a) = (toLatex r) ++ ":\\, " ++ (toLatexV env [] [] a) 

instance ToLatexV Comment where 
        toLatexV env [] [] (LeftComment x) = "\\leftcomment{" ++ (toLatexV env [] [] x) ++ "}"
        toLatexV env [] [] (RightComment x) = "\\rightcomment{" ++ (toLatexV env [] [] x) ++ "}" 
        toLatexV env [] [] (BothComment x y) = "\\bothcomment{" ++ (toLatexV env [] [] x) ++ "}{" ++ (toLatexV env [] [] y) ++ "}"
        toLatexV env [] [] x =  "\\comment{"++ (show x) ++"}"
