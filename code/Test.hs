module Test where
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

main = putStrLn (show $ (provelemas 30))


---- Strategy
-- list types with 2 constructors, 1 recursive call, 0 embeded types
dats0 = enumContainerRecTypes 2 0 0
-- only one..
boo = dats0!!0

(boonom, _) = boo
-- pass from abbreviation to expansion
booExt = datasH2C boo

-- list types with 2 constructors, 1 recursive call, 0 embeded types
dats1 = enumContainerRecTypes 2 0 1
nat = dats1!!0

(natnom, _) = nat
-- pass from abbreviation to expansion
natExt = datasH2C nat

-- list types with 2 constructors, 1 recursive call, 1 embeded types
dats2 = enumContainerRecTypes 2 1 1
lis = dats2!!0

(lisnom, _) = lis
-- pass from abbreviation to expansion
lisExt = datasH2C lis

tipos = armarTip 2 [TAtm (TCon boonom), TAtm (TCon natnom), TAtm (TCon lisnom)]
tipo = tipos!!26

pruebaEnum = enumFun emptyRec "f" tipo [nat, boo] []

candidatos :: [Term]
candidatos = enumFun emptyRec "f" tipo [nat, boo, lis] (mapFst (Atm . Con) natExt)

candidatosFst :: [Term]
candidatosFst = filter (\t -> all (`elem`termToAtm t) [Var "x", Var "f"] ) $ enumFun emptyRec "f" tipo [boo,nat,lis] (mapFst (Atm . Con) (natExt++lisExt++booExt))

candidatosRev :: [Term]
candidatosRev = filter (\t -> all (`elem`termToAtm t) [Var "concat", Var "f"] ) $ enumFun emptyRec "f" (TBin TCom (TAtm (TCon "C_,a_R")) (TAtm (TCon "C_,a_R"))) [boo,nat,lis] ((Atm (Var "concat"), TBin TCom (TAtm (TCon "C_,a_R")) (TBin TCom (TAtm (TCon "C_,a_R")) (TAtm (TCon "C_,a_R")))):(mapFst (Atm . Con) (natExt++lisExt++booExt))) 

-- prueba conjetura
expsconcandidatos :: Int -> [Term]
expsconcandidatos a = enumApp a (TAtm (TCon natnom))  ([(Atm (Var "x"), TAtm (TCon natnom)), (Atm (Var "y"), TAtm (TCon natnom)), (Atm (Var "f"), tipo)] ++ ( mapFst (Atm . Con) $ concatMap datasH2C [nat, boo]))


conjeturasFst :: [Affirm]
conjeturasFst = conjeturas (TAtm (TCon natnom)) ((Atm (Var "f"), tipo) : ( mapFst (Atm . Con) $ concatMap datasH2C [nat, boo])) [((Var "f"))]

conjeturasSnd :: [Affirm]
conjeturasSnd = conjeturas (TAtm (TCon natnom)) ((Atm (Var "g"), tipo) : (Atm (Var "f"), tipo) : ( mapFst (Atm . Con) $ concatMap datasH2C [nat, boo])) [((Var "f1"))]

conjeturas0 :: [Affirm]
conjeturas0 = filter (\(Affirm _ x y) -> case (getHeadCon x, getHeadCon y) of { (Just (a,_), Just (b,_)) -> a /= b; _ -> True;}) $
              -- for any constructor S, (S x = S y <=> x = y) so we can safely ignore it
              filter (\(Affirm _ x y) -> all (`elem`(termToAtm x ++ termToAtm y)) [Var "x", Var "f"] ) $
              -- ignore what does not apply f to a quantified variable
              filter (\a -> a /= flipAffirm a) $  
              -- avoid repetitions
              map (\(y,z) ->  Affirm [("x", (TAtm . TCon) natnom), ("y", (TAtm . TCon) natnom)] y z) $
              armarParejas (expsconcandidatos 3)
            

conjeturas2 = let  (sim0, nosim0) = partition (simplifies env) conjeturas0;
                   (sim1, nosim) = partition ((simplifies env).flipAffirm) nosim0; 
                   sim = sim0 ++ (map flipAffirm sim1);
                   (floDep0, nofloDep0) = partition (floatsDep env) nosim;
                   (floDep1, nofloDep) = partition ((floatsDep env).flipAffirm) nofloDep0; 
                   floDep = floDep0 ++ (map flipAffirm floDep1);
                   (perm, _) = partition (soloPermuta) nofloDep;
               in ((sortBy (simplifiesOrd env) sim ) ++ (sortBy (floatsDepOrd env) floDep ) ++ (filter soloPermuta perm))
               where env = [(Var "f", candidatos!!48)]


suma = (candidatos)!!48


conjeturas :: Type -> [(Term, Type)] -> [Atm] -> [Affirm]
conjeturas t exps must = filter (\(Affirm vs x y) -> (any (`elem`must) (termToAtm x ++ termToAtm y))) $ 
                        filter (\a -> a /= flipAffirm a) ${-sortBy comp $-} 
                        map (\(y,z) ->  Affirm vars y z) $ armarParejas ( repiteAtmHasta 3 $ enumApp 3 (TAtm (TCon natnom)) (exps++(map (\(a,b) -> ((Atm .Var) a, b))  vars)))
                        where vars = [("x", (TAtm . TCon) natnom), ("y", (TAtm . TCon) natnom)]


--For testing tactics without testing strategy:

--Nat

hTrue  = Atm (Con sTrue)
hFalse = Atm (Con sFalse)
sTrue  = "True"
sFalse = "False"
hO = Atm (Con sO)
hS = Atm (Con sS)
sO = "O"
sS = "S"
fS = App hS
hNil = Atm (Con sNil)
hCons = Atm (Con sCons)
sNil = "Nil"
sCons = "Cons"
fCons x xs = App ((App hCons) x) xs

dataBool = ("Bool", [(sTrue,[]),(sFalse,[])])
dataNat = ("Nat", [(sO,[]),(sS,[TAtm (TCon "Nat")])])
dataList =  ("List", [(sNil, []), (sCons, [TAtm (TVar "a"), TAtm (TCon "List")] )])
datas = [dataBool, dataNat, dataList]

envToVars :: Env -> [Var]
envToVars  = map (\(Var x) -> x) . filter (not . isCon) . fsts

env :: Env
env =
    (Var "suma" , Abs "x" $ Abs "y" $ Cas (Atm (Var "x")) [((sO, []), Atm (Var "y")), ((sS, ["k"]), fS (App (App (Atm (Var "suma")) (Atm (Var "k"))) (Atm (Var "y"))))]  ) :
    (Var "mult" , Abs "x" $ Abs "y" $ Cas (Atm (Var "x")) 
                                    [((sO, []), hO), 
                                    ((sS, ["k"]), App (App (Atm (Var "suma")) (App (App (Atm (Var "mult")) (Atm (Var "k"))) (Atm (Var "y")))) (Atm (Var "y")))]  ) :
    (Var "flipexp" , Abs "x" $ Abs "y" $ Cas (Atm (Var "x")) 
                                    [((sO, []), mkAp [Con "S", Con "O"]), 
                                    ((sS, ["k"]), App (App (Atm (Var "mult")) (App (App (Atm (Var "flipexp")) (Atm (Var "k"))) (Atm (Var "y")))) (Atm (Var "y")))]  ) :
    (Var "not"  , Abs "x" $ Cas (Atm (Var "x")) [((sTrue, []), hFalse), ((sFalse, []), hTrue)]) :
    (Var "and"  , Abs "x" $ Abs "y" $ Cas (Atm (Var "x")) [((sTrue , []), Atm (Var "y")), ((sFalse, []), hFalse)]) :
    (Var "or"   , Abs "x" $ Abs "y" $ Cas (Atm (Var "x")) [((sFalse, []), Atm (Var "y")), ((sTrue , []), hTrue)]) :
    (Var "ssi"  , Abs "x" $ Abs "y" $ Cas (Atm (Var "x"))
                            [((sTrue , []), Atm (Var "y")),
                             ((sFalse, []), Cas (Atm (Var "y"))
                                                [((sTrue, []), hFalse), 
                                                 ((sFalse, []), hTrue)])]) :
    (Var "xor"  , Abs "x" $ Abs "y" $ Cas (Atm (Var "x")) [((sTrue, []),  mkAp [ Var "not", Var "y"]), ((sFalse, []), Atm (Var "y")) ]) :
    (Var "mayoria", Abs "x" $ Abs "y" $ Abs "z" $ Cas (Atm (Var "x")) 
                                                 [((sFalse, []), Cas (Atm (Var "y")) 
                                                                     [((sFalse, []), hFalse), 
                                                                      ((sTrue , []), Atm (Var "z"))]),
                                                  ((sTrue , []), Cas (Atm (Var "y")) 
                                                                     [((sFalse, []), Atm (Var "z")),
                                                                      ((sTrue , []), hTrue)])]) :
    (Var "par"  , Abs "x" $ Cas (Atm (Var "x")) [((sO, []), hTrue), ((sS, ["k"]), (App  (Atm (Var "not")) (App (Atm (Var "par")) (Atm (Var "k")))))]  ) :
    (Var "doble"  , Abs "x" $ Cas (Atm (Var "x")) [((sO, []), hO), ((sS, ["k"]), App  (Atm (Con "S")) (App  (Atm (Con "S")) (App (Atm (Var "doble")) (Atm (Var "k")))))]  ) :
    (Var "pred" , Abs "x" $ Cas (Atm (Var "x")) [((sO, []), hO), ((sS, ["k"]), (App (Atm (Var "pred")) (Atm (Var "k"))))]  ) :
    (Var "min" , Abs "x" $ Abs "y" $ Cas (Atm (Var "x")) 
                                    [((sO, []), (Atm (Con "O"))), 
                                    ((sS, ["k"]), Cas (Atm (Var "y")) 
                                                [((sO, []), Atm (Con "O")), 
                                                ((sS, ["j"]), mkAp1 [ Atm (Con "S"), mkAp [ Var "min", Var "k", Var "j"]])])]) :
    (Var "max" , Abs "x" $ Abs "y" $ Cas (Atm (Var "x")) 
                                    [((sO, []), (Atm (Var "y"))), 
                                    ((sS, ["k"]), Cas (Atm (Var "y")) 
                                                [((sO, []), Atm (Var "x")), 
                                                ((sS, ["j"]), mkAp1 [ Atm (Con "S"), mkAp [ Var "max", Var "k", Var "j"]])])]) :
    (Var "absr" , Abs "x" $ Abs "y" $ Cas (Atm (Var "x")) 
                                    [((sO, []), (Atm (Var "y"))), 
                                    ((sS, ["k"]), Cas (Atm (Var "y")) 
                                                [((sO, []), Atm (Var "x")), 
                                                ((sS, ["j"]), mkAp1 [ mkAp [ Var "absr", Var "k", Var "j"]])])]) :
    (Var "concat" , Abs "xs" $ Abs "ys" $ Cas (Atm (Var "xs")) [ ((sNil, []), Atm (Var "ys")), ((sCons, ["k", "ks"]), fCons (Atm (Var "k")) (App (App (Atm (Var "concat")) (Atm (Var "ks"))) (Atm (Var "ys"))))]  ) :
    (Var "largo" , Abs "xs" $ Cas (Atm (Var "xs")) [ ((sNil, []), hO), ((sCons, ["k", "ks"]), fS (App (Atm (Var "largo")) (Atm (Var "ks"))) )]  ) :
    (Var "rev" , Abs "xs" $ Cas (Atm (Var "xs")) [ ((sNil, []), hNil), ((sCons, ["k", "ks"]), (hConcat (App (Atm (Var "rev")) (Atm (Var "ks"))) (fCons (Atm (Var "k")) hNil)))]  ) :
    []




intToS n | n == 0 = hO
         | otherwise = fS (intToS (n-1))

sToInt (Atm (Con "O")) = 0
sToInt (App (Atm (Con "S")) x) = 1 + (sToInt x)
sToInt _ = error "no es un número"

-- Probar, ejemplo:
omasy   = App (App (Atm (Var "suma")) (Atm (Con "O"))) (Atm (Var "y")) 
xmaso   = App (App (Atm (Var "suma")) (Atm (Var "x"))) (Atm (Con "O")) 
sxmasy  = App (App (Atm (Var "suma")) (App (Atm (Con "S"))  (Atm (Var "x")))) (Atm (Var "y"))
xmassy  = App (App (Atm (Var "suma")) (Atm (Var "x"))) (App (Atm (Con "S"))  (Atm (Var "y")))
xmasy   = App (App (Atm (Var "suma")) (Atm (Var "x"))) (Atm (Var "y"))
ymasx   = App (App (Atm (Var "suma")) (Atm (Var "y"))) (Atm (Var "x"))
ymasz   = App (App (Atm (Var "suma")) (Atm (Var "y"))) (Atm (Var "z"))
xmas_ymasz = App (App (Atm (Var "suma")) (Atm (Var "x"))) ymasz
xmasy_masz = App (App (Atm (Var "suma")) xmasy) (Atm (Var "z")) 
s_xmasy = App (Atm (Con "S")) (xmasy)
opory   = App (App (Atm (Var "mult")) (Atm (Con "O"))) (Atm (Var "y")) 
xporo   = App (App (Atm (Var "mult")) (Atm (Var "x"))) (Atm (Con "O")) 
sxpory  = App (App (Atm (Var "mult")) (App (Atm (Con "S"))  (Atm (Var "x")))) (Atm (Var "y"))
xporsy  = App (App (Atm (Var "mult")) (Atm (Var "x"))) (App (Atm (Con "S"))  (Atm (Var "y")))
xpory   = App (App (Atm (Var "mult")) (Atm (Var "x"))) (Atm (Var "y"))
xporz   = App (App (Atm (Var "mult")) (Atm (Var "x"))) (Atm (Var "z"))
yporx   = App (App (Atm (Var "mult")) (Atm (Var "y"))) (Atm (Var "x"))
yporz   = App (App (Atm (Var "mult")) (Atm (Var "y"))) (Atm (Var "z"))
s_xpory = App (Atm (Con "S")) (xpory)
xmas_xpory = App (App (Atm (Var "suma")) (Atm (Var "x"))) (xpory)
ymas_xpory = App (App (Atm (Var "suma")) (Atm (Var "y"))) (xpory)
xpor_ymasz = App (App (Atm (Var "mult")) (Atm (Var "x"))) (ymasz)
xpory_mas_xporz = App (App (Atm (Var "suma")) (xpory)) (xporz)
ymasz_porx = App (App (Atm (Var "mult")) ymasz) (Atm (Var "x"))
xporymas_x = App (App (Atm (Var "suma")) xpory) (Atm (Var "x")) 
xporymas_y = App (App (Atm (Var "suma")) xpory) (Atm (Var "y")) 
xpor_yporz = App (App (Atm (Var "mult")) (Atm (Var "x"))) yporz
xpory_porz = App (App (Atm (Var "mult")) xpory) (Atm (Var "z")) 
nilconcatxs   = App (App (Atm (Var "concat")) hNil) (Atm (Var "xs")) 
xsconcatnil   = App (App (Atm (Var "concat")) (Atm (Var "xs"))) hNil 
xsconcatys   = App (App (Atm (Var "concat")) (Atm (Var "xs"))) (Atm (Var "ys"))
ysconcatxs   = App (App (Atm (Var "concat")) (Atm (Var "ys"))) (Atm (Var "xs"))
ysconcatzs   = App (App (Atm (Var "concat")) (Atm (Var "ys"))) (Atm (Var "zs"))
xsconcat_ysconcatzs = App (App (Atm (Var "concat")) (Atm (Var "xs"))) ysconcatzs
xsconcatys_concatzs = App (App (Atm (Var "concat")) xsconcatys) (Atm (Var "zs")) 
x_xsconcatys = fCons (Atm (Var "x")) xsconcatys

asocmas :: Int -> Term
asocmas 0 = Atm (Var "0")
asocmas n = App (App (Atm (Var "suma")) (Atm (Var (show n)))) (asocmas (n-1))
-- probar mas

mkAp = (foldl1 App) . (map Atm)
mkAp1 = (foldl1 App) 

lemascomp :: [Affirm]
lemascomp =
        Affirm [("y",(TAtm . TCon) "Nat")] 
                                    (mkAp [Var "suma", Con "O", Var "y"]) 
                                    (Atm (Var "y")) :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat")]
                                    (mkAp1 [Atm (Con "S"), (mkAp [Var "suma", Var "x", Var "y"])]) 
                                    (mkAp1 [Atm (Var "suma"), mkAp [Con "S", Var "x"], Atm (Var "y")]) :
        Affirm [("y",(TAtm . TCon) "Nat")] opory (Atm (Con "O")) :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat")]
                                    (mkAp1 [Atm (Var "mult"), mkAp [Con "S", Var "x"], Atm (Var "y")]) 
                                    (mkAp1 [mkAp [Var "suma", Var "y"], mkAp [Var "mult", Var "x", Var "y"]]) :
        Affirm [("xs",(TAtm . TCon) "List")] nilconcatxs (Atm (Var "xs")) :
        []

lemas :: [Affirm]
lemas =
        Affirm [("b1",(TAtm . TCon) "Bool"), ("b2",(TAtm . TCon) "Bool")] 
                                    (mkAp [Var "mayoria", Var "b1", Var "b1", Var "b2"]) 
                                    (Atm (Var "b1")) :
--        Affirm [("x",(TAtm . TCon) "Bool")] 
--                                    (mkAp1 [Atm (Var "not"), mkAp [Var "not", Var "x"]]) 
--                                    (Atm (Var "x")) :
        Affirm [("x",(TAtm . TCon) "Bool")] 
                                    (mkAp [Var "and", Var "x", Var "x"])
                                    (Atm (Var "x")) :
        Affirm [("x",(TAtm . TCon) "Bool")] 
                                    (mkAp [Var "ssi", Var "x", Var "x"])
                                    (Atm (Con "True")) :
        Affirm [("x",(TAtm . TCon) "Bool"), ("y",(TAtm . TCon) "Bool")] 
                                    (mkAp1 [Atm (Var "not"), mkAp [Var "ssi", Var "x", Var "y"]])
                                    (mkAp1 [Atm (Var "ssi"), mkAp [Var "not", Var "x"], Atm (Var "y")]) :
        Affirm [("x",(TAtm . TCon) "Bool"), ("y",(TAtm . TCon) "Bool")] 
                                    (mkAp [Var "ssi", Var "x", Var "y"])
                                    (mkAp [Var "ssi", Var "y", Var "x"]) :
        Affirm [("x",(TAtm . TCon) "Bool"), ("y",(TAtm . TCon) "Bool")] 
                                    (mkAp1 [Atm (Var "not"), mkAp [Var "xor", Var "x", Var "y"]])
                                    (mkAp1 [Atm (Var "xor"), mkAp [Var "not", Var "x"], Atm (Var "y")]) :
        Affirm [("x",(TAtm . TCon) "Bool"), ("y",(TAtm . TCon) "Bool")] 
                                    (mkAp [Var "xor", Var "x", Var "y"])
                                    (mkAp [Var "xor", Var "y", Var "x"]) :
        Affirm [("x",(TAtm . TCon) "Bool"), ("y",(TAtm . TCon) "Bool"), ("z",(TAtm . TCon) "Bool")]
                                    (mkAp1 [mkAp [Var "xor", Var "x"], mkAp [Var "xor", Var "y", Var "z"]])
                                    (mkAp1 [Atm (Var "xor"), mkAp [Var "xor", Var "x", Var "y"], Atm (Var "z")]) :
        Affirm [("x",(TAtm . TCon) "Nat")] 
                                    (mkAp [Var "suma", Var "x", Con "O"]) 
                                    (Atm (Var "x")) :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat")]
                                    (mkAp1 [Atm (Con "S"), (mkAp [Var "suma", Var "x", Var "y"])]) 
                                    (mkAp1 [Atm (Var "suma"), Atm (Var "x"), mkAp [Con "S", Var "y"]]) :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat")] 
                                    (mkAp [Var "suma", Var "x", Var "y"]) 
                                    (mkAp [Var "suma", Var "y", Var "x"]) :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat"), ("z",(TAtm . TCon) "Nat")]
                                    (mkAp1 [mkAp [Var "suma", Var "x"], mkAp [Var "suma", Var "y", Var "z"]])
                                    (mkAp1 [Atm (Var "suma"), mkAp [Var "suma", Var "x", Var "y"], Atm (Var "z")]) :
        Affirm [("y",(TAtm . TCon) "Nat")] opory (Atm (Con "O")) :
        Affirm [("x",(TAtm . TCon) "Nat")] xporo (Atm (Con "O")) :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat")]
                                    (mkAp1 [Atm (Var "mult"), mkAp [Con "S", Var "x"], Atm (Var "y")]) 
                                    (mkAp1 [mkAp [Var "suma", Var "y"], mkAp [Var "mult", Var "x", Var "y"]]) :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat")] sxpory ymas_xpory :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat")] xporsy xmas_xpory :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat")] sxpory xporymas_y :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat")] xporsy xporymas_x :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat"), ("z",(TAtm . TCon) "Nat")] xpor_ymasz xpory_mas_xporz :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat"), ("z",(TAtm . TCon) "Nat")] ymasz_porx xpory_mas_xporz :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat")] xpory yporx :
        Affirm [("x",(TAtm . TCon) "Nat"), ("y",(TAtm . TCon) "Nat"), ("z",(TAtm . TCon) "Nat")] xpor_yporz xpory_porz :
        Affirm [("x",(TAtm . TCon) "Nat")] (App (Atm(Var "doble")) (Atm (Var "x"))) (App (App (Atm(Var "suma")) (Atm (Var "x"))) (Atm (Var "x"))):
        Affirm [("xs",(TAtm . TCon) "List")] nilconcatxs (Atm (Var "xs")) :
        Affirm [("xs",(TAtm . TCon) "List")] xsconcatnil (Atm (Var "xs")) :
        Affirm [("x", (TAtm . TCon) "a"), ("xs",(TAtm . TCon) "List"), ("ys",(TAtm . TCon) "List")] 
                                            (mkAp1 [Atm (Var "concat"), mkAp [Con "Cons", Var "x", Var "xs"], mkAp [Var "ys"]])
                                            (mkAp1 [Atm (Con "Cons"), mkAp [Var "x"], mkAp [Var "concat", Var "xs", Var "ys"]]):
        Affirm [("xs",(TAtm . TCon) "List"), ("ys",(TAtm . TCon) "List"), ("zs",(TAtm . TCon) "List")] xsconcat_ysconcatzs xsconcatys_concatzs :
        Affirm [("x", (TAtm . TCon) "a"), ("xs",(TAtm . TCon) "List")] 
                                                (mkAp1 [Atm (Var "rev"), mkAp [Con "Cons", Var "x", Var "xs"]])
                                                (mkAp1 [Atm (Var "concat"), mkAp [Var "rev", Var "xs"], mkAp [Con "Cons", Var "x", Con "Nil"]]):
        Affirm [("x", (TAtm . TCon) "a") ] 
                                                (mkAp1 [Atm (Var "rev"), mkAp [Con "Cons", Var "x", Con "Nil"]])
                                                (mkAp [Con "Cons", Var "x", Con "Nil"]):
        Affirm [] ((App (Atm (Var "rev")) (Atm (Con "Nil")))) (Atm (Con "Nil")) :
        Affirm [("xs",(TAtm . TCon) "List"), ("ys",(TAtm . TCon) "List")] (App (Atm (Var "rev")) xsconcatys)   (hConcat (App (Atm (Var "rev")) (Atm (Var "ys"))) (App (Atm (Var "rev")) (Atm (Var "xs")))) :
        Affirm [("xs",(TAtm . TCon) "List")] (App (Atm (Var "rev")) (App (Atm (Var "rev")) (Atm (Var "xs")))) (Atm (Var "xs")) :
        Affirm [("xs",(TAtm . TCon) "List"), ("ys",(TAtm . TCon) "List")] 
                (App (Atm (Var "largo")) xsconcatys) (hSuma (App (Atm (Var "largo")) (Atm (Var "xs"))) (App (Atm (Var "largo")) (Atm (Var "ys")))) :
        Affirm [("xs",(TAtm . TCon) "List"), ("ys",(TAtm . TCon) "List")] (App (Atm (Var "largo")) xsconcatys) (App (Atm (Var "largo")) ysconcatxs) :
        []

hSuma x y = App (App (Atm (Var "suma")) x) y
hConcat x y = App (App (Atm (Var "concat")) x) y

--ie 
-- prove ([], lema1)
-- prove ([], lema2)
-- prove ([lema1], lema2)


tenv :: [(Term, Type)]
tenv =   
         (Atm (Con "O"), TAtm (TCon "Nat")) :
         (Atm (Con "S"), TBin TCom (TAtm (TCon "Nat")) (TAtm (TCon "Nat"))) :
         (Atm (Var "suma"), TBin TCom (TAtm (TCon "Nat")) (TBin TCom (TAtm (TCon "Nat")) (TAtm (TCon "Nat")))) :
         (Atm (Var "mult"), TBin TCom (TAtm (TCon "Nat")) (TBin TCom (TAtm (TCon "Nat")) (TAtm (TCon "Nat")))) :
         (Atm (Var "flipexp"), TBin TCom (TAtm (TCon "Nat")) (TBin TCom (TAtm (TCon "Nat")) (TAtm (TCon "Nat")))) :
         (Atm (Con "True"), TAtm (TCon "Bool")) :
         (Atm (Con "False"), TAtm (TCon "Bool")) :
         (Atm (Var "par"), TBin TCom (TAtm (TCon "Nat")) (TAtm (TCon "Bool"))) :
         (Atm (Var "doble"), TBin TCom (TAtm (TCon "Nat")) (TAtm (TCon "Nat"))) :
         (Atm (Var "not"), TBin TCom (TAtm (TCon "Bool")) (TAtm (TCon "Bool"))) :
         (Atm (Var "mayoria"), foldr1 (TBin TCom) $ map TAtm $ [TCon "Bool", TCon "Bool", TCon "Bool", TCon "Bool"]) :
         (Atm (Var "and"), foldr1 (TBin TCom) $ map TAtm $ [TCon "Bool", TCon "Bool", TCon "Bool"]) :
         (Atm (Var "or"), foldr1 (TBin TCom) $ map TAtm $ [TCon "Bool", TCon "Bool", TCon "Bool"]) :
         (Atm (Var "ssi"), foldr1 (TBin TCom) $ map TAtm $ [TCon "Bool", TCon "Bool", TCon "Bool"]) :
         (Atm (Var "xor"), foldr1 (TBin TCom) $ map TAtm $ [TCon "Bool", TCon "Bool", TCon "Bool"]) :
         (Atm (Var "min"), TBin TCom (TAtm (TCon "Nat")) (TBin TCom (TAtm (TCon "Nat")) (TAtm (TCon "Nat")))) :
         (Atm (Var "max"), TBin TCom (TAtm (TCon "Nat")) (TBin TCom (TAtm (TCon "Nat")) (TAtm (TCon "Nat")))) :
         (Atm (Var "absr"), TBin TCom (TAtm (TCon "Nat")) (TBin TCom (TAtm (TCon "Nat")) (TAtm (TCon "Nat")))) :
         (Atm (Con "Nil"), TAtm (TCon "List")) :
         (Atm (Con "Cons"), TBin TCom (TAtm (TCon "a")) (TBin TCom (TAtm (TCon "List")) (TAtm (TCon "List")))) :
         (Atm (Var "concat"), TBin TCom (TAtm (TCon "List")) (TBin TCom (TAtm (TCon "List")) (TAtm (TCon "List")))) :
         (Atm (Var "rev"), TBin TCom (TAtm (TCon "List")) (TAtm (TCon "List"))) :
         (Atm (Var "largo"), TBin TCom (TAtm (TCon "List")) (TAtm (TCon "Nat"))) :
         (Atm (Con "Hoja"), TBin TCom (TAtm (TCon "Nat")) (TAtm (TCon "TreeNat"))) :
         (Atm (Con "Nodo"), TBin TCom (TAtm (TCon "TreeNat")) (TBin TCom (TAtm (TCon "TreeNat")) (TAtm (TCon "TreeNat")))) :
         []




lsumad = findlemas (take 3 env) (take 5 tenv) datas 30 emptyRec (Var "suma")
lsumal = plemas (take 3 env) (take 5 tenv) datas 30 emptyRec (Var "suma")
lsuma  = map headProof lsumad
lsumar = addAffirms env emptyRec lsuma

lmultd = findlemas (take 4 env) (take 6 tenv) datas 30 lsumar (Var "mult")
lmultl = plemas (take 4 env) (take 6 tenv) datas 30 lsumar (Var "mult")
lmult  = map headProof lmultd
lmultr = addAffirms env lsumar lmult

lexpd = findlemas (take 5 env) (take 6 tenv) datas 30 lmultr (Var "flipexp")
lexpl = plemas (take 5 env) (take 6 tenv) datas 30 lmultr (Var "flipexp")
lexp  = map headProof lexpd
lexpr = addAffirms env lmultr lexp

lmind = findlemas env tenv datas 30 emptyRec (Var "min")
lmin  = map headProof lmind
lminr = addAffirms env emptyRec lmin

lmaxd = findlemas env tenv datas 30 emptyRec (Var "max")
lmax  = map headProof lmaxd
lmaxr = addAffirms env emptyRec lmax

labsrd = findlemas env tenv datas 30 emptyRec (Var "absr")
labsr  = map headProof labsrd
labsrr = addAffirms env emptyRec labsr

landd = findlemas env tenv datas 30 emptyRec (Var "and")
land  = map headProof landd
landr = addAffirms env emptyRec land


lord = findlemas env tenv datas 30 emptyRec (Var "or")
lor  = map headProof lord
lorr = addAffirms env emptyRec lor

lnotd = findlemas env tenv datas 30 emptyRec (Var "not")
lnot  = map headProof lnotd
lnotr = addAffirms env emptyRec lnot


lconcatd = findlemas env tenv datas 30 emptyRec (Var "concat")
lconcatl = plemas env tenv datas 30 emptyRec (Var "concat")
lconcat  = map headProof lconcatd
lconcatr = addAffirms env emptyRec lconcat

lrevd = findlemas env tenv datas 30 lconcatr (Var "rev")
lrevl = plemas env tenv datas 30 lconcatr (Var "rev")
lrev  = map headProof lrevd
lrevr = addAffirms env lconcatr lrev

provelemas m = [prove m datas env (addAffirms env emptyRec (lemascomp ++ take n lemas)) (lemas!!n)  | n<-[0..((length lemas )-1)]]

(provedlemas, unprovedlemas) = partition proofCompleto $ provelemas 30

cliprovedlemas = mapM_ putStrLn $ map (toCLI . headProof) provedlemas
cliunprovedlemas = mapM_ putStrLn $ map (toCLI . headProof) unprovedlemas


