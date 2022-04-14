module Prueba where
import Compute
import Syntax
import Type
import SimpleSubst
import Prueba.Bool
import Prueba.Nat
import Tactic
import Misc

prove = cutSingleStepCycles . traceTactic (mainTactic datas tenv) 

senv :: Show a => [a] -> IO ()
senv = mapM_ print

-- Para probar:
tenv = Prueba.Bool.env ++ Prueba.Nat.env


datas = [dataBool, dataNat]

-- Probar, ejemplo:
mult3por2 = sToInt $ flip repetirc (cWideLazy tenv) $ (App (App (Atm Var "mult") (intToS 3)) (intToS 2))

omasy = App (App (Atm Var "suma") (Atm Con "O")) (Atm Var "y") 
xmaso = App (App (Atm Var "suma") (Atm Var "x")) (Atm Con "O") 
sxmasy = App (App (Atm Var "suma") (App (Atm Con "S")  (Atm Var "x"))) (Atm Var "y")
s_xmasy = App (Atm Con "S") (App (App (Atm Var "suma") (Atm Var "x")) (Atm Var "y"))
xmassy = App (App (Atm Var "suma") (Atm Var "x")) (App (Atm Con "S")  (Atm Var "y"))
xmasy = App (App (Atm Var "suma") (Atm Var "x")) (Atm Var "y")
ymasx = App (App (Atm Var "suma") (Atm Var "y")) (Atm Var "x")

-- probar mas
lema1 = EQA [("y","Nat")] omasy (Atm Var "y") 
lema2 = EQA [("x","Nat")] xmaso (Atm Var "x")
lema3 = EQA [("x","Nat"), ("y","Nat")] sxmasy s_xmasy 
lema4 = EQA [("x","Nat"), ("y","Nat")] xmassy s_xmasy
lema5 = EQA [("x","Nat"), ("y","Nat")] xmasy ymasx



