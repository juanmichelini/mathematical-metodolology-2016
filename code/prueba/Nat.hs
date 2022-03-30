module Prueba.Nat where
import Syntax
import Compute
import Type
import SimpleSubst
import Prueba.Bool

-- data Nat = O | S Nat

hO = Atm Con sO
hS = Atm Con sS
sO = "O"
sS = "S"
fS = App hS

env :: Env
env = [
    ("par"  , Abs "x" $ Cas (Atm Var "x") [(sO, [], hTrue), (sS, ["k"], (App  (Atm Var "not") (App (Atm Var "par") (Atm Var "k"))))]  ),
    ("pred" , Abs "x" $ Cas (Atm Var "x") [(sO, [], hO), (sS, ["k"], (App (Atm Var "pred") (Atm Var "k")))]  ),
    ("suma" , Abs "x" $ Abs "y" $ Cas (Atm Var "x") [(sO, [], Atm Var "y"), (sS, ["k"], fS (App (App (Atm Var "suma") (Atm Var "k")) (Atm Var "y")))]  ),
    ("mult" , Abs "x" $ Abs "y" $ Cas (Atm Var "x") [(sO, [], hO), (sS, ["k"], (App (App (Atm Var "suma") (App (App (Atm Var "mult") (Atm Var "k")) (Atm Var "y"))) (Atm Var "y")))]  )
    ]

dataNat = ("Nat", [(sO,[]),(sS,[Sim "Nat"])])

intToS n | n == 0 = hO
         | otherwise = fS (intToS (n-1))

sToInt (Atm Con "O") = 0
sToInt (App (Atm Con "S") x) = 1 + (sToInt x)
sToInt _ = error "no es un número"
