module Prueba.Bool where
import Syntax
import Compute
import Type

-- data Bool = True | False

hTrue  = Atm Con sTrue
hFalse = Atm Con sFalse
sTrue  = "True"
sFalse = "False"

env = [

    ("not" , Abs "x" $ Cas (Atm Var "x") [(sTrue, [], hFalse), (sFalse, [], hTrue)]),

    ("and" , Abs "x" $ Abs "y" $ Cas (Atm Var "x") [(sTrue, [], Atm Var "y"), (sFalse, [], hFalse)]),

    ("or" , Abs "x" $ Abs "y" $ Cas (Atm Var "x") [(sFalse, [], Atm Var "y"), (sTrue, [], hTrue)])

    ]


dataBool = ("Bool", [(sTrue,[]),(sFalse,[])])
        
