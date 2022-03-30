module Type where
import Syntax
import SimpleSubst
import Compute
import Data.List

type SimpleType = String

data Type = Sim SimpleType | Com Type Type
        deriving (Eq, Show)


type TypedHExp = (HExp, Type)
type TypedName = (Name, Type)
type TypedHExpWV = (TypedHExp, [TypedName]) 

type Data = (SimpleType, [(Name, [Type])])

type TesisHipotesis = [(Name, [Bool])]


lkupData :: SimpleType -> [Data] -> Data 
lkupData t ds = case lookup t ds of {
                            Nothing -> error "data no existe";
                            Just bs -> (t, bs);
                            }

-- No cuenta hips que esten adentro de constructores
-- Estilo data AB = AB N [Ab], no lo toma en cuenta
-- No pense que hacer con parametros arbitrarios estilo [a] ...
marcarHip :: Data -> [(Name, [Bool])]
marcarHip (t, cvs) = map (\(c, par) -> (c, map (== Sim t) par)) cvs

