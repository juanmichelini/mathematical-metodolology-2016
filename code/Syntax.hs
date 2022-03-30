module Syntax where
import Data.List

type Name = String
data TAtm = Var | Con
            deriving (Eq)

data HExp = Atm TAtm Name | App HExp HExp | Abs Name HExp | Cas HExp [(Name, [Name], HExp)]
                deriving (Eq)


listParams :: HExp -> (HExp, [HExp])
listParams (App x y) =  case listParams x of { (h, hs) -> (h, hs++[y])} 
listParams h = (h, [])

appParams :: (HExp, [HExp]) -> HExp
appParams  (h, x:xs) = appParams ((App h x), xs)
appParams  (h, []) = h


instance Show HExp where
    show (Atm t n) = (show t) ++ n
    show (App e f) = "(" ++ show e ++" "++ show f ++ ")"
    show (Abs x b) = "(\\" ++ x ++ "." ++ show b ++ ")"
    show (Cas e cs) = "{"++ show e ++ "?" ++ (concat $ map (\(c,vs,h) -> c ++ " " ++  (intercalate " " vs) ++ ": " ++ show h ++ "; ") cs)  ++ "}"

instance Show TAtm where
    show Var = "v"
    show Con = "c"
