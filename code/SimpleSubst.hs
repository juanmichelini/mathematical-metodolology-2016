module SimpleSubst where
import Syntax

subst :: HExp -> Name -> HExp -> HExp
subst (Atm Var v) x g | x == v = g
                  | otherwise = Atm Var v
subst (Atm Con c) x g = Atm Con c
subst (App e f) x g = App (subst e x g) (subst f x g)
subst (Abs y b) x g | x == y =  Abs y b
                    | not (isFresh y g) = Abs w (subst (subst b y (Atm Var w)) x g)
                    | otherwise = Abs y (subst b x g)
                          where w = fresh [b, g]
subst (Cas e cs) x g = Cas (subst e x g) (map (\ (c,vs,f) -> (c, vs, if (elem x vs) then f else subst f x g)) cs) 

multisubst :: HExp -> [(Name, HExp)] -> HExp
multisubst (Atm Var v) xs = case lookup v xs of { Just u -> u; Nothing -> (Atm Var v)}
multisubst (Atm Con c) xs = Atm Con c
multisubst (App e f) xs = App (multisubst e xs) (multisubst f xs)
multisubst (Abs y b) xs | any (not . isFresh y . snd)  xs = Abs w (multisubst b ((y, Atm Var w):xs))
                        | otherwise = Abs y (multisubst b (filter ((y /=) . fst) xs))
                                where w = fresh (b:(map snd xs))
multisubst (Cas e cs) xs = Cas (multisubst e xs)  (map (\ (c, vs, f) -> (c, vs, multisubst f (filter (not . (flip elem vs) . fst) xs))) cs)

isFresh :: Name -> HExp -> Bool
isFresh w (Atm Var v) | w == v = False
                      | otherwise = True
isFresh w (Atm Con c)    = True
isFresh w (App e f)  = (isFresh w e) && (isFresh w f)
isFresh w (Abs y b)  = (y/=w) && (isFresh w b)
isFresh w (Cas e cs) = isFresh w e && all (\ (c,vs,f) -> (not (elem w vs)) && (isFresh w f)) cs

infinitevars :: [Name]
infinitevars = map (\n -> "x"++(show n)) [0..] 

fresh :: [HExp] -> Name
fresh es = head $ filter (\ w -> all (isFresh w) es) infinitevars
