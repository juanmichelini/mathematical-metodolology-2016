module Strategy where
import Compute
import Syntax
import Type
import SimpleSubst
import Prueba.Bool
import Prueba.Nat
import Tactic
import Misc

data ArbolInst a = ArbolInst [(a, ArbolInst a)] 
type Poda a = ArbolInst a -> ArbolInst a

stra :: [(Var, Type)] -> Type ->  [AHExp]
stra xs ty = (filtrarPorTipo (conVariables xs) ty)

conVariables :: [(Var, Type)] -> [((Var, Type), (HExp, Type))] 

filtrarPorTipo :: [((Var, Type), (HExp, Type))]  -> Type -> [((Var, Type), HExp))]

armarArbol :: [([(Var,Type)], HExp)] ->  ArbolInst ([(Var,Type)], HExp)
armarArbol xs = ArbolInst (map (\u -> (u, case fst u of { [] -> []; (v,t):vs -> mapArbolInst (subst (snd u) v) (armarPlan xs   )) xs)



    

descartarRepetidos
descartarConMismaFunciónRepetida
descartar

-- [
--  ("O", Sim "N"),
--  ("S", Com (Sim "N") (Sim "N"),
--  ("suma", Com (Com (Sim "N") (Sim "N")) (Sim "N))
--  ("mult", Com (Com (Sim "N") (Sim "N")) (Sim "N))
-- ]
--
--El tipo actúa de guía. 
--Se agarra una expresión que tiene huecos de cierto tipo, se buscán expresiones completas de esos tipos para llenar los huecos.
--Hay infinitas, se ordenan por orden de complejidad.
--Se hace lo mismo del otro lado.
--El truco está en recorrer esta estructura de menor orden de complejidad a mayor. Equilibrando ambos lados.
--Tambien hay podas inteligentes. Si tengo conmutativa y asociativa, puedo descartar muchas ramas.
--Eso.
--
--iniciar: O : N, S : N -> N, + : N -> (N -> N).
--completar:   O : N, S : N -> N, + : N -> (N -> N), (All x) S x : N, (All x) (Suma x) : N -> N, (All x,y) ((Suma x) y) : N
--filtrar N:  xs = [ O : N, (All x) S x : N, (All x,y) ((Suma x) y) : N]
--armarPlan : [([TypedVar],TypedHExp)] -> Plan HExp
--devolver: Plan xs (map (\ x -> se llama recursivamente y a ese plan se le mapea aplicar la expresión x, cambiando su variable por lo que está en el plan) xs))
--
--hay que poder programar el producto cartesano de dos planes
--
--Sólo con S: S x = S x; S x = S y; S $ S x = S x; S $ S x = S $ S y
--y así al infinito. La complejidad crece línealmente, siempre seguiría intentando probar esto, sólo que fallaría e iría a probar otras cosas de mayor complejidad. la conmutativa de la suma tiene complejidad 10. Eso quiere decir que antes se habrían itentado probar 20 lemas idiotas. A no ser que se haga una poda mejor.
--
--Sólo con suma, O y S.
--
--S $ S ( suma x y ) = S $ S (suma  x y)
--S ( suma x y ) = (suma (S x) y)
--
--Sólo con suma,
--hay dos huecos.
--
--1) Probar con variables cuantificas
--del otro lado cambio el orden de las variables cuantificadas, o sustituyo algunas por otras variables cuantificadas
--suma x y = suma j k - no tiene gracia, es constante
--suma x y = suma x k - no tiene gracia, es constante en el segundo
--suma x y = suma j y - no tiene gracia, es constante el primero
--suma x y = suma y x - opa
--
--2) Agregar sumas, eso agrega variables cuantificadas
--suma x y = suma x (suma x y)
--suma x y = suma x (suma x y)
--
--suma (suma x y) z = suma x (suma y z)  
--suma (suma x y) z = suma (suma x z) y
--
--
--partiendo de suma con variables cuantificadas,
--
--
--armar 
