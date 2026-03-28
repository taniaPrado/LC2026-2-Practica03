module Practica03 where

--Sintaxis de la logica proposicional
data Prop = Var String | Cons Bool | Not Prop
            | And Prop Prop | Or Prop Prop
            | Impl Prop Prop | Syss Prop Prop
            deriving (Eq)

instance Show Prop where 
                    show (Cons True) = "⊤"
                    show (Cons False) = "⊥"
                    show (Var p) = p
                    show (Not p) = "¬" ++ show p
                    show (Or p q) = "(" ++ show p ++ " ∨ " ++ show q ++ ")"
                    show (And p q) = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
                    show (Impl p q) = "(" ++ show p ++ " → " ++ show q ++ ")"
                    show (Syss p q) = "(" ++ show p ++ " ↔ " ++ show q ++ ")"

p, q, r, s, t, u :: Prop
p = Var "p"
q = Var "q"
r = Var "r"
s = Var "s"
t = Var "t"
u = Var "u"
w = Var "w"
v = Var "v"

{-
FORMAS NORMALES
-}

--Ejercicio 1
fnn :: Prop -> Prop
fnn (Cons a) = Cons a
fnn (Var p) = Var p

fnn (Or a b) = Or (fnn a) (fnn b)
fnn (And a b) = And (fnn a) (fnn b)

fnn (Impl a b) = Or (fnn (Not a)) (fnn b)
fnn (Syss a b) = And (fnn (Impl a b)) (fnn (Impl b a))

--Negaciones
fnn (Not (Cons True)) = Cons False
fnn (Not (Cons False)) = Cons True

fnn (Not (Not a)) = fnn a
fnn (Not (Var p)) = Not (Var p )

fnn (Not (Or a b)) =  (And (fnn (Not a)) (fnn(Not b)) )
fnn (Not (And a b)) = (Or  (fnn (Not a)) (fnn(Not b)) )

fnn (Not (Impl a b)) = fnn (Not (fnn (Impl a b)))
fnn (Not (Syss a b)) = fnn (Not (fnn (Syss a b)))


--Ejercicio 2
fnc :: Prop -> Prop
fnc p = auxFnc (fnn p)
    where 
        auxFnc :: Prop -> Prop 
        auxFnc (And p q) = And (auxFnc p) (auxFnc q)
        auxFnc (Or p q) = distribuir (auxFnc p) (auxFnc q)
        auxFnc p = p 

distribuir :: Prop -> Prop -> Prop
distribuir p (And q r) = And (distribuir p q) (distribuir p r)
distribuir (And p q) r = And (distribuir p r) (distribuir q r)
distribuir p q = Or p q

{-
RESOLUCION BINARIA
-}

--Sinonimos a usar
type Literal = Prop
type Clausula = [Literal]

--Ejercicio 1
clausulas :: Prop -> [Clausula]
clausulas (And p q) = clausulas p ++ clausulas q
clausulas p = [revisa(generaClausula p)]
    where
        generaClausula :: Literal -> Clausula
        generaClausula (Cons True)  = [Cons True]
        generaClausula (Cons False) = []
        generaClausula (Or p q) = generaClausula p ++ generaClausula q
        generaClausula (Var p) = ((Var p):[])
        generaClausula (Not (Var p)) = ((Not (Var p)):[]) 

revisa :: Clausula -> Clausula
revisa [] = []
revisa (x:xs)
    | x == (Cons False) = revisa (revisaAux x xs)
    | x /= (Cons True) = x : revisa (revisaAux x xs)
    | otherwise = [Cons True]
        where 
            revisaAux :: Literal -> Clausula -> Clausula
            revisaAux _ [] = []
            revisaAux e (y:ys)
                | e == y = revisaAux e ys
                | otherwise = y : revisaAux e ys

--Ejercicio 2
resolucion :: Clausula -> Clausula -> Clausula
resolucion c1 c2 = buscarYResolver c1 c1 c2
  where
    buscarYResolver [] o1 o2 = revisa (o1 ++ o2)
    buscarYResolver (x:xs) o1 o2
        | existe (opuesto x) o2 = revisa (quitar x o1 ++ quitar (opuesto x) o2)
        | otherwise = buscarYResolver xs o1 o2    

opuesto :: Literal -> Literal
opuesto (Var p) = Not (Var p)
opuesto (Not (Var p)) = Var p
opuesto x = x

existe :: Literal -> Clausula -> Bool
existe _ [] = False
existe l (x:xs) = l == x || existe l xs

quitar :: Literal -> Clausula -> Clausula
quitar _ [] = []
quitar l (x:xs)
    | l == x    = xs
    | otherwise = x : quitar l xs

{-
ALGORITMO DE SATURACION
-}

--Ejercicio 1
hayResolvente :: Clausula -> Clausula -> Bool
hayResolvente clau1 clau2 = not (null [ x | x <- clau1,
                    case x of
                     Var y        -> Not (Var y) `elem` clau2
                     Not (Var y)  -> Var y `elem` clau2
                     _            -> False ])

--Ejercicio 2
--Funcion principal que pasa la formula proposicional a fnc e invoca a res con las clausulas de la formula.
saturacion :: Prop -> Bool
saturacion p = resN (clausulas (fnc p))

resN :: [Clausula] -> Bool
resN conjuntoClausulas
    | [] `elem` conjuntoClausulas = False
    | nuevos == [] = True
    | otherwise = resN (conjuntoClausulas ++ nuevos)
  where
  nuevos =
    [ resolvente | clau1 <- conjuntoClausulas
        , clau2 <- conjuntoClausulas
        , hayResolvente clau1 clau2
        , let resolvente = resolucion clau1 clau2
        , not (resolvente `elem` conjuntoClausulas)]