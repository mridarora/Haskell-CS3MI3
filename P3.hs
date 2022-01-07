module Aroram15 where

import Data.List
import Debug.Trace

data T = App T T
       | If T T T 
       | Succ T
       | Pred T
       | IsZero T
       | Val V
       | Let Label T T
       | Seq T T
       | Alloc T
       | DeRef T
       | Assign T T 
  deriving (Show, Eq)
  
data V = Tru | Fls | Z | SuccNV V | UnitV | Location Loc | Var Label | L Label Type T deriving(Show, Eq)
  
data Label = A | C | D | E | F | G | H | I | J | K 
    | M | O | P | Q | R | S | U | W | X | Y  
    deriving (Show, Eq)
    
data Loc = L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9
    deriving (Show, Eq)

data Type = BOOL | NAT | Unit | Arrow Type Type | Ref Type deriving (Show, Eq)

type Gamma = [(Label, Type)] 

type Mu = [(Loc, V)]

ssos :: (T, Mu) -> (T, Mu)
ssos (Val x, m) = (Val x, m)
ssos ((If (Val Tru) t _), m) = (t, m) --E-If True
ssos ((If (Val Fls) _ t), m) = (t, m) --E-If False
ssos ((If t x y), m) = (If (fst(ssos (t, m))) x y, m) --E-If

ssos (Pred (Val Z), m) = (Val Z, m)  
ssos (Pred (Succ (Val x)), m) = (Val x, m) -- E- PreSucc
ssos (Pred t, m) = (Pred (fst(ssos (t, m))), m) -- E-Pred
ssos (Succ t, m) = (Succ (fst(ssos (t, m))), m) -- E-Succ

ssos (IsZero (Val Z), m) = (Val Tru, m)          --E-Iszerzozero    
ssos (IsZero (Succ (Val x)), m) = (Val Fls, m) --E-IszeroSucc
ssos (IsZero t, m) = (IsZero (fst(ssos (t, m))), m) --E-Iszero

ssos t@((App t1 t2), m)
    | isNF t1 && isNF t2 = case t1 of 
        (Val (L variable typ body)) -> (sub body variable t2, m)     -- E-AppAbs
        _ -> t                              -- Reflexivity
    | isNF t1 = ((App t1 (fst(ssos (t2, m)))), m) -- E-App2
    | otherwise = ((App (fst(ssos (t1, m))) t2), m) -- E-App1
ssos t = t                                      -- Reflexivity

sub :: T -> Label -> T -> T
sub v@(Val (Var a)) d e = if a == d then e else v

typeCheck :: Gamma -> T -> Maybe Type
typeCheck g (Val (SuccNV Z)) = (Just NAT)
typeCheck g (Val Z) = (Just NAT)
typeCheck g (Succ t) --T-Succ
    | (typeCheck g t == (Just NAT)) = (typeCheck g t)
    | otherwise = Nothing
typeCheck g (Pred t) --T-Pred
    | (typeCheck g t == (Just NAT)) = (typeCheck g t)
    | otherwise = Nothing
typeCheck g (IsZero t) --T-Iszero
    | ((typeCheck g t) == (Just NAT)) = Just BOOL
    | otherwise = Nothing
typeCheck g (Val Tru) = (Just BOOL) --T-Tru
typeCheck g (Val Fls) = (Just BOOL)  --T-Fls
typeCheck g (If t1 t2 t3) --T-If
    | ((typeCheck g t1) == (Just BOOL)) && ((typeCheck g t2) == (typeCheck g t3)) = ((typeCheck g t3))
    | otherwise = Nothing

freeVars :: T -> [Label]
freeVars (Val (Var a)) = [a]
freeVars (Val (L a b t1)) = freeVars t1 \\ [a]
freeVars (App t1 t2) = freeVars t1 `union` freeVars t2

relabel :: T -> Label -> Label -> T
relabel v@(Val (Var x)) a b = if a == x then (Val (Var b)) else v
relabel (Val (L x y t)) a b = if a == x then Val (L b y (relabel t a b)) else Val (L x y (relabel t a b))
relabel (App t1 t2) a b = App (relabel t1 a b) (relabel t2 a b)

isNF :: T -> Bool
isNF (Val (Var _)) = True
isNF (Val (L _ _ _)) = True
isNF (App (Val (L _ _ _)) _) = False
isNF (App (Val (Var _)) (Val (L _ _ _))) = True
isNF (App t1 t2) = isNF t1 && isNF t2

eval :: (T, Mu) -> (T, Mu)
eval (t, m)
    | isNF t = (t, m)
    | otherwise = eval (ssos (t, m))

run :: (T, Mu) -> (T, Mu)
run (t, m) 
    | (typeCheck [] t) /= Nothing = eval (t, m)
    | otherwise = error "Oops!"
