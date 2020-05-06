module Simplify (simplifyQF, nnf) where

import Lang

nnf :: Formula a -> Formula a
nnf (Atomic a) = Atomic a
nnf (Or f1 f2) = Or (nnf f1) (nnf f2)
nnf (And f1 f2) = And (nnf f1) (nnf f2)
nnf (Exists v f) = Exists v (nnf f)
nnf (Forall v f) = Not $ Exists v $ nnf (Not f)
nnf (Not (Atomic a)) = Not (Atomic a)
nnf (Not (Or f1 f2)) = And (nnf $ Not f1) (nnf $ Not f2)
nnf (Not (And f1 f2)) = Or (nnf $ Not f1) (nnf $ Not f2)
nnf (Not (Not f)) = nnf f
nnf (Not (Forall v f)) = Exists v (nnf $ Not f)
nnf (Not (Exists v f)) = Not (Exists v f)

mapAllQF :: (QFFormula a -> QFFormula a) -> QFFormula a -> QFFormula a
mapAllQF f x =
  let f' = mapAllQF f
  in case x of
    (QFOr f1 f2) -> f $ QFOr (f' f1) (f' f2)
    (QFAnd f1 f2) -> f $ QFAnd (f' f1) (f' f2)
    (QOr v s n) -> f $ QOr v s (f' n)
    (QAnd v s n) -> f $ QAnd v s (f' n)
    x -> f x

mapUntilFixpoint :: Eq a => (a -> a) -> a -> a
mapUntilFixpoint f x = if x' == x then x' else mapUntilFixpoint f x'
  where x' = f x

simplifyQF :: QFFormula DivAtom -> QFFormula DivAtom
simplifyQF = mapAllQF $ mapUntilFixpoint aux
  where
    aux (QFOr Top _) = Top
    aux (QFOr _ Top) = Top
    aux (QFOr x Bottom) = x
    aux (QFOr Bottom x) = x
    aux (QFAnd Top x) = x
    aux (QFAnd x Top) = x
    aux (QFAnd Bottom _) = Bottom
    aux (QFAnd _ Bottom) = Bottom
    aux (QOr _ _ Top) = Top
    aux (QOr _ _ Bottom) = Bottom
    aux (QOr x (Range a b) f) | a == b = subst x (constantTerm a) f
    aux (QAnd _ _ Top) = Top
    aux (QAnd _ _ Bottom) = Top
    aux (QAnd x (Range a b) f) | a == b = subst x (constantTerm a) f
    aux (QFAtomic True a) = simplifyAtom a
    aux (QFAtomic False a) = negateQF $ simplifyAtom a
    aux x = x

logicalBool :: Bool -> QFFormula a
logicalBool True = Top
logicalBool False = Bottom

simplifyAtom :: DivAtom -> QFFormula DivAtom
simplifyAtom (Lt t1 t2) =
  maybe (QFAtomic True $ Lt t1 t2) (\x -> logicalBool (x > 0)) (getConstant (t2 .-. t1))
simplifyAtom (Div n t) =
  if isConstant t then logicalBool (n |. (constant t))
  else if n == 1 then Top
  else QFAtomic True (Div n t)
