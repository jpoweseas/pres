{-# LANGUAGE TupleSections #-}

module Normalize (qe, qe') where

import qualified Data.Set as Set
import Data.Set (Set)

import Lang
import Simplify

import Debug.Trace (trace)

-- TODO: Preprocess negations
qe :: Formula Atom -> QFFormula DivAtom
qe f = case nnf f of
  (Atomic a) -> toDivAtom a
  (Or f1 f2) -> QFOr (qe f1) (qe f2)
  (And f1 f2) -> QFAnd (qe f1) (qe f2)
  (Exists v f) -> qe' v (qe f)
  (Forall v f) -> qe $ Not (Exists v (Not f))
  (Not (Atomic a)) -> negateQF $ toDivAtom a
  (Not (Or f1 f2)) -> QFAnd (negateQF $ qe f1) (negateQF $ qe f2)
  (Not (And f1 f2)) -> QFOr (negateQF $ qe f1) (negateQF $ qe f2)
  (Not (Not f)) -> qe f
  (Not (Forall v f)) -> qe' v (negateQF $ qe f)
  (Not (Exists v f)) -> negateQF $ qe' v (qe f)

toDivAtom :: Atom -> QFFormula DivAtom
toDivAtom (Comparison Lt' t1 t2) = QFAtomic True $ Lt t1 t2
toDivAtom (Comparison Eq t1 t2) = QFAnd (QFAtomic False $ Lt t1 t2) (QFAtomic False $ Lt t2 t1)
toDivAtom (Div' n t) = QFAtomic True $ Div n t
toDivAtom (Comparison Gt t1 t2) = QFAtomic True $ Lt t2 t1
toDivAtom (Comparison Le t1 t2) = QFAtomic False $ Lt t2 t1
toDivAtom (Comparison Ge t1 t2) = QFAtomic False $ Lt t1 t2

qe' :: Var -> QFFormula DivAtom -> QFFormula DivAtom
qe' v f = simplifyQF $ produce v $ distinguish v $ rearrange v f

rearrange :: Var -> QFFormula DivAtom -> (QFFormula (Nat -> DistAtom), [Nat])
rearrange v atom =
  case atom of
    Top -> (Top, [])
    Bottom -> (Bottom, [])
    (QFAtomic b atom) -> (QFAtomic (b == b') atom', ns)
      where (atom', ns, b') = aux atom
    (QFOr f1 f2) -> (QFOr f1' f2', l1 ++ l2)
      where (f1', l1) = rearrange v f1
            (f2', l2) = rearrange v f2
    (QFAnd f1 f2) -> (QFAnd f1' f2', l1 ++ l2)
      where (f1', l1) = rearrange v f1
            (f2', l2) = rearrange v f2
    (QOr v' s f) -> (QOr v' s f', l)
      where (f', l) = rearrange v f
    (QAnd v' s f) -> (QAnd v' s f', l)
      where (f', l) = rearrange v f
  where
    aux :: DivAtom -> ((Nat -> DistAtom), [Nat], Bool)
    aux (Lt t1 t2) =
      case removeVar v $ subTerms t2 t1 of
        (t, 0) -> (const $ Dist (Lt (constantTerm 0) t), [], True)
        (t, coeff)
          | coeff > 0 ->
            (,[abs coeff],False) $ \lcm ->
              DistLt $ ((lcm `div` (abs coeff)) .*. (((-1) .*. t) .+. constantTerm 1))
          | coeff < 0 ->
            (,[abs coeff],True) $ \lcm ->
              DistLt $ ((lcm `div` (abs coeff)) .*. t)
    aux (Div n t) =
      case removeVar v t of
        (t, 0) -> (const $ Dist (Div n t), [], True)
        (t, coeff) -> (,[abs coeff],True) $ \lcm ->
          let mult = lcm `div` coeff
          in DistDiv (abs $ n * mult) (mult .*. t)

distinguish :: Var -> (QFFormula (Nat -> DistAtom), [Nat]) -> QFFormula DistAtom
distinguish v (f, ns) = QFAnd (aux f) (QFAtomic True $ DistDiv lcm_ (constantTerm 0))
  where
    lcm_ :: Nat
    lcm_ = foldr lcm 1 ns
    aux :: QFFormula (Nat -> DistAtom) -> QFFormula DistAtom
    aux (QFAtomic b a) = QFAtomic b (a lcm_)
    aux (QOr v' _ _) | (v == v') = error "wtf"
    aux (QAnd v' _ _) | (v == v') = error "wtf"
    aux f = applySubs aux f

produce :: Var -> QFFormula DistAtom -> QFFormula DivAtom
produce v f = QFOr
  (QOr v (Range 1 lcm_) $ mapAtoms (produce1 v) f)
  (QOr v (Range 1 lcm_) $
  foldr QFOr Bottom $
  map (\t -> mapAtoms (produce2 v t) f) $
  getBounds f)
  where
    lcm_ :: Nat
    lcm_ = foldr lcm 1 $ getDivisors f

getDivisors :: QFFormula DistAtom -> [Nat]
getDivisors = fromAtoms aux
  where aux _ (DistDiv n _) = [n]
        aux _ _ = []

getBounds :: QFFormula DistAtom -> [Term]
getBounds = fromAtoms aux
  where aux False (DistLt t) = [t .-. constantTerm 1]
        aux _ _ = []

fromAtoms :: (Bool -> a -> [b]) -> QFFormula a -> [b]
fromAtoms f (QFAtomic b a) = f b a
fromAtoms f (QFOr f1 f2) = fromAtoms f f1 ++ fromAtoms f f2
fromAtoms f (QFAnd f1 f2) = fromAtoms f f1 ++ fromAtoms f f2
fromAtoms f (QOr _ _ f1) = fromAtoms f f1
fromAtoms f (QAnd _ _ f1) = fromAtoms f f1
fromAtoms _ _ = []

produce1 :: Var -> DistAtom -> Either DivAtom (QFFormula DivAtom)
produce1 v (Dist d) = Left d
produce1 v (DistLt _) = Right Top
produce1 v (DistDiv n t) = Left $ Div n (addTerms (varTerm v) t)

produce2 :: Var -> Term -> DistAtom -> Either DivAtom (QFFormula DivAtom)
produce2 _ _ (Dist d) = Left d
produce2 v u (DistLt t) = Left $ Lt lhs t
  where lhs = addTerms (varTerm v) u
produce2 v u (DistDiv h c) = Left $ Div h (addTerms c lhs)
  where lhs = addTerms (varTerm v) u
