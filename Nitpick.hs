module Nitpick (nitpick) where

import Lang

import qualified Data.Set as Set
import Data.Set (Set)

nitpick :: Formula Atom -> Either String ()
nitpick = nitpick_ Set.empty

nitpick_ :: Set Var -> Formula Atom -> Either String ()
nitpick_ bound (Atomic (Comparison _ t1 t2)) =
  checkTerm bound t1 >> checkTerm bound t2
nitpick_ bound (Atomic (Div' n t)) = checkTerm bound t
nitpick_ bound (Not f) = nitpick_ bound f
nitpick_ bound (Or f1 f2) = nitpick_ bound f1 >> nitpick_ bound f2
nitpick_ bound (And f1 f2) = nitpick_ bound f1 >> nitpick_ bound f2
nitpick_ bound (Exists v f) =
  if Set.member v bound then Left ("Illegally shadowed variable " ++ show v)
  else nitpick_ (Set.insert v bound) f
nitpick_ bound (Forall v f) =
  if Set.member v bound then Left ("Illegally shadowed variable " ++ show v)
  else nitpick_ (Set.insert v bound) f

checkTerm :: Set Var -> Term -> Either String ()
checkTerm bound t =
  foldl (\acc var -> acc >>
          if Set.member var bound then Right ()
          else Left ("Unknown function variable " ++ show var)
        ) (Right ()) (varsOfTerm t)
