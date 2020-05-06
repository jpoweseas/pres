module Solver (decide) where

import qualified Data.Map as Map
import Data.Map (Map, (!))

import Lang
import Simplify

-- TODO: Merge with other context?
type Context = Map Var Nat

emptyCtxt :: Context
emptyCtxt = Map.empty

addBinding :: Var -> Nat -> Context -> Context
addBinding = Map.insert

-- throws exception if there is a free var
natOfTerm :: Context -> Term -> Nat
natOfTerm ctxt (Term constant coeffs) =
  constant + (sum $
  map (\(var, coeff) -> (ctxt ! var) * coeff) $
  Map.assocs coeffs)

decideAtom :: Context -> DivAtom -> Bool
decideAtom ctxt (Lt t1 t2) =
  natOfTerm ctxt t1 < natOfTerm ctxt t2
decideAtom ctxt (Div n t) =
  n |. natOfTerm ctxt t

decide :: QFFormula DivAtom -> Bool
decide = decide' emptyCtxt

decide' :: Context -> QFFormula DivAtom -> Bool
decide' _ Top = True
decide' _ Bottom = False
decide' ctxt (QFAtomic b a) = b == decideAtom ctxt a
decide' ctxt (QFOr f1 f2) = decide' ctxt f1 || decide' ctxt f2
decide' ctxt (QFAnd f1 f2) = decide' ctxt f1 && decide' ctxt f2
decide' ctxt (QOr v s f) = any (\n -> decide' (addBinding v n ctxt) f) $ natSetToList s
decide' ctxt (QAnd v s f) = all (\n -> decide' (addBinding v n ctxt) f) $ natSetToList s
