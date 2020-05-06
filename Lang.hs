module Lang where

import Control.Monad
import Data.List (intersperse)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Text.Printf

import Debug.Trace (trace)

trace' :: Show a => String -> a -> a
trace' msg x = trace (msg ++ show x) x

type Nat = Int

(|.) :: Nat -> Nat -> Bool
(|.) b a = a `rem` b == 0

-- VARIABLES

data Var = Var String
  deriving (Eq, Ord)

instance Show Var where
  show (Var s) = s

-- TERMS

data Term = Term { constant :: Nat, coeffs :: Map Var Nat }

removeZeros :: Map Var Nat -> Map Var Nat
removeZeros = Map.filter (/= 0)

instance Eq Term where
  (==) (Term c1 coeffs1) (Term c2 coeffs2) =
    c1 == c2 && removeZeros coeffs1 == removeZeros coeffs2

isConstant :: Term -> Bool
isConstant = null . removeZeros . coeffs

getConstant :: Term -> Maybe Nat
getConstant t = if isConstant t then Just $ constant t else Nothing

removeVar :: Var -> Term -> (Term, Nat)
removeVar x (Term c v) =
  (Term c (Map.delete x v), fromMaybe 0 $ Map.lookup x v)

combineTerms :: (Nat -> Nat -> Nat) -> Term -> Term -> Term
combineTerms f (Term c1 v1) (Term c2 v2) =
  Term (f c1 c2) (Map.unionWith f v1 v2)

scaleTerm :: Nat -> Term -> Term
scaleTerm n (Term c v) = Term (c * n) (Map.map (* n) v)

(.*.) = scaleTerm
(.-) = scaleTerm (-1)

addTerms = combineTerms (+)
subTerms t1 t2 = addTerms t1 ((-1) .*. t2)

(.+.) = addTerms
(.-.) = subTerms

constantTerm :: Nat -> Term
constantTerm n = Term n Map.empty

emptyTerm :: Term
emptyTerm = constantTerm 0

varTerm :: Var -> Term
varTerm v = Term 0 $ Map.singleton v 1

termFromList :: Nat -> [(Var, Nat)] -> Term
termFromList n l = Term n (Map.fromList l)

varsOfTerm :: Term -> [Var]
varsOfTerm (Term _ coeffs) = map fst $ Map.assocs $ removeZeros coeffs

-- NATSETS

data NatSet =
  Range Nat Nat -- Range a b represents [a, b] with both inclusive
  | NSet (Set Nat)
  deriving Eq

natSetToList :: NatSet -> [Nat]
natSetToList (Range a b) = [a..b]
natSetToList (NSet s) = Set.toList s

-- FORMULAS

data Cmp = Lt' | Eq | Gt | Ge | Le
  deriving Eq

data Atom =
  Comparison Cmp Term Term
  | Div' Nat Term
  deriving Eq

data DivAtom =
  Lt Term Term
  | Div Nat Term
  deriving Eq

data DistAtom =
  Dist DivAtom
  | DistLt Term -- [DistLt t] -> x' < t
  | DistDiv Nat Term -- [DistDiv h c] -> h | x' + c
  deriving Eq

data QFFormula a =
  Top
  | Bottom
  | QFAtomic Bool a
  | QFOr (QFFormula a) (QFFormula a)
  | QFAnd (QFFormula a) (QFFormula a)
  | QOr Var NatSet (QFFormula a)
  | QAnd Var NatSet (QFFormula a)
  deriving Eq

data (Formula a) =
  Atomic a
  | Or (Formula a) (Formula a)
  | And (Formula a) (Formula a)
  | Not (Formula a)
  | Forall Var (Formula a)
  | Exists Var (Formula a)
  deriving Eq


-- SUBSTITUTABLE

class Substitutable a where
  subst :: Var -> Term -> a -> a

instance Substitutable Term where
  subst v s t =
    case removeVar v t of
      (t', 0) -> t'
      (t', n) -> t' .+. (n .*. s)

-- instance Substitutable Atom where
--   subst v s t =
--     let subT = subst v s
--     in case t of
--       (Lt' t1 t2) -> Lt' (subT t1) (subT t2)
--       (Div n t) -> Div n (subT t)
--       x -> x

instance Substitutable DivAtom where
  subst v s t =
    let subT = subst v s
    in case t of
      (Lt t1 t2) -> Lt (subT t1) (subT t2)
      (Div n t) -> Div n (subT t)

instance Substitutable a => Substitutable (QFFormula a) where
  subst v s t =
    let sub = subst v s
    in case t of
      (QFAtomic b a) -> QFAtomic b $ subst v s a
      (QFOr f1 f2) -> QFOr (sub f1) (sub f2)
      (QFAnd f1 f2) -> QFAnd (sub f1) (sub f2)
      (QOr v' s f) | v /= v' -> QOr v s (sub f)
      x -> x

-- instance Substitutable a => Substitutable (Formula a) where
--   subst v s t =
--     let sub = subst v s
--     in case t of
--       (Atomic a) -> Atomic $ subst v s a
--       (Or f1 f2) -> Or (sub f1) (sub f2)
--       (And f1 f2) -> And (sub f1) (sub f2)
--       (Not f) -> Not (sub f)
--       (Forall v' f) | v /= v' -> Forall v' (sub f)
--       (Exists v' f) | v /= v' -> Exists v' (sub f)
--       x -> x

-- APPLY TO SUBEXPRS

negateQF :: QFFormula a -> QFFormula a
negateQF Top = Bottom
negateQF Bottom = Top
negateQF (QFOr f1 f2) = QFAnd (negateQF f1) (negateQF f2)
negateQF (QFAnd f1 f2) = QFOr (negateQF f1) (negateQF f2)
negateQF (QOr v s f) = QAnd v s (negateQF f)
negateQF (QAnd v s f) = QOr v s (negateQF f)
negateQF (QFAtomic b a) = QFAtomic (not b) a

mapAtoms :: (a -> Either b (QFFormula b)) -> QFFormula a -> QFFormula b
mapAtoms f (QFAtomic b a) =
  case f a of
    Left a' -> QFAtomic b a'
    Right f' -> if b then f' else negateQF f'
mapAtoms f (QFOr f1 f2) = QFOr (mapAtoms f f1) (mapAtoms f f2)
mapAtoms f (QFAnd f1 f2) = QFAnd (mapAtoms f f1) (mapAtoms f f2)
mapAtoms f (QOr v s f1) = QOr v s (mapAtoms f f1)
mapAtoms f (QAnd v s f1) = QAnd v s (mapAtoms f f1)
mapAtoms _ Top = Top
mapAtoms _ Bottom = Bottom

class Sub m where
  applySubs :: (m a -> m b) -> m a -> m b

instance Sub QFFormula where
  applySubs f (QFOr f1 f2) = QFOr (f f1) (f f2)
  applySubs f (QFAnd f1 f2) = QFAnd (f f1) (f f2)
  applySubs f (QOr v s f1) = QOr v s (f f1)
  applySubs f (QAnd v s f1) = QAnd v s (f f1)
  applySubs _ Top = Top
  applySubs _ Bottom = Bottom
  applySubs f x = f x

instance Sub Formula where
  applySubs f (Or f1 f2) = Or (f f1) (f f2)
  applySubs f (And f1 f2) = And (f f1) (f f2)
  applySubs f (Not f1) = Not (f f1)
  applySubs f (Forall v f1) = Forall v (f f1)
  applySubs f (Exists v f1) = Exists v (f f1)
  applySubs f x = f x

-- PRETTY PRINTING


showBinop :: Show a => Show b => String -> a -> b -> String
showBinop s f1 f2 =
  printf "%s %s %s" (show f1) s (show f2)

showParens :: String -> String
showParens s = printf "(%s)" s

-- TODO: Pretty print terms

instance Show Term where
  show (Term constant vars) =
    case Map.assocs $ Map.filterWithKey (\_ a -> a /= 0) vars of
      [] -> show constant
      (h : t) -> showFirstCoeff h ++ concatMap showCoeff t ++ showConstant constant
        where
          showConstant n =
            if n == 0 then ""
            else if n > 0 then "+" ++ show n
            else "-" ++ show (abs n)
          showFirstCoeff (var, coeff) =
            if coeff == 0 then ""
            else if coeff == 1 then show var
            else if coeff == -1 then "-" ++ show var
            else show coeff ++ show var
          showCoeff (var, coeff) =
            if coeff == 0 then ""
            else if coeff == 1 then "+" ++ show var
            else if coeff == -1 then "-" ++ show var
            else showConstant coeff ++ show var

instance Show Cmp where
  show Lt' = "<"
  show Eq = "="
  show Gt = ">"
  show Ge = ">="
  show Le = "<="

instance Show Atom where
  show (Comparison cmp t1 t2) =
    showBinop (show cmp) t1 t2
  show (Div' n t) = showBinop "|" n t

instance Show DivAtom where
  show (Lt t1 t2) = showBinop "<" t1 t2
  show (Div n t) = showBinop "|" n t

instance Show DistAtom where
  show (Dist d) = show d
  show (DistLt t) = printf "DIST < %s" $ show t
  show (DistDiv h coeff) =
    if coeff == (constantTerm 0) then
      printf "%d | DIST" h
    else
      printf "%d | DIST + %s" h (show coeff)

instance Show a => Show (QFFormula a) where
  show Top = "TOP"
  show Bottom = "BOT"
  show (QFAtomic True a) = show a
  show (QFAtomic False a) = "NOT " ++ (showParens $ show a)
  show (QFOr f1 f2) = showParens $ showBinop "or" f1 f2
  show (QFAnd f1 f2) = showParens $ showBinop "and" f1 f2
  show (QOr v s f) = printf "\\/_{%s in %s} (%s)" (show v) (show s) (show f)
  show (QAnd v s f) = printf "/\\_{%s in %s} (%s)" (show v) (show s) (show f)

instance Show a => Show (Formula a) where
  show (Atomic a) = show a
  show (Or f1 f2) = showParens $ showBinop "or" f1 f2
  show (And f1 f2) = showParens $ showBinop "and" f1 f2
  show (Not f) = printf "not %s" (show f)
  show (Forall v f) = "forall " ++ show v ++ "(" ++ show f ++ ")"
  show (Exists v f) = "exists " ++ show v ++ "(" ++ show f ++ ")"

instance Show NatSet where
  show (Range a b) = printf "[%d, %d]" a b
  show (NSet s) = show s
