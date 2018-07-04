module Addition.Digit

import Common.Util
import Common.Interfaces
import Specifications.TranslationInvariance
import Proofs.Interval

%default total
%access public export

data Digit : (leq : Binrel s) -> (neg : s -> s) -> s -> Type where
  MkDigit : (x : s) -> .InSymRange leq neg u x -> Digit leq neg u

val : Digit {s} _ _ _ -> s
val (MkDigit x _) = x

implementation Show s => Show (Digit {s} leq neg u) where
  show (MkDigit x _) = show x

||| adding two digits makes the range twice as big
addDigits : Ringops s => PartiallyOrderedGroupSpec {s} (+) Zero Ng leq ->
  OuterBinop (Digit leq Ng) u u (u + u)
addDigits spec (MkDigit x p) (MkDigit y q) =
  MkDigit (x + y) (addInSymRange spec p q)


||| To produce test input, full decidability is overkill
maybeDigit : Decidable [s,s] leq => (neg : s -> s) -> (u : s) ->
  s -> Maybe (Digit leq neg u)
maybeDigit {leq} neg u x =
  case decideBetween {leq} (neg u) u x of
    Yes prf => Just (MkDigit x prf)
    No _ => Nothing

||| To produce test input, full decidability is overkill
maybeDigits : (Traversable trav, Decidable [s,s] leq) =>
  (neg : s -> s) -> (u : s) -> trav s -> Maybe (trav (Digit leq neg u))
maybeDigits {leq} neg u = sequence . map (maybeDigit {leq} neg u)
