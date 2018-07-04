module Addition.Reduce

import Data.Vect
import Common.Util
import Common.Interfaces
import Specifications.OrderedRing
import Addition.Carry
import Addition.Absorb
import Addition.AbsorptionLemmas
import public Addition.Digit

%default total
%access export

||| Recursively reduce the input digits and absorb the carries. 
total
reduce : (Ringops s, Decidable [s,s] leq) =>
  DiscreteOrderedRingSpec (+) Zero Ng (*) leq One ->
  (u : s) ->
  (bound : leq One (u + Ng One)) ->
  (digits : Vect (S k) (Digit leq Ng (u + u))) ->
  Absorption k (Ranges leq Ng u (u + Ng One)) (phi (One + u))
      (map Digit.val digits)
-- Base case. Explicitly pass dictionaries to improve compilation time.
reduce @{ops} spec u bound [MkDigit input inRange] =
  absorptionBase @{ops} spec {u} (One + u)
      (computeCarry @{ops}
        (discreteOrderedGroup spec) u bound input inRange)
-- Recursive case.
reduce @{ops} spec u bound (MkDigit input inRange :: digits@(_::_)) =
  absorptionStep @{ops} spec {u} (One + u)
    (computeCarry @{ops}
       (discreteOrderedGroup spec) u bound input inRange)
    (reduce @{ops} spec u bound digits)
