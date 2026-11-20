import RischTragerBronstein.Computable.ExpPolyDecision
import RischTragerBronstein.Computable.LogTimesPositive

/-!
# The zero-test oracle

Integration algorithms must decide whether constants are zero. For `ℚ` or number fields this is
decidable outright; for constants such as `e`, `π`, `log 2` it is the *constant problem*, undecidable
in general, and implementations use heuristics (e.g. numerical evaluation at random points).

This file isolates that dependency. A `ZeroOracle C` is a Boolean zero test on `C` together with the
statement that it is correct. Every algorithm of this development is parametric in
`[DecidableEq R]`, and `ZeroOracle.decidableEq` turns an oracle into that instance. Consequently:

* **all soundness and completeness theorems hold verbatim for an oracle-driven instantiation**, and
* the **only** thing that can ever be assumed is the field `correct` of the oracle in use.

Policy (requested by the user of this development): a heuristic zero test may be admitted through
exactly one named assumption — the `correct` field of its `ZeroOracle`, provided e.g. as a single
`axiom` next to the implementation — and nothing else may be admitted. No such axiom appears in
this library; `ZeroOracle.ofDecidableEq` gives the exact oracle wherever equality is decidable.
-/

/-- A zero test on `C` with its correctness statement. -/
structure ZeroOracle (C : Type*) [Zero C] where
  /-- the (possibly heuristic) test -/
  isZero : C → Bool
  /-- the single trusted fact about it -/
  correct : ∀ c, isZero c = true ↔ c = 0

namespace ZeroOracle

variable {C : Type*}

/-- The exact oracle, when equality is decidable. Nothing is assumed. -/
def ofDecidableEq [Zero C] [DecidableEq C] : ZeroOracle C where
  isZero c := decide (c = 0)
  correct c := by simp

/-- An oracle yields decidable equality, which is all the algorithms require. -/
def decidableEq [AddGroup C] (O : ZeroOracle C) : DecidableEq C := fun a b ↦
  decidable_of_iff (O.isZero (a - b) = true) (by rw [O.correct, sub_eq_zero])

end ZeroOracle

namespace CPoly

open Differential Polynomial

/-- The decision theorem for `∫ p exp a`, driven by an arbitrary zero oracle: both answers remain
proved, relative only to the oracle's `correct` field. -/
theorem integrateExpPoly_decides_of_oracle {R : Type*} [Field R] [CharZero R] [Differential R]
    (O : ZeroOracle R) (h0 : ∀ r : R, r′ = 0) (p a : CPoly R) :
    letI := O.decidableEq
    trim (deriv a) ≠ [] →
    letI : Differential (RatFunc R) := ratFuncOfDeriv (1 : R[X])
    letI : Differential (RatFunc (RatFunc R)) := ratFuncOfDeriv (C (expEta a) * X)
    (∀ Y, integrateExpPoly p a = some Y →
        (expIntegrand Y)′ = expIntegrand p ∧ HasElementaryIntegral (expIntegrand p)) ∧
    (integrateExpPoly p a = none → ¬HasElementaryIntegral (expIntegrand p)) :=
  letI := O.decidableEq
  fun ha ↦ integrateExpPoly_decides h0 p a ha

end CPoly

-- The exact oracle on `ℚ` drives the same computation as before.
#eval
  letI := (ZeroOracle.ofDecidableEq (C := ℚ)).decidableEq
  CPoly.integrateExpPoly ([1] : CPoly ℚ) [0, 0, 1]
