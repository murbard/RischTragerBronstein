import RischTragerBronstein.Computable.CField
import RischTragerBronstein.Differential.Monomial

/-!
# Computable models of monomial extensions: the tower step

Given operations `O : COps α` with a model `M : CField α K O`, and a code `w : GPoly α` for
`W ∈ K[t]`:

* `COps.monomial O w : COps (GPoly α × GPoly α)` — **computable** operations on fractions
  `(num, den)` of coded polynomials, with the derivation given by the quotient rule and `t′ = W`;
* `CField.monomial M w` — the proof that they model `(K(t), t′ = W)`, i.e. `RatFunc K` with
  `Differential.ratFuncOfDeriv W`.

No normalisation and no invariant on codes is needed: Lean's convention `a / 0 = 0` makes every
operation except addition correct on all pairs, and addition guards the zero-denominator case.

Iterating the construction gives computable models of towers
`C ⊂ C(x) ⊂ C(x)(t₁) ⊂ C(x)(t₁)(t₂) ⊂ …` of any height, with `tᵢ′` an arbitrary polynomial in `tᵢ`
over the previous field: logarithms (`t′ = a′ / a`), exponentials (`t′ = a′ t`), tangents, ….
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

/-- Codes for elements of `K(t)`: pairs `(num, den)` of coded polynomials. -/
abbrev GFrac (α : Type*) := GPoly α × GPoly α

namespace COps

variable {α : Type*} (O : COps α)

/-- **The tower step**, operations: fractions over `O`, derivation with `t′ = w`. -/
def monomial (w : GPoly α) : COps (GFrac α) where
  zero := ([], [O.one])
  one := ([O.one], [O.one])
  add := fun a b ↦
    if GPoly.isZero O a.2 then b
    else if GPoly.isZero O b.2 then a
    else (GPoly.add O (GPoly.mul O a.1 b.2) (GPoly.mul O b.1 a.2), GPoly.mul O a.2 b.2)
  neg := fun a ↦ (GPoly.neg O a.1, a.2)
  mul := fun a b ↦ (GPoly.mul O a.1 b.1, GPoly.mul O a.2 b.2)
  inv := fun a ↦ (a.2, a.1)
  deriv := fun a ↦
    (GPoly.sub O (GPoly.mul O (GPoly.derivT O w a.1) a.2) (GPoly.mul O a.1 (GPoly.derivT O w a.2)),
      GPoly.mul O a.2 a.2)
  isZero := fun a ↦ GPoly.isZero O a.1 || GPoly.isZero O a.2
  natCast := fun n ↦ ([O.natCast n], [O.one])

end COps

namespace GFrac

variable {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

/-- Semantics of a fraction code (`num / den`, with `a / 0 = 0`). -/
noncomputable def sem (q : GFrac α) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (GPoly.toPoly M q.1) / algebraMap K[X] (RatFunc K) (GPoly.toPoly M q.2)

end GFrac

namespace CField

variable {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

/-- **The tower step**, model: `COps.monomial O w` models `(K(t), t′ = W)`. -/
noncomputable def monomial (w : GPoly α) :
    @CField (GFrac α) (RatFunc K) _ (ratFuncOfDeriv (GPoly.toPoly M w)) (O.monomial w) :=
  letI : Differential (RatFunc K) := ratFuncOfDeriv (GPoly.toPoly M w)
  have hφ0 : ∀ {P : K[X]}, P ≠ 0 → algebraMap K[X] (RatFunc K) P ≠ 0 :=
    fun h ↦ RatFunc.algebraMap_ne_zero h
  { sem := GFrac.sem M
    sem_zero := by simp [GFrac.sem, COps.monomial]
    sem_one := by simp [GFrac.sem, COps.monomial, M.sem_one]
    sem_add := fun a b ↦ by
      simp only [COps.monomial]
      split_ifs with ha hb
      · have h0 := (GPoly.isZero_iff M _).mp ha
        simp [GFrac.sem, h0]
      · have h0 := (GPoly.isZero_iff M _).mp hb
        simp [GFrac.sem, h0]
      · have ha' := hφ0 (fun h ↦ ha ((GPoly.isZero_iff M _).mpr h))
        have hb' := hφ0 (fun h ↦ hb ((GPoly.isZero_iff M _).mpr h))
        simp only [GFrac.sem, GPoly.toPoly_add, GPoly.toPoly_mul, map_add, map_mul]
        field_simp
    sem_neg := fun a ↦ by
      simp only [COps.monomial, GFrac.sem, GPoly.toPoly_neg, map_neg, neg_div]
    sem_mul := fun a b ↦ by
      simp only [COps.monomial, GFrac.sem, GPoly.toPoly_mul, map_mul, mul_div_mul_comm]
    sem_inv := fun a ↦ by
      simp only [COps.monomial, GFrac.sem, inv_div]
    sem_deriv := fun a ↦ by
      letI : Differential K[X] := polynomialOfDeriv (GPoly.toPoly M w)
      simp only [COps.monomial, GFrac.sem, GPoly.toPoly_sub, GPoly.toPoly_mul,
        GPoly.toPoly_derivT, map_mul]
      by_cases hd : GPoly.toPoly M a.2 = 0
      · simp [hd]
      · have hq := ofFractionRing_deriv_div K[X] (RatFunc K) (GPoly.toPoly M a.1)
          (GPoly.toPoly M a.2) hd
        rw [hq, pow_two]
        rfl
    sem_natCast := fun n ↦ by
      simp only [COps.monomial, GFrac.sem, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero,
        add_zero, M.sem_natCast, M.sem_one, map_one, div_one]
      rw [← map_natCast (algebraMap K[X] (RatFunc K)), ← map_natCast (C : K →+* K[X])]
    isZero_iff := fun a ↦ by
      simp only [COps.monomial, Bool.or_eq_true, GFrac.sem, div_eq_zero_iff,
        map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
      rw [GPoly.isZero_iff M, GPoly.isZero_iff M] }

end CField
