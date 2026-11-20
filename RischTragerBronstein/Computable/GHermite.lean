import RischTragerBronstein.Computable.GBezout
import Mathlib.FieldTheory.Separable

/-!
# Executable Hermite reduction in a monomial extension, with a verified checker

For a computable model `M` of `K` and `t′ = W` (code `w`), working in `(K(t), t′ = W)`:

* `GPoly.hermite O w A D` — Mack's linear Hermite reduction, with the **tower derivation**
  `derivT O w` in the Bézout coefficient and `d/dt` (`derivX`) for the squarefree part;
* `GPoly.hermiteCheck O w A D r` — a decidable certificate for an output `r = (gn, gd, b, s)`;
* `GPoly.hermiteCheck_sound` — if the certificate passes, then in `RatFunc K` with
  `ratFuncOfDeriv W`:  `A / D = (gn / gd)′ + b / s`  and `s` is squarefree.

So Hermite reduction is available, certified, at every level of a computable tower. (That the
certificate always passes holds in primitive extensions, where all irreducibles are normal —
`Rational/SquarefreePartD.lean`; in exponential extensions the special prime `t` must first be
split off, cf. `hermite_reduction_exponential`.)
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace GPoly

variable {α K : Type*} [Field K] [Differential K]

/-- Output of Hermite reduction: `A / D = (gn / gd)′ + b / s`. -/
structure HermiteResult (α : Type*) where
  gn : GPoly α
  gd : GPoly α
  b : GPoly α
  s : GPoly α

section Ops

variable (O : COps α) (w : GPoly α)

/-- Mack's loop in `K(t)`. -/
def hermiteLoop : ℕ → GPoly α → GPoly α → GPoly α → GPoly α → GPoly α → HermiteResult α
  | 0, gn, gd, A, Ds, Dm => ⟨gn, gd, A, mul O Ds Dm⟩
  | fuel + 1, gn, gd, A, Ds, Dm =>
    if (trim O Dm).length ≤ 1 then ⟨trim O gn, trim O gd, trim O A, trim O (mul O Ds Dm)⟩
    else
      let Dm2 := gcd O Dm (derivX O Dm)
      let Dms := div O Dm Dm2
      let BC := solveBezout O (neg O (div O (mul O Ds (derivT O w Dm)) Dm)) Dms A
      let A' := sub O BC.2 (div O (mul O (derivT O w BC.1) Ds) Dms)
      hermiteLoop fuel (add O (mul O gn Dm) (mul O BC.1 gd)) (mul O gd Dm) A' Ds Dm2

/-- Hermite reduction of `A / D` in `K(t)`. -/
def hermite (A D : GPoly α) : HermiteResult α :=
  let Dm := gcd O D (derivX O D)
  hermiteLoop O w D.length [] [O.one] A (div O D Dm) Dm

/-- Certificate of squarefreeness. -/
def squarefreeCheck (s : GPoly α) : Bool := (trim O (egcd O s (derivX O s)).1).length == 1

/-- Certificate for `A / D = (gn / gd)′ + b / s`, `s` squarefree. -/
def hermiteCheck (A D : GPoly α) (r : HermiteResult α) : Bool :=
  !isZero O D && !isZero O r.gd && !isZero O r.s &&
  isZero O (sub O (mul O (mul O A (mul O r.gd r.gd)) r.s)
    (add O (mul O (mul O (sub O (mul O (derivT O w r.gn) r.gd) (mul O r.gn (derivT O w r.gd))) D)
      r.s) (mul O (mul O r.b D) (mul O r.gd r.gd)))) &&
  squarefreeCheck O r.s

end Ops

variable {O : COps α} (M : CField α K O)

theorem squarefreeCheck_sound {s : GPoly α} (h : squarefreeCheck O s = true) :
    Squarefree (toPoly M s) := by
  rw [squarefreeCheck, beq_iff_eq] at h
  have hne : trim O (egcd O s (derivX O s)).1 ≠ [] := fun h0 ↦ by simp [h0] at h
  have hdeg : (toPoly M (egcd O s (derivX O s)).1).natDegree = 0 := by
    have := length_trim M hne
    omega
  have hg0 : toPoly M (egcd O s (derivX O s)).1 ≠ 0 := fun h0 ↦
    hne ((trim_eq_nil_iff M _).mpr h0)
  obtain ⟨γ, hγ⟩ : ∃ γ : K, toPoly M (egcd O s (derivX O s)).1 = C γ :=
    ⟨_, eq_C_of_natDegree_eq_zero hdeg⟩
  have hγ0 : γ ≠ 0 := fun h0 ↦ hg0 (by rw [hγ, h0, C_0])
  have hbez := egcd_spec M s (derivX O s)
  rw [hγ, toPoly_derivX] at hbez
  refine Separable.squarefree ⟨C γ⁻¹ * toPoly M (egcd O s (derivX O s)).2.1,
    C γ⁻¹ * toPoly M (egcd O s (derivX O s)).2.2, ?_⟩
  have : C γ⁻¹ * C γ = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hγ0, C_1]
  linear_combination C γ⁻¹ * hbez + this

/-- **Soundness of the Hermite certificate in `(K(t), t′ = W)`.** -/
theorem hermiteCheck_sound (w A D : GPoly α) (r : HermiteResult α)
    (hc : hermiteCheck O w A D r = true) :
    letI := ratFuncOfDeriv (toPoly M w)
    algebraMap K[X] (RatFunc K) (toPoly M A) / algebraMap K[X] (RatFunc K) (toPoly M D) =
      (algebraMap K[X] (RatFunc K) (toPoly M r.gn) /
          algebraMap K[X] (RatFunc K) (toPoly M r.gd))′ +
        algebraMap K[X] (RatFunc K) (toPoly M r.b) / algebraMap K[X] (RatFunc K) (toPoly M r.s) ∧
    Squarefree (toPoly M r.s) := by
  let _ := polynomialOfDeriv (toPoly M w)
  let _ := ratFuncOfDeriv (toPoly M w)
  simp only [hermiteCheck, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
    isZero_iff M] at hc
  obtain ⟨⟨⟨⟨hD, hgd⟩, hs⟩, hid⟩, hsq⟩ := hc
  refine ⟨?_, squarefreeCheck_sound M hsq⟩
  set φ := algebraMap K[X] (RatFunc K)
  have hφD : φ (toPoly M D) ≠ 0 := RatFunc.algebraMap_ne_zero hD
  have hφgd : φ (toPoly M r.gd) ≠ 0 := RatFunc.algebraMap_ne_zero hgd
  have hφs : φ (toPoly M r.s) ≠ 0 := RatFunc.algebraMap_ne_zero hs
  have hquot := ofFractionRing_deriv_div K[X] (RatFunc K) (toPoly M r.gn) (toPoly M r.gd) hgd
  rw [hquot]
  change _ = φ (implicitDeriv (toPoly M w) (toPoly M r.gn) * toPoly M r.gd -
    toPoly M r.gn * implicitDeriv (toPoly M w) (toPoly M r.gd)) / φ (toPoly M r.gd) ^ 2 + _
  rw [toPoly_sub] at hid
  have hid' := congrArg φ (sub_eq_zero.mp hid)
  simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_derivT, map_mul, map_add, map_sub]
    at hid'
  simp only [map_mul, map_sub]
  field_simp
  linear_combination hid'

end GPoly
