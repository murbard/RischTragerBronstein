import RischTragerBronstein.Computable.GEuclidDegree
import Mathlib.RingTheory.Coprime.Basic

/-!
# The Bézout solver over a computable model

`GPoly.solveBezout_spec`: for coprime `a`, `b` with `b ≠ 0`, the executable
`solveBezout O a b c = (s, t)` satisfies `s * a + t * b = c` — at every level of a computable
tower. This is the inner step of Hermite reduction in `K(t)`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace GPoly

variable {α K : Type*} [Field K] [Differential K]

section Ops

variable (O : COps α)

/-- Quotient of the division. -/
def div (p d : GPoly α) : GPoly α := (divMod O p d).1

/-- A (non-normalised) gcd. -/
def gcd (p q : GPoly α) : GPoly α := trim O (egcd O p q).1

/-- Solve `s * a + t * b = c` with `s` reduced modulo `b` (for coprime `a`, `b`). -/
def solveBezout (a b c : GPoly α) : GPoly α × GPoly α :=
  let e := egcd O a b
  let γ := lead O (trim O e.1)
  let s := (divMod O (smul O (O.inv γ) (mul O c e.2.1)) b).2
  (s, div O (sub O c (mul O s a)) b)

end Ops

variable {O : COps α} (M : CField α K O)

lemma toPoly_gcd (p q : GPoly α) : toPoly M (gcd O p q) = toPoly M (egcd O p q).1 :=
  toPoly_trim M _

theorem solveBezout_spec (a b c : GPoly α) (hb : toPoly M b ≠ 0)
    (hcop : IsCoprime (toPoly M a) (toPoly M b)) :
    toPoly M (solveBezout O a b c).1 * toPoly M a + toPoly M (solveBezout O a b c).2 * toPoly M b =
      toPoly M c := by
  have hbez := egcd_spec M a b
  obtain ⟨hga, hgb⟩ := egcd_dvd M a b
  set g := (egcd O a b).1 with hg
  set σ := (egcd O a b).2.1 with hσ
  set τ := (egcd O a b).2.2 with hτ
  have hunit : IsUnit (toPoly M g) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact isUnit_of_dvd_one (huv ▸ dvd_add (Dvd.dvd.mul_left hga u) (Dvd.dvd.mul_left hgb v))
  obtain ⟨γ, hγ, hgγ⟩ := Polynomial.isUnit_iff.mp hunit
  have hγ0 : γ ≠ 0 := hγ.ne_zero
  have hlead : M.sem (lead O (trim O g)) = γ := by
    rw [← leadingCoeff_toPoly M (by rw [← hgγ]; exact C_ne_zero.mpr hγ0), ← hgγ, leadingCoeff_C]
  set S0 := smul O (O.inv (lead O (trim O g))) (mul O c σ) with hS0
  have hsol : solveBezout O a b c =
      ((divMod O S0 b).2, div O (sub O c (mul O (divMod O S0 b).2 a)) b) := rfl
  rw [hsol]
  have hdm := divMod_spec M S0 b
  set q := (divMod O S0 b).1
  set s := (divMod O S0 b).2
  have hS0p : toPoly M S0 = C γ⁻¹ * (toPoly M c * toPoly M σ) := by
    simp [hS0, M.sem_inv, hlead]
  have hCγ : C γ⁻¹ * C γ = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hγ0, C_1]
  have hdvd : toPoly M b ∣ toPoly M (sub O c (mul O s a)) := by
    refine ⟨C γ⁻¹ * toPoly M c * toPoly M τ + toPoly M q * toPoly M a, ?_⟩
    have hs : toPoly M s = toPoly M S0 - toPoly M q * toPoly M b := by rw [hdm]; ring
    rw [toPoly_sub, toPoly_mul, hs, hS0p]
    linear_combination (-(C γ⁻¹ * toPoly M c)) * hbez - (toPoly M c) * hCγ +
      (C γ⁻¹ * toPoly M c) * hgγ
  have hexact := div_mul_of_dvd M (sub O c (mul O s a)) b hb hdvd
  rw [toPoly_sub, toPoly_mul] at hexact
  change toPoly M s * toPoly M a + toPoly M (divMod O (sub O c (mul O s a)) b).1 * toPoly M b = _
  linear_combination -hexact

end GPoly
