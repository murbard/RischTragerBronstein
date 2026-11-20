import RischTragerBronstein.Computable.ExpPolyRat

/-!
# Polynomials in `exp (a(x))` with rational coefficients: the positive answer

* `rdeRational_sound_in`: a solution returned by `rdeRational g A D`, evaluated at an element `x`
  with `x′ = 1` of **any** differential field `K ⊇ R`, solves `y′ + g(x) y = A(x) / D(x)` in `K`.
* `hasElementaryIntegral_expPolyRat`: if `rdeRational ((j+1) a′) Aⱼ Dⱼ = some (Yⱼ, Gⱼ)` for all
  `j < n`, then `A₀/D₀ + ∑_{j<n} (Aⱼ/Dⱼ) t^(j+1)` has an elementary integral, namely
  `∑ (Yⱼ/Gⱼ) t^(j+1) + ∫ A₀/D₀`.

With `not_hasElementaryIntegral_expPolyRat`, elementary integrability of polynomials in `exp a`
with coefficients in `R(x)` is decided by `n` runs of the verified solver.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Differential R]
variable [Field K] [Differential K] [Algebra R K] [DifferentialAlgebra R K]

theorem rdeRational_sound_in (h0 : ∀ r : R, r′ = 0) (x : K) (hx : x′ = 1) {g A D Y G : CPoly R}
    (hD0 : toPoly D ≠ 0) (hsome : rdeRational g A D = some (Y, G)) :
    (aeval x (toPoly Y) / aeval x (toPoly G))′ +
        aeval x (toPoly g) * (aeval x (toPoly Y) / aeval x (toPoly G)) =
      aeval x (toPoly A) / aeval x (toPoly D) := by
  have htr : Transcendental R x :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx]; exact one_ne_zero)
  have hw : x′ = aeval x (1 : R[X]) := by rw [hx, map_one]
  let _ := algebraAdjoinSimple (F := R) x
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x 1 hw)
  have hFR : IsFractionRing R[X] R⟮x⟯ := isFractionRing_adjoin_simple x htr
  have hDA : DifferentialAlgebra R[X] R⟮x⟯ := differentialAlgebra_adjoin_simple x 1 hw
  have hDpoly : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x⟯ P : R⟮x⟯) : K) = aeval x P :=
    algebraMap_adjoinSimple x
  have hsol := rdeRational_sound (K := R⟮x⟯) (RingHom.id R) hDpoly hD0 hsome
  simp only [Polynomial.map_id] at hsol
  have := congrArg (fun z : R⟮x⟯ ↦ (z : K)) hsol
  simp only [IntermediateField.coe_div, IntermediateField.coe_add, IntermediateField.coe_mul,
    hcoe] at this
  rw [← this]
  congr 1
  simp only [← hcoe, ← IntermediateField.coe_div]
  rfl

theorem hasElementaryIntegral_expPolyRat (h0 : ∀ r : R, r′ = 0) (x t : K) (hx : x′ = 1)
    (a : CPoly R) (ht : t′ = aeval x (derivative (toPoly a)) * t)
    (n : ℕ) (A D Y G : ℕ → CPoly R) (A₀ D₀ : CPoly R) (hD₀ : toPoly D₀ ≠ 0)
    (hD0 : ∀ j < n, toPoly (D j) ≠ 0)
    (hsome : ∀ j < n, rdeRational (expCoeff a j) (A j) (D j) = some (Y j, G j)) :
    HasElementaryIntegral (aeval x (toPoly A₀) / aeval x (toPoly D₀) +
      ∑ j ∈ Finset.range n, aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ (j + 1)) := by
  set W : K := ∑ j ∈ Finset.range n,
    aeval x (toPoly (Y j)) / aeval x (toPoly (G j)) * t ^ (j + 1) with hW
  have hW' : W′ = ∑ j ∈ Finset.range n,
      aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ (j + 1) := by
    rw [hW, map_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjn := Finset.mem_range.mp hj
    have hsol := rdeRational_sound_in h0 x hx (hD0 j hjn) (hsome j hjn)
    have hg : aeval x (toPoly (expCoeff a j)) =
        ((j + 1 : ℕ) : K) * aeval x (derivative (toPoly a)) := by
      rw [expCoeff, toPoly_smul, toPoly_deriv, map_mul, aeval_C, map_natCast]
    rw [hg] at hsol
    rw [Derivation.leibniz, Derivation.leibniz_pow, ht, ← hsol]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
    rw [pow_succ]
    ring
  have hform : aeval x (toPoly A₀) / aeval x (toPoly D₀) +
      ∑ j ∈ Finset.range n, aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ (j + 1) =
      W′ + aeval x (toPoly A₀) / aeval x (toPoly D₀) := by rw [hW']; ring
  rw [hform]
  exact hasElementaryIntegral_rational_in h0 x hx _ _ hD₀ W

end CPoly
