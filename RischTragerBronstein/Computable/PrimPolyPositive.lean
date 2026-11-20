import RischTragerBronstein.Computable.PrimPolyStrong

/-!
# Polynomials in a primitive `t` over `R(x)`: the positive answer

If the recursive limited-integration loop `primLoop` succeeds, then `∑_{j ≤ d} fⱼ(x) t ^ j` has an
elementary integral: with the returned `(cₖ, Qₖ)`, the antiderivative is
`∑ₖ (Qₖ₊₁ + cₖ / (k + 1)) t ^ (k + 1) + ∫ (f₀ - η Q₁)`, the last integrand being rational in `x`.

With `not_hasElementaryIntegral_primPoly`, elementary integrability of polynomials in one primitive
(in particular one logarithm `log b(x)`) with coefficients in `R(x)` is decided by `primLoop`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Differential R]
variable [Field K] [Differential K] [Algebra R K] [DifferentialAlgebra R K]

/-- The value of a fraction at `x ∈ K`. -/
noncomputable def evx (x : K) (q : CPoly R × CPoly R) : K :=
  aeval x (toPoly q.1) / aeval x (toPoly q.2)

theorem primStep_sound_in (h0 : ∀ r : R, r′ = 0) (x : K) (hx : x′ = 1)
    {En Ed : CPoly R} {Iη : RationalIntegral R} (hcη : rationalCheck En Ed Iη = true)
    (hEd : toPoly Ed ≠ 0) {k : ℕ} {An Ad : CPoly R} {Q : CPoly R × CPoly R}
    (hAd : toPoly Ad ≠ 0) (hQ : toPoly Q.2 ≠ 0) {c : R} {Q' : CPoly R × CPoly R}
    (h : primStep En Ed Iη k An Ad Q = some (c, Q')) :
    toPoly Q'.2 ≠ 0 ∧
      (evx x Q')′ = evx x (An, Ad) - ((k + 1 : ℕ) : K) * evx x (En, Ed) * evx x Q -
        algebraMap R K c * evx x (En, Ed) := by
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
  have hderiv : ∀ y : R⟮x⟯, ((y′ : R⟮x⟯) : K) = (y : K)′ := fun _ ↦ rfl
  obtain ⟨hQ', hsol⟩ := primStep_sound (K := R⟮x⟯) (RingHom.id R) hDpoly hcη hEd hAd hQ h
  refine ⟨hQ', ?_⟩
  have := congrArg (fun z : R⟮x⟯ ↦ (z : K)) hsol
  have hnat : (((k + 1 : ℕ) : R⟮x⟯) : K) = ((k + 1 : ℕ) : K) := by
    rw [← map_natCast (algebraMap R⟮x⟯ K)]
    rfl
  simp only [ev, Polynomial.map_id, RingHom.id_apply, hderiv, AddSubgroupClass.coe_sub,
    MulMemClass.coe_mul, IntermediateField.coe_div, hcoe, aeval_C, hnat] at this
  exact this

/-- The loop invariant of the positive side. -/
theorem hasElementaryIntegral_primLoop (h0 : ∀ r : R, r′ = 0) (x t : K) (hx : x′ = 1)
    (En Ed : CPoly R) (ht : t′ = evx x (En, Ed))
    (Iη : RationalIntegral R) (hcη : rationalCheck En Ed Iη = true) (hEd : toPoly Ed ≠ 0)
    (A D : ℕ → CPoly R) (k : ℕ) (hD0 : ∀ j ≤ k, toPoly (D j) ≠ 0)
    (Q : CPoly R × CPoly R) (hQ : toPoly Q.2 ≠ 0) {L : List (R × (CPoly R × CPoly R))}
    (hL : primLoop En Ed Iη A D k Q = some L) (W : K) :
    HasElementaryIntegral (W′ + (evx x Q)′ * t ^ (k + 1) +
      ∑ j ∈ Finset.range (k + 1), evx x (A j, D j) * t ^ j) := by
  have hcharK : CharZero K := charZero_of_injective_algebraMap (algebraMap R K).injective
  have htr : Transcendental R x :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx]; exact one_ne_zero)
  have hinjx : Function.Injective (aeval x : R[X] →ₐ[R] K) := transcendental_iff_injective.mp htr
  have hne : ∀ {P : R[X]}, P ≠ 0 → aeval x P ≠ 0 := fun hP ↦
    (map_ne_zero_iff (aeval x) hinjx).mpr hP
  induction k generalizing Q L W with
  | zero =>
    -- `W′ + q′ t + f₀ = (W + q t)′ + (f₀ - q η)`, the last term rational in `x`
    have h1 := hne (hD0 0 le_rfl)
    have h2 := hne hQ
    have h3 := hne hEd
    have hform : W′ + (evx x Q)′ * t ^ (0 + 1) +
        ∑ j ∈ Finset.range (0 + 1), evx x (A j, D j) * t ^ j =
        (W + evx x Q * t)′ +
          aeval x (toPoly (A 0) * (toPoly Q.2 * toPoly Ed) -
            toPoly Q.1 * toPoly En * toPoly (D 0)) /
          aeval x (toPoly (D 0) * (toPoly Q.2 * toPoly Ed)) := by
      rw [map_add, Derivation.leibniz, ht]
      simp only [evx, smul_eq_mul, zero_add, pow_one, Finset.range_one, Finset.sum_singleton,
        pow_zero, mul_one, map_sub, map_mul]
      field_simp
      ring
    rw [hform]
    exact hasElementaryIntegral_rational_in h0 x hx _ _
      (mul_ne_zero (hD0 0 le_rfl) (mul_ne_zero hQ hEd)) _
  | succ k ih =>
    simp only [primLoop] at hL
    cases hstep : primStep En Ed Iη (k + 1) (A (k + 1)) (D (k + 1)) Q with
    | none => rw [hstep] at hL; exact absurd hL (by simp)
    | some cQ =>
      obtain ⟨c, Q'⟩ := cQ
      rw [hstep] at hL
      simp only [Option.map_eq_some_iff] at hL
      obtain ⟨L', hL', -⟩ := hL
      obtain ⟨hQ', hsol⟩ := primStep_sound_in h0 x hx hcη hEd (hD0 (k + 1) le_rfl) hQ hstep
      set γ : K := algebraMap R K (c / ((k + 1 + 1 : ℕ) : R)) with hγ
      have hγ' : γ′ = 0 := by rw [hγ, deriv_algebraMap, h0, map_zero]
      have hγc : ((k + 1 + 1 : ℕ) : K) * γ = algebraMap R K c := by
        rw [hγ, map_div₀, map_natCast]
        exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))
      have hform : W′ + (evx x Q)′ * t ^ (k + 1 + 1) +
          ∑ j ∈ Finset.range (k + 1 + 1), evx x (A j, D j) * t ^ j =
          (W + (evx x Q + γ) * t ^ (k + 1 + 1))′ + (evx x Q')′ * t ^ (k + 1) +
            ∑ j ∈ Finset.range (k + 1), evx x (A j, D j) * t ^ j := by
        rw [Finset.sum_range_succ _ (k + 1), map_add, Derivation.leibniz, map_add, hγ',
          Derivation.leibniz_pow, ht, hsol, ← hγc]
        simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, add_zero]
        ring
      rw [hform]
      exact ih (fun j hj ↦ hD0 j (by omega)) Q' hQ' hL' _

/-- **The positive answer for polynomials in a primitive.** -/
theorem hasElementaryIntegral_primPoly (h0 : ∀ r : R, r′ = 0) (x t : K) (hx : x′ = 1)
    (En Ed : CPoly R) (ht : t′ = aeval x (toPoly En) / aeval x (toPoly Ed))
    (Iη : RationalIntegral R) (hcη : rationalCheck En Ed Iη = true)
    (d : ℕ) (A D : ℕ → CPoly R) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0)
    {L : List (R × (CPoly R × CPoly R))} (hL : primLoop En Ed Iη A D d ([], [1]) = some L) :
    HasElementaryIntegral (∑ j ∈ Finset.range (d + 1),
      aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j) := by
  have hEd : toPoly Ed ≠ 0 := by
    have h := hcη
    rw [rationalCheck, Bool.and_eq_true] at h
    exact ((hermiteCheck_iff _ _ _).mp h.1).1
  have := hasElementaryIntegral_primLoop h0 x t hx En Ed ht Iη hcη hEd A D d hD0 ([], [1])
    (by simp) hL 0
  have hz : (evx x (([] : CPoly R), ([1] : CPoly R)))′ = 0 := by simp [evx]
  rw [hz] at this
  simpa [evx] using this

/-! ### The explicit antiderivative -/

/-- The closed-form part `∑ₖ (Qₖ₊₁ + cₖ / (k + 1)) t ^ (k + 1) + Q₁ t` of the antiderivative, read off
from the output of `primLoop` (`m` is the current power of `t`). -/
noncomputable def primW (x t : K) : ℕ → CPoly R × CPoly R → List (R × (CPoly R × CPoly R)) → K
  | _, Q, [] => evx x Q * t
  | m, Q, cQ :: L =>
    (evx x Q + algebraMap R K (cQ.1 / (m : R))) * t ^ m + primW x t (m - 1) cQ.2 L

/-- The last fraction `Q₁` produced by the loop. -/
def primLast : CPoly R × CPoly R → List (R × (CPoly R × CPoly R)) → CPoly R × CPoly R
  | Q, [] => Q
  | _, cQ :: L => primLast cQ.2 L

/-- **The result is an antiderivative.** If `primLoop` returns `L`, then with the explicit
`W = primW … L ∈ K`,

  `Q′ t ^ (k + 1) + ∑_{j ≤ k} fⱼ t ^ j = W′ + (f₀ - η Q₁)`,

and the remainder `f₀ - η Q₁` is a rational function of `x` (integrated by `integrateRational`). -/
theorem primLoop_antiderivative (h0 : ∀ r : R, r′ = 0) (x t : K) (hx : x′ = 1)
    (En Ed : CPoly R) (ht : t′ = evx x (En, Ed))
    (Iη : RationalIntegral R) (hcη : rationalCheck En Ed Iη = true) (hEd : toPoly Ed ≠ 0)
    (A D : ℕ → CPoly R) (k : ℕ) (hD0 : ∀ j, 1 ≤ j → j ≤ k → toPoly (D j) ≠ 0)
    (Q : CPoly R × CPoly R) (hQ : toPoly Q.2 ≠ 0) {L : List (R × (CPoly R × CPoly R))}
    (hL : primLoop En Ed Iη A D k Q = some L) :
    (evx x Q)′ * t ^ (k + 1) + ∑ j ∈ Finset.range (k + 1), evx x (A j, D j) * t ^ j =
      (primW x t (k + 1) Q L)′ + (evx x (A 0, D 0) - evx x (En, Ed) * evx x (primLast Q L)) := by
  have hcharK : CharZero K := charZero_of_injective_algebraMap (algebraMap R K).injective
  induction k generalizing Q L with
  | zero =>
    simp only [primLoop, Option.some.injEq] at hL
    subst hL
    rw [primW, primLast, Derivation.leibniz, ht]
    simp only [smul_eq_mul, zero_add, pow_one, Finset.range_one, Finset.sum_singleton, pow_zero,
      mul_one]
    ring
  | succ k ih =>
    simp only [primLoop] at hL
    cases hstep : primStep En Ed Iη (k + 1) (A (k + 1)) (D (k + 1)) Q with
    | none => rw [hstep] at hL; exact absurd hL (by simp)
    | some cQ =>
      obtain ⟨c, Q'⟩ := cQ
      rw [hstep] at hL
      simp only [Option.map_eq_some_iff] at hL
      obtain ⟨L', hL', rfl⟩ := hL
      obtain ⟨hQ', hsol⟩ := primStep_sound_in h0 x hx hcη hEd (hD0 (k + 1) (by omega) le_rfl) hQ
        hstep
      have hrec := ih (fun j h1 h2 ↦ hD0 j h1 (by omega)) Q' hQ' hL'
      set γ : K := algebraMap R K (c / ((k + 1 + 1 : ℕ) : R)) with hγ
      have hγ' : γ′ = 0 := by rw [hγ, deriv_algebraMap, h0, map_zero]
      have hγc : ((k + 1 + 1 : ℕ) : K) * γ = algebraMap R K c := by
        rw [hγ, map_div₀, map_natCast]
        exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))
      have hX : ((evx x Q + γ) * t ^ (k + 1 + 1))′ = (evx x Q)′ * t ^ (k + 1 + 1) +
          ((k + 1 + 1 : ℕ) : K) * (evx x Q + γ) * evx x (En, Ed) * t ^ (k + 1) := by
        rw [Derivation.leibniz, map_add, hγ', Derivation.leibniz_pow, ht]
        simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, add_zero]
        ring
      have hW : primW x t (k + 1 + 1) Q ((c, Q') :: L') =
          (evx x Q + γ) * t ^ (k + 1 + 1) + primW x t (k + 1) Q' L' := rfl
      rw [hW, primLast, map_add, hX, Finset.sum_range_succ _ (k + 1)]
      linear_combination hrec - t ^ (k + 1) * hsol - evx x (En, Ed) * t ^ (k + 1) * hγc

end CPoly
