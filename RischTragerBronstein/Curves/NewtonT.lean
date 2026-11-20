import RischTragerBronstein.Curves.AutoPuiseux
import RischTragerBronstein.Curves.Puiseux

/-!
# Correctness of the truncated Newton iteration

`newtonT H L k Z` runs `k` Newton steps `Z ↦ Z − H(Z)/H_Y(Z)` on truncated series (precision
`L`). For a simple root `ρ ∈ F⟦T⟧` of `H(T, Y)`:

* `newton_step`: one step doubles the precision of an approximation (`Z ≡ ρ mod Tˢ` gives
  `Z' ≡ ρ mod T^{min(L, 2s)}`);
* `newtonT_approx`: `k` steps give precision `min(L, 2ᵏ s)`;
* **`newtonT_root`**: from `y₀` with `H(0, y₀) = 0 ≠ H_Y(0, y₀)`, the lift
  `newtonT H L (log₂ L + 3) [y₀]` agrees with the root `ρ`, `ρ(0) = y₀` (Hensel), modulo `T^L`.

This is the correctness of the Newton lifts used by the place search (`puiseuxAt`, `npRec`) and
by the irreducibility certificates at primes (`liftRootsAt`).
-/

open Polynomial

namespace Curves

open CPoly Sup

section Newton

variable {F : Type*} [Field F] [DecidableEq F]

/-- `F[T] → F⟦T⟧`. -/
local notation "cT" => (Polynomial.coeToPowerSeries.ringHom (R := F))

/-- The series of a truncated series. -/
noncomputable abbrev valT (Z : CPoly F) : PowerSeries F := cT (toPoly Z)

/-- `H(T, Y)` over `F⟦T⟧`. -/
noncomputable abbrev HS (H : BPoly F) : Polynomial (PowerSeries F) := (toB H).map cT

lemma sMulT_getD (p q : CPoly F) (L m : ℕ) (hm : m < L) :
    (sMulT p q L).getD m 0 = (toPoly p * toPoly q).coeff m := by
  rw [sMulT, List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_map, List.getElem_range,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b ↦ (toPoly p).coeff a * (toPoly q).coeff b)]
  simp [coeff_toPoly]

/-- **`evalBT` computes `H(Z)` below `T^L`.** -/
lemma evalBT_getD (Z : CPoly F) (L : ℕ) : ∀ (H : BPoly F), ∀ m < L,
    (evalBT H Z L).getD m 0 = ((toB H).eval (toPoly Z)).coeff m
  | [], m, hm => by simp [evalBT]
  | c :: H, m, hm => by
    have e : evalBT (c :: H) Z L = (List.range L).map fun m ↦
        c.getD m 0 + (sMulT Z (evalBT H Z L) L).getD m 0 := rfl
    rw [e, List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_map, List.getElem_range,
      sMulT_getD _ _ _ _ hm, toB_cons, eval_add, eval_C, eval_mul, eval_X, coeff_add, coeff_toPoly]
    congr 1
    rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [coeff_toPoly (evalBT H Z L), evalBT_getD Z L H ij.2 (by omega)]

lemma valT_eval (H : BPoly F) (Z : CPoly F) :
    (HS H).eval (valT Z) = cT ((toB H).eval (toPoly Z)) := by
  rw [HS, eval_map, eval₂_at_apply]

lemma derivative_HS (H : BPoly F) : derivative (HS H) = HS (derivYB H) := by
  rw [HS, HS, toB_derivYB, derivative_map]

/-- Agreement of coefficients below `L` as divisibility by `T^L`. -/
lemma X_pow_dvd_valT_sub {P : CPoly F} {Q : F[X]} {L : ℕ}
    (h : ∀ m < L, P.getD m 0 = Q.coeff m) :
    (PowerSeries.X : PowerSeries F) ^ L ∣ valT P - cT Q := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  simp only [map_sub, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
    coeff_toPoly, h m hm, sub_self]

lemma X_pow_dvd_evalBT (H : BPoly F) (Z : CPoly F) (L : ℕ) :
    (PowerSeries.X : PowerSeries F) ^ L ∣ valT (evalBT H Z L) - (HS H).eval (valT Z) := by
  rw [valT_eval]
  exact X_pow_dvd_valT_sub (evalBT_getD Z L H)

/-- One Newton step. -/
def newtonStep (H : BPoly F) (L : ℕ) (Z : CPoly F) : CPoly F :=
  (List.range L).map fun m ↦
    Z.getD m 0 - (sDivT (evalBT H Z L) (evalBT (derivYB H) Z L) L).getD m 0

lemma newtonT_succ (H : BPoly F) (L k : ℕ) (Z : CPoly F) :
    newtonT H L (k + 1) Z = newtonT H L k (newtonStep H L Z) := rfl

/-- **One Newton step doubles the precision.** -/
theorem newton_step (H : BPoly F) (L s : ℕ) (Z : CPoly F) (ρ : PowerSeries F)
    (hρ : (HS H).eval ρ = 0)
    (hu : PowerSeries.constantCoeff ((derivative (HS H)).eval ρ) ≠ 0) (hs : 1 ≤ s)
    (hZ : (PowerSeries.X : PowerSeries F) ^ s ∣ valT Z - ρ) :
    (PowerSeries.X : PowerSeries F) ^ (min L (2 * s)) ∣ valT (newtonStep H L Z) - ρ := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · rw [hL, Nat.zero_min, pow_zero]; exact one_dvd _
  set X := (PowerSeries.X : PowerSeries F)
  set ζ := valT Z with hζ
  set e := ζ - ρ with he
  set V := evalBT H Z L with hV
  set D := evalBT (derivYB H) Z L with hD
  set Q := sDivT V D L with hQ
  set H' := derivative (HS H) with hH'
  -- the derivative along `ζ` agrees with the derivative along `ρ` modulo `T`
  have hXe : X ∣ e := (dvd_pow_self X (by omega)).trans hZ
  have hD' : X ^ L ∣ valT D - H'.eval ζ := by
    rw [hH', derivative_HS]; exact X_pow_dvd_evalBT _ _ _
  have hH'ρ : ζ - ρ ∣ H'.eval ζ - H'.eval ρ := sub_dvd_eval_sub _ _ _
  obtain ⟨r2, hr2⟩ := hH'ρ
  have hcc : PowerSeries.constantCoeff (H'.eval ζ) = PowerSeries.constantCoeff (H'.eval ρ) := by
    have : H'.eval ζ = H'.eval ρ + e * r2 := by rw [he, ← hr2]; ring
    obtain ⟨t, ht⟩ := hXe
    rw [this, map_add, map_mul, ht, map_mul, PowerSeries.constantCoeff_X, zero_mul, zero_mul,
      add_zero]
  have e1 : PowerSeries.constantCoeff (H'.eval ζ) = D.getD 0 0 := by
    rw [hH', derivative_HS, valT_eval, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
      evalBT_getD Z L (derivYB H) 0 hL]
  have hD0 : D.getD 0 0 ≠ 0 := by rw [← e1, hcc]; exact hu
  -- `D Q ≡ V` modulo `T^L`
  have hDQ : X ^ L ∣ valT D * valT Q - valT V := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp only [valT, ← map_mul, map_sub, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeff_coe, hQ, sDivT]
    rw [← Polynomial.coe_mul, Polynomial.coeff_coe, coeff_mul_divTrunc V D hD0 L m hm,
      coeff_toPoly, sub_self]
  -- `H'(ζ) Q ≡ H(ζ)` modulo `T^L`
  have hV' : X ^ L ∣ valT V - (HS H).eval ζ := X_pow_dvd_evalBT _ _ _
  have hmain : X ^ L ∣ H'.eval ζ * valT Q - (HS H).eval ζ := by
    have : H'.eval ζ * valT Q - (HS H).eval ζ =
        -((valT D - H'.eval ζ) * valT Q) + (valT D * valT Q - valT V) + (valT V - (HS H).eval ζ) := by
      ring
    rw [this]
    exact dvd_add (dvd_add (dvd_neg.mpr (Dvd.dvd.mul_right hD' _)) hDQ) hV'
  -- Taylor expansion at `ρ`
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (HS H) ρ e
  have hζρ : ρ + e = ζ := by rw [he]; ring
  rw [hζρ, hρ, zero_add] at hk
  -- `H'(ζ) (e − Q) ≡ e² (r₂ − k)` modulo `T^L`
  have hkey : X ^ (min L (2 * s)) ∣ H'.eval ζ * (e - valT Q) := by
    have : H'.eval ζ * (e - valT Q) = e ^ 2 * (r2 - k) - (H'.eval ζ * valT Q - (HS H).eval ζ) := by
      rw [hk]
      have h2 : H'.eval ζ = H'.eval ρ + e * r2 := by rw [he, ← hr2]; ring
      rw [h2, hH']
      ring
    rw [this]
    refine dvd_sub ?_ ((pow_dvd_pow X (min_le_left _ _)).trans hmain)
    refine Dvd.dvd.mul_right ((pow_dvd_pow X (min_le_right _ _)).trans ?_) _
    rw [pow_mul', pow_two, pow_two]
    exact mul_dvd_mul hZ hZ
  have hEQ : X ^ (min L (2 * s)) ∣ e - valT Q := by
    have := X_pow_dvd_of_mul_unit (V := e) (V' := valT Q) (U := H'.eval ζ) (by rw [hcc]; exact hu)
      (by rw [mul_comm]; exact hkey)
    exact this
  -- the truncation
  have htr : X ^ L ∣ valT (newtonStep H L Z) - (ζ - valT Q) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp only [map_sub, hζ, valT, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
      coeff_toPoly, newtonStep, List.getD_eq_getElem _ _ (show m < ((List.range L).map _).length by
        simpa using hm), List.getElem_map, List.getElem_range]
    rw [hQ]; ring
  have : valT (newtonStep H L Z) - ρ = (valT (newtonStep H L Z) - (ζ - valT Q)) + (e - valT Q) := by
    rw [he]; ring
  rw [this]
  exact dvd_add ((pow_dvd_pow X (min_le_left _ _)).trans htr) hEQ

/-- **`k` Newton steps**: precision `min(L, 2ᵏ s)`. -/
theorem newtonT_approx (H : BPoly F) (L : ℕ) (ρ : PowerSeries F) (hρ : (HS H).eval ρ = 0)
    (hu : PowerSeries.constantCoeff ((derivative (HS H)).eval ρ) ≠ 0) :
    ∀ (k : ℕ) (Z : CPoly F) (s : ℕ), 1 ≤ s →
      (PowerSeries.X : PowerSeries F) ^ s ∣ valT Z - ρ →
      (PowerSeries.X : PowerSeries F) ^ (min L (2 ^ k * s)) ∣ valT (newtonT H L k Z) - ρ
  | 0, Z, s, _, hZ => by
    rw [pow_zero, one_mul]
    exact (pow_dvd_pow _ (min_le_right _ _)).trans hZ
  | k + 1, Z, s, hs, hZ => by
    rw [newtonT_succ]
    rcases Nat.eq_zero_or_pos L with hL | hL
    · rw [hL, Nat.zero_min, pow_zero]; exact one_dvd _
    have h1 := newton_step H L s Z ρ hρ hu hs hZ
    have h2 := newtonT_approx H L ρ hρ hu k (newtonStep H L Z) (min L (2 * s))
      (le_min hL (by omega)) h1
    refine (pow_dvd_pow _ ?_).trans h2
    rcases le_total L (2 * s) with h | h
    · rw [min_eq_left h]
      refine le_min (min_le_left _ _) (le_trans (min_le_left _ _) ?_)
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
    · rw [min_eq_right h, pow_succ, mul_assoc]

/-- **The Newton lift of a simple root** agrees with the root modulo `T^L`. -/
theorem newtonT_root (H : BPoly F) (L : ℕ) (Z : CPoly F) (ρ : PowerSeries F)
    (hρ : (HS H).eval ρ = 0)
    (hu : PowerSeries.constantCoeff ((derivative (HS H)).eval ρ) ≠ 0)
    (hZ : (PowerSeries.X : PowerSeries F) ∣ valT Z - ρ) :
    (PowerSeries.X : PowerSeries F) ^ L ∣ valT (newtonT H L (Nat.log2 L + 3) Z) - ρ := by
  have h := newtonT_approx H L ρ hρ hu (Nat.log2 L + 3) Z 1 le_rfl (by rw [pow_one]; exact hZ)
  have hL : L ≤ 2 ^ (Nat.log2 L + 3) * 1 := by
    have := Nat.lt_log2_self (n := L)
    rw [mul_one, pow_add]
    have : 2 ^ (L.log2 + 1) ≤ 2 ^ L.log2 * 2 ^ 3 := by rw [pow_succ]; omega
    omega
  rwa [min_eq_left hL] at h

/-- **Existence and computation of the simple root** through `y₀` (`H(0, y₀) = 0`,
`H_Y(0, y₀) ≠ 0`): Hensel's lemma gives the root `ρ`, and the Newton lift from `[y₀]` agrees
with it modulo `T^L`. -/
theorem exists_newtonT_root (H : BPoly F) (y₀ : F)
    (h0 : PowerSeries.constantCoeff ((HS H).eval (PowerSeries.C y₀)) = 0)
    (h1 : PowerSeries.constantCoeff ((derivative (HS H)).eval (PowerSeries.C y₀)) ≠ 0) :
    ∃ ρ : PowerSeries F, (HS H).eval ρ = 0 ∧ PowerSeries.constantCoeff ρ = y₀ ∧
      ∀ L, (PowerSeries.X : PowerSeries F) ^ L ∣ valT (newtonT H L (Nat.log2 L + 3) [y₀]) - ρ := by
  obtain ⟨ρ, hρ, hc⟩ := Puiseux.hensel_simple (HS H) (PowerSeries.C y₀) h0 h1
  rw [PowerSeries.constantCoeff_C] at hc
  have hu : PowerSeries.constantCoeff ((derivative (HS H)).eval ρ) ≠ 0 := by
    have hd : ρ - PowerSeries.C y₀ ∣ (derivative (HS H)).eval ρ -
        (derivative (HS H)).eval (PowerSeries.C y₀) := sub_dvd_eval_sub _ _ _
    obtain ⟨r, hr⟩ := hd
    have hX : PowerSeries.constantCoeff (ρ - PowerSeries.C y₀) = 0 := by
      rw [map_sub, hc, PowerSeries.constantCoeff_C, sub_self]
    have := congrArg PowerSeries.constantCoeff hr
    rw [map_sub, map_mul, hX, zero_mul, sub_eq_zero] at this
    rw [this]; exact h1
  refine ⟨ρ, hρ, hc, fun L ↦ newtonT_root H L [y₀] ρ hρ hu ?_⟩
  rw [PowerSeries.X_dvd_iff, map_sub, hc]
  simp [valT, toPoly]

end Newton

end Curves
