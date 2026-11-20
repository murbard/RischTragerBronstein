import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The derivation `d/dX` on Laurent series

Mathlib provides `LaurentSeries.derivative` as a linear map (the first Hasse derivative). We prove
the Leibniz rule (`derivative_mul`), by writing a Laurent series as `Xᵃ · F` with `F` a power
series (`single_order_mul_powerSeriesPart`) and using `PowerSeries.derivative`, and package it as
a `Derivation` (`LaurentSeries.derivation`).
-/

open HahnSeries PowerSeries

namespace LaurentSeries

variable {K : Type*} [Field K]

lemma derivative_coeff (f : K⸨X⸩) (n : ℤ) :
    (derivative K f).coeff n = ((n + 1 : ℤ) : K) * f.coeff (n + 1) := by
  rw [derivative_apply, hasseDeriv_coeff, Ring.choose_one_right, zsmul_eq_mul]
  push_cast; ring

lemma coeff_ofPS (H : K⟦X⟧) (m : ℤ) :
    (ofPowerSeries ℤ K H).coeff m = if 0 ≤ m then PowerSeries.coeff m.toNat H else 0 := by
  split_ifs with hm
  · rw [← Int.toNat_of_nonneg hm, ofPowerSeries_apply_coeff, Int.toNat_natCast]
  · rw [ofPowerSeries_apply, embDomain_notin_range]
    simp only [Nat.castOrderEmbedding_apply, Set.mem_range, not_exists]
    intro k hk; omega

lemma coeff_single_mul (c : ℤ) (x : K⸨X⸩) (n : ℤ) :
    (single c (1 : K) * x).coeff n = x.coeff (n - c) := by
  rw [show n = (n - c) + c by ring, coeff_single_mul_add, one_mul, add_sub_cancel_right]

/-- `d/dX (Xᶜ H) = Xᶜ H′ + c Xᶜ⁻¹ H`. -/
lemma derivative_single_mul_ofPS (c : ℤ) (H : K⟦X⟧) :
    derivative K (single c (1 : K) * ofPowerSeries ℤ K H) =
      single c (1 : K) * ofPowerSeries ℤ K (PowerSeries.derivative H) +
        (c : K) • (single (c - 1) (1 : K) * ofPowerSeries ℤ K H) := by
  ext n
  rw [derivative_coeff, coeff_add, HahnSeries.coeff_smul, coeff_single_mul, coeff_single_mul,
    coeff_single_mul, coeff_ofPS, coeff_ofPS, coeff_ofPS, smul_eq_mul]
  rcases lt_trichotomy (n - c) (-1) with h | h | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    have h0 : (n + 1 - c).toNat = 0 := by omega
    have h1 : n - (c - 1) = n + 1 - c := by ring
    rw [h1, h0]
    have hn : (n : K) + 1 = c := by
      have : n + 1 = c := by omega
      rw [← this]; push_cast; ring
    push_cast; rw [hn]; ring
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), PowerSeries.coeff_derivative]
    have h1 : n - (c - 1) = n + 1 - c := by ring
    have h2 : (n + 1 - c).toNat = (n - c).toNat + 1 := by omega
    rw [h1, h2]
    have h3 : (((n - c).toNat : ℕ) : K) = (n : K) - c := by
      have h' : ((n - c).toNat : ℤ) = n - c := Int.toNat_of_nonneg (by omega)
      have := congrArg (fun z : ℤ ↦ (z : K)) h'
      push_cast at this
      exact this
    push_cast; rw [h3]; ring

/-- **The Leibniz rule for `d/dX` on Laurent series.** -/
theorem derivative_mul (f g : K⸨X⸩) :
    derivative K (f * g) = derivative K f * g + f * derivative K g := by
  rw [← single_order_mul_powerSeriesPart f, ← single_order_mul_powerSeriesPart g]
  set a := f.order
  set b := g.order
  set F := f.powerSeriesPart
  set G := g.powerSeriesPart
  have e : single a (1 : K) * ofPowerSeries ℤ K F * (single b (1 : K) * ofPowerSeries ℤ K G) =
      single (a + b) (1 : K) * ofPowerSeries ℤ K (F * G) := by
    rw [map_mul, show single (a + b) (1 : K) = single a (1 : K) * single b 1 by
      rw [single_mul_single, one_mul]]
    ring
  have e1 : single a (1 : K) * single b 1 = single (a + b) 1 := by rw [single_mul_single, one_mul]
  have ea : single (a - 1) (1 : K) * single b 1 = single (a + b - 1) 1 := by
    rw [single_mul_single, one_mul]; ring_nf
  have eb : single a (1 : K) * single (b - 1) 1 = single (a + b - 1) 1 := by
    rw [single_mul_single, one_mul]; ring_nf
  change derivative K (single a (1 : K) * ofPowerSeries ℤ K F *
    (single b (1 : K) * ofPowerSeries ℤ K G)) = _
  rw [e, derivative_single_mul_ofPS, derivative_single_mul_ofPS, derivative_single_mul_ofPS,
    Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
  simp only [← HahnSeries.C_mul_eq_smul]
  rw [show ((a + b : ℤ) : K) = (a : K) + b by push_cast; ring, map_add]
  simp only [map_mul]
  linear_combination -(HahnSeries.C (a : K) * ofPowerSeries ℤ K F * ofPowerSeries ℤ K G) * ea -
    (HahnSeries.C (b : K) * ofPowerSeries ℤ K F * ofPowerSeries ℤ K G) * eb -
    (ofPowerSeries ℤ K (PowerSeries.derivative F) * ofPowerSeries ℤ K G +
      ofPowerSeries ℤ K F * ofPowerSeries ℤ K (PowerSeries.derivative G)) * e1

lemma algebraMap_mul_coeff (c : K) (f : K⸨X⸩) (m : ℤ) :
    (algebraMap K K⸨X⸩ c * f).coeff m = c * f.coeff m := by
  rw [HahnSeries.algebraMap_apply']
  change ((ofPowerSeries ℤ K) (PowerSeries.C c) * f).coeff m = _
  rw [ofPowerSeries_C, C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

lemma derivative_one : derivative K (1 : K⸨X⸩) = 0 := by
  ext n
  rw [derivative_coeff, HahnSeries.coeff_zero, show (1 : K⸨X⸩) = single (0 : ℤ) (1 : K) from rfl,
    HahnSeries.coeff_single]
  split_ifs with h
  · have : n = -1 := by omega
    subst this; simp
  · rw [mul_zero]

/-- **`d/dX` as a derivation of Laurent series.** -/
noncomputable def derivation : Derivation K K⸨X⸩ K⸨X⸩ where
  toFun f := derivative K f
  map_add' f g := map_add (derivative K) f g
  map_smul' c f := by
    simp only [RingHom.id_apply]
    ext n
    rw [Algebra.smul_def, derivative_coeff, algebraMap_mul_coeff]
    first
      | (rw [HahnSeries.coeff_smul, derivative_coeff, smul_eq_mul]; ring)
      | (rw [Algebra.smul_def, algebraMap_mul_coeff, derivative_coeff]; ring)
  map_one_eq_zero' := derivative_one
  leibniz' f g := by
    change derivative K (f * g) = f • derivative K g + g • derivative K f
    rw [derivative_mul, smul_eq_mul, smul_eq_mul]; ring

lemma derivation_apply (f : K⸨X⸩) : derivation f = derivative K f := rfl

end LaurentSeries
