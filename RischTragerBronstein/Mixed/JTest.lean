import RischTragerBronstein.Mixed.ManinComplete
import RischTragerBronstein.Mixed.EllIsoClassify

/-!
# An executable test for constant `j`

`jConstB Ac Bc`: `A = 0`, `B = 0`, or `A³ = r B²` with `r` the ratio of leading coefficients.
**`jConstB_true`**: a passing test gives the constant-`j` alternative of `const_j_classify`;
**`bt_ne_of_jConstB`**: a failing test gives `β ≠ 0` (non-constant `j`, the Manin route), because
`3A'B − 2AB' = 0` would make `A³/B²` a constant of `d/dX` (`const_of_dX`).
-/

open Polynomial CPoly

namespace FFHeight

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

noncomputable local instance (priority := 2000) intAlgRF'' : Algebra ℤ (RatFunc K) :=
  Ring.toIntAlgebra _

/-- **The constant-`j` test.** -/
def jConstB (Ac Bc : CPoly K) : Bool :=
  CPoly.isZero Ac || CPoly.isZero Bc ||
    CPoly.isZero (CPoly.sub (CPoly.mul Ac (CPoly.mul Ac Ac))
      (CPoly.smul (lead (trim Ac) ^ 3 / lead (trim Bc) ^ 2) (CPoly.mul Bc Bc)))

theorem jConstB_true {Ac Bc : CPoly K} (h : jConstB Ac Bc = true) :
    toPoly Ac = 0 ∨ toPoly Bc = 0 ∨ ∃ r : K, toPoly Ac ^ 3 = C r * toPoly Bc ^ 2 := by
  simp only [jConstB, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact Or.inl ((CPoly.isZero_iff _).mp h)
  · exact Or.inr (Or.inl ((CPoly.isZero_iff _).mp h))
  · refine Or.inr (Or.inr ⟨lead (trim Ac) ^ 3 / lead (trim Bc) ^ 2, ?_⟩)
    have := (CPoly.isZero_iff _).mp h
    simp only [CPoly.toPoly_sub, CPoly.toPoly_mul, CPoly.toPoly_smul] at this
    linear_combination this

/-- **A failing test means non-constant `j`.** -/
theorem bt_ne_of_jConstB {Ac Bc : CPoly K} (h : jConstB Ac Bc = false)
    (hΔ : 4 * toPoly Ac ^ 3 + 27 * toPoly Bc ^ 2 ≠ 0) :
    Manin.bt Manin.dX (ι (toPoly Ac)) (ι (toPoly Bc)) ≠ 0 := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  simp only [jConstB, Bool.or_eq_false_iff] at h
  obtain ⟨⟨hA, hB⟩, hr⟩ := h
  set A := toPoly Ac
  set B := toPoly Bc
  have hA0 : A ≠ 0 := fun h0 ↦ by rw [← CPoly.isZero_iff] at h0; rw [h0] at hA; exact absurd hA (by decide)
  have hB0 : B ≠ 0 := fun h0 ↦ by rw [← CPoly.isZero_iff] at h0; rw [h0] at hB; exact absurd hB (by decide)
  have hιA : ι A ≠ 0 := (map_ne_zero_iff _ hinj).mpr hA0
  have hιB : ι B ≠ 0 := (map_ne_zero_iff _ hinj).mpr hB0
  have hZ : (4 * ι A ^ 3 + 27 * ι B ^ 2 : RatFunc K) ≠ 0 := by
    intro h0; apply hΔ; apply hinj; simp only [map_add, map_mul, map_pow, map_ofNat, map_zero]; exact h0
  intro hbt
  simp only [Manin.bt, Manin.beZ, Manin.ZZ, Manin.dX_ι] at hbt
  have h1 : 9 * ι (derivative A) * ι B - 6 * ι A * ι (derivative B) = 0 := by
    rcases div_eq_zero_iff.mp hbt with h | h
    · exact h
    · exact absurd h (mul_ne_zero (by norm_num) hZ)
  -- `A³/B²` is a constant
  have hd : Manin.dX (ι A ^ 3 / ι B ^ 2) = 0 := by
    rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    simp only [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Manin.dX_ι]
    push_cast
    linear_combination ((ι B ^ 2)⁻¹ ^ 2 * (ι A ^ 2 * ι B / 3)) * h1
  obtain ⟨r, hr'⟩ := Manin.const_of_dX _ hd
  have hrel : A ^ 3 = C r * B ^ 2 := by
    apply hinj
    rw [map_pow, map_mul, map_pow, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, ← hr']
    field_simp
  -- `r` is the ratio of leading coefficients
  have hlc : (A ^ 3).leadingCoeff = (C r * B ^ 2).leadingCoeff := by rw [hrel]
  rw [leadingCoeff_pow, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow] at hlc
  have hlB : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB0
  have hrv : r = lead (trim Ac) ^ 3 / lead (trim Bc) ^ 2 := by
    rw [RFC.lead_trim_eq, RFC.lead_trim_eq, hlc]
    exact (mul_div_cancel_right₀ r (pow_ne_zero 2 hlB)).symm
  apply Bool.false_ne_true
  rw [← hr, CPoly.isZero_iff]
  simp only [CPoly.toPoly_sub, CPoly.toPoly_mul, CPoly.toPoly_smul]
  rw [← hrv]
  linear_combination hrel

end FFHeight

