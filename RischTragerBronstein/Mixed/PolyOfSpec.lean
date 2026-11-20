import RischTragerBronstein.Mixed.KXMWDecideS

/-!
# Exactness of the polynomial read-off `polyOf`

The Mordell–Weil searches read the short-model coefficients `A, B` off normalized fractions by
`polyOf` (level `0`) / `polyOfS` (levels `m + 1`): numerator of the reduced fraction, divided by the
head of its denominator. **`polyOfG_spec`**: when the value of the fraction is a polynomial `p`,
the read-off is exactly `p` (the reduced denominator is coprime to `p ·` itself, hence a unit).
-/

open Polynomial

namespace FFHeight

variable {K : Type*} [Field K] [DecidableEq K]

local notation "ι" => algebraMap K[X] (RatFunc K)

/-- The generic read-off (`polyOf`, `polyOfS` are instances). -/
def polyOfG (f : Fr K) : CPoly K :=
  (CPoly.trim (Fr.norm f).1).map (· / (CPoly.trim (Fr.norm f).2).headD 1)

theorem headD_coeff (l : CPoly K) (d : K) (hl : l ≠ []) : l.headD d = (CPoly.toPoly l).coeff 0 := by
  rw [CPoly.coeff_toPoly]
  cases l with
  | nil => exact absurd rfl hl
  | cons a l => rfl

/-- **The read-off is exact on polynomial values.** -/
theorem polyOfG_spec (f : Fr K) (hf : Fr.ok f) (p : K[X]) (hv : Fr.val f = ι p) :
    CPoly.toPoly (polyOfG f) = p := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hok : Fr.ok (Fr.norm f) := Fr.ok_norm hf
  have hcop := reduce_coprime f.1 f.2 hf
  change IsCoprime (CPoly.toPoly (Fr.norm f).1) (CPoly.toPoly (Fr.norm f).2) at hcop
  set a := CPoly.toPoly (Fr.norm f).1
  set b := CPoly.toPoly (Fr.norm f).2
  have hb : b ≠ 0 := hok
  have hab : a = p * b := by
    have hv' := hv
    rw [← Fr.val_norm hf] at hv'
    have : ι a / ι b = ι p := hv'
    rw [div_eq_iff (Fr.ι_ne hb), ← map_mul] at this
    exact hinj this
  have hbu : IsUnit b := by
    rw [hab] at hcop
    exact IsCoprime.isUnit_of_dvd' hcop (dvd_mul_left _ _) dvd_rfl
  obtain ⟨c, hc, hbC⟩ := Polynomial.isUnit_iff.mp hbu
  have hc0 : c ≠ 0 := hc.ne_zero
  have htr : CPoly.trim (Fr.norm f).2 ≠ [] := by
    intro h0; apply hb
    show CPoly.toPoly (Fr.norm f).2 = 0
    rw [← CPoly.toPoly_trim, h0]; rfl
  have hhead : (CPoly.trim (Fr.norm f).2).headD 1 = c := by
    rw [headD_coeff _ _ htr, CPoly.toPoly_trim]
    show b.coeff 0 = c
    rw [← hbC, coeff_C_zero]
  have hmap : (CPoly.trim (Fr.norm f).1).map (· / c) = CPoly.smul c⁻¹ (CPoly.trim (Fr.norm f).1) := by
    unfold CPoly.smul
    exact List.map_congr_left fun x _ ↦ by rw [div_eq_mul_inv, mul_comm]
  unfold polyOfG
  rw [hhead, hmap, CPoly.toPoly_smul, CPoly.toPoly_trim]
  show C c⁻¹ * a = p
  rw [hab, ← hbC, mul_comm p, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc0, C_1, one_mul]

end FFHeight

/-- `polyOfS` is the generic read-off. -/
theorem polyOfS_eq_polyOfG (Fc : Sup.BPoly ℚ) [Fact (Irreducible (CPoly.toPoly (Curves.MT.fKc Fc)))] (m : ℕ) (f : FFHeight.Fr (Curves.MT.KF Fc m)) : Curves.MT.polyOfS Fc m f = FFHeight.polyOfG f := rfl
