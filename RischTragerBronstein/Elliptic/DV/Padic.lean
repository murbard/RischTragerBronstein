import RischTragerBronstein.Elliptic.DV.Torsion
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# The `p`-adic valuation on `ℚ_p` as a `DVal`

`padicDVal p : DVal ℚ_[p] p` (`v = Padic.valuation`, `v(p) = 1`). With `torsion_integral_y`:
torsion points of `y² = x³ + ax² + bx + c` over `ℚ_p` (hence over any number field embedded in
`ℚ_p`) have `p`-integral `y`.
-/

namespace EllDV

variable (p : ℕ) [hp : Fact p.Prime]

lemma padic_valuation_neg_one : Padic.valuation (-1 : ℚ_[p]) = 0 := by
  have h := Padic.valuation_mul (p := p) (x := -1) (y := -1) (by norm_num) (by norm_num)
  rw [neg_one_mul, neg_neg, Padic.valuation_one] at h
  omega

/-- **The `p`-adic valuation.** -/
noncomputable def padicDVal : DVal ℚ_[p] p where
  v := Padic.valuation
  mul hx hy := Padic.valuation_mul hx hy
  add _ _ hxy := Padic.le_valuation_add hxy
  neg x := by
    by_cases hx : x = 0
    · simp [hx]
    rw [show -x = -1 * x by ring, Padic.valuation_mul (by norm_num) hx, padic_valuation_neg_one]
    ring
  intCast z _ := by
    rw [Padic.valuation_intCast]; exact_mod_cast Nat.zero_le _
  natCast_unit n hn := by
    rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd hn]; rfl
  self := Padic.valuation_p
  one := Padic.valuation_one

end EllDV
