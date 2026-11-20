import RischTragerBronstein.Computable.EuclidDegree
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# A computable resultant

`resC a b` computes `Res(a, b)` (Mathlib's `Polynomial.resultant`, i.e. the Sylvester determinant
with the true degrees) by the Euclidean recursion
`Res(a, b) = (-1)^{n(m - m')} lc(b)^{m - m'} Res(a mod b, b)`, `Res(a, b) = (-1)^{mn} Res(b, a)`.
`resC_eq`: it agrees with `Polynomial.resultant`.
-/

open Polynomial

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R]

/-- The degree (of the trimmed list). -/
def degT (p : CPoly R) : ℕ := (trim p).length - 1

/-- The leading coefficient. -/
def lcT (p : CPoly R) : R := lead (trim p)

/-- The Euclidean resultant, with fuel. -/
def resAux : ℕ → CPoly R → CPoly R → R
  | 0, _, _ => 0
  | fuel + 1, a, b =>
    if isZero b then (if degT a = 0 then 1 else 0)
    else if degT b = 0 then lcT b ^ degT a
    else if degT a < degT b then (-1) ^ (degT a * degT b) * resAux fuel b a
    else
      if isZero (divMod a b).2 then 0
      else (-1) ^ (degT b * (degT a - degT (divMod a b).2)) *
        lcT b ^ (degT a - degT (divMod a b).2) * resAux fuel (divMod a b).2 b

/-- **The resultant.** -/
def resC (a b : CPoly R) : R := resAux (2 * (degT a + degT b) + 2) a b

lemma degT_eq (p : CPoly R) : degT p = (toPoly p).natDegree := by
  by_cases h : toPoly p = 0
  · have := (trim_eq_nil_iff p).mpr h
    simp [degT, this, h]
  · have htr : trim p ≠ [] := fun h0 ↦ h ((trim_eq_nil_iff p).mp h0)
    rw [degT, length_trim htr]; simp

lemma lcT_eq (p : CPoly R) : lcT p = (toPoly p).leadingCoeff := by
  by_cases h : toPoly p = 0
  · have := (trim_eq_nil_iff p).mpr h
    simp [lcT, this, h, lead]
  · have htr : trim p ≠ [] := fun h0 ↦ h ((trim_eq_nil_iff p).mp h0)
    have hl := length_trim htr
    rw [leadingCoeff, ← toPoly_trim, coeff_toPoly, lcT, lead, List.getLastD_eq_getLast?,
      List.getLast?_eq_getElem?, hl]
    simp [List.getD_eq_getElem?_getD]

theorem resAux_spec : ∀ (fuel : ℕ) (a b : CPoly R),
    2 * (degT a + degT b) + (if degT a < degT b then 1 else 0) < fuel →
    resAux fuel a b = resultant (toPoly a) (toPoly b)
  | 0, a, b, h => by omega
  | fuel + 1, a, b, h => by
    simp only [degT_eq] at h
    unfold resAux
    simp only [degT_eq, lcT_eq]
    split_ifs with hb hm hn hmn hr
    · rw [(isZero_iff _).mp hb, resultant_zero_right, hm]; simp
    · rw [(isZero_iff _).mp hb, resultant_zero_right]
      simp [zero_pow hm]
    · -- `b` constant
      have hb0 : toPoly b ≠ 0 := fun h0 ↦ hb ((isZero_iff _).mpr h0)
      conv_rhs => rw [eq_C_of_natDegree_eq_zero hn]
      rw [natDegree_C, resultant_C_zero_right, leadingCoeff, hn]
    · rw [resAux_spec fuel b a (by simp only [degT_eq]; split_ifs at h ⊢ <;> omega),
        resultant_comm (toPoly a)]
    · -- `r = 0`
      have hsp := divMod_spec a b
      rw [(isZero_iff _).mp hr, add_zero] at hsp
      have hb0 : toPoly b ≠ 0 := fun h0 ↦ hb ((isZero_iff _).mpr h0)
      have hq : (toPoly (divMod a b).1).natDegree + (toPoly b).natDegree ≤ (toPoly a).natDegree := by
        by_cases hq0 : toPoly (divMod a b).1 = 0
        · rw [hq0, natDegree_zero]; omega
        · rw [hsp, natDegree_mul hq0 hb0]
      rw [show toPoly a = 0 + toPoly b * toPoly (divMod a b).1 by rw [hsp]; ring]
      rw [show (0 + toPoly b * toPoly (divMod a b).1).natDegree = (toPoly a).natDegree by
        rw [← show toPoly a = 0 + toPoly b * toPoly (divMod a b).1 by rw [hsp]; ring]]
      rw [resultant_add_mul_left _ _ _ _ _ (by rw [mul_comm] at hsp; omega) le_rfl]
      rw [resultant_zero_left, zero_pow (by omega), zero_mul]
    · -- the Euclidean step
      set q := (divMod a b).1
      set r := (divMod a b).2
      have hsp : toPoly a = toPoly q * toPoly b + toPoly r := divMod_spec a b
      have hb0 : toPoly b ≠ 0 := fun h0 ↦ hb ((isZero_iff _).mpr h0)
      have hr0 : toPoly r ≠ 0 := fun h0 ↦ hr ((isZero_iff _).mpr h0)
      have hrd : (toPoly r).degree < (toPoly b).degree := divMod_degree_lt a b hb0
      have hrn : (toPoly r).natDegree < (toPoly b).natDegree :=
        natDegree_lt_natDegree hr0 hrd
      have hq : (toPoly q).natDegree + (toPoly b).natDegree ≤ (toPoly a).natDegree := by
        by_cases hq0 : toPoly q = 0
        · rw [hq0, natDegree_zero]; omega
        · have hqb : (toPoly q * toPoly b).natDegree = (toPoly q).natDegree + (toPoly b).natDegree :=
            natDegree_mul hq0 hb0
          have : (toPoly a).natDegree = (toPoly q * toPoly b).natDegree := by
            rw [hsp]; exact natDegree_add_eq_left_of_natDegree_lt (by rw [hqb]; omega)
          omega
      have e1 : resultant (toPoly a) (toPoly b) =
          resultant (toPoly r) (toPoly b) (toPoly a).natDegree (toPoly b).natDegree := by
        conv_lhs => rw [show toPoly a = toPoly r + toPoly b * toPoly q by rw [hsp]; ring]
        rw [show (toPoly r + toPoly b * toPoly q).natDegree = (toPoly a).natDegree by
          rw [← show toPoly a = toPoly r + toPoly b * toPoly q by rw [hsp]; ring]]
        exact resultant_add_mul_left _ _ _ _ _ (by omega) le_rfl
      have e2 := resultant_add_left_deg (toPoly r) (toPoly b) ((toPoly r).natDegree)
        (toPoly b).natDegree ((toPoly a).natDegree - (toPoly r).natDegree) le_rfl
      rw [show (toPoly r).natDegree + ((toPoly a).natDegree - (toPoly r).natDegree) =
        (toPoly a).natDegree by omega] at e2
      rw [e1, e2, resAux_spec fuel r b (by simp only [degT_eq]; split_ifs at h ⊢ <;> omega)]
      rfl

/-- **`resC` computes the resultant.** -/
theorem resC_eq (a b : CPoly R) : resC a b = resultant (toPoly a) (toPoly b) :=
  resAux_spec _ a b (by split_ifs <;> omega)

end CPoly
