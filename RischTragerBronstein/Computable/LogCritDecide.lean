import RischTragerBronstein.Computable.LogTimes
import RischTragerBronstein.Computable.EuclidDegree

/-!
# The criterion for `∫ f log x` is decidable

`CPoly.logCrit r s : Bool` decides `LogCrit (toPoly r) (toPoly s)` (`logCrit_iff`): either `r = 0`,
or `x ∣ s` and `r` is a constant multiple of `s / x`. The constant, if it exists, is the quotient of
the leading coefficients.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

/-- Executable form of `LogCrit`. -/
def logCrit (r s : CPoly R) : Bool :=
  isZero r ||
    (decide (s.getD 0 0 = 0) &&
      beq r (smul (lead (trim r) / lead (trim s.tail)) s.tail))

lemma toPoly_eq_X_mul_tail {s : CPoly R} (h : s.getD 0 0 = 0) :
    toPoly s = X * toPoly s.tail := by
  cases s with
  | nil => simp
  | cons a s' =>
    have : a = 0 := by simpa using h
    simp [this]

lemma leadingCoeff_toPoly {q : CPoly R} (hq : toPoly q ≠ 0) :
    (toPoly q).leadingCoeff = lead (trim q) := by
  have hne : trim q ≠ [] := fun h ↦ hq ((trim_eq_nil_iff q).mp h)
  obtain ⟨hdeg, hlc, -⟩ := natDegree_toPoly_of_trim_ne_nil hne
  rw [leadingCoeff, hdeg, hlc]

theorem logCrit_iff (r s : CPoly R) : logCrit r s = true ↔ LogCrit (toPoly r) (toPoly s) := by
  simp only [logCrit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, isZero_iff, beq_iff,
    toPoly_smul]
  constructor
  · rintro (h0 | ⟨hs, hr⟩)
    · exact Or.inr h0
    · exact Or.inl ⟨toPoly s.tail, _, toPoly_eq_X_mul_tail hs, hr⟩
  · rintro (⟨s', c, hs, hr⟩ | h0)
    · by_cases hr0 : toPoly r = 0
      · exact Or.inl hr0
      right
      have hs0 : s.getD 0 0 = 0 := by
        have := congrArg (fun P : R[X] ↦ P.coeff 0) hs
        simpa [coeff_toPoly] using this
      have htail : toPoly s.tail = s' :=
        mul_left_cancel₀ X_ne_zero ((toPoly_eq_X_mul_tail hs0).symm.trans hs)
      refine ⟨hs0, ?_⟩
      have hs'0 : s' ≠ 0 := fun h ↦ hr0 (by rw [hr, h, mul_zero])
      have hc0 : c ≠ 0 := fun h ↦ hr0 (by rw [hr, h, C_0, zero_mul])
      have hlead : lead (trim r) / lead (trim s.tail) = c := by
        rw [← leadingCoeff_toPoly hr0, ← leadingCoeff_toPoly (htail ▸ hs'0), htail, hr,
          leadingCoeff_mul, leadingCoeff_C]
        field_simp [leadingCoeff_ne_zero.mpr hs'0]
      rw [hlead, htail, hr]
    · exact Or.inl h0

instance (r s : CPoly R) : Decidable (LogCrit (toPoly r) (toPoly s)) :=
  decidable_of_iff _ (logCrit_iff r s)

end CPoly

-- ∫ log x / (x + 1): criterion fails (not elementary).  ∫ log x / x: holds (= (log x)² / 2).
#eval CPoly.logCrit ([1] : CPoly ℚ) [1, 1]
#eval CPoly.logCrit ([1] : CPoly ℚ) [0, 1]
