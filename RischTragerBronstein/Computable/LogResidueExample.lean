import RischTragerBronstein.Computable.LogResidueDecision

/-!
# Simple poles in `log x`: two worked examples, fully verified

* `∫ dx / (x (log² x + 1))` is elementary (`= arctan (log x)`; the residues `± 1 / 2i` are
  constants, and no algebraic numbers are needed to see it).
* `∫ dx / log x` is **not** elementary (the logarithmic integral): the residue `x` is not a constant.

Both follow from `logResidue_decides` by kernel computation of `residueCheck`.
-/

open Polynomial Differential

namespace Tower

theorem check_arctan_log :
    GPoly.residueCheck ops₁ [invX] [invX] [ops₁.one, ops₁.zero, ops₁.one] = true := by
  decide +kernel

theorem check_li : GPoly.residueCheck ops₁ [invX] [ops₁.one] [ops₁.zero, ops₁.one] = false := by
  decide +kernel

/-- **`∫ dx / log x` is not elementary** (in `ℚ(x)(log x)`, via the executable residue test). -/
theorem li_not_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (GPoly.toPoly M₁ [invX])
    ¬HasElementaryIntegral (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
        (GPoly.toPoly M₁ [ops₁.one]) /
      algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (GPoly.toPoly M₁ [ops₁.zero, ops₁.one])) := by
  let _ : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
  have hs : GPoly.toPoly M₁ [ops₁.zero, ops₁.one] = X := by
    simp [GPoly.toPoly, M₁.sem_zero, M₁.sem_one]
  have hb : GPoly.toPoly M₁ [ops₁.one] = 1 := by
    simp [GPoly.toPoly, M₁.sem_one]
  have := logResidue_decides [ops₁.one] [ops₁.zero, ops₁.one]
    (by rw [hs]; exact (irreducible_X).squarefree)
    (by rw [hs, hb, degree_one, degree_X]; exact zero_lt_one)
  rw [this, check_li]
  exact Bool.noConfusion

/-- **`∫ dx / (x (log² x + 1))` is elementary**, certified by the residue test. -/
theorem arctan_log_elementary :
    letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
    letI : Differential (RatFunc (RatFunc ℚ)) := ratFuncOfDeriv (GPoly.toPoly M₁ [invX])
    HasElementaryIntegral (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
        (GPoly.toPoly M₁ [invX]) /
      algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
        (GPoly.toPoly M₁ [ops₁.one, ops₁.zero, ops₁.one])) := by
  let _ : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
  have hs : GPoly.toPoly M₁ [ops₁.one, ops₁.zero, ops₁.one] = X ^ 2 + 1 := by
    simp [GPoly.toPoly, M₁.sem_zero, M₁.sem_one]
    ring
  have hb : GPoly.toPoly M₁ [invX] = C (M₁.sem invX) := by
    simp [GPoly.toPoly]
  have hsep : (X ^ 2 + 1 : (RatFunc ℚ)[X]).Separable := by
    rw [separable_def']
    refine ⟨1, -C (1 / 2 : RatFunc ℚ) * X, ?_⟩
    simp only [derivative_add, derivative_X_pow, derivative_one, Nat.cast_ofNat, C_ofNat]
    have : (C (1 / 2 : RatFunc ℚ) : (RatFunc ℚ)[X]) * 2 = 1 := by
      rw [← C_ofNat, ← C_mul]
      norm_num
    linear_combination (-X ^ 2) * this
  have := logResidue_decides [invX] [ops₁.one, ops₁.zero, ops₁.one]
    (by rw [hs]; exact hsep.squarefree)
    (by
      rw [hs, hb]
      refine lt_of_le_of_lt degree_C_le ?_
      have : (X ^ 2 + 1 : (RatFunc ℚ)[X]) = X ^ 2 + C 1 := by rw [C_1]
      rw [this, degree_X_pow_add_C (by norm_num)]
      exact_mod_cast zero_lt_two)
  rw [this, check_arctan_log]

end Tower
