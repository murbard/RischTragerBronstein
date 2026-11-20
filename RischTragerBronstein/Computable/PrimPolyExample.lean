import RischTragerBronstein.Computable.PrimPolyPositive

/-!
# Polynomials in `log x`: the loop, run

`t = log x`, `η = 1 / x`. Coefficients `fⱼ = Aⱼ / Dⱼ ∈ ℚ(x)`.

* `∫ log² x dx`: the loop succeeds (`x log² x - 2 x log x + 2 x`).
* `∫ log² x / (x + 1) dx`: the loop fails at the top level — `1 / (x + 1) - c / x` has no rational
  integral for any constant `c` — so by `not_hasElementaryIntegral_primPoly` there is no elementary
  integral.
-/

namespace CPoly.PrimPolyExample

/-- `η = 1 / x`. -/
def En : CPoly ℚ := [1]
/-- `η = 1 / x`. -/
def Ed : CPoly ℚ := [0, 1]
/-- Hermite data of `η`. -/
def Iη : RationalIntegral ℚ := integrateRational En Ed

/-- `log² x`. -/
def A₁ : ℕ → CPoly ℚ := fun j ↦ if j = 2 then [1] else []
/-- All denominators `1`. -/
def D₁ : ℕ → CPoly ℚ := fun _ ↦ [1]

/-- `log² x / (x + 1)`. -/
def D₂ : ℕ → CPoly ℚ := fun j ↦ if j = 2 then [1, 1] else [1]

#eval rationalCheck En Ed Iη
#eval isZero Iη.r
#eval primLoop En Ed Iη A₁ D₁ 2 ([], [1])
#eval primLoop En Ed Iη A₁ D₂ 2 ([], [1])

theorem check_η : rationalCheck En Ed Iη = true := by decide +kernel

theorem η_not_derivative : isZero Iη.r = false := by decide +kernel

theorem loop_log_sq : (primLoop En Ed Iη A₁ D₁ 2 ([], [1])).isSome = true := by decide +kernel

theorem loop_log_sq_div : primLoop En Ed Iη A₁ D₂ 2 ([], [1]) = none := by decide +kernel

end CPoly.PrimPolyExample
