import RischTragerBronstein.Computable.LogCritDecide
import RischTragerBronstein.Rational.RationalPart

/-!
# Executable limited integration over `R(x)`

`CPoly.limitedCrit rf sf rη sη : Option R` decides whether there is a constant `c` with
`rf * sη = c * rη * sf`, and returns it. By `Differential.limited_integral_iff`, for Hermite data
`f = g_f′ + rf / sf`, `η = g_η′ + rη / sη` this is exactly the question whether `f - c η` has a
rational antiderivative for some constant `c`.

* `limitedCrit_sound`:    `limitedCrit … = some c  →  rf * sη = c * rη * sf`;
* `limitedCrit_complete`: `limitedCrit … = none    →  no such `c` exists`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

/-- Find the constant `c` with `rf * sη = c * rη * sf`, if there is one. -/
def limitedCrit (rf sf rη sη : CPoly R) : Option R :=
  let L := mul rf sη
  let Rr := mul rη sf
  if isZero Rr then (if isZero L then some 0 else none)
  else
    let c := lead (trim L) / lead (trim Rr)
    if beq L (smul c Rr) then some c else none

theorem limitedCrit_sound {rf sf rη sη : CPoly R} {c : R}
    (h : limitedCrit rf sf rη sη = some c) :
    toPoly rf * toPoly sη = C c * toPoly rη * toPoly sf := by
  simp only [limitedCrit] at h
  split_ifs at h with h1 h2 h3
  · have hR := (isZero_iff _).mp h1
    have hL := (isZero_iff _).mp h2
    rw [toPoly_mul] at hR hL
    rw [hL, mul_assoc, hR, mul_zero]
  · have := (beq_iff _ _).mp h3
    rw [toPoly_mul, toPoly_smul, toPoly_mul, Option.some.inj h] at this
    rw [this]; ring

theorem limitedCrit_complete {rf sf rη sη : CPoly R} (h : limitedCrit rf sf rη sη = none) :
    ¬∃ c : R, toPoly rf * toPoly sη = C c * toPoly rη * toPoly sf := by
  rintro ⟨c, hc⟩
  simp only [limitedCrit] at h
  split_ifs at h with h1 h2 h3
  · -- `rη sf = 0` but `rf sη ≠ 0`
    have hR := (isZero_iff _).mp h1
    rw [toPoly_mul] at hR
    refine h2 ((isZero_iff _).mpr ?_)
    rw [toPoly_mul, hc, mul_assoc, hR, mul_zero]
  · -- `rη sf ≠ 0`: the constant is forced to be the ratio of leading coefficients
    have hR0 : toPoly (mul rη sf) ≠ 0 := fun h0 ↦ h1 ((isZero_iff _).mpr h0)
    refine h3 ((beq_iff _ _).mpr ?_)
    have hL : toPoly (mul rf sη) = C c * toPoly (mul rη sf) := by
      rw [toPoly_mul, toPoly_mul, hc]; ring
    rw [toPoly_smul]
    by_cases hc0 : c = 0
    · have hL0 : toPoly (mul rf sη) = 0 := by rw [hL, hc0, C_0, zero_mul]
      have : trim (mul rf sη) = [] := (trim_eq_nil_iff _).mpr hL0
      rw [this, hL0]
      simp [lead]
    · have hLne : toPoly (mul rf sη) ≠ 0 := by
        rw [hL]; exact mul_ne_zero (C_ne_zero.mpr hc0) hR0
      have hlead : lead (trim (mul rf sη)) / lead (trim (mul rη sf)) = c := by
        rw [← leadingCoeff_toPoly hLne, ← leadingCoeff_toPoly hR0, hL, leadingCoeff_mul,
          leadingCoeff_C]
        exact mul_div_cancel_right₀ _ (leadingCoeff_ne_zero.mpr hR0)
      rw [hlead, hL]

end CPoly

-- f = 1/(x+1), η = 1/x: no constant (so log x/(x+1) is not elementary)
#eval CPoly.limitedCrit ([1] : CPoly ℚ) [1, 1] [1] [0, 1]
-- f = 3/x, η = 1/x: c = 3
#eval CPoly.limitedCrit ([3] : CPoly ℚ) [0, 1] [1] [0, 1]

namespace CPoly

open Polynomial

variable {R S : Type*} [Field R] [Field S]

/-- **Descent.** If the limited-integration identity holds over a field extension `S` of `R`, with
a constant `c ∈ S`, then it already holds over `R` with a constant from `R`: new constants do not
help. -/
theorem limited_descent (ι : R →+* S) {rf sf rη sη : R[X]} {c : S}
    (h : rf.map ι * sη.map ι = C c * rη.map ι * sf.map ι) :
    ∃ c₀ : R, rf * sη = C c₀ * rη * sf := by
  by_cases hR : rη * sf = 0
  · refine ⟨0, ?_⟩
    have : (rf * sη).map ι = 0 := by
      rw [Polynomial.map_mul, h, mul_assoc, ← Polynomial.map_mul, hR, Polynomial.map_zero,
        mul_zero]
    rw [(Polynomial.map_eq_zero_iff ι.injective).mp this, C_0, zero_mul, zero_mul]
  · refine ⟨(rf * sη).leadingCoeff / (rη * sf).leadingCoeff, ?_⟩
    have hRS : (rη * sf).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hR
    have hL : (rf * sη).map ι = C c * (rη * sf).map ι := by
      rw [Polynomial.map_mul, Polynomial.map_mul, h]; ring
    have hlc : ι (rf * sη).leadingCoeff = c * ι (rη * sf).leadingCoeff := by
      have := congrArg leadingCoeff hL
      rw [leadingCoeff_map] at this
      rw [this, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_map]
    have hι0 : ι (rη * sf).leadingCoeff ≠ 0 := (map_ne_zero ι).mpr (leadingCoeff_ne_zero.mpr hR)
    have hc : c = ι ((rf * sη).leadingCoeff / (rη * sf).leadingCoeff) := by
      rw [map_div₀, hlc, mul_div_cancel_right₀ _ hι0]
    apply Polynomial.map_injective ι ι.injective
    rw [hL, hc, mul_assoc, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, map_C]

end CPoly
