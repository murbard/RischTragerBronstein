import RischTragerBronstein.Computable.Rational
import RischTragerBronstein.RDE.NoSolution

/-!
# A verified decision procedure for the polynomial Risch differential equation

`CPoly.rdeSolve g f` decides whether `Y′ + g Y = f` has a polynomial solution, for `g, f ∈ R[x]`,
`g ≠ 0`, and returns it:

* `rdeSolve_sound`:    `rdeSolve g f = some Y  →  Y′ + g Y = f`;
* `rdeSolve_complete`: `rdeSolve g f = none    →  no `Y ∈ R[x]` satisfies `Y′ + g Y = f``.

Unlike the certificate-checked rational integrator, here **both** answers are proved: a `none` is
a proof of non-existence. The algorithm determines the coefficients of `Y` from the top: if
`deg Z ≤ k` then the coefficient of `x ^ (k + deg g)` in `Z′ + g Z` is `lc(g) * Z_k`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R]

/-- The operator `Y ↦ Y′ + g Y`. -/
def rdeOp (g Y : CPoly R) : CPoly R := add (deriv Y) (mul g Y)

/-- Main loop: `k` coefficients of `Y` remain to be determined; `Rm` is the current remainder. -/
def rdeLoop (g : CPoly R) (dg : ℕ) (lcg : R) : ℕ → CPoly R → CPoly R → CPoly R × CPoly R
  | 0, Y, Rm => (Y, Rm)
  | k + 1, Y, Rm =>
    let m := monomial k (Rm.getD (k + dg) 0 / lcg)
    rdeLoop g dg lcg k (add Y m) (sub Rm (rdeOp g m))

/-- Decide `Y′ + g Y = f` over polynomials (`g ≠ 0`). -/
def rdeSolve (g f : CPoly R) : Option (CPoly R) :=
  let r := rdeLoop g ((trim g).length - 1) (lead (trim g)) f.length [] f
  if isZero r.2 then some (trim r.1) else none

@[simp] lemma toPoly_rdeOp (g Y : CPoly R) :
    toPoly (rdeOp g Y) = derivative (toPoly Y) + toPoly g * toPoly Y := by
  simp [rdeOp]

/-- Invariant of the loop: `Rm = f - (Y′ + g Y)`. -/
lemma rdeLoop_inv (g : CPoly R) (dg : ℕ) (lcg : R) (Fp : R[X]) (k : ℕ) (Y Rm : CPoly R)
    (h : toPoly Rm = Fp - (derivative (toPoly Y) + toPoly g * toPoly Y)) :
    toPoly (rdeLoop g dg lcg k Y Rm).2 =
      Fp - (derivative (toPoly (rdeLoop g dg lcg k Y Rm).1) +
        toPoly g * toPoly (rdeLoop g dg lcg k Y Rm).1) := by
  induction k generalizing Y Rm with
  | zero => exact h
  | succ k ih =>
    simp only [rdeLoop]
    apply ih
    simp only [toPoly_sub, toPoly_rdeOp, toPoly_add, h, derivative_add]
    ring

theorem rdeSolve_sound {g f Y : CPoly R} (h : rdeSolve g f = some Y) :
    derivative (toPoly Y) + toPoly g * toPoly Y = toPoly f := by
  simp only [rdeSolve] at h
  split_ifs at h with hz
  have hinv := rdeLoop_inv g ((trim g).length - 1) (lead (trim g)) (toPoly f) f.length [] f
    (by simp)
  rw [(isZero_iff _).mp hz] at hinv
  rw [← Option.some.inj h, toPoly_trim]
  exact (sub_eq_zero.mp hinv.symm).symm

/-- Completeness of the loop: if a solution `Ys` exists and agrees with `Y` from degree `k` on,
the final remainder is zero. -/
lemma rdeLoop_complete (g : CPoly R) (dg : ℕ) (lcg : R) (hdg : (toPoly g).natDegree = dg)
    (hlc : (toPoly g).coeff dg = lcg) (hlc0 : lcg ≠ 0) (Ys : R[X]) (k : ℕ) (Y Rm : CPoly R)
    (h : toPoly Rm = (derivative Ys + toPoly g * Ys) -
      (derivative (toPoly Y) + toPoly g * toPoly Y))
    (hZ : ∀ m, k ≤ m → (Ys - toPoly Y).coeff m = 0) :
    toPoly (rdeLoop g dg lcg k Y Rm).2 = 0 := by
  induction k generalizing Y Rm with
  | zero =>
    have hZ0 : Ys - toPoly Y = 0 := by ext m; simpa using hZ m (Nat.zero_le m)
    have : Ys = toPoly Y := sub_eq_zero.mp hZ0
    simp only [rdeLoop]
    rw [h, this, sub_self]
  | succ k ih =>
    simp only [rdeLoop]
    set Z := Ys - toPoly Y with hZdef
    have hZdeg : Z.natDegree ≤ k :=
      natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ hZ N hN
    have hRm : toPoly Rm = derivative Z + toPoly g * Z := by
      rw [h, hZdef, derivative_sub]; ring
    -- the coefficient extracted by the algorithm is `Z_k`
    have hc : Rm.getD (k + dg) 0 / lcg = Z.coeff k := by
      rw [← coeff_toPoly, hRm, coeff_add, coeff_derivative,
        coeff_eq_zero_of_natDegree_lt (by omega : Z.natDegree < k + dg + 1), zero_mul, zero_add,
        add_comm k dg, coeff_mul_add_eq_of_natDegree_le hdg.le hZdeg, hlc]
      field_simp
    apply ih
    · simp only [toPoly_sub, toPoly_rdeOp, toPoly_add, h, derivative_add]
      ring
    · intro m hm
      rw [toPoly_add, toPoly_monomial, hc, ← sub_sub, ← hZdef, coeff_sub, coeff_C_mul, coeff_X_pow]
      rcases hm.eq_or_lt with rfl | hlt
      · simp
      · rw [if_neg (by omega : ¬m = k), mul_zero, sub_zero]
        exact hZ m hlt

lemma natDegree_toPoly_of_trim_ne_nil {g : CPoly R} (hg : trim g ≠ []) :
    (toPoly g).natDegree = (trim g).length - 1 ∧
      (toPoly g).coeff ((trim g).length - 1) = lead (trim g) ∧ lead (trim g) ≠ 0 := by
  have hpos := List.length_pos_of_ne_nil hg
  have hlead : lead (trim g) = (trim g).getLast hg := by
    rw [lead, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hg]; rfl
  have hne : lead (trim g) ≠ 0 := hlead ▸ getLast_trim_ne_zero g hg
  have hcoeff : (toPoly g).coeff ((trim g).length - 1) = lead (trim g) := by
    rw [← toPoly_trim, coeff_toPoly, List.getD_eq_getElem _ _ (by omega),
      ← List.getLast_eq_getElem hg, hlead]
  refine ⟨le_antisymm ?_ (le_natDegree_of_ne_zero (hcoeff ▸ hne)), hcoeff, hne⟩
  have := degree_toPoly_lt (trim g)
  rw [toPoly_trim] at this
  have h2 := natDegree_lt_iff_degree_lt (p := toPoly g) (n := (trim g).length)
    (fun h0 ↦ by rw [h0, coeff_zero] at hcoeff; exact hne hcoeff.symm)
  have := h2.mpr this
  omega

theorem rdeSolve_complete {g f : CPoly R} (hg : trim g ≠ []) (h : rdeSolve g f = none) :
    ¬∃ Ys : R[X], derivative Ys + toPoly g * Ys = toPoly f := by
  rintro ⟨Ys, hYs⟩
  obtain ⟨hdg, hlc, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil hg
  have hg0 : toPoly g ≠ 0 := fun h0 ↦ by rw [h0, coeff_zero] at hlc; exact hlc0 hlc.symm
  -- degree bound for the solution
  have hbound : ∀ m, f.length ≤ m → (Ys - toPoly ([] : CPoly R)).coeff m = 0 := by
    intro m hm
    rw [toPoly_nil, sub_zero]
    by_cases hY0 : Ys = 0
    · simp [hY0]
    apply coeff_eq_zero_of_natDegree_lt
    have hlt : (derivative Ys).degree < (toPoly g * Ys).degree := by
      refine lt_of_lt_of_le (degree_derivative_lt hY0) ?_
      rw [degree_mul]
      exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hg0)
    have hdeg : (toPoly f).natDegree = (toPoly g).natDegree + Ys.natDegree := by
      rw [← hYs, add_comm, natDegree_add_eq_left_of_degree_lt hlt, natDegree_mul hg0 hY0]
    have hf0 : toPoly f ≠ 0 := fun h0 ↦ by
      have := degree_add_eq_right_of_degree_lt hlt
      rw [hYs, h0, degree_zero] at this
      exact mul_ne_zero hg0 hY0 (degree_eq_bot.mp this.symm)
    have := (natDegree_lt_iff_degree_lt hf0).mpr (degree_toPoly_lt f)
    omega
  have hfin := rdeLoop_complete g _ _ hdg hlc hlc0 Ys f.length [] f (by simp [hYs]) hbound
  simp only [rdeSolve] at h
  split_ifs at h with hz
  exact hz ((isZero_iff _).mpr hfin)

end CPoly

-- ∫ (2x² + 1) exp(x²) dx = x exp(x²):  Y′ + 2x Y = 2x² + 1 has the solution Y = x.
#eval CPoly.rdeSolve ([0, 2] : CPoly ℚ) [1, 0, 2]
-- ∫ exp(x²) dx: Y′ + 2x Y = 1 has no solution — `none` is a proof of that.
#eval CPoly.rdeSolve ([0, 2] : CPoly ℚ) [1]
-- ∫ x³ exp(x) dx = (x³ - 3x² + 6x - 6) exp(x)
#eval CPoly.rdeSolve ([1] : CPoly ℚ) [0, 0, 0, 1]
