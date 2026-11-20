import RischTragerBronstein.Computable.RDEPolyMap

/-!
# A verified solver for `P₁ Y′ + P₀ Y = A` over polynomials

`CPoly.odeSolve P₁ P₀ A` decides whether the first-order linear ODE `P₁ Y′ + P₀ Y = A` has a
polynomial solution, when `deg P₁ ≤ deg P₀` and `P₀ ≠ 0` (then the term `P₀ Y` dominates, and the
coefficients of `Y` are determined from the top):

* `odeSolve_sound`:        `odeSolve P₁ P₀ A = some Y → P₁ Y′ + P₀ Y = A`;
* `odeSolve_complete_map`: `odeSolve P₁ P₀ A = none` ⟹ no polynomial solution exists over **any**
  field extension of the coefficient field.

This generalises `rdeSolve` (`P₁ = 1`, `P₀ = g`). It is the polynomial problem to which the Risch
differential equation `y′ + a′ y = A / D` over `C(x)` reduces after clearing the denominator of `y`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R S : Type*} [Field R] [DecidableEq R] [Field S]

/-- The operator `Y ↦ P₁ Y′ + P₀ Y`. -/
def odeOp (P₁ P₀ Y : CPoly R) : CPoly R := add (mul P₁ (deriv Y)) (mul P₀ Y)

/-- Main loop. -/
def odeLoop (P₁ P₀ : CPoly R) (dg : ℕ) (lc : R) : ℕ → CPoly R → CPoly R → CPoly R × CPoly R
  | 0, Y, Rm => (Y, Rm)
  | k + 1, Y, Rm =>
    let m := monomial k (Rm.getD (k + dg) 0 / lc)
    odeLoop P₁ P₀ dg lc k (add Y m) (sub Rm (odeOp P₁ P₀ m))

/-- Decide `P₁ Y′ + P₀ Y = A` over polynomials (`deg P₁ ≤ deg P₀`, `P₀ ≠ 0`). -/
def odeSolve (P₁ P₀ A : CPoly R) : Option (CPoly R) :=
  let r := odeLoop P₁ P₀ ((trim P₀).length - 1) (lead (trim P₀)) A.length [] A
  if isZero r.2 then some (trim r.1) else none

@[simp] lemma toPoly_odeOp (P₁ P₀ Y : CPoly R) :
    toPoly (odeOp P₁ P₀ Y) = toPoly P₁ * derivative (toPoly Y) + toPoly P₀ * toPoly Y := by
  simp [odeOp]

lemma odeLoop_inv (P₁ P₀ : CPoly R) (dg : ℕ) (lc : R) (Fp : R[X]) (k : ℕ) (Y Rm : CPoly R)
    (h : toPoly Rm = Fp - (toPoly P₁ * derivative (toPoly Y) + toPoly P₀ * toPoly Y)) :
    toPoly (odeLoop P₁ P₀ dg lc k Y Rm).2 =
      Fp - (toPoly P₁ * derivative (toPoly (odeLoop P₁ P₀ dg lc k Y Rm).1) +
        toPoly P₀ * toPoly (odeLoop P₁ P₀ dg lc k Y Rm).1) := by
  induction k generalizing Y Rm with
  | zero => exact h
  | succ k ih =>
    simp only [odeLoop]
    apply ih
    simp only [toPoly_sub, toPoly_odeOp, toPoly_add, h, derivative_add]
    ring

theorem odeSolve_sound {P₁ P₀ A Y : CPoly R} (h : odeSolve P₁ P₀ A = some Y) :
    toPoly P₁ * derivative (toPoly Y) + toPoly P₀ * toPoly Y = toPoly A := by
  simp only [odeSolve] at h
  split_ifs at h with hz
  have hinv := odeLoop_inv P₁ P₀ ((trim P₀).length - 1) (lead (trim P₀)) (toPoly A) A.length [] A
    (by simp)
  rw [(isZero_iff _).mp hz] at hinv
  rw [← Option.some.inj h, toPoly_trim]
  exact (sub_eq_zero.mp hinv.symm).symm

variable (ι : R →+* S)

lemma odeLoop_complete_map (P₁ P₀ : CPoly R) (dg : ℕ) (lc : R)
    (hdg : (toPoly P₀).natDegree = dg) (hlc : (toPoly P₀).coeff dg = lc) (hlc0 : lc ≠ 0)
    (hP₁ : (toPoly P₁).natDegree ≤ dg)
    (Ys : S[X]) (k : ℕ) (Y Rm : CPoly R)
    (h : (toPoly Rm).map ι = ((toPoly P₁).map ι * derivative Ys + (toPoly P₀).map ι * Ys) -
      ((toPoly P₁).map ι * derivative ((toPoly Y).map ι) + (toPoly P₀).map ι * (toPoly Y).map ι))
    (hZ : ∀ m, k ≤ m → (Ys - (toPoly Y).map ι).coeff m = 0) :
    (toPoly (odeLoop P₁ P₀ dg lc k Y Rm).2).map ι = 0 := by
  induction k generalizing Y Rm with
  | zero =>
    have hZ0 : Ys - (toPoly Y).map ι = 0 := by ext m; simpa using hZ m (Nat.zero_le m)
    have : Ys = (toPoly Y).map ι := sub_eq_zero.mp hZ0
    simp only [odeLoop]
    rw [h, this, sub_self]
  | succ k ih =>
    simp only [odeLoop]
    set Z := Ys - (toPoly Y).map ι with hZdef
    have hZdeg : Z.natDegree ≤ k :=
      natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ hZ N hN
    have hRm : (toPoly Rm).map ι =
        (toPoly P₁).map ι * derivative Z + (toPoly P₀).map ι * Z := by
      rw [h, hZdef, derivative_sub]; ring
    have hG₀ : ((toPoly P₀).map ι).natDegree ≤ dg := natDegree_map_le.trans hdg.le
    have hG₁ : ((toPoly P₁).map ι).natDegree ≤ dg := natDegree_map_le.trans hP₁
    -- the top coefficient of `P₁ Z′` vanishes
    have htop : ((toPoly P₁).map ι * derivative Z).coeff (k + dg) = 0 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have : derivative Z = 0 := by
          rw [eq_C_of_natDegree_le_zero hZdeg, derivative_C]
        rw [this, mul_zero, coeff_zero]
      · apply coeff_eq_zero_of_natDegree_lt
        have h1 := natDegree_mul_le (p := (toPoly P₁).map ι) (q := derivative Z)
        have h2 := natDegree_derivative_le Z
        omega
    have hc : ι (Rm.getD (k + dg) 0 / lc) = Z.coeff k := by
      have h1 : ι (Rm.getD (k + dg) 0) = ι lc * Z.coeff k := by
        rw [← coeff_toPoly, ← coeff_map, hRm, coeff_add, htop, zero_add, add_comm k dg,
          coeff_mul_add_eq_of_natDegree_le hG₀ hZdeg, coeff_map, hlc]
      have hι0 : ι lc ≠ 0 := (map_ne_zero ι).mpr hlc0
      rw [map_div₀, h1]
      field_simp
    apply ih
    · simp only [toPoly_sub, toPoly_odeOp, toPoly_add, Polynomial.map_sub, Polynomial.map_add,
        Polynomial.map_mul, derivative_map, h, derivative_add]
      ring
    · intro m hm
      rw [toPoly_add, toPoly_monomial, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        map_C, map_X, hc, ← sub_sub, ← hZdef, coeff_sub, coeff_C_mul, coeff_X_pow]
      rcases hm.eq_or_lt with rfl | hlt
      · simp
      · rw [if_neg (by omega : ¬m = k), mul_zero, sub_zero]
        exact hZ m hlt

theorem odeSolve_complete_map [CharZero S] {P₁ P₀ A : CPoly R} (hP₀ : trim P₀ ≠ [])
    (hdeg : (toPoly P₁).natDegree ≤ (toPoly P₀).natDegree) (h : odeSolve P₁ P₀ A = none) :
    ¬∃ Ys : S[X], (toPoly P₁).map ι * derivative Ys + (toPoly P₀).map ι * Ys =
      (toPoly A).map ι := by
  rintro ⟨Ys, hYs⟩
  obtain ⟨hdg, hlc, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil hP₀
  have hP₀0 : toPoly P₀ ≠ 0 := fun h0 ↦ by rw [h0, coeff_zero] at hlc; exact hlc0 hlc.symm
  have hG0 : (toPoly P₀).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hP₀0
  have hbound : ∀ m, A.length ≤ m → (Ys - (toPoly ([] : CPoly R)).map ι).coeff m = 0 := by
    intro m hm
    rw [toPoly_nil, Polynomial.map_zero, sub_zero]
    by_cases hY0 : Ys = 0
    · simp [hY0]
    apply coeff_eq_zero_of_natDegree_lt
    have hlt : ((toPoly P₁).map ι * derivative Ys).degree < ((toPoly P₀).map ι * Ys).degree := by
      by_cases hd0 : (toPoly P₁).map ι * derivative Ys = 0
      · rw [hd0, degree_zero]
        exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr (mul_ne_zero hG0 hY0))
      · have hP₁0 : (toPoly P₁).map ι ≠ 0 := left_ne_zero_of_mul hd0
        have hYd0 : derivative Ys ≠ 0 := right_ne_zero_of_mul hd0
        rw [degree_mul, degree_mul, degree_eq_natDegree hP₁0, degree_eq_natDegree hYd0,
          degree_eq_natDegree hG0, degree_eq_natDegree hY0, ← Nat.cast_add, ← Nat.cast_add]
        have h1 : ((toPoly P₁).map ι).natDegree ≤ ((toPoly P₀).map ι).natDegree := by
          rw [natDegree_map, natDegree_map]; exact hdeg
        have hYpos : Ys.natDegree ≠ 0 := fun h0 ↦ hYd0 (derivative_eq_zero.mpr h0)
        have h2 := natDegree_derivative_lt hYpos
        exact_mod_cast (by omega :
          ((toPoly P₁).map ι).natDegree + (derivative Ys).natDegree <
            ((toPoly P₀).map ι).natDegree + Ys.natDegree)
    have hdegA : ((toPoly A).map ι).natDegree = ((toPoly P₀).map ι).natDegree + Ys.natDegree := by
      rw [← hYs, natDegree_add_eq_right_of_degree_lt hlt, natDegree_mul hG0 hY0]
    have hA0 : toPoly A ≠ 0 := fun h0 ↦ by
      have := degree_add_eq_right_of_degree_lt hlt
      rw [hYs, h0, Polynomial.map_zero, degree_zero] at this
      exact mul_ne_zero hG0 hY0 (degree_eq_bot.mp this.symm)
    have := (natDegree_lt_iff_degree_lt hA0).mpr (degree_toPoly_lt A)
    have hle : ((toPoly A).map ι).natDegree ≤ (toPoly A).natDegree := natDegree_map_le
    omega
  have hfin := odeLoop_complete_map ι P₁ P₀ _ _ hdg hlc hlc0 (hdeg.trans hdg.le) Ys A.length [] A
    (by simp [hYs]) hbound
  simp only [odeSolve] at h
  split_ifs at h with hz
  exact hz ((isZero_iff _).mpr ((Polynomial.map_eq_zero_iff ι.injective).mp hfin))

end CPoly

-- x Y′ + (x² + 1) Y = x³ + 2x  has the solution Y = x
#eval CPoly.odeSolve ([0, 1] : CPoly ℚ) [1, 0, 1] [0, 2, 0, 1]
-- x Y′ + (x² + 1) Y = 1 has none
#eval CPoly.odeSolve ([0, 1] : CPoly ℚ) [1, 0, 1] [1]
