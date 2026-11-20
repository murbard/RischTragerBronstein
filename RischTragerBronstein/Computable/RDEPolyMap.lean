import RischTragerBronstein.Computable.RDEPoly

/-!
# Completeness of the polynomial RDE solver over extension fields

`rdeSolve_complete_map`: if `rdeSolve g f = none` over `R`, then `Y′ + g Y = f` has no polynomial
solution over **any field extension** `S` of `R` either.

This is what makes the solver's negative answer robust under enlargement of the constant field:
by the strong Liouville theorem, an elementary antiderivative may involve new constants, and the
corresponding Risch differential equation then lives over a bigger constant field. The proof is the
completeness proof of `RDEPoly.lean`, transported along `ι : R → S`; the algorithm's arithmetic
commutes with `ι`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R S : Type*} [Field R] [DecidableEq R] [Field S] (ι : R →+* S)

lemma rdeLoop_complete_map (g : CPoly R) (dg : ℕ) (lcg : R)
    (hdg : (toPoly g).natDegree = dg) (hlc : (toPoly g).coeff dg = lcg) (hlc0 : lcg ≠ 0)
    (Ys : S[X]) (k : ℕ) (Y Rm : CPoly R)
    (h : (toPoly Rm).map ι = (derivative Ys + (toPoly g).map ι * Ys) -
      (derivative ((toPoly Y).map ι) + (toPoly g).map ι * (toPoly Y).map ι))
    (hZ : ∀ m, k ≤ m → (Ys - (toPoly Y).map ι).coeff m = 0) :
    (toPoly (rdeLoop g dg lcg k Y Rm).2).map ι = 0 := by
  induction k generalizing Y Rm with
  | zero =>
    have hZ0 : Ys - (toPoly Y).map ι = 0 := by ext m; simpa using hZ m (Nat.zero_le m)
    have : Ys = (toPoly Y).map ι := sub_eq_zero.mp hZ0
    simp only [rdeLoop]
    rw [h, this, sub_self]
  | succ k ih =>
    simp only [rdeLoop]
    set Z := Ys - (toPoly Y).map ι with hZdef
    have hZdeg : Z.natDegree ≤ k :=
      natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ hZ N hN
    have hRm : (toPoly Rm).map ι = derivative Z + (toPoly g).map ι * Z := by
      rw [h, hZdef, derivative_sub]; ring
    have hGdeg : ((toPoly g).map ι).natDegree ≤ dg := (natDegree_map_le).trans hdg.le
    have hc : ι (Rm.getD (k + dg) 0 / lcg) = Z.coeff k := by
      have h1 : ι (Rm.getD (k + dg) 0) = ι lcg * Z.coeff k := by
        rw [← coeff_toPoly, ← coeff_map, hRm, coeff_add, coeff_derivative,
          coeff_eq_zero_of_natDegree_lt (by omega : Z.natDegree < k + dg + 1), zero_mul, zero_add,
          add_comm k dg, coeff_mul_add_eq_of_natDegree_le hGdeg hZdeg, coeff_map, hlc]
      have hι0 : ι lcg ≠ 0 := (map_ne_zero ι).mpr hlc0
      rw [map_div₀, h1]
      field_simp
    apply ih
    · simp only [toPoly_sub, toPoly_rdeOp, toPoly_add, Polynomial.map_sub, Polynomial.map_add,
        Polynomial.map_mul, derivative_map, h, derivative_add]
      ring
    · intro m hm
      rw [toPoly_add, toPoly_monomial, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        map_C, map_X, hc, ← sub_sub, ← hZdef, coeff_sub, coeff_C_mul, coeff_X_pow]
      rcases hm.eq_or_lt with rfl | hlt
      · simp
      · rw [if_neg (by omega : ¬m = k), mul_zero, sub_zero]
        exact hZ m hlt

theorem rdeSolve_complete_map {g f : CPoly R} (hg : trim g ≠ []) (h : rdeSolve g f = none) :
    ¬∃ Ys : S[X], derivative Ys + (toPoly g).map ι * Ys = (toPoly f).map ι := by
  rintro ⟨Ys, hYs⟩
  obtain ⟨hdg, hlc, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil hg
  have hg0 : toPoly g ≠ 0 := fun h0 ↦ by rw [h0, coeff_zero] at hlc; exact hlc0 hlc.symm
  have hG0 : (toPoly g).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hg0
  have hbound : ∀ m, f.length ≤ m → (Ys - (toPoly ([] : CPoly R)).map ι).coeff m = 0 := by
    intro m hm
    rw [toPoly_nil, Polynomial.map_zero, sub_zero]
    by_cases hY0 : Ys = 0
    · simp [hY0]
    apply coeff_eq_zero_of_natDegree_lt
    have hlt : (derivative Ys).degree < ((toPoly g).map ι * Ys).degree := by
      refine lt_of_lt_of_le (degree_derivative_lt hY0) ?_
      rw [degree_mul]
      exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hG0)
    have hdeg : ((toPoly f).map ι).natDegree = ((toPoly g).map ι).natDegree + Ys.natDegree := by
      rw [← hYs, add_comm, natDegree_add_eq_left_of_degree_lt hlt, natDegree_mul hG0 hY0]
    have hf0 : toPoly f ≠ 0 := fun h0 ↦ by
      have := degree_add_eq_right_of_degree_lt hlt
      rw [hYs, h0, Polynomial.map_zero, degree_zero] at this
      exact mul_ne_zero hG0 hY0 (degree_eq_bot.mp this.symm)
    have := (natDegree_lt_iff_degree_lt hf0).mpr (degree_toPoly_lt f)
    have hle : ((toPoly f).map ι).natDegree ≤ (toPoly f).natDegree := natDegree_map_le
    omega
  have hfin := rdeLoop_complete_map ι g _ _ hdg hlc hlc0 Ys f.length [] f (by simp [hYs]) hbound
  simp only [rdeSolve] at h
  split_ifs at h with hz
  refine hz ((isZero_iff _).mpr ?_)
  exact (Polynomial.map_eq_zero_iff ι.injective).mp hfin

end CPoly
