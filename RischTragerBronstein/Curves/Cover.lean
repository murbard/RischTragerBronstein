import RischTragerBronstein.Curves.BivTools

/-!
# Covering the roots of a polynomial by given points

`synthDiv P a`: Horner division by `X − a` (`synthDiv_spec`). `stripAt` removes factors `X − a`,
and `coverCheck P as` strips every `a ∈ as` and checks that a non-zero constant remains.
`coverCheck_spec`: then every root of `P` (in any field, through any `ψ`) is some `ψ a`.
-/

open Polynomial

namespace Curves

open CPoly

section Defs

variable {F : Type*} [Field F] [DecidableEq F]

/-- Horner division by `X − a`: quotient and remainder. -/
def synthDiv (a : F) : CPoly F → CPoly F × F
  | [] => ([], 0)
  | c :: P => ((synthDiv a P).2 :: (synthDiv a P).1, c + a * (synthDiv a P).2)

/-- Remove factors `X − a` (at most `fuel` of them). -/
def stripAt (a : F) : ℕ → CPoly F → CPoly F
  | 0, P => P
  | fuel + 1, P => if (synthDiv a P).2 = 0 then stripAt a fuel (synthDiv a P).1 else P

/-- Strip all the given points and check that a non-zero constant remains. -/
def coverCheck (P : CPoly F) (as : List F) : Bool :=
  let R := as.foldl (fun Q a ↦ stripAt a Q.length Q) P
  decide (degT R = 0) && !isZero R

end Defs

section Spec

variable {F : Type*} [Field F] [DecidableEq F]

lemma synthDiv_spec (a : F) (P : CPoly F) :
    toPoly P = (X - Polynomial.C a) * toPoly (synthDiv a P).1 + Polynomial.C (synthDiv a P).2 := by
  induction P with
  | nil => simp [synthDiv]
  | cons c P ih =>
    simp only [synthDiv, toPoly_cons]
    rw [ih]
    simp only [map_add, map_mul]
    ring

lemma stripAt_spec (a : F) (fuel : ℕ) (P : CPoly F) :
    ∃ e : ℕ, toPoly P = (X - Polynomial.C a) ^ e * toPoly (stripAt a fuel P) := by
  induction fuel generalizing P with
  | zero => exact ⟨0, by simp [stripAt]⟩
  | succ fuel ih =>
    simp only [stripAt]
    split_ifs with h
    · obtain ⟨e, he⟩ := ih (synthDiv a P).1
      refine ⟨e + 1, ?_⟩
      rw [synthDiv_spec a P, h, map_zero, add_zero, he]; ring
    · exact ⟨0, by simp⟩

lemma foldl_strip_spec (as : List F) (P : CPoly F) :
    ∃ Q : F[X], toPoly P = Q * toPoly (as.foldl (fun Q a ↦ stripAt a Q.length Q) P) ∧
      (∀ {K : Type*} [Field K] (ψ : F →+* K) (z : K), (Q.map ψ).eval z = 0 → ∃ a ∈ as, z = ψ a) ∧
      Q ≠ 0 := by
  induction as generalizing P with
  | nil => exact ⟨1, by simp, fun ψ z h ↦ by simp at h, one_ne_zero⟩
  | cons a as ih =>
    obtain ⟨e, he⟩ := stripAt_spec a P.length P
    obtain ⟨Q, hQ, hQr, hQ0⟩ := ih (stripAt a P.length P)
    refine ⟨(X - Polynomial.C a) ^ e * Q, ?_, fun ψ z hz ↦ ?_,
      mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero a)) hQ0⟩
    · rw [List.foldl_cons, he, hQ]; ring
    · rw [Polynomial.map_mul, eval_mul, mul_eq_zero] at hz
      rcases hz with hz | hz
      · simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
          eval_pow, eval_sub, eval_X, eval_C] at hz
        exact ⟨a, List.mem_cons_self, sub_eq_zero.mp (pow_eq_zero_iff'.mp hz).1⟩
      · obtain ⟨b, hb, hzb⟩ := hQr ψ z hz
        exact ⟨b, List.mem_cons_of_mem _ hb, hzb⟩

/-- **The cover check**: every root of `P` is one of the given points. -/
theorem coverCheck_spec (P : CPoly F) (as : List F) (h : coverCheck P as = true)
    {K : Type*} [Field K] (ψ : F →+* K) (z : K) (hz : ((toPoly P).map ψ).eval z = 0) :
    ∃ a ∈ as, z = ψ a := by
  simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Bool.eq_false_iff] at h
  obtain ⟨hdeg, hnz⟩ := h
  obtain ⟨Q, hQ, hQr, -⟩ := foldl_strip_spec as P
  set R := as.foldl (fun Q a ↦ stripAt a Q.length Q) P with hR
  have hR0 : toPoly R ≠ 0 := fun h0 ↦ hnz ((isZero_iff R).mpr h0)
  have hRc : toPoly R = Polynomial.C ((toPoly R).coeff 0) := by
    rw [degT_eq] at hdeg; exact eq_C_of_natDegree_eq_zero hdeg
  rw [hQ, Polynomial.map_mul, eval_mul, hRc, Polynomial.map_C, eval_C] at hz
  have hc : ψ ((toPoly R).coeff 0) ≠ 0 := by
    rw [map_ne_zero_iff ψ ψ.injective]
    intro h0; apply hR0; rw [hRc, h0, map_zero]
  exact hQr ψ z ((mul_eq_zero.mp hz).resolve_right hc)

/-- A passing cover check means a nonzero polynomial. -/
theorem coverCheck_ne_zero (P : CPoly F) (as : List F) (h : coverCheck P as = true) :
    toPoly P ≠ 0 := by
  simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Bool.eq_false_iff] at h
  obtain ⟨-, hnz⟩ := h
  obtain ⟨Q, hQ, -, hQ0⟩ := foldl_strip_spec.{_, 0} as P
  rw [hQ]
  exact mul_ne_zero hQ0 fun h0 ↦ hnz ((isZero_iff _).mpr h0)

end Spec

end Curves
