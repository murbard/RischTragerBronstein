import RischTragerBronstein.Curves.Cover
import RischTragerBronstein.Computable.ResultantC

/-!
# Completeness of the cover check

`coverCheck P as` strips the factors `X − a` (`a ∈ as`) of `P` and checks that a non-zero constant
remains. **`coverCheck_complete`**: if `P ≠ 0` and every root of `P` in an algebraically closed
field `K ⊇ F` is (the image of) one of the points, the check passes. With `coverCheck_spec` this
makes the check an exact test.
-/

open Polynomial

namespace Curves

open CPoly

section Complete

variable {F : Type*} [Field F] [DecidableEq F]

lemma natDegree_toPoly_lt_length (P : CPoly F) (h : toPoly P ≠ 0) :
    (toPoly P).natDegree < P.length := by
  by_contra hle
  push Not at hle
  apply leadingCoeff_ne_zero.mpr h
  rw [leadingCoeff, coeff_toPoly]
  exact List.getD_eq_default _ _ hle

/-- Stripping `X − a` as long as possible leaves a factor not vanishing at `a`. -/
lemma stripAt_eval_ne (a : F) : ∀ (fuel : ℕ) (P : CPoly F), toPoly P ≠ 0 →
    (toPoly P).natDegree < fuel → (toPoly (stripAt a fuel P)).eval a ≠ 0
  | 0, P, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, P, hP, hdeg => by
    simp only [stripAt]
    have hs := synthDiv_spec a P
    split_ifs with h
    · rw [h, map_zero, add_zero] at hs
      have hQ : toPoly (synthDiv a P).1 ≠ 0 := fun h0 ↦ hP (by rw [hs, h0, mul_zero])
      refine stripAt_eval_ne a fuel _ hQ ?_
      have := congrArg natDegree hs
      rw [natDegree_mul (X_sub_C_ne_zero a) hQ, natDegree_X_sub_C] at this
      omega
    · rw [hs]; simpa using h

/-- Stripping all the points: a non-zero factor dividing `P` that vanishes at none of them. -/
lemma foldl_strip_facts : ∀ (as : List F) (P : CPoly F), toPoly P ≠ 0 →
    toPoly (as.foldl (fun Q a ↦ stripAt a Q.length Q) P) ≠ 0 ∧
      toPoly (as.foldl (fun Q a ↦ stripAt a Q.length Q) P) ∣ toPoly P ∧
      ∀ a ∈ as, (toPoly (as.foldl (fun Q a ↦ stripAt a Q.length Q) P)).eval a ≠ 0
  | [], P, hP => ⟨hP, dvd_rfl, fun a ha ↦ by simp at ha⟩
  | a :: as, P, hP => by
    obtain ⟨e, he⟩ := stripAt_spec a P.length P
    set S := stripAt a P.length P with hS
    have hS0 : toPoly S ≠ 0 := fun h0 ↦ hP (by rw [he, h0, mul_zero])
    have hSa : (toPoly S).eval a ≠ 0 :=
      stripAt_eval_ne a P.length P hP (natDegree_toPoly_lt_length P hP)
    obtain ⟨h1, h2, h3⟩ := foldl_strip_facts as S hS0
    rw [List.foldl_cons]
    refine ⟨h1, h2.trans ⟨_, by rw [he, mul_comm]⟩, fun b hb ↦ ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · obtain ⟨c, hc⟩ := h2
      intro h0
      apply hSa
      rw [hc, eval_mul, h0, zero_mul]
    · exact h3 b hb

/-- **The cover check is complete.** -/
theorem coverCheck_complete (P : CPoly F) (as : List F) (hP : toPoly P ≠ 0) {K : Type*} [Field K]
    [IsAlgClosed K] (ψ : F →+* K)
    (hroots : ∀ z : K, ((toPoly P).map ψ).eval z = 0 → ∃ a ∈ as, z = ψ a) :
    coverCheck P as = true := by
  obtain ⟨hR0, hRd, hRa⟩ := foldl_strip_facts as P hP
  set R := as.foldl (fun Q a ↦ stripAt a Q.length Q) P with hR
  simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨?_, ?_⟩
  · rw [← hR, degT_eq]
    by_contra hdeg
    have hdeg' : 0 < ((toPoly R).map ψ).degree := by
      rw [degree_map]
      exact natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ (ne_of_gt hdeg')
    obtain ⟨a, ha, rfl⟩ := hroots z (by
      obtain ⟨c, hc⟩ := hRd
      rw [hc, Polynomial.map_mul, eval_mul, hz.eq_zero, zero_mul])
    apply hRa a ha
    rw [IsRoot, eval_map, eval₂_at_apply] at hz
    exact (map_eq_zero_iff ψ ψ.injective).mp hz
  · rw [← hR]
    cases h : isZero R
    · rfl
    · exact absurd ((isZero_iff R).mp h) hR0

end Complete

end Curves
