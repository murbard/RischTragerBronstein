import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.Int.Interval

/-!
# Schur's theorem

A non-constant integer polynomial has a root modulo infinitely many primes
(`exists_prime_dvd_eval`: outside any finite set of primes there is a prime dividing some value).
-/

open Polynomial

namespace Schur

/-- **Schur's theorem.** For a non-constant `F ∈ ℤ[X]` and a finite set `S`, some prime `p ∉ S`
divides a value `F(n)`. -/
theorem exists_prime_dvd_eval (F : ℤ[X]) (hF : 0 < F.natDegree) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ n : ℤ, (p : ℤ) ∣ F.eval n := by
  classical
  by_cases hc : F.eval 0 = 0
  · obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (S.sup id + 1)
    refine ⟨p, hpp, fun hmem ↦ ?_, 0, by rw [hc]; exact dvd_zero _⟩
    have := Finset.le_sup (f := id) hmem
    simp at this; omega
  set c := F.eval 0
  set P : ℤ := ∏ p ∈ S.filter Nat.Prime, (p : ℤ)
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦ by
    exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  set Q : ℤ := c * P
  have hQ0 : Q ≠ 0 := mul_ne_zero hc hP0
  set G : ℤ[X] := F.comp (C Q * X)
  have hGdeg : G.natDegree = F.natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X Q hQ0, mul_one]
  -- values with `|G(k)| ≤ |c|` are finitely many
  set T : Finset ℤ := Finset.Icc (-|c|) |c|
  set bad : Finset ℤ := T.biUnion fun t ↦ (G - C t).roots.toFinset
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset bad
  have hbig : |c| < |G.eval k| := by
    by_contra hle
    push_neg at hle
    apply hk
    refine Finset.mem_biUnion.mpr ⟨G.eval k, Finset.mem_Icc.mpr (abs_le.mp hle), ?_⟩
    have hne : G - C (G.eval k) ≠ 0 := fun h0 ↦ by
      have := congrArg natDegree h0
      rw [natDegree_sub_C, natDegree_zero] at this; omega
    rw [Multiset.mem_toFinset, mem_roots hne]
    simp
  -- `G(k) = c (1 + P k m)`
  have hdvd : Q * k ∣ G.eval k - c := by
    have := sub_dvd_eval_sub (Q * k) 0 F
    simpa [G, eval_comp] using this
  obtain ⟨m, hm⟩ := hdvd
  set v : ℤ := 1 + P * k * m
  have hGv : G.eval k = c * v := by
    have : G.eval k = c + Q * k * m := by linarith
    rw [this]; simp only [v, Q]; ring
  have hv : 1 < v.natAbs := by
    rw [hGv, abs_mul] at hbig
    have hc' : 0 < |c| := abs_pos.mpr hc
    have : 1 < |v| := by
      by_contra h; push_neg at h
      have := mul_le_mul_of_nonneg_left h hc'.le
      linarith
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  obtain ⟨q, hq, hqv⟩ := Nat.exists_prime_and_dvd (show v.natAbs ≠ 1 by omega)
  refine ⟨q, hq, fun hqS ↦ ?_, Q * k, ?_⟩
  · have hqP : (q : ℤ) ∣ P :=
      Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hqS, hq⟩)
    have hqv' : (q : ℤ) ∣ v := Int.natCast_dvd.mpr hqv
    have : (q : ℤ) ∣ 1 := by
      have h2 : (q : ℤ) ∣ P * k * m := Dvd.dvd.mul_right (Dvd.dvd.mul_right hqP _) _
      have := dvd_sub hqv' h2
      simpa [v] using this
    have := Int.eq_one_of_dvd_one (by positivity) this
    exact hq.one_lt.ne' (by exact_mod_cast this)
  · have : F.eval (Q * k) = G.eval k := by simp [G, eval_comp]
    rw [this, hGv]
    exact Dvd.dvd.mul_left (Int.natCast_dvd.mpr hqv) _

end Schur
