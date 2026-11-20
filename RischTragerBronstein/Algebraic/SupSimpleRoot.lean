import RischTragerBronstein.Algebraic.SupRedGNF

/-!
# Simple roots modulo infinitely many primes, for any separable integer polynomial

`exists_simple_root_prime_sep`: a non-constant `m ∈ ℤ[X]`, separable over `ℚ`, has a simple root
modulo infinitely many primes (Schur's theorem and the resultant `Res(m, m′) ≠ 0`).
-/

open Polynomial

namespace Sup

lemma exists_simple_root_prime_sep (mZ : ℤ[X]) (hsep : (mZ.map (Int.castRingHom ℚ)).Separable)
    (hF0 : 0 < mZ.natDegree) (T : ℕ) :
    ∃ p, T < p ∧ p.Prime ∧ ∃ s : ZMod p, (mZ.map (Int.castRingHom (ZMod p))).eval s = 0 ∧
      ((derivative mZ).map (Int.castRingHom (ZMod p))).eval s ≠ 0 := by
  obtain ⟨u', v', -, -, huv'⟩ := exists_mul_add_mul_eq_C_resultant mZ (derivative mZ) le_rfl le_rfl
    (Or.inl hF0.ne')
  set R := resultant mZ (derivative mZ)
  have hR0 : R ≠ 0 := by
    intro h0
    have hmap := resultant_map_map mZ (derivative mZ) mZ.natDegree (derivative mZ).natDegree
      (Int.castRingHom ℚ)
    rw [← show R = resultant mZ (derivative mZ) from rfl, h0, map_zero] at hmap
    have hne := resultant_ne_zero (mZ.map (Int.castRingHom ℚ)) _ (hsep : IsCoprime _ _)
    rw [derivative_map, natDegree_map_eq_of_injective (RingHom.injective_int _),
      natDegree_map_eq_of_injective (RingHom.injective_int _)] at hne
    exact hne hmap
  obtain ⟨p, hp, hpS, n, hn⟩ := Schur.exists_prime_dvd_eval mZ hF0
    (Finset.range (T + 1) ∪ Nat.primeFactors R.natAbs)
  have hpT : T < p := by
    by_contra h; exact hpS (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega)))
  have hpR : ¬ (p : ℤ) ∣ R := fun h ↦ hpS (Finset.mem_union_right _
    (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hR0⟩))
  refine ⟨p, hpT, hp, (n : ZMod p), ?_, ?_⟩
  · rw [eval_map, eval₂_at_intCast, eq_intCast, Int.cast_id,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hn]
  · intro h0
    apply hpR
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hs : (mZ.map (Int.castRingHom (ZMod p))).eval (n : ZMod p) = 0 := by
      rw [eval_map, eval₂_at_intCast, eq_intCast, Int.cast_id,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hn]
    have := congrArg (fun P : ℤ[X] ↦ (P.map (Int.castRingHom (ZMod p))).eval (n : ZMod p)) huv'
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, map_C, eval_C] at this
    simp only [hs, h0, mul_zero, zero_mul, zero_add, eq_intCast] at this
    exact this.symm

end Sup
