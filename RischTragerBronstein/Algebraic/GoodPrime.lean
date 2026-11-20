import RischTragerBronstein.Algebraic.Schur
import RischTragerBronstein.Algebraic.EllComplete
import RischTragerBronstein.Elliptic.DV.GoodRed

/-!
# Good auxiliary primes exist

For a separable non-constant `F ∈ ℤ[X]` and a curve `y² = x³ + ax² + bx + c` with squarefree
cubic, there is an odd prime `p` of good reduction at which `F` has a simple root modulo `p`
(`exists_good_prime`). The proof uses Schur's theorem, avoiding the primes that divide
`Res(F, F′)`, the discriminant of the cubic, or `2`.
-/

open Polynomial

namespace Schur

/-- The predicate searched for. -/
def GoodPrime (F : ℤ[X]) (a b c : ℤ) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ EllDV.goodRedMod p a b c ∧
    ∃ s : ZMod p, (F.map (Int.castRingHom (ZMod p))).eval s = 0 ∧
      ((derivative F).map (Int.castRingHom (ZMod p))).eval s ≠ 0

theorem exists_good_prime (F : ℤ[X]) (hF : 0 < F.natDegree)
    (hsep : (F.map (Int.castRingHom ℚ)).Separable) (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ))) :
    ∃ p, GoodPrime F a b c p := by
  classical
  -- the resultant of `F` and `F′` is a non-zero integer
  set R := resultant F (derivative F) with hRdef
  have hinj := RingHom.injective_int (Int.castRingHom ℚ)
  have hR0 : R ≠ 0 := by
    intro h0
    have hmap := resultant_map_map F (derivative F) F.natDegree (derivative F).natDegree
      (Int.castRingHom ℚ)
    rw [← hRdef, h0, map_zero] at hmap
    have hne := resultant_ne_zero (F.map (Int.castRingHom ℚ)) _ (hsep : IsCoprime _ _)
    rw [derivative_map, natDegree_map_eq_of_injective hinj,
      natDegree_map_eq_of_injective hinj] at hne
    exact hne hmap
  obtain ⟨u, v, -, -, huv⟩ := exists_mul_add_mul_eq_C_resultant F (derivative F) le_rfl le_rfl
    (Or.inl hF.ne')
  -- the discriminant of the cubic
  have hD0 : EllNL.disc a b c ≠ 0 := EllAlgo.disc_ne_zero_of_squarefree a b c hsq
  set S := Nat.primeFactors (R.natAbs * (EllNL.disc a b c).natAbs * 2)
  obtain ⟨p, hp, hpS, n, hn⟩ := exists_prime_dvd_eval F hF S
  have hprod0 : R.natAbs * (EllNL.disc a b c).natAbs * 2 ≠ 0 := by
    simp [hR0, hD0]
  have hndvd : ¬p ∣ R.natAbs * (EllNL.disc a b c).natAbs * 2 := fun h ↦
    hpS (Nat.mem_primeFactors.mpr ⟨hp, h, hprod0⟩)
  have hpR : ¬(p : ℤ) ∣ R := fun h ↦ hndvd (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (Int.natCast_dvd.mp h) _) _)
  have hpD : ¬(p : ℤ) ∣ EllNL.disc a b c := fun h ↦ hndvd (Dvd.dvd.mul_right (Dvd.dvd.mul_left
    (Int.natCast_dvd.mp h) _) _)
  have hp2 : p ≠ 2 := fun h ↦ hndvd (by subst h; exact dvd_mul_left 2 _)
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hp2, ?_, (n : ZMod p), ?_, ?_⟩
  · -- good reduction
    intro s hs1 hs2
    apply hpD
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := EllNL.disc_bezout a b c 0
    have hb : ((EllNL.disc a b c : ℤ) : ZMod p) =
        ((-6 * a ^ 2 + 18 * b) * s + (-4 * a ^ 3 + 15 * a * b - 27 * c)) *
          (s ^ 3 + a * s ^ 2 + b * s + c) +
        ((2 * a ^ 2 - 6 * b) * s ^ 2 + (2 * a ^ 3 - 7 * a * b + 9 * c) * s +
          (a ^ 2 * b + 3 * a * c - 4 * b ^ 2)) * (3 * s ^ 2 + 2 * a * s + b) := by
      simp only [EllNL.disc]; push_cast; ring
    rw [hb, hs1, hs2]; ring
  · -- a root
    rw [eval_map, eval₂_at_intCast, eq_intCast, Int.cast_id, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hn]
  · -- simple
    intro h0
    apply hpR
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrArg (fun P : ℤ[X] ↦ (P.map (Int.castRingHom (ZMod p))).eval (n : ZMod p)) huv
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, map_C, eval_C] at this
    have hF0 : (F.map (Int.castRingHom (ZMod p))).eval (n : ZMod p) = 0 := by
      rw [eval_map, eval₂_at_intCast, eq_intCast, Int.cast_id, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hn]
    rw [hF0, h0, zero_mul, zero_mul, add_zero, eq_intCast] at this
    exact this.symm

end Schur
