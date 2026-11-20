import RischTragerBronstein.Mixed.ManinComplete
import RischTragerBronstein.Mixed.KXManin

/-!
# The Manin certificate exists on represented points (relative to `MKT`)

`manCertP_exists`: for independent represented points `P, Q` (`Rel`) of `y² = x³ + A x + B` over
`K(X)` with non-constant `j` (`β ≠ 0`), Manin's kernel theorem `MKT K` makes the Manin check
`manCertP` or its constant-ratio variant `manCertRP` accept the code points (`cert_complete`, after
checking the side conditions `muOK` from the representation: `v ≠ 0` since independent points are not
`2`-torsion).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Manin

open FFHeight FFHeight.Fr

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)

/-- Independence modulo torsion from independence. -/
theorem indep_tors {G : Type*} [AddCommGroup G] (P Q : G)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) (m n : ℤ) (T : G)
    (hT : ∃ k : ℕ, k ≠ 0 ∧ k • T = 0) (h : m • P = n • Q + T) : m = 0 ∧ n = 0 := by
  obtain ⟨k, hk, hkT⟩ := hT
  have h2 : ((k : ℤ) * m) • P = ((k : ℤ) * n) • Q := by
    rw [mul_smul, mul_smul, h, smul_add, natCast_zsmul T k, hkT, add_zero]
  obtain ⟨h3, h4⟩ := hind _ _ h2
  have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk
  exact ⟨(mul_eq_zero.mp h3).resolve_left hk', (mul_eq_zero.mp h4).resolve_left hk'⟩

open scoped Classical in
/-- **The Manin certificate accepts independent represented points, given `MKT`.** -/
theorem manCertP_exists (hM : MKT K) {isRat : K → Bool}
    (hRat : ∀ x, isRat x = true ↔ ∃ q : ℚ, x = q) (Ac Bc : CPoly K)
    (hΔ' : 4 * CPoly.toPoly Ac ^ 3 + 27 * CPoly.toPoly Bc ^ 2 ≠ 0)
    (hβ : bt dX (ι (CPoly.toPoly Ac)) (ι (CPoly.toPoly Bc)) ≠ 0)
    (oD oZ : PtC K) (P Q : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point)
    (hP : Rel _ _ oD P) (hQ : Rel _ _ oZ Q) (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    Differential.SuperData.manCertP Ac Bc oD oZ = true ∨
      Differential.SuperData.manCertRP Ac Bc isRat oD oZ = true := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  -- neither point is `0` nor `2`-torsion
  have hP2 : P + P ≠ 0 := fun h ↦ by
    have := hind 2 0 (by rw [two_zsmul, h, zero_zsmul]); omega
  have hQ2 : Q + Q ≠ 0 := fun h ↦ by
    have := hind 0 2 (by rw [two_zsmul, h, zero_zsmul]); omega
  rcases oD with _ | ⟨uD, vD⟩
  · rcases P with _ | ⟨x, y, h⟩
    · exact absurd rfl hP2
    · exact absurd hP (by simp [FFHeight.Rel])
  rcases oZ with _ | ⟨uZ, vZ⟩
  · rcases Q with _ | ⟨x, y, h⟩
    · exact absurd rfl hQ2
    · exact absurd hQ (by simp [FFHeight.Rel])
  rcases P with _ | ⟨xP, yP, hPn⟩
  · exact absurd hP (by simp [FFHeight.Rel])
  rcases Q with _ | ⟨xQ, yQ, hQn⟩
  · exact absurd hQ (by simp [FFHeight.Rel])
  obtain ⟨ouD, ovD, rfl, rfl⟩ := hP
  obtain ⟨ouZ, ovZ, rfl, rfl⟩ := hQ
  have hy0 : ∀ {x y : RatFunc K} (hn : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Nonsingular x y),
      Point.some x y hn + Point.some x y hn ≠ 0 → y ≠ 0 := fun hn h2 hy ↦ by
    apply h2; apply Point.add_self_of_Y_eq; rw [hy]; simp [negY, shortW]
  have hvD := hy0 hPn hP2
  have hvZ := hy0 hQn hQ2
  have hZF : val (ZF Ac Bc) ≠ 0 := by
    rw [val_ZF]; unfold ZZ; intro h; apply hΔ'; apply hinj
    simp only [map_add, map_mul, map_pow, map_ofNat, map_zero]; exact h
  have hbF : val (beF Ac Bc) ≠ 0 := by rw [val_beF hZF]; exact hβ
  have hisZ : ∀ {f : Fr K}, ok f → val f ≠ 0 → isZ f = false := fun hf h ↦ by
    rw [Bool.eq_false_iff]; intro h'; exact h ((isZ_iff hf).mp h')
  have hnz : ∀ {f : Fr K}, ok f → CPoly.isZero f.2 = false := fun hf ↦ by
    rw [Bool.eq_false_iff]; intro h'; exact hf ((CPoly.isZero_iff _).mp h')
  have hmuD : muOK Ac Bc uD vD = true := by
    simp [muOK, hnz ouD, hnz ovD, hisZ ovD hvD, hisZ ok_ZF hZF, hisZ (ok_beF hZF) hbF]
  have hmuZ : muOK Ac Bc uZ vZ = true := by
    simp [muOK, hnz ouZ, hnz ovZ, hisZ ovZ hvZ, hisZ ok_ZF hZF, hisZ (ok_beF hZF) hbF]
  have := cert_complete hM hRat hmuD hmuZ hPn hQn (fun m n T hT h ↦
    indep_tors (G := (sW (ι (CPoly.toPoly Ac)) (ι (CPoly.toPoly Bc))).toAffine.Point) _ _ hind m n T hT h)
  simpa [Differential.SuperData.manCertP, Differential.SuperData.manCertRP] using this

end Manin

