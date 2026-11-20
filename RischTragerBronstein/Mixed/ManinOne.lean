import RischTragerBronstein.Mixed.ManinRep

/-!
# The one-point Manin certificate

`manCert1`: the Manin side conditions hold and `muC P ≠ 0`. **`nontors_of_manCert1`**: then `P` has
infinite order (torsion lies in the kernel of `mu`). **`manCert1_complete`**: under Manin's kernel
theorem `MKT`, every point of infinite order with `v ≠ 0` on a curve with non-constant `j` passes.
`manCert1P` / `nontors_of_manCert1P` / `manCert1P_exists`: the versions on represented code points.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Manin

open FFHeight FFHeight.Fr

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)

/-- **The one-point Manin check.** -/
def manCert1 (Ac Bc : CPoly K) (u v : Fr K) : Bool := muOK Ac Bc u v && !isZ (muC Ac Bc u v)

/-- On optional code points. -/
def manCert1P (Ac Bc : CPoly K) : PtC K → Bool
  | some (u, v) => manCert1 Ac Bc u v
  | none => false

open scoped Classical in
theorem nontors_of_manCert1P (Ac Bc : CPoly K) (o : PtC K)
    (P : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point) (hR : Rel _ _ o P)
    (hc : manCert1P Ac Bc o = true) (n : ℤ) (hn : n • P = 0) : n = 0 := by
  rcases o with _ | ⟨u, v⟩
  · simp [manCert1P] at hc
  rcases P with _ | ⟨x, y, hP⟩
  · simp [FFHeight.Rel] at hR
  obtain ⟨-, -, rfl, rfl⟩ := hR
  simp only [manCert1P, manCert1, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨h1, h2⟩ := hc
  obtain ⟨hu, hv, hv0, hZ, hb⟩ := of_muOK h1
  have hΔ : 4 * ι (CPoly.toPoly Ac) ^ 3 + 27 * ι (CPoly.toPoly Bc) ^ 2 ≠ 0 := by
    rw [val_ZF] at hZ; exact hZ
  have okm := ok_muC hZ hb hu hv0
  have hmu : mu dX (ι (CPoly.toPoly Ac)) (ι (CPoly.toPoly Bc)) (Point.some _ _ hP) ≠ 0 := by
    rw [← val_muC hZ hb hu hv hv0 hP]
    intro h0; rw [← isZ_iff okm] at h0; rw [h0] at h2; exact Bool.false_ne_true h2.symm
  by_contra hn0
  apply hmu
  have h := congrArg (muHom dX hΔ) (show n • (Point.some _ _ hP :
    (sW (ι (CPoly.toPoly Ac)) (ι (CPoly.toPoly Bc))).toAffine.Point) = 0 from hn)
  rw [map_zsmul, map_zero, zsmul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn0)

open scoped Classical in
/-- **The one-point Manin certificate exists, given `MKT`.** -/
theorem manCert1P_exists (hM : MKT K) (Ac Bc : CPoly K)
    (hΔ' : 4 * CPoly.toPoly Ac ^ 3 + 27 * CPoly.toPoly Bc ^ 2 ≠ 0)
    (hβ : bt dX (ι (CPoly.toPoly Ac)) (ι (CPoly.toPoly Bc)) ≠ 0) (o : PtC K)
    (P : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point) (hR : Rel _ _ o P)
    (hP : ∀ n : ℤ, n • P = 0 → n = 0) : manCert1P Ac Bc o = true := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hP2 : P + P ≠ 0 := fun h ↦ by
    have := hP 2 (by rw [two_zsmul, h]); omega
  rcases o with _ | ⟨u, v⟩
  · rcases P with _ | ⟨x, y, h⟩
    · exact absurd rfl hP2
    · simp [FFHeight.Rel] at hR
  rcases P with _ | ⟨x, y, hPn⟩
  · simp [FFHeight.Rel] at hR
  obtain ⟨ou, ov, rfl, rfl⟩ := hR
  have hv0 : val v ≠ 0 := fun hy ↦ by
    apply hP2; apply Point.add_self_of_Y_eq; rw [hy]; simp [negY, shortW]
  have hZF : val (ZF Ac Bc) ≠ 0 := by
    rw [val_ZF]; unfold ZZ; intro h; apply hΔ'; apply hinj
    simp only [map_add, map_mul, map_pow, map_ofNat, map_zero]; exact h
  have hbF : val (beF Ac Bc) ≠ 0 := by rw [val_beF hZF]; exact hβ
  have hisZ : ∀ {f : Fr K}, ok f → val f ≠ 0 → isZ f = false := fun hf h ↦ by
    rw [Bool.eq_false_iff]; intro h'; exact h ((isZ_iff hf).mp h')
  have hnz : ∀ {f : Fr K}, ok f → CPoly.isZero f.2 = false := fun hf ↦ by
    rw [Bool.eq_false_iff]; intro h'; exact hf ((CPoly.isZero_iff _).mp h')
  have hmuOK : muOK Ac Bc u v = true := by
    simp [muOK, hnz ou, hnz ov, hisZ ov hv0, hisZ ok_ZF hZF, hisZ (ok_beF hZF) hbF]
  have hΔ : 4 * ι (CPoly.toPoly Ac) ^ 3 + 27 * ι (CPoly.toPoly Bc) ^ 2 ≠ 0 := by
    rw [val_ZF] at hZF; exact hZF
  have okm := ok_muC hZF hbF ou hv0
  have hmu : mu dX (ι (CPoly.toPoly Ac)) (ι (CPoly.toPoly Bc)) (Point.some _ _ hPn) ≠ 0 := by
    intro h0
    obtain ⟨n, hn, hnP⟩ := hM _ _ hΔ hβ _ h0
    have := hP n (by rw [natCast_zsmul]; exact hnP)
    omega
  simp only [manCert1P, manCert1, hmuOK, Bool.true_and, Bool.not_eq_true']
  rw [Bool.eq_false_iff]; intro h'
  apply hmu; rw [← val_muC hZF hbF ou ov hv0 hPn]; exact (isZ_iff okm).mp h'

end Manin

