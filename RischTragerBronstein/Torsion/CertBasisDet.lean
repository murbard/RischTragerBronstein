import RischTragerBronstein.Torsion.CertBasis1

/-!
# Integral bases that are not triangular

`isIntBasis_of_special_det`: the version of `isIntBasis_of_special` for any basis with
`deg Bⱼ < n` and a non-zero determinant of the coefficient matrix (for example a basis normal at
infinity, which need not be triangular); the non-special points avoid the roots of that
determinant.
-/

open Polynomial HahnSeries

namespace Curves

open Differential LaurentSeries GTors

/-- `[pⱼ(vᵢ)] = V(v) · [coeff_k pⱼ]` for `deg pⱼ < n`. -/
lemma det_eval_general {R : Type*} [CommRing R] {n : ℕ} (p : Fin n → R[X])
    (hp : ∀ j, (p j).natDegree < n) (v : Fin n → R) :
    (Matrix.of fun i j ↦ (p j).eval (v i)).det =
      (Matrix.vandermonde v).det * (Matrix.of fun (k j : Fin n) ↦ (p j).coeff k).det := by
  rw [← Matrix.det_mul]
  congr 1
  ext i j
  rw [Matrix.of_apply, Matrix.mul_apply, eval_eq_sum_range' (hp j)]
  rw [← Fin.sum_univ_eq_sum_range (fun k ↦ (p j).coeff k * v i ^ k)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Matrix.vandermonde_apply, Matrix.of_apply, mul_comm]

section NS

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

variable [IsAlgClosed K]

theorem isIntBasis_of_special_det {B : Fin S.F.natDegree → C[X][X]} {D : C[X]}
    {δ : Fin S.F.natDegree → ℕ} (hD : D ≠ 0) (deg : ∀ j, (B j).natDegree < S.F.natDegree)
    (det : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det ≠ 0) (Sp : Finset K)
    (hcov : ∀ a, a ∉ Sp →
      resultant ((S.F.map (mapRingHom (algebraMap C K))).map (evalRingHom a))
        (derivative ((S.F.map (mapRingHom (algebraMap C K))).map (evalRingHom a)))
        S.F.natDegree (S.F.natDegree - 1) ≠ 0 ∧
      (D.map (algebraMap C K)).eval a ≠ 0 ∧
      ((Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det.map (algebraMap C K)).eval a ≠ 0)
    (hregSp : ∀ j, ∀ a ∈ Sp, ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      0 ≤ (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (S.fnWQ (B j) D)).order)
    (hindSp : ∀ a ∈ Sp, ∃ N, ∃ hN : 0 < N, ∃ r : Fin S.F.natDegree → LaurentSeries K,
      ∃ hs : S.F.map (branchSub N a) = ∏ k, (X - Polynomial.C (r k)),
        S.LocIndep (fun j ↦ S.fnWQ (B j) D) N hN a r hs)
    (hinf : ∀ j (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K)
      (hr : r ∈ l), LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
        (S.root_of_mem hl hr) (S.fnWQ (B j) D)) (-((N * δ j : ℕ) : ℤ)))
    (hindInf : ∃ N, ∃ hN : 0 < N, ∃ r : Fin S.F.natDegree → LaurentSeries K,
      ∃ hs : S.F.map (infSub N) = ∏ k, (X - Polynomial.C (r k)),
        S.LocIndepInf (fun j ↦ S.fnWQ (B j) D) δ N hN r hs) :
    S.IsIntBasis K B D δ := by
  classical
  set ι := algebraMap C K with hι
  refine ⟨hD, deg, det,
    fun j a N hN l hl r hr ↦ ?_, hinf, fun a ↦ ?_, hindInf⟩
  · by_cases ha : a ∈ Sp
    · exact hregSp j a ha N hN l hl r hr
    · have hDa := (hcov a ha).2.1
      have hN0 : 0 < N := Nat.pos_of_ne_zero hN
      have hD0 : D ≠ 0 := hD
      have hgD : (branchSub (C := C) N a D).order = 0 := by
        rw [order_branchSub N hN0 a D hD0, rootMultiplicity_eq_zero]
        · simp
        · exact hDa
      have hgD0 : branchSub (C := C) N a D ≠ 0 :=
        (map_ne_zero_iff _ (branchSub_injective N hN0 a)).mpr hD0
      rw [S.embG_fnWQ]
      by_cases hW : ((B j).map (branchSub N a)).eval r = 0
      · rw [hW, zero_mul, HahnSeries.order_zero]
      rw [HahnSeries.order_mul hW (inv_ne_zero hgD0), order_inv' _ hgD0, hgD, neg_zero, add_zero]
      have hroot := S.root_of_mem hl hr
      refine order_nonneg_of_lowerBd' _ ?_
      refine lowerBd_eval _ r 0 le_rfl (S.fin_root_lowerBd N a r hroot) 0 fun i ↦ ?_
      rw [coeff_map, zero_mul, sub_zero]
      exact lowerBd_branchSub_nonneg N a _
  · by_cases ha : a ∈ Sp
    · exact hindSp a ha
    obtain ⟨hres, hDa, hlead⟩ := hcov a ha
    set Fa := (S.F.map (mapRingHom ι)).map (evalRingHom a) with hFa
    have hFam : Fa.Monic := (S.monic.map _).map _
    have hFan : Fa.natDegree = S.F.natDegree := by
      rw [hFa, (S.monic.map (mapRingHom ι)).natDegree_map, S.monic.natDegree_map]
    obtain ⟨b, hbinj, hb⟩ := fibre_distinct_roots Fa hFam hFan S.natDegree_F_ne_zero hres
    obtain ⟨Y, hY, hs⟩ := split_unramified S.F S.monic a b hbinj (fun k ↦ (hb k).1)
      (fun k ↦ by
        rw [fibreAt, ← Polynomial.derivative_map, ← Polynomial.derivative_map]
        exact (hb k).2)
    refine ⟨1, one_pos, fun k ↦ ofPowerSeries ℤ K (Y k), hs, S.locIndep_unram B D a hDa Y hs ?_⟩
    have hY2 : ∀ k, PowerSeries.constantCoeff (Y k) = b k := fun k ↦ (hY k).2
    simp only [hY2]
    have := det_eval_general (fun j ↦ ((B j).map (mapRingHom ι)).map (evalRingHom a))
      (fun j ↦ lt_of_le_of_lt (natDegree_map_le.trans natDegree_map_le) (deg j)) b
    rw [show (Matrix.of fun k j ↦ Sup.evalW ((B j).map (mapRingHom ι)) a (b k)) =
      Matrix.of fun i j ↦ (((B j).map (mapRingHom ι)).map (evalRingHom a)).eval (b i) from rfl, this]
    refine mul_ne_zero ((Matrix.det_vandermonde_ne_zero_iff).mpr hbinj) ?_
    have e : (Matrix.of fun k j : Fin S.F.natDegree ↦
        (((B j).map (mapRingHom ι)).map (evalRingHom a)).coeff k) =
        ((evalRingHom a).comp (mapRingHom ι)).mapMatrix
          (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i) := by
      ext k j
      simp [coeff_map]
    rw [e, ← RingHom.map_det]
    simpa [eval_map, eval₂_at_apply] using hlead

end CurveData

end NS

end Curves
