import RischTragerBronstein.Torsion.TwoPrimesUnram

/-!
# Integral bases at non-special points (any characteristic)

* `coeff0_embG_fnWQ`: along an unramified branch through `(a, b)` with `D(a) ≠ 0`, the constant
  term of `W(x, y)/D(x)` is `W(a, b)/D(a)`;
* `det_triangular_eval`: for `Bⱼ` of `Y`-degree `≤ j`, `det [Bⱼ(a, b_k)] = V(b) ∏ⱼ Bⱼ,ⱼ(a)`;
* `locIndep_unram`: local independence along an unramified branch system when this determinant
  does not vanish;
* `fibre_distinct_roots`: if the discriminant does not vanish at `a`, the fibre `F(a, Y)` has
  `n` distinct simple roots (over an algebraically closed field).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

lemma det_triangular_eval {R : Type*} [CommRing R] {n : ℕ} (p : Fin n → R[X])
    (hp : ∀ j, (p j).natDegree ≤ j) (v : Fin n → R) :
    (Matrix.of fun i j ↦ (p j).eval (v i)).det =
      (Matrix.vandermonde v).det * ∏ j, (p j).coeff j := by
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials v p hp, Matrix.det_mul,
    Matrix.det_of_isUpperTriangular (Matrix.matrixOfPolynomials_isUpperTriangular p hp)]
  rfl

/-- **Distinct simple roots at non-special points.** -/
lemma fibre_distinct_roots {K : Type*} [Field K] [IsAlgClosed K] (Fa : K[X]) (hm : Fa.Monic)
    {n : ℕ} (hn : Fa.natDegree = n) (hn0 : n ≠ 0)
    (hres : resultant Fa (derivative Fa) n (n - 1) ≠ 0) :
    ∃ b : Fin n → K, Function.Injective b ∧ ∀ k, Fa.eval (b k) = 0 ∧
      (derivative Fa).eval (b k) ≠ 0 := by
  classical
  have hF0 : Fa ≠ 0 := hm.ne_zero
  have hsimple : ∀ b, Fa.IsRoot b → (derivative Fa).eval b ≠ 0 := by
    intro b hb hd
    obtain ⟨p, q, -, -, h⟩ := exists_mul_add_mul_eq_C_resultant Fa (derivative Fa) (m := n)
      (n := n - 1) hn.le (by rw [← hn]; exact natDegree_derivative_le Fa) (Or.inl hn0)
    have := congrArg (eval b) h
    rw [eval_add, eval_mul, eval_mul, hb.eq_zero, hd, eval_C] at this
    exact hres (by simpa using this.symm)
  have hnodup : Fa.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro b
    rw [count_roots]
    by_contra h
    push Not at h
    have := (one_lt_rootMultiplicity_iff_isRoot hF0).mp h
    exact hsimple b this.1 this.2
  have hcard : Fa.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnodup, IsAlgClosed.card_roots_eq_natDegree, hn]
  set e := Fa.roots.toFinset.equivFin with he
  refine ⟨fun k ↦ (e.symm (Fin.cast hcard.symm k) : K), fun a b h ↦ ?_, fun k ↦ ?_⟩
  · have := e.symm.injective (Subtype.ext h)
    exact Fin.cast_injective _ this
  · have hmem := (e.symm (Fin.cast hcard.symm k)).2
    rw [Multiset.mem_toFinset, mem_roots hF0] at hmem
    exact ⟨hmem, hsimple _ hmem⟩

section NS

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Constant terms along unramified branches.** -/
lemma coeff0_embG_fnWQ (W : C[X][X]) (D : C[X]) (a : K) (hDa : (D.map (algebraMap C K)).eval a ≠ 0)
    (Yp : PowerSeries K)
    (hY : (S.F.map (branchSub 1 a)).eval (ofPowerSeries ℤ K Yp) = 0) :
    (S.embG (branchSub 1 a) (branchSub_injective 1 one_pos a) (ofPowerSeries ℤ K Yp) hY
      (S.fnWQ W D)).coeff 0 =
      Sup.evalW (W.map (mapRingHom (algebraMap C K))) a (PowerSeries.constantCoeff Yp) *
        ((D.map (algebraMap C K)).eval a)⁻¹ := by
  set d := psSub (C := C) 1 a D with hd
  have hd0 : PowerSeries.constantCoeff d ≠ 0 := by rw [hd, coeff_zero_psSub]; exact hDa
  set t := (W.map (psSub 1 a)).eval Yp with ht
  have hbs : branchSub (C := C) 1 a D = ofPowerSeries ℤ K d := branchSub_eq_psSub 1 a D
  have hinv : (ofPowerSeries ℤ K d)⁻¹ = ofPowerSeries ℤ K d⁻¹ := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ ((map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr
      (fun h ↦ hd0 (by rw [h, map_zero])))]
    rw [← map_mul, PowerSeries.inv_mul_cancel _ hd0, map_one]
  rw [S.embG_fnWQ, eval_branchSub_ofPS, hbs, hinv, ← map_mul, coeff_ofPS, if_pos le_rfl,
    Int.toNat_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    PowerSeries.constantCoeff_inv, ← ht, constantCoeff_eval_psSub, hd, coeff_zero_psSub]

/-- **Local independence along an unramified system.** -/
theorem locIndep_unram (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (a : K)
    (hDa : (D.map (algebraMap C K)).eval a ≠ 0) (Y : Fin S.F.natDegree → PowerSeries K)
    (hs : S.F.map (branchSub 1 a) = ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K (Y k))))
    (hdet : (Matrix.of fun k j ↦ Sup.evalW ((B j).map (mapRingHom (algebraMap C K))) a
      (PowerSeries.constantCoeff (Y k))).det ≠ 0) :
    S.LocIndep (fun j ↦ S.fnWQ (B j) D) 1 one_pos a (fun k ↦ ofPowerSeries ℤ K (Y k)) hs := by
  intro c hc
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  funext k
  have h := hc k 0 one_pos
  rw [HahnSeries.coeff_sum] at h
  simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] at h
  simp only [S.coeff0_embG_fnWQ _ _ a hDa] at h
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
  have h2 : (∑ j, c j * (Sup.evalW ((B j).map (mapRingHom (algebraMap C K))) a
      (PowerSeries.constantCoeff (Y k)) * ((D.map (algebraMap C K)).eval a)⁻¹)) *
      (D.map (algebraMap C K)).eval a = 0 := by rw [h, zero_mul]
  rw [Finset.sum_mul] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  field_simp

variable [IsAlgClosed K]

/-- **Integral bases from their special points.** Away from a finite set of points (containing
the roots of the discriminant, of `D` and of the diagonal coefficients `B_{j,j}`), integrality and
local independence are automatic. -/
theorem isIntBasis_of_special {B : Fin S.F.natDegree → C[X][X]} {D : C[X]}
    {δ : Fin S.F.natDegree → ℕ} (hD : D ≠ 0) (tri : ∀ j, (B j).natDegree ≤ (j : ℕ))
    (lead : ∀ j, (B j).coeff j ≠ 0) (Sp : Finset K)
    (hcov : ∀ a, a ∉ Sp →
      resultant ((S.F.map (mapRingHom (algebraMap C K))).map (evalRingHom a))
        (derivative ((S.F.map (mapRingHom (algebraMap C K))).map (evalRingHom a)))
        S.F.natDegree (S.F.natDegree - 1) ≠ 0 ∧
      (D.map (algebraMap C K)).eval a ≠ 0 ∧ ∀ j, (((B j).coeff j).map (algebraMap C K)).eval a ≠ 0)
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
  refine ⟨hD, fun j ↦ lt_of_le_of_lt (tri j) j.2, CurveData.det_of_tri B tri lead,
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
    have := det_triangular_eval (fun j ↦ ((B j).map (mapRingHom ι)).map (evalRingHom a))
      (fun j ↦ (natDegree_map_le.trans natDegree_map_le).trans (tri j)) b
    rw [show (Matrix.of fun k j ↦ Sup.evalW ((B j).map (mapRingHom ι)) a (b k)) =
      Matrix.of fun i j ↦ (((B j).map (mapRingHom ι)).map (evalRingHom a)).eval (b i) from rfl, this]
    refine mul_ne_zero ((Matrix.det_vandermonde_ne_zero_iff).mpr hbinj)
      (Finset.prod_ne_zero_iff.mpr fun j _ ↦ ?_)
    rw [coeff_map, coeff_map]
    exact hlead j

end CurveData

end NS

end Curves
