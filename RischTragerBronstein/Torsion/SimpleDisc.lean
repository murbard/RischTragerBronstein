import RischTragerBronstein.Torsion.CertBasisDet
import RischTragerBronstein.Torsion.RamPrime
import RischTragerBronstein.Curves.Puiseux

/-!
# Local independence at simple roots of the discriminant

If the discriminant `R = Res_Y(F, F_Y)` vanishes to order at most `1` at `a`, and `D(a) ≠ 0`,
`det [Bⱼ,ᵢ](a) ≠ 0`, then `Bⱼ/D` are locally independent along **every** Puiseux system above `a`
(`locIndep_of_mult_le_one`): with `F(a + Tᴺ, Y) = ∏ₖ (Y − rₖ)`, `∑ₖ ord f′(rₖ) = N · mult ≤ N`
and each pair `(k, j)` is counted twice, so `ord f′(rₖ) ≤ N/2`; Lagrange interpolation at the
`rₖ` then forces every coefficient of `∑ⱼ cⱼ Bⱼ(a, Y)` to have positive order, i.e. to vanish
(a Dedekind-type criterion). No branch certificate is needed at such points.
-/

open Polynomial HahnSeries Finset

namespace Curves

open Differential LaurentSeries GTors

section Aux

variable {K : Type*} [Field K]

lemma order_prod_ls {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries K) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).order = ∑ i ∈ s, (f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, HahnSeries.order_mul (hf i (mem_insert_self _ _))
      (prod_ne_zero_iff.mpr fun j hj ↦ hf j (mem_insert_of_mem hj)),
      ih fun j hj ↦ hf j (mem_insert_of_mem hj)]

lemma lowerBd_coeff_nodal {ι : Type*} (s : Finset ι) (r : ι → LaurentSeries K)
    (hr : ∀ i, LowerBd (r i) 0) : ∀ m, LowerBd ((Lagrange.nodal s r).coeff m) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m
    rw [Lagrange.nodal_empty, Polynomial.coeff_one]
    split_ifs
    · exact fun k hk ↦ by simp [HahnSeries.coeff_one, hk.ne]
    · exact lowerBd_zero 0
  | insert i s hi ih =>
    intro m
    rw [Lagrange.nodal_insert_eq_nodal hi, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rcases m with _ | m
    · rw [coeff_X_mul_zero, zero_sub]; exact ((hr i).mul (ih 0)).neg
    · rw [coeff_X_mul]; exact (ih m).sub ((hr i).mul (ih (m + 1)))

lemma lowerBd_C0 (v : K) : LowerBd (HahnSeries.C v : LaurentSeries K) 0 := fun k hk ↦ by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hk.ne]

lemma order_nonneg_of_lowerBd0 {z : LaurentSeries K} (hz : z ≠ 0) (h : LowerBd z 0) :
    0 ≤ z.order := by
  by_contra hlt
  push Not at hlt
  exact (HahnSeries.coeff_order_eq_zero.not.mpr hz) (h _ hlt)

/-- **Each node takes at most half of the discriminant.** -/
lemma two_mul_order_nodal_le {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → LaurentSeries K)
    (hr : ∀ i, LowerBd (r i) 0) (hne : ∀ i j, i ≠ j → r i ≠ r j) (i : ι) :
    2 * (∏ j ∈ univ.erase i, (r i - r j)).order ≤
      ∑ k, (∏ j ∈ univ.erase k, (r k - r j)).order := by
  have hd : ∀ k j, j ∈ univ.erase k → r k - r j ≠ 0 := fun k j hj ↦
    sub_ne_zero.mpr (hne k j (ne_of_mem_erase hj).symm)
  have hP : ∀ k, (∏ j ∈ univ.erase k, (r k - r j)).order =
      ∑ j ∈ univ.erase k, (r k - r j).order := fun k ↦ order_prod_ls _ _ (hd k)
  have ho : ∀ k j, j ∈ univ.erase k → 0 ≤ (r k - r j).order := fun k j hj ↦
    order_nonneg_of_lowerBd0 (hd k j hj) ((hr k).sub (hr j))
  rw [← add_sum_erase _ _ (mem_univ i), two_mul, add_le_add_iff_left]
  calc (∏ j ∈ univ.erase i, (r i - r j)).order
      = ∑ k ∈ univ.erase i, (r k - r i).order := by
        rw [hP]
        refine sum_congr rfl fun k _ ↦ ?_
        rw [← neg_sub, HahnSeries.order_neg]
    _ ≤ ∑ k ∈ univ.erase i, (∏ j ∈ univ.erase k, (r k - r j)).order := by
        refine sum_le_sum fun k hk ↦ ?_
        rw [hP]
        exact single_le_sum (fun j hj ↦ ho k j hj)
          (mem_erase.mpr ⟨(ne_of_mem_erase hk).symm, mem_univ i⟩)

variable {C : Type*} [Field C] [Algebra C K]

/-- `P(a + Tᴺ) − P(a)` has no terms below `Tᴺ`. -/
lemma lowerBd_branchSub_sub (N : ℕ) (hN : 0 < N) (a : K) (P : C[X]) :
    LowerBd (branchSub N a P - HahnSeries.C ((P.map (algebraMap C K)).eval a)) N := by
  set Q := P.map (algebraMap C K) with hQ
  have hc : Q.comp (Polynomial.C a + X ^ N) = expand K N (taylor a Q) := by
    rw [expand_eq_comp_X_pow, taylor_apply, comp_assoc, add_comp, X_comp, C_comp, add_comm]
  intro k hk
  rw [HahnSeries.coeff_sub, branchSub_apply, ← hQ, hc, coeff_ofPS, HahnSeries.C_apply]
  rcases lt_or_ge k 0 with hk0 | hk0
  · rw [if_neg (not_le.mpr hk0), HahnSeries.coeff_single_of_ne hk0.ne, sub_zero]
  rw [if_pos hk0, Polynomial.coeff_coe]
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  rw [Int.toNat_natCast, coeff_expand hN]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [taylor_coeff_zero]
  · have hmN : m < N := by exact_mod_cast hk
    rw [if_neg (Nat.not_dvd_of_pos_of_lt hm hmN),
      HahnSeries.coeff_single_of_ne (by exact_mod_cast hm.ne'), sub_zero]

lemma ex_comp_psSubR_sd (N : ℕ) (hN : N ≠ 0) (a : K) :
    (Puiseux.ex N).comp (psSubR 1 a) = psSubR N a := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · simp [psSubR, Puiseux.ex_C]
  · simp [psSubR, Puiseux.ex_apply hN, PowerSeries.expand_X, PowerSeries.expand_C]

/-- The roots of `G(a + Tᴺ, Y)` (Newton–Puiseux; as `exists_roots`). -/
lemma exists_roots_sd [IsAlgClosed K] [CharZero K] (G : K[X][X]) (hmon : G.Monic) (n : ℕ)
    (hdeg : G.natDegree = n) (a : K) :
    ∃ N, N ≠ 0 ∧ ∃ l : List (PowerSeries K), l.length = n ∧
      G.map (psSubR N a) = (l.map fun r ↦ X - Polynomial.C r).prod := by
  have hHm : (G.map (psSubR 1 a)).Monic := hmon.map _
  have hHd : (G.map (psSubR 1 a)).natDegree = n := by rw [hmon.natDegree_map, hdeg]
  obtain ⟨N, hN, l, hl, h⟩ := Puiseux.puiseux_split n _ hHm hHd
  refine ⟨N, hN, l, hl, ?_⟩
  rw [← h, Polynomial.map_map, ex_comp_psSubR_sd N hN]

end Aux

section Main

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Local independence where the discriminant vanishes to order `≤ 1`.** -/
theorem locIndep_of_mult_le_one (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (a : K)
    (deg : ∀ j, (B j).natDegree < S.F.natDegree)
    (hDa : (D.map (algebraMap C K)).eval a ≠ 0)
    (hdet : ((Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det.map
      (algebraMap C K)).eval a ≠ 0)
    (hR : resultant S.F (derivative S.F) S.F.natDegree (S.F.natDegree - 1) ≠ 0)
    (hm : ((resultant S.F (derivative S.F) S.F.natDegree (S.F.natDegree - 1)).map
      (algebraMap C K)).rootMultiplicity a ≤ 1)
    (N : ℕ) (hN : 0 < N) (r : Fin S.F.natDegree → LaurentSeries K) (hr : ∀ k, LowerBd (r k) 0)
    (hs : S.F.map (branchSub N a) = ∏ k, (X - Polynomial.C (r k))) :
    S.LocIndep (fun j ↦ S.fnWQ (B j) D) N hN a r hs := by
  classical
  set ι := algebraMap C K with hι
  set g : C[X] →+* LaurentSeries K := branchSub N a with hgdef
  set R := resultant S.F (derivative S.F) S.F.natDegree (S.F.natDegree - 1) with hRdef
  set P : Fin S.F.natDegree → LaurentSeries K := fun k ↦ ∏ j ∈ univ.erase k, (r k - r j) with hPdef
  -- the nodes and the discriminant
  have hdegf : (∏ k, (X - Polynomial.C (r k))).natDegree = S.F.natDegree := by
    rw [← hs, S.monic.natDegree_map]
  have hPk : ∀ k, (derivative (∏ k, (X - Polynomial.C (r k)))).eval (r k) = P k := fun k ↦ by
    have := Lagrange.eval_nodal_derivative_eval_node_eq (s := univ) (v := r) (mem_univ k)
    rw [Lagrange.eval_nodal] at this
    exact this
  have hprodP : ∏ k, P k = g R := by
    have h1 : resultant (S.F.map g) (derivative (S.F.map g)) S.F.natDegree
        (S.F.natDegree - 1) = g R := by
      rw [Polynomial.derivative_map, resultant_map_map]
    rw [hs] at h1
    have hd' : (derivative (∏ k, (X - Polynomial.C (r k)))).natDegree ≤ S.F.natDegree - 1 :=
      (natDegree_derivative_le _).trans (by rw [hdegf])
    have h2 := resultant_prod_left (univ : Finset (Fin S.F.natDegree))
      (fun k ↦ X - Polynomial.C (r k)) _ _ (by simp) hd'
    rw [hdegf] at h2
    rw [← h1, h2]
    refine prod_congr rfl fun k _ ↦ ?_
    rw [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ hd', hPk]
  have hgR : g R ≠ 0 := (map_ne_zero_iff _ (branchSub_injective N hN a)).mpr hR
  have hP0 : ∀ k, P k ≠ 0 := fun k h0 ↦
    hgR (by rw [← hprodP]; exact prod_eq_zero (mem_univ k) h0)
  have hne : ∀ i j, i ≠ j → r i ≠ r j := fun i j hij h ↦
    hP0 i (prod_eq_zero (mem_erase.mpr ⟨hij.symm, mem_univ j⟩) (by rw [h, sub_self]))
  have hord : ∀ k, 2 * (P k).order ≤ N := by
    intro k
    have h2 := two_mul_order_nodal_le r hr hne k
    rw [← order_prod_ls _ _ fun k _ ↦ hP0 k] at h2
    change 2 * (P k).order ≤ (∏ k, P k).order at h2
    rw [hprodP, hgdef, order_branchSub N hN a R hR] at h2
    refine h2.trans ?_
    have : N * (R.map ι).rootMultiplicity a ≤ N := by nlinarith
    exact_mod_cast this
  intro c hc
  set Lc : K →+* LaurentSeries K := HahnSeries.C with hLc
  set WL : (LaurentSeries K)[X] := ∑ j, Polynomial.C (Lc (c j)) *
    (((B j).map (mapRingHom ι)).map (evalRingHom a)).map Lc with hWL
  have hcoef : ∀ m, WL.coeff m = Lc (∑ j, c j * (((B j).coeff m).map ι).eval a) := by
    intro m
    simp only [hWL, finset_sum_coeff, coeff_C_mul, coeff_map, map_sum, map_mul]
    rfl
  -- the values at the nodes
  have hval : ∀ k, LowerBd (WL.eval (r k)) N := by
    intro k
    have h := hc k
    simp only [S.embG_fnWQ] at h
    set V := ∑ j, Lc (c j) * ((B j).map g).eval (r k) with hV
    have hgD : g D ≠ 0 := (map_ne_zero_iff _ (branchSub_injective N hN a)).mpr
      (fun h0 ↦ hDa (by rw [h0, Polynomial.map_zero, eval_zero]))
    have e : ∑ j, HahnSeries.C (c j) * (((B j).map g).eval (r k) * (g D)⁻¹) = V * (g D)⁻¹ := by
      rw [hV, sum_mul]
      exact sum_congr rfl fun j _ ↦ (mul_assoc _ _ _).symm
    rw [e] at h
    have hVN : LowerBd V N := by
      have := h.mul (lowerBd_branchSub_nonneg (C := C) N a D)
      rw [add_zero, mul_assoc, inv_mul_cancel₀ hgD, mul_one] at this
      exact this
    have hdiff : LowerBd (V - WL.eval (r k)) N := by
      rw [hV, hWL, eval_finset_sum, ← sum_sub_distrib]
      refine lowerBd_sum _ _ fun j _ ↦ ?_
      rw [eval_mul, eval_C, ← mul_sub, ← eval_sub]
      have hE := lowerBd_eval ((B j).map g -
        (((B j).map (mapRingHom ι)).map (evalRingHom a)).map Lc) (r k) 0 le_rfl (hr k) N
        fun i ↦ by
          rw [zero_mul, sub_zero, Polynomial.coeff_sub, coeff_map, coeff_map, coeff_map,
            coeff_map]
          exact lowerBd_branchSub_sub N hN a _
      have := (lowerBd_C0 (c j)).mul hE
      rwa [zero_add] at this
    have := hVN.sub hdiff
    rwa [sub_sub_cancel] at this
  -- the interpolation
  have hWdeg : WL.degree < (univ : Finset (Fin S.F.natDegree)).card := by
    rw [card_univ, Fintype.card_fin]
    refine (degree_lt_iff_coeff_zero _ _).mpr fun m hm ↦ ?_
    rw [hcoef, sum_eq_zero fun j _ ↦ ?_, map_zero]
    rw [coeff_eq_zero_of_natDegree_lt ((deg j).trans_le hm), Polynomial.map_zero, eval_zero,
      mul_zero]
  have hinj : Set.InjOn r (univ : Finset (Fin S.F.natDegree)) := fun i _ j _ h ↦ by
    by_contra hij; exact hne i j hij h
  have hL := Lagrange.eq_interpolate hinj hWdeg
  have hbasis : ∀ i, Lagrange.basis univ r i =
      Polynomial.C (P i)⁻¹ * Lagrange.nodal (univ.erase i) r := fun i ↦ by
    simp_rw [Lagrange.basis, Lagrange.basisDivisor, prod_mul_distrib, ← map_prod,
      prod_inv_distrib]
    rfl
  have hlow : ∀ m, LowerBd (WL.coeff m) 1 := by
    intro m
    rw [hL, Lagrange.interpolate_apply, finset_sum_coeff]
    refine lowerBd_sum _ _ fun i _ ↦ ?_
    rw [hbasis, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul]
    have := (hval i).mul ((lowerBd_inv (P i) (hP0 i)).mul (lowerBd_coeff_nodal (univ.erase i) r hr m))
    rw [mul_assoc]
    refine LowerBd.mono (m' := 1) this ?_
    have := hord i
    omega
  -- the coefficients vanish
  have hMdet : (Matrix.of fun (i j : Fin S.F.natDegree) ↦
      (((B j).coeff i).map ι).eval a).det ≠ 0 := by
    have e : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (((B j).coeff i).map ι).eval a) =
        ((evalRingHom a).comp (mapRingHom ι)).mapMatrix
          (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i) := by
      ext i j
      simp
    rw [e, ← RingHom.map_det]
    simpa using hdet
  apply Matrix.eq_zero_of_mulVec_eq_zero hMdet
  funext i
  have h0 := hlow i 0 one_pos
  rw [hcoef, hLc, HahnSeries.C_apply, HahnSeries.coeff_single_same] at h0
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
  rw [← h0]
  exact sum_congr rfl fun j _ ↦ mul_comm _ _

/-- **A Puiseux system at any point** (Fin-indexed). -/
lemma exists_fin_split [IsAlgClosed K] [CharZero K] (a : K) :
    ∃ N, ∃ hN : 0 < N, ∃ r : Fin S.F.natDegree → LaurentSeries K, (∀ k, LowerBd (r k) 0) ∧
      S.F.map (branchSub N a) = ∏ k, (X - Polynomial.C (r k)) := by
  obtain ⟨N, hN, l, hl, h⟩ := exists_roots_sd (S.F.map (mapRingHom (algebraMap C K)))
    (S.monic.map _) S.F.natDegree (S.monic.natDegree_map _) a
  refine ⟨N, Nat.pos_of_ne_zero hN,
    fun k ↦ ofPowerSeries ℤ K (l[(k : ℕ)]'(by rw [hl]; exact k.2)), fun k ↦ lowerBd_ofPS _, ?_⟩
  have e1 : S.F.map (branchSub N a) =
      ((S.F.map (mapRingHom (algebraMap C K))).map (psSubR N a)).map (ofPowerSeries ℤ K) := by
    rw [Polynomial.map_map, Polynomial.map_map]; rfl
  rw [e1, h, Polynomial.map_list_prod, List.map_map, ← Fin.prod_univ_fun_getElem]
  exact Fintype.prod_equiv (finCongr hl) _ _ (fun i ↦ by simp)

/-- **Integral bases from their special points, simple discriminant roots allowed.** Outside
`Sp` it suffices that the discriminant vanishes to order `≤ 1` and `D`, `det [Bⱼ,ᵢ]` do not
vanish. -/
theorem isIntBasis_of_special_simple [IsAlgClosed K] [CharZero K] {B : Fin S.F.natDegree → C[X][X]}
    {D : C[X]} {δ : Fin S.F.natDegree → ℕ} (hD : D ≠ 0) (deg : ∀ j, (B j).natDegree < S.F.natDegree)
    (det : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det ≠ 0)
    (hR : resultant S.F (derivative S.F) S.F.natDegree (S.F.natDegree - 1) ≠ 0) (Sp : Finset K)
    (hcov : ∀ a, a ∉ Sp →
      ((resultant S.F (derivative S.F) S.F.natDegree (S.F.natDegree - 1)).map
        (algebraMap C K)).rootMultiplicity a ≤ 1 ∧
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
  refine ⟨hD, deg, det, fun j a N hN l hl r hr ↦ ?_, hinf, fun a ↦ ?_, hindInf⟩
  · by_cases ha : a ∈ Sp
    · exact hregSp j a ha N hN l hl r hr
    · have hDa := (hcov a ha).2.1
      have hN0 : 0 < N := Nat.pos_of_ne_zero hN
      have hgD : (branchSub (C := C) N a D).order = 0 := by
        rw [order_branchSub N hN0 a D hD, rootMultiplicity_eq_zero]
        · simp
        · exact hDa
      have hgD0 : branchSub (C := C) N a D ≠ 0 :=
        (map_ne_zero_iff _ (branchSub_injective N hN0 a)).mpr hD
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
    obtain ⟨hm, hDa, hdet⟩ := hcov a ha
    obtain ⟨N, hN, r, hr, hs⟩ := S.exists_fin_split a
    exact ⟨N, hN, r, hs, S.locIndep_of_mult_le_one B D a deg hDa hdet hR hm N hN r hr hs⟩

end CurveData

end Main

end Curves
