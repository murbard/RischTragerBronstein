import RischTragerBronstein.Mixed.CurveRdeSound
import RischTragerBronstein.Mixed.RdeBounds
import RischTragerBronstein.Computable.NestMRde0

/-!
# The parametric Risch equation on a curve: completeness

**`curveRde_complete`**: every solution `z ∈ Kc⟮x⟯⟮y⟯` of `z′ + h′ z = ∑ cⱼ wⱼ` with constant
`cⱼ ∈ Kc` is a constant combination of the solutions returned by `curveRde`, compatibly with the
parameters. The solution lies in the ansatz space (`rde_ansatz`); the resulting relation among
the values of the columns is a polynomial identity of `y`-degree `< n`, hence (irreducibility of
`F`) a relation among the columns, and `nullBasis` is complete over every extension.
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup

section Complete

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero E] in
lemma evRH_eq_evXY (V : ℚ[X][X]) :
    evRH S V = S.evXY (V.map (mapRingHom (algebraMap ℚ Kc))) := by
  simp [evRH, CurveData.evXY, Polynomial.map_map]

/-- Values of curve codes lie in the function field. -/
lemma sem_mem (a : GPoly (GFrac ℚ)) : (cM hC S hx Fc hSF).sem a ∈ Kc⟮S.x⟯⟮S.y⟯ := by
  have hQ := aeval_codeQ_ne_zero S a
  have h := eval_codeW hC S hx Fc hSF a
  rw [← evRH_toB S, evRH_eq_evXY] at h
  have : (cM hC S hx Fc hSF).sem a =
      S.evXY (((toB (codeW a))).map (mapRingHom (algebraMap ℚ Kc))) /
        aeval S.x ((toPoly (codeQ a)).map (algebraMap ℚ Kc)) := by
    rw [h]; field_simp
  rw [this]
  exact div_mem (S.evXY_mem _) (S.aeval_mem _)

include hSF in
omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero E] in
lemma coeff_F_natDegree_le (i : ℕ) : (S.F.coeff i).natDegree ≤ cvK Fc := by
  rw [hSF, coeff_map, coe_mapRingHom, natDegree_map_eq_of_injective (algebraMap ℚ Kc).injective,
    coeff_toB]
  refine (natDegree_toPoly_le_length _).trans ?_
  by_cases hi : i < Fc.length
  · have hmem : (Fc.getD i []).length - 1 ∈ Fc.map fun c ↦ c.length - 1 := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.mem_map_of_mem (List.getElem_mem hi)
    exact le_foldr_max_self hmem
  · rw [List.getD_eq_default _ _ (by omega)]; simp

include hSF in
omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero E] in
lemma degB_le : S.degB ≤ cvDegB Fc := by
  set g : ℕ → ℕ := fun i ↦ (Fc.getD i []).length - 1 with hg
  have hlist : ∀ L : BPoly ℚ, (L.map fun c ↦ c.length - 1).sum =
      ∑ i ∈ Finset.range L.length, ((L.getD i []).length - 1) := by
    intro L
    induction L with
    | nil => simp
    | cons c L ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']; simp [add_comm]
  have hf : ∀ i, (S.F.coeff i).natDegree ≤ g i := fun i ↦ by
    rw [hSF, coeff_map, coe_mapRingHom, natDegree_map_eq_of_injective (algebraMap ℚ Kc).injective,
      coeff_toB]
    exact natDegree_toPoly_le_length _
  have hz : ∀ i, Fc.length ≤ i → g i = 0 := fun i hi ↦ by
    rw [hg]; simp only; rw [List.getD_eq_default _ _ hi]; rfl
  rw [CurveData.degB, cvDegB, hlist]
  calc ∑ i ∈ Finset.range (S.F.natDegree + 1), (S.F.coeff i).natDegree
      ≤ ∑ i ∈ Finset.range (S.F.natDegree + 1), g i := Finset.sum_le_sum fun i _ ↦ hf i
    _ ≤ ∑ i ∈ Finset.range (S.F.natDegree + 1 + Fc.length), g i :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    _ = ∑ i ∈ Finset.range Fc.length, g i := by
        rw [add_comm, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range (S.F.natDegree + 1))
          (f := fun x ↦ g (Fc.length + x)) (fun x _ ↦ hz _ (by omega)), add_zero]

variable (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)

include hSF hmon hdeg in
omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero E] in
lemma natDegree_F_cvN : S.F.natDegree = cvN Fc := by
  rw [hSF, hmon.natDegree_map, hdeg]

include hSF hmon hdeg in
omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero E] in
lemma discR_eq_cv :
    S.discR = (toPoly (discRC Fc (cvN Fc) (cvK Fc))).map (algebraMap ℚ Kc) := by
  have hk : ∀ i, ((toB Fc).coeff i).natDegree ≤ cvK Fc := fun i ↦ by
    have := coeff_F_natDegree_le S Fc hSF i
    rwa [hSF, coeff_map, coe_mapRingHom,
      natDegree_map_eq_of_injective (algebraMap ℚ Kc).injective] at this
  rw [toPoly_discRC Fc (cvN Fc) (cvK Fc) hmon hdeg hk, CurveData.discR,
    natDegree_F_cvN S Fc hSF hmon hdeg, hSF, derivative_map, resultant_map_map]
  rfl

omit [CharZero Kc] in
lemma boundDW_ge (k : ℕ) (V : BPoly ℚ) (i : ℕ) (hi : i < V.length) :
    (V.getD i []).length - 1 + k * i ≤ boundDW k V := by
  unfold boundDW
  exact le_foldr_max_self (List.mem_map_of_mem (f := fun i ↦ (V.getD i []).length - 1 + k * i)
    (List.mem_range.mpr hi))

omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero E] in
lemma evXY_sum_CC {ι : Type*} (s : Finset ι) (c : ι → Kc) (V : ι → Kc[X][X]) :
    S.evXY (∑ j ∈ s, Polynomial.C (Polynomial.C (c j)) * V j) =
      ∑ j ∈ s, algebraMap Kc E (c j) * S.evXY (V j) := by
  simp [CurveData.evXY, Polynomial.map_sum, eval_finset_sum]

/-- **The right-hand side over the common denominator.** -/
lemma rhs_repr (ws : List (GPoly (GFrac ℚ))) (c : List Kc) :
    (∑ j ∈ Finset.range ws.length, algebraMap Kc E (c.getD j 0) *
        (cM hC S hx Fc hSF).sem (ws.getD j [])) *
      aeval S.x ((toPoly (prodQs (ws.map fun w ↦ fracOf (cvRed Fc w)))).map (algebraMap ℚ Kc)) =
    S.evXY (∑ j ∈ Finset.range ws.length, Polynomial.C (Polynomial.C (c.getD j 0)) *
      (toB ((scaledWs (ws.map fun w ↦ fracOf (cvRed Fc w))).getD j [])).map
        (mapRingHom (algebraMap ℚ Kc))) := by
  rw [evXY_sum_CC, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [← evRH_eq_evXY, evRH_scaled hC S hx Fc hSF ws j (Finset.mem_range.mp hj), evRH_C]
  ring

omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero E] in
/-- **The degree bound of the right-hand side.** -/
lemma rhs_bound (Vw : List (BPoly ℚ)) (c : List Kc) (i : ℕ)
    (hi : (∑ j ∈ Finset.range Vw.length, Polynomial.C (Polynomial.C (c.getD j 0)) *
      (toB (Vw.getD j [])).map (mapRingHom (algebraMap ℚ Kc))).coeff i ≠ 0) :
    ((∑ j ∈ Finset.range Vw.length, Polynomial.C (Polynomial.C (c.getD j 0)) *
      (toB (Vw.getD j [])).map (mapRingHom (algebraMap ℚ Kc))).coeff i).natDegree + cvK Fc * i ≤
      (Vw.map (boundDW (cvK Fc))).foldr max 0 := by
  set DW := (Vw.map (boundDW (cvK Fc))).foldr max 0
  have hcoef : (∑ j ∈ Finset.range Vw.length, Polynomial.C (Polynomial.C (c.getD j 0)) *
      (toB (Vw.getD j [])).map (mapRingHom (algebraMap ℚ Kc))).coeff i =
      ∑ j ∈ Finset.range Vw.length, Polynomial.C (c.getD j 0) *
        (toPoly ((Vw.getD j []).getD i [])).map (algebraMap ℚ Kc) := by
    rw [finsetSum_coeff]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [coeff_C_mul, coeff_map, coeff_toB, coe_mapRingHom]
  have hB : ∀ j < Vw.length, boundDW (cvK Fc) (Vw.getD j []) ≤ DW := fun j hj ↦ by
    refine le_foldr_max_self (List.mem_map_of_mem ?_)
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  rw [hcoef] at hi ⊢
  obtain ⟨j0, hj0, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hj0' := Finset.mem_range.mp hj0
  have hi0 : i < (Vw.getD j0 []).length := by
    by_contra hge
    rw [List.getD_eq_default (Vw.getD j0 []) [] (by omega)] at hne
    simp [CPoly.toPoly] at hne
  have hki : cvK Fc * i ≤ DW :=
    (Nat.le_add_left _ _).trans ((boundDW_ge (cvK Fc) _ i hi0).trans (hB j0 hj0'))
  suffices h : (∑ j ∈ Finset.range Vw.length, Polynomial.C (c.getD j 0) *
      (toPoly ((Vw.getD j []).getD i [])).map (algebraMap ℚ Kc)).natDegree ≤ DW - cvK Fc * i by
    omega
  refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_map_eq_of_injective (algebraMap ℚ Kc).injective]
  by_cases hij : i < (Vw.getD j []).length
  · have := boundDW_ge (cvK Fc) _ i hij
    have := hB j hj'
    have := natDegree_toPoly_le_length ((Vw.getD j []).getD i [])
    omega
  · rw [List.getD_eq_default (Vw.getD j []) [] (by omega)]; simp [CPoly.toPoly]

/-- **A function of the ansatz space as a combination of the basis elements.** -/
lemma z_expand (den : CPoly ℚ) (D : Kc[X]) (hden : (toPoly den).map (algebraMap ℚ Kc) = D)
    (hD0 : aeval S.x D ≠ 0) (Wz : Kc[X][X]) (n Eb : ℕ) (hn : Wz.natDegree < n)
    (hc : ∀ j, (Wz.coeff j).natDegree ≤ Eb) (z : E) (hz : z * aeval S.x D = S.evXY Wz) :
    z = ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range (Eb + 1),
      algebraMap Kc E ((Wz.coeff i).coeff e) * (cM hC S hx Fc hSF).sem (bcode den i e) := by
  have hz' : z = S.evXY Wz / aeval S.x D := by rw [← hz]; field_simp
  rw [hz']
  have hW : S.evXY Wz = ∑ i ∈ Finset.range n, aeval S.x (Wz.coeff i) * S.y ^ i := by
    rw [CurveData.evXY, eval_eq_sum_range' (n := n) (lt_of_le_of_lt natDegree_map_le hn)]
    simp [coeff_map]
  rw [hW, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [aeval_eq_sum_range' (n := Eb + 1) (by have := hc i; omega), Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [sem_bcode, hden, Algebra.smul_def]
  field_simp

omit [CharZero Kc] in
lemma natDegree_toB_le : ∀ V : BPoly ℚ, (toB V).natDegree ≤ V.length - 1
  | [] => by simp
  | [c] => by simp
  | c :: d :: V => by
    have ih := natDegree_toB_le (d :: V)
    rw [toB_cons, List.length_cons, Nat.add_sub_cancel]
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_X]
    simp only [List.length_cons, Nat.add_sub_cancel] at ih ⊢; omega

/-- **A relation among the values is a relation among the columns.** -/
lemma lcombS_zero_of_values (codes : List (GPoly (GFrac ℚ))) (cv : List Kc)
    (hcv : cv.length = codes.length)
    (hsum : ∑ k ∈ Finset.range codes.length,
      algebraMap Kc E (cv.getD k 0) * (cM hC S hx Fc hSF).sem (codes.getD k []) = 0) :
    lcombS (algebraMap ℚ Kc) cv
      ((scaledWs (codes.map fun a ↦ fracOf (cvRed Fc a))).map fun V ↦
        flatV V (maxLenB (scaledWs (codes.map fun a ↦ fracOf (cvRed Fc a))))) = 0 := by
  set fr := codes.map fun a ↦ fracOf (cvRed Fc a) with hfr
  set Vs := scaledWs fr with hVs
  set b := maxLenB Vs
  set m := S.F.natDegree
  have hVl : Vs.length = codes.length := by rw [hVs, length_scaledWs, hfr, List.length_map]
  have hm : ∀ V ∈ Vs, V.length ≤ m := by
    intro V hV
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hV
    have hkc : k < codes.length := by rwa [hVl] at hk
    have hkf : k < fr.length := by rw [hfr, List.length_map]; exact hkc
    rw [← List.getD_eq_getElem _ [] hk, length_getD_scaledWs fr k hkf]
    rw [hfr, List.getD_eq_getElem _ _ (by simpa using hkc), List.getElem_map, fracOf,
      length_codeW]
    exact length_cvRed hC S hx Fc hSF _
  have hm0 : 0 < m := natDegree_F_pos' S
  set G := ∑ k ∈ Finset.range Vs.length, Polynomial.C (Polynomial.C (cv.getD k 0)) *
    (toB (Vs.getD k [])).map (mapRingHom (algebraMap ℚ Kc)) with hG
  have hGev : S.evXY G = 0 := by
    rw [hG, evXY_sum_CC]
    have hDall : evRH S (C (toPoly (prodQs fr))) ≠ 0 := by
      rw [evRH_C]
      refine aeval_x_ne_zero' S _ ((Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr
        (prodQs_ne_zero fr fun p hp ↦ ?_))
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hp
      exact codeQ_ne_zero _
    have : ∑ k ∈ Finset.range Vs.length, algebraMap Kc E (cv.getD k 0) *
        S.evXY ((toB (Vs.getD k [])).map (mapRingHom (algebraMap ℚ Kc))) =
        evRH S (C (toPoly (prodQs fr))) * ∑ k ∈ Finset.range codes.length,
          algebraMap Kc E (cv.getD k 0) * (cM hC S hx Fc hSF).sem (codes.getD k []) := by
      rw [Finset.mul_sum, hVl]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [← evRH_eq_evXY, evRH_scaled hC S hx Fc hSF codes k (Finset.mem_range.mp hk)]
      ring
    rw [this, hsum, mul_zero]
  have hGdeg : G.natDegree < m := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := m - 1) fun k hk ↦ ?_) (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_map_le.trans ?_
    have hk' := Finset.mem_range.mp hk
    have hV : Vs.getD k [] ∈ Vs := by
      rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem _
    have := natDegree_toB_le (Vs.getD k [])
    have := hm _ hV
    omega
  have hG0 : G = 0 := S.irr G hGdeg hGev
  rw [lcombS_eq_range _ cv _ (by rw [List.length_map, hVl, hcv]), List.length_map]
  have hcol : ∀ k ∈ Finset.range Vs.length,
      C (cv.getD k 0) * (toPoly ((Vs.map fun V ↦ flatV V b).getD k [])).map (algebraMap ℚ Kc) =
        ∑ i ∈ Finset.range m, X ^ (b * i) *
          (C (cv.getD k 0) * (toPoly ((Vs.getD k []).getD i [])).map (algebraMap ℚ Kc)) :=
    fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      have hV : Vs.getD k [] ∈ Vs := by
        rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem _
      rw [List.getD_eq_getElem (Vs.map fun V ↦ flatV V b) [] (by simpa using hk'),
        List.getElem_map, ← List.getD_eq_getElem _ [] hk',
        toPoly_flatV b _ (length_le_maxLenB Vs _ hV), Polynomial.map_sum, Finset.mul_sum]
      rw [← Finset.sum_range_add_sum_Ico _ (hm _ hV)]
      rw [Finset.sum_eq_zero (s := Finset.Ico _ _) fun i hi ↦ by
        rw [List.getD_eq_default (Vs.getD k []) [] (Finset.mem_Ico.mp hi).1]
        simp [CPoly.toPoly], add_zero]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]; ring
  rw [Finset.sum_congr rfl hcol, Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hGi := congrArg (fun P ↦ P.coeff i) hG0
  simp only [hG, finsetSum_coeff, coeff_C_mul, coeff_map, coeff_toB, coe_mapRingHom,
    Polynomial.coeff_zero] at hGi
  rw [← Finset.mul_sum, hGi, mul_zero]

include hmon hdeg in
/-- **Completeness of the Risch solver on the curve.** -/
theorem curveRde_complete (h : GPoly (GFrac ℚ)) (ws : List (GPoly (GFrac ℚ))) (c : List Kc)
    (z : E) (hzK : z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hE : z′ + ((cM hC S hx Fc hSF).sem h)′ * z = ∑ j ∈ Finset.range ws.length,
      algebraMap Kc E (c.getD j 0) * (cM hC S hx Fc hSF).sem (ws.getD j [])) :
    ∃ β : List Kc,
      (∀ j < ws.length, c.getD j 0 = ∑ l ∈ Finset.range (curveRde Fc h ws).length,
        β.getD l 0 * algebraMap ℚ Kc (((curveRde Fc h ws).getD l ([], [])).1.getD j 0)) ∧
      z = ∑ l ∈ Finset.range (curveRde Fc h ws).length,
        algebraMap Kc E (β.getD l 0) * (cM hC S hx Fc hSF).sem ((curveRde Fc h ws).getD l ([], [])).2 := by
  classical
  set M := cM hC S hx Fc hSF with hMdef
  set n := cvN Fc with hn
  set Eb := rdeE Fc ws with hEb
  set den := rdeDen Fc ws with hden
  set frw := ws.map fun w ↦ fracOf (cvRed Fc w) with hfrw
  set Dw := prodQs frw with hDw
  set Vw := scaledWs frw with hVw
  have hVwl : Vw.length = ws.length := by rw [hVw, length_scaledWs, hfrw, List.length_map]
  set Q : Kc[X] := (toPoly Dw).map (algebraMap ℚ Kc) with hQ
  have hQ0 : Q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr
    (prodQs_ne_zero frw fun p hp ↦ by obtain ⟨a, -, rfl⟩ := List.mem_map.mp hp; exact codeQ_ne_zero _)
  set Ww : Kc[X][X] := ∑ j ∈ Finset.range Vw.length, Polynomial.C (Polynomial.C (c.getD j 0)) *
    (toB (Vw.getD j [])).map (mapRingHom (algebraMap ℚ Kc)) with hWw
  set DW := (Vw.map (boundDW (cvK Fc))).foldr max 0 with hDW
  set w : E := ∑ j ∈ Finset.range ws.length, algebraMap Kc E (c.getD j 0) * M.sem (ws.getD j [])
    with hw
  have hwrep : w * aeval S.x Q = S.evXY Ww := by
    rw [hw, hWw, hVwl]; exact rhs_repr hC S hx Fc hSF ws c
  -- elements of the function field
  have hwK : w ∈ Kc⟮S.x⟯⟮S.y⟯ := by
    rw [hw]
    exact sum_mem fun j _ ↦ mul_mem (S.const_mem _) (sem_mem hC S hx Fc hSF _)
  -- the ansatz
  obtain ⟨Wz, hWzn, hWzc, hWz⟩ := S.rde_ansatz hC hx ⟨z, hzK⟩ ⟨M.sem h, sem_mem hC S hx Fc hSF h⟩
    ⟨w, hwK⟩ hE (cvK Fc) (coeff_F_natDegree_le S Fc hSF) Ww Q hQ0 hwrep DW
    (fun i hi ↦ rhs_bound Fc Vw c i hi)
  have hSn := natDegree_F_cvN S Fc hSF hmon hdeg
  have hdB := degB_le S Fc hSF
  have hQdeg : Q.natDegree ≤ Dw.length - 1 := by
    rw [hQ, natDegree_map_eq_of_injective (algebraMap ℚ Kc).injective]
    exact natDegree_toPoly_le_length _
  have hcE : ∀ j, (Wz.coeff j).natDegree ≤ Eb := fun j ↦ by
    have h1 := hWzc j
    rw [hSn, ← hn] at h1
    have h2 : ((n - 1) * (n - 1) + (n - 1)) * S.degB ≤ ((n - 1) * (n - 1) + (n - 1)) * cvDegB Fc :=
      Nat.mul_le_mul_left _ hdB
    have key : ∀ a a' D : ℕ, a ≤ a' → a + (D + 1 - a) ≤ a' + (D + 1 - a') := by intros; omega
    show _ ≤ (Dw.length - 1) + (DW + 1 - (Dw.length - 1)) +
      ((n - 1) * (n - 1) + (n - 1)) * cvDegB Fc
    exact h1.trans (Nat.add_le_add (key _ _ DW hQdeg) h2)
  have hdenQ : (toPoly den).map (algebraMap ℚ Kc) = S.discR * Q := by
    rw [hden, rdeDen, toPoly_mul, Polynomial.map_mul, discR_eq_cv S Fc hSF hmon hdeg]
  have hD0 : aeval S.x (S.discR * Q) ≠ 0 :=
    aeval_x_ne_zero' S _ (mul_ne_zero S.discR_ne_zero hQ0)
  have hzexp := z_expand hC S hx Fc hSF den (S.discR * Q) hdenQ hD0 Wz n Eb
    (by show Wz.natDegree < cvN Fc; rw [← hSn]; exact hWzn) hcE z hWz
  -- the relation among the values of the columns
  set bs := bcodes den n Eb with hbs
  set codes := bs.map (rdeOp Fc h) ++ ws.map (GPoly.neg xOps) with hcodes
  set cvμ : List Kc := (List.range n).flatMap fun i ↦
    (List.range (Eb + 1)).map fun e ↦ (Wz.coeff i).coeff e with hcvμ
  set cv : List Kc := cvμ ++ (List.range ws.length).map fun j ↦ c.getD j 0 with hcv
  have hbl : bs.length = n * (Eb + 1) := length_bcodes den Eb n
  have hμl : cvμ.length = n * (Eb + 1) := length_flatMap_range _ Eb n
  have hcl : codes.length = n * (Eb + 1) + ws.length := by simp [hcodes, hbl]
  have hcvl : cv.length = codes.length := by simp [hcv, hμl, hcl]
  have hconst : ∀ a : Kc, (algebraMap Kc E a)′ = 0 := fun a ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hsum : ∑ k ∈ Finset.range codes.length,
      algebraMap Kc E (cv.getD k 0) * M.sem (codes.getD k []) = 0 := by
    rw [hcl, Finset.sum_range_add, sum_range_mul_succ]
    have e1 : ∀ i ∈ Finset.range n, ∀ e ∈ Finset.range (Eb + 1),
        algebraMap Kc E (cv.getD (i * (Eb + 1) + e) 0) * M.sem (codes.getD (i * (Eb + 1) + e) []) =
        algebraMap Kc E ((Wz.coeff i).coeff e) *
          ((M.sem (bcode den i e))′ + (M.sem h)′ * M.sem (bcode den i e)) := fun i hi e he ↦ by
      have hi' := Finset.mem_range.mp hi
      have he' := Finset.mem_range.mp he
      have hk : i * (Eb + 1) + e < n * (Eb + 1) := by nlinarith
      rw [hcv, List.getD_append _ _ _ _ (by rw [hμl]; exact hk), hcvμ,
        getD_flatMap_range _ _ Eb n i e hi' (by omega), hcodes,
        List.getD_append _ _ _ _ (by simpa [hbl] using hk),
        List.getD_eq_getElem _ _ (by simpa [hbl] using hk), List.getElem_map,
        ← List.getD_eq_getElem _ [] (by simpa [hbl] using hk), hbs,
        getD_bcodes den Eb n i e hi' (by omega), sem_rdeOp hC S hx Fc hSF]
    have e2 : ∀ j ∈ Finset.range ws.length,
        algebraMap Kc E (cv.getD (n * (Eb + 1) + j) 0) * M.sem (codes.getD (n * (Eb + 1) + j) []) =
        -(algebraMap Kc E (c.getD j 0) * M.sem (ws.getD j [])) := fun j hj ↦ by
      have hj' := Finset.mem_range.mp hj
      rw [hcv, List.getD_append_right _ _ _ _ (by rw [hμl]; omega), hμl, Nat.add_sub_cancel_left,
        List.getD_eq_getElem ((List.range ws.length).map fun j ↦ c.getD j 0) 0 (by simpa using hj'),
        List.getElem_map, List.getElem_range,
        hcodes, List.getD_append_right _ _ _ _ (by simp [hbl]), List.length_map, hbl,
        Nat.add_sub_cancel_left,
        List.getD_eq_getElem (ws.map (GPoly.neg xOps)) [] (by simpa using hj'), List.getElem_map,
        ← List.getD_eq_getElem _ [] hj', sem_negCode hC S hx Fc hSF]
      ring
    rw [Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun e he ↦ e1 i hi e he,
      Finset.sum_congr rfl e2, Finset.sum_neg_distrib, ← hw, ← hE, hzexp]
    simp only [map_sum, Derivation.leibniz, hconst, smul_eq_mul, mul_zero, add_zero,
      Finset.mul_sum]
    rw [← sub_eq_add_neg, sub_eq_zero, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    ring
  have h0 := lcombS_zero_of_values hC S hx Fc hSF codes cv hcvl hsum
  have hcols : rdeCols Fc h ws = (scaledWs (codes.map fun a ↦ fracOf (cvRed Fc a))).map fun V ↦
      flatV V (maxLenB (scaledWs (codes.map fun a ↦ fracOf (cvRed Fc a)))) := rfl
  rw [← hcols] at h0
  have hlen : cv.length = (rdeCols Fc h ws).length := by
    rw [hcols, List.length_map, length_scaledWs, List.length_map, hcvl]
  obtain ⟨β, hβ⟩ := Tower.NestM.nullBasis_coeffs (rdeCols Fc h ws) cv hlen h0
  have hsl : (curveRde Fc h ws).length = (nullBasis (rdeCols Fc h ws)).length := by
    simp [curveRde]
  have hsg : ∀ l, (curveRde Fc h ws).getD l ([], []) =
      if l < (nullBasis (rdeCols Fc h ws)).length then
        rdeOut Fc ws ((nullBasis (rdeCols Fc h ws)).getD l []) else ([], []) := fun l ↦ by
    split_ifs with hl
    · rw [curveRde, List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
        ← List.getD_eq_getElem _ [] hl]
    · rw [List.getD_eq_default _ _ (by simp [curveRde]; omega)]
  refine ⟨β, fun j hj ↦ ?_, ?_⟩
  · have hcj : c.getD j 0 = cv.getD (n * (Eb + 1) + j) 0 := by
      rw [hcv, List.getD_append_right _ _ _ _ (by rw [hμl]; omega), hμl, Nat.add_sub_cancel_left,
        List.getD_eq_getElem ((List.range ws.length).map fun j ↦ c.getD j 0) 0 (by simpa using hj),
        List.getElem_map, List.getElem_range]
    rw [hcj, hβ, hsl]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [hsg l, if_pos (Finset.mem_range.mp hl), rdeOut]
    simp only
    rw [List.getD_eq_getElem ((List.range ws.length).map fun j ↦
      ((nullBasis (rdeCols Fc h ws)).getD l []).getD (n * (Eb + 1) + j) 0) 0 (by simpa using hj),
      List.getElem_map, List.getElem_range]
  · rw [hzexp, hsl]
    have hμ : ∀ i < n, ∀ e ≤ Eb, (Wz.coeff i).coeff e = cv.getD (i * (Eb + 1) + e) 0 :=
      fun i hi e he ↦ by
        rw [hcv, List.getD_append _ _ _ _ (by rw [hμl]; nlinarith), hcvμ,
          getD_flatMap_range _ _ Eb n i e hi he]
    have hz2 : ∀ l ∈ Finset.range (nullBasis (rdeCols Fc h ws)).length,
        M.sem ((curveRde Fc h ws).getD l ([], [])).2 =
        ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range (Eb + 1),
          ((((nullBasis (rdeCols Fc h ws)).getD l []).getD (i * (Eb + 1) + e) 0 : ℚ) : E) *
            M.sem (bcode den i e) := fun l hl ↦ by
      rw [hsg l, if_pos (Finset.mem_range.mp hl), rdeOut]
      exact sem_zcode hC S hx Fc hSF den n Eb _
    have hfin : ∑ l ∈ Finset.range (nullBasis (rdeCols Fc h ws)).length,
        algebraMap Kc E (β.getD l 0) * M.sem ((curveRde Fc h ws).getD l ([], [])).2 =
        ∑ l ∈ Finset.range (nullBasis (rdeCols Fc h ws)).length,
        algebraMap Kc E (β.getD l 0) * ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range (Eb + 1),
          ((((nullBasis (rdeCols Fc h ws)).getD l []).getD (i * (Eb + 1) + e) 0 : ℚ) : E) *
            M.sem (bcode den i e) :=
      Finset.sum_congr rfl fun l hl ↦ by rw [hz2 l hl]
    rw [hfin]
    simp only [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    rw [hμ i (Finset.mem_range.mp hi) e (by have := Finset.mem_range.mp he; omega), hβ,
      map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_mul]
    simp only [eq_ratCast, map_ratCast]
    ring

end Complete

end Curves
