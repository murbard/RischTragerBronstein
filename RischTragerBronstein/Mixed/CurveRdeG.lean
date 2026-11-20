import RischTragerBronstein.Mixed.CurveRdeComplete

/-!
# A generic parametric Risch solver on a curve

`curveRdeG Fc fc den Eb ws`: the solver of `CurveRde` with the potential `h′` replaced by an
arbitrary code `fc` (the equation `z′ + f z = ∑ βⱼ wⱼ`), and the ansatz denominator `den` and degree
bound `Eb` given as parameters. Soundness (`curveRdeG_sound`) holds for all parameters;
completeness (`curveRdeG_complete`) for every solution lying in the ansatz space.
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup

section Alg

variable (Fc : BPoly ℚ)

/-- The operator `z ↦ z′ + f z` on codes. -/
def rdeOpF (fc z : GPoly (GFrac ℚ)) : GPoly (GFrac ℚ) :=
  (curveOps Fc).add ((curveOps Fc).deriv z) ((curveOps Fc).mul fc z)

/-- The columns of the linear system. -/
def rdeColsG (fc : GPoly (GFrac ℚ)) (den : CPoly ℚ) (Eb : ℕ) (ws : List (GPoly (GFrac ℚ))) :
    List (CPoly ℚ) :=
  let bs := bcodes den (cvN Fc) Eb
  let fr := ((bs.map (rdeOpF Fc fc)) ++ ws.map (GPoly.neg xOps)).map fun a ↦ fracOf (cvRed Fc a)
  let Vs := scaledWs fr
  Vs.map fun V ↦ flatV V (maxLenB Vs)

/-- The solution attached to a relation `u`. -/
def rdeOutG (den : CPoly ℚ) (Eb : ℕ) (ws : List (GPoly (GFrac ℚ))) (u : CPoly ℚ) :
    List ℚ × GPoly (GFrac ℚ) :=
  let n := cvN Fc
  ((List.range ws.length).map fun j ↦ u.getD (n * (Eb + 1) + j) 0,
    (List.range n).map fun i ↦ ((List.range (Eb + 1)).map fun e ↦ u.getD (i * (Eb + 1) + e) 0,
      den))

/-- **The generic parametric Risch solver on the curve.** -/
def curveRdeG (fc : GPoly (GFrac ℚ)) (den : CPoly ℚ) (Eb : ℕ) (ws : List (GPoly (GFrac ℚ))) :
    List (List ℚ × GPoly (GFrac ℚ)) :=
  (nullBasis (rdeColsG Fc fc den Eb ws)).map (rdeOutG Fc den Eb ws)

end Alg

section Proofs

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

lemma sem_rdeOpF (fc z : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem (rdeOpF Fc fc z) =
      ((cM hC S hx Fc hSF).sem z)′ + (cM hC S hx Fc hSF).sem fc * (cM hC S hx Fc hSF).sem z := by
  simp only [rdeOpF, CField.sem_add, CField.sem_deriv, CField.sem_mul]

/-- **Soundness of the generic Risch solver on the curve.** -/
theorem curveRdeG_sound (fc : GPoly (GFrac ℚ)) (den : CPoly ℚ) (Eb : ℕ)
    (ws : List (GPoly (GFrac ℚ))) :
    ∀ r ∈ curveRdeG Fc fc den Eb ws,
      ((cM hC S hx Fc hSF).sem r.2)′ + (cM hC S hx Fc hSF).sem fc * (cM hC S hx Fc hSF).sem r.2 =
        ∑ j ∈ Finset.range ws.length, ((r.1.getD j 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (ws.getD j []) := by
  intro r hr
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  set n := cvN Fc
  set bs := bcodes den n Eb with hbs
  set codes := bs.map (rdeOpF Fc fc) ++ ws.map (GPoly.neg xOps) with hcodes
  set fr := codes.map fun a ↦ fracOf (cvRed Fc a) with hfr
  set Vs := scaledWs fr with hVs
  have hcols : rdeColsG Fc fc den Eb ws = Vs.map fun V ↦ flatV V (maxLenB Vs) := rfl
  have hbl : bs.length = n * (Eb + 1) := length_bcodes den Eb n
  have hcl : codes.length = n * (Eb + 1) + ws.length := by simp [hcodes, hbl]
  have hVl : Vs.length = codes.length := by rw [hVs, length_scaledWs, hfr, List.length_map]
  -- lengths of the numerators
  have hm : ∀ V ∈ Vs, V.length ≤ S.F.natDegree := by
    intro V hV
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hV
    have hkc : k < codes.length := by rwa [hVl] at hk
    have hkf : k < fr.length := by rw [hfr, List.length_map]; exact hkc
    rw [← List.getD_eq_getElem _ [] hk, length_getD_scaledWs fr k hkf]
    rw [hfr, List.getD_eq_getElem _ _ (by simpa using hkc), List.getElem_map, fracOf,
      length_codeW]
    exact length_cvRed hC S hx Fc hSF _
  have hrel := rel_bivariate Vs _ hm u (by rw [← hcols]; exact nullBasis_sound _ u hu)
  -- evaluate
  have hev := congrArg (evRH S) hrel
  rw [map_sum, map_zero] at hev
  have hDall : evRH S (C (toPoly (prodQs fr))) ≠ 0 := by
    rw [evRH_C]
    refine aeval_x_ne_zero' S _ ((Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr
      (prodQs_ne_zero fr fun p hp ↦ ?_))
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hp
    exact codeQ_ne_zero _
  have hsum : ∑ k ∈ Finset.range codes.length, ((u.getD k 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (codes.getD k []) = 0 := by
    apply mul_left_cancel₀ hDall
    rw [mul_zero, ← hev, Finset.mul_sum, hVl]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [map_mul, evRH_scaled hC S hx Fc hSF codes k (Finset.mem_range.mp hk)]
    have hq : evRH S (C (C (u.getD k 0))) = ((u.getD k 0 : ℚ) : E) := by simp [evRH]
    rw [hq]
    ring
  rw [hcl, Finset.sum_range_add, sum_range_mul_succ] at hsum
  -- the two parts
  have hA : ∀ i ∈ Finset.range n, ∀ e ∈ Finset.range (Eb + 1),
      codes.getD (i * (Eb + 1) + e) [] = rdeOpF Fc fc (bcode den i e) := fun i hi e he ↦ by
    have hi' := Finset.mem_range.mp hi
    have he' := Finset.mem_range.mp he
    have hk : i * (Eb + 1) + e < bs.length := by rw [hbl]; nlinarith
    rw [hcodes, List.getD_append _ _ _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk),
      List.getElem_map, ← List.getD_eq_getElem _ [] hk, hbs, getD_bcodes den Eb n i e hi' (by omega)]
  have hB : ∀ j ∈ Finset.range ws.length,
      codes.getD (n * (Eb + 1) + j) [] = GPoly.neg xOps (ws.getD j []) := fun j hj ↦ by
    have hj' := Finset.mem_range.mp hj
    rw [hcodes, List.getD_append_right _ _ _ _ (by simp [hbl]), List.length_map, hbl,
      Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
      ← List.getD_eq_getElem _ [] hj']
  have e1 : ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range (Eb + 1),
      ((u.getD (i * (Eb + 1) + e) 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (codes.getD (i * (Eb + 1) + e) []) =
      ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range (Eb + 1),
      ((u.getD (i * (Eb + 1) + e) 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (rdeOpF Fc fc (bcode den i e)) :=
    Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun e he ↦ by rw [hA i hi e he]
  have e2 : ∑ j ∈ Finset.range ws.length,
      ((u.getD (n * (Eb + 1) + j) 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (codes.getD (n * (Eb + 1) + j) []) =
      ∑ j ∈ Finset.range ws.length,
      ((u.getD (n * (Eb + 1) + j) 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (GPoly.neg xOps (ws.getD j [])) :=
    Finset.sum_congr rfl fun j hj ↦ by rw [hB j hj]
  rw [e1, e2] at hsum
  simp only [sem_rdeOpF hC S hx Fc hSF fc, sem_negCode hC S hx Fc hSF, mul_neg,
    Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero] at hsum
  -- the solution
  show ((cM hC S hx Fc hSF).sem ((List.range n).map fun i ↦ ((List.range (Eb + 1)).map fun e ↦
      u.getD (i * (Eb + 1) + e) 0, den)))′ + (cM hC S hx Fc hSF).sem fc * (cM hC S hx Fc hSF).sem ((List.range n).map fun i ↦
      ((List.range (Eb + 1)).map fun e ↦ u.getD (i * (Eb + 1) + e) 0, den)) = _
  rw [sem_zcode hC S hx Fc hSF]
  simp only [map_sum, Derivation.leibniz, deriv_ratCast hC, smul_eq_mul, mul_zero, add_zero,
    Finset.mul_sum]
  have hR : ∀ j ∈ Finset.range ws.length,
      ((((List.range ws.length).map fun j ↦ u.getD (n * (Eb + 1) + j) 0).getD j 0 : ℚ) : E) =
        ((u.getD (n * (Eb + 1) + j) 0 : ℚ) : E) := fun j hj ↦ by
    rw [List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.mp hj), List.getElem_map,
      List.getElem_range]
  show _ = ∑ j ∈ Finset.range ws.length, ((((List.range ws.length).map fun j ↦
      u.getD (n * (Eb + 1) + j) 0).getD j 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (ws.getD j [])
  have e3 : ∑ j ∈ Finset.range ws.length, ((((List.range ws.length).map fun j ↦
      u.getD (n * (Eb + 1) + j) 0).getD j 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (ws.getD j []) =
      ∑ j ∈ Finset.range ws.length, ((u.getD (n * (Eb + 1) + j) 0 : ℚ) : E) *
        (cM hC S hx Fc hSF).sem (ws.getD j []) :=
    Finset.sum_congr rfl fun j hj ↦ by rw [hR j hj]
  rw [e3, ← hsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  ring

/-- **Completeness of the generic Risch solver on the curve**, given the ansatz: a solution
`z = Wz(x, y)/D(x)` with `deg_y Wz < n`, `deg_x` of the coefficients `≤ Eb`, `D` the value of `den`,
is a constant combination of the returned solutions, compatibly with the parameters. -/
theorem curveRdeG_complete (fc : GPoly (GFrac ℚ)) (den : CPoly ℚ) (Eb : ℕ)
    (ws : List (GPoly (GFrac ℚ))) (Dq : Kc[X]) (hdenQ : (toPoly den).map (algebraMap ℚ Kc) = Dq)
    (hDq0 : Dq ≠ 0) (c : List Kc) (z : E)
    (hE : z′ + (cM hC S hx Fc hSF).sem fc * z = ∑ j ∈ Finset.range ws.length,
      algebraMap Kc E (c.getD j 0) * (cM hC S hx Fc hSF).sem (ws.getD j []))
    (Wz : Kc[X][X]) (hWzn : Wz.natDegree < cvN Fc) (hcE : ∀ j, (Wz.coeff j).natDegree ≤ Eb)
    (hWz : z * aeval S.x Dq = S.evXY Wz) :
    ∃ β : List Kc,
      (∀ j < ws.length, c.getD j 0 = ∑ l ∈ Finset.range (curveRdeG Fc fc den Eb ws).length,
        β.getD l 0 * algebraMap ℚ Kc (((curveRdeG Fc fc den Eb ws).getD l ([], [])).1.getD j 0)) ∧
      z = ∑ l ∈ Finset.range (curveRdeG Fc fc den Eb ws).length,
        algebraMap Kc E (β.getD l 0) *
          (cM hC S hx Fc hSF).sem ((curveRdeG Fc fc den Eb ws).getD l ([], [])).2 := by
  classical
  set M := cM hC S hx Fc hSF with hMdef
  set n := cvN Fc with hn
  set w : E := ∑ j ∈ Finset.range ws.length, algebraMap Kc E (c.getD j 0) * M.sem (ws.getD j [])
    with hw
  have hD0 : aeval S.x Dq ≠ 0 := aeval_x_ne_zero' S _ hDq0
  have hzexp := z_expand hC S hx Fc hSF den Dq hdenQ hD0 Wz n Eb hWzn hcE z hWz
  -- the relation among the values of the columns
  set bs := bcodes den n Eb with hbs
  set codes := bs.map (rdeOpF Fc fc) ++ ws.map (GPoly.neg xOps) with hcodes
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
          ((M.sem (bcode den i e))′ + M.sem fc * M.sem (bcode den i e)) := fun i hi e he ↦ by
      have hi' := Finset.mem_range.mp hi
      have he' := Finset.mem_range.mp he
      have hk : i * (Eb + 1) + e < n * (Eb + 1) := by nlinarith
      rw [hcv, List.getD_append _ _ _ _ (by rw [hμl]; exact hk), hcvμ,
        getD_flatMap_range _ _ Eb n i e hi' (by omega), hcodes,
        List.getD_append _ _ _ _ (by simpa [hbl] using hk),
        List.getD_eq_getElem _ _ (by simpa [hbl] using hk), List.getElem_map,
        ← List.getD_eq_getElem _ [] (by simpa [hbl] using hk), hbs,
        getD_bcodes den Eb n i e hi' (by omega), sem_rdeOpF hC S hx Fc hSF fc]
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
  have hcols : rdeColsG Fc fc den Eb ws = (scaledWs (codes.map fun a ↦ fracOf (cvRed Fc a))).map fun V ↦
      flatV V (maxLenB (scaledWs (codes.map fun a ↦ fracOf (cvRed Fc a)))) := rfl
  rw [← hcols] at h0
  have hlen : cv.length = (rdeColsG Fc fc den Eb ws).length := by
    rw [hcols, List.length_map, length_scaledWs, List.length_map, hcvl]
  obtain ⟨β, hβ⟩ := Tower.NestM.nullBasis_coeffs (rdeColsG Fc fc den Eb ws) cv hlen h0
  have hsl : (curveRdeG Fc fc den Eb ws).length = (nullBasis (rdeColsG Fc fc den Eb ws)).length := by
    simp [curveRdeG]
  have hsg : ∀ l, (curveRdeG Fc fc den Eb ws).getD l ([], []) =
      if l < (nullBasis (rdeColsG Fc fc den Eb ws)).length then
        rdeOutG Fc den Eb ws ((nullBasis (rdeColsG Fc fc den Eb ws)).getD l []) else ([], []) := fun l ↦ by
    split_ifs with hl
    · rw [curveRdeG, List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
        ← List.getD_eq_getElem _ [] hl]
    · rw [List.getD_eq_default _ _ (by simp [curveRdeG]; omega)]
  refine ⟨β, fun j hj ↦ ?_, ?_⟩
  · have hcj : c.getD j 0 = cv.getD (n * (Eb + 1) + j) 0 := by
      rw [hcv, List.getD_append_right _ _ _ _ (by rw [hμl]; omega), hμl, Nat.add_sub_cancel_left,
        List.getD_eq_getElem ((List.range ws.length).map fun j ↦ c.getD j 0) 0 (by simpa using hj),
        List.getElem_map, List.getElem_range]
    rw [hcj, hβ, hsl]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [hsg l, if_pos (Finset.mem_range.mp hl), rdeOutG]
    simp only
    rw [List.getD_eq_getElem ((List.range ws.length).map fun j ↦
      ((nullBasis (rdeColsG Fc fc den Eb ws)).getD l []).getD (n * (Eb + 1) + j) 0) 0 (by simpa using hj),
      List.getElem_map, List.getElem_range]
  · rw [hzexp, hsl]
    have hμ : ∀ i < n, ∀ e ≤ Eb, (Wz.coeff i).coeff e = cv.getD (i * (Eb + 1) + e) 0 :=
      fun i hi e he ↦ by
        rw [hcv, List.getD_append _ _ _ _ (by rw [hμl]; nlinarith), hcvμ,
          getD_flatMap_range _ _ Eb n i e hi he]
    have hz2 : ∀ l ∈ Finset.range (nullBasis (rdeColsG Fc fc den Eb ws)).length,
        M.sem ((curveRdeG Fc fc den Eb ws).getD l ([], [])).2 =
        ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range (Eb + 1),
          ((((nullBasis (rdeColsG Fc fc den Eb ws)).getD l []).getD (i * (Eb + 1) + e) 0 : ℚ) : E) *
            M.sem (bcode den i e) := fun l hl ↦ by
      rw [hsg l, if_pos (Finset.mem_range.mp hl), rdeOutG]
      exact sem_zcode hC S hx Fc hSF den n Eb _
    have hfin : ∑ l ∈ Finset.range (nullBasis (rdeColsG Fc fc den Eb ws)).length,
        algebraMap Kc E (β.getD l 0) * M.sem ((curveRdeG Fc fc den Eb ws).getD l ([], [])).2 =
        ∑ l ∈ Finset.range (nullBasis (rdeColsG Fc fc den Eb ws)).length,
        algebraMap Kc E (β.getD l 0) * ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range (Eb + 1),
          ((((nullBasis (rdeColsG Fc fc den Eb ws)).getD l []).getD (i * (Eb + 1) + e) 0 : ℚ) : E) *
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

end Proofs

end Curves
