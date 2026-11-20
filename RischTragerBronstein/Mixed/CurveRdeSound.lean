import RischTragerBronstein.Mixed.CurveRdeSem

/-!
# The parametric Risch equation on a curve: soundness

**`curveRde_sound`**: every pair `(β, z)` returned by `curveRde Fc h ws` satisfies
`z′ + h′ z = ∑ βⱼ wⱼ` (values in the model `curveModel`).
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup

section Sound

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

/-- Evaluation of bivariate polynomials over `ℚ` at `(x, y)`. -/
noncomputable def evRH : ℚ[X][X] →+* E :=
  (evalRingHom S.y).comp ((mapRingHom (aeval S.x).toRingHom).comp
    (mapRingHom (mapRingHom (algebraMap ℚ Kc))))

omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero E] in
lemma evRH_C (p : ℚ[X]) : evRH S (C p) = aeval S.x (p.map (algebraMap ℚ Kc)) := by
  simp [evRH]

omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero E] in
lemma evRH_toB (V : BPoly ℚ) : evRH S (toB V) =
    (((toB V).map (mapRingHom (algebraMap ℚ Kc))).map (aeval S.x).toRingHom).eval S.y := by
  simp [evRH, Polynomial.map_map]

include hC in
lemma deriv_ratCast (q : ℚ) : ((q : E))′ = 0 := by
  have : (q : E) = algebraMap Kc E (q : Kc) := by simp
  rw [this, deriv_algebraMap, hC, map_zero]

/-- **The value of a scaled numerator**: `Vₖ(x, y) = D(x) · value(codeₖ)`. -/
lemma evRH_scaled (codes : List (GPoly (GFrac ℚ))) (k : ℕ) (hk : k < codes.length) :
    evRH S (toB ((scaledWs (codes.map fun a ↦ fracOf (cvRed Fc a))).getD k [])) =
      evRH S (C (toPoly (prodQs (codes.map fun a ↦ fracOf (cvRed Fc a))))) *
        (cM hC S hx Fc hSF).sem (codes.getD k []) := by
  set fr := codes.map fun a ↦ fracOf (cvRed Fc a) with hfr
  have hk' : k < fr.length := by simpa [hfr] using hk
  have hsp := scaledWs_spec fr k hk'
  have hfk : fr.getD k ([], []) = fracOf (cvRed Fc (codes.getD k [])) := by
    rw [hfr, List.getD_eq_getElem _ _ hk', List.getElem_map, List.getD_eq_getElem _ _ hk]
  rw [hfk, fracOf] at hsp
  have h1 := congrArg (evRH S) hsp
  rw [map_mul, map_mul, evRH_C, evRH_C, evRH_toB S (codeW _), eval_codeW hC S hx Fc hSF,
    sem_cvRed hC S hx Fc hSF] at h1
  have hQ := aeval_codeQ_ne_zero S (cvRed Fc (codes.getD k []))
  rw [evRH_C]
  apply mul_right_cancel₀ hQ
  rw [h1]; ring

omit [CharZero Kc] in
/-- **A relation among the flattened columns is a relation among the numerators.** -/
lemma rel_bivariate (Vs : List (BPoly ℚ)) (m : ℕ) (hm : ∀ V ∈ Vs, V.length ≤ m) (u : List ℚ)
    (hu : lcomb u (Vs.map fun V ↦ flatV V (maxLenB Vs)) = 0) :
    ∑ k ∈ Finset.range Vs.length, C (C (u.getD k 0)) * toB (Vs.getD k []) = 0 := by
  set b := maxLenB Vs
  have hlen := length_le_maxLenB Vs
  rw [lcomb_eq_range', List.length_map] at hu
  -- the Kronecker form
  have hcol : ∀ k ∈ Finset.range Vs.length,
      C (u.getD k 0) * toPoly ((Vs.map fun V ↦ flatV V b).getD k []) =
        ∑ i ∈ Finset.range m, X ^ (b * i) * (C (u.getD k 0) * toPoly ((Vs.getD k []).getD i [])) :=
    fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      have hV : Vs.getD k [] ∈ Vs := by
        rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem _
      rw [List.getD_eq_getElem (Vs.map fun V ↦ flatV V b) [] (by simpa using hk'),
        List.getElem_map, ← List.getD_eq_getElem _ [] hk', toPoly_flatV b _ (hlen _ hV),
        Finset.mul_sum]
      rw [← Finset.sum_range_add_sum_Ico _ (hm _ hV)]
      rw [Finset.sum_eq_zero (s := Finset.Ico _ _) fun i hi ↦ by
        rw [List.getD_eq_default _ _ (Finset.mem_Ico.mp hi).1]; simp [CPoly.toPoly], add_zero]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [Finset.sum_congr rfl hcol, Finset.sum_comm] at hu
  have hK := kronecker_eq_zero b m
    (fun i ↦ ∑ k ∈ Finset.range Vs.length, C (u.getD k 0) * toPoly ((Vs.getD k []).getD i []))
    (fun i _ ↦ by
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ((Finset.sup_lt_iff
        (WithBot.bot_lt_coe _)).mpr fun k hk ↦ ?_)
      rcases eq_or_ne (u.getD k 0) 0 with h0 | h0
      · rw [h0, C_0, zero_mul, degree_zero]; exact WithBot.bot_lt_coe _
      rw [degree_C_mul h0]
      have hk' := Finset.mem_range.mp hk
      have hV : Vs.getD k [] ∈ Vs := by
        rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem _
      by_cases hi : i < (Vs.getD k []).length
      · have hp : (Vs.getD k []).getD i [] ∈ Vs.getD k [] := by
          rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
        exact lt_of_lt_of_le (CPoly.degree_toPoly_lt _) (by exact_mod_cast hlen _ hV _ hp)
      · rw [List.getD_eq_default (Vs.getD k []) [] (by omega)]
        simp [CPoly.toPoly])
    (by rw [← hu]; exact Finset.sum_congr rfl fun i _ ↦ by rw [Finset.mul_sum])
  ext1 i
  rw [finsetSum_coeff, Polynomial.coeff_zero]
  simp only [coeff_C_mul, coeff_toB]
  by_cases hi : i < m
  · exact hK i hi
  · refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    have hV : Vs.getD k [] ∈ Vs := by
      rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem _
    rw [List.getD_eq_default (Vs.getD k []) [] (by have := hm _ hV; omega)]
    simp [CPoly.toPoly]

lemma sem_rdeOp (h z : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem (rdeOp Fc h z) =
      ((cM hC S hx Fc hSF).sem z)′ + ((cM hC S hx Fc hSF).sem h)′ * (cM hC S hx Fc hSF).sem z := by
  simp only [rdeOp, CField.sem_add, CField.sem_deriv, CField.sem_mul]

lemma sem_negCode (w : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem (GPoly.neg xOps w) = -(cM hC S hx Fc hSF).sem w := by
  rw [sem_cM, sem_cM, GPoly.toPoly_neg, eval_neg]

omit [CharZero Kc] [CharZero E] in
lemma eval_toPoly_range {α : Type*} {O : COps α} (M : CField α E O) (g : ℕ → α) (y : E) :
    ∀ n : ℕ, (GPoly.toPoly M ((List.range n).map g)).eval y = ∑ i ∈ Finset.range n, M.sem (g i) * y ^ i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, GPoly.toPoly_append, eval_add, eval_toPoly_range M g y n,
      Finset.sum_range_succ, List.length_map, List.length_range]
    simp [GPoly.toPoly_cons]

lemma toPoly_range_map' (f : ℕ → ℚ) : ∀ L : ℕ,
    CPoly.toPoly ((List.range L).map f) = ∑ k ∈ Finset.range L, Polynomial.C (f k) * X ^ k
  | 0 => by simp
  | L + 1 => by
    rw [List.range_succ, List.map_append, toPoly_append, toPoly_range_map' f L,
      Finset.sum_range_succ]
    simp [List.length_map, List.length_range]

/-- The value of the solution code. -/
lemma sem_zcode (den : CPoly ℚ) (n Eb : ℕ) (u : CPoly ℚ) :
    (cM hC S hx Fc hSF).sem ((List.range n).map fun i ↦
      ((List.range (Eb + 1)).map fun e ↦ u.getD (i * (Eb + 1) + e) 0, den)) =
    ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range (Eb + 1),
      ((u.getD (i * (Eb + 1) + e) 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (bcode den i e) := by
  rw [sem_cM, eval_toPoly_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [sem_xModel]
  simp only [sem_bcode, toPoly_range_map', Polynomial.map_sum, map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_mul, aeval_C, map_pow, aeval_X,
    Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  simp only [eq_ratCast, algebraMap.coe_ratCast]
  ring

omit [CharZero Kc] [CharZero E] in
lemma length_getD_scaledWs : ∀ (L : List (BPoly ℚ × CPoly ℚ)) (k : ℕ), k < L.length →
    ((scaledWs L).getD k []).length = (L.getD k ([], [])).1.length
  | [], k, hk => by simp at hk
  | p :: L, 0, _ => by simp [scaledWs]
  | p :: L, k + 1, hk => by
    have ih := length_getD_scaledWs L k (by simpa using hk)
    have hk' : k < (scaledWs L).length := by rw [length_scaledWs]; simpa using hk
    simp only [scaledWs, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_map, List.length_map,
      ← List.getD_eq_getElem _ [] hk', ih]

/-- **Soundness of the Risch solver on the curve.** -/
theorem curveRde_sound (h : GPoly (GFrac ℚ)) (ws : List (GPoly (GFrac ℚ))) :
    ∀ r ∈ curveRde Fc h ws,
      ((cM hC S hx Fc hSF).sem r.2)′ + ((cM hC S hx Fc hSF).sem h)′ * (cM hC S hx Fc hSF).sem r.2 =
        ∑ j ∈ Finset.range ws.length, ((r.1.getD j 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (ws.getD j []) := by
  intro r hr
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  set n := cvN Fc
  set Eb := rdeE Fc ws
  set den := rdeDen Fc ws
  set bs := bcodes den n Eb with hbs
  set codes := bs.map (rdeOp Fc h) ++ ws.map (GPoly.neg xOps) with hcodes
  set fr := codes.map fun a ↦ fracOf (cvRed Fc a) with hfr
  set Vs := scaledWs fr with hVs
  have hcols : rdeCols Fc h ws = Vs.map fun V ↦ flatV V (maxLenB Vs) := rfl
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
      codes.getD (i * (Eb + 1) + e) [] = rdeOp Fc h (bcode den i e) := fun i hi e he ↦ by
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
      ((u.getD (i * (Eb + 1) + e) 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (rdeOp Fc h (bcode den i e)) :=
    Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun e he ↦ by rw [hA i hi e he]
  have e2 : ∑ j ∈ Finset.range ws.length,
      ((u.getD (n * (Eb + 1) + j) 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (codes.getD (n * (Eb + 1) + j) []) =
      ∑ j ∈ Finset.range ws.length,
      ((u.getD (n * (Eb + 1) + j) 0 : ℚ) : E) * (cM hC S hx Fc hSF).sem (GPoly.neg xOps (ws.getD j [])) :=
    Finset.sum_congr rfl fun j hj ↦ by rw [hB j hj]
  rw [e1, e2] at hsum
  simp only [sem_rdeOp hC S hx Fc hSF, sem_negCode hC S hx Fc hSF, mul_neg,
    Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero] at hsum
  -- the solution
  show ((cM hC S hx Fc hSF).sem ((List.range n).map fun i ↦ ((List.range (Eb + 1)).map fun e ↦
      u.getD (i * (Eb + 1) + e) 0, den)))′ + ((cM hC S hx Fc hSF).sem h)′ * (cM hC S hx Fc hSF).sem ((List.range n).map fun i ↦
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

end Sound

end Curves
