import RischTragerBronstein.Mixed.CurveRdeG
import RischTragerBronstein.Mixed.RdeBoundsLog
import RischTragerBronstein.Mixed.LogCurveDecide

/-!
# The parametric Risch equation on a curve, with a logarithmic part in the potential

`curveRdeL Fc h logs ws`, `logs = [(c₁, u₁), …]` with `cᵢ ∈ ℚ` and curve codes `uᵢ`: a basis of the
pairs `(β, z)` with `z′ + (h′ + ∑ cᵢ uᵢ′/uᵢ) z = ∑ βⱼ wⱼ`.

It is the generic solver `curveRdeG` with the ansatz of `rdeL_ansatz`: the denominator is enlarged
by `∏ (Qᵢ Q'ᵢ)^{kᵢ}` (`Qᵢ`, `Q'ᵢ` the denominators in `x` of `uᵢ` and `uᵢ⁻¹`, `kᵢ = ⌈|cᵢ|⌉`) and the
degree bound by `∑ kᵢ (D_{Wᵢ} + D_{W'ᵢ})`.
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup

section Alg

variable (Fc : BPoly ℚ)

/-- `p ^ k` for polynomials over `ℚ`. -/
def cpow (p : CPoly ℚ) : ℕ → CPoly ℚ
  | 0 => [1]
  | k + 1 => mul p (cpow p k)

/-- The potential `h′ + ∑ cᵢ uᵢ′/uᵢ`. -/
def fcodeL (h : GPoly (GFrac ℚ)) (logs : List (ℚ × GPoly (GFrac ℚ))) : GPoly (GFrac ℚ) :=
  logs.foldr (fun cu acc ↦ (curveOps Fc).add ((curveOps Fc).mul (ratCode Fc cu.1)
    ((curveOps Fc).mul ((curveOps Fc).deriv cu.2) ((curveOps Fc).inv cu.2))) acc)
    ((curveOps Fc).deriv h)

/-- `⌈|c|⌉`. -/
def kOf (c : ℚ) : ℕ := ⌈|c|⌉₊

/-- The denominators of `u` and `u⁻¹`. -/
def logQ (u : GPoly (GFrac ℚ)) : CPoly ℚ :=
  mul (codeQ (cvRed Fc u)) (codeQ (cvRed Fc ((curveOps Fc).inv u)))

/-- The extra denominator `∏ (Qᵢ Q'ᵢ)^{kᵢ}`. -/
def logDen (logs : List (ℚ × GPoly (GFrac ℚ))) : CPoly ℚ :=
  logs.foldr (fun cu acc ↦ mul (cpow (logQ Fc cu.2) (kOf cu.1)) acc) [1]

/-- The extra degree `∑ kᵢ (D_{Wᵢ} + D_{W'ᵢ})`. -/
def logDeg (logs : List (ℚ × GPoly (GFrac ℚ))) : ℕ :=
  (logs.map fun cu ↦ kOf cu.1 * (boundDW (cvK Fc) (codeW (cvRed Fc cu.2)) +
    boundDW (cvK Fc) (codeW (cvRed Fc ((curveOps Fc).inv cu.2))))).sum

/-- The ansatz denominator. -/
def denL (logs : List (ℚ × GPoly (GFrac ℚ))) (ws : List (GPoly (GFrac ℚ))) : CPoly ℚ :=
  mul (rdeDen Fc ws) (logDen Fc logs)

/-- The degree bound. -/
def EL (logs : List (ℚ × GPoly (GFrac ℚ))) (ws : List (GPoly (GFrac ℚ))) : ℕ :=
  let Qw := prodQs (ws.map fun w ↦ fracOf (cvRed Fc w))
  let DW := ((scaledWs (ws.map fun w ↦ fracOf (cvRed Fc w))).map (boundDW (cvK Fc))).foldr max 0
  (Qw.length - 1) + (DW + 1 - (Qw.length - 1)) + ((logDen Fc logs).length - 1) + logDeg Fc logs +
    ((cvN Fc - 1) * (cvN Fc - 1) + (cvN Fc - 1)) * cvDegB Fc

/-- **The parametric Risch equation on the curve with a logarithmic part.** -/
def curveRdeL (h : GPoly (GFrac ℚ)) (logs : List (ℚ × GPoly (GFrac ℚ)))
    (ws : List (GPoly (GFrac ℚ))) : List (List ℚ × GPoly (GFrac ℚ)) :=
  curveRdeG Fc (fcodeL Fc h logs) (denL Fc logs ws) (EL Fc logs ws) ws

end Alg

lemma toPoly_cpow (p : CPoly ℚ) : ∀ k, toPoly (cpow p k) = toPoly p ^ k
  | 0 => by simp [cpow, CPoly.toPoly]
  | k + 1 => by rw [cpow, toPoly_mul, toPoly_cpow p k, pow_succ, mul_comm]

section Proofs

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

/-- The value of the potential. -/
lemma sem_fcodeL (h : GPoly (GFrac ℚ)) (logs : List (ℚ × GPoly (GFrac ℚ))) :
    (cM hC S hx Fc hSF).sem (fcodeL Fc h logs) = ((cM hC S hx Fc hSF).sem h)′ +
      ∑ i ∈ Finset.range logs.length, ((logs.getD i (0, [])).1 : E) *
        logDeriv ((cM hC S hx Fc hSF).sem (logs.getD i (0, [])).2) := by
  induction logs with
  | nil => simp [fcodeL, CField.sem_deriv]
  | cons cu logs ih =>
    rw [fcodeL, List.foldr_cons, CField.sem_add, CField.sem_mul, CField.sem_mul, CField.sem_deriv,
      CField.sem_inv, sem_ratCode]
    rw [fcodeL] at ih
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, logDeriv, div_eq_mul_inv]
    ring

/-- **Soundness.** -/
theorem curveRdeL_sound (h : GPoly (GFrac ℚ)) (logs : List (ℚ × GPoly (GFrac ℚ)))
    (ws : List (GPoly (GFrac ℚ))) :
    ∀ r ∈ curveRdeL Fc h logs ws,
      ((cM hC S hx Fc hSF).sem r.2)′ + (((cM hC S hx Fc hSF).sem h)′ +
        ∑ i ∈ Finset.range logs.length, ((logs.getD i (0, [])).1 : E) *
          logDeriv ((cM hC S hx Fc hSF).sem (logs.getD i (0, [])).2)) *
        (cM hC S hx Fc hSF).sem r.2 =
        ∑ j ∈ Finset.range ws.length, ((r.1.getD j 0 : ℚ) : E) *
          (cM hC S hx Fc hSF).sem (ws.getD j []) := by
  intro r hr
  have := curveRdeG_sound hC S hx Fc hSF (fcodeL Fc h logs) (denL Fc logs ws) (EL Fc logs ws) ws
    r hr
  rwa [sem_fcodeL] at this

/-- The representation `a · Q(x) = W(x, y)` of a curve code. -/
lemma rep_code (a : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem a * aeval S.x ((toPoly (codeQ (cvRed Fc a))).map (algebraMap ℚ Kc)) =
      S.evXY ((toB (codeW (cvRed Fc a))).map (mapRingHom (algebraMap ℚ Kc))) := by
  have := eval_codeW hC S hx Fc hSF (cvRed Fc a)
  rw [sem_cvRed hC S hx Fc hSF] at this
  rw [CurveData.evXY, this, mul_comm]

omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero E] in
/-- The degree bound of the numerator of a single code. -/
lemma bound_code (a : GPoly (GFrac ℚ)) (j : ℕ)
    (hj : ((toB (codeW (cvRed Fc a))).map (mapRingHom (algebraMap ℚ Kc))).coeff j ≠ 0) :
    (((toB (codeW (cvRed Fc a))).map (mapRingHom (algebraMap ℚ Kc))).coeff j).natDegree +
      cvK Fc * j ≤ boundDW (cvK Fc) (codeW (cvRed Fc a)) := by
  set V := codeW (cvRed Fc a)
  have e : ((toB V).map (mapRingHom (algebraMap ℚ Kc))).coeff j =
      (toPoly (V.getD j [])).map (algebraMap ℚ Kc) := by
    rw [coeff_map, coeff_toB, coe_mapRingHom]
  rw [e] at hj ⊢
  have hjV : j < V.length := by
    by_contra hge
    rw [List.getD_eq_default V [] (by omega)] at hj
    simp [CPoly.toPoly] at hj
  rw [natDegree_map_eq_of_injective (algebraMap ℚ Kc).injective]
  have := boundDW_ge (cvK Fc) V j hjV
  have := natDegree_toPoly_le_length (V.getD j [])
  omega

lemma toPoly_logDen (logs : List (ℚ × GPoly (GFrac ℚ))) :
    toPoly (logDen Fc logs) = ∏ i ∈ Finset.range logs.length,
      toPoly (logQ Fc (logs.getD i (0, [])).2) ^ kOf (logs.getD i (0, [])).1 := by
  induction logs with
  | nil => simp [logDen, CPoly.toPoly]
  | cons cu logs ih =>
    rw [logDen, List.foldr_cons, toPoly_mul, toPoly_cpow]
    rw [logDen] at ih
    rw [ih, List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

lemma logDeg_eq (logs : List (ℚ × GPoly (GFrac ℚ))) :
    logDeg Fc logs = ∑ i ∈ Finset.range logs.length, kOf (logs.getD i (0, [])).1 *
      (boundDW (cvK Fc) (codeW (cvRed Fc (logs.getD i (0, [])).2)) +
        boundDW (cvK Fc) (codeW (cvRed Fc ((curveOps Fc).inv (logs.getD i (0, [])).2)))) := by
  induction logs with
  | nil => simp [logDeg]
  | cons cu logs ih =>
    rw [logDeg, List.map_cons, List.sum_cons]
    rw [logDeg] at ih
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring


include hC hx in
/-- **Completeness**, for non-zero `uᵢ`. -/
theorem curveRdeL_complete (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (h : GPoly (GFrac ℚ)) (logs : List (ℚ × GPoly (GFrac ℚ)))
    (hu0 : ∀ i < logs.length, (cM hC S hx Fc hSF).sem (logs.getD i (0, [])).2 ≠ 0)
    (ws : List (GPoly (GFrac ℚ))) (c : List Kc) (z : E) (hzK : z ∈ Kc⟮S.x⟯⟮S.y⟯)
    (hE : z′ + (((cM hC S hx Fc hSF).sem h)′ +
        ∑ i ∈ Finset.range logs.length, ((logs.getD i (0, [])).1 : E) *
          logDeriv ((cM hC S hx Fc hSF).sem (logs.getD i (0, [])).2)) * z =
      ∑ j ∈ Finset.range ws.length, algebraMap Kc E (c.getD j 0) *
        (cM hC S hx Fc hSF).sem (ws.getD j [])) :
    ∃ β : List Kc,
      (∀ j < ws.length, c.getD j 0 = ∑ l ∈ Finset.range (curveRdeL Fc h logs ws).length,
        β.getD l 0 * algebraMap ℚ Kc (((curveRdeL Fc h logs ws).getD l ([], [])).1.getD j 0)) ∧
      z = ∑ l ∈ Finset.range (curveRdeL Fc h logs ws).length,
        algebraMap Kc E (β.getD l 0) *
          (cM hC S hx Fc hSF).sem ((curveRdeL Fc h logs ws).getD l ([], [])).2 := by
  classical
  set M := cM hC S hx Fc hSF with hMdef
  set n := cvN Fc with hn
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
  have hwK : w ∈ Kc⟮S.x⟯⟮S.y⟯ := by
    rw [hw]
    exact sum_mem fun j _ ↦ mul_mem (S.const_mem _) (sem_mem hC S hx Fc hSF _)
  -- the data of the logarithmic part
  set L := logs.length with hL
  set cf : ℕ → ℚ := fun i ↦ (logs.getD i (0, [])).1 with hcf
  set uc : ℕ → GPoly (GFrac ℚ) := fun i ↦ (logs.getD i (0, [])).2 with huc
  set uf : ℕ → Kc⟮S.x⟯⟮S.y⟯ := fun i ↦ ⟨M.sem (uc i), sem_mem hC S hx Fc hSF _⟩ with huf
  set Wu : ℕ → Kc[X][X] := fun i ↦ (toB (codeW (cvRed Fc (uc i)))).map (mapRingHom (algebraMap ℚ Kc))
  set Wi : ℕ → Kc[X][X] := fun i ↦
    (toB (codeW (cvRed Fc ((curveOps Fc).inv (uc i))))).map (mapRingHom (algebraMap ℚ Kc))
  set Qu : ℕ → Kc[X] := fun i ↦ (toPoly (codeQ (cvRed Fc (uc i)))).map (algebraMap ℚ Kc)
  set Qi : ℕ → Kc[X] := fun i ↦
    (toPoly (codeQ (cvRed Fc ((curveOps Fc).inv (uc i))))).map (algebraMap ℚ Kc)
  have hQu : ∀ i ∈ Finset.range L, Qu i ≠ 0 := fun i _ ↦
    (Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr (codeQ_ne_zero _)
  have hQi : ∀ i ∈ Finset.range L, Qi i ≠ 0 := fun i _ ↦
    (Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr (codeQ_ne_zero _)
  have hu : ∀ i ∈ Finset.range L, uf i ≠ 0 := fun i hi h0 ↦
    hu0 i (Finset.mem_range.mp hi) (congrArg Subtype.val h0)
  have hru : ∀ i ∈ Finset.range L, (uf i : E) * aeval S.x (Qu i) = S.evXY (Wu i) := fun i _ ↦
    rep_code hC S hx Fc hSF (uc i)
  have hri : ∀ i ∈ Finset.range L, (uf i : E)⁻¹ * aeval S.x (Qi i) = S.evXY (Wi i) := fun i _ ↦ by
    have := rep_code hC S hx Fc hSF ((curveOps Fc).inv (uc i))
    rwa [CField.sem_inv] at this
  have hE' : z′ + ((M.sem h)′ + ∑ i ∈ Finset.range L, (cf i : E) * logDeriv (uf i : E)) * z =
      w := hE
  obtain ⟨Wz, hWzn, hWzc, hWz⟩ := S.rdeL_ansatz hC hx ⟨z, hzK⟩ ⟨M.sem h, sem_mem hC S hx Fc hSF h⟩
    ⟨w, hwK⟩ (Finset.range L) cf uf hu hE' (cvK Fc) (coeff_F_natDegree_le S Fc hSF) Ww Q hQ0 hwrep
    DW (fun i hi ↦ rhs_bound Fc Vw c i hi) Wu Wi Qu Qi hQu hQi hru hri
    (fun i ↦ boundDW (cvK Fc) (codeW (cvRed Fc (uc i))))
    (fun i ↦ boundDW (cvK Fc) (codeW (cvRed Fc ((curveOps Fc).inv (uc i)))))
    (fun i _ j hj ↦ bound_code Fc (uc i) j hj)
    (fun i _ j hj ↦ bound_code Fc ((curveOps Fc).inv (uc i)) j hj)
    (fun i ↦ kOf (cf i)) (fun i _ ↦ Nat.le_ceil _)
  -- the denominator
  set P : Kc[X] := ∏ i ∈ Finset.range L, (Qu i * Qi i) ^ kOf (cf i) with hP
  have hPq : (toPoly (logDen Fc logs)).map (algebraMap ℚ Kc) = P := by
    rw [toPoly_logDen, Polynomial.map_prod, hP]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Polynomial.map_pow, logQ, toPoly_mul, Polynomial.map_mul]
  have hdenQ : (toPoly (denL Fc logs ws)).map (algebraMap ℚ Kc) = S.discR * (Q * P) := by
    rw [denL, toPoly_mul, Polynomial.map_mul, rdeDen, toPoly_mul, Polynomial.map_mul,
      discR_eq_cv S Fc hSF hmon hdeg, hPq]
    ring
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi ↦
    pow_ne_zero _ (mul_ne_zero (hQu i hi) (hQi i hi))
  -- the degree bound
  have hSn := natDegree_F_cvN S Fc hSF hmon hdeg
  have hdB := degB_le S Fc hSF
  have hQdeg : Q.natDegree ≤ Dw.length - 1 := by
    rw [hQ, natDegree_map_eq_of_injective (algebraMap ℚ Kc).injective]
    exact natDegree_toPoly_le_length _
  have hPdeg : P.natDegree ≤ (logDen Fc logs).length - 1 := by
    rw [← hPq, natDegree_map_eq_of_injective (algebraMap ℚ Kc).injective]
    exact natDegree_toPoly_le_length _
  have hcE : ∀ j, (Wz.coeff j).natDegree ≤ EL Fc logs ws := fun j ↦ by
    have h1 := hWzc j
    rw [hSn, ← hn, natDegree_mul hQ0 hP0] at h1
    have h2 : ((n - 1) * (n - 1) + (n - 1)) * S.degB ≤ ((n - 1) * (n - 1) + (n - 1)) * cvDegB Fc :=
      Nat.mul_le_mul_left _ hdB
    have key : ∀ a a' D : ℕ, a ≤ a' → a + (D + 1 - a) ≤ a' + (D + 1 - a') := by intros; omega
    have hk := key _ _ DW hQdeg
    have hld : ∑ i ∈ Finset.range L, kOf (cf i) *
        (boundDW (cvK Fc) (codeW (cvRed Fc (uc i))) +
          boundDW (cvK Fc) (codeW (cvRed Fc ((curveOps Fc).inv (uc i))))) = logDeg Fc logs :=
      (logDeg_eq Fc logs).symm
    show _ ≤ (Dw.length - 1) + (DW + 1 - (Dw.length - 1)) + ((logDen Fc logs).length - 1) +
      logDeg Fc logs + ((n - 1) * (n - 1) + (n - 1)) * cvDegB Fc
    rw [← hld]
    omega
  exact curveRdeG_complete hC S hx Fc hSF (fcodeL Fc h logs) (denL Fc logs ws) (EL Fc logs ws) ws
    (S.discR * (Q * P)) hdenQ (mul_ne_zero S.discR_ne_zero (mul_ne_zero hQ0 hP0)) c z
    (by rw [sem_fcodeL]; exact hE) Wz (by rw [← hSn]; exact hWzn) hcE hWz

end Proofs

end Curves
