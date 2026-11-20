import RischTragerBronstein.Mixed.ExpCurveSetup

/-!
# One exponential over a curve: the algorithm

`integrateExpCurve Fc acode A D N`, for `∫ A(t)/D(t)` with `t = exp a` over the function field of
the curve `F(x, y) = 0` (`Fc` over `ℚ`, `a` and the coefficients of `A, D` curve codes):

1. split off the powers of `t` from `D` and run Hermite reduction on the rest;
2. the residue test on the simple part;
3. every Risch equation `y′ + (j − k) a′ y = Λⱼ` (`j ≠ k`) must have a solution in the function
   field (`curveRde`, a returned solution with non-zero parameter);
4. the constant term `Λₖ` must have an elementary integral on the curve, decided by the total
   decision on curves `decideTotal` with search bound `N`.

This file: the algorithm and the three facts it rests on besides the structure theorem
(`shapeOK_constProb`, `rdeOK_iff`, `const_iff`).
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup NFC

section Alg

variable (Fc : BPoly ℚ)

/-- The derivation of `F₀[t]`: `t′ = a′ t`. -/
def expCurveW (acode : GPoly (GFrac ℚ)) : GPoly (GPoly (GFrac ℚ)) :=
  [(curveOps Fc).zero, (curveOps Fc).deriv acode]

/-- The Risch equation `y′ + h′ y = f` has a solution (with non-zero parameter). -/
def rdeOK (h f : GPoly (GFrac ℚ)) : Bool :=
  (curveRde Fc h [f]).any fun r ↦ decide (r.1.getD 0 0 ≠ 0)

/-- A curve code reduced modulo the curve equation, with every coefficient in lowest terms. -/
def cvNorm (c : GPoly (GFrac ℚ)) : GPoly (GFrac ℚ) := (cvRed Fc c).map CPoly.normCoeff

/-- The problem on the curve for a curve code (numerators trimmed). -/
def constProb (c : GPoly (GFrac ℚ)) : CurveProb ℚ :=
  curveProbQ Fc ((codeW (cvNorm Fc c)).map trim) (codeQ (cvNorm Fc c))

/-- The shape of the curve. -/
def curveShape : Bool := (curveProbQ Fc [] [1]).shapeOK

/-- **One exponential over a curve**, with search bound `N` for the constant term. -/
def integrateExpCurve (acode : GPoly (GFrac ℚ)) (A D : GPoly (GPoly (GFrac ℚ))) (N : ℕ) :
    Option Bool :=
  let O := curveOps Fc
  let w := expCurveW Fc acode
  let sp := GPoly.expSplit O A D
  let k := sp.2.2.1
  let h := GPoly.hermite O w sp.1 sp.2.2.2
  let qr := GPoly.divMod O h.b h.s
  let Λ := GPoly.add O (GPoly.mul O qr.1 (GPoly.monomial O k O.one)) sp.2.1
  if !(GPoly.residueCheck O w qr.2 h.s) then some false
  else if !((List.range (Λ.length + k + 1)).all fun j ↦
      decide (j = k) || rdeOK Fc (mulCode Fc ((j : ℤ) - k) acode) (Λ.getD j O.zero)) then some false
  else decideTotal Fc ((codeW (cvNorm Fc (Λ.getD k O.zero))).map trim)
    (codeQ (cvNorm Fc (Λ.getD k O.zero))) N

end Alg

section Shape

lemma shapeOK_constProb (Fc : BPoly ℚ) (hsh : curveShape Fc = true) (W : BPoly ℚ) (Q : CPoly ℚ)
    (hQ : toPoly Q ≠ 0) : (curveProbQ Fc (W.map trim) Q).shapeOK = true := by
  have hS' := hsh
  simp only [curveShape, CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩, h9⟩, -⟩, -⟩ := hS'
  have hdisc : toPoly (discRC Fc (Fc.length - 1) (autoK Fc)) ≠ 0 := by
    intro h0
    have : toPoly (curveProbQ Fc [] [1]).R0 = 0 := by
      simp only [CurveProb.R0, toPoly_trim, CPoly.toPoly_mul]
      change toPoly (discRC Fc (Fc.length - 1) (autoK Fc)) * _ = 0
      rw [h0, zero_mul]
    rw [← trim_eq_nil_iff] at this
    rw [this] at h9; simp at h9
  simp only [CurveProb.shapeOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨decide_eq_true h1, decide_eq_true h2⟩, decide_eq_true h3⟩, decide_eq_true h4⟩,
    decide_eq_true h5⟩, fun j hj ↦ decide_eq_true (h6 j hj)⟩, fun j hj ↦ decide_eq_true (h7 j hj)⟩,
    ?_⟩, decide_eq_true ?_⟩, decide_eq_true ?_⟩, fun j hj ↦ decide_eq_true ?_⟩
  · rw [Bool.eq_false_iff, Ne, isZero_iff]; exact hQ
  · change 0 < (trim (trim (mul (discRC Fc (Fc.length - 1) (autoK Fc)) Q))).length
    rw [List.length_pos_iff, Ne, trim_eq_nil_iff, toPoly_trim, CPoly.toPoly_mul]
    exact mul_ne_zero hdisc hQ
  · rw [List.length_pos_iff, Ne, trim_eq_nil_iff]; exact hQ
  · refine A_shape_of_trim (curveProbQ Fc (W.map trim) Q) (fun i hi ↦ ?_) j hj
    replace hi : i < (W.map trim).length := hi
    refine ⟨W.getD i [], ?_⟩
    change (W.map trim).getD i [] = _
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ (by simpa using hi)]

end Shape

section Rde

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))
  (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)

include hmon hdeg in
/-- **The Risch check**: `y′ + h′ y = f` is solvable in the function field iff `rdeOK`. -/
theorem rdeOK_iff (h f : GPoly (GFrac ℚ)) :
    (∃ y ∈ Kc⟮S.x⟯⟮S.y⟯, y′ + ((cM hC S hx Fc hSF).sem h)′ * y = (cM hC S hx Fc hSF).sem f) ↔
      rdeOK Fc h f = true := by
  set M := cM hC S hx Fc hSF
  set sols := curveRde Fc h [f]
  have hmemL : ∀ l, l < sols.length → sols.getD l ([], []) ∈ sols := fun l hl ↦ by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
  rw [rdeOK, List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hyE⟩
    obtain ⟨β, hβ1, -⟩ := curveRde_complete hC S hx Fc hSF hmon hdeg h [f] [1] y hy (by
      simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
        map_one, one_mul]
      exact hyE)
    have h1 := hβ1 0 (by simp)
    simp only [List.getD_cons_zero] at h1
    by_contra hall
    push Not at hall
    rw [Finset.sum_eq_zero fun l hl ↦ by
      have : (sols.getD l ([], [])).1.getD 0 0 = 0 := by
        simpa using hall _ (hmemL l (Finset.mem_range.mp hl))
      rw [this, map_zero, mul_zero]] at h1
    exact one_ne_zero h1
  · rintro ⟨r, hr, hr0⟩
    rw [decide_eq_true_eq] at hr0
    have hs := curveRde_sound hC S hx Fc hSF h [f] r hr
    simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton,
      List.getD_cons_zero] at hs
    have hq : ((r.1.getD 0 0 : ℚ) : E) ≠ 0 := by exact_mod_cast hr0
    have hqd : (((r.1.getD 0 0 : ℚ) : E))′ = 0 := by
      rw [show ((r.1.getD 0 0 : ℚ) : E) = algebraMap Kc E ((r.1.getD 0 0 : ℚ) : Kc) by simp,
        deriv_algebraMap, hC, map_zero]
    refine ⟨M.sem r.2 / (r.1.getD 0 0 : ℚ), div_mem (sem_mem hC S hx Fc hSF _) (by
      rw [show ((r.1.getD 0 0 : ℚ) : E) = algebraMap Kc E ((r.1.getD 0 0 : ℚ) : Kc) by simp]
      exact S.const_mem _), ?_⟩
    rw [Derivation.leibniz_div, hqd]
    simp only [smul_eq_mul, mul_zero, sub_zero]
    field_simp
    linear_combination hs

end Rde

section Frac

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

/-- **Normalisation keeps the value.** -/
lemma sem_cvNorm (c : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem (cvNorm Fc c) = (cM hC S hx Fc hSF).sem c := by
  rw [cvNorm, ← sem_cvRed hC S hx Fc hSF c]
  generalize cvRed Fc c = a
  rw [sem_cM, sem_cM]
  congr 1
  set ψ : ℚ[X] →+* E := (aeval S.x).toRingHom.comp (mapRingHom (algebraMap ℚ Kc)) with hψ
  have hψv : ∀ P : ℚ[X], ψ P = aeval S.x (P.map (algebraMap ℚ Kc)) := fun _ ↦ rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    by_contra h0
    exact aeval_x_ne_zero' S _ ((Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr h0)
      (by rw [← hψv]; exact hP)
  have hq : ∀ q : GFrac ℚ, (xM hC S hx).sem (CPoly.normCoeff q) = (xM hC S hx).sem q := by
    intro q
    rw [sem_xModel, sem_xModel, ← hψv, ← hψv, ← hψv, ← hψv]
    exact CPoly.normCoeff_spec ψ hinj q
  induction a with
  | nil => rfl
  | cons q a ih => rw [List.map_cons, GPoly.toPoly_cons, GPoly.toPoly_cons, ih, hq]

/-- **A code as the integrand of the curve problem.** -/
lemma sem_eq_constProb (c : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc hSF).sem c =
      S.evXY ((toB (constProb Fc c).A).map (mapRingHom (algebraMap ℚ Kc))) /
        aeval S.x ((toPoly (constProb Fc c).D).map (algebraMap ℚ Kc)) := by
  change _ = S.evXY ((toB ((codeW (cvNorm Fc c)).map trim)).map _) / _
  rw [toB_map_trim, ← evRH_eq_evXY, evRH_toB, eval_codeW hC S hx Fc hSF, sem_cvNorm hC S hx Fc hSF]
  have hne := aeval_codeQ_ne_zero S (cvNorm Fc c)
  change _ = _ * _ / aeval S.x ((toPoly (codeQ (cvNorm Fc c))).map (algebraMap ℚ Kc))
  exact (mul_div_cancel_left₀ _ hne).symm

end Frac

section Const

universe u

variable {Kc K : Type u} [Field Kc] [Field K] [Algebra Kc K] [Differential Kc] [Differential K]
variable [DifferentialAlgebra Kc K] [CharZero Kc] [CharZero K] [IsAlgClosed Kc]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc K) (hx : S.x′ = 1)
  (Fc : BPoly ℚ) (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

set_option maxHeartbeats 1000000 in
/-- **The constant term is decided by the curve decision**, for any `K` elementary over the
function field; a positive answer gives an elementary integral in every extension. -/
theorem const_decides_of (hsh : curveShape Fc = true)
    (hE : letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
      IsElementaryExtension (cF S) K) (c : GPoly (GFrac ℚ)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b, decideTotal Fc ((codeW (cvNorm Fc c)).map trim)
        (codeQ (cvNorm Fc c)) N = some b ∧
      (HasElementaryIntegral ((cM hC S hx Fc hSF).sem c) ↔ b = true) ∧
      (b = true → HasElementaryIntegralIn ((cM hC S hx Fc hSF).sem c)) := by
  letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
  haveI hDA : DifferentialAlgebra (cF S) K := differentialAlgebra_of_derivClosed _
  haveI hDAc : DifferentialAlgebra Kc (cF S) := cF_diffAlg hC S hx
  haveI : CharZero (cF S) := ⟨fun m n h ↦ by
    have := congrArg (fun z : cF S ↦ (z : K)) h
    simpa using this⟩
  set M := cM hC S hx Fc hSF
  set W := (codeW (cvNorm Fc c)).map trim with hW
  set Q := codeQ (cvNorm Fc c) with hQ
  have hQ0 : toPoly Q ≠ 0 := codeQ_ne_zero _
  have hshape := shapeOK_constProb Fc hsh (codeW (cvNorm Fc c)) Q hQ0
  have hSF0 : (curveIn S).F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)) := by
    rw [curveIn_F, hSF]
  obtain ⟨N₀, hN₀⟩ := decideTotal_decides hC (curveIn S) (curveIn_hx hC S hx) (curveIn_gen S) Fc W Q
    hshape hSF0
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff⟩ := hN₀ N hN
  refine ⟨b, hb, ?_⟩
  rw [← hiff]
  -- the value of the constant term inside the function field
  have hmemc : M.sem c ∈ cF S := sem_mem_cF hC S hx Fc hSF c
  have hval : ((((curveIn S).fE (curveProbQ Fc W Q) (algebraMap ℚ Kc) :
      Kc⟮(curveIn S).x⟯⟮(curveIn S).y⟯)) : cF S) = ⟨M.sem c, hmemc⟩ := by
    apply Subtype.ext
    change ((CurveData.evXY (curveIn S) _ / aeval (curveIn S).x _ : cF S) : K) = M.sem c
    rw [IntermediateField.coe_div, CurveData.evXY, curveIn_x, curveIn_y, coe_evalIn]
    have haev : ((aeval (xIn S) ((toPoly (curveProbQ Fc W Q).D).map (algebraMap ℚ Kc)) : cF S) :
        K) = aeval S.x ((toPoly Q).map (algebraMap ℚ Kc)) := by
      change (cF S).val (aeval (xIn S) _) = _
      rw [← Polynomial.aeval_algHom_apply]
      rfl
    rw [haev]
    change S.evXY ((toB W).map (mapRingHom (algebraMap ℚ Kc))) / _ = _
    rw [hW, toB_map_trim, ← evRH_eq_evXY, evRH_toB, eval_codeW hC S hx Fc hSF,
      sem_cvNorm hC S hx Fc hSF]
    have hne := aeval_codeQ_ne_zero S (cvNorm Fc c)
    rw [← hQ] at hne ⊢
    exact mul_div_cancel_left₀ _ hne
  have hIn : HasElementaryIntegral (⟨M.sem c, hmemc⟩ : cF S) → HasElementaryIntegralIn (M.sem c) := by
    intro h0
    rw [← hval] at h0
    have hL := curve_liouvilleForm hC (curveIn S) (curveIn_hx hC S hx) (curveIn_gen S)
      (curveProbQ Fc W Q) hshape hSF0 h0
    rw [hval] at hL
    exact (hL.map (algebraMap (cF S) K) fun z ↦ deriv_algebraMap z).hasElementaryIntegralIn
  rw [hval]
  exact ⟨⟨fun hK ↦ HasElementaryIntegral.of_extension hE hK,
    fun h0 ↦ (hIn h0).hasElementaryIntegral⟩, hIn⟩

set_option maxHeartbeats 1000000 in
/-- **The constant term is decided by the curve decision** (one exponential). -/
theorem const_decides (hsh : curveShape Fc = true) (acode : GPoly (GFrac ℚ)) (t : K)
    (ht0 : t ≠ 0) (ht : t′ = ((cM hC S hx Fc hSF).sem acode)′ * t)
    (hgen : adjoin (cF S) {t} = (⊤ : IntermediateField (cF S) K)) (c : GPoly (GFrac ℚ)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b, decideTotal Fc ((codeW (cvNorm Fc c)).map trim)
        (codeQ (cvNorm Fc c)) N = some b ∧
      (HasElementaryIntegral ((cM hC S hx Fc hSF).sem c) ↔ b = true) := by
  letI := differentialOfDerivClosed (cF_derivClosed hC S hx)
  have hE := isElementaryExtension_exp (F₀ := cF S) t hgen ht0 ((cM hC S hx Fc hSF).sem acode)
    ⟨⟨_, sem_mem_cF hC S hx Fc hSF acode⟩, rfl⟩ (by rw [logDeriv, ht, mul_div_assoc,
      div_self ht0, mul_one])
  obtain ⟨N₀, h⟩ := const_decides_of hC S hx Fc hSF hsh hE c
  exact ⟨N₀, fun N hN ↦ by obtain ⟨b, hb, hi, -⟩ := h N hN; exact ⟨b, hb, hi⟩⟩

end Const

end Curves
