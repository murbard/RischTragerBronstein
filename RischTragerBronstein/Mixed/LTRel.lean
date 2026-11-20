import RischTragerBronstein.Mixed.LTTower
import RischTragerBronstein.Computable.NestPConsys

/-!
# Towers of logarithms over a curve: constant linear relations

`lrel Fc us m vs`: a `ℚ`-basis of the relations `∑ cⱼ vⱼ = 0` among values of level-`m` codes,
**complete for constant coefficients** in every realization (`lrel_complete`) and sound
(`lrel_sound`).

* Level `0` (`curveCols`): over the common denominator, the numerators are bivariate polynomials
  of `y`-degree `< n`; by irreducibility of the curve a relation among values is a relation among
  numerators (`lcombS_zero_of_values`) and conversely (`values_zero_of_lcombS`), and Kronecker
  flattening turns them into `ℚ`-columns.
* Level `m + 1` (`LCols`): clear denominators (`cross`), take coefficients in `tₘ`, recurse and
  glue the blocks (as for towers over `ℚ(x)`, `Tower.NestP.colsOf`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open CPoly Sup

/-- The `ℚ`-columns of the values of curve codes. -/
def curveCols (Fc : BPoly ℚ) (vs : List (GPoly (GFrac ℚ))) : List (CPoly ℚ) :=
  (scaledWs (vs.map fun a ↦ fracOf (cvRed Fc a))).map fun V ↦
    flatV V (maxLenB (scaledWs (vs.map fun a ↦ fracOf (cvRed Fc a))))

lemma length_curveCols (Fc : BPoly ℚ) (vs : List (GPoly (GFrac ℚ))) :
    (curveCols Fc vs).length = vs.length := by
  rw [curveCols, List.length_map, length_scaledWs, List.length_map]

section Level0

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc : BPoly ℚ)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

/-- **A relation among the columns is a relation among the values.** -/
lemma values_zero_of_lcombS (codes : List (GPoly (GFrac ℚ))) (cv : List Kc)
    (hcv : cv.length = codes.length)
    (h0 : lcombS (algebraMap ℚ Kc) cv (curveCols Fc codes) = 0) :
    ∑ k ∈ Finset.range codes.length,
      algebraMap Kc E (cv.getD k 0) * (cM hC S hx Fc hSF).sem (codes.getD k []) = 0 := by
  set fr := codes.map fun a ↦ fracOf (cvRed Fc a) with hfr
  set Vs := scaledWs fr with hVs
  set b := maxLenB Vs with hb
  set m := S.F.natDegree with hmdef
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
  have hcols : curveCols Fc codes = Vs.map fun V ↦ flatV V b := rfl
  rw [hcols, lcombS_eq_range _ cv _ (by rw [List.length_map, hVl, hcv]), List.length_map] at h0
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
  rw [Finset.sum_congr rfl hcol, Finset.sum_comm] at h0
  set G' : ℕ → Kc[X] := fun i ↦ ∑ k ∈ Finset.range Vs.length,
    C (cv.getD k 0) * (toPoly ((Vs.getD k []).getD i [])).map (algebraMap ℚ Kc) with hG'
  have h0' : ∑ i ∈ Finset.range m, X ^ (b * i) * G' i = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hG', Finset.mul_sum]
  have hdeg : ∀ i < m, (G' i).degree < b := by
    intro i _
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe b)).mpr fun k hk ↦ ?_
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    have hk' := Finset.mem_range.mp hk
    have hV : Vs.getD k [] ∈ Vs := by
      rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem _
    have hlen : ((Vs.getD k []).getD i []).length ≤ b := by
      by_cases hi : i < (Vs.getD k []).length
      · rw [List.getD_eq_getElem _ _ hi]
        exact length_le_maxLenB Vs _ hV _ (List.getElem_mem _)
      · rw [List.getD_eq_default _ _ (by omega)]; simp
    have hd := Tower.NestP.degree_toPoly_lt hlen
    rcases eq_or_ne (cv.getD k 0) 0 with hc | hc
    · rw [hc, map_zero, degree_zero, WithBot.bot_add]; exact WithBot.bot_lt_coe _
    · rw [degree_C hc, zero_add, degree_map]
      exact hd
  have hG0 := kronecker_eq_zero b m G' hdeg h0'
  -- the bivariate combination vanishes
  set G := ∑ k ∈ Finset.range Vs.length, Polynomial.C (Polynomial.C (cv.getD k 0)) *
    (toB (Vs.getD k [])).map (mapRingHom (algebraMap ℚ Kc)) with hG
  have hGz : G = 0 := by
    ext i : 1
    have hci : G.coeff i = G' i := by
      simp only [hG, hG', finsetSum_coeff, coeff_C_mul, coeff_map, coeff_toB, coe_mapRingHom]
    rw [hci, Polynomial.coeff_zero]
    by_cases hi : i < m
    · exact hG0 i hi
    · refine Finset.sum_eq_zero fun k hk ↦ ?_
      have hk' := Finset.mem_range.mp hk
      have hV : Vs.getD k [] ∈ Vs := by
        rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem _
      rw [List.getD_eq_default (Vs.getD k []) [] (by have := hm _ hV; omega)]
      simp [CPoly.toPoly]
  have hDall : evRH S (C (toPoly (prodQs fr))) ≠ 0 := by
    rw [evRH_C]
    refine aeval_x_ne_zero' S _ ((Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr
      (prodQs_ne_zero fr fun p hp ↦ ?_))
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hp
    exact codeQ_ne_zero _
  have key : S.evXY G = evRH S (C (toPoly (prodQs fr))) * ∑ k ∈ Finset.range codes.length,
      algebraMap Kc E (cv.getD k 0) * (cM hC S hx Fc hSF).sem (codes.getD k []) := by
    rw [hG, evXY_sum_CC, Finset.mul_sum, hVl]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← evRH_eq_evXY, evRH_scaled hC S hx Fc hSF codes k (Finset.mem_range.mp hk)]
    ring
  rw [hGz] at key
  have : S.evXY (0 : Kc[X][X]) = 0 := by simp [CurveData.evXY]
  rw [this] at key
  exact (mul_eq_zero.mp key.symm).resolve_left hDall

/-- **Relations on the curve**, in both directions. -/
theorem curveCols_spec (codes : List (GPoly (GFrac ℚ))) (cv : List Kc)
    (hcv : cv.length = codes.length) :
    ∑ k ∈ Finset.range codes.length,
      algebraMap Kc E (cv.getD k 0) * (cM hC S hx Fc hSF).sem (codes.getD k []) = 0 ↔
    lcombS (algebraMap ℚ Kc) cv (curveCols Fc codes) = 0 :=
  ⟨lcombS_zero_of_values hC S hx Fc hSF codes cv hcv,
    values_zero_of_lcombS hC S hx Fc hSF codes cv hcv⟩

end Level0

namespace LT

open Tower.NestP

/-! ### Columns at every level -/

/-- **Columns of the constant system** `∑ cⱼ vⱼ = 0` over `ℚ`, at level `m`. -/
def LCols (Fc : BPoly ℚ) (us : (m : ℕ) → LC m) : (m : ℕ) → List (LC m) → List (CPoly ℚ)
  | 0, vs => curveCols Fc vs
  | m + 1, vs =>
    let O := LO Fc us m
    let N := cross (GPoly.mul O) [O.one] ((vs : List (GFrac (LC m))).map fun v ↦
      if GPoly.isZero O v.2 then (([] : GPoly (LC m)), [O.one]) else v)
    let K := (N.map List.length).foldr max 0
    let blocks := (List.range K).map fun k ↦ LCols Fc us m (N.map fun p ↦ p.getD k O.zero)
    glueU vs.length (maxLen blocks) blocks

/-- **A basis of the constant relations** `∑ cⱼ vⱼ = 0` among level-`m` values. -/
def lrel (Fc : BPoly ℚ) (us : (m : ℕ) → LC m) (m : ℕ) (vs : List (LC m)) : List (CPoly ℚ) :=
  nullBasis (LCols Fc us m vs)

lemma length_LCols (Fc : BPoly ℚ) (us : (m : ℕ) → LC m) :
    ∀ (m : ℕ) (vs : List (LC m)), (LCols Fc us m vs).length = vs.length
  | 0, vs => length_curveCols Fc vs
  | m + 1, vs => by
    simp only [LCols]
    rw [length_glueU]
    intro B hB
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hB
    rw [length_LCols Fc us m, List.length_map, length_cross]
    exact List.length_map _

/-- A zipped sum as a sum over indices. -/
lemma sum_zipWith_range {α β γ : Type*} [AddCommMonoid γ] (f : α → β → γ) (a0 : α) (b0 : β) :
    ∀ (c : List α) (vs : List β), c.length = vs.length →
      (List.zipWith f c vs).sum = ∑ k ∈ Finset.range vs.length, f (c.getD k a0) (vs.getD k b0)
  | [], [], _ => by simp
  | a :: c, v :: vs, h => by
    rw [List.zipWith_cons_cons, List.sum_cons, sum_zipWith_range f a0 b0 c vs (by simpa using h),
      List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact add_comm _ _
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

universe u

variable {Fc : BPoly ℚ} {us : (m : ℕ) → LC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace LTower

variable (T : LTower Fc us Cc L)

lemma phi_C (m : ℕ) (z : T.F m) : T.phi m (C z) = IntermediateField.inclusion (T.le_succ m) z :=
  Subtype.ext (by rw [coe_phi, aeval_C]; rfl)

lemma algebraMap_succ (m : ℕ) (c : Cc) :
    algebraMap Cc (T.F (m + 1)) c = T.phi m (C (algebraMap Cc (T.F m) c)) := by
  rw [T.phi_C]; rfl

/-- `(F m)[X] → F (m + 1)` on codes. -/
noncomputable def sigP (m : ℕ) (M : CField (LC m) (T.F m) (LO Fc us m)) (p : GPoly (LC m)) :
    T.F (m + 1) := T.phi m (GPoly.toPoly M p)

/-- Zero-denominator cleaning at level `m + 1`. -/
def cleanS (m : ℕ) (v : GFrac (LC m)) : GFrac (LC m) :=
  if GPoly.isZero (LO Fc us m) v.2 then (([] : GPoly (LC m)), [(LO Fc us m).one]) else v

lemma sigP_mul (m : ℕ) (M : CField (LC m) (T.F m) (LO Fc us m)) (a b) :
    T.sigP m M (GPoly.mul (LO Fc us m) a b) = T.sigP m M a * T.sigP m M b := by
  simp only [sigP, GPoly.toPoly_mul, map_mul]

lemma sigP_one (m : ℕ) (M : CField (LC m) (T.F m) (LO Fc us m)) :
    T.sigP m M [(LO Fc us m).one] = 1 := by
  simp only [sigP, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, M.sem_one, C_1,
    map_one]

lemma sum_sigP (m : ℕ) (M : CField (LC m) (T.F m) (LO Fc us m)) :
    ∀ (c : List Cc) (N : List (GPoly (LC m))),
      (List.zipWith (fun c y ↦ c * T.sigP m M y) (c.map (algebraMap Cc (T.F (m + 1)))) N).sum =
        T.phi m (List.zipWith (fun c y ↦ C (algebraMap Cc (T.F m) c) * GPoly.toPoly M y) c N).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, y :: N => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, map_add, map_mul,
      T.algebraMap_succ, sigP]
    rw [← sum_sigP m M cs N]
    rfl

lemma coeff_sum_toPoly (m : ℕ) (M : CField (LC m) (T.F m) (LO Fc us m)) (k : ℕ) :
    ∀ (c : List Cc) (N : List (GPoly (LC m))),
      (List.zipWith (fun c y ↦ C (algebraMap Cc (T.F m) c) * GPoly.toPoly M y) c N).sum.coeff k =
        (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * M.sem v) c
          (N.map fun p ↦ p.getD k (LO Fc us m).zero)).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, y :: N => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, coeff_add, coeff_C_mul,
      coeff_toPoly_getD']
    rw [coeff_sum_toPoly m M k cs N]

lemma sum_zero_codes (m : ℕ) (M : CField (LC m) (T.F m) (LO Fc us m)) :
    ∀ (c : List Cc) (vs : List (LC m)), (∀ v ∈ vs, v = (LO Fc us m).zero) →
      (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * M.sem v) c vs).sum = 0
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | c :: cs, v :: vs, h => by
    simp only [List.zipWith_cons_cons, List.sum_cons, h v List.mem_cons_self, M.sem_zero,
      mul_zero, zero_add]
    exact sum_zero_codes m M cs vs fun w hw ↦ h w (List.mem_cons_of_mem _ hw)

lemma zipWith_map_left' {γ K : Type*} [Field K] (a : Cc → K) (f : γ → K) :
    ∀ (c : List Cc) (vs : List γ), (List.zipWith (fun c v ↦ a c * f v) c vs).sum =
      (List.zipWith (fun c v ↦ c * f v) (c.map a) vs).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, v :: vs => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons,
      zipWith_map_left' a f cs vs]

lemma zipWith_comp_map' {γ δ K : Type*} [Field K] (f : γ → K) (g : δ → K) (cl : γ → δ)
    (hfg : ∀ v, f v = g (cl v)) : ∀ (c : List K) (vs : List γ),
    (List.zipWith (fun c v ↦ c * f v) c vs).sum = (List.zipWith (fun c p ↦ c * g p) c (vs.map cl)).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, v :: vs => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, hfg v,
      zipWith_comp_map' f g cl hfg cs vs]

lemma semS_clean (m : ℕ) (h : T.Tr (m + 1)) (v : GFrac (LC m)) :
    (T.MP (m + 1) h).sem v = T.sigP m (T.MP m h.of_succ) (cleanS (Fc := Fc) (us := us) m v).1 /
      T.sigP m (T.MP m h.of_succ) (cleanS (Fc := Fc) (us := us) m v).2 := by
  refine (T.sem_MP_succ m h v).trans ?_
  unfold cleanS
  split_ifs with hz
  · rw [(GPoly.isZero_iff (T.MP m h.of_succ) _).mp hz]
    simp [sigP]
  · rfl

/-- **The constant system at level `m`**: for constants `c`, `∑ cⱼ vⱼ = 0` in `F m` iff the
`ℚ`-columns `LCols m vs` combine to `0`. -/
theorem LCols_spec : ∀ (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (c : List Cc),
    c.length = vs.length →
    ((List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v) c vs).sum = 0 ↔
      lcombS (algebraMap ℚ Cc) c (LCols Fc us m vs) = 0)
  | 0, h, vs, c, hl => by
    have e : (List.zipWith (fun c v ↦ algebraMap Cc (T.F 0) c * (T.MP 0 h).sem v) c vs).sum =
        ∑ k ∈ Finset.range vs.length, algebraMap Cc (T.F 0) (c.getD k 0) *
          (T.MP 0 h).sem (vs.getD k []) := sum_zipWith_range _ 0 [] c vs hl
    have e2 : ((∑ k ∈ Finset.range vs.length, algebraMap Cc (T.F 0) (c.getD k 0) *
          (T.MP 0 h).sem (vs.getD k []) : T.F 0) : L) =
        ∑ k ∈ Finset.range vs.length, algebraMap Cc L (c.getD k 0) *
          (cM T.hC T.S T.hx Fc T.hSF).sem (vs.getD k []) := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [IntermediateField.coe_mul, T.sem_MP]
      rfl
    show _ ↔ lcombS (algebraMap ℚ Cc) c (curveCols Fc vs) = 0
    rw [e, ← curveCols_spec T.hC T.S T.hx Fc T.hSF vs c hl]
    exact ⟨fun h0 ↦ e2.symm.trans (by rw [h0]; rfl),
      fun h0 ↦ Subtype.ext (e2.trans (h0.trans (ZeroMemClass.coe_zero _).symm))⟩
  | m + 1, h, vs, c, hl => by
    set hm : T.Tr m := h.of_succ with hhm
    set M := T.MP m hm with hM
    have hinj := T.phi_injective (h m (by omega))
    have hden : ∀ v ∈ ((vs : List (GFrac (LC m))).map (cleanS (Fc := Fc) (us := us) m)),
        T.sigP m M v.2 ≠ 0 := by
      intro v hv
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
      unfold cleanS
      split_ifs with hz
      · rw [T.sigP_one]; exact one_ne_zero
      · exact (map_ne_zero_iff _ hinj).mpr fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
    have hP := σ_prodD_ne_zero (GPoly.mul (LO Fc us m)) [(LO Fc us m).one] (T.sigP m M)
      (T.sigP_mul m M) (T.sigP_one m M) _ hden
    set N := cross (GPoly.mul (LO Fc us m)) [(LO Fc us m).one]
      ((vs : List (GFrac (LC m))).map (cleanS (Fc := Fc) (us := us) m)) with hN
    have key := sum_cross (GPoly.mul (LO Fc us m)) [(LO Fc us m).one] (T.sigP m M)
      (T.sigP_mul m M) (T.sigP_one m M) ((vs : List (GFrac (LC m))).map
        (cleanS (Fc := Fc) (us := us) m)) (c.map (algebraMap Cc (T.F (m + 1)))) hden
    have e1 : (List.zipWith (fun c v ↦ algebraMap Cc (T.F (m + 1)) c * (T.MP (m + 1) h).sem v)
        c vs).sum = (List.zipWith (fun c p ↦ c * (T.sigP m M p.1 / T.sigP m M p.2))
          (c.map (algebraMap Cc (T.F (m + 1))))
          ((vs : List (GFrac (LC m))).map (cleanS (Fc := Fc) (us := us) m))).sum :=
      (zipWith_map_left' (algebraMap Cc (T.F (m + 1))) ((T.MP (m + 1) h).sem) c vs).trans
        (zipWith_comp_map' _ _ (cleanS (Fc := Fc) (us := us) m) (T.semS_clean m h) _ _)
    set Q := (List.zipWith (fun c y ↦ C (algebraMap Cc (T.F m) c) * GPoly.toPoly M y) c N).sum
      with hQ
    have e2 : (List.zipWith (fun c y ↦ c * T.sigP m M y) (c.map (algebraMap Cc (T.F (m + 1))))
        N).sum = T.phi m Q := T.sum_sigP m M c N
    have hstep : (List.zipWith (fun c v ↦ algebraMap Cc (T.F (m + 1)) c *
        (T.MP (m + 1) h).sem v) c vs).sum = 0 ↔ Q = 0 := by
      rw [e1]
      constructor
      · intro h0
        rw [h0, zero_mul, e2] at key
        exact (map_eq_zero_iff _ hinj).mp key
      · intro h0
        rw [e2, h0, map_zero] at key
        exact (mul_eq_zero.mp key.symm).resolve_right hP
    rw [hstep]
    have hNl : N.length = vs.length := by rw [hN, length_cross]; exact List.length_map _
    set K := (N.map List.length).foldr max 0 with hK
    have hlenK : ∀ p ∈ N, p.length ≤ K := fun p hp ↦ Tower.NestP.le_foldr_max _ _ (List.mem_map_of_mem hp)
    set blocks := (List.range K).map fun k ↦
      LCols Fc us m (N.map fun p ↦ p.getD k (LO Fc us m).zero) with hblocks
    have hcols : LCols Fc us (m + 1) vs = glueU vs.length (maxLen blocks) blocks := rfl
    rw [hcols, lcombS_glueU _ _ _ c blocks (fun B hB ↦ ⟨by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hB
      rw [length_LCols, List.length_map, hNl], fun a ha ↦ le_maxLen blocks B hB a ha⟩)]
    rw [Polynomial.ext_iff]
    simp only [coeff_zero]
    constructor
    · intro h0 B hB
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hB
      have := h0 k
      rw [T.coeff_sum_toPoly m M k c N] at this
      exact (LCols_spec m hm _ c (by rw [List.length_map, hNl]; exact hl)).mp this
    · intro h0 k
      rw [T.coeff_sum_toPoly m M k c N]
      by_cases hk : k < K
      · exact (LCols_spec m hm _ c (by rw [List.length_map, hNl]; exact hl)).mpr
          (h0 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
      · refine T.sum_zero_codes m M c _ fun v hv ↦ ?_
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
        exact List.getD_eq_default _ _ (by have := hlenK p hp; omega)

/-- **Soundness of the relations**: every basis vector `w` gives `∑ⱼ w[j] vⱼ = 0`. -/
theorem lrel_sound (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (w : CPoly ℚ)
    (hw : w ∈ lrel Fc us m vs) :
    (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v)
      ((List.range vs.length).map fun j ↦ algebraMap ℚ Cc (w.getD j 0)) vs).sum = 0 := by
  rw [T.LCols_spec m h vs _ (by simp)]
  have h0 := nullBasis_sound (LCols Fc us m vs) w hw
  rw [← length_LCols Fc us m vs, Tower.NestP.NestTower.lcombS_getD, lcombS_map_ns, h0, Polynomial.map_zero]

/-- **Completeness of the relations**: every relation with constant coefficients is a constant
combination of the basis vectors, componentwise. -/
theorem lrel_complete (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (c : List Cc)
    (hl : c.length = vs.length)
    (h0 : (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v) c vs).sum = 0) :
    ∃ β : List Cc, ∀ j, c.getD j 0 = ∑ k ∈ Finset.range (lrel Fc us m vs).length,
      β.getD k 0 * algebraMap ℚ Cc (((lrel Fc us m vs).getD k []).getD j 0) :=
  Tower.NestM.nullBasis_coeffs (LCols Fc us m vs) c (by rw [length_LCols]; exact hl)
    ((T.LCols_spec m h vs c hl).mp h0)

end LTower

end LT

end Curves
