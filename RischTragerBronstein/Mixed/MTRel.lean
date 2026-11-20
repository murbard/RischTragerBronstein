import RischTragerBronstein.Mixed.MTTower

/-!
# Mixed towers over a curve: constant linear relations

`mrel Fc ks m vs`: a `ℚ`-basis of the relations `∑ cⱼ vⱼ = 0` among values of level-`m` codes,
complete for constant coefficients in every realization (as `LTRel`, with kinds).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT
open Tower.NestP


open Tower.NestP

/-! ### Columns at every level -/

/-- **Columns of the constant system** `∑ cⱼ vⱼ = 0` over `ℚ`, at level `m`. -/
def MCols (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) : (m : ℕ) → List (LC m) → List (CPoly ℚ)
  | 0, vs => curveCols Fc vs
  | m + 1, vs =>
    let O := MO Fc ks m
    let N := cross (GPoly.mul O) [O.one] ((vs : List (GFrac (LC m))).map fun v ↦
      if GPoly.isZero O v.2 then (([] : GPoly (LC m)), [O.one]) else v)
    let K := (N.map List.length).foldr max 0
    let blocks := (List.range K).map fun k ↦ MCols Fc ks m (N.map fun p ↦ p.getD k O.zero)
    glueU vs.length (maxLen blocks) blocks

/-- **A basis of the constant relations** `∑ cⱼ vⱼ = 0` among level-`m` values. -/
def mrel (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) (vs : List (LC m)) : List (CPoly ℚ) :=
  nullBasis (MCols Fc ks m vs)

lemma length_MCols (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) :
    ∀ (m : ℕ) (vs : List (LC m)), (MCols Fc ks m vs).length = vs.length
  | 0, vs => length_curveCols Fc vs
  | m + 1, vs => by
    simp only [MCols]
    rw [length_glueU]
    intro B hB
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hB
    rw [length_MCols Fc ks m, List.length_map, length_cross]
    exact List.length_map _

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- `(F m)[X] → F (m + 1)` on codes. -/
noncomputable def sigP (m : ℕ) (M : CField (LC m) (T.F m) (MO Fc ks m)) (p : GPoly (LC m)) :
    T.F (m + 1) := T.phi m (GPoly.toPoly M p)

/-- Zero-denominator cleaning at level `m + 1`. -/
def cleanS (m : ℕ) (v : GFrac (LC m)) : GFrac (LC m) :=
  if GPoly.isZero (MO Fc ks m) v.2 then (([] : GPoly (LC m)), [(MO Fc ks m).one]) else v

lemma sigP_mul (m : ℕ) (M : CField (LC m) (T.F m) (MO Fc ks m)) (a b) :
    T.sigP m M (GPoly.mul (MO Fc ks m) a b) = T.sigP m M a * T.sigP m M b := by
  simp only [sigP, GPoly.toPoly_mul, map_mul]

lemma sigP_one (m : ℕ) (M : CField (LC m) (T.F m) (MO Fc ks m)) :
    T.sigP m M [(MO Fc ks m).one] = 1 := by
  simp only [sigP, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, M.sem_one, C_1,
    map_one]

lemma sum_sigP (m : ℕ) (M : CField (LC m) (T.F m) (MO Fc ks m)) :
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

lemma coeff_sum_toPoly (m : ℕ) (M : CField (LC m) (T.F m) (MO Fc ks m)) (k : ℕ) :
    ∀ (c : List Cc) (N : List (GPoly (LC m))),
      (List.zipWith (fun c y ↦ C (algebraMap Cc (T.F m) c) * GPoly.toPoly M y) c N).sum.coeff k =
        (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * M.sem v) c
          (N.map fun p ↦ p.getD k (MO Fc ks m).zero)).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, y :: N => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, coeff_add, coeff_C_mul,
      coeff_toPoly_getD']
    rw [coeff_sum_toPoly m M k cs N]

lemma sum_zero_codes (m : ℕ) (M : CField (LC m) (T.F m) (MO Fc ks m)) :
    ∀ (c : List Cc) (vs : List (LC m)), (∀ v ∈ vs, v = (MO Fc ks m).zero) →
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
    (T.MP (m + 1) h).sem v = T.sigP m (T.MP m h.of_succ) (cleanS (Fc := Fc) (ks := ks) m v).1 /
      T.sigP m (T.MP m h.of_succ) (cleanS (Fc := Fc) (ks := ks) m v).2 := by
  refine (T.sem_MP_succ m h v).trans ?_
  unfold cleanS
  split_ifs with hz
  · rw [(GPoly.isZero_iff (T.MP m h.of_succ) _).mp hz]
    simp [sigP]
  · rfl

/-- **The constant system at level `m`**: for constants `c`, `∑ cⱼ vⱼ = 0` in `F m` iff the
`ℚ`-columns `MCols m vs` combine to `0`. -/
theorem MCols_spec : ∀ (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (c : List Cc),
    c.length = vs.length →
    ((List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v) c vs).sum = 0 ↔
      lcombS (algebraMap ℚ Cc) c (MCols Fc ks m vs) = 0)
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
    have hden : ∀ v ∈ ((vs : List (GFrac (LC m))).map (cleanS (Fc := Fc) (ks := ks) m)),
        T.sigP m M v.2 ≠ 0 := by
      intro v hv
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
      unfold cleanS
      split_ifs with hz
      · rw [T.sigP_one]; exact one_ne_zero
      · exact (map_ne_zero_iff _ hinj).mpr fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
    have hP := σ_prodD_ne_zero (GPoly.mul (MO Fc ks m)) [(MO Fc ks m).one] (T.sigP m M)
      (T.sigP_mul m M) (T.sigP_one m M) _ hden
    set N := cross (GPoly.mul (MO Fc ks m)) [(MO Fc ks m).one]
      ((vs : List (GFrac (LC m))).map (cleanS (Fc := Fc) (ks := ks) m)) with hN
    have key := sum_cross (GPoly.mul (MO Fc ks m)) [(MO Fc ks m).one] (T.sigP m M)
      (T.sigP_mul m M) (T.sigP_one m M) ((vs : List (GFrac (LC m))).map
        (cleanS (Fc := Fc) (ks := ks) m)) (c.map (algebraMap Cc (T.F (m + 1)))) hden
    have e1 : (List.zipWith (fun c v ↦ algebraMap Cc (T.F (m + 1)) c * (T.MP (m + 1) h).sem v)
        c vs).sum = (List.zipWith (fun c p ↦ c * (T.sigP m M p.1 / T.sigP m M p.2))
          (c.map (algebraMap Cc (T.F (m + 1))))
          ((vs : List (GFrac (LC m))).map (cleanS (Fc := Fc) (ks := ks) m))).sum :=
      (zipWith_map_left' (algebraMap Cc (T.F (m + 1))) ((T.MP (m + 1) h).sem) c vs).trans
        (zipWith_comp_map' _ _ (cleanS (Fc := Fc) (ks := ks) m) (T.semS_clean m h) _ _)
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
      MCols Fc ks m (N.map fun p ↦ p.getD k (MO Fc ks m).zero) with hblocks
    have hcols : MCols Fc ks (m + 1) vs = glueU vs.length (maxLen blocks) blocks := rfl
    rw [hcols, lcombS_glueU _ _ _ c blocks (fun B hB ↦ ⟨by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hB
      rw [length_MCols, List.length_map, hNl], fun a ha ↦ le_maxLen blocks B hB a ha⟩)]
    rw [Polynomial.ext_iff]
    simp only [coeff_zero]
    constructor
    · intro h0 B hB
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hB
      have := h0 k
      rw [T.coeff_sum_toPoly m M k c N] at this
      exact (MCols_spec m hm _ c (by rw [List.length_map, hNl]; exact hl)).mp this
    · intro h0 k
      rw [T.coeff_sum_toPoly m M k c N]
      by_cases hk : k < K
      · exact (MCols_spec m hm _ c (by rw [List.length_map, hNl]; exact hl)).mpr
          (h0 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
      · refine T.sum_zero_codes m M c _ fun v hv ↦ ?_
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
        exact List.getD_eq_default _ _ (by have := hlenK p hp; omega)

/-- **Soundness of the relations**: every basis vector `w` gives `∑ⱼ w[j] vⱼ = 0`. -/
theorem mrel_sound (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (w : CPoly ℚ)
    (hw : w ∈ mrel Fc ks m vs) :
    (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v)
      ((List.range vs.length).map fun j ↦ algebraMap ℚ Cc (w.getD j 0)) vs).sum = 0 := by
  rw [T.MCols_spec m h vs _ (by simp)]
  have h0 := nullBasis_sound (MCols Fc ks m vs) w hw
  rw [← length_MCols Fc ks m vs, Tower.NestP.NestTower.lcombS_getD, lcombS_map_ns, h0, Polynomial.map_zero]

/-- **Completeness of the relations**: every relation with constant coefficients is a constant
combination of the basis vectors, componentwise. -/
theorem mrel_complete (m : ℕ) (h : T.Tr m) (vs : List (LC m)) (c : List Cc)
    (hl : c.length = vs.length)
    (h0 : (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v) c vs).sum = 0) :
    ∃ β : List Cc, ∀ j, c.getD j 0 = ∑ k ∈ Finset.range (mrel Fc ks m vs).length,
      β.getD k 0 * algebraMap ℚ Cc (((mrel Fc ks m vs).getD k []).getD j 0) :=
  Tower.NestM.nullBasis_coeffs (MCols Fc ks m vs) c (by rw [length_MCols]; exact hl)
    ((T.MCols_spec m h vs c hl).mp h0)

end MTower

end Curves.MT
