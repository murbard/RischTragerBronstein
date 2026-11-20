import RischTragerBronstein.Mixed.LTExactStep
import RischTragerBronstein.Mixed.CurveOverConst

/-!
# Towers of logarithms over a curve: transfer between realizations

* `evL_congr`: the value of a level-`m` code only depends on `t₀, …, t_{m-1}`;
* `LTower.mapT`: a realization pushed along a differential embedding `j : L → L'`, with a curve
  over new constants (`ev` commutes with `j`);
* **`tr_transfer`**: transcendence of the generators transfers between *any* two realizations of
  the same code data. A solution of `y′ = ηₘ` in the second one gives, by completeness of `lex`
  there, a returned code with non-zero parameter; by soundness in the first one it is an
  antiderivative of `ηₘ` there.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.LT

open CPoly Sup

section Congr

variable {L : Type*} [Field L]

/-- **The value of a level-`m` code only depends on the generators below `m`.** -/
lemma evL_congr (M0 : LC 0 → L) (ts ts' : ℕ → L) :
    ∀ (m : ℕ), (∀ i < m, ts i = ts' i) → ∀ q : LC m, evL M0 ts m q = evL M0 ts' m q
  | 0, _, _ => rfl
  | m + 1, h, q => by
    have hm := h m (by omega)
    have ih := evL_congr M0 ts ts' m fun i hi ↦ h i (by omega)
    have hf : ∀ l : List (LC m), l.foldr (fun a acc ↦ evL M0 ts m a + ts m * acc) 0 =
        l.foldr (fun a acc ↦ evL M0 ts' m a + ts' m * acc) 0 := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ihl => rw [List.foldr_cons, List.foldr_cons, ihl, ih a, hm]
    simp only [evL, hf]

end Congr

universe u v

variable {Fc : BPoly ℚ} {us : (m : ℕ) → LC m}

section Transfer

variable {C₁ L₁ : Type u} [Field C₁] [Field L₁] [Algebra C₁ L₁] [Differential C₁]
  [Differential L₁] [DifferentialAlgebra C₁ L₁] [CharZero C₁] [CharZero L₁]
variable {C₂ L₂ : Type v} [Field C₂] [Field L₂] [Algebra C₂ L₂] [Differential C₂]
  [Differential L₂] [DifferentialAlgebra C₂ L₂] [CharZero C₂] [CharZero L₂]

include C₁ L₁ in
/-- **Transcendence transfers** between realizations of the same code data. -/
theorem tr_transfer (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (T₁ : LTower Fc us C₁ L₁) (T₂ : LTower Fc us C₂ L₂) (m : ℕ) (hm : m < T₂.n)
    (h₁ : T₁.Tr (m + 1)) (h₂ : T₂.Tr m) : Transcendental (T₂.F m) (T₂.ts m) := by
  refine transcendental_primitive (T₂.eta m) (T₂.ht' hm) fun y hy ↦ ?_
  -- completeness in `T₂`
  obtain ⟨-, hcomp⟩ := T₂.lex_spec hmon hdeg m h₂ [etaC Fc us m]
  obtain ⟨β, hβ, -⟩ := hcomp [1] (fun i hi ↦ by
      rcases i with _ | i
      · simp at hi
      · rfl) y (by
    rw [LTower.sumK, List.length_singleton, Finset.sum_range_one, List.getD_cons_zero,
      List.getD_cons_zero, map_one, one_mul, T₂.sem_eta, hy])
  have h1 := hβ 0
  rw [List.getD_cons_zero] at h1
  set sols := lex Fc us m [etaC Fc us m] with hsols
  have hex : ∃ k < sols.length, (sols.getD k ([], zc Fc us m)).1.getD 0 0 ≠ 0 := by
    by_contra hall
    push Not at hall
    rw [Finset.sum_eq_zero fun k hk ↦ by
      rw [hall k (Finset.mem_range.mp hk), map_zero, mul_zero]] at h1
    exact one_ne_zero h1
  obtain ⟨k, hk, hr0⟩ := hex
  set r := sols.getD k ([], zc Fc us m) with hr
  have hmem : r ∈ lex Fc us m [etaC Fc us m] := by
    rw [hr, hsols, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  -- soundness in `T₁`
  have h₁m : T₁.Tr m := h₁.of_succ
  obtain ⟨hsnd, -⟩ := T₁.lex_spec hmon hdeg m h₁m [etaC Fc us m]
  have hs := hsnd r hmem
  rw [LTower.sumQ, List.length_singleton, Finset.sum_range_one, List.getD_cons_zero,
    T₁.sem_eta] at hs
  set q0 : ℚ := r.1.getD 0 0 with hq0
  have hq : ((q0 : ℚ) : T₁.F m) ≠ 0 := by exact_mod_cast hr0
  apply T₁.eta_not_deriv m (h₁ m (by omega)) ((T₁.MP m h₁m).sem r.2 / (q0 : T₁.F m))
  rw [Derivation.leibniz_div, T₁.deriv_ratCast, hs]
  simp only [smul_eq_mul, mul_zero, sub_zero]
  field_simp

include C₁ L₁ in
/-- Transcendence of all the generators below `m` transfers. -/
theorem Tr_transfer (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (T₁ : LTower Fc us C₁ L₁) (T₂ : LTower Fc us C₂ L₂) :
    ∀ m, m ≤ T₂.n → T₁.Tr m → T₂.Tr m
  | 0, _, _ => fun i hi ↦ absurd hi (Nat.not_lt_zero i)
  | m + 1, hm, h₁ => by
    have ih := Tr_transfer hmon hdeg T₁ T₂ m (by omega) h₁.of_succ
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih i hi
    · exact tr_transfer hmon hdeg T₁ T₂ i (by omega) h₁ ih

end Transfer

/-! ### Lifting a realization to an extension -/

/-- The constants of a differential field, with the zero derivation. -/
noncomputable scoped instance instDifferentialConstants (E : Type*) [Field E] [Differential E] :
    Differential (constants E) := ⟨0⟩

scoped instance instDifferentialAlgebraConstants (E : Type*) [Field E] [Differential E] :
    DifferentialAlgebra (constants E) E := ⟨fun c ↦ c.2⟩

scoped instance instCharZeroConstants (E : Type*) [Field E] [CharZero E] [Differential E] :
    CharZero (constants E) := ⟨fun a b h ↦ by
  have := congrArg (fun z : constants E ↦ (z : E)) h
  simpa using this⟩

section Lift

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **The realization in an extension**, over its constants. -/
theorem LTower.exists_lift (T : LTower Fc us Cc L) (E : Type v) [Field E] [Differential E]
    [Algebra L E] [DifferentialAlgebra L E] [CharZero E] :
    ∃ T' : LTower Fc us (constants E) E, T'.n = T.n ∧
      (∀ i, T'.ts i = algebraMap L E (T.ts i)) ∧
      (∀ m q, T'.ev m q = algebraMap L E (T.ev m q)) ∧
      (∀ m, ∀ z ∈ T.F m, algebraMap L E z ∈ T'.F m) := by
  obtain ⟨φ, SL, hxL, hSLx, hSLy, hSLF, hφ, hmem⟩ := curve_over_constants T.hC T.S T.hx T.hconst E
  have hSFL : SL.F = (toB Fc).map (mapRingHom (algebraMap ℚ (constants E))) := by
    rw [hSLF, T.hSF, Polynomial.map_map, mapRingHom_comp]
    congr 2
    exact RingHom.ext_rat _ _
  set ψ := algebraMap L E with hψ
  have hCc : ∀ c : constants E, c′ = 0 := fun _ ↦ rfl
  have hsem : ∀ a, (cM hCc SL hxL Fc hSFL).sem a = ψ ((cM T.hC T.S T.hx Fc T.hSF).sem a) :=
    fun a ↦ sem_cM_map T.hC T.S T.hx Fc T.hSF hCc SL hxL hSFL ψ hSLx hSLy a
  have hev : ∀ m q, evL (cM hCc SL hxL Fc hSFL).sem (fun i ↦ ψ (T.ts i)) m q = ψ (T.ev m q) :=
    fun m q ↦ map_evL ψ _ _ hsem T.ts m q
  have hψd : ∀ z : L, (ψ z)′ = ψ z′ := fun z ↦ deriv_algebraMap z
  let T' : LTower Fc us (constants E) E :=
    { S := SL
      hC := hCc
      hx := hxL
      hSF := hSFL
      n := T.n
      ts := fun i ↦ ψ (T.ts i)
      hts := fun m hm ↦ by simp only [T.hts m hm, map_zero]
      hu0 := fun m hm ↦ by
        rw [hev]; exact (map_ne_zero ψ).mpr (T.hu0 m hm)
      ht := fun m hm ↦ by
        rw [hev, hψd, T.ht m hm, logDeriv, logDeriv, map_div₀, hψd]
      hconst := fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩ }
  have hmemT : ∀ m, ∀ z ∈ T.F m, ψ z ∈ T'.F m := by
    intro m
    induction m with
    | zero => exact fun z hz ↦ hmem z hz
    | succ m ih =>
      intro z hz
      let N : IntermediateField (T.F m) L :=
        { carrier := {w | ψ w ∈ T'.F (m + 1)}
          mul_mem' := fun {a b} ha hb ↦ by
            change ψ (a * b) ∈ T'.F (m + 1); rw [map_mul]; exact mul_mem ha hb
          one_mem' := by change ψ 1 ∈ T'.F (m + 1); rw [map_one]; exact one_mem _
          add_mem' := fun {a b} ha hb ↦ by
            change ψ (a + b) ∈ T'.F (m + 1); rw [map_add]; exact add_mem ha hb
          zero_mem' := by change ψ 0 ∈ T'.F (m + 1); rw [map_zero]; exact zero_mem _
          algebraMap_mem' := fun f ↦ T'.le_succ m (ih f f.2)
          inv_mem' := fun a ha ↦ by
            change ψ a⁻¹ ∈ T'.F (m + 1); rw [map_inv₀]; exact inv_mem ha }
      have hle : IntermediateField.adjoin (T.F m) {T.ts m} ≤ N := by
        rw [IntermediateField.adjoin_le_iff]
        rintro w rfl
        exact T'.ts_mem m
      exact hle ((T.mem_F_succ).mp hz)
  exact ⟨T', rfl, fun _ ↦ rfl, hev, hmemT⟩

end Lift

/-! ### The curve inside an intermediate field -/

section Restrict

variable {Kc K : Type*} [Field Kc] [Field K] [Algebra Kc K]
variable (S : CurveData Kc K) (K' : IntermediateField Kc K) (hxK : S.x ∈ K') (hyK : S.y ∈ K')

/-- Evaluation commutes with the inclusion of `K'`. -/
lemma coe_evalR (G : Kc[X][X]) :
    (((G.map (aeval (⟨S.x, hxK⟩ : K')).toRingHom).eval (⟨S.y, hyK⟩ : K') : K') : K) =
      S.evXY G := by
  have h1 : K'.val.toRingHom.comp (aeval (R := Kc) (⟨S.x, hxK⟩ : K')).toRingHom =
      (aeval (R := Kc) S.x).toRingHom := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · simp
    · simp
  change K'.val.toRingHom _ = _
  rw [eval_map, Polynomial.hom_eval₂]
  erw [h1]
  rw [CurveData.evXY, eval_map]
  rfl

/-- **The curve inside an intermediate field containing `x` and `y`.** -/
noncomputable def restrictC : CurveData Kc K' where
  x := ⟨S.x, hxK⟩
  y := ⟨S.y, hyK⟩
  F := S.F
  htr := fun ⟨p, hp0, hp⟩ ↦ S.htr ⟨p, hp0, by
    have := congrArg K'.val hp
    rwa [← Polynomial.aeval_algHom_apply, map_zero] at this⟩
  monic := S.monic
  irr := fun G hG hG0 ↦ S.irr G hG (by
    have := congrArg (fun z : K' ↦ (z : K)) hG0
    rwa [coe_evalR, ZeroMemClass.coe_zero] at this)
  root := Subtype.ext (by rw [coe_evalR, ZeroMemClass.coe_zero]; exact S.root)

lemma restrictC_gen (z : K') (hz : (z : K) ∈ Kc⟮S.x⟯⟮S.y⟯) :
    z ∈ Kc⟮(restrictC S K' hxK hyK).x⟯⟮(restrictC S K' hxK hyK).y⟯ := by
  rw [← IntermediateField.mem_restrictScalars Kc, adjoin_simple_adjoin_simple] at hz ⊢
  have hmap : (Kc⟮(restrictC S K' hxK hyK).x, (restrictC S K' hxK hyK).y⟯).map K'.val =
      Kc⟮S.x, S.y⟯ := by
    rw [IntermediateField.adjoin_map]
    congr 1
    ext w
    simp [restrictC, Set.image_insert_eq]
  rw [← hmap] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  rwa [show w = z from Subtype.ext hwz] at hw

end Restrict

/-! ### The sub-tower of height `k` inside `F k` -/

section Sub

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

instance LTower.instDifferentialAlgebraCcF (T : LTower Fc us Cc L) (m : ℕ) :
    DifferentialAlgebra Cc (T.F m) :=
  ⟨fun c ↦ Subtype.ext (by
    rw [LTower.coe_deriv]
    exact deriv_algebraMap (A := Cc) (B := L) c)⟩

/-- **The sub-tower of height `k`**, realized inside the field `F k`; it generates `F k`. -/
theorem LTower.exists_sub (T : LTower Fc us Cc L) (k : ℕ) (hk : k ≤ T.n) :
    ∃ T' : LTower Fc us Cc (T.F k), T'.n = k ∧
      (∀ m ≤ k, ∀ q, ((T'.ev m q : T.F k) : L) = T.ev m q) ∧
      (∀ z : T.F k, z ∈ T'.F k) ∧ (∀ i < k, ((T'.ts i : T.F k) : L) = T.ts i) := by
  have hx0 : T.S.x ∈ T.F k := T.F_mono (Nat.zero_le k)
    ((Cc⟮T.S.x⟯⟮T.S.y⟯).algebraMap_mem ⟨T.S.x, mem_adjoin_simple_self Cc T.S.x⟩)
  have hy0 : T.S.y ∈ T.F k := T.F_mono (Nat.zero_le k) (mem_adjoin_simple_self _ T.S.y)
  set S' := restrictC T.S (T.F k) hx0 hy0 with hS'
  have hx' : S'.x′ = 1 := Subtype.ext (by rw [LTower.coe_deriv]; exact T.hx)
  set j := algebraMap (T.F k) L with hj
  have hsem0 : ∀ a, (cM T.hC T.S T.hx Fc T.hSF).sem a = j ((cM T.hC S' hx' Fc T.hSF).sem a) :=
    fun a ↦ sem_cM_map T.hC S' hx' Fc T.hSF T.hC T.S T.hx T.hSF j rfl rfl a
  set ts' : ℕ → T.F k := fun i ↦ if h : i < k then
    ⟨T.ts i, T.F_mono (by omega : i + 1 ≤ k) (T.ts_mem i)⟩ else 0 with hts'
  have hts'j : ∀ i < k, j (ts' i) = T.ts i := fun i hi ↦ by
    simp only [hts', dif_pos hi]; rfl
  have hev : ∀ m ≤ k, ∀ q, j (evL (cM T.hC S' hx' Fc T.hSF).sem ts' m q) = T.ev m q := by
    intro m hm q
    rw [← map_evL j _ _ hsem0 ts' m q]
    exact evL_congr _ _ _ m (fun i hi ↦ hts'j i (by omega)) q
  let T' : LTower Fc us Cc (T.F k) :=
    { S := S'
      hC := T.hC
      hx := hx'
      hSF := T.hSF
      n := k
      ts := ts'
      hts := fun m hm ↦ by simp only [hts', dif_neg (show ¬m < k by omega)]
      hu0 := fun m hm h0 ↦ T.hu0 m (by omega) (by
        have := hev m hm.le (us m)
        rw [h0, map_zero] at this
        exact this.symm)
      ht := fun m hm ↦ Subtype.ext (by
        rw [LTower.coe_deriv]
        change (j (ts' m))′ = j (logDeriv (evL (cM T.hC S' hx' Fc T.hSF).sem ts' m (us m)))
        rw [hts'j m hm, T.ht m (by omega), ← logDeriv_algebraMap, hev m hm.le])
      hconst := fun z hz ↦ by
        obtain ⟨c, hc⟩ := T.hconst (z : L) (by rw [← LTower.coe_deriv, hz]; rfl)
        exact ⟨c, Subtype.ext hc⟩ }
  have hgen : ∀ m ≤ k, ∀ z : T.F k, (z : L) ∈ T.F m → z ∈ T'.F m := by
    intro m
    induction m with
    | zero => exact fun _ z hz ↦ restrictC_gen T.S (T.F k) hx0 hy0 z hz
    | succ m ih =>
      intro hm z hz
      let N : IntermediateField (T.F m) L :=
        { carrier := {w | ∃ h : w ∈ T.F k, (⟨w, h⟩ : T.F k) ∈ T'.F (m + 1)}
          mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ ↦ ⟨mul_mem ha hb, mul_mem ha' hb'⟩
          one_mem' := ⟨one_mem _, one_mem _⟩
          add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ ↦ ⟨add_mem ha hb, add_mem ha' hb'⟩
          zero_mem' := ⟨zero_mem _, zero_mem _⟩
          algebraMap_mem' := fun f ↦ ⟨T.F_mono (by omega) f.2,
            T'.le_succ m (ih (by omega) ⟨f, T.F_mono (by omega) f.2⟩ f.2)⟩
          inv_mem' := fun a ⟨ha, ha'⟩ ↦ ⟨inv_mem ha, inv_mem ha'⟩ }
      have hle : IntermediateField.adjoin (T.F m) {T.ts m} ≤ N := by
        rw [IntermediateField.adjoin_le_iff]
        rintro w rfl
        refine ⟨T.F_mono (by omega : m + 1 ≤ k) (T.ts_mem m), ?_⟩
        have : (⟨T.ts m, T.F_mono (by omega : m + 1 ≤ k) (T.ts_mem m)⟩ : T.F k) = T'.ts m := by
          change _ = ts' m
          simp only [hts', dif_pos (show m < k by omega)]
        rw [this]
        exact T'.ts_mem m
      obtain ⟨h, h'⟩ := hle ((T.mem_F_succ).mp hz)
      exact h'
  exact ⟨T', rfl, fun m hm q ↦ hev m hm q, fun z ↦ hgen k le_rfl z z.2, hts'j⟩

end Sub

end Curves.LT
