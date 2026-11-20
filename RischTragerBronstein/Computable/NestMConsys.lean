import RischTragerBronstein.Computable.NestMTower
import RischTragerBronstein.Computable.NestPConsys

/-!
# Constant linear systems in mixed towers: soundness and completeness

As `NestPConsys`: for constants `cⱼ ∈ Kc`, `∑ cⱼ vⱼ = 0` in `F m` iff the columns
`colsOf ks m vs` over `ℚ` have `∑ cⱼ colⱼ = 0` (`colsOf_spec`); `consys_sound`,
`consys_complete`.
-/

open Polynomial Differential CPoly

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP

lemma length_colsOf (ks : (m : ℕ) → KindN m) :
    ∀ (m : ℕ) (vs : List (Code (m + 1))), (colsOf ks m vs).length = vs.length
  | 0, vs => by
    simp only [colsOf, length_cross]
    exact List.length_map _
  | m + 1, vs => by
    simp only [colsOf]
    rw [length_glueU]
    intro B hB
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hB
    rw [length_colsOf ks m, List.length_map, length_cross]
    exact List.length_map _

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}

namespace NestMTower

variable (T : NestMTower Kc E ks)

lemma model0_sem_eq (q : GFrac ℚ) :
    T.model0.sem q = T.phi0 ((CPoly.toPoly q.1).map (algebraMap ℚ Kc)) /
      T.phi0 ((CPoly.toPoly q.2).map (algebraMap ℚ Kc)) := by
  change T.phi0 (GPoly.toPoly _ q.1) / T.phi0 (GPoly.toPoly _ q.2) = _
  rw [toPoly_ofHom', toPoly_ofHom']

lemma phi0_C (c : Kc) : T.phi0 (C c) = algebraMap Kc (T.F 0) c :=
  Subtype.ext (by rw [coe_phi0, aeval_C]; rfl)

lemma phi_C (m : ℕ) (z : T.F m) : T.phi m (C z) =
    IntermediateField.inclusion (T.le_succ m) z :=
  Subtype.ext (by rw [coe_phi, aeval_C]; rfl)

lemma algebraMap_succ (m : ℕ) (c : Kc) :
    algebraMap Kc (T.F (m + 1)) c = T.phi m (C (algebraMap Kc (T.F m) c)) := by
  rw [T.phi_C]; rfl

lemma zipWith_sem_eq {γ K : Type*} [Field K] (f g : γ → K) (hfg : ∀ v, f v = g v) :
    ∀ (c : List K) (vs : List γ), (List.zipWith (fun c v ↦ c * f v) c vs).sum =
      (List.zipWith (fun c v ↦ c * g v) c vs).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, v :: vs => by
    simp only [List.zipWith_cons_cons, List.sum_cons, hfg v, zipWith_sem_eq f g hfg cs vs]

lemma zipWith_map_left {γ K : Type*} [Field K] (a : Kc → K) (f : γ → K) :
    ∀ (c : List Kc) (vs : List γ), (List.zipWith (fun c v ↦ a c * f v) c vs).sum =
      (List.zipWith (fun c v ↦ c * f v) (c.map a) vs).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, v :: vs => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons,
      zipWith_map_left a f cs vs]

lemma zipWith_map_right {γ K : Type*} [Field K] (f : γ → K) (cl : γ → γ) :
    ∀ (c : List K) (vs : List γ), (List.zipWith (fun c v ↦ c * f v) c (vs.map cl)).sum =
      (List.zipWith (fun c v ↦ c * f (cl v)) c vs).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, v :: vs => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons,
      zipWith_map_right f cl cs vs]

/-- `ℚ[X] → F 0`. -/
noncomputable def psiP (p : CPoly ℚ) : T.F 0 := T.phi0 ((toPoly p).map (algebraMap ℚ Kc))

/-- `(F m)[X] → F (m + 1)` on codes. -/
noncomputable def sigP (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsM ks m))
    (p : GPoly (Code (m + 1))) : T.F (m + 1) := T.phi m (GPoly.toPoly M p)

/-- Zero-denominator cleaning at level `0`. -/
def clean0 (v : GFrac ℚ) : GFrac ℚ :=
  if CPoly.isZero v.2 then (([] : CPoly ℚ), ([1] : CPoly ℚ)) else v

/-- Zero-denominator cleaning at level `m + 1`. -/
def cleanS (m : ℕ) (v : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) :
    GPoly (Code (m + 1)) × GPoly (Code (m + 1)) :=
  if GPoly.isZero (opsM ks m) v.2 then (([] : GPoly (Code (m + 1))), [(opsM ks m).one]) else v

lemma colsOf_zero (vs : List (Code 1)) :
    colsOf ks 0 vs = cross CPoly.mul [1] (vs.map clean0) := rfl

lemma psiP_mul (a b : CPoly ℚ) : T.psiP (CPoly.mul a b) = T.psiP a * T.psiP b := by
  simp only [psiP, toPoly_mul, Polynomial.map_mul, map_mul]

lemma psiP_one : T.psiP [1] = 1 := by simp [psiP, CPoly.toPoly]

lemma sigP_mul (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsM ks m)) (a b) :
    T.sigP m M (GPoly.mul (opsM ks m) a b) = T.sigP m M a * T.sigP m M b := by
  simp only [sigP, GPoly.toPoly_mul, map_mul]

lemma sigP_one (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsM ks m)) :
    T.sigP m M [(opsM ks m).one] = 1 := by
  simp only [sigP, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, M.sem_one, C_1,
    map_one]

lemma sum_psiP : ∀ (c : List Kc) (N : List (CPoly ℚ)),
    (List.zipWith (fun c y ↦ c * T.psiP y) (c.map (algebraMap Kc (T.F 0))) N).sum =
      T.phi0 (lcombS (algebraMap ℚ Kc) c N)
  | [], _ => by simp [lcombS]
  | _ :: _, [] => by simp [lcombS]
  | c :: cs, y :: N => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, lcombS, map_add, map_mul,
      T.phi0_C]
    rw [sum_psiP cs N]
    rfl

lemma sum_sigP (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsM ks m)) :
    ∀ (c : List Kc) (N : List (GPoly (Code (m + 1)))),
      (List.zipWith (fun c y ↦ c * T.sigP m M y) (c.map (algebraMap Kc (T.F (m + 1)))) N).sum =
        T.phi m (List.zipWith (fun c y ↦ C (algebraMap Kc (T.F m) c) * GPoly.toPoly M y) c N).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, y :: N => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, map_add, map_mul,
      T.algebraMap_succ, sigP]
    rw [← sum_sigP m M cs N]
    rfl

lemma coeff_sum_toPoly (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsM ks m)) (k : ℕ) :
    ∀ (c : List Kc) (N : List (GPoly (Code (m + 1)))),
      (List.zipWith (fun c y ↦ C (algebraMap Kc (T.F m) c) * GPoly.toPoly M y) c N).sum.coeff k =
        (List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * M.sem v) c
          (N.map fun p ↦ p.getD k (opsM ks m).zero)).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, y :: N => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, coeff_add, coeff_C_mul,
      coeff_toPoly_getD']
    rw [coeff_sum_toPoly m M k cs N]

lemma sum_zero_codes (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsM ks m)) :
    ∀ (c : List Kc) (vs : List (Code (m + 1))), (∀ v ∈ vs, v = (opsM ks m).zero) →
      (List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * M.sem v) c vs).sum = 0
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | c :: cs, v :: vs, h => by
    simp only [List.zipWith_cons_cons, List.sum_cons, h v List.mem_cons_self, M.sem_zero,
      mul_zero, zero_add]
    exact sum_zero_codes m M cs vs fun w hw ↦ h w (List.mem_cons_of_mem _ hw)

lemma zipWith_comp_map {γ δ K : Type*} [Field K] (f : γ → K) (g : δ → K) (cl : γ → δ)
    (hfg : ∀ v, f v = g (cl v)) : ∀ (c : List K) (vs : List γ),
    (List.zipWith (fun c v ↦ c * f v) c vs).sum = (List.zipWith (fun c p ↦ c * g p) c (vs.map cl)).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, v :: vs => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, hfg v,
      zipWith_comp_map f g cl hfg cs vs]

lemma sem0_clean (h : T.Tr 0) (v : GFrac ℚ) :
    (T.MP 0 h).sem v = T.psiP (clean0 v).1 / T.psiP (clean0 v).2 := by
  refine (T.model0_sem_eq v).trans ?_
  unfold clean0
  split_ifs with hz
  · rw [(isZero_iff _).mp hz]
    simp [psiP, CPoly.toPoly]
  · rfl

lemma semS_clean (m : ℕ) (h : T.Tr (m + 1)) (v : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) :
    (T.MP (m + 1) h).sem v = T.sigP m (T.MP m fun i hi ↦ h i (by omega)) (cleanS (ks := ks) m v).1 /
      T.sigP m (T.MP m fun i hi ↦ h i (by omega)) (cleanS (ks := ks) m v).2 := by
  refine (T.sem_MP_succ m h v).trans ?_
  unfold cleanS
  split_ifs with hz
  · rw [(GPoly.isZero_iff (T.MP m fun i hi ↦ h i (by omega)) _).mp hz]
    simp [sigP]
  · rfl

/-- **The constant system at level `m`**: for constants `c`, `∑ cⱼ vⱼ = 0` in `F m` iff the
`ℚ`-columns `colsOf ks m vs` combine to `0`. -/
theorem colsOf_spec : ∀ (m : ℕ) (h : T.Tr m) (vs : List (Code (m + 1))) (c : List Kc),
    c.length = vs.length →
    ((List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem v) c vs).sum = 0 ↔
      lcombS (algebraMap ℚ Kc) c (colsOf ks m vs) = 0)
  | 0, h, vs, c, hl => by
    have hinj : Function.Injective (T.phi0.comp (mapRingHom (algebraMap ℚ Kc))) :=
      T.phi0_injective.comp (Polynomial.map_injective _ (algebraMap ℚ Kc).injective)
    have hden : ∀ v ∈ ((vs : List (GFrac ℚ)).map clean0), T.psiP v.2 ≠ 0 := by
      intro v hv
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
      unfold clean0
      split_ifs with hz
      · rw [T.psiP_one]; exact one_ne_zero
      · exact (map_ne_zero_iff _ hinj).mpr fun h0 ↦ hz ((isZero_iff _).mpr h0)
    have hP := σ_prodD_ne_zero CPoly.mul [1] T.psiP T.psiP_mul T.psiP_one _ hden
    have key := sum_cross CPoly.mul [1] T.psiP T.psiP_mul T.psiP_one ((vs : List (GFrac ℚ)).map clean0)
      (c.map (algebraMap Kc (T.F 0))) hden
    have e1 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F 0) c * (T.MP 0 h).sem v) c vs).sum =
        (List.zipWith (fun c p ↦ c * (T.psiP p.1 / T.psiP p.2)) (c.map (algebraMap Kc (T.F 0)))
          ((vs : List (GFrac ℚ)).map clean0)).sum :=
      (zipWith_map_left (algebraMap Kc (T.F 0)) ((T.MP 0 h).sem) c vs).trans
        (zipWith_comp_map (γ := GFrac ℚ) (δ := GFrac ℚ) _ _ clean0 (T.sem0_clean h) _ _)
    have e2 := T.sum_psiP c (cross CPoly.mul [1] ((vs : List (GFrac ℚ)).map clean0))
    rw [e1]
    constructor
    · intro h0
      rw [h0, zero_mul, e2] at key
      exact (map_eq_zero_iff _ T.phi0_injective).mp key
    · intro h0
      have h0' : lcombS (algebraMap ℚ Kc) c
          (cross CPoly.mul [1] ((vs : List (GFrac ℚ)).map clean0)) = 0 := h0
      rw [e2, h0', map_zero] at key
      exact (mul_eq_zero.mp key.symm).resolve_right hP
  | m + 1, h, vs, c, hl => by
    set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
    set M := T.MP m hm with hM
    have hinj := T.phi_injective (h m (by omega))
    have hden : ∀ v ∈ ((vs : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))).map
        (cleanS (ks := ks) m)), T.sigP m M v.2 ≠ 0 := by
      intro v hv
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
      unfold cleanS
      split_ifs with hz
      · rw [T.sigP_one]; exact one_ne_zero
      · exact (map_ne_zero_iff _ hinj).mpr fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
    have hP := σ_prodD_ne_zero (GPoly.mul (opsM ks m)) [(opsM ks m).one] (T.sigP m M)
      (T.sigP_mul m M) (T.sigP_one m M) _ hden
    set N := cross (GPoly.mul (opsM ks m)) [(opsM ks m).one]
      ((vs : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))).map (cleanS (ks := ks) m))
      with hN
    have key := sum_cross (GPoly.mul (opsM ks m)) [(opsM ks m).one] (T.sigP m M) (T.sigP_mul m M)
      (T.sigP_one m M) ((vs : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))).map
        (cleanS (ks := ks) m)) (c.map (algebraMap Kc (T.F (m + 1)))) hden
    have e1 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c * (T.MP (m + 1) h).sem v)
        c vs).sum = (List.zipWith (fun c p ↦ c * (T.sigP m M p.1 / T.sigP m M p.2))
          (c.map (algebraMap Kc (T.F (m + 1))))
          ((vs : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))).map
            (cleanS (ks := ks) m))).sum :=
      (zipWith_map_left (algebraMap Kc (T.F (m + 1))) ((T.MP (m + 1) h).sem) c vs).trans
        (zipWith_comp_map _ _ (cleanS (ks := ks) m) (T.semS_clean m h) _ _)
    set Q := (List.zipWith (fun c y ↦ C (algebraMap Kc (T.F m) c) * GPoly.toPoly M y) c N).sum
      with hQ
    have e2 : (List.zipWith (fun c y ↦ c * T.sigP m M y) (c.map (algebraMap Kc (T.F (m + 1))))
        N).sum = T.phi m Q := T.sum_sigP m M c N
    have hstep : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c *
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
    have hlenK : ∀ p ∈ N, p.length ≤ K := fun p hp ↦ le_foldr_max _ _ (List.mem_map_of_mem hp)
    set blocks := (List.range K).map fun k ↦
      colsOf ks m (N.map fun p ↦ p.getD k (opsM ks m).zero) with hblocks
    have hcols : colsOf ks (m + 1) vs = glueU vs.length (maxLen blocks) blocks := rfl
    rw [hcols, lcombS_glueU _ _ _ c blocks (fun B hB ↦ ⟨by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hB
      rw [length_colsOf, List.length_map, hNl], fun a ha ↦ le_maxLen blocks B hB a ha⟩)]
    rw [Polynomial.ext_iff]
    simp only [coeff_zero]
    constructor
    · intro h0 B hB
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hB
      have := h0 k
      rw [T.coeff_sum_toPoly m M k c N] at this
      exact (colsOf_spec m hm _ c (by rw [List.length_map, hNl]; exact hl)).mp this
    · intro h0 k
      rw [T.coeff_sum_toPoly m M k c N]
      by_cases hk : k < K
      · exact (colsOf_spec m hm _ c (by rw [List.length_map, hNl]; exact hl)).mpr
          (h0 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
      · refine T.sum_zero_codes m M c _ fun v hv ↦ ?_
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
        exact List.getD_eq_default _ _ (by have := hlenK p hp; omega)

lemma toPoly_unitL (j : ℕ) : toPoly (unitL j : CPoly ℚ) = X ^ j := by
  rw [unitL, toPoly_append]
  have : toPoly (List.replicate j (0 : ℚ)) = 0 := by
    induction j with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ih]
  simp [this]

lemma lcombS_range_unitL {S : Type*} [Field S] (ι : ℚ →+* S) :
    ∀ (c : List S), lcombS ι c ((List.range c.length).map unitL) = toPoly c := by
  classical
  intro c
  induction c using List.reverseRecOn with
  | nil => simp [lcombS]
  | append_singleton c x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
      List.map_singleton, lcombS_append ι _ _ _ _ (by simp), ih, toPoly_append, toPoly_unitL]
    simp

lemma coeff_lcombS {S : Type*} [Field S] (ι : ℚ →+* S) (j : ℕ) :
    ∀ (β : List S) (ws : List (CPoly ℚ)), (lcombS ι β ws).coeff j =
      (List.zipWith (fun b w ↦ b * ι (w.getD j 0)) β ws).sum
  | [], _ => by simp [lcombS]
  | _ :: _, [] => by simp [lcombS]
  | b :: β, w :: ws => by
    have ih := coeff_lcombS ι j β ws
    simp only [lcombS] at ih
    simp only [lcombS, List.zipWith_cons_cons, List.sum_cons, coeff_add, coeff_C_mul, coeff_map,
      coeff_toPoly, ih]

lemma lcombS_getD {S : Type*} [Field S] (ι : ℚ →+* S) : ∀ (cols : List (CPoly ℚ)) (w : CPoly ℚ),
    lcombS ι ((List.range cols.length).map fun j ↦ ι (w.getD j 0)) cols = lcombS ι (w.map ι) cols
  | [], w => by simp [lcombS]
  | a :: as, w => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    cases w with
    | nil =>
      rw [lcombS_of_zero ι _ _ (by simp)]
      simp [lcombS]
    | cons x w =>
      have ih := lcombS_getD ι as w
      have e : ((fun j ↦ ι ((x :: w).getD j 0)) ∘ Nat.succ) = fun j ↦ ι (w.getD j 0) := by
        funext j; simp
      rw [e]
      simp only [List.getD_cons_zero, List.map_cons, lcombS, List.zipWith_cons_cons,
        List.sum_cons] at ih ⊢
      rw [ih]

/-- **Soundness of the constant system**: every basis vector `w` of `consys` gives a relation
`∑ⱼ w[j] vⱼ = 0` in `F m`. -/
theorem consys_sound (m : ℕ) (h : T.Tr m) (vs : List (Code (m + 1))) (w : CPoly ℚ)
    (hw : w ∈ consys ks m vs) :
    (List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem v)
      ((List.range vs.length).map fun j ↦ algebraMap ℚ Kc (w.getD j 0)) vs).sum = 0 := by
  rw [T.colsOf_spec m h vs _ (by simp)]
  have h0 := nullBasis_sound (colsOf ks m vs) w hw
  rw [← length_colsOf ks m vs, lcombS_getD, lcombS_map_ns, h0, Polynomial.map_zero]

/-- **Completeness of the constant system**: every relation with constant coefficients is a
combination of the basis vectors, componentwise. -/
theorem consys_complete (m : ℕ) (h : T.Tr m) (vs : List (Code (m + 1))) (c : List Kc)
    (hl : c.length = vs.length)
    (h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem v) c vs).sum = 0) :
    ∃ β : List Kc, β.length = (consys ks m vs).length ∧ ∀ j,
      c.getD j 0 = (List.zipWith (fun b w ↦ b * algebraMap ℚ Kc (w.getD j 0)) β
        (consys ks m vs)).sum := by
  have hc := (T.colsOf_spec m h vs c hl).mp h0
  obtain ⟨β, hβ, heq⟩ := nullBasis_complete (algebraMap ℚ Kc) (colsOf ks m vs) c
    (by rw [length_colsOf]; exact hl) hc
  refine ⟨β, hβ, fun j ↦ ?_⟩
  have hsnd : (nsItems (colsOf ks m vs)).map Prod.snd =
      (List.range c.length).map unitL := by
    simp only [nsItems, List.map_map]
    rw [length_colsOf, ← hl]
    rfl
  rw [hsnd, lcombS_range_unitL] at heq
  have := congrArg (fun P : Kc[X] ↦ P.coeff j) heq
  simp only [coeff_toPoly] at this
  rw [this, coeff_lcombS]
  rfl

end NestMTower

end Tower.NestM
