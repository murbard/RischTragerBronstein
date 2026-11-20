import RischTragerBronstein.Computable.NestPTower

/-!
# Constant linear systems at any level: soundness and completeness

`colsOf_spec`: for constants `cⱼ ∈ Kc`, `∑ cⱼ vⱼ = 0` in `F m` iff the columns `colsOf ηs m vs`
over `ℚ` have `∑ cⱼ colⱼ = 0`. Hence (`consys_sound`, `consys_complete`) the basis `consys` of
the `ℚ`-relations spans all relations with constant coefficients.
-/

open Polynomial Differential CPoly

set_option linter.unusedSectionVars false

namespace Tower.NestP

open Tower.PrimN

/-! ### Cleared denominators -/

section Cross

variable {β : Type} {K : Type*} [Field K] (mul : β → β → β) (one : β) (σ : β → K)
  (hmul : ∀ a b, σ (mul a b) = σ a * σ b) (hone : σ one = 1)

include hmul hone in
lemma σ_prodD (l : List (β × β)) : σ (prodD mul one l) = (l.map fun p ↦ σ p.2).prod := by
  induction l with
  | nil => simp [prodD, hone]
  | cons p l ih =>
    simp only [prodD, List.foldr_cons, List.map_cons, List.prod_cons] at ih ⊢
    rw [hmul, ih]

lemma length_cross (l : List (β × β)) : (cross mul one l).length = l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => obtain ⟨n, d⟩ := p; simp [cross, ih]

include hmul hone in
/-- **Clearing denominators**: `∑ cⱼ σ(nⱼ ∏_{k≠j} dₖ) = (∑ cⱼ σ nⱼ / σ dⱼ) ∏ σ dₖ`. -/
lemma sum_cross : ∀ (l : List (β × β)) (c : List K), (∀ p ∈ l, σ p.2 ≠ 0) →
    (List.zipWith (fun c y ↦ c * σ y) c (cross mul one l)).sum =
      (List.zipWith (fun c p ↦ c * (σ p.1 / σ p.2)) c l).sum * σ (prodD mul one l)
  | [], c, _ => by simp [cross]
  | (n, d) :: rest, [], _ => by simp [cross]
  | (n, d) :: rest, c₀ :: cs, h => by
    have ih := sum_cross rest cs fun p hp ↦ h p (List.mem_cons_of_mem _ hp)
    have hd : σ d ≠ 0 := h (n, d) List.mem_cons_self
    have hmap : ∀ (cs : List K) (ys : List β),
        (List.zipWith (fun c y ↦ c * σ y) cs (ys.map fun y ↦ mul y d)).sum =
          (List.zipWith (fun c y ↦ c * σ y) cs ys).sum * σ d := by
      intro cs ys
      induction cs generalizing ys with
      | nil => simp
      | cons c cs ihc =>
        cases ys with
        | nil => simp
        | cons y ys =>
          simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, ihc, hmul]
          ring
    simp only [cross, List.zipWith_cons_cons, List.sum_cons]
    rw [hmap cs, ih]
    simp only [prodD, List.foldr_cons, hmul]
    simp only [prodD] at ih ⊢
    field_simp

include hmul hone in
lemma σ_prodD_ne_zero (l : List (β × β)) (h : ∀ p ∈ l, σ p.2 ≠ 0) : σ (prodD mul one l) ≠ 0 := by
  rw [σ_prodD mul one σ hmul hone]
  intro h0
  rw [List.prod_eq_zero_iff] at h0
  obtain ⟨p, hp, hp0⟩ := List.mem_map.mp h0
  exact h p hp hp0

end Cross

/-! ### Glued blocks -/

section Glue

variable {S : Type*} [Field S] (ι : ℚ →+* S)

lemma length_padL (L : ℕ) (p : CPoly ℚ) : (padL L p).length = L := by
  simp only [padL, List.length_append, List.length_take, List.length_replicate]
  omega

lemma toPoly_padL {L : ℕ} {p : CPoly ℚ} (h : p.length ≤ L) : toPoly (padL L p) = toPoly p := by
  rw [padL, List.take_of_length_le h, toPoly_append]
  have : toPoly (List.replicate (L - p.length) (0 : ℚ)) = 0 := by
    induction L - p.length with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ih]
  rw [this, mul_zero, add_zero]

lemma degree_toPoly_lt {p : CPoly ℚ} {L : ℕ} (h : p.length ≤ L) : (toPoly p).degree < L := by
  induction p generalizing L with
  | nil => simp
  | cons a p ih =>
    cases L with
    | zero => simp at h
    | succ L =>
      have := ih (L := L) (by simpa using h)
      rw [toPoly_cons]
      refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.succ_pos L)
      · rw [degree_mul, degree_X]
        rcases eq_or_ne (toPoly p) 0 with h0 | h0
        · simp [h0]
        · rw [degree_eq_natDegree h0] at this ⊢
          have h1 : (toPoly p).natDegree < L := by exact_mod_cast this
          have : ((1 : ℕ) : WithBot ℕ) + ((toPoly p).natDegree : WithBot ℕ) =
              ((1 + (toPoly p).natDegree : ℕ) : WithBot ℕ) := by push_cast; ring
          rw [show (1 : WithBot ℕ) = ((1 : ℕ) : WithBot ℕ) from rfl, this]
          exact_mod_cast (by omega : 1 + (toPoly p).natDegree < L + 1)

lemma degree_lcombS_lt {L : ℕ} : ∀ (c : List S) (B : List (CPoly ℚ)), (∀ a ∈ B, a.length ≤ L) →
    (lcombS ι c B).degree < L
  | [], B, _ => by simp [lcombS]
  | c :: cs, [], _ => by simp [lcombS]
  | c :: cs, a :: B, h => by
    have ih := degree_lcombS_lt cs B fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    simp only [lcombS, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ih)
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    rcases eq_or_ne c 0 with hc | hc
    · simp [hc, WithBot.bot_lt_coe]
    · rw [degree_C hc, zero_add, degree_map]
      exact degree_toPoly_lt (h a List.mem_cons_self)

lemma lcombS_zipWith_pad (L : ℕ) : ∀ (c : List S) (B R : List (CPoly ℚ)),
    (∀ a ∈ B, a.length ≤ L) → B.length = R.length →
    lcombS ι c (List.zipWith (fun a r ↦ padL L a ++ r) B R) =
      lcombS ι c B + X ^ L * lcombS ι c R
  | [], B, R, _, _ => by simp [lcombS]
  | c :: cs, [], [], _, _ => by simp [lcombS]
  | c :: cs, a :: B, r :: R, h, hl => by
    have ih := lcombS_zipWith_pad L cs B R (fun b hb ↦ h b (List.mem_cons_of_mem _ hb))
      (by simpa using hl)
    simp only [List.zipWith_cons_cons, lcombS, List.sum_cons] at ih ⊢
    rw [ih, toPoly_append, length_padL, toPoly_padL (h a List.mem_cons_self), Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_pow, map_X]
    ring
  | c :: cs, [], _ :: _, _, hl => by simp at hl
  | c :: cs, _ :: _, [], _, hl => by simp at hl

lemma length_glueU (n L : ℕ) : ∀ blocks : List (List (CPoly ℚ)), (∀ B ∈ blocks, B.length = n) →
    (glueU n L blocks).length = n
  | [], _ => by simp [glueU]
  | B :: Bs, h => by
    simp only [glueU, List.length_zipWith, h B List.mem_cons_self,
      length_glueU n L Bs fun B' hB' ↦ h B' (List.mem_cons_of_mem _ hB'), min_self]

lemma lcombS_replicate_nil (c : List S) (n : ℕ) : lcombS ι c (List.replicate n []) = 0 := by
  induction c generalizing n with
  | nil => simp [lcombS]
  | cons c cs ih =>
    cases n with
    | zero => simp [lcombS]
    | succ n =>
      have := ih n
      simp only [List.replicate_succ, lcombS, List.zipWith_cons_cons, List.sum_cons] at this ⊢
      rw [this]; simp

/-- **Glued blocks vanish iff each block does.** -/
lemma lcombS_glueU (n L : ℕ) (c : List S) : ∀ blocks : List (List (CPoly ℚ)),
    (∀ B ∈ blocks, B.length = n ∧ ∀ a ∈ B, a.length ≤ L) →
    (lcombS ι c (glueU n L blocks) = 0 ↔ ∀ B ∈ blocks, lcombS ι c B = 0)
  | [], _ => by simp [glueU, lcombS_replicate_nil]
  | B :: Bs, h => by
    have ih := lcombS_glueU n L c Bs fun B' hB' ↦ h B' (List.mem_cons_of_mem _ hB')
    obtain ⟨hBn, hBL⟩ := h B List.mem_cons_self
    have hlen : B.length = (glueU n L Bs).length := by
      rw [hBn, length_glueU n L Bs fun B' hB' ↦ (h B' (List.mem_cons_of_mem _ hB')).1]
    simp only [glueU]
    rw [lcombS_zipWith_pad ι L c B _ hBL hlen, List.forall_mem_cons, ← ih]
    have hdeg := degree_lcombS_lt ι c B hBL
    constructor
    · intro h0
      have hP : lcombS ι c B = 0 := by
        by_contra hne
        have hco := congrArg (fun P : S[X] ↦ P.coeff (lcombS ι c B).natDegree) h0
        simp only [coeff_add, coeff_X_pow_mul', coeff_zero] at hco
        have hlt : (lcombS ι c B).natDegree < L := by
          rw [degree_eq_natDegree hne] at hdeg; exact_mod_cast hdeg
        rw [if_neg (by omega), add_zero] at hco
        exact hne (leadingCoeff_eq_zero.mp hco)
      refine ⟨hP, ?_⟩
      rw [hP, zero_add] at h0
      exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ X_ne_zero)
    · rintro ⟨h1, h2⟩
      rw [h1, h2, mul_zero, add_zero]

end Glue

section Coeff

variable {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma coeff_toPoly_getD' (p : GPoly α) (k : ℕ) :
    (GPoly.toPoly M p).coeff k = M.sem (p.getD k O.zero) := by
  rw [GPoly.coeff_toPoly]
  by_cases hk : k < p.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getD_eq_getElem _ _ hk]
  · rw [List.getD_eq_default _ _ (by simpa using hk), List.getD_eq_default _ _ (by omega),
      M.sem_zero]

end Coeff

lemma le_foldr_max (l : List ℕ) : ∀ a ∈ l, a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih a ha).trans (le_max_right _ _)

lemma le_maxLen (blocks : List (List (CPoly ℚ))) : ∀ B ∈ blocks, ∀ a ∈ B, a.length ≤ maxLen blocks := by
  intro B hB a ha
  exact (le_foldr_max _ _ (List.mem_map_of_mem ha)).trans
    (le_foldr_max _ _ (List.mem_map.mpr ⟨B, hB, rfl⟩))

lemma length_colsOf (ηs : (m : ℕ) → Code (m + 1)) :
    ∀ (m : ℕ) (vs : List (Code (m + 1))), (colsOf ηs m vs).length = vs.length
  | 0, vs => by
    simp only [colsOf, length_cross]
    exact List.length_map _
  | m + 1, vs => by
    simp only [colsOf]
    rw [length_glueU]
    intro B hB
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hB
    rw [length_colsOf ηs m, List.length_map, length_cross]
    exact List.length_map _

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ηs : (m : ℕ) → Code (m + 1)}

namespace NestTower

variable (T : NestTower Kc E ηs)

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
noncomputable def sigP (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsQ ηs m))
    (p : GPoly (Code (m + 1))) : T.F (m + 1) := T.phi m (GPoly.toPoly M p)

/-- Zero-denominator cleaning at level `0`. -/
def clean0 (v : GFrac ℚ) : GFrac ℚ :=
  if CPoly.isZero v.2 then (([] : CPoly ℚ), ([1] : CPoly ℚ)) else v

/-- Zero-denominator cleaning at level `m + 1`. -/
def cleanS (m : ℕ) (v : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) :
    GPoly (Code (m + 1)) × GPoly (Code (m + 1)) :=
  if GPoly.isZero (opsQ ηs m) v.2 then (([] : GPoly (Code (m + 1))), [(opsQ ηs m).one]) else v

lemma colsOf_zero (vs : List (Code 1)) :
    colsOf ηs 0 vs = cross CPoly.mul [1] (vs.map clean0) := rfl

lemma psiP_mul (a b : CPoly ℚ) : T.psiP (CPoly.mul a b) = T.psiP a * T.psiP b := by
  simp only [psiP, toPoly_mul, Polynomial.map_mul, map_mul]

lemma psiP_one : T.psiP [1] = 1 := by simp [psiP, CPoly.toPoly]

lemma sigP_mul (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsQ ηs m)) (a b) :
    T.sigP m M (GPoly.mul (opsQ ηs m) a b) = T.sigP m M a * T.sigP m M b := by
  simp only [sigP, GPoly.toPoly_mul, map_mul]

lemma sigP_one (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsQ ηs m)) :
    T.sigP m M [(opsQ ηs m).one] = 1 := by
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

lemma sum_sigP (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsQ ηs m)) :
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

lemma coeff_sum_toPoly (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsQ ηs m)) (k : ℕ) :
    ∀ (c : List Kc) (N : List (GPoly (Code (m + 1)))),
      (List.zipWith (fun c y ↦ C (algebraMap Kc (T.F m) c) * GPoly.toPoly M y) c N).sum.coeff k =
        (List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * M.sem v) c
          (N.map fun p ↦ p.getD k (opsQ ηs m).zero)).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, y :: N => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, coeff_add, coeff_C_mul,
      coeff_toPoly_getD']
    rw [coeff_sum_toPoly m M k cs N]

lemma sum_zero_codes (m : ℕ) (M : CField (Code (m + 1)) (T.F m) (opsQ ηs m)) :
    ∀ (c : List Kc) (vs : List (Code (m + 1))), (∀ v ∈ vs, v = (opsQ ηs m).zero) →
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
    (T.MP (m + 1) h).sem v = T.sigP m (T.MP m fun i hi ↦ h i (by omega)) (cleanS (ηs := ηs) m v).1 /
      T.sigP m (T.MP m fun i hi ↦ h i (by omega)) (cleanS (ηs := ηs) m v).2 := by
  refine (T.sem_MP_succ m h v).trans ?_
  unfold cleanS
  split_ifs with hz
  · rw [(GPoly.isZero_iff (T.MP m fun i hi ↦ h i (by omega)) _).mp hz]
    simp [sigP]
  · rfl

/-- **The constant system at level `m`**: for constants `c`, `∑ cⱼ vⱼ = 0` in `F m` iff the
`ℚ`-columns `colsOf ηs m vs` combine to `0`. -/
theorem colsOf_spec : ∀ (m : ℕ) (h : T.Tr m) (vs : List (Code (m + 1))) (c : List Kc),
    c.length = vs.length →
    ((List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem v) c vs).sum = 0 ↔
      lcombS (algebraMap ℚ Kc) c (colsOf ηs m vs) = 0)
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
        (cleanS (ηs := ηs) m)), T.sigP m M v.2 ≠ 0 := by
      intro v hv
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
      unfold cleanS
      split_ifs with hz
      · rw [T.sigP_one]; exact one_ne_zero
      · exact (map_ne_zero_iff _ hinj).mpr fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
    have hP := σ_prodD_ne_zero (GPoly.mul (opsQ ηs m)) [(opsQ ηs m).one] (T.sigP m M)
      (T.sigP_mul m M) (T.sigP_one m M) _ hden
    set N := cross (GPoly.mul (opsQ ηs m)) [(opsQ ηs m).one]
      ((vs : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))).map (cleanS (ηs := ηs) m))
      with hN
    have key := sum_cross (GPoly.mul (opsQ ηs m)) [(opsQ ηs m).one] (T.sigP m M) (T.sigP_mul m M)
      (T.sigP_one m M) ((vs : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))).map
        (cleanS (ηs := ηs) m)) (c.map (algebraMap Kc (T.F (m + 1)))) hden
    have e1 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c * (T.MP (m + 1) h).sem v)
        c vs).sum = (List.zipWith (fun c p ↦ c * (T.sigP m M p.1 / T.sigP m M p.2))
          (c.map (algebraMap Kc (T.F (m + 1))))
          ((vs : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))).map
            (cleanS (ηs := ηs) m))).sum :=
      (zipWith_map_left (algebraMap Kc (T.F (m + 1))) ((T.MP (m + 1) h).sem) c vs).trans
        (zipWith_comp_map _ _ (cleanS (ηs := ηs) m) (T.semS_clean m h) _ _)
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
      colsOf ηs m (N.map fun p ↦ p.getD k (opsQ ηs m).zero) with hblocks
    have hcols : colsOf ηs (m + 1) vs = glueU vs.length (maxLen blocks) blocks := rfl
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
    (hw : w ∈ consys ηs m vs) :
    (List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem v)
      ((List.range vs.length).map fun j ↦ algebraMap ℚ Kc (w.getD j 0)) vs).sum = 0 := by
  rw [T.colsOf_spec m h vs _ (by simp)]
  have h0 := nullBasis_sound (colsOf ηs m vs) w hw
  rw [← length_colsOf ηs m vs, lcombS_getD, lcombS_map_ns, h0, Polynomial.map_zero]

/-- **Completeness of the constant system**: every relation with constant coefficients is a
combination of the basis vectors, componentwise. -/
theorem consys_complete (m : ℕ) (h : T.Tr m) (vs : List (Code (m + 1))) (c : List Kc)
    (hl : c.length = vs.length)
    (h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem v) c vs).sum = 0) :
    ∃ β : List Kc, β.length = (consys ηs m vs).length ∧ ∀ j,
      c.getD j 0 = (List.zipWith (fun b w ↦ b * algebraMap ℚ Kc (w.getD j 0)) β
        (consys ηs m vs)).sum := by
  have hc := (T.colsOf_spec m h vs c hl).mp h0
  obtain ⟨β, hβ, heq⟩ := nullBasis_complete (algebraMap ℚ Kc) (colsOf ηs m vs) c
    (by rw [length_colsOf]; exact hl) hc
  refine ⟨β, hβ, fun j ↦ ?_⟩
  have hsnd : (nsItems (colsOf ηs m vs)).map Prod.snd =
      (List.range c.length).map unitL := by
    simp only [nsItems, List.map_map]
    rw [length_colsOf, ← hl]
    rfl
  rw [hsnd, lcombS_range_unitL] at heq
  have := congrArg (fun P : Kc[X] ↦ P.coeff j) heq
  simp only [coeff_toPoly] at this
  rw [this, coeff_lcombS]
  rfl

end NestTower

end Tower.NestP
