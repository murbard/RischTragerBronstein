import RischTragerBronstein.Computable.NestPPoly

/-!
# Parametric limited integration in towers with nested primitives: the inductive step

At level `m + 1` (`t = tₘ`, `t′ = ηₘ ∈ F m`): every weight is Hermite-reduced,
`wᵢ = gᵢ′ + Pᵢ + rᵢ / sᵢ`; a solution `z′ = ∑ cᵢ wᵢ` forces `∑ cᵢ rᵢ / sᵢ = 0`
(`proper_step_sum`: sums of proper fractions are not derivatives) — a constant system at level
`m + 1` — and `z - ∑ cᵢ gᵢ` is a polynomial `Q` with `Q′ = ∑ cᵢ Pᵢ` — the parametric polynomial
problem, whose one-level-down solver is `paramLim` at level `m`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestP

open Tower.PrimN

namespace NestTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ηs : (m : ℕ) → Code (m + 1)}
variable (T : NestTower Kc E ηs)

/-- **Sums of proper fractions are not derivatives**, at level `m + 1`. -/
lemma proper_step_sum (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (A : (T.F m)[X])
    (l : List ((T.F m)[X] × (T.F m)[X])) (hsq : ∀ p ∈ l, Squarefree p.2)
    (hdeg : ∀ p ∈ l, p.1.degree < p.2.degree) (z : E) (hz : z ∈ T.F (m + 1))
    (h : z′ = aeval (T.ts m) A + (l.map fun p ↦ aeval (T.ts m) p.1 / aeval (T.ts m) p.2).sum) :
    (l.map fun p ↦ aeval (T.ts m) p.1 / aeval (T.ts m) p.2).sum = 0 ∧
      ∃ P : (T.F m)[X], z = aeval (T.ts m) P ∧ implicitDeriv (T.wPoly m) P = A := by
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) (T.ts m)
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮T.ts m⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple (T.ts m) _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮T.ts m⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮T.ts m⟯ :=
    differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ P : (T.F m)⟮T.ts m⟯) : E) =
      aeval (T.ts m) P := algebraMap_adjoinSimple _
  have hsum : ∀ l' : List ((T.F m)[X] × (T.F m)[X]),
      (((l'.map fun p ↦ algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ p.1 /
        algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ p.2).sum : (T.F m)⟮T.ts m⟯) : E) =
      (l'.map fun p ↦ aeval (T.ts m) p.1 / aeval (T.ts m) p.2).sum := by
    intro l'
    induction l' with
    | nil => simp
    | cons p l' ih =>
      simp only [List.map_cons, List.sum_cons, IntermediateField.coe_add,
        IntermediateField.coe_div, hcoe, ih]
  obtain ⟨hb, P, hP, hPd⟩ := deriv_eq_poly_add_sum_proper (K := (T.F m)⟮T.ts m⟯)
    (fun p hp ↦ T.normal m htr p hp) A l hsq hdeg ⟨z, (T.mem_F_succ).mp hz⟩
    (Subtype.ext (by
      change z′ = _
      rw [h, IntermediateField.coe_add, hcoe, hsum]))
  refine ⟨?_, P, ?_, hPd⟩
  · have := congrArg Subtype.val hb
    rw [hsum] at this
    exact this
  · have := congrArg Subtype.val hP
    rw [hcoe] at this
    exact this

/-- The Hermite data of a (cleaned) weight at level `m + 1`. -/
def hermW (m : ℕ) (w : Code (m + 2)) : GPoly.HermiteResult (Code (m + 1)) :=
  let w' := if GPoly.isZero (opsQ ηs m) w.2 then (([] : GPoly (Code (m + 1))), [(opsQ ηs m).one])
    else w
  GPoly.hermite (opsQ ηs m) [ηs m] w'.1 w'.2

/-- **The decomposition of a weight** `w = g′ + P + r / s` at level `m + 1`. -/
lemma weight_decomp (m : ℕ) (h : T.Tr (m + 1)) (w : Code (m + 2)) :
    (T.MP (m + 1) h).sem w =
      ((T.MP (m + 1) h).sem (((hermW (ηs := ηs) m w).gn, (hermW (ηs := ηs) m w).gd) :
        Code (m + 2)))′ +
        T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega))
          (GPoly.divMod (opsQ ηs m) (hermW (ηs := ηs) m w).b (hermW (ηs := ηs) m w).s).1) +
        T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega))
          (GPoly.divMod (opsQ ηs m) (hermW (ηs := ηs) m w).b (hermW (ηs := ηs) m w).s).2) /
        T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) (hermW (ηs := ηs) m w).s) ∧
    Squarefree (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) (hermW (ηs := ηs) m w).s) ∧
    (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega))
      (GPoly.divMod (opsQ ηs m) (hermW (ηs := ηs) m w).b (hermW (ηs := ηs) m w).s).2).degree <
      (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) (hermW (ηs := ηs) m w).s).degree := by
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injective htr
  obtain ⟨w', hw'⟩ : ∃ w' : GPoly (Code (m + 1)) × GPoly (Code (m + 1)), w' =
      if GPoly.isZero (opsQ ηs m) w.2 then (([] : GPoly (Code (m + 1))), [(opsQ ηs m).one])
        else w := ⟨_, rfl⟩
  have hsemw : (T.MP (m + 1) h).sem w = T.phi m (GPoly.toPoly M w'.1) /
      T.phi m (GPoly.toPoly M w'.2) := by
    rw [T.sem_MP_succ]
    by_cases hz : GPoly.isZero (opsQ ηs m) w.2 = true
    · simp only [hz, ↓reduceIte] at hw'
      rw [hw', (GPoly.isZero_iff (T.MP m fun i hi ↦ h i (by omega)) _).mp hz]
      simp
    · simp only [hz, ↓reduceIte, Bool.false_eq_true] at hw'
      rw [hw']
  have hD : GPoly.toPoly M w'.2 ≠ 0 := by
    by_cases hz : GPoly.isZero (opsQ ηs m) w.2 = true
    · simp only [hz, ↓reduceIte] at hw'
      rw [hw']
      simp [M.sem_one]
    · simp only [hz, ↓reduceIte, Bool.false_eq_true] at hw'
      rw [hw']
      exact fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr w'.1 w'.2 hD
  rw [← hM] at hval hsq
  have hherm : hermW (ηs := ηs) m w = GPoly.hermite (opsQ ηs m) [ηs m] w'.1 w'.2 := by
    rw [hw']; rfl
  rw [hherm]
  refine ⟨?_, hsq, GPoly.divMod_degree_lt M _ _ hsq.ne_zero⟩
  have hdm := GPoly.divMod_spec M (GPoly.hermite (opsQ ηs m) [ηs m] w'.1 w'.2).b
    (GPoly.hermite (opsQ ηs m) [ηs m] w'.1 w'.2).s
  have hs0 : T.phi m (GPoly.toPoly M (GPoly.hermite (opsQ ηs m) [ηs m] w'.1 w'.2).s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
  have hg : (T.MP (m + 1) h).sem (((GPoly.hermite (opsQ ηs m) [ηs m] w'.1 w'.2).gn,
      (GPoly.hermite (opsQ ηs m) [ηs m] w'.1 w'.2).gd) : Code (m + 2)) =
      T.phi m (GPoly.toPoly M (GPoly.hermite (opsQ ηs m) [ηs m] w'.1 w'.2).gn) /
        T.phi m (GPoly.toPoly M (GPoly.hermite (opsQ ηs m) [ηs m] w'.1 w'.2).gd) := rfl
  rw [hsemw, hval, hg, hdm, map_add, map_mul]
  field_simp
  ring

/-- The simple parts of the weights, as codes of level `m + 1`. -/
def simpleCodes (m : ℕ) (W : List (Code (m + 2))) : List (Code (m + 2)) :=
  (List.zip ((W.map (hermW (ηs := ηs) m)).map fun h ↦ GPoly.divMod (opsQ ηs m) h.b h.s)
    (W.map (hermW (ηs := ηs) m))).map fun p ↦ ((p.1.2, p.2.s) : Code (m + 2))

lemma paramLim_succ_eq (m : ℕ) (W : List (Code (m + 2))) :
    paramLim ηs (m + 1) W =
      let O := opsQ ηs m
      let O' := opsQ ηs (m + 1)
      let n := W.length
      let H := W.map (hermW (ηs := ηs) m)
      let QR := H.map fun h ↦ GPoly.divMod O h.b h.s
      let U := consys ηs (m + 1) (simpleCodes (ηs := ηs) m W)
      let E := U.map (vecOf n)
      let Pu := E.map fun e ↦ lcombGP O (cstN m) e (QR.map Prod.fst)
      let Gu := E.map fun e ↦ lcombCode O' (cstN (m + 1)) e
        (H.map fun h ↦ ((h.gn, h.gd) : Code (m + 2)))
      (paramPoly O (cstN m) (ηs m) (paramLim ηs m) Pu).map fun r ↦
        (vcomb n r.1 E, O'.add (lcombCode O' (cstN (m + 1)) r.1 Gu) ((r.2, [O.one]) : Code (m + 2))) :=
  rfl

lemma len_zip_map {β γ δ ε : Type*} (g : β → δ) (f : δ → γ) (k : γ × δ → ε) (l : List β) :
    ((List.zip ((l.map g).map f) (l.map g)).map k).length = l.length := by simp

lemma getD_zip_map {β γ δ ε : Type*} (g : β → δ) (f : δ → γ) (k : γ × δ → ε) (l : List β)
    (d : β) (d' : ε) {i : ℕ} (hi : i < l.length) :
    ((List.zip ((l.map g).map f) (l.map g)).map k).getD i d' =
      k (f (g (l.getD i d)), g (l.getD i d)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

lemma length_simpleCodes (m : ℕ) (W : List (Code (m + 2))) :
    (simpleCodes (ηs := ηs) m W).length = W.length :=
  len_zip_map (hermW (ηs := ηs) m) (fun h ↦ GPoly.divMod (opsQ ηs m) h.b h.s)
    (fun p ↦ ((p.1.2, p.2.s) : Code (m + 2))) W

lemma getD_simpleCodes (m : ℕ) (W : List (Code (m + 2))) {i : ℕ} (hi : i < W.length) :
    (simpleCodes (ηs := ηs) m W).getD i (zc ηs (m + 1)) =
      (((GPoly.divMod (opsQ ηs m) (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).b
        (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).s).2,
        (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).s) : Code (m + 2)) :=
  getD_zip_map (hermW (ηs := ηs) m) (fun h ↦ GPoly.divMod (opsQ ηs m) h.b h.s)
    (fun p ↦ ((p.1.2, p.2.s) : Code (m + 2))) W (zc ηs (m + 1)) (zc ηs (m + 1)) hi

lemma len_map_map {β δ γ : Type*} (g : β → δ) (f : δ → γ) (l : List β) :
    ((l.map g).map f).length = l.length := by simp

lemma getD_map_map {β δ γ : Type*} (g : β → δ) (f : δ → γ) (l : List β) (d : β) (d' : γ)
    {i : ℕ} (hi : i < l.length) : ((l.map g).map f).getD i d' = f (g (l.getD i d)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

/-- The Hermite part `gᵢ` of a weight, as a code. -/
def gCode (m : ℕ) (w : Code (m + 2)) : Code (m + 2) :=
  (((hermW (ηs := ηs) m w).gn, (hermW (ηs := ηs) m w).gd) : Code (m + 2))

/-- The polynomial part `Pᵢ` of a weight. -/
def pPart (m : ℕ) (w : Code (m + 2)) : GPoly (Code (m + 1)) :=
  (GPoly.divMod (opsQ ηs m) (hermW (ηs := ηs) m w).b (hermW (ηs := ηs) m w).s).1

lemma sem_Gu (m : ℕ) (h : T.Tr (m + 1)) (W : List (Code (m + 2))) (e : List ℚ) :
    (T.MP (m + 1) h).sem (lcombCode (opsQ ηs (m + 1)) (cstN (m + 1)) e
      ((W.map (hermW (ηs := ηs) m)).map fun h ↦ ((h.gn, h.gd) : Code (m + 2)))) =
      ∑ i ∈ Finset.range W.length, ((e.getD i 0 : ℚ) : T.F (m + 1)) *
        (T.MP (m + 1) h).sem (gCode (ηs := ηs) m (W.getD i (zc ηs (m + 1)))) := by
  rw [sem_lcombCode (T.MP (m + 1) h) (cstN (m + 1)) (T.sem_cstN (m + 1) h),
    zipWith_sum_getD (fun (q : ℚ) (a : Code (m + 2)) ↦ ((q : ℚ) : T.F (m + 1)) *
      (T.MP (m + 1) h).sem a) 0 (zc ηs (m + 1)) (by simp)]
  refine Finset.sum_congr (congrArg Finset.range (len_map_map _ _ W)) fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  congr 2
  exact getD_map_map (hermW (ηs := ηs) m) (fun h ↦ ((h.gn, h.gd) : Code (m + 2))) W
    (zc ηs (m + 1)) (zc ηs (m + 1)) hi'

lemma toPoly_Pu (m : ℕ) (hm : T.Tr m) (W : List (Code (m + 2))) (e : List ℚ) :
    GPoly.toPoly (T.MP m hm) (lcombGP (opsQ ηs m) (cstN m) e
      (((W.map (hermW (ηs := ηs) m)).map fun h ↦ GPoly.divMod (opsQ ηs m) h.b h.s).map Prod.fst)) =
      ∑ i ∈ Finset.range W.length, C ((e.getD i 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MP m hm) (pPart (ηs := ηs) m (W.getD i (zc ηs (m + 1)))) := by
  rw [toPoly_lcombGP (T.MP m hm) (cstN m) (T.sem_cstN m hm),
    zipWith_sum_getD (fun (q : ℚ) (p : GPoly (Code (m + 1))) ↦ C ((q : ℚ) : T.F m) *
      GPoly.toPoly (T.MP m hm) p) 0 [] (by simp)]
  refine Finset.sum_congr (by simp) fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  congr 2
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getD_eq_getElem _ _ hi']
  simp [pPart, List.getD_eq_getElem _ _ hi']

lemma sem_final (m : ℕ) (h : T.Tr (m + 1)) (a : Code (m + 2)) (Q : GPoly (Code (m + 1))) :
    (T.MP (m + 1) h).sem ((opsQ ηs (m + 1)).add a ((Q, [(opsQ ηs m).one]) : Code (m + 2))) =
      (T.MP (m + 1) h).sem a + T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) Q) := by
  refine ((T.MP (m + 1) h).sem_add a _).trans ?_
  congr 1
  refine (T.sem_MP_succ m h _).trans ?_
  simp [(T.MP m fun i hi ↦ h i (by omega)).sem_one]

lemma wPoly_eq (m : ℕ) (hm : T.Tr m) : T.wPoly m = C ((T.MP m hm).sem (ηs m)) := by
  rw [wPoly, T.sem_MP_F]

lemma phi_C_ratCast (m : ℕ) (q : ℚ) : T.phi m (C ((q : ℚ) : T.F m)) = ((q : ℚ) : T.F (m + 1)) := by
  rw [T.phi_C]
  exact map_ratCast _ q

/-- The relation given by a basis vector of the constant system on the simple parts. -/
lemma rel_simple (m : ℕ) (h : T.Tr (m + 1)) (W : List (Code (m + 2))) (u : CPoly ℚ)
    (hu : u ∈ consys ηs (m + 1) (simpleCodes (ηs := ηs) m W)) :
    ∑ i ∈ Finset.range W.length, ((u.getD i 0 : ℚ) : T.F (m + 1)) *
      (T.MP (m + 1) h).sem ((simpleCodes (ηs := ηs) m W).getD i (zc ηs (m + 1))) = 0 := by
  have := T.consys_sound (m + 1) h (simpleCodes (ηs := ηs) m W) u hu
  rw [zipWith_sum_range _ 0 (zc ηs (m + 1)) _ _ (by simp)] at this
  rw [← this]
  refine Finset.sum_congr (by simp [length_simpleCodes]) fun i hi ↦ ?_
  have hi' : i < W.length := by simpa [length_simpleCodes] using hi
  rw [getD_range_map (fun j ↦ algebraMap ℚ Kc (u.getD j 0)) 0
    (by rw [length_simpleCodes]; exact hi'), T.algebraMap_ratCast]

/-- The value of a simple part. -/
lemma sem_simple (m : ℕ) (h : T.Tr (m + 1)) (W : List (Code (m + 2))) {i : ℕ} (hi : i < W.length) :
    (T.MP (m + 1) h).sem ((simpleCodes (ηs := ηs) m W).getD i (zc ηs (m + 1))) =
      T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega))
        (GPoly.divMod (opsQ ηs m) (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).b
          (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).s).2) /
      T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega))
        (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).s) := by
  rw [getD_simpleCodes m W hi]
  rfl

/-- The one-level-down solver meets the specification. -/
lemma limSpec_of (m : ℕ) (hm : T.Tr m)
    (IH : ∀ W', T.PLSound m hm W' (paramLim ηs m W') ∧ T.PLComplete m hm W' (paramLim ηs m W')) :
    LimSpec (algebraMap Kc (T.F m)) (T.MP m hm) (paramLim ηs m) :=
  ⟨fun ws r hr ↦ (IH ws).1 r hr, fun ws c hc z hz ↦ (IH ws).2 c hc z hz⟩

/-- **Soundness of the inductive step.** -/
theorem paramLim_succ_sound (m : ℕ) (h : T.Tr (m + 1))
    (IH : ∀ W', T.PLSound m (fun i hi ↦ h i (by omega)) W' (paramLim ηs m W') ∧
      T.PLComplete m (fun i hi ↦ h i (by omega)) W' (paramLim ηs m W'))
    (W : List (Code (m + 2))) : T.PLSound (m + 1) h W (paramLim ηs (m + 1) W) := by
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  have hspec := T.limSpec_of m hm IH
  have hconstK : ∀ y : T.F m, y′ = 0 → ∃ κ : Kc, y = algebraMap Kc (T.F m) κ := fun y hy ↦
    T.const_F y hy
  intro r' hr'
  rw [paramLim_succ_eq] at hr'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  set U := consys ηs (m + 1) (simpleCodes (ηs := ηs) m W) with hU
  set E := U.map (vecOf W.length) with hE
  have hsound := paramPoly_sound (algebraMap Kc (T.F m)) (ηs m) (paramLim ηs m)
    (T.sem_cstN m hm) hspec hconstK (fun q ↦ T.algebraMap_ratCast q) _ r hr
  simp only
  rw [T.sem_final m h, map_add,
    sem_lcombCode (T.MP (m + 1) h) (cstN (m + 1)) (T.sem_cstN (m + 1) h),
    zipWith_sum_getD (fun (q : ℚ) (a : Code (m + 2)) ↦ ((q : ℚ) : T.F (m + 1)) *
      (T.MP (m + 1) h).sem a) 0 (zc ηs (m + 1)) (by simp),
    T.deriv_sum_ratCast, T.deriv_phi, ← hM, T.wPoly_eq m hm, ← hM]
  change _ + T.phi m (Dη M (ηs m) _) = _
  rw [hsound, polySumQ, map_sum]
  have hlG : (E.map fun e ↦ lcombCode (opsQ ηs (m + 1)) (cstN (m + 1)) e
      ((W.map (hermW (ηs := ηs) m)).map fun h ↦ ((h.gn, h.gd) : Code (m + 2)))).length = U.length := by
    simp [hE]
  have hlP : (E.map fun e ↦ lcombGP (opsQ ηs m) (cstN m) e
      (((W.map (hermW (ηs := ηs) m)).map fun h ↦ GPoly.divMod (opsQ ηs m) h.b h.s).map
        Prod.fst)).length = U.length := by simp [hE]
  -- regroup by basis vector
  have hterm : ∀ u < U.length,
      ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * ((T.MP (m + 1) h).sem
        ((E.map fun e ↦ lcombCode (opsQ ηs (m + 1)) (cstN (m + 1)) e
          ((W.map (hermW (ηs := ηs) m)).map fun h ↦ ((h.gn, h.gd) : Code (m + 2)))).getD u
            (zc ηs (m + 1))))′ +
      T.phi m (C ((r.1.getD u 0 : ℚ) : T.F m) * GPoly.toPoly M
        ((E.map fun e ↦ lcombGP (opsQ ηs m) (cstN m) e
          (((W.map (hermW (ηs := ηs) m)).map fun h ↦ GPoly.divMod (opsQ ηs m) h.b h.s).map
            Prod.fst)).getD u [])) =
      ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * ∑ i ∈ Finset.range W.length,
        (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) *
          (T.MP (m + 1) h).sem (W.getD i (zc ηs (m + 1))) := by
    intro u hu
    have huE : u < E.length := by simpa [hE] using hu
    rw [getD_map' _ E [] (zc ηs (m + 1)) huE, getD_map' _ E [] [] huE, T.sem_Gu m h W,
      T.toPoly_Pu m hm W, T.deriv_sum_ratCast, Finset.mul_sum, map_mul, map_sum,
      T.phi_C_ratCast, Finset.mul_sum, ← Finset.sum_add_distrib]
    have hrel := T.rel_simple m h W (U.getD u []) (by
      rw [List.getD_eq_getElem _ _ hu]; exact List.getElem_mem _)
    have e : ∀ i ∈ Finset.range W.length,
        ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * ((((E.getD u []).getD i 0 : ℚ) : T.F (m + 1)) *
          ((T.MP (m + 1) h).sem (gCode (ηs := ηs) m (W.getD i (zc ηs (m + 1)))))′) +
        ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * T.phi m (C (((E.getD u []).getD i 0 : ℚ) : T.F m) *
          GPoly.toPoly (T.MP m hm) (pPart (ηs := ηs) m (W.getD i (zc ηs (m + 1))))) =
        ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * ((((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) *
          (T.MP (m + 1) h).sem (W.getD i (zc ηs (m + 1)))) -
        ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * ((((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) *
          (T.MP (m + 1) h).sem ((simpleCodes (ηs := ηs) m W).getD i (zc ηs (m + 1)))) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [hE, getD_map' _ U [] [] hu, getD_vecOf, if_pos hi', map_mul, T.phi_C_ratCast,
        (T.weight_decomp m h (W.getD i (zc ηs (m + 1)))).1, T.sem_simple m h W hi']
      simp only [gCode, pPart]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrel,
      mul_zero, sub_zero]
  rw [Finset.sum_congr (congrArg Finset.range hlG) fun u hu ↦ rfl,
    Finset.sum_congr (congrArg Finset.range hlP) fun u hu ↦ rfl, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun u hu ↦ hterm u (Finset.mem_range.mp hu), sumQ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [getD_vcomb, if_pos (Finset.mem_range.mp hi), List.length_map]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [hE, getD_map' _ U [] [] (Finset.mem_range.mp hu), getD_vecOf,
    if_pos (Finset.mem_range.mp hi)]
  ring

lemma coe_algebraMap_F (m : ℕ) (κ : Kc) :
    ((algebraMap Kc (T.F m) κ : T.F m) : E) = algebraMap Kc E κ := rfl

lemma coe_phi_sum (m : ℕ) (n : ℕ) (a : ℕ → Kc) (p : ℕ → (T.F m)[X]) :
    ((∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (a i) * T.phi m (p i) : T.F (m + 1)) : E) =
      aeval (T.ts m) (∑ i ∈ Finset.range n, C (algebraMap Kc (T.F m) (a i)) * p i) := by
  rw [map_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, aeval_C, coe_phi]
  rfl

lemma coe_phi_div_sum (m : ℕ) (n : ℕ) (a : ℕ → Kc) (p q : ℕ → (T.F m)[X]) :
    ((∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (a i) *
      (T.phi m (p i) / T.phi m (q i)) : T.F (m + 1)) : E) =
      (((List.range n).map fun i ↦ (C (algebraMap Kc (T.F m) (a i)) * p i, q i)).map
        fun r ↦ aeval (T.ts m) r.1 / aeval (T.ts m) r.2).sum := by
  rw [List.map_map, list_sum_map_range]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Function.comp_apply, coe_phi, map_mul, aeval_C]
  rw [show algebraMap (T.F m) E (algebraMap Kc (T.F m) (a i)) = algebraMap Kc E (a i) from rfl]
  ring

/-- Reassembling the double change of basis. -/
lemma reassemble {K : Type*} [Field K] [CharZero K] (alg : Kc →+* K) (n NU NK : ℕ)
    (Uv δ : ℕ → ℕ → ℚ) (c β γ : ℕ → Kc) (gv : ℕ → K)
    (hc : ∀ i < n, c i = ∑ u ∈ Finset.range NU, β u * algebraMap ℚ Kc (Uv u i))
    (hβ : ∀ u < NU, β u = ∑ k ∈ Finset.range NK, γ k * algebraMap ℚ Kc (δ k u)) :
    ∑ i ∈ Finset.range n, alg (c i) * gv i = ∑ k ∈ Finset.range NK, alg (γ k) *
      ∑ u ∈ Finset.range NU, ((δ k u : ℚ) : K) * ∑ i ∈ Finset.range n, ((Uv u i : ℚ) : K) * gv i := by
  have hq : ∀ q : ℚ, alg (algebraMap ℚ Kc q) = (q : K) := fun q ↦ by
    rw [eq_ratCast (algebraMap ℚ Kc) q, map_ratCast]
  have e : ∀ i ∈ Finset.range n, alg (c i) * gv i = ∑ u ∈ Finset.range NU, ∑ k ∈ Finset.range NK,
      alg (γ k) * (((δ k u : ℚ) : K) * (((Uv u i : ℚ) : K) * gv i)) := fun i hi ↦ by
    rw [hc i (Finset.mem_range.mp hi), map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    rw [hβ u (Finset.mem_range.mp hu), Finset.sum_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_mul, hq, hq]
    ring
  rw [Finset.sum_congr rfl e]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.sum_comm]

set_option maxHeartbeats 3200000 in
/-- **Completeness of the inductive step.** -/
theorem paramLim_succ_complete (m : ℕ) (h : T.Tr (m + 1))
    (hη : ∀ y : T.F m, y′ ≠ T.valN m (ηs m))
    (IH : ∀ W', T.PLSound m (fun i hi ↦ h i (by omega)) W' (paramLim ηs m W') ∧
      T.PLComplete m (fun i hi ↦ h i (by omega)) W' (paramLim ηs m W'))
    (W : List (Code (m + 2))) : T.PLComplete (m + 1) h W (paramLim ηs (m + 1) W) := by
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) h with hM'
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hspec := T.limSpec_of m hm IH
  have hconstK : ∀ y : T.F m, y′ = 0 → ∃ κ : Kc, y = algebraMap Kc (T.F m) κ := fun y hy ↦
    T.const_F y hy
  have hη' : ∀ y : T.F m, y′ ≠ M.sem (ηs m) := by rw [hM, T.sem_MP_F]; exact hη
  intro c hc z hz
  set n := W.length with hn
  set U := consys ηs (m + 1) (simpleCodes (ηs := ηs) m W) with hU
  set EE := U.map (vecOf n) with hEE
  set gv : ℕ → T.F (m + 1) := fun i ↦ M'.sem (gCode (ηs := ηs) m (W.getD i (zc ηs (m + 1))))
    with hgv
  set pv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (pPart (ηs := ηs) m (W.getD i (zc ηs (m + 1))))
    with hpv
  set rv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (GPoly.divMod (opsQ ηs m)
    (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).b
    (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).s).2 with hrv
  set sv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).s
    with hsv
  set G := ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) * gv i with hG
  -- the derivative of `z - G`
  have hZd : (z - G)′ = ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) *
      T.phi m (pv i) + ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) *
        (T.phi m (rv i) / T.phi m (sv i)) := by
    rw [map_sub, hz, hG, T.deriv_sum_Kc, sumK, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(T.weight_decomp m h (W.getD i (zc ηs (m + 1)))).1]
    simp only [hgv, hpv, hrv, hsv, gCode, pPart, hM, hM']
    ring
  -- in `E`: the proper step
  set A := ∑ i ∈ Finset.range n, C (algebraMap Kc (T.F m) (c.getD i 0)) * pv i with hA
  set l := (List.range n).map fun i ↦ (C (algebraMap Kc (T.F m) (c.getD i 0)) * rv i, sv i) with hl
  have hZE : ((z - G : T.F (m + 1)) : E)′ = aeval (T.ts m) A +
      (l.map fun r ↦ aeval (T.ts m) r.1 / aeval (T.ts m) r.2).sum := by
    rw [← coe_deriv, hZd, IntermediateField.coe_add, T.coe_phi_sum, T.coe_phi_div_sum]
  obtain ⟨hsum0, P, hZP, hPd⟩ := T.proper_step_sum m htr A l
    (fun p hp ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact (T.weight_decomp m h (W.getD i (zc ηs (m + 1)))).2.1)
    (fun p hp ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _)
        (T.weight_decomp m h (W.getD i (zc ηs (m + 1)))).2.2)
    _ (z - G).2 hZE
  -- the simple parts cancel: the constant system at level `m + 1`
  have hsimple0 : ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) *
      (T.phi m (rv i) / T.phi m (sv i)) = 0 := by
    apply Subtype.ext
    rw [T.coe_phi_div_sum, ← hl, hsum0]
    rfl
  have h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c * M'.sem v)
      ((List.range (simpleCodes (ηs := ηs) m W).length).map fun i ↦ c.getD i 0)
      (simpleCodes (ηs := ηs) m W)).sum = 0 := by
    rw [zipWith_sum_range _ 0 (zc ηs (m + 1)) _ _ (by simp), ← hsimple0]
    refine Finset.sum_congr (by simp [length_simpleCodes, hn]) fun i hi ↦ ?_
    have hi' : i < n := Finset.mem_range.mp hi
    rw [getD_range_map (fun j ↦ c.getD j 0) 0 (by rw [length_simpleCodes]; exact hi'),
      T.sem_simple m h W hi']
  obtain ⟨β, hβl, hβ⟩ := T.consys_complete (m + 1) h (simpleCodes (ηs := ηs) m W) _ (by simp) h0
  have hβc : ∀ i < n, c.getD i 0 = ∑ u ∈ Finset.range U.length,
      β.getD u 0 * algebraMap ℚ Kc ((U.getD u []).getD i 0) := fun i hi ↦ by
    have := hβ i
    rw [getD_range_map (fun j ↦ c.getD j 0) 0 (by rw [length_simpleCodes]; exact hi),
      zipWith_sum_range _ 0 [] _ _ hβl, hβl] at this
    exact this
  -- the polynomial problem, in terms of `β`
  set Pu := EE.map fun e ↦ lcombGP (opsQ ηs m) (cstN m) e
    (((W.map (hermW (ηs := ηs) m)).map fun h ↦ GPoly.divMod (opsQ ηs m) h.b h.s).map Prod.fst)
    with hPu
  set βt := (List.range U.length).map fun u ↦ β.getD u 0 with hβt
  have hβtD : ∀ u < U.length, βt.getD u 0 = β.getD u 0 := fun u hu ↦ getD_range_map _ _ hu
  have hlPu : Pu.length = U.length := by simp [hPu, hEE]
  have hPoly : Dη M (ηs m) P = polySumC (algebraMap Kc (T.F m)) M βt Pu := by
    rw [Dη, ← T.wPoly_eq m hm, hPd, polySumC, hA]
    have e : ∀ u ∈ Finset.range Pu.length, C (algebraMap Kc (T.F m) (βt.getD u 0)) *
        GPoly.toPoly M (Pu.getD u []) = ∑ i ∈ Finset.range n,
          C (algebraMap Kc (T.F m) (β.getD u 0 * algebraMap ℚ Kc ((U.getD u []).getD i 0))) *
            pv i := fun u hu ↦ by
      have hu' : u < U.length := by rw [← hlPu]; exact Finset.mem_range.mp hu
      rw [hβtD u hu', hPu, getD_map' _ EE [] [] (by simpa [hEE] using hu'), T.toPoly_Pu m hm W,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [hEE, getD_map' _ U [] [] hu', getD_vecOf, if_pos (Finset.mem_range.mp hi), map_mul,
        T.algebraMap_ratCast, C_mul, mul_assoc]
    rw [Finset.sum_congr rfl e, Finset.sum_comm, hlPu]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← hβc i (Finset.mem_range.mp hi)]
  obtain ⟨γ, hγc, hγP⟩ := paramPoly_complete (algebraMap Kc (T.F m)) (ηs m) (paramLim ηs m)
    (T.sem_cstN m hm) hspec hconstK (fun q ↦ T.algebraMap_ratCast q) hη' Pu βt
    (fun u hu ↦ List.getD_eq_default _ _ (by simp [hβt, ← hlPu]; omega)) P hPoly
  -- assemble
  set pp := paramPoly (opsQ ηs m) (cstN m) (ηs m) (paramLim ηs m) Pu with hpp
  set Gu := EE.map fun e ↦ lcombCode (opsQ ηs (m + 1)) (cstN (m + 1)) e
    ((W.map (hermW (ηs := ηs) m)).map fun h ↦ ((h.gn, h.gd) : Code (m + 2))) with hGu
  set F' : List ℚ × GPoly (Code (m + 1)) → List ℚ × Code (m + 2) := fun r ↦
    (vcomb n r.1 EE, (opsQ ηs (m + 1)).add (lcombCode (opsQ ηs (m + 1)) (cstN (m + 1)) r.1 Gu)
      ((r.2, [(opsQ ηs m).one]) : Code (m + 2))) with hF'
  have hout : paramLim ηs (m + 1) W = pp.map F' := rfl
  have hβu : ∀ u < U.length, β.getD u 0 = ∑ k ∈ Finset.range pp.length,
      γ.getD k 0 * algebraMap ℚ Kc ((pp.getD k ([], [])).1.getD u 0) := fun u hu ↦ by
    rw [← hβtD u hu, hγc u]
  have hlGu : Gu.length = U.length := by simp [hGu, hEE]
  rw [hout]
  have hgetD : ∀ k < pp.length, (pp.map F').getD k ([], zc ηs (m + 1)) = F' (pp.getD k ([], [])) :=
    fun k hk ↦ getD_map' _ pp ([], []) _ hk
  have hlen : (pp.map F').length = pp.length := List.length_map _
  -- the coefficients
  have hcoef : ∀ i, c.getD i 0 = ∑ k ∈ Finset.range (pp.map F').length,
      γ.getD k 0 * algebraMap ℚ Kc (((pp.map F').getD k ([], zc ηs (m + 1))).1.getD i 0) := by
    intro i
    rw [hlen]
    have e : ∀ k ∈ Finset.range pp.length, γ.getD k 0 * algebraMap ℚ Kc
        (((pp.map F').getD k ([], zc ηs (m + 1))).1.getD i 0) = γ.getD k 0 *
          algebraMap ℚ Kc ((vcomb n (pp.getD k ([], [])).1 EE).getD i 0) := fun k hk ↦ by
      rw [hgetD k (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl e]
    by_cases hi : i < n
    · rw [hβc i hi]
      simp only [getD_vcomb, if_pos hi, map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr (by simp [hEE]) fun u hu ↦ ?_
      have hu' : u < U.length := by simpa [hEE] using hu
      rw [hβu u hu', Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [hEE, getD_map' _ U [] [] hu', getD_vecOf, if_pos hi]
      ring
    · rw [hc i (by omega)]
      symm
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [getD_vcomb, if_neg hi, map_zero, mul_zero]
  refine ⟨γ, hcoef, ?_⟩
  -- the antiderivative
  have hZP' : z - G = T.phi m P := Subtype.ext (by rw [hZP, coe_phi])
  have hsemy : ∀ k < pp.length, M'.sem (F' (pp.getD k ([], []))).2 =
      ∑ u ∈ Finset.range U.length, (((pp.getD k ([], [])).1.getD u 0 : ℚ) : T.F (m + 1)) *
        ∑ i ∈ Finset.range n, (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) * gv i +
      T.phi m (GPoly.toPoly M (pp.getD k ([], [])).2) := fun k hk ↦ by
    rw [hF']
    simp only
    rw [T.sem_final m h, sem_lcombCode (T.MP (m + 1) h) (cstN (m + 1)) (T.sem_cstN (m + 1) h),
      zipWith_sum_getD (fun (q : ℚ) (a : Code (m + 2)) ↦ ((q : ℚ) : T.F (m + 1)) *
        (T.MP (m + 1) h).sem a) 0 (zc ηs (m + 1)) (by simp), hlGu, add_left_inj]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    have hu' := Finset.mem_range.mp hu
    rw [hGu, getD_map' _ EE [] (zc ηs (m + 1)) (by simpa [hEE] using hu'), T.sem_Gu m h W]
    refine congrArg _ (Finset.sum_congr rfl fun i hi ↦ ?_)
    rw [hEE, getD_map' _ U [] [] hu', getD_vecOf, if_pos (Finset.mem_range.mp hi)]
  have htotal : z = ∑ k ∈ Finset.range (pp.map F').length, algebraMap Kc (T.F (m + 1)) (γ.getD k 0) *
      M'.sem ((pp.map F').getD k ([], zc ηs (m + 1))).2 := by
    rw [hlen]
    have e : ∀ k ∈ Finset.range pp.length, algebraMap Kc (T.F (m + 1)) (γ.getD k 0) *
        M'.sem ((pp.map F').getD k ([], zc ηs (m + 1))).2 =
        algebraMap Kc (T.F (m + 1)) (γ.getD k 0) * (∑ u ∈ Finset.range U.length,
          (((pp.getD k ([], [])).1.getD u 0 : ℚ) : T.F (m + 1)) *
            ∑ i ∈ Finset.range n, (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) * gv i +
          T.phi m (GPoly.toPoly M (pp.getD k ([], [])).2)) := fun k hk ↦ by
      rw [hgetD k (Finset.mem_range.mp hk), hsemy k (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl e]
    simp only [mul_add, Finset.sum_add_distrib]
    have hphi : ∑ k ∈ Finset.range pp.length, algebraMap Kc (T.F (m + 1)) (γ.getD k 0) *
        T.phi m (GPoly.toPoly M (pp.getD k ([], [])).2) = T.phi m P := by
      rw [hγP, map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_mul, ← T.algebraMap_succ]
    rw [hphi, ← hZP', hG]
    have hG' : ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) * gv i =
        ∑ k ∈ Finset.range pp.length, algebraMap Kc (T.F (m + 1)) (γ.getD k 0) *
          ∑ u ∈ Finset.range U.length, (((pp.getD k ([], [])).1.getD u 0 : ℚ) : T.F (m + 1)) *
            ∑ i ∈ Finset.range n, (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) * gv i := by
      exact reassemble (algebraMap Kc (T.F (m + 1))) n U.length pp.length
        (fun u i ↦ (U.getD u []).getD i 0) (fun k u ↦ (pp.getD k ([], [])).1.getD u 0)
        (fun i ↦ c.getD i 0) (fun u ↦ β.getD u 0) (fun k ↦ γ.getD k 0) gv hβc hβu
    rw [hG']
    ring
  rw [← htotal, sub_self, map_zero]

/-- **Parametric limited integration at every level**: sound and complete, given that no `ηᵢ`
(`i < m`) is a derivative in `F i`. -/
theorem paramLim_spec : ∀ (m : ℕ) (h : T.Tr m), (∀ i < m, ∀ y : T.F i, y′ ≠ T.valN i (ηs i)) →
    ∀ W : List (Code (m + 1)),
      T.PLSound m h W (paramLim ηs m W) ∧ T.PLComplete m h W (paramLim ηs m W)
  | 0, h, _, W => T.paramLim_zero h W
  | m + 1, h, hη, W =>
    have IH := fun W' ↦ paramLim_spec m (fun i hi ↦ h i (by omega))
      (fun i hi ↦ hη i (by omega)) W'
    ⟨T.paramLim_succ_sound m h IH W,
      T.paramLim_succ_complete m h (hη m (Nat.lt_succ_self m)) IH W⟩

end NestTower








end Tower.NestP
