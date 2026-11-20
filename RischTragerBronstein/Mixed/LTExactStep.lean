import RischTragerBronstein.Mixed.LTExact

/-!
# Towers of logarithms over a curve: the inductive step of parametric exact integration

Ported from `Tower.NestP` (`NestPParamStep`), for realizations of the log tower over a curve. At
level `m + 1` (`t = tₘ`, `t′ = ηₘ ∈ F m`): every weight is Hermite-reduced,
`wᵢ = gᵢ′ + Pᵢ + rᵢ / sᵢ`; a solution `z′ = ∑ cᵢ wᵢ` forces `∑ cᵢ rᵢ / sᵢ = 0`
(`proper_step_sum`), a constant system at level `m + 1` (`lrel`), and `z − ∑ cᵢ gᵢ` is a
polynomial `Q` with `Q′ = ∑ cᵢ Pᵢ` (`Tower.NestP.paramPoly`, solver one level down `lex m`).

**`lex_spec`**: `lex` is sound and complete at every level of every realization in which the
generators are transcendental.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.LT

open CPoly Sup
open Tower.NestP (lcombCode lcombGP vcomb paramPoly LimSpec sQ sC Dη polySumC polySumQ
  sem_lcombCode toPoly_lcombGP zipWith_sum_getD getD_vcomb paramPoly_sound paramPoly_complete)
open Tower.NestP.NestTower (getD_range_map getD_map' vecOf getD_vecOf list_sum_map_range
  zipWith_sum_range)

universe u

variable {Fc : BPoly ℚ} {us : (m : ℕ) → LC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

lemma lex_succ_eq (m : ℕ) (W : List (LC (m + 1))) :
    lex Fc us (m + 1) W =
      let O := LO Fc us m
      let O' := LO Fc us (m + 1)
      let n := W.length
      let H := W.map (hermW Fc us m)
      let QR := H.map fun h ↦ GPoly.divMod O h.b h.s
      let U := lrel Fc us (m + 1) (simpleCodes Fc us m W)
      let E := U.map (vecOf n)
      let Pu := E.map fun e ↦ lcombGP O (lcst Fc us m) e (QR.map Prod.fst)
      let Gu := E.map fun e ↦ lcombCode O' (lcst Fc us (m + 1)) e
        (H.map fun h ↦ ((h.gn, h.gd) : GFrac (LC m)))
      (paramPoly O (lcst Fc us m) (etaC Fc us m) (lex Fc us m) Pu).map fun r ↦
        (vcomb n r.1 E, O'.add (lcombCode O' (lcst Fc us (m + 1)) r.1 Gu)
          ((r.2, [O.one]) : GFrac (LC m))) := rfl

namespace LTower

variable (T : LTower Fc us Cc L)


/-- **Sums of proper fractions are not derivatives**, at level `m + 1`. -/
lemma proper_step_sum (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) (A : (T.F m)[X])
    (l : List ((T.F m)[X] × (T.F m)[X])) (hsq : ∀ p ∈ l, Squarefree p.2)
    (hdeg : ∀ p ∈ l, p.1.degree < p.2.degree) (z : L) (hz : z ∈ T.F (m + 1))
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
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ P : (T.F m)⟮T.ts m⟯) : L) =
      aeval (T.ts m) P := algebraMap_adjoinSimple _
  have hsum : ∀ l' : List ((T.F m)[X] × (T.F m)[X]),
      (((l'.map fun p ↦ algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ p.1 /
        algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ p.2).sum : (T.F m)⟮T.ts m⟯) : L) =
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

/-- **The decomposition of a weight** `w = g′ + P + r / s` at level `m + 1`. -/
lemma weight_decomp (m : ℕ) (h : T.Tr (m + 1)) (w : LC (m + 1)) :
    (T.MP (m + 1) h).sem w =
      ((T.MP (m + 1) h).sem (((hermW Fc us m w).gn, (hermW Fc us m w).gd) :
        LC (m + 1)))′ +
        T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega))
          (GPoly.divMod (LO Fc us m) (hermW Fc us m w).b (hermW Fc us m w).s).1) +
        T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega))
          (GPoly.divMod (LO Fc us m) (hermW Fc us m w).b (hermW Fc us m w).s).2) /
        T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) (hermW Fc us m w).s) ∧
    Squarefree (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) (hermW Fc us m w).s) ∧
    (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega))
      (GPoly.divMod (LO Fc us m) (hermW Fc us m w).b (hermW Fc us m w).s).2).degree <
      (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) (hermW Fc us m w).s).degree := by
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injective htr
  obtain ⟨w', hw'⟩ : ∃ w' : GPoly (LC m) × GPoly (LC m), w' =
      if GPoly.isZero (LO Fc us m) w.2 then (([] : GPoly (LC m)), [(LO Fc us m).one])
        else w := ⟨_, rfl⟩
  have hsemw : (T.MP (m + 1) h).sem w = T.phi m (GPoly.toPoly M w'.1) /
      T.phi m (GPoly.toPoly M w'.2) := by
    rw [T.sem_MP_succ]
    by_cases hz : GPoly.isZero (LO Fc us m) w.2 = true
    · simp only [hz, ↓reduceIte] at hw'
      rw [hw', (GPoly.isZero_iff (T.MP m fun i hi ↦ h i (by omega)) _).mp hz]
      simp
    · simp only [hz, ↓reduceIte, Bool.false_eq_true] at hw'
      rw [hw']
  have hD : GPoly.toPoly M w'.2 ≠ 0 := by
    by_cases hz : GPoly.isZero (LO Fc us m) w.2 = true
    · simp only [hz, ↓reduceIte] at hw'
      rw [hw']
      simp [M.sem_one]
    · simp only [hz, ↓reduceIte, Bool.false_eq_true] at hw'
      rw [hw']
      exact fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr w'.1 w'.2 hD
  rw [← hM] at hval hsq
  have hherm : hermW Fc us m w = GPoly.hermite (LO Fc us m) [etaC Fc us m] w'.1 w'.2 := by
    rw [hw']; rfl
  rw [hherm]
  refine ⟨?_, hsq, GPoly.divMod_degree_lt M _ _ hsq.ne_zero⟩
  have hdm := GPoly.divMod_spec M (GPoly.hermite (LO Fc us m) [etaC Fc us m] w'.1 w'.2).b
    (GPoly.hermite (LO Fc us m) [etaC Fc us m] w'.1 w'.2).s
  have hs0 : T.phi m (GPoly.toPoly M (GPoly.hermite (LO Fc us m) [etaC Fc us m] w'.1 w'.2).s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
  have hg : (T.MP (m + 1) h).sem (((GPoly.hermite (LO Fc us m) [etaC Fc us m] w'.1 w'.2).gn,
      (GPoly.hermite (LO Fc us m) [etaC Fc us m] w'.1 w'.2).gd) : LC (m + 1)) =
      T.phi m (GPoly.toPoly M (GPoly.hermite (LO Fc us m) [etaC Fc us m] w'.1 w'.2).gn) /
        T.phi m (GPoly.toPoly M (GPoly.hermite (LO Fc us m) [etaC Fc us m] w'.1 w'.2).gd) := rfl
  rw [hsemw, hval, hg, hdm, map_add, map_mul]
  field_simp
  ring

lemma len_zip_map {β γ δ ε : Type*} (g : β → δ) (f : δ → γ) (k : γ × δ → ε) (l : List β) :
    ((List.zip ((l.map g).map f) (l.map g)).map k).length = l.length := by simp

lemma getD_zip_map {β γ δ ε : Type*} (g : β → δ) (f : δ → γ) (k : γ × δ → ε) (l : List β)
    (d : β) (d' : ε) {i : ℕ} (hi : i < l.length) :
    ((List.zip ((l.map g).map f) (l.map g)).map k).getD i d' =
      k (f (g (l.getD i d)), g (l.getD i d)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

lemma length_simpleCodes (m : ℕ) (W : List (LC (m + 1))) :
    (simpleCodes Fc us m W).length = W.length :=
  len_zip_map (hermW Fc us m) (fun h ↦ GPoly.divMod (LO Fc us m) h.b h.s)
    (fun p ↦ ((p.1.2, p.2.s) : LC (m + 1))) W

lemma getD_simpleCodes (m : ℕ) (W : List (LC (m + 1))) {i : ℕ} (hi : i < W.length) :
    (simpleCodes Fc us m W).getD i (zc Fc us (m + 1)) =
      (((GPoly.divMod (LO Fc us m) (hermW Fc us m (W.getD i (zc Fc us (m + 1)))).b
        (hermW Fc us m (W.getD i (zc Fc us (m + 1)))).s).2,
        (hermW Fc us m (W.getD i (zc Fc us (m + 1)))).s) : LC (m + 1)) :=
  getD_zip_map (hermW Fc us m) (fun h ↦ GPoly.divMod (LO Fc us m) h.b h.s)
    (fun p ↦ ((p.1.2, p.2.s) : LC (m + 1))) W (zc Fc us (m + 1)) (zc Fc us (m + 1)) hi

lemma len_map_map {β δ γ : Type*} (g : β → δ) (f : δ → γ) (l : List β) :
    ((l.map g).map f).length = l.length := by simp

lemma getD_map_map {β δ γ : Type*} (g : β → δ) (f : δ → γ) (l : List β) (d : β) (d' : γ)
    {i : ℕ} (hi : i < l.length) : ((l.map g).map f).getD i d' = f (g (l.getD i d)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

lemma sem_Gu (m : ℕ) (h : T.Tr (m + 1)) (W : List (LC (m + 1))) (e : List ℚ) :
    (T.MP (m + 1) h).sem (lcombCode (LO Fc us (m + 1)) (lcst Fc us (m + 1)) e
      ((W.map (hermW Fc us m)).map fun h ↦ ((h.gn, h.gd) : LC (m + 1)))) =
      ∑ i ∈ Finset.range W.length, ((e.getD i 0 : ℚ) : T.F (m + 1)) *
        (T.MP (m + 1) h).sem (gCode Fc us m (W.getD i (zc Fc us (m + 1)))) := by
  rw [sem_lcombCode (T.MP (m + 1) h) (lcst Fc us (m + 1)) (T.sem_lcst (m + 1) h),
    zipWith_sum_getD (fun (q : ℚ) (a : LC (m + 1)) ↦ ((q : ℚ) : T.F (m + 1)) *
      (T.MP (m + 1) h).sem a) 0 (zc Fc us (m + 1)) (by simp)]
  refine Finset.sum_congr (congrArg Finset.range (len_map_map _ _ W)) fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  congr 2
  exact getD_map_map (hermW Fc us m) (fun h ↦ ((h.gn, h.gd) : LC (m + 1))) W
    (zc Fc us (m + 1)) (zc Fc us (m + 1)) hi'

lemma toPoly_Pu (m : ℕ) (hm : T.Tr m) (W : List (LC (m + 1))) (e : List ℚ) :
    GPoly.toPoly (T.MP m hm) (lcombGP (LO Fc us m) (lcst Fc us m) e
      (((W.map (hermW Fc us m)).map fun h ↦ GPoly.divMod (LO Fc us m) h.b h.s).map Prod.fst)) =
      ∑ i ∈ Finset.range W.length, C ((e.getD i 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MP m hm) (pPart Fc us m (W.getD i (zc Fc us (m + 1)))) := by
  rw [toPoly_lcombGP (T.MP m hm) (lcst Fc us m) (T.sem_lcst m hm),
    zipWith_sum_getD (fun (q : ℚ) (p : GPoly (LC m)) ↦ C ((q : ℚ) : T.F m) *
      GPoly.toPoly (T.MP m hm) p) 0 [] (by simp)]
  refine Finset.sum_congr (by simp) fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  congr 2
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getD_eq_getElem _ _ hi']
  simp [pPart, List.getD_eq_getElem _ _ hi']

lemma sem_final (m : ℕ) (h : T.Tr (m + 1)) (a : LC (m + 1)) (Q : GPoly (LC m)) :
    (T.MP (m + 1) h).sem ((LO Fc us (m + 1)).add a ((Q, [(LO Fc us m).one]) : LC (m + 1))) =
      (T.MP (m + 1) h).sem a + T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) Q) := by
  refine ((T.MP (m + 1) h).sem_add a _).trans ?_
  congr 1
  refine (T.sem_MP_succ m h _).trans ?_
  simp [(T.MP m fun i hi ↦ h i (by omega)).sem_one]

/-- The relation given by a basis vector of the constant system on the simple parts. -/
lemma rel_simple (m : ℕ) (h : T.Tr (m + 1)) (W : List (LC (m + 1))) (u : CPoly ℚ)
    (hu : u ∈ lrel Fc us (m + 1) (simpleCodes Fc us m W)) :
    ∑ i ∈ Finset.range W.length, ((u.getD i 0 : ℚ) : T.F (m + 1)) *
      (T.MP (m + 1) h).sem ((simpleCodes Fc us m W).getD i (zc Fc us (m + 1))) = 0 := by
  have := T.lrel_sound (m + 1) h (simpleCodes Fc us m W) u hu
  rw [zipWith_sum_range _ 0 (zc Fc us (m + 1)) _ _ (by simp)] at this
  rw [← this]
  refine Finset.sum_congr (by simp [length_simpleCodes]) fun i hi ↦ ?_
  have hi' : i < W.length := by simpa [length_simpleCodes] using hi
  rw [getD_range_map (fun j ↦ algebraMap ℚ Cc (u.getD j 0)) 0
    (by rw [length_simpleCodes]; exact hi'), T.algebraMap_ratCast]

/-- The value of a simple part. -/
lemma sem_simple (m : ℕ) (h : T.Tr (m + 1)) (W : List (LC (m + 1))) {i : ℕ} (hi : i < W.length) :
    (T.MP (m + 1) h).sem ((simpleCodes Fc us m W).getD i (zc Fc us (m + 1))) =
      T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega))
        (GPoly.divMod (LO Fc us m) (hermW Fc us m (W.getD i (zc Fc us (m + 1)))).b
          (hermW Fc us m (W.getD i (zc Fc us (m + 1)))).s).2) /
      T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega))
        (hermW Fc us m (W.getD i (zc Fc us (m + 1)))).s) := by
  rw [getD_simpleCodes m W hi]
  rfl

/-- The one-level-down solver meets the specification. -/
lemma limSpec_of (m : ℕ) (hm : T.Tr m)
    (IH : ∀ W', T.PLSound m hm W' (lex Fc us m W') ∧ T.PLComplete m hm W' (lex Fc us m W')) :
    LimSpec (algebraMap Cc (T.F m)) (T.MP m hm) (lex Fc us m) :=
  ⟨fun ws r hr ↦ (IH ws).1 r hr, fun ws c hc z hz ↦ (IH ws).2 c hc z hz⟩

/-- **Soundness of the inductive step.** -/
theorem paramLim_succ_sound (m : ℕ) (h : T.Tr (m + 1))
    (IH : ∀ W', T.PLSound m (fun i hi ↦ h i (by omega)) W' (lex Fc us m W') ∧
      T.PLComplete m (fun i hi ↦ h i (by omega)) W' (lex Fc us m W'))
    (W : List (LC (m + 1))) : T.PLSound (m + 1) h W (lex Fc us (m + 1) W) := by
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  have hspec := T.limSpec_of m hm IH
  have hconstK : ∀ y : T.F m, y′ = 0 → ∃ κ : Cc, y = algebraMap Cc (T.F m) κ := fun y hy ↦
    T.const_F y hy
  intro r' hr'
  rw [lex_succ_eq] at hr'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  set U := lrel Fc us (m + 1) (simpleCodes Fc us m W) with hU
  set E := U.map (vecOf W.length) with hE
  have hsound := paramPoly_sound (algebraMap Cc (T.F m)) (etaC Fc us m) (lex Fc us m)
    (T.sem_lcst m hm) hspec hconstK (fun q ↦ T.algebraMap_ratCast q) _ r hr
  simp only
  rw [T.sem_final m h, map_add,
    sem_lcombCode (T.MP (m + 1) h) (lcst Fc us (m + 1)) (T.sem_lcst (m + 1) h),
    zipWith_sum_getD (fun (q : ℚ) (a : LC (m + 1)) ↦ ((q : ℚ) : T.F (m + 1)) *
      (T.MP (m + 1) h).sem a) 0 (zc Fc us (m + 1)) (by simp),
    T.deriv_sum_ratCast, T.deriv_phi, ← hM, T.wPoly_eq m hm (T.lt_of_transcendental (h m (by omega))), ← hM]
  change _ + T.phi m (Dη M (etaC Fc us m) _) = _
  rw [hsound, polySumQ, map_sum]
  have hlG : (E.map fun e ↦ lcombCode (LO Fc us (m + 1)) (lcst Fc us (m + 1)) e
      ((W.map (hermW Fc us m)).map fun h ↦ ((h.gn, h.gd) : LC (m + 1)))).length = U.length := by
    simp [hE]
  have hlP : (E.map fun e ↦ lcombGP (LO Fc us m) (lcst Fc us m) e
      (((W.map (hermW Fc us m)).map fun h ↦ GPoly.divMod (LO Fc us m) h.b h.s).map
        Prod.fst)).length = U.length := by simp [hE]
  -- regroup by basis vector
  have hterm : ∀ u < U.length,
      ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * ((T.MP (m + 1) h).sem
        ((E.map fun e ↦ lcombCode (LO Fc us (m + 1)) (lcst Fc us (m + 1)) e
          ((W.map (hermW Fc us m)).map fun h ↦ ((h.gn, h.gd) : LC (m + 1)))).getD u
            (zc Fc us (m + 1))))′ +
      T.phi m (C ((r.1.getD u 0 : ℚ) : T.F m) * GPoly.toPoly M
        ((E.map fun e ↦ lcombGP (LO Fc us m) (lcst Fc us m) e
          (((W.map (hermW Fc us m)).map fun h ↦ GPoly.divMod (LO Fc us m) h.b h.s).map
            Prod.fst)).getD u [])) =
      ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * ∑ i ∈ Finset.range W.length,
        (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) *
          (T.MP (m + 1) h).sem (W.getD i (zc Fc us (m + 1))) := by
    intro u hu
    have huE : u < E.length := by simpa [hE] using hu
    rw [getD_map' _ E [] (zc Fc us (m + 1)) huE, getD_map' _ E [] [] huE, T.sem_Gu m h W,
      T.toPoly_Pu m hm W, T.deriv_sum_ratCast, Finset.mul_sum, map_mul, map_sum,
      T.phi_C_ratCast, Finset.mul_sum, ← Finset.sum_add_distrib]
    have hrel := T.rel_simple m h W (U.getD u []) (by
      rw [List.getD_eq_getElem _ _ hu]; exact List.getElem_mem _)
    have e : ∀ i ∈ Finset.range W.length,
        ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * ((((E.getD u []).getD i 0 : ℚ) : T.F (m + 1)) *
          ((T.MP (m + 1) h).sem (gCode Fc us m (W.getD i (zc Fc us (m + 1)))))′) +
        ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * T.phi m (C (((E.getD u []).getD i 0 : ℚ) : T.F m) *
          GPoly.toPoly (T.MP m hm) (pPart Fc us m (W.getD i (zc Fc us (m + 1))))) =
        ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * ((((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) *
          (T.MP (m + 1) h).sem (W.getD i (zc Fc us (m + 1)))) -
        ((r.1.getD u 0 : ℚ) : T.F (m + 1)) * ((((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) *
          (T.MP (m + 1) h).sem ((simpleCodes Fc us m W).getD i (zc Fc us (m + 1)))) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [hE, getD_map' _ U [] [] hu, getD_vecOf, if_pos hi', map_mul, T.phi_C_ratCast,
        (T.weight_decomp m h (W.getD i (zc Fc us (m + 1)))).1, T.sem_simple m h W hi']
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

lemma coe_algebraMap_F (m : ℕ) (κ : Cc) :
    ((algebraMap Cc (T.F m) κ : T.F m) : L) = algebraMap Cc L κ := rfl

lemma coe_phi_sum (m : ℕ) (n : ℕ) (a : ℕ → Cc) (p : ℕ → (T.F m)[X]) :
    ((∑ i ∈ Finset.range n, algebraMap Cc (T.F (m + 1)) (a i) * T.phi m (p i) : T.F (m + 1)) : L) =
      aeval (T.ts m) (∑ i ∈ Finset.range n, C (algebraMap Cc (T.F m) (a i)) * p i) := by
  rw [map_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, aeval_C, coe_phi]
  rfl

lemma coe_phi_div_sum (m : ℕ) (n : ℕ) (a : ℕ → Cc) (p q : ℕ → (T.F m)[X]) :
    ((∑ i ∈ Finset.range n, algebraMap Cc (T.F (m + 1)) (a i) *
      (T.phi m (p i) / T.phi m (q i)) : T.F (m + 1)) : L) =
      (((List.range n).map fun i ↦ (C (algebraMap Cc (T.F m) (a i)) * p i, q i)).map
        fun r ↦ aeval (T.ts m) r.1 / aeval (T.ts m) r.2).sum := by
  rw [List.map_map, list_sum_map_range]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Function.comp_apply, coe_phi, map_mul, aeval_C]
  rw [show algebraMap (T.F m) L (algebraMap Cc (T.F m) (a i)) = algebraMap Cc L (a i) from rfl]
  ring

/-- Reassembling the double change of basis. -/
lemma reassemble {K : Type*} [Field K] [CharZero K] (alg : Cc →+* K) (n NU NK : ℕ)
    (Uv δ : ℕ → ℕ → ℚ) (c β γ : ℕ → Cc) (gv : ℕ → K)
    (hc : ∀ i < n, c i = ∑ u ∈ Finset.range NU, β u * algebraMap ℚ Cc (Uv u i))
    (hβ : ∀ u < NU, β u = ∑ k ∈ Finset.range NK, γ k * algebraMap ℚ Cc (δ k u)) :
    ∑ i ∈ Finset.range n, alg (c i) * gv i = ∑ k ∈ Finset.range NK, alg (γ k) *
      ∑ u ∈ Finset.range NU, ((δ k u : ℚ) : K) * ∑ i ∈ Finset.range n, ((Uv u i : ℚ) : K) * gv i := by
  have hq : ∀ q : ℚ, alg (algebraMap ℚ Cc q) = (q : K) := fun q ↦ by
    rw [eq_ratCast (algebraMap ℚ Cc) q, map_ratCast]
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
    (hη : ∀ y : T.F m, y′ ≠ T.eta m)
    (IH : ∀ W', T.PLSound m (fun i hi ↦ h i (by omega)) W' (lex Fc us m W') ∧
      T.PLComplete m (fun i hi ↦ h i (by omega)) W' (lex Fc us m W'))
    (W : List (LC (m + 1))) : T.PLComplete (m + 1) h W (lex Fc us (m + 1) W) := by
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) h with hM'
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hspec := T.limSpec_of m hm IH
  have hconstK : ∀ y : T.F m, y′ = 0 → ∃ κ : Cc, y = algebraMap Cc (T.F m) κ := fun y hy ↦
    T.const_F y hy
  have hη' : ∀ y : T.F m, y′ ≠ M.sem (etaC Fc us m) := by rw [hM, T.sem_eta]; exact hη
  intro c hc z hz
  set n := W.length with hn
  set U := lrel Fc us (m + 1) (simpleCodes Fc us m W) with hU
  set EE := U.map (vecOf n) with hEE
  set gv : ℕ → T.F (m + 1) := fun i ↦ M'.sem (gCode Fc us m (W.getD i (zc Fc us (m + 1))))
    with hgv
  set pv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (pPart Fc us m (W.getD i (zc Fc us (m + 1))))
    with hpv
  set rv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (GPoly.divMod (LO Fc us m)
    (hermW Fc us m (W.getD i (zc Fc us (m + 1)))).b
    (hermW Fc us m (W.getD i (zc Fc us (m + 1)))).s).2 with hrv
  set sv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (hermW Fc us m (W.getD i (zc Fc us (m + 1)))).s
    with hsv
  set G := ∑ i ∈ Finset.range n, algebraMap Cc (T.F (m + 1)) (c.getD i 0) * gv i with hG
  -- the derivative of `z - G`
  have hZd : (z - G)′ = ∑ i ∈ Finset.range n, algebraMap Cc (T.F (m + 1)) (c.getD i 0) *
      T.phi m (pv i) + ∑ i ∈ Finset.range n, algebraMap Cc (T.F (m + 1)) (c.getD i 0) *
        (T.phi m (rv i) / T.phi m (sv i)) := by
    rw [map_sub, hz, hG, T.deriv_sum_Cc, sumK, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(T.weight_decomp m h (W.getD i (zc Fc us (m + 1)))).1]
    simp only [hgv, hpv, hrv, hsv, gCode, pPart, hM, hM']
    ring
  -- in `E`: the proper step
  set A := ∑ i ∈ Finset.range n, C (algebraMap Cc (T.F m) (c.getD i 0)) * pv i with hA
  set l := (List.range n).map fun i ↦ (C (algebraMap Cc (T.F m) (c.getD i 0)) * rv i, sv i) with hl
  have hZE : ((z - G : T.F (m + 1)) : L)′ = aeval (T.ts m) A +
      (l.map fun r ↦ aeval (T.ts m) r.1 / aeval (T.ts m) r.2).sum := by
    rw [← coe_deriv, hZd, IntermediateField.coe_add, T.coe_phi_sum, T.coe_phi_div_sum]
  obtain ⟨hsum0, P, hZP, hPd⟩ := T.proper_step_sum m htr A l
    (fun p hp ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact (T.weight_decomp m h (W.getD i (zc Fc us (m + 1)))).2.1)
    (fun p hp ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _)
        (T.weight_decomp m h (W.getD i (zc Fc us (m + 1)))).2.2)
    _ (z - G).2 hZE
  -- the simple parts cancel: the constant system at level `m + 1`
  have hsimple0 : ∑ i ∈ Finset.range n, algebraMap Cc (T.F (m + 1)) (c.getD i 0) *
      (T.phi m (rv i) / T.phi m (sv i)) = 0 := by
    apply Subtype.ext
    rw [T.coe_phi_div_sum, ← hl, hsum0]
    rfl
  have h0 : (List.zipWith (fun c v ↦ algebraMap Cc (T.F (m + 1)) c * M'.sem v)
      ((List.range (simpleCodes Fc us m W).length).map fun i ↦ c.getD i 0)
      (simpleCodes Fc us m W)).sum = 0 := by
    rw [zipWith_sum_range _ 0 (zc Fc us (m + 1)) _ _ (by simp), ← hsimple0]
    refine Finset.sum_congr (by simp [length_simpleCodes, hn]) fun i hi ↦ ?_
    have hi' : i < n := Finset.mem_range.mp hi
    rw [getD_range_map (fun j ↦ c.getD j 0) 0 (by rw [length_simpleCodes]; exact hi'),
      T.sem_simple m h W hi']
  obtain ⟨β, hβ⟩ := T.lrel_complete (m + 1) h (simpleCodes Fc us m W) _ (by simp) h0
  have hβc : ∀ i < n, c.getD i 0 = ∑ u ∈ Finset.range U.length,
      β.getD u 0 * algebraMap ℚ Cc ((U.getD u []).getD i 0) := fun i hi ↦ by
    have := hβ i
    rw [getD_range_map (fun j ↦ c.getD j 0) 0 (by rw [length_simpleCodes]; exact hi)] at this
    exact this
  -- the polynomial problem, in terms of `β`
  set Pu := EE.map fun e ↦ lcombGP (LO Fc us m) (lcst Fc us m) e
    (((W.map (hermW Fc us m)).map fun h ↦ GPoly.divMod (LO Fc us m) h.b h.s).map Prod.fst)
    with hPu
  set βt := (List.range U.length).map fun u ↦ β.getD u 0 with hβt
  have hβtD : ∀ u < U.length, βt.getD u 0 = β.getD u 0 := fun u hu ↦ getD_range_map _ _ hu
  have hlPu : Pu.length = U.length := by simp [hPu, hEE]
  have hPoly : Dη M (etaC Fc us m) P = polySumC (algebraMap Cc (T.F m)) M βt Pu := by
    rw [Dη, ← T.wPoly_eq m hm (T.lt_of_transcendental (h m (by omega))), hPd, polySumC, hA]
    have e : ∀ u ∈ Finset.range Pu.length, C (algebraMap Cc (T.F m) (βt.getD u 0)) *
        GPoly.toPoly M (Pu.getD u []) = ∑ i ∈ Finset.range n,
          C (algebraMap Cc (T.F m) (β.getD u 0 * algebraMap ℚ Cc ((U.getD u []).getD i 0))) *
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
  obtain ⟨γ, hγc, hγP⟩ := paramPoly_complete (algebraMap Cc (T.F m)) (etaC Fc us m) (lex Fc us m)
    (T.sem_lcst m hm) hspec hconstK (fun q ↦ T.algebraMap_ratCast q) hη' Pu βt
    (fun u hu ↦ List.getD_eq_default _ _ (by simp [hβt, ← hlPu]; omega)) P hPoly
  -- assemble
  set pp := paramPoly (LO Fc us m) (lcst Fc us m) (etaC Fc us m) (lex Fc us m) Pu with hpp
  set Gu := EE.map fun e ↦ lcombCode (LO Fc us (m + 1)) (lcst Fc us (m + 1)) e
    ((W.map (hermW Fc us m)).map fun h ↦ ((h.gn, h.gd) : LC (m + 1))) with hGu
  set F' : List ℚ × GPoly (LC m) → List ℚ × LC (m + 1) := fun r ↦
    (vcomb n r.1 EE, (LO Fc us (m + 1)).add (lcombCode (LO Fc us (m + 1)) (lcst Fc us (m + 1)) r.1 Gu)
      ((r.2, [(LO Fc us m).one]) : LC (m + 1))) with hF'
  have hout : lex Fc us (m + 1) W = pp.map F' := rfl
  have hβu : ∀ u < U.length, β.getD u 0 = ∑ k ∈ Finset.range pp.length,
      γ.getD k 0 * algebraMap ℚ Cc ((pp.getD k ([], [])).1.getD u 0) := fun u hu ↦ by
    rw [← hβtD u hu, hγc u]
  have hlGu : Gu.length = U.length := by simp [hGu, hEE]
  rw [hout]
  have hgetD : ∀ k < pp.length, (pp.map F').getD k ([], zc Fc us (m + 1)) = F' (pp.getD k ([], [])) :=
    fun k hk ↦ getD_map' _ pp ([], []) _ hk
  have hlen : (pp.map F').length = pp.length := List.length_map _
  -- the coefficients
  have hcoef : ∀ i, c.getD i 0 = ∑ k ∈ Finset.range (pp.map F').length,
      γ.getD k 0 * algebraMap ℚ Cc (((pp.map F').getD k ([], zc Fc us (m + 1))).1.getD i 0) := by
    intro i
    rw [hlen]
    have e : ∀ k ∈ Finset.range pp.length, γ.getD k 0 * algebraMap ℚ Cc
        (((pp.map F').getD k ([], zc Fc us (m + 1))).1.getD i 0) = γ.getD k 0 *
          algebraMap ℚ Cc ((vcomb n (pp.getD k ([], [])).1 EE).getD i 0) := fun k hk ↦ by
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
    rw [T.sem_final m h, sem_lcombCode (T.MP (m + 1) h) (lcst Fc us (m + 1)) (T.sem_lcst (m + 1) h),
      zipWith_sum_getD (fun (q : ℚ) (a : LC (m + 1)) ↦ ((q : ℚ) : T.F (m + 1)) *
        (T.MP (m + 1) h).sem a) 0 (zc Fc us (m + 1)) (by simp), hlGu, add_left_inj]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    have hu' := Finset.mem_range.mp hu
    rw [hGu, getD_map' _ EE [] (zc Fc us (m + 1)) (by simpa [hEE] using hu'), T.sem_Gu m h W]
    refine congrArg _ (Finset.sum_congr rfl fun i hi ↦ ?_)
    rw [hEE, getD_map' _ U [] [] hu', getD_vecOf, if_pos (Finset.mem_range.mp hi)]
  have htotal : z = ∑ k ∈ Finset.range (pp.map F').length, algebraMap Cc (T.F (m + 1)) (γ.getD k 0) *
      M'.sem ((pp.map F').getD k ([], zc Fc us (m + 1))).2 := by
    rw [hlen]
    have e : ∀ k ∈ Finset.range pp.length, algebraMap Cc (T.F (m + 1)) (γ.getD k 0) *
        M'.sem ((pp.map F').getD k ([], zc Fc us (m + 1))).2 =
        algebraMap Cc (T.F (m + 1)) (γ.getD k 0) * (∑ u ∈ Finset.range U.length,
          (((pp.getD k ([], [])).1.getD u 0 : ℚ) : T.F (m + 1)) *
            ∑ i ∈ Finset.range n, (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) * gv i +
          T.phi m (GPoly.toPoly M (pp.getD k ([], [])).2)) := fun k hk ↦ by
      rw [hgetD k (Finset.mem_range.mp hk), hsemy k (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl e]
    simp only [mul_add, Finset.sum_add_distrib]
    have hphi : ∑ k ∈ Finset.range pp.length, algebraMap Cc (T.F (m + 1)) (γ.getD k 0) *
        T.phi m (GPoly.toPoly M (pp.getD k ([], [])).2) = T.phi m P := by
      rw [hγP, map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_mul, ← T.algebraMap_succ]
    rw [hphi, ← hZP', hG]
    have hG' : ∑ i ∈ Finset.range n, algebraMap Cc (T.F (m + 1)) (c.getD i 0) * gv i =
        ∑ k ∈ Finset.range pp.length, algebraMap Cc (T.F (m + 1)) (γ.getD k 0) *
          ∑ u ∈ Finset.range U.length, (((pp.getD k ([], [])).1.getD u 0 : ℚ) : T.F (m + 1)) *
            ∑ i ∈ Finset.range n, (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) * gv i := by
      exact reassemble (algebraMap Cc (T.F (m + 1))) n U.length pp.length
        (fun u i ↦ (U.getD u []).getD i 0) (fun k u ↦ (pp.getD k ([], [])).1.getD u 0)
        (fun i ↦ c.getD i 0) (fun u ↦ β.getD u 0) (fun k ↦ γ.getD k 0) gv hβc hβu
    rw [hG']
    ring
  rw [← htotal, sub_self, map_zero]

/-- **Parametric exact integration at every level**: sound and complete in every realization
whose generators below `m` are transcendental. -/
theorem lex_spec (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) :
    ∀ (m : ℕ) (h : T.Tr m) (W : List (LC m)),
      T.PLSound m h W (lex Fc us m W) ∧ T.PLComplete m h W (lex Fc us m W)
  | 0, h, W => T.lex_zero hmon hdeg h W
  | m + 1, h, W =>
    have IH := fun W' ↦ lex_spec hmon hdeg m (fun i hi ↦ h i (by omega)) W'
    ⟨T.paramLim_succ_sound m h IH W,
      T.paramLim_succ_complete m h (T.eta_not_deriv m (h m (Nat.lt_succ_self m))) IH W⟩

end LTower

end Curves.LT
