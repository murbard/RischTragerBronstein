import RischTragerBronstein.Computable.NestXBase

/-!
# Mixed towers: parametric limited integration over a logarithmic level

At a level `m + 1` with `ks m = .prim η` (`t′ = η`): every weight is Hermite-reduced,
`wᵢ = gᵢ′ + Pᵢ + rᵢ / sᵢ`; a solution `z′ = ∑ cᵢ wᵢ` forces `∑ cᵢ rᵢ / sᵢ = 0` (a constant
system at level `m + 1`) and `z - ∑ cᵢ gᵢ` is a polynomial `Q` with `Q′ = ∑ cᵢ Pᵢ` (the
parametric polynomial problem, solved with limited integration one level down).
`primLimStep_spec`: the step is sound and complete (`LimSpec`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP Tower.NestX

/-- The Hermite data of a (cleaned) weight at level `m + 1`. -/
def hermWP (ks : (m : ℕ) → KindN m) (m : ℕ) (w : Code (m + 2)) :
    GPoly.HermiteResult (Code (m + 1)) :=
  let w' := cleanG (opsM ks m) w
  GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) w'.1 w'.2

/-- The simple parts of the weights, as codes of level `m + 1`. -/
def simpleCodesP (ks : (m : ℕ) → KindN m) (m : ℕ) (W : List (Code (m + 2))) :
    List (Code (m + 2)) :=
  (List.zip ((W.map (hermWP ks m)).map fun h ↦ GPoly.divMod (opsM ks m) h.b h.s)
    (W.map (hermWP ks m))).map fun p ↦ ((p.1.2, p.2.s) : Code (m + 2))

/-- The Hermite part `gᵢ` of a weight, as a code. -/
def gCodeP (ks : (m : ℕ) → KindN m) (m : ℕ) (w : Code (m + 2)) : Code (m + 2) :=
  (((hermWP ks m w).gn, (hermWP ks m w).gd) : Code (m + 2))

/-- The polynomial part `Pᵢ` of a weight. -/
def pPartP (ks : (m : ℕ) → KindN m) (m : ℕ) (w : Code (m + 2)) : GPoly (Code (m + 1)) :=
  (GPoly.divMod (opsM ks m) (hermWP ks m w).b (hermWP ks m w).s).1

/-- The default code of level `m + 1`. -/
abbrev zP (ks : (m : ℕ) → KindN m) (m : ℕ) : Code (m + 2) := (opsM ks (m + 1)).zero

lemma primLimStep_eq (ks : (m : ℕ) → KindN m) (m : ℕ) (η : Code (m + 1))
    (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1))) (W : List (Code (m + 2))) :
    primLimStep ks m η lim W =
      (paramPoly (opsM ks m) (cstN m) η lim
        (((consys ks (m + 1) (simpleCodesP ks m W)).map (NestTower.vecOf W.length)).map fun e ↦
          lcombGP (opsM ks m) (cstN m) e
            (((W.map (hermWP ks m)).map fun h ↦ GPoly.divMod (opsM ks m) h.b h.s).map
              Prod.fst))).map fun r ↦
        (vcomb W.length r.1 ((consys ks (m + 1) (simpleCodesP ks m W)).map (NestTower.vecOf W.length)),
          (opsM ks (m + 1)).add (lcombCode (opsM ks (m + 1)) (cstN (m + 1))
            (vcomb W.length r.1 ((consys ks (m + 1) (simpleCodesP ks m W)).map (NestTower.vecOf W.length)))
            ((W.map (hermWP ks m)).map fun h ↦ ((h.gn, h.gd) : Code (m + 2))))
            ((r.2, [(opsM ks m).one]) : Code (m + 2))) := rfl

lemma length_simpleCodesP (ks : (m : ℕ) → KindN m) (m : ℕ) (W : List (Code (m + 2))) :
    (simpleCodesP ks m W).length = W.length :=
  NestTower.len_zip_map (hermWP ks m) (fun h ↦ GPoly.divMod (opsM ks m) h.b h.s)
    (fun p ↦ ((p.1.2, p.2.s) : Code (m + 2))) W

lemma getD_simpleCodesP (ks : (m : ℕ) → KindN m) (m : ℕ) (W : List (Code (m + 2))) {i : ℕ}
    (hi : i < W.length) :
    (simpleCodesP ks m W).getD i (zP ks m) =
      (((GPoly.divMod (opsM ks m) (hermWP ks m (W.getD i (zP ks m))).b
        (hermWP ks m (W.getD i (zP ks m))).s).2,
        (hermWP ks m (W.getD i (zP ks m))).s) : Code (m + 2)) :=
  NestTower.getD_zip_map (hermWP ks m) (fun h ↦ GPoly.divMod (opsM ks m) h.b h.s)
    (fun p ↦ ((p.1.2, p.2.s) : Code (m + 2))) W (zP ks m) (zP ks m) hi

/-- Recombining through `vcomb` over the vectors of a basis. -/
lemma vcomb_vecOf_sum {K : Type*} [Field K] [CharZero K] (n : ℕ) (δ : List ℚ)
    (U : List (CPoly ℚ)) (g : ℕ → K) :
    ∑ i ∈ Finset.range n, (((vcomb n δ (U.map (NestTower.vecOf n))).getD i 0 : ℚ) : K) * g i =
      ∑ u ∈ Finset.range U.length, ((δ.getD u 0 : ℚ) : K) *
        ∑ i ∈ Finset.range n, (((U.getD u []).getD i 0 : ℚ) : K) * g i := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [getD_vcomb, if_pos (Finset.mem_range.mp hi), List.length_map]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [NestTower.getD_map' _ U [] [] (Finset.mem_range.mp hu), NestTower.getD_vecOf,
    if_pos (Finset.mem_range.mp hi)]
  ring

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

lemma deriv_sum_ratCastP {m : ℕ} (n : ℕ) (q : ℕ → ℚ) (a : ℕ → T.F m) :
    (∑ i ∈ Finset.range n, (q i : T.F m) * a i)′ = ∑ i ∈ Finset.range n, (q i : T.F m) * (a i)′ := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Derivation.leibniz, T.deriv_ratCast, smul_eq_mul, smul_eq_mul, mul_zero, add_zero, mul_comm]

lemma deriv_sum_KcP {m : ℕ} (n : ℕ) (q : ℕ → Kc) (a : ℕ → T.F m) :
    (∑ i ∈ Finset.range n, algebraMap Kc (T.F m) (q i) * a i)′ =
      ∑ i ∈ Finset.range n, algebraMap Kc (T.F m) (q i) * (a i)′ := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Derivation.leibniz, T.deriv_algebraMap_Kc, smul_eq_mul, smul_eq_mul, mul_zero, add_zero,
    mul_comm]

lemma coe_phi_sumP (m : ℕ) (n : ℕ) (a : ℕ → Kc) (p : ℕ → (T.F m)[X]) :
    ((∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (a i) * T.phi m (p i) : T.F (m + 1)) : E) =
      aeval (T.ts m) (∑ i ∈ Finset.range n, C (algebraMap Kc (T.F m) (a i)) * p i) := by
  rw [map_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, aeval_C, coe_phi]
  rfl

lemma coe_phi_div_sumP (m : ℕ) (n : ℕ) (a : ℕ → Kc) (p q : ℕ → (T.F m)[X]) :
    ((∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (a i) *
      (T.phi m (p i) / T.phi m (q i)) : T.F (m + 1)) : E) =
      (((List.range n).map fun i ↦ (C (algebraMap Kc (T.F m) (a i)) * p i, q i)).map
        fun r ↦ aeval (T.ts m) r.1 / aeval (T.ts m) r.2).sum := by
  rw [List.map_map, NestTower.list_sum_map_range]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Function.comp_apply, coe_phi, map_mul, aeval_C]
  rw [show algebraMap (T.F m) E (algebraMap Kc (T.F m) (a i)) = algebraMap Kc E (a i) from rfl]
  ring

section Step

variable (m : ℕ) (h : T.Tr (m + 1)) {η : Code (m + 1)} (hk : ks m = .prim η)

include h hk in
/-- **Sums of proper fractions are not derivatives**, at a logarithmic level. -/
lemma proper_step_sumP (A : (T.F m)[X])
    (l : List ((T.F m)[X] × (T.F m)[X])) (hsq : ∀ p ∈ l, Squarefree p.2)
    (hdeg : ∀ p ∈ l, p.1.degree < p.2.degree) (z : E) (hz : z ∈ T.F (m + 1))
    (hzd : z′ = aeval (T.ts m) A + (l.map fun p ↦ aeval (T.ts m) p.1 / aeval (T.ts m) p.2).sum) :
    (l.map fun p ↦ aeval (T.ts m) p.1 / aeval (T.ts m) p.2).sum = 0 ∧
      ∃ P : (T.F m)[X], z = aeval (T.ts m) P ∧ implicitDeriv (T.wPoly m) P = A := by
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
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
    (fun p hp ↦ T.normal_prim m htr hk p hp) A l hsq hdeg ⟨z, (T.mem_F_succ).mp hz⟩
    (Subtype.ext (by
      change z′ = _
      rw [hzd, IntermediateField.coe_add, hcoe, hsum]))
  refine ⟨?_, P, ?_, hPd⟩
  · have := congrArg Subtype.val hb
    rw [hsum] at this
    exact this
  · have := congrArg Subtype.val hP
    rw [hcoe] at this
    exact this

include hk in
/-- **The decomposition of a weight** `w = g′ + P + r / s` at a logarithmic level. -/
lemma weight_decompP (w : Code (m + 2)) :
    (T.MP (m + 1) h).sem w =
      ((T.MP (m + 1) h).sem (gCodeP ks m w))′ +
        T.phi m (GPoly.toPoly (T.MX m h) (pPartP ks m w)) +
        T.phi m (GPoly.toPoly (T.MX m h)
          (GPoly.divMod (opsM ks m) (hermWP ks m w).b (hermWP ks m w).s).2) /
        T.phi m (GPoly.toPoly (T.MX m h) (hermWP ks m w).s) ∧
    Squarefree (GPoly.toPoly (T.MX m h) (hermWP ks m w).s) ∧
    (GPoly.toPoly (T.MX m h)
      (GPoly.divMod (opsM ks m) (hermWP ks m w).b (hermWP ks m w).s).2).degree <
      (GPoly.toPoly (T.MX m h) (hermWP ks m w).s).degree := by
  set M := T.MX m h with hM
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injective htr
  obtain ⟨w', hw'⟩ : ∃ w' : GPoly (Code (m + 1)) × GPoly (Code (m + 1)),
      w' = cleanG (opsM ks m) w := ⟨_, rfl⟩
  have hsemw : (T.MP (m + 1) h).sem w = T.phi m (GPoly.toPoly M w'.1) /
      T.phi m (GPoly.toPoly M w'.2) := by
    rw [hw', ← T.semX_cleanG m h w]
    rfl
  have hD : GPoly.toPoly M w'.2 ≠ 0 := by
    intro h0
    apply T.σX_cleanG_ne m h w
    rw [← hw']
    change T.phi m (GPoly.toPoly M w'.2) = 0
    rw [h0, map_zero]
  obtain ⟨hval, hsq⟩ := T.hermite_value m (fun i hi ↦ h i (by omega)) htr w'.1 w'.2 hD
    (fun p hp _ ↦ T.normal_prim m htr hk p hp)
  simp only [show T.MP m (fun i hi ↦ h i (by omega)) = M from rfl] at hval hsq
  have hherm : hermWP ks m w = GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) w'.1 w'.2 := by
    rw [hw']; rfl
  simp only [gCodeP, pPartP]
  rw [hherm]
  refine ⟨?_, hsq, GPoly.divMod_degree_lt M _ _ hsq.ne_zero⟩
  have hdm := GPoly.divMod_spec M (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) w'.1 w'.2).b
    (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) w'.1 w'.2).s
  have hs0 : T.phi m (GPoly.toPoly M
      (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) w'.1 w'.2).s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
  have hg : (T.MP (m + 1) h).sem
      (((GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) w'.1 w'.2).gn,
      (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) w'.1 w'.2).gd) : Code (m + 2)) =
      T.phi m (GPoly.toPoly M (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) w'.1 w'.2).gn) /
        T.phi m (GPoly.toPoly M
          (GPoly.hermite (opsM ks m) (wK (opsM ks m) (ks m)) w'.1 w'.2).gd) := rfl
  rw [hsemw, hval, hg, hdm, map_add, map_mul]
  field_simp
  ring

lemma sem_GP (W : List (Code (m + 2))) (e : List ℚ) :
    (T.MP (m + 1) h).sem (lcombCode (opsM ks (m + 1)) (cstN (m + 1)) e
      ((W.map (hermWP ks m)).map fun h ↦ ((h.gn, h.gd) : Code (m + 2)))) =
      ∑ i ∈ Finset.range W.length, ((e.getD i 0 : ℚ) : T.F (m + 1)) *
        (T.MP (m + 1) h).sem (gCodeP ks m (W.getD i (zP ks m))) := by
  rw [sem_lcombCode (T.MP (m + 1) h) (cstN (m + 1)) (T.sem_cstN (m + 1) h),
    zipWith_sum_getD (fun (q : ℚ) (a : Code (m + 2)) ↦ ((q : ℚ) : T.F (m + 1)) *
      (T.MP (m + 1) h).sem a) 0 (zP ks m) (by simp)]
  refine Finset.sum_congr (congrArg Finset.range (NestTower.len_map_map _ _ W)) fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  congr 2
  exact NestTower.getD_map_map (hermWP ks m) (fun h ↦ ((h.gn, h.gd) : Code (m + 2))) W
    (zP ks m) (zP ks m) hi'

lemma sem_lcomb_G (W : List (Code (m + 2))) (Gl : List (Code (m + 2)))
    (hGl : Gl = (W.map (hermWP ks m)).map fun h ↦ ((h.gn, h.gd) : Code (m + 2))) (e : List ℚ) :
    (T.MP (m + 1) h).sem (lcombCode (opsM ks (m + 1)) (cstN (m + 1)) e Gl) =
      ∑ i ∈ Finset.range W.length, ((e.getD i 0 : ℚ) : T.F (m + 1)) *
        (T.MP (m + 1) h).sem (gCodeP ks m (W.getD i (zP ks m))) := by
  subst hGl
  exact T.sem_GP m h W e

lemma toPoly_PuP (W : List (Code (m + 2))) (e : List ℚ) :
    GPoly.toPoly (T.MX m h) (lcombGP (opsM ks m) (cstN m) e
      (((W.map (hermWP ks m)).map fun h ↦ GPoly.divMod (opsM ks m) h.b h.s).map Prod.fst)) =
      ∑ i ∈ Finset.range W.length, C ((e.getD i 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MX m h) (pPartP ks m (W.getD i (zP ks m))) := by
  rw [toPoly_lcombGP (T.MX m h) (cstN m) (T.sem_cstX m h),
    zipWith_sum_getD (fun (q : ℚ) (p : GPoly (Code (m + 1))) ↦ C ((q : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) p) 0 [] (by simp)]
  refine Finset.sum_congr (by simp) fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  congr 2
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getD_eq_getElem _ _ hi']
  simp [pPartP]

lemma sem_finalP (a : Code (m + 2)) (Q : GPoly (Code (m + 1))) :
    (T.MP (m + 1) h).sem ((opsM ks (m + 1)).add a ((Q, [(opsM ks m).one]) : Code (m + 2))) =
      (T.MP (m + 1) h).sem a + T.phi m (GPoly.toPoly (T.MX m h) Q) := by
  refine ((T.MP (m + 1) h).sem_add a _).trans ?_
  congr 1
  exact T.semX_poly m h Q

/-- The relation given by a basis vector of the constant system on the simple parts. -/
lemma rel_simpleP (W : List (Code (m + 2))) (u : CPoly ℚ)
    (hu : u ∈ consys ks (m + 1) (simpleCodesP ks m W)) :
    ∑ i ∈ Finset.range W.length, ((u.getD i 0 : ℚ) : T.F (m + 1)) *
      (T.MP (m + 1) h).sem ((simpleCodesP ks m W).getD i (zP ks m)) = 0 := by
  have := T.consys_sound (m + 1) h (simpleCodesP ks m W) u hu
  rw [NestTower.zipWith_sum_range _ 0 (zP ks m) _ _ (by simp)] at this
  rw [← this]
  refine Finset.sum_congr (by simp [length_simpleCodesP]) fun i hi ↦ ?_
  have hi' : i < W.length := by simpa [length_simpleCodesP] using hi
  rw [NestTower.getD_range_map (fun j ↦ algebraMap ℚ Kc (u.getD j 0)) 0
    (by rw [length_simpleCodesP]; exact hi'), T.algebraMap_ratX]

/-- The value of a simple part. -/
lemma sem_simpleP (W : List (Code (m + 2))) {i : ℕ} (hi : i < W.length) :
    (T.MP (m + 1) h).sem ((simpleCodesP ks m W).getD i (zP ks m)) =
      T.phi m (GPoly.toPoly (T.MX m h)
        (GPoly.divMod (opsM ks m) (hermWP ks m (W.getD i (zP ks m))).b
          (hermWP ks m (W.getD i (zP ks m))).s).2) /
      T.phi m (GPoly.toPoly (T.MX m h) (hermWP ks m (W.getD i (zP ks m))).s) := by
  rw [getD_simpleCodesP ks m W hi]
  rfl

include hk in
set_option maxHeartbeats 1600000 in
/-- **Soundness of the logarithmic step.** -/
theorem primLimStep_sound (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hlim : LimSpec (algebraMap Kc (T.F m)) (T.MX m h) lim) (W : List (Code (m + 2))) :
    ∀ r ∈ primLimStep ks m η lim W,
      ((T.MP (m + 1) h).sem r.2)′ = sQ (T.MP (m + 1) h) r.1 W := by
  set M := T.MX m h with hM
  have hconstK : ∀ y : T.F m, y′ = 0 → ∃ κ : Kc, y = algebraMap Kc (T.F m) κ := fun y hy ↦
    T.const_F y hy
  intro r' hr'
  rw [primLimStep_eq] at hr'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  set n := W.length with hn
  set U := consys ks (m + 1) (simpleCodesP ks m W) with hU
  set EE := U.map (NestTower.vecOf n) with hEE
  set Pu := EE.map fun e ↦ lcombGP (opsM ks m) (cstN m) e
    (((W.map (hermWP ks m)).map fun h ↦ GPoly.divMod (opsM ks m) h.b h.s).map Prod.fst) with hPu
  have hsound := paramPoly_sound (algebraMap Kc (T.F m)) η lim
    (T.sem_cstX m h) hlim hconstK (fun q ↦ T.algebraMap_ratX q) Pu r hr
  set gv : ℕ → T.F (m + 1) := fun i ↦ (T.MP (m + 1) h).sem (gCodeP ks m (W.getD i (zP ks m)))
    with hgv
  set pv : ℕ → T.F (m + 1) := fun i ↦ T.phi m (GPoly.toPoly M (pPartP ks m (W.getD i (zP ks m))))
    with hpv
  set sv : ℕ → T.F (m + 1) := fun i ↦ (T.MP (m + 1) h).sem ((simpleCodesP ks m W).getD i (zP ks m))
    with hsv
  have hdec : ∀ i < n, (T.MP (m + 1) h).sem (W.getD i (zP ks m)) = (gv i)′ + pv i + sv i := by
    intro i hi
    rw [(T.weight_decompP m h hk (W.getD i (zP ks m))).1]
    simp only [hsv]
    rw [T.sem_simpleP m h W hi]
  -- the polynomial part
  have hpoly : T.phi m (polySumQ M r.1 Pu) = ∑ u ∈ Finset.range U.length,
      ((r.1.getD u 0 : ℚ) : T.F (m + 1)) *
        ∑ i ∈ Finset.range n, (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) * pv i := by
    rw [polySumQ, map_sum, show Pu.length = U.length by simp [hPu, hEE]]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    have hu' := Finset.mem_range.mp hu
    rw [hPu, NestTower.getD_map' _ EE [] [] (by simpa [hEE] using hu'), T.toPoly_PuP m h W,
      map_mul, T.phi_C_ratX, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hEE, NestTower.getD_map' _ U [] [] hu', NestTower.getD_vecOf, if_pos (Finset.mem_range.mp hi),
      map_mul, T.phi_C_ratX]
  simp only
  rw [T.sem_finalP m h, map_add, T.sem_GP m h W, T.deriv_sum_ratCastP,
    T.deriv_phi_primX m h hk]
  change _ + T.phi m (Dη M η _) = _
  rw [hsound, hpoly, sQ]
  change ∑ i ∈ Finset.range n, _ * (gv i)′ + _ = ∑ i ∈ Finset.range n, _ * _
  rw [vcomb_vecOf_sum n r.1 U (fun i ↦ (gv i)′)]
  have hR : ∑ i ∈ Finset.range n, (((vcomb n r.1 EE).getD i 0 : ℚ) : T.F (m + 1)) *
      (T.MP (m + 1) h).sem (W.getD i (opsM ks (m + 1)).zero) =
      ∑ i ∈ Finset.range n, (((vcomb n r.1 EE).getD i 0 : ℚ) : T.F (m + 1)) *
        ((gv i)′ + pv i + sv i) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [hdec i (Finset.mem_range.mp hi)]
  rw [hR, vcomb_vecOf_sum n r.1 U, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hrel := T.rel_simpleP m h W (U.getD u []) (by
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hu)]; exact List.getElem_mem _)
  have e : ∑ i ∈ Finset.range n, (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) *
      ((gv i)′ + pv i + sv i) = ∑ i ∈ Finset.range n, (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) *
        (gv i)′ + ∑ i ∈ Finset.range n, (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) * pv i +
      ∑ i ∈ Finset.range n, (((U.getD u []).getD i 0 : ℚ) : T.F (m + 1)) * sv i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e, hrel]
  ring

include hk in
set_option maxHeartbeats 3200000 in
/-- **Parametric limited integration over a logarithmic level is sound and complete.** -/
theorem primLimStep_spec (hnd : ∀ y : T.F m, y′ ≠ T.ηX m h η)
    (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hlim : LimSpec (algebraMap Kc (T.F m)) (T.MX m h) lim) :
    LimSpec (algebraMap Kc (T.F (m + 1))) (T.MP (m + 1) h) (primLimStep ks m η lim) := by
  refine ⟨fun W r hr ↦ T.primLimStep_sound m h hk lim hlim W r hr, fun W c hc z hz ↦ ?_⟩
  set M := T.MX m h with hM
  set M' := T.MP (m + 1) h with hM'
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hconstK : ∀ y : T.F m, y′ = 0 → ∃ κ : Kc, y = algebraMap Kc (T.F m) κ := fun y hy ↦
    T.const_F y hy
  set n := W.length with hn
  set U := consys ks (m + 1) (simpleCodesP ks m W) with hU
  set EE := U.map (NestTower.vecOf n) with hEE
  set gv : ℕ → T.F (m + 1) := fun i ↦ M'.sem (gCodeP ks m (W.getD i (zP ks m))) with hgv
  set pv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (pPartP ks m (W.getD i (zP ks m))) with hpv
  set rv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (GPoly.divMod (opsM ks m)
    (hermWP ks m (W.getD i (zP ks m))).b (hermWP ks m (W.getD i (zP ks m))).s).2 with hrv
  set sv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (hermWP ks m (W.getD i (zP ks m))).s
    with hsv
  set G := ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) * gv i with hG
  -- the derivative of `z - G`
  have hZd : (z - G)′ = ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) *
      T.phi m (pv i) + ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) *
        (T.phi m (rv i) / T.phi m (sv i)) := by
    rw [map_sub, hz, hG, T.deriv_sum_KcP, sC, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(T.weight_decompP m h hk (W.getD i (zP ks m))).1]
    simp only [hgv, hpv, hrv, hsv, hM, hM']
    ring
  -- in `E`: the proper step
  set A := ∑ i ∈ Finset.range n, C (algebraMap Kc (T.F m) (c.getD i 0)) * pv i with hA
  set l := (List.range n).map fun i ↦ (C (algebraMap Kc (T.F m) (c.getD i 0)) * rv i, sv i)
    with hl
  have hZE : ((z - G : T.F (m + 1)) : E)′ = aeval (T.ts m) A +
      (l.map fun r ↦ aeval (T.ts m) r.1 / aeval (T.ts m) r.2).sum := by
    rw [← coe_deriv, hZd, IntermediateField.coe_add, T.coe_phi_sumP, T.coe_phi_div_sumP]
  obtain ⟨hsum0, P, hZP, hPd⟩ := T.proper_step_sumP m h hk A l
    (fun p hp ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact (T.weight_decompP m h hk (W.getD i (zP ks m))).2.1)
    (fun p hp ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _)
        (T.weight_decompP m h hk (W.getD i (zP ks m))).2.2)
    _ (z - G).2 hZE
  -- the simple parts cancel: the constant system at level `m + 1`
  have hsimple0 : ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) *
      (T.phi m (rv i) / T.phi m (sv i)) = 0 := by
    apply Subtype.ext
    rw [T.coe_phi_div_sumP, ← hl, hsum0]
    rfl
  have h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c * M'.sem v)
      ((List.range (simpleCodesP ks m W).length).map fun i ↦ c.getD i 0)
      (simpleCodesP ks m W)).sum = 0 := by
    rw [NestTower.zipWith_sum_range _ 0 (zP ks m) _ _ (by simp), ← hsimple0]
    refine Finset.sum_congr (by simp [length_simpleCodesP, hn]) fun i hi ↦ ?_
    have hi' : i < n := by simpa [length_simpleCodesP, hn] using hi
    rw [NestTower.getD_range_map (fun j ↦ c.getD j 0) 0
      (by rw [length_simpleCodesP]; exact hi'), T.sem_simpleP m h W hi']
  obtain ⟨β, hβl, hβ⟩ := T.consys_complete (m + 1) h (simpleCodesP ks m W) _ (by simp) h0
  have hβc : ∀ i < n, c.getD i 0 = ∑ u ∈ Finset.range U.length,
      β.getD u 0 * algebraMap ℚ Kc ((U.getD u []).getD i 0) := fun i hi ↦ by
    have := hβ i
    rw [NestTower.getD_range_map (fun j ↦ c.getD j 0) 0
      (by rw [length_simpleCodesP]; exact hi),
      NestTower.zipWith_sum_range _ 0 [] _ _ hβl, hβl] at this
    exact this
  -- the polynomial problem, in terms of `β`
  set Pu := EE.map fun e ↦ lcombGP (opsM ks m) (cstN m) e
    (((W.map (hermWP ks m)).map fun h ↦ GPoly.divMod (opsM ks m) h.b h.s).map Prod.fst)
    with hPu
  set βt := (List.range U.length).map fun u ↦ β.getD u 0 with hβt
  have hβtD : ∀ u < U.length, βt.getD u 0 = β.getD u 0 := fun u hu ↦
    NestTower.getD_range_map _ _ hu
  have hlPu : Pu.length = U.length := by simp [hPu, hEE]
  have hPoly : Dη M η P = polySumC (algebraMap Kc (T.F m)) M βt Pu := by
    rw [Dη, ← T.wPoly_eq_ηX m h hk, hPd, polySumC, hA]
    have e : ∀ u ∈ Finset.range Pu.length, C (algebraMap Kc (T.F m) (βt.getD u 0)) *
        GPoly.toPoly M (Pu.getD u []) = ∑ i ∈ Finset.range n,
          C (algebraMap Kc (T.F m) (β.getD u 0 * algebraMap ℚ Kc ((U.getD u []).getD i 0))) *
            pv i := fun u hu ↦ by
      have hu' : u < U.length := by rw [← hlPu]; exact Finset.mem_range.mp hu
      rw [hβtD u hu', hPu, NestTower.getD_map' _ EE [] [] (by simpa [hEE] using hu'),
        T.toPoly_PuP m h W, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [hEE, NestTower.getD_map' _ U [] [] hu', NestTower.getD_vecOf, if_pos (Finset.mem_range.mp hi),
        map_mul, T.algebraMap_ratX, C_mul, mul_assoc]
    rw [Finset.sum_congr rfl e, Finset.sum_comm, hlPu]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← hβc i (Finset.mem_range.mp hi)]
  obtain ⟨γ, hγc, hγP⟩ := paramPoly_complete (algebraMap Kc (T.F m)) η lim
    (T.sem_cstX m h) hlim hconstK (fun q ↦ T.algebraMap_ratX q) hnd Pu βt
    (fun u hu ↦ List.getD_eq_default _ _ (by simp [hβt, ← hlPu]; omega)) P hPoly
  -- assemble
  set pp := paramPoly (opsM ks m) (cstN m) η lim Pu with hpp
  set Gl : List (Code (m + 2)) := (W.map (hermWP ks m)).map fun h ↦ ((h.gn, h.gd) : Code (m + 2))
    with hGl
  set F' : List ℚ × GPoly (Code (m + 1)) → List ℚ × Code (m + 2) := fun r ↦
    (vcomb n r.1 EE, (opsM ks (m + 1)).add (lcombCode (opsM ks (m + 1)) (cstN (m + 1))
      (vcomb n r.1 EE) Gl) ((r.2, [(opsM ks m).one]) : Code (m + 2))) with hF'
  have hout : primLimStep ks m η lim W = pp.map F' := rfl
  have hβu : ∀ u < U.length, β.getD u 0 = ∑ k ∈ Finset.range pp.length,
      γ.getD k 0 * algebraMap ℚ Kc ((pp.getD k ([], [])).1.getD u 0) := fun u hu ↦ by
    rw [← hβtD u hu, hγc u]
  rw [hout]
  have hgetD : ∀ k < pp.length, (pp.map F').getD k ([], zP ks m) = F' (pp.getD k ([], [])) :=
    fun k hk ↦ NestTower.getD_map' _ pp ([], []) _ hk
  have hlen : (pp.map F').length = pp.length := List.length_map _
  -- the coefficients
  have hcoef : ∀ i, c.getD i 0 = ∑ k ∈ Finset.range (pp.map F').length,
      γ.getD k 0 * algebraMap ℚ Kc (((pp.map F').getD k ([], zP ks m)).1.getD i 0) := by
    intro i
    rw [hlen]
    have e : ∀ k ∈ Finset.range pp.length, γ.getD k 0 * algebraMap ℚ Kc
        (((pp.map F').getD k ([], zP ks m)).1.getD i 0) = γ.getD k 0 *
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
      rw [hEE, NestTower.getD_map' _ U [] [] hu', NestTower.getD_vecOf, if_pos hi]
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
    rw [T.sem_finalP m h, T.sem_lcomb_G m h W Gl hGl, vcomb_vecOf_sum n _ U gv]
  have htotal : z = ∑ k ∈ Finset.range (pp.map F').length,
      algebraMap Kc (T.F (m + 1)) (γ.getD k 0) * M'.sem ((pp.map F').getD k ([], zP ks m)).2 := by
    rw [hlen]
    have e : ∀ k ∈ Finset.range pp.length, algebraMap Kc (T.F (m + 1)) (γ.getD k 0) *
        M'.sem ((pp.map F').getD k ([], zP ks m)).2 =
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
      exact NestTower.reassemble (algebraMap Kc (T.F (m + 1))) n U.length pp.length
        (fun u i ↦ (U.getD u []).getD i 0) (fun k u ↦ (pp.getD k ([], [])).1.getD u 0)
        (fun i ↦ c.getD i 0) (fun u ↦ β.getD u 0) (fun k ↦ γ.getD k 0) gv hβc hβu
    rw [hG']
    ring
  rw [← htotal, sub_self, map_zero]

end Step

end NestMTower

end Tower.NestM
