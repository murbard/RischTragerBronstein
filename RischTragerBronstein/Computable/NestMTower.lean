import RischTragerBronstein.Computable.NestM
import RischTragerBronstein.Computable.NestPTower

/-!
# Mixed towers with nested data inside one differential field

`NestMTower Kc E ks`: `x ∈ E` with `x′ = 1` and `t₀, t₁, … ∈ E`, each a primitive
`tₘ′ = evN m ηₘ` or an exponential `tₘ′ = (evN m aₘ)′ tₘ`, the data being values of codes of level
`m` (so they may involve the previous generators). `Kc ⊇` all constants of `E`. The levels
`F m`, their derivations and the models of the codes are as for `NestTower`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP

variable (Kc : Type*) {E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc]
variable [Differential E] [DifferentialAlgebra Kc E] [CharZero Kc]

/-- The derivative of the level-`m` generator. -/
noncomputable def kder (x : E) (ts : ℕ → E) (m : ℕ) : KindN m → E
  | .prim η => evN Kc x ts m η
  | .exp a => (evN Kc x ts m a)′ * ts m

variable (E) in
/-- **A mixed tower with nested data** inside `E`. -/
structure NestMTower (ks : (m : ℕ) → KindN m) where
  x : E
  ts : ℕ → E
  hC : ∀ c : Kc, c′ = 0
  hx : x′ = 1
  ht : ∀ m, (ts m)′ = kder Kc x ts m (ks m)
  hts0 : ∀ m (a : Code (m + 1)), ks m = .exp a → ts m ≠ 0
  hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)

lemma oneC_succM (ks : (m : ℕ) → KindN m) : ∀ m : ℕ, oneC (m + 1) = (opsM ks m).one
  | 0 => rfl
  | m + 1 => by
    change ([oneC (m + 1)], [oneC (m + 1)]) = ([(opsM ks m).one], [(opsM ks m).one])
    rw [oneC_succM ks m]

namespace NestMTower

variable {Kc} {ks : (m : ℕ) → KindN m} (T : NestMTower Kc E ks)

/-- The levels `F m = Kc(x, t₀, …, t_{m-1})`. -/
def F (T : NestMTower Kc E ks) : ℕ → IntermediateField Kc E
  | 0 => Kc⟮T.x⟯
  | m + 1 => (IntermediateField.adjoin (F T m) {T.ts m}).restrictScalars Kc

lemma mem_F_succ {m : ℕ} {z : E} :
    z ∈ T.F (m + 1) ↔ z ∈ IntermediateField.adjoin (T.F m) {T.ts m} := Iff.rfl

lemma le_succ (m : ℕ) : T.F m ≤ T.F (m + 1) := fun z hz ↦
  (IntermediateField.adjoin (T.F m) {T.ts m}).algebraMap_mem (⟨z, hz⟩ : T.F m)

lemma F_mono {m k : ℕ} (h : m ≤ k) : T.F m ≤ T.F k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (T.le_succ _)

lemma ts_mem (m : ℕ) : T.ts m ∈ T.F (m + 1) :=
  (T.mem_F_succ).mpr (mem_adjoin_simple_self (T.F m) (T.ts m))

lemma aeval_mem_F0 (P : Kc[X]) : aeval T.x P ∈ T.F 0 := by
  let _ := algebraAdjoinSimple (F := Kc) T.x
  rw [← algebraMap_adjoinSimple T.x P]
  exact (algebraMap Kc[X] Kc⟮T.x⟯ P).2

lemma evP_mem (m : ℕ) (hm : ∀ q, evN Kc T.x T.ts m q ∈ T.F m) (p : GPoly (Code (m + 1))) :
    evP Kc T.x T.ts m p ∈ T.F (m + 1) := by
  induction p with
  | nil => exact zero_mem _
  | cons a p ih =>
    exact add_mem (T.le_succ m (hm a)) (mul_mem (T.ts_mem m) ih)

lemma evN_mem : ∀ (m : ℕ) (q : Code (m + 1)), evN Kc T.x T.ts m q ∈ T.F m
  | 0, q => div_mem (T.aeval_mem_F0 _) (T.aeval_mem_F0 _)
  | m + 1, q => div_mem (T.evP_mem m (evN_mem m) _) (T.evP_mem m (evN_mem m) _)

/-- The value of a code of level `m`, in `F m`. -/
noncomputable def valN (m : ℕ) (q : Code (m + 1)) : T.F m := ⟨evN Kc T.x T.ts m q, T.evN_mem m q⟩

/-- The derivation polynomial of `F m [tₘ]` (`X′ = ηₘ` or `X′ = aₘ′ X`), given the derivation
of `F m`. -/
noncomputable def wPolyAux (m : ℕ) (hd : DerivClosed (T.F m)) : (T.F m)[X] :=
  letI := differentialOfDerivClosed hd
  match ks m with
  | .prim η => C (T.valN m η)
  | .exp a => C (T.valN m a)′ * X

lemma deriv_ts_aux (m : ℕ) (hd : DerivClosed (T.F m)) :
    (T.ts m)′ = aeval (T.ts m) (T.wPolyAux m hd) := by
  rw [T.ht m, wPolyAux]
  cases ks m with
  | prim η => rw [aeval_C]; rfl
  | exp a => rw [map_mul, aeval_C, aeval_X]; rfl

/-- Every level is closed under the derivation. -/
theorem derivClosed : ∀ m, DerivClosed (T.F m)
  | 0 => derivClosed_adjoin_simple T.x 1 (by rw [T.hx, map_one])
  | m + 1 => by
    letI := differentialOfDerivClosed (derivClosed m)
    letI := differentialAlgebra_of_derivClosed (derivClosed m)
    exact derivClosed_adjoin_simple (F := T.F m) (T.ts m) (T.wPolyAux m (derivClosed m))
      (T.deriv_ts_aux m _)

noncomputable instance instDifferentialF (m : ℕ) : Differential (T.F m) :=
  differentialOfDerivClosed (T.derivClosed m)

instance instDifferentialAlgebraF (m : ℕ) : DifferentialAlgebra (T.F m) E :=
  differentialAlgebra_of_derivClosed (T.derivClosed m)

lemma coe_deriv {m : ℕ} (z : T.F m) : ((z′ : T.F m) : E) = (z : E)′ := rfl

/-- The derivation polynomial of `F m [tₘ]`. -/
noncomputable def wPoly (m : ℕ) : (T.F m)[X] := T.wPolyAux m (T.derivClosed m)

lemma deriv_ts_aeval (m : ℕ) : (T.ts m)′ = aeval (T.ts m) (T.wPoly m) := T.deriv_ts_aux m _

lemma wPoly_prim {m : ℕ} {η : Code (m + 1)} (hk : ks m = .prim η) :
    T.wPoly m = C (T.valN m η) := by
  rw [wPoly, wPolyAux]
  split <;> simp_all

lemma wPoly_exp {m : ℕ} {a : Code (m + 1)} (hk : ks m = .exp a) :
    T.wPoly m = C (T.valN m a)′ * X := by
  rw [wPoly, wPolyAux]
  split <;> simp_all

instance instCharZeroF (m : ℕ) : CharZero (T.F m) :=
  charZero_of_injective_algebraMap (algebraMap Kc (T.F m)).injective

lemma transcendental_x : Transcendental Kc T.x :=
  transcendental_of_deriv_ne_zero T.hC (by rw [T.hx]; exact one_ne_zero)

noncomputable instance instAlgebraF0 : Algebra Kc[X] (T.F 0) := algebraAdjoinSimple (F := Kc) T.x

instance instIsFractionRingF0 : IsFractionRing Kc[X] (T.F 0) :=
  isFractionRing_adjoin_simple T.x T.transcendental_x

/-- `Kc[X] → F 0`, `X ↦ x`. -/
noncomputable def phi0 : Kc[X] →+* T.F 0 := algebraMap Kc[X] (T.F 0)

lemma coe_phi0 (P : Kc[X]) : ((T.phi0 P : T.F 0) : E) = aeval T.x P :=
  algebraMap_adjoinSimple T.x P

lemma phi0_injective : Function.Injective T.phi0 := IsFractionRing.injective Kc[X] (T.F 0)

/-- `F m[X] → F (m + 1)`, `X ↦ tₘ`. -/
noncomputable def phi (m : ℕ) : (T.F m)[X] →+* T.F (m + 1) :=
  eval₂RingHom (IntermediateField.inclusion (T.le_succ m)).toRingHom ⟨T.ts m, T.ts_mem m⟩

lemma coe_phi (m : ℕ) (P : (T.F m)[X]) : ((T.phi m P : T.F (m + 1)) : E) = aeval (T.ts m) P := by
  rw [phi, coe_eval₂RingHom, aeval_def]
  change (T.F (m + 1)).val.toRingHom _ = _
  rw [hom_eval₂]
  rfl

lemma phi_injective {m : ℕ} (htr : Transcendental (T.F m) (T.ts m)) :
    Function.Injective (T.phi m) := fun P Q h ↦ by
  have h' := congrArg (fun z : T.F (m + 1) ↦ (z : E)) h
  simp only [coe_phi] at h'
  exact transcendental_iff_injective.mp htr h'

lemma deriv_phi0 (P : Kc[X]) : (T.phi0 P)′ = T.phi0 (implicitDeriv 1 P) := by
  apply Subtype.ext
  rw [coe_deriv, coe_phi0, coe_phi0]
  exact deriv_aeval_eq_implicitDeriv T.x 1 (by rw [T.hx, map_one]) P

lemma deriv_phi (m : ℕ) (P : (T.F m)[X]) :
    (T.phi m P)′ = T.phi m (implicitDeriv (T.wPoly m) P) := by
  apply Subtype.ext
  rw [coe_deriv, coe_phi, coe_phi]
  exact deriv_aeval_eq_implicitDeriv (T.ts m) (T.wPoly m) (T.deriv_ts_aeval m) P

/-! ### The models -/

/-- The model of `ℚ(x)` in `F 0 = Kc(x)`. -/
noncomputable def model0 : CField (Code 1) (T.F 0) (opsM ks 0) :=
  ((CField.ofHom (algebraMap ℚ Kc) T.hC).monomialVia [1] T.phi0
    (fun p hp ↦ T.phi0_injective (hp.trans (map_zero _).symm))
    (fun P ↦ by
      rw [T.deriv_phi0]
      congr 2
      rw [toPoly_ofHom']
      simp [CPoly.toPoly])).normalizeBy CPoly.normCoeff fun q ↦ by
    change T.phi0 _ / T.phi0 _ = T.phi0 _ / T.phi0 _
    simp only [toPoly_ofHom']
    exact CPoly.normCoeff_spec (T.phi0.comp (mapRingHom (algebraMap ℚ Kc)))
      (T.phi0_injective.comp (Polynomial.map_injective _ (algebraMap ℚ Kc).injective)) q

lemma sem_model0 (q : Code 1) : ((T.model0.sem q : T.F 0) : E) = evN Kc T.x T.ts 0 q := by
  change ((T.phi0 _ / T.phi0 _ : T.F 0) : E) = _
  rw [IntermediateField.coe_div, coe_phi0, coe_phi0, toPoly_ofHom', toPoly_ofHom']
  rfl

/-- Transcendence of the generators below level `m`. -/
abbrev Tr (m : ℕ) : Prop := ∀ i < m, Transcendental (T.F i) (T.ts i)

lemma aeval_toPoly {m : ℕ} (M : CField (Code (m + 1)) (T.F m) (opsM ks m))
    (hM : ∀ q, ((M.sem q : T.F m) : E) = evN Kc T.x T.ts m q) (p : GPoly (Code (m + 1))) :
    aeval (T.ts m) (GPoly.toPoly M p) = evP Kc T.x T.ts m p := by
  induction p with
  | nil => simp [evP]
  | cons a p ih =>
    rw [GPoly.toPoly_cons, map_add, map_mul, aeval_C, aeval_X, ih]
    simp only [evP, List.foldr_cons]
    rw [← hM a]
    rfl

/-- The models, agreeing with the evaluation. -/
noncomputable def MPs : (m : ℕ) → T.Tr m →
    {M : CField (Code (m + 1)) (T.F m) (opsM ks m) //
      ∀ q, ((M.sem q : T.F m) : E) = evN Kc T.x T.ts m q}
  | 0, _ => ⟨T.model0, T.sem_model0⟩
  | m + 1, h =>
    let M := (MPs m fun i hi ↦ h i (by omega)).1
    have hM := (MPs m fun i hi ↦ h i (by omega)).2
    have hw : GPoly.toPoly M (wK (opsM ks m) (ks m)) = T.wPoly m := by
      rw [wPoly, wPolyAux]
      cases ks m with
      | prim η =>
        simp only [wK, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero]
        congr 1
        exact Subtype.ext (hM _)
      | exp a =>
        simp only [wK, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, M.sem_zero,
          M.sem_deriv, C_0, zero_add]
        rw [mul_comm, show M.sem a = T.valN m a from Subtype.ext (hM a)]
    ⟨M.monomialVia (wK (opsM ks m) (ks m)) (T.phi m)
      (fun p hp ↦ T.phi_injective (h m (by omega)) (hp.trans (map_zero _).symm))
      (fun P ↦ by rw [hw]; exact T.deriv_phi m P), fun q ↦ by
        change ((T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) :
          T.F (m + 1)) : E) = _
        rw [IntermediateField.coe_div, coe_phi, coe_phi, T.aeval_toPoly M hM, T.aeval_toPoly M hM]
        rfl⟩

/-- **The model of `Kₘ = F m`.** -/
noncomputable def MP (m : ℕ) (h : T.Tr m) : CField (Code (m + 1)) (T.F m) (opsM ks m) :=
  (T.MPs m h).1

lemma sem_MP (m : ℕ) (h : T.Tr m) (q : Code (m + 1)) :
    (((T.MP m h).sem q : T.F m) : E) = evN Kc T.x T.ts m q := (T.MPs m h).2 q

lemma sem_MP_F (m : ℕ) (h : T.Tr m) (q : Code (m + 1)) : (T.MP m h).sem q = T.valN m q :=
  Subtype.ext (T.sem_MP m h q)

lemma sem_MP_succ (m : ℕ) (h : T.Tr (m + 1)) (q : Code (m + 2)) :
    (T.MP (m + 1) h).sem q =
      T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) q.1) /
        T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) q.2) := rfl

lemma toPoly_wK (m : ℕ) (h : T.Tr m) :
    GPoly.toPoly (T.MP m h) (wK (opsM ks m) (ks m)) = T.wPoly m := by
  rw [wPoly, wPolyAux]
  cases ks m with
  | prim η => rw [wK, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, T.sem_MP_F]
  | exp a =>
    simp only [wK, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, (T.MP m h).sem_zero,
      (T.MP m h).sem_deriv, C_0, zero_add, T.sem_MP_F]
    rw [mul_comm]

end NestMTower

end Tower.NestM
