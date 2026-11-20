import RischTragerBronstein.Computable.MixN
import RischTragerBronstein.Computable.PrimNTower

/-!
# Mixed towers inside one differential field

`MixTower Kc E ks`: `x ∈ E` with `x′ = 1` and generators `tₘ ∈ E`, each a primitive
(`tₘ′ = ηₘ(x)`) or an exponential (`tₘ′ = bₘ(x) tₘ`, `bₘ ∈ ℚ(x)`, `tₘ ≠ 0`), `Kc ⊇` all constants of `E`.
The levels `F m = Kc(x, t₀, …, t_{m-1})` and the models of the codes are as for `PrimTower`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.MixN

open Tower.PrimN

lemma oneC_succ' (ks : List Kind) : ∀ m : ℕ, oneC (m + 1) = (opsM ks m).one
  | 0 => rfl
  | m + 1 => by
    change ([oneC (m + 1)], [oneC (m + 1)]) = ([(opsM ks m).one], [(opsM ks m).one])
    rw [oneC_succ' ks m]

lemma opsM_succ (ks : List Kind) (m : ℕ) : opsM ks (m + 1) = (opsM ks m).monomial (wK ks m) :=
  rfl

variable (Kc : Type*) {E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc]
variable [Differential E] [DifferentialAlgebra Kc E] [CharZero Kc]

/-- The derivative of `tₘ` prescribed by its kind. -/
noncomputable def tsDeriv (x : E) (k : Kind) (t : E) : E :=
  match k with
  | .prim η => evx Kc x η
  | .exp b => evx Kc x b * t

variable (E) in
/-- **A mixed tower** of primitives and exponentials over `Kc(x)`. -/
structure MixTower (ks : List Kind) where
  x : E
  ts : ℕ → E
  hC : ∀ c : Kc, c′ = 0
  hx : x′ = 1
  ht : ∀ m, (ts m)′ = tsDeriv Kc x (kind ks m) (ts m)
  hts0 : ∀ m b, kind ks m = .exp b → ts m ≠ 0
  hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)

namespace MixTower

variable {Kc} {ks : List Kind} (T : MixTower Kc E ks)

/-- The levels `F m = Kc(x, t₀, …, t_{m-1})`. -/
def F (T : MixTower Kc E ks) : ℕ → IntermediateField Kc E
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

lemma x_mem (m : ℕ) : T.x ∈ T.F m := T.F_mono (Nat.zero_le m) (mem_adjoin_simple_self Kc T.x)

lemma ts_mem (m : ℕ) : T.ts m ∈ T.F (m + 1) :=
  (T.mem_F_succ).mpr (mem_adjoin_simple_self (T.F m) (T.ts m))

lemma aeval_mem_F0 (P : Kc[X]) : aeval T.x P ∈ T.F 0 := by
  let _ := algebraAdjoinSimple (F := Kc) T.x
  rw [← algebraMap_adjoinSimple T.x P]
  exact (algebraMap Kc[X] Kc⟮T.x⟯ P).2

lemma evx_mem (q : GFrac ℚ) : evx Kc T.x q ∈ T.F 0 :=
  div_mem (T.aeval_mem_F0 _) (T.aeval_mem_F0 _)

/-- An element of `ℚ(x)` in `F k`. -/
noncomputable def ratF (k : ℕ) (q : GFrac ℚ) : T.F k :=
  ⟨evx Kc T.x q, T.F_mono (Nat.zero_le k) (T.evx_mem _)⟩

/-- The derivation of `F m [tₘ]`: `X′ = η` or `X′ = b X`. -/
noncomputable def wPoly (m : ℕ) : (T.F m)[X] :=
  match kind ks m with
  | .prim η => C (T.ratF m η)
  | .exp b => C (T.ratF m b) * X

lemma deriv_ts_aeval (m : ℕ) : (T.ts m)′ = aeval (T.ts m) (T.wPoly m) := by
  rw [T.ht m]
  unfold tsDeriv wPoly
  cases kind ks m with
  | prim η => rw [aeval_C]; rfl
  | exp b => rw [map_mul, aeval_C, aeval_X]; rfl

/-- Every level is closed under the derivation. -/
theorem derivClosed : ∀ m, DerivClosed (T.F m)
  | 0 => derivClosed_adjoin_simple T.x 1 (by rw [T.hx, map_one])
  | m + 1 => by
    letI := differentialOfDerivClosed (derivClosed m)
    letI := differentialAlgebra_of_derivClosed (derivClosed m)
    exact derivClosed_adjoin_simple (F := T.F m) (T.ts m) (T.wPoly m) (T.deriv_ts_aeval m)

noncomputable instance instDifferentialF (m : ℕ) : Differential (T.F m) :=
  differentialOfDerivClosed (T.derivClosed m)

instance instDifferentialAlgebraF (m : ℕ) : DifferentialAlgebra (T.F m) E :=
  differentialAlgebra_of_derivClosed (T.derivClosed m)

lemma coe_deriv {m : ℕ} (z : T.F m) : ((z′ : T.F m) : E) = (z : E)′ := rfl

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

lemma sem_model0 (q : Code 1) :
    ((T.model0.sem q : T.F 0) : E) = evx Kc T.x q := by
  change ((T.phi0 _ / T.phi0 _ : T.F 0) : E) = _
  rw [IntermediateField.coe_div, coe_phi0, coe_phi0, toPoly_ofHom', toPoly_ofHom']
  rfl

/-- Transcendence of the generators below level `m`. -/
abbrev Tr (m : ℕ) : Prop := ∀ i < m, Transcendental (T.F i) (T.ts i)

lemma toPoly_wK_of {m : ℕ} (M : CField (Code (m + 1)) (T.F m) (opsM ks m))
    (hM : ∀ q, ((M.sem (lift m q) : T.F m) : E) = evx Kc T.x q) :
    GPoly.toPoly M (wK ks m) = T.wPoly m := by
  have hl : ∀ q, M.sem (lift m q) = T.ratF m q := fun q ↦ Subtype.ext (hM q)
  rw [wK, wK', wPoly]
  cases kind ks m with
  | prim η => simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, hl]
  | exp b =>
    simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, M.sem_zero, C_0,
      zero_add]
    rw [mul_comm]
    congr 2
    exact hl _

/-- The models, with the value of the lifted codes of `ℚ(x)`. -/
noncomputable def MPs : (m : ℕ) → T.Tr m →
    {M : CField (Code (m + 1)) (T.F m) (opsM ks m) //
      ∀ q, ((M.sem (lift m q) : T.F m) : E) = evx Kc T.x q}
  | 0, _ => ⟨T.model0, T.sem_model0⟩
  | m + 1, h =>
    let M := (MPs m fun i hi ↦ h i (by omega)).1
    have hM := (MPs m fun i hi ↦ h i (by omega)).2
    have hw : GPoly.toPoly M (wK ks m) = T.wPoly m := T.toPoly_wK_of M hM
    ⟨M.monomialVia (wK ks m) (T.phi m)
      (fun p hp ↦ T.phi_injective (h m (by omega)) (hp.trans (map_zero _).symm))
      (fun P ↦ by rw [hw]; exact T.deriv_phi m P), fun q ↦ by
        change ((T.phi m (GPoly.toPoly M [lift m q]) / T.phi m (GPoly.toPoly M [oneC (m + 1)]) :
          T.F (m + 1)) : E) = _
        rw [oneC_succ' ks m]
        simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, M.sem_one, map_one,
          coe_phi, aeval_C, div_one]
        exact hM q⟩

/-- **The model of `Kₘ = F m`.** -/
noncomputable def MP (m : ℕ) (h : T.Tr m) : CField (Code (m + 1)) (T.F m) (opsM ks m) :=
  (T.MPs m h).1

lemma sem_lift (m : ℕ) (h : T.Tr m) (q : GFrac ℚ) :
    (((T.MP m h).sem (lift m q) : T.F m) : E) = evx Kc T.x q := (T.MPs m h).2 q

lemma sem_lift_F (m : ℕ) (h : T.Tr m) (q : GFrac ℚ) :
    (T.MP m h).sem (lift m q) = T.ratF m q := Subtype.ext (T.sem_lift m h q)

lemma sem_MP_succ (m : ℕ) (h : T.Tr (m + 1)) (q : Code (m + 2)) :
    (T.MP (m + 1) h).sem q =
      T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) q.1) /
        T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) q.2) := rfl

lemma toPoly_wK (m : ℕ) (h : T.Tr m) : GPoly.toPoly (T.MP m h) (wK ks m) = T.wPoly m :=
  T.toPoly_wK_of _ (T.sem_lift m h)

end MixTower

end Tower.MixN
