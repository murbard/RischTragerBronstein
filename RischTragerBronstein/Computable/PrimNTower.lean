import RischTragerBronstein.Computable.PrimN
import RischTragerBronstein.Computable.CFracVia
import RischTragerBronstein.Computable.ModelIn
import RischTragerBronstein.Liouville.SimpleTranscendental
import RischTragerBronstein.Liouville.Transcendence

/-!
# Towers of `n` primitives inside one differential field

`PrimTower Kc E ηs`: a differential field `E`, a subfield `Kc` containing **all** constants of `E`,
`x ∈ E` with `x′ = 1` and `t₀, t₁, … ∈ E` with `tₘ′ = ηₘ(x)` (the `ηₘ ∈ ℚ(x)` given by codes).
The levels `F m = C(x, t₀, …, t_{m-1})` are intermediate fields of `E`, each closed under the
derivation (`derivClosed`), hence differential fields (global instances).

When each `tₘ` is transcendental over `F m`, the codes `Code (m + 1)` with the operations
`opsP ηs m` have a model in `F m` (`MP`): the base `C(x)` through `aeval x`, and each step through
`aeval tₘ` (`CField.monomialVia`), so that everything happens inside the one field `E`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.PrimN

lemma oneC_succ (ηs : List (Code 1)) : ∀ m : ℕ, oneC (m + 1) = (opsP ηs m).one
  | 0 => rfl
  | m + 1 => by
    change ([oneC (m + 1)], [oneC (m + 1)]) = ([(opsP ηs m).one], [(opsP ηs m).one])
    rw [oneC_succ ηs m]

variable (Kc : Type*) {E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc]

lemma toPoly_ofHom' {R S : Type*} [Field R] [DecidableEq R] [Field S] [Differential S]
    (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (l : List R) :
    GPoly.toPoly (CField.ofHom ι h0) l = (CPoly.toPoly l).map ι := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [GPoly.toPoly_cons, CPoly.toPoly_cons, ih, Polynomial.map_add, Polynomial.map_mul, map_C,
      map_X]
    rfl

/-- The value of a code of `ℚ(x)` at `x ∈ E`. -/
noncomputable def evx (x : E) (q : GFrac ℚ) : E :=
  aeval x ((CPoly.toPoly q.1).map (algebraMap ℚ Kc)) /
    aeval x ((CPoly.toPoly q.2).map (algebraMap ℚ Kc))

variable (E) in
/-- **A tower of primitives** `C(x)(t₀)(t₁)…` inside `E`. -/
structure PrimTower (ηs : List (Code 1)) where
  x : E
  ts : ℕ → E
  hC : ∀ c : Kc, c′ = 0
  hx : x′ = 1
  ht : ∀ m, (ts m)′ = evx Kc x (eta ηs m)
  hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)

namespace PrimTower

variable {Kc} {ηs : List (Code 1)} (T : PrimTower Kc E ηs)

/-- The levels `F m = C(x, t₀, …, t_{m-1})`. -/
def F (T : PrimTower Kc E ηs) : ℕ → IntermediateField Kc E
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

lemma evx_mem (q : Code 1) : evx Kc T.x q ∈ T.F 0 :=
  div_mem (T.aeval_mem_F0 _) (T.aeval_mem_F0 _)

/-- `ηₘ` as an element of `F k`. -/
noncomputable def etaF (k m : ℕ) : T.F k := ⟨evx Kc T.x (eta ηs m), T.F_mono (Nat.zero_le k) (T.evx_mem _)⟩

/-- Every level is closed under the derivation. -/
theorem derivClosed : ∀ m, DerivClosed (T.F m)
  | 0 => derivClosed_adjoin_simple T.x 1 (by rw [T.hx, map_one])
  | m + 1 => by
    letI := differentialOfDerivClosed (derivClosed m)
    letI := differentialAlgebra_of_derivClosed (derivClosed m)
    exact derivClosed_adjoin_simple (F := T.F m) (T.ts m) (C (T.etaF m m))
      (by rw [aeval_C, T.ht]; rfl)

noncomputable instance instDifferentialF (m : ℕ) : Differential (T.F m) :=
  differentialOfDerivClosed (T.derivClosed m)

instance instDifferentialAlgebraF (m : ℕ) : DifferentialAlgebra (T.F m) E :=
  differentialAlgebra_of_derivClosed (T.derivClosed m)

lemma coe_deriv {m : ℕ} (z : T.F m) : ((z′ : T.F m) : E) = (z : E)′ := rfl

instance instCharZeroF (m : ℕ) : CharZero (T.F m) :=
  charZero_of_injective_algebraMap (algebraMap Kc (T.F m)).injective

lemma deriv_ts_F (m : ℕ) : (T.ts m)′ = algebraMap (T.F m) E (T.etaF m m) := T.ht m

/-- `x` is transcendental over the constants. -/
lemma transcendental_x : Transcendental Kc T.x :=
  transcendental_of_deriv_ne_zero T.hC (by rw [T.hx]; exact one_ne_zero)

/-- `Kc[X]` acts on `F 0 = Kc(x)` through `X ↦ x`. -/
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
    (T.phi m P)′ = T.phi m (implicitDeriv (C (T.etaF m m)) P) := by
  apply Subtype.ext
  rw [coe_deriv, coe_phi, coe_phi]
  exact deriv_aeval_eq_implicitDeriv (T.ts m) (C (T.etaF m m)) (by rw [aeval_C]; exact T.ht m) P

/-! ### The models -/

/-- The model of `ℚ(x)` in `F 0 = C(x)`. -/
noncomputable def model0 : CField (Code 1) (T.F 0) (opsP ηs 0) :=
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

/-- The models, with the value of the lifted codes of `ℚ(x)`. -/
noncomputable def MPs : (m : ℕ) → T.Tr m →
    {M : CField (Code (m + 1)) (T.F m) (opsP ηs m) //
      ∀ q, ((M.sem (lift m q) : T.F m) : E) = evx Kc T.x q}
  | 0, _ => ⟨T.model0, T.sem_model0⟩
  | m + 1, h =>
    let M := (MPs m fun i hi ↦ h i (by omega)).1
    have hM := (MPs m fun i hi ↦ h i (by omega)).2
    have hw : GPoly.toPoly M [lift m (eta ηs m)] = C (T.etaF m m) := by
      rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero]
      congr 1
      exact Subtype.ext (hM _)
    ⟨M.monomialVia [lift m (eta ηs m)] (T.phi m)
      (fun p hp ↦ T.phi_injective (h m (by omega)) (hp.trans (map_zero _).symm))
      (fun P ↦ by rw [hw]; exact T.deriv_phi m P), fun q ↦ by
        change ((T.phi m (GPoly.toPoly M [lift m q]) / T.phi m (GPoly.toPoly M [oneC (m + 1)]) :
          T.F (m + 1)) : E) = _
        rw [oneC_succ ηs m]
        simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, M.sem_one, map_one,
          coe_phi, aeval_C, div_one]
        exact hM q⟩

/-- **The model of `Kₘ = F m`.** -/
noncomputable def MP (m : ℕ) (h : T.Tr m) : CField (Code (m + 1)) (T.F m) (opsP ηs m) :=
  (T.MPs m h).1

lemma sem_lift (m : ℕ) (h : T.Tr m) (q : Code 1) :
    (((T.MP m h).sem (lift m q) : T.F m) : E) = evx Kc T.x q := (T.MPs m h).2 q

lemma sem_lift_eta (m : ℕ) (h : T.Tr m) : (T.MP m h).sem (lift m (eta ηs m)) = T.etaF m m :=
  Subtype.ext (T.sem_lift m h _)

lemma MP_succ (m : ℕ) (h : T.Tr (m + 1)) :
    T.MP (m + 1) h = (T.MP m fun i hi ↦ h i (by omega)).monomialVia [lift m (eta ηs m)] (T.phi m)
      (fun p hp ↦ T.phi_injective (h m (by omega)) (hp.trans (map_zero _).symm))
      (fun P ↦ by
        rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, T.sem_lift_eta]
        exact T.deriv_phi m P) := rfl

lemma sem_MP_succ (m : ℕ) (h : T.Tr (m + 1)) (q : Code (m + 2)) :
    (T.MP (m + 1) h).sem q =
      T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) q.1) /
        T.phi m (GPoly.toPoly (T.MP m fun i hi ↦ h i (by omega)) q.2) := rfl

lemma toPoly_wP (m : ℕ) (h : T.Tr m) :
    GPoly.toPoly (T.MP m h) (wP ηs m) = C (T.etaF m m) := by
  rw [wP, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, T.sem_lift_eta]

end PrimTower

end Tower.PrimN
