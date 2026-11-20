import RischTragerBronstein.Mixed.LTTransfer

/-!
# Mixed towers of logarithms and exponentials over a curve: codes, realizations, levels, models

As `LTTower` (towers of logarithms over a curve), with each level a logarithm-type primitive
`tₘ′ = ηₘ` (`KindC.prim ηₘ`) or an exponential `tₘ′ = aₘ′ tₘ` (`KindC.exp aₘ`), the data `ηₘ, aₘ`
codes of level `m`. The realizations have a height `n`: the generators from `n` on are `0`.

* `KindC m`, `wKC` (the derivation polynomial of `tₘ`), `MO ks m` (operations);
* `MTower`: a realization in `L` over constants `Cc`, of height `n`;
* `F m`, `derivClosed`, and the models `MP m` (transcendence below `m`) agreeing with `evL`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT

/-- The kind of the level-`m` generator. -/
inductive KindC (m : ℕ) where
  | prim (η : LC m)
  | exp (a : LC m)

/-- The derivative of `tₘ`, as a polynomial in `tₘ`. -/
def wKC {m : ℕ} (O : COps (LC m)) : KindC m → GPoly (LC m)
  | .prim η => [η]
  | .exp a => [O.zero, O.deriv a]

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The operations of level `m`. -/
def MO : (m : ℕ) → COps (LC m)
  | 0 => curveOps Fc
  | m + 1 => (MO m).monomial (wKC (MO m) (ks m))

lemma MO_succ (m : ℕ) : MO Fc ks (m + 1) = (MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)) :=
  rfl

section Eval

variable {L : Type*} [Field L] [Differential L]

/-- The derivative of the level-`m` generator, given the values of the codes. -/
noncomputable def kderC (ev : LC m → L) (t : L) : KindC m → L
  | .prim η => ev η
  | .exp a => (ev a)′ * t

end Eval

universe u

/-- **A realization of the mixed tower of height `n`** in `L`, over the constants `Cc`. -/
structure MTower (Cc L : Type u) [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
    [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] where
  S : CurveData Cc L
  hC : ∀ c : Cc, c′ = 0
  hx : S.x′ = 1
  hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Cc))
  n : ℕ
  ts : ℕ → L
  hts : ∀ m, n ≤ m → ts m = 0
  ht : ∀ m < n, (ts m)′ = kderC (evL (cM hC S hx Fc hSF).sem ts m) (ts m) (ks m)
  hts0 : ∀ m < n, ∀ a, ks m = .exp a → ts m ≠ 0
  hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap Cc L)

namespace MTower

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

/-- The value of a code. -/
noncomputable abbrev ev (m : ℕ) (q : LC m) : L := evL (cM T.hC T.S T.hx Fc T.hSF).sem T.ts m q

/-- The value of a polynomial over level `m` at `tₘ`. -/
noncomputable abbrev evP (m : ℕ) (p : GPoly (LC m)) : L :=
  evPL (cM T.hC T.S T.hx Fc T.hSF).sem T.ts m p

/-- The levels `F 0 = Cc(x, y)`, `F (m + 1) = F m (tₘ)`. -/
noncomputable def F : ℕ → IntermediateField Cc L
  | 0 => cF T.S
  | m + 1 => (IntermediateField.adjoin (F m) {T.ts m}).restrictScalars Cc

lemma mem_F_succ {m : ℕ} {z : L} :
    z ∈ T.F (m + 1) ↔ z ∈ IntermediateField.adjoin (T.F m) {T.ts m} := Iff.rfl

lemma le_succ (m : ℕ) : T.F m ≤ T.F (m + 1) := fun z hz ↦
  (IntermediateField.adjoin (T.F m) {T.ts m}).algebraMap_mem (⟨z, hz⟩ : T.F m)

lemma F_mono {m k : ℕ} (h : m ≤ k) : T.F m ≤ T.F k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (T.le_succ _)

lemma ts_mem (m : ℕ) : T.ts m ∈ T.F (m + 1) :=
  (T.mem_F_succ).mpr (mem_adjoin_simple_self (T.F m) (T.ts m))

lemma const_mem (m : ℕ) (c : Cc) : algebraMap Cc L c ∈ T.F m := (T.F m).algebraMap_mem c

lemma evP_mem (m : ℕ) (hm : ∀ q, T.ev m q ∈ T.F m) (p : GPoly (LC m)) :
    T.evP m p ∈ T.F (m + 1) := by
  induction p with
  | nil => exact zero_mem _
  | cons a p ih =>
    exact add_mem (T.le_succ m (hm a)) (mul_mem (T.ts_mem m) ih)

lemma ev_mem : ∀ (m : ℕ) (q : LC m), T.ev m q ∈ T.F m
  | 0, q => sem_mem_cF T.hC T.S T.hx Fc T.hSF q
  | m + 1, q => div_mem (T.evP_mem m (ev_mem m) _) (T.evP_mem m (ev_mem m) _)

/-- The value of a code of level `m`, in `F m`. -/
noncomputable def val (m : ℕ) (q : LC m) : T.F m := ⟨T.ev m q, T.ev_mem m q⟩

/-- The derivation polynomial of `F m [tₘ]`, given the derivation of `F m` (`0` above the
height). -/
noncomputable def wPolyAux (m : ℕ) (hd : DerivClosed (T.F m)) : (T.F m)[X] :=
  letI := differentialOfDerivClosed hd
  if m < T.n then
    match ks m with
    | .prim η => C (T.val m η)
    | .exp a => C (T.val m a)′ * X
  else 0

lemma deriv_ts_aux (m : ℕ) (hd : DerivClosed (T.F m)) :
    (T.ts m)′ = aeval (T.ts m) (T.wPolyAux m hd) := by
  rw [wPolyAux]
  split_ifs with hm
  · have := T.ht m hm
    revert this
    cases ks m with
    | prim η => intro h; rw [h, aeval_C]; rfl
    | exp a => intro h; rw [h, map_mul, aeval_C, aeval_X]; rfl
  · rw [T.hts m (not_lt.mp hm), Derivation.map_zero, map_zero]

/-- Every level is closed under the derivation. -/
theorem derivClosed : ∀ m, DerivClosed (T.F m)
  | 0 => cF_derivClosed T.hC T.S T.hx
  | m + 1 => by
    letI := differentialOfDerivClosed (derivClosed m)
    letI := differentialAlgebra_of_derivClosed (derivClosed m)
    exact derivClosed_adjoin_simple (F := T.F m) (T.ts m) (T.wPolyAux m (derivClosed m))
      (T.deriv_ts_aux m _)

noncomputable instance instDifferentialF (m : ℕ) : Differential (T.F m) :=
  differentialOfDerivClosed (T.derivClosed m)

instance instDifferentialAlgebraF (m : ℕ) : DifferentialAlgebra (T.F m) L :=
  differentialAlgebra_of_derivClosed (T.derivClosed m)

lemma coe_deriv {m : ℕ} (z : T.F m) : ((z′ : T.F m) : L) = (z : L)′ := rfl

instance instCharZeroF (m : ℕ) : CharZero (T.F m) :=
  charZero_of_injective_algebraMap (algebraMap Cc (T.F m)).injective

instance instDifferentialAlgebraCcF (m : ℕ) : DifferentialAlgebra Cc (T.F m) :=
  ⟨fun c ↦ Subtype.ext (by
    rw [coe_deriv]
    exact deriv_algebraMap (A := Cc) (B := L) c)⟩

/-- The derivation polynomial of `F m [tₘ]`. -/
noncomputable def wPoly (m : ℕ) : (T.F m)[X] := T.wPolyAux m (T.derivClosed m)

lemma deriv_ts_aeval (m : ℕ) : (T.ts m)′ = aeval (T.ts m) (T.wPoly m) := T.deriv_ts_aux m _

lemma wPoly_prim {m : ℕ} (hm : m < T.n) {η : LC m} (hk : ks m = .prim η) :
    T.wPoly m = C (T.val m η) := by
  rw [wPoly, wPolyAux, if_pos hm]
  split <;> simp_all

lemma wPoly_exp {m : ℕ} (hm : m < T.n) {a : LC m} (hk : ks m = .exp a) :
    T.wPoly m = C (T.val m a)′ * X := by
  rw [wPoly, wPolyAux, if_pos hm]
  split <;> simp_all

/-- A transcendental generator is below the height. -/
lemma lt_of_transcendental {m : ℕ} (htr : Transcendental (T.F m) (T.ts m)) : m < T.n := by
  by_contra h
  apply htr
  rw [T.hts m (not_lt.mp h)]
  exact isAlgebraic_zero

/-- `F m[X] → F (m + 1)`, `X ↦ tₘ`. -/
noncomputable def phi (m : ℕ) : (T.F m)[X] →+* T.F (m + 1) :=
  eval₂RingHom (IntermediateField.inclusion (T.le_succ m)).toRingHom ⟨T.ts m, T.ts_mem m⟩

lemma coe_phi (m : ℕ) (P : (T.F m)[X]) : ((T.phi m P : T.F (m + 1)) : L) = aeval (T.ts m) P := by
  rw [phi, coe_eval₂RingHom, aeval_def]
  change (T.F (m + 1)).val.toRingHom _ = _
  rw [hom_eval₂]
  rfl

lemma phi_injective {m : ℕ} (htr : Transcendental (T.F m) (T.ts m)) :
    Function.Injective (T.phi m) := fun P Q h ↦ by
  have h' := congrArg (fun z : T.F (m + 1) ↦ (z : L)) h
  simp only [coe_phi] at h'
  exact transcendental_iff_injective.mp htr h'

lemma deriv_phi (m : ℕ) (P : (T.F m)[X]) :
    (T.phi m P)′ = T.phi m (implicitDeriv (T.wPoly m) P) := by
  apply Subtype.ext
  rw [coe_deriv, coe_phi, coe_phi]
  exact deriv_aeval_eq_implicitDeriv (T.ts m) (T.wPoly m) (T.deriv_ts_aeval m) P

lemma phi_C (m : ℕ) (z : T.F m) : T.phi m (C z) = IntermediateField.inclusion (T.le_succ m) z :=
  Subtype.ext (by rw [coe_phi, aeval_C]; rfl)

lemma algebraMap_succ (m : ℕ) (c : Cc) :
    algebraMap Cc (T.F (m + 1)) c = T.phi m (C (algebraMap Cc (T.F m) c)) := by
  rw [T.phi_C]; rfl

/-! ### The models -/

/-- Transcendence of the generators below level `m`. -/
abbrev Tr (m : ℕ) : Prop := ∀ i < m, Transcendental (T.F i) (T.ts i)

lemma Tr.of_succ {m : ℕ} (h : T.Tr (m + 1)) : T.Tr m := fun i hi ↦ h i (by omega)

lemma aeval_toPoly {m : ℕ} (M : CField (LC m) (T.F m) (MO Fc ks m))
    (hM : ∀ q, ((M.sem q : T.F m) : L) = T.ev m q) (p : GPoly (LC m)) :
    aeval (T.ts m) (GPoly.toPoly M p) = T.evP m p := by
  induction p with
  | nil => simp [evP, evPL]
  | cons a p ih =>
    rw [GPoly.toPoly_cons, map_add, map_mul, aeval_C, aeval_X, ih]
    simp only [evP, evPL, List.foldr_cons]
    congr 1
    exact hM a

lemma toPoly_wKC_aux {m : ℕ} (hm : m < T.n) (M : CField (LC m) (T.F m) (MO Fc ks m))
    (hM : ∀ q, ((M.sem q : T.F m) : L) = T.ev m q) :
    GPoly.toPoly M (wKC (MO Fc ks m) (ks m)) = T.wPoly m := by
  have hv : ∀ q, M.sem q = T.val m q := fun q ↦ Subtype.ext (hM q)
  rw [wPoly, wPolyAux, if_pos hm]
  cases ks m with
  | prim η =>
    simp only [wKC, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, hv]
  | exp a =>
    simp only [wKC, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, M.sem_zero,
      M.sem_deriv, C_0, zero_add, hv]
    rw [mul_comm]

/-- The model of the curve codes in `F 0`. -/
noncomputable def model0 : CField (LC 0) (T.F 0) (MO Fc ks 0) :=
  cMF T.hC T.S T.hx Fc T.hSF

/-- The models, agreeing with the evaluation. -/
noncomputable def MPs : (m : ℕ) → T.Tr m →
    {M : CField (LC m) (T.F m) (MO Fc ks m) // ∀ q, ((M.sem q : T.F m) : L) = T.ev m q}
  | 0, _ => ⟨T.model0, fun _ ↦ rfl⟩
  | m + 1, h =>
    let M := (MPs m h.of_succ).1
    have hM := (MPs m h.of_succ).2
    have hw : GPoly.toPoly M (wKC (MO Fc ks m) (ks m)) = T.wPoly m :=
      T.toPoly_wKC_aux (T.lt_of_transcendental (h m (by omega))) M hM
    ⟨M.monomialVia (wKC (MO Fc ks m) (ks m)) (T.phi m)
      (fun p hp ↦ T.phi_injective (h m (by omega)) (hp.trans (map_zero _).symm))
      (fun P ↦ by rw [hw]; exact T.deriv_phi m P), fun q ↦ by
        change ((T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) :
          T.F (m + 1)) : L) = _
        rw [IntermediateField.coe_div, coe_phi, coe_phi, T.aeval_toPoly M hM, T.aeval_toPoly M hM]
        rfl⟩

/-- **The model of `F m`.** -/
noncomputable def MP (m : ℕ) (h : T.Tr m) : CField (LC m) (T.F m) (MO Fc ks m) :=
  (T.MPs m h).1

lemma sem_MP (m : ℕ) (h : T.Tr m) (q : LC m) :
    (((T.MP m h).sem q : T.F m) : L) = T.ev m q := (T.MPs m h).2 q

lemma sem_MP_F (m : ℕ) (h : T.Tr m) (q : LC m) : (T.MP m h).sem q = T.val m q :=
  Subtype.ext (T.sem_MP m h q)

lemma sem_MP_succ (m : ℕ) (h : T.Tr (m + 1)) (q : LC (m + 1)) :
    (T.MP (m + 1) h).sem q =
      T.phi m (GPoly.toPoly (T.MP m h.of_succ) q.1) /
        T.phi m (GPoly.toPoly (T.MP m h.of_succ) q.2) := rfl

lemma toPoly_wKC (m : ℕ) (h : T.Tr m) (hm : m < T.n) :
    GPoly.toPoly (T.MP m h) (wKC (MO Fc ks m) (ks m)) = T.wPoly m :=
  T.toPoly_wKC_aux hm (T.MP m h) (T.sem_MP m h)

end MTower

end Curves.MT
