import RischTragerBronstein.Mixed.LogCurveMain

/-!
# Towers of logarithms over a curve: codes, realizations, levels, models

Data (computable): a curve `Fc` over `ℚ` and, for every level `m`, the code `us m` of an element
`uₘ` of the level-`m` field; the tower is `F₀ = Kc(x, y)`, `Fₘ₊₁ = Fₘ(tₘ)`, `tₘ = log uₘ`.

* `LC m`: codes of level `m` (`LC 0` curve codes, `LC (m + 1)` fractions over `LC m`);
* `LO us m`: their operations (`tₘ′ = uₘ′ / uₘ`);
* `evL`: the value of a code in a field, given the curve model and the generators;
* `LTower`: a **realization** of the tower in a differential field `L` over constants `Cc`. The
  same codes are realized in the field of the integrand and in every elementary extension of it
  (over its own constants), which is how the Liouville arguments transfer;
* `F m`, `derivClosed`, and the models `MP m` (under transcendence of the generators below `m`)
  agreeing with `evL` (`sem_MP`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.LT

open CPoly Sup

/-! ### Codes and operations -/

/-- Codes of level `m`. -/
def LC : ℕ → Type
  | 0 => GPoly (GFrac ℚ)
  | m + 1 => GFrac (LC m)

/-- `u′ / u`. -/
def etaOf {α : Type} (O : COps α) (u : α) : α := O.mul (O.deriv u) (O.inv u)

/-- The operations of level `m`. -/
def LO (Fc : BPoly ℚ) (us : (m : ℕ) → LC m) : (m : ℕ) → COps (LC m)
  | 0 => curveOps Fc
  | m + 1 => (LO Fc us m).monomial [etaOf (LO Fc us m) (us m)]

/-- The code of `ηₘ = uₘ′ / uₘ`. -/
def etaC (Fc : BPoly ℚ) (us : (m : ℕ) → LC m) (m : ℕ) : LC m := etaOf (LO Fc us m) (us m)

lemma LO_succ (Fc : BPoly ℚ) (us : (m : ℕ) → LC m) (m : ℕ) :
    LO Fc us (m + 1) = (LO Fc us m).monomial [etaC Fc us m] := rfl

/-! ### Evaluation -/

section Eval

variable {L : Type*} [Field L] [Differential L]

/-- The value of a code of level `m`, given the values of the curve codes and the generators. -/
noncomputable def evL (M0 : LC 0 → L) (ts : ℕ → L) : (m : ℕ) → LC m → L
  | 0, q => M0 q
  | m + 1, q => (q.1.foldr (fun a acc ↦ evL M0 ts m a + ts m * acc) 0) /
      (q.2.foldr (fun a acc ↦ evL M0 ts m a + ts m * acc) 0)

/-- The value of a polynomial over level `m` at `tₘ`. -/
noncomputable def evPL (M0 : LC 0 → L) (ts : ℕ → L) (m : ℕ) (p : GPoly (LC m)) : L :=
  p.foldr (fun a acc ↦ evL M0 ts m a + ts m * acc) 0

lemma evL_succ (M0 : LC 0 → L) (ts : ℕ → L) (m : ℕ) (q : LC (m + 1)) :
    evL M0 ts (m + 1) q = evPL M0 ts m q.1 / evPL M0 ts m q.2 := rfl

/-- Evaluation commutes with ring maps. -/
lemma map_evL {L' : Type*} [Field L'] (j : L →+* L') (M0 : LC 0 → L) (M0' : LC 0 → L')
    (h0 : ∀ q, M0' q = j (M0 q)) (ts : ℕ → L) :
    ∀ (m : ℕ) (q : LC m), evL M0' (fun i ↦ j (ts i)) m q = j (evL M0 ts m q)
  | 0, q => h0 q
  | m + 1, q => by
    have hf : ∀ l : List (LC m),
        l.foldr (fun a acc ↦ evL M0' (fun i ↦ j (ts i)) m a + j (ts m) * acc) 0 =
          j (l.foldr (fun a acc ↦ evL M0 ts m a + ts m * acc) 0) := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih => rw [List.foldr_cons, List.foldr_cons, map_add, map_mul, ih,
          map_evL j M0 M0' h0 ts m a]
    simp only [evL, map_div₀, hf]

end Eval

/-! ### Realizations -/

universe u

variable (Fc : BPoly ℚ) (us : (m : ℕ) → LC m)

/-- **A realization of the log tower of height `n`** in `L`, over the constants `Cc`: a curve `S`
with equation `Fc`, and generators `tₘ` (`m < n`) with `tₘ′ = uₘ′ / uₘ` (`uₘ ≠ 0`); the generators
from `n` on are `0`, so the levels stop growing at `n`. All constants of `L` are in `Cc`. -/
structure LTower (Cc L : Type u) [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
    [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] where
  S : CurveData Cc L
  hC : ∀ c : Cc, c′ = 0
  hx : S.x′ = 1
  hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Cc))
  n : ℕ
  ts : ℕ → L
  hts : ∀ m, n ≤ m → ts m = 0
  hu0 : ∀ m < n, evL (cM hC S hx Fc hSF).sem ts m (us m) ≠ 0
  ht : ∀ m < n, (ts m)′ = logDeriv (evL (cM hC S hx Fc hSF).sem ts m (us m))
  hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap Cc L)

namespace LTower

variable {Fc us} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : LTower Fc us Cc L)

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

/-- Every level is closed under the derivation. -/
theorem derivClosed : ∀ m, DerivClosed (T.F m)
  | 0 => cF_derivClosed T.hC T.S T.hx
  | m + 1 => by
    letI := differentialOfDerivClosed (derivClosed m)
    letI := differentialAlgebra_of_derivClosed (derivClosed m)
    by_cases hm : m < T.n
    · have hη : logDeriv (T.ev m (us m)) ∈ T.F m := by
        rw [logDeriv]
        exact div_mem (derivClosed m _ (T.ev_mem m _)) (T.ev_mem m _)
      exact derivClosed_adjoin_simple (F := T.F m) (T.ts m) (C ⟨_, hη⟩)
        (by rw [aeval_C, T.ht m hm]; rfl)
    · exact derivClosed_adjoin_simple (F := T.F m) (T.ts m) 0
        (by rw [T.hts m (not_lt.mp hm), Derivation.map_zero, map_zero])

noncomputable instance instDifferentialF (m : ℕ) : Differential (T.F m) :=
  differentialOfDerivClosed (T.derivClosed m)

instance instDifferentialAlgebraF (m : ℕ) : DifferentialAlgebra (T.F m) L :=
  differentialAlgebra_of_derivClosed (T.derivClosed m)

lemma coe_deriv {m : ℕ} (z : T.F m) : ((z′ : T.F m) : L) = (z : L)′ := rfl

instance instCharZeroF (m : ℕ) : CharZero (T.F m) :=
  charZero_of_injective_algebraMap (algebraMap Cc (T.F m)).injective

/-- `ηₘ = uₘ′ / uₘ` in `F m`. -/
noncomputable def eta (m : ℕ) : T.F m :=
  ⟨logDeriv (T.ev m (us m)), by
    rw [logDeriv]; exact div_mem (T.derivClosed m _ (T.ev_mem m _)) (T.ev_mem m _)⟩

lemma coe_eta (m : ℕ) : ((T.eta m : T.F m) : L) = logDeriv (T.ev m (us m)) := rfl

lemma ht' {m : ℕ} (hm : m < T.n) : (T.ts m)′ = algebraMap (T.F m) L (T.eta m) := T.ht m hm

/-- The derivation of `F m [tₘ]`: `X′ = ηₘ` (below the height; `0` above). -/
noncomputable def wPoly (m : ℕ) : (T.F m)[X] := if m < T.n then C (T.eta m) else 0

lemma wPoly_of_lt {m : ℕ} (hm : m < T.n) : T.wPoly m = C (T.eta m) := if_pos hm

lemma deriv_ts_aeval (m : ℕ) : (T.ts m)′ = aeval (T.ts m) (T.wPoly m) := by
  by_cases hm : m < T.n
  · rw [T.wPoly_of_lt hm, aeval_C]; exact T.ht' hm
  · rw [wPoly, if_neg hm, map_zero, T.hts m (not_lt.mp hm), Derivation.map_zero]

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

/-! ### The models -/

/-- Transcendence of the generators below level `m`. -/
abbrev Tr (m : ℕ) : Prop := ∀ i < m, Transcendental (T.F i) (T.ts i)

lemma Tr.of_succ {m : ℕ} (h : T.Tr (m + 1)) : T.Tr m := fun i hi ↦ h i (by omega)

lemma aeval_toPoly {m : ℕ} (M : CField (LC m) (T.F m) (LO Fc us m))
    (hM : ∀ q, ((M.sem q : T.F m) : L) = T.ev m q) (p : GPoly (LC m)) :
    aeval (T.ts m) (GPoly.toPoly M p) = T.evP m p := by
  induction p with
  | nil => simp [evP, evPL]
  | cons a p ih =>
    rw [GPoly.toPoly_cons, map_add, map_mul, aeval_C, aeval_X, ih]
    simp only [evP, evPL, List.foldr_cons]
    congr 1
    exact hM a

/-- The model of the curve codes in `F 0`. -/
noncomputable def model0 : CField (LC 0) (T.F 0) (LO Fc us 0) :=
  cMF T.hC T.S T.hx Fc T.hSF

/-- The models, agreeing with the evaluation. -/
noncomputable def MPs : (m : ℕ) → T.Tr m →
    {M : CField (LC m) (T.F m) (LO Fc us m) // ∀ q, ((M.sem q : T.F m) : L) = T.ev m q}
  | 0, _ => ⟨T.model0, fun _ ↦ rfl⟩
  | m + 1, h =>
    let M := (MPs m h.of_succ).1
    have hM := (MPs m h.of_succ).2
    have hw : GPoly.toPoly M [etaC Fc us m] = T.wPoly m := by
      rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero,
        T.wPoly_of_lt (T.lt_of_transcendental (h m (by omega)))]
      congr 1
      apply Subtype.ext
      rw [etaC, etaOf, M.sem_mul, M.sem_deriv, M.sem_inv, IntermediateField.coe_mul,
        IntermediateField.coe_inv, coe_deriv, hM, coe_eta, logDeriv, div_eq_mul_inv]
    ⟨M.monomialVia [etaC Fc us m] (T.phi m)
      (fun p hp ↦ T.phi_injective (h m (by omega)) (hp.trans (map_zero _).symm))
      (fun P ↦ by rw [hw]; exact T.deriv_phi m P), fun q ↦ by
        change ((T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) :
          T.F (m + 1)) : L) = _
        rw [IntermediateField.coe_div, coe_phi, coe_phi, T.aeval_toPoly M hM, T.aeval_toPoly M hM]
        rfl⟩

/-- **The model of `F m`.** -/
noncomputable def MP (m : ℕ) (h : T.Tr m) : CField (LC m) (T.F m) (LO Fc us m) :=
  (T.MPs m h).1

lemma sem_MP (m : ℕ) (h : T.Tr m) (q : LC m) :
    (((T.MP m h).sem q : T.F m) : L) = T.ev m q := (T.MPs m h).2 q

lemma sem_MP_F (m : ℕ) (h : T.Tr m) (q : LC m) : (T.MP m h).sem q = T.val m q :=
  Subtype.ext (T.sem_MP m h q)

lemma toPoly_eta (m : ℕ) (h : T.Tr m) :
    GPoly.toPoly (T.MP m h) [etaC Fc us m] = C (T.eta m) := by
  rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero]
  congr 1
  apply Subtype.ext
  rw [etaC, etaOf, (T.MP m h).sem_mul, (T.MP m h).sem_deriv, (T.MP m h).sem_inv,
    IntermediateField.coe_mul, IntermediateField.coe_inv, coe_deriv, sem_MP, coe_eta, logDeriv,
    div_eq_mul_inv]

lemma sem_MP_succ (m : ℕ) (h : T.Tr (m + 1)) (q : LC (m + 1)) :
    (T.MP (m + 1) h).sem q =
      T.phi m (GPoly.toPoly (T.MP m h.of_succ) q.1) /
        T.phi m (GPoly.toPoly (T.MP m h.of_succ) q.2) := rfl

end LTower

end Curves.LT
