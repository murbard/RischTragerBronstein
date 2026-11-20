import RischTragerBronstein.Mixed.KEDecide
import RischTragerBronstein.Mixed.MTSpecs
import RischTragerBronstein.Mixed.KPDecideMain2

/-!
# Square roots over an exponential level: the values of the codes of `keDecide`

For a realization `T`: `tᵏ` (`ev_monoG`), the potential `½ a₀′/a₀` (`sem_halfFr`), the kernel of
`z ↦ z′ + ½ (a₀′/a₀) z` read from `prdeC` (`halfKer_sound`, `halfKer_complete`), the column
`B_W z` (`ev_logCol`) and the normalization `normC` (`ev_normC`).
-/

open Polynomial Differential CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma ev_zero_code (m : ℕ) (h : T.Tr m) : T.ev m (MO Fc ks m).zero = 0 := by
  rw [← T.sem_MP m h, (T.MP m h).sem_zero]; rfl

lemma ev_one_code (m : ℕ) (h : T.Tr m) : T.ev m (MO Fc ks m).one = 1 := by
  rw [← T.sem_MP m h, (T.MP m h).sem_one]; rfl

/-- The value of `tᵏ`. -/
lemma evP_monoG (m : ℕ) (h : T.Tr m) (k : ℕ) : T.evP m (monoG Fc ks m k) = T.ts m ^ k := by
  induction k with
  | zero =>
    simp [monoG, evP, evPL, T.ev_one_code m h]
  | succ k ih =>
    have e : monoG Fc ks m (k + 1) = (MO Fc ks m).zero :: monoG Fc ks m k := by
      simp [monoG, List.replicate_succ]
    rw [e]
    simp only [evP, evPL, List.foldr_cons] at ih ⊢
    rw [ih]
    calc _ = 0 + T.ts m * T.ts m ^ k := by congr 1; exact T.ev_zero_code m h
      _ = _ := by ring

/-- The value of the right-hand side `B/tᵏ`. -/
lemma evP_denC (m : ℕ) (h : T.Tr m) (A : GPoly (LC m)) (k l : ℕ) :
    T.evP m (denC Fc ks m k l A) = T.ts m ^ k * T.evP m A ^ l := by
  rw [denC, ← T.aeval_toPoly (T.MP m h) (T.sem_MP m h), GPoly.toPoly_mul, map_mul,
    T.aeval_toPoly (T.MP m h) (T.sem_MP m h), T.aeval_toPoly (T.MP m h) (T.sem_MP m h),
    T.evP_monoG m h, T.evP_powG m h]

lemma ev_rhs (m : ℕ) (h : T.Tr (m + 1)) (A B : GPoly (LC m)) (k l : ℕ) :
    T.ev (m + 1) ((B, denC Fc ks m k l A) : LC (m + 1)) = T.evP m B / (T.ts m ^ k * T.evP m A ^ l) := by
  rw [show T.ev (m + 1) ((B, denC Fc ks m k l A) : LC (m + 1)) =
    T.evP m B / T.evP m (denC Fc ks m k l A) from rfl, T.evP_denC m h.of_succ]

lemma halfFr_ok (m : ℕ) (h : T.Tr m) (a0 : LC m) : FRepOK (T.MP m h) (halfFr Fc ks m a0) := by
  intro cw hcw
  simp only [halfFr, List.mem_singleton] at hcw
  subst hcw
  rw [T.sem_mcst, T.deriv_ratCast]

/-- The potential `½ a₀′/a₀`. -/
lemma sem_halfFr (m : ℕ) (h : T.Tr m) (a0 : LC m) :
    (((T.MP m h).sem (fCode (MO Fc ks m) (halfFr Fc ks m a0)) : T.F m) : L) =
      (1 / 2 : L) * logDeriv (T.ev m a0) := by
  rw [sem_fCode, logSumV]
  simp only [halfFr, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    (T.MP m h).sem_zero, Derivation.map_zero, zero_add]
  rw [IntermediateField.coe_mul, T.coe_logDeriv_FX, T.sem_mcst, T.sem_MP m h]
  push_cast
  have h2 : ((2 : T.F m) : L) = 2 := by norm_cast
  simp only [h2]

/-- **The kernel read from `prdeC`**: each returned solution is a solution. -/
lemma halfKer_sound (m : ℕ) (h : T.Tr m) (fr : FRep (LC m))
    (hs : RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) fr))
      (prdeC Fc ks lv m fr)) :
    ∀ r ∈ prdeC Fc ks lv m fr [], ((T.MP m h).sem r.2)′ +
      (T.MP m h).sem (fCode (MO Fc ks m) fr) * (T.MP m h).sem r.2 = 0 := fun r hr ↦ by
  rw [hs.sound [] r hr]
  simp [sQ]

/-- **The kernel read from `prdeC`** is complete: a non-zero solution gives a non-zero code. -/
lemma halfKer_complete (m : ℕ) (h : T.Tr m) (fr : FRep (LC m))
    (hs : RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) fr))
      (prdeC Fc ks lv m fr)) (y : T.F m) (hy0 : y ≠ 0)
    (hy : y′ + (T.MP m h).sem (fCode (MO Fc ks m) fr) * y = 0) :
    ∃ r ∈ prdeC Fc ks lv m fr [], (MO Fc ks m).isZero r.2 = false := by
  classical
  obtain ⟨β, -, hβ⟩ := hs.complete [] [] (fun i _ ↦ by simp) y (by rw [hy]; simp [sC])
  by_contra hno
  push_neg at hno
  apply hy0
  rw [hβ]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  have hmem : (prdeC Fc ks lv m fr []).getD k ([], (MO Fc ks m).zero) ∈ prdeC Fc ks lv m fr [] := by
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]
    exact List.getElem_mem _
  have hz := hno _ hmem
  have : (MO Fc ks m).isZero ((prdeC Fc ks lv m fr []).getD k ([], (MO Fc ks m).zero)).2 = true := by
    cases h' : (MO Fc ks m).isZero ((prdeC Fc ks lv m fr []).getD k ([], (MO Fc ks m).zero)).2
    · exact absurd h' hz
    · rfl
  rw [((T.MP m h).isZero_iff _).mp this, mul_zero]

/-- **Normalization** keeps the value. -/
lemma ev_normC [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (h : T.Tr m) (q : LC m) :
    T.ev m (normC Fc m q) = T.ev m q := by
  rw [normC, T.ev_unTr m h, T.psiC_trC m h]

lemma sem_code_eq (m : ℕ) (h : T.Tr m) (q : LC m) :
    (((T.MP m h).sem q : T.F m) : L) = T.ev m q := T.sem_MP m h q

/-- **The value of the column `B_W z`.** -/
lemma ev_logCol (m : ℕ) (h : T.Tr (m + 1)) (Ahat W0 W1 : GPoly (LC m)) (z : LC m) :
    T.ev (m + 1) (logCol Fc ks m Ahat W0 W1 z) =
      (T.evP m W0 * ((T.evP m W1)′ + T.evP m W1 *
        ((1 / 2 : L) * ((T.evP m Ahat)′ * (T.evP m Ahat)⁻¹))) - (T.evP m W0)′ * T.evP m W1) *
        (T.evP m W0 * T.evP m W0 - T.evP m W1 * T.evP m W1 * T.evP m Ahat)⁻¹ * T.ev m z := by
  have hf : ∀ P : GPoly (LC m), (((T.MP (m + 1) h).sem (pc Fc ks m P) : T.F (m + 1)) : L) =
      T.evP m P := fun P ↦ by
    rw [pc, T.sem_frac_code m h]
    have : T.evP m [(MO Fc ks m).one] = 1 := by
      simp [evP, evPL, T.ev_one_code m h.of_succ]
    rw [this, div_one]
  have hz : T.evP m [z] = T.ev m z := by simp [evP, evPL]
  rw [← T.sem_MP (m + 1) h]
  simp only [logCol, halfLog, subC, (T.MP (m + 1) h).sem_mul, (T.MP (m + 1) h).sem_add,
    (T.MP (m + 1) h).sem_neg, (T.MP (m + 1) h).sem_inv, (T.MP (m + 1) h).sem_deriv,
    IntermediateField.coe_mul, IntermediateField.coe_add, IntermediateField.coe_neg,
    IntermediateField.coe_inv, MTower.coe_deriv, T.sem_mcst, hf, hz]
  push_cast
  have h2 : ((2 : T.F (m + 1)) : L) = 2 := by norm_cast
  simp only [h2]
  ring
