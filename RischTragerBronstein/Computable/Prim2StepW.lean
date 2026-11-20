import RischTragerBronstein.Computable.LimitedPrimWComplete
import RischTragerBronstein.Computable.Prim2LoopGen

/-!
# The `t₂`-loop for a nested primitive `t₂′ = W ∈ R(x)(t₁)`

Coefficient equations of `(∑ Pₖ t₂ ^ k)′ = ∑ Aₖ t₂ ^ k`:
`Pₖ′ + (k + 1) W Pₖ₊₁ = Aₖ`, with `Pₖ₊₁ = Q + b` known up to a constant `b`. Each level is one
limited integration problem `Aₖ - (k + 1) W Q - c W = Pₖ′` in `R(x)(t₁)`, solved by `limitedPrimW`
(`W` has a non-zero Hermite remainder: `log u` with `u ∉ R(x)`, `li x`, …).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- `Aₖ - (k + 1) W Q`. -/
def gCodeW (En₁ Ed₁ : CPoly R) (W : GFrac (GFrac R)) (k : ℕ) (Ak Q : GFrac (GFrac R)) :
    GFrac (GFrac R) :=
  normF₂ ((ops₂p En₁ Ed₁).add Ak ((ops₂p En₁ Ed₁).neg ((ops₂p En₁ Ed₁).mul
    ((ops₂p En₁ Ed₁).mul ((ops₂p En₁ Ed₁).natCast (k + 1)) W) Q)))

/-- One level of the loop. -/
def prim2StepW (En₁ Ed₁ : CPoly R) (Iη₁ : CPoly.RationalIntegral R) (W : GFrac (GFrac R))
    (k : ℕ) (Ak Q : GFrac (GFrac R)) : Option (R × GFrac (GFrac R)) :=
  (limitedPrimW En₁ Ed₁ Iη₁ (gCodeW En₁ Ed₁ W k Ak Q) W).map fun r ↦
    (r.1, solCode En₁ Ed₁ r.2.1 r.2.2 ((GPoly.divMod (ops₁g R) r.2.1.b r.2.1.s).1.length + 1))

/-- Levels `k, k - 1, …, 1`. -/
def prim2LoopW (En₁ Ed₁ : CPoly R) (Iη₁ : CPoly.RationalIntegral R) (W : GFrac (GFrac R))
    (A : ℕ → GFrac (GFrac R)) : ℕ → GFrac (GFrac R) → Option (List (R × GFrac (GFrac R)))
  | 0, _ => some []
  | k + 1, Q =>
    match prim2StepW En₁ Ed₁ Iη₁ W (k + 1) (A (k + 1)) Q with
    | none => none
    | some cQ => (prim2LoopW En₁ Ed₁ Iη₁ W A k cQ.2).map (cQ :: ·)

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

/-- The hypotheses on the two-level model `S(x) ⊆ S(x)(t₁)`, bundled. -/
structure ModelW (ι : R →+* S) (En₁ Ed₁ : CPoly R) : Prop where
  hD : ∀ P : S[X], P′ = derivative P
  hKconst : ∀ y : K₁, y′ = 0 → ∃ b : S, y = φ (C b)
  hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P
  hconst₂ : ∀ P : K₁[X], P′ = 0 → ∃ e : K₁, P = C e
  hK₂const : ∀ y : K₂, y′ = 0 → ∃ b : S, y = φ₂ (C (φ (C b)))

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {En₁ Ed₁ : CPoly R}
  (M : ModelW (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁)

/-- The model of codes of `R(x)(t₁)`. -/
noncomputable abbrev ModelW.cf : CField (GFrac (GFrac R)) K₂ (ops₂p En₁ Ed₁) :=
  M₂W (K₂ := K₂) ι h0 M.hD M.hD₂

lemma sem_gCodeW (W : GFrac (GFrac R)) (k : ℕ) (Ak Q : GFrac (GFrac R)) :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) (gCodeW En₁ Ed₁ W k Ak Q).2 ≠ 0 ∧
      (M.cf ι h0).sem (gCodeW En₁ Ed₁ W k Ak Q) = (M.cf ι h0).sem Ak -
        ((k + 1 : ℕ) : K₂) * (M.cf ι h0).sem W * (M.cf ι h0).sem Q := by
  have hsem : (M.cf ι h0).sem ((ops₂p En₁ Ed₁).add Ak ((ops₂p En₁ Ed₁).neg ((ops₂p En₁ Ed₁).mul
      ((ops₂p En₁ Ed₁).mul ((ops₂p En₁ Ed₁).natCast (k + 1)) W) Q))) = (M.cf ι h0).sem Ak -
        ((k + 1 : ℕ) : K₂) * (M.cf ι h0).sem W * (M.cf ι h0).sem Q := by
    rw [CField.sem_add, CField.sem_neg, CField.sem_mul, CField.sem_mul, CField.sem_natCast]
    ring
  rw [← hsem]
  unfold gCodeW normF₂
  split_ifs with hz
  · have hz' := (GPoly.isZero_iff (M₁In (K₁ := K₁) ι h0 M.hD) _).mp hz
    refine ⟨by simp [CField.sem_one], ?_⟩
    rw [sem_M₂W, sem_M₂W, hz']
    simp
  · exact ⟨fun h ↦ hz ((GPoly.isZero_iff (M₁In (K₁ := K₁) ι h0 M.hD) _).mpr h), rfl⟩

/-- **Semantics of the solution code.** -/
theorem sem_solCodeW (h : GPoly.HermiteResult (GFrac R)) (P : ℕ → CPoly R × CPoly R) (n : ℕ) :
    (M.cf ι h0).sem (solCode En₁ Ed₁ h P n) =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) h.gn) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) h.gd) +
        CPoly.ev₂ (K₁ := K₁) ι (φ₂ X) P n := by
  rw [solCode, (M.cf ι h0).sem_add, sem_M₂W, sem_M₂W, toPoly_map_range]
  simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one, C_1,
    map_one, div_one, CPoly.ev₂, map_sum, map_mul, map_pow]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [IsScalarTower.algebraMap_apply K₁ K₁[X] K₂, Polynomial.algebraMap_eq]

/-- **Soundness of one level.** -/
theorem prim2StepW_sound {Iη₁ : CPoly.RationalIntegral R}
    (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (W : GFrac (GFrac R)) (k : ℕ) (Ak Q : GFrac (GFrac R)) {c : R} {Q' : GFrac (GFrac R)}
    (h : prim2StepW En₁ Ed₁ Iη₁ W k Ak Q = some (c, Q')) :
    ((M.cf ι h0).sem Q')′ = (M.cf ι h0).sem Ak -
      ((k + 1 : ℕ) : K₂) * (M.cf ι h0).sem W * (M.cf ι h0).sem Q -
      φ₂ (C (φ (C (ι c)))) * (M.cf ι h0).sem W := by
  simp only [prim2StepW, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨c₀, hr, P⟩, hsome, rfl, rfl⟩ := h
  obtain ⟨-, hsem⟩ := sem_gCodeW (K₂ := K₂) ι h0 M W k Ak Q
  have := limitedPrimW_sound (K₁ := K₁) (K₂ := K₂) ι h0 M.hD hcη₁ hEd₁ M.hD₂ M.hconst₂ _ W hsome
  rw [sem_solCodeW ι h0 M, this, ← hsem]

/-- **Completeness of one level.** -/
theorem prim2StepW_complete {Iη₁ : CPoly.RationalIntegral R}
    (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (hη0 : CPoly.isZero Iη₁.r = false) (W : GFrac (GFrac R))
    (hW0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) W.2 ≠ 0)
    (hrW : GPoly.isZero (ops₁g R) (GPoly.divMod (ops₁g R)
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2 = false)
    (k : ℕ) (Ak Q : GFrac (GFrac R)) (Pk : K₂) (b : S)
    (hP : Pk′ + ((k + 1 : ℕ) : K₂) * (M.cf ι h0).sem W *
      ((M.cf ι h0).sem Q + φ₂ (C (φ (C b)))) = (M.cf ι h0).sem Ak) :
    ∃ c Q', prim2StepW En₁ Ed₁ Iη₁ W k Ak Q = some (c, Q') ∧
      ∃ b' : S, Pk = (M.cf ι h0).sem Q' + φ₂ (C (φ (C b'))) := by
  obtain ⟨hden, hsem⟩ := sem_gCodeW (K₂ := K₂) ι h0 M W k Ak Q
  have hcast : φ₂ (C (φ (C (((k + 1 : ℕ) : S) * b)))) = ((k + 1 : ℕ) : K₂) * φ₂ (C (φ (C b))) := by
    rw [C_mul, map_mul, C_mul, map_mul, map_natCast (C : S →+* S[X]), map_natCast,
      map_natCast (C : K₁ →+* K₁[X]), map_natCast]
  obtain ⟨c', hr, P, hsome, hc'⟩ := limitedPrimW_complete (K₁ := K₁) (K₂ := K₂) ι h0 M.hD
    M.hKconst hcη₁ hEd₁ hη0 M.hD₂ M.hconst₂ (gCodeW En₁ Ed₁ W k Ak Q) W hden hW0 hrW Pk
    (((k + 1 : ℕ) : S) * b) (by
      rw [hcast]
      change _ = (M.cf ι h0).sem _ - _ * (M.cf ι h0).sem W
      rw [hsem]
      linear_combination hP)
  have hstep : prim2StepW En₁ Ed₁ Iη₁ W k Ak Q = some (c',
      solCode En₁ Ed₁ hr P ((GPoly.divMod (ops₁g R) hr.b hr.s).1.length + 1)) := by
    simp only [prim2StepW, hsome, Option.map_some]
  refine ⟨c', _, hstep, ?_⟩
  have hsound := prim2StepW_sound (K₁ := K₁) (K₂ := K₂) ι h0 M hcη₁ hEd₁ W k Ak Q hstep
  have hconst : (Pk - (M.cf ι h0).sem (solCode En₁ Ed₁ hr P
      ((GPoly.divMod (ops₁g R) hr.b hr.s).1.length + 1)))′ = 0 := by
    rw [map_sub, hsound, hc', hcast]
    linear_combination hP
  obtain ⟨b', hb'⟩ := M.hK₂const _ hconst
  exact ⟨b', by rw [← hb']; ring⟩

/-- **Completeness of the loop, with its final state.** -/
theorem prim2LoopW_complete_last {Iη₁ : CPoly.RationalIntegral R}
    (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (hη0 : CPoly.isZero Iη₁.r = false) (W : GFrac (GFrac R))
    (hW0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) W.2 ≠ 0)
    (hrW : GPoly.isZero (ops₁g R) (GPoly.divMod (ops₁g R)
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2 = false)
    (A : ℕ → GFrac (GFrac R)) (p : ℕ → K₂) (k : ℕ)
    (hp : ∀ j, 1 ≤ j → j ≤ k →
      (p j)′ + ((j + 1 : ℕ) : K₂) * (M.cf ι h0).sem W * p (j + 1) = (M.cf ι h0).sem (A j))
    (Q : GFrac (GFrac R)) (b : S) (hb : p (k + 1) = (M.cf ι h0).sem Q + φ₂ (C (φ (C b)))) :
    ∃ L, prim2LoopW En₁ Ed₁ Iη₁ W A k Q = some L ∧
      ∃ b' : S, p 1 = (M.cf ι h0).sem (lastGen Q L) + φ₂ (C (φ (C b'))) := by
  induction k generalizing Q b with
  | zero => exact ⟨[], rfl, b, hb⟩
  | succ k ih =>
    obtain ⟨c, Q', hstep, b', hb'⟩ := prim2StepW_complete (K₁ := K₁) (K₂ := K₂) ι h0 M hcη₁ hEd₁
      hη0 W hW0 hrW (k + 1) (A (k + 1)) Q (p (k + 1)) b (by
        rw [← hb]
        exact hp (k + 1) (by omega) le_rfl)
    obtain ⟨L, hL, b'', hb''⟩ := ih (fun j h1 h2 ↦ hp j h1 (by omega)) Q' b' hb'
    exact ⟨(c, Q') :: L, by simp only [prim2LoopW, hstep, hL, Option.map_some], b'', hb''⟩

end Tower
