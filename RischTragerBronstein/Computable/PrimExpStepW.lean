import RischTragerBronstein.Computable.LimitedExpSol
import RischTragerBronstein.Computable.Prim2LoopGen

/-!
# The `t₂`-loop for a primitive `t₂′ = W ∈ R(x)(exp a)`

Coefficient equations of `(∑ Pₖ t₂ ^ k)′ = ∑ Aₖ t₂ ^ k`:
`Pₖ′ + (k + 1) W Pₖ₊₁ = Aₖ`, with `Pₖ₊₁ = Q + b` known up to a constant `b`. Each level is one
limited integration problem `Aₖ - (k + 1) W Q - c W = Pₖ′` in `R(x)(exp a)`, solved by
`limitedExpSol` (`W` not a derivative in `R(x)(exp a)`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- `Aₖ - (k + 1) W Q`. -/
def gCodeE (a : CPoly R) (W : GFrac (GFrac R)) (k : ℕ) (Ak Q : GFrac (GFrac R)) :
    GFrac (GFrac R) :=
  normF₂ ((ops₂e a).add Ak ((ops₂e a).neg ((ops₂e a).mul
    ((ops₂e a).mul ((ops₂e a).natCast (k + 1)) W) Q)))

/-- One level of the loop. -/
def primExpStepW (a : CPoly R) (W : GFrac (GFrac R)) (k : ℕ) (Ak Q : GFrac (GFrac R)) :
    Option (R × GFrac (GFrac R)) :=
  limitedExpSol a (gCodeE a W k Ak Q) W

/-- Levels `k, k - 1, …, 1`. -/
def primExpLoopW (a : CPoly R) (W : GFrac (GFrac R)) (A : ℕ → GFrac (GFrac R)) :
    ℕ → GFrac (GFrac R) → Option (List (R × GFrac (GFrac R)))
  | 0, _ => some []
  | k + 1, Q =>
    match primExpStepW a W (k + 1) (A (k + 1)) Q with
    | none => none
    | some cQ => (primExpLoopW a W A k cQ.2).map (cQ :: ·)

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [DecidableEq S]
variable [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

/-- The hypotheses on the two-level model `S(x) ⊆ S(x)(exp a)`, bundled. -/
structure ModelEW (ι : R →+* S) (a : CPoly R) : Prop where
  hD : ∀ P : S[X], P′ = derivative P
  ha : CPoly.trim (CPoly.deriv a) ≠ []
  hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P
  hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n
  hK₂const : ∀ y : K₂, y′ = 0 → ∃ b : S, y = φ₂ (C (φ (C b)))

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) {a : CPoly R}
  (M : ModelEW (K₁ := K₁) (K₂ := K₂) ι a)

/-- The model of codes of `R(x)(exp a)`. -/
noncomputable abbrev ModelEW.cf : CField (GFrac (GFrac R)) K₂ (ops₂e a) :=
  M₂E (K₂ := K₂) ι h0 M.hD M.hD₂

lemma sem_gCodeE (W : GFrac (GFrac R)) (k : ℕ) (Ak Q : GFrac (GFrac R)) :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) (gCodeE a W k Ak Q).2 ≠ 0 ∧
      (M.cf ι h0).sem (gCodeE a W k Ak Q) = (M.cf ι h0).sem Ak -
        ((k + 1 : ℕ) : K₂) * (M.cf ι h0).sem W * (M.cf ι h0).sem Q := by
  have hsem : (M.cf ι h0).sem ((ops₂e a).add Ak ((ops₂e a).neg ((ops₂e a).mul
      ((ops₂e a).mul ((ops₂e a).natCast (k + 1)) W) Q))) = (M.cf ι h0).sem Ak -
        ((k + 1 : ℕ) : K₂) * (M.cf ι h0).sem W * (M.cf ι h0).sem Q := by
    rw [CField.sem_add, CField.sem_neg, CField.sem_mul, CField.sem_mul, CField.sem_natCast]
    ring
  rw [← hsem]
  unfold gCodeE normF₂
  split_ifs with hz
  · have hz' := (GPoly.isZero_iff (M₁In (K₁ := K₁) ι h0 M.hD) _).mp hz
    refine ⟨by simp [CField.sem_one], ?_⟩
    rw [ModelEW.cf, sem_M₂E, sem_M₂E, hz']
    simp
  · exact ⟨fun h ↦ hz ((GPoly.isZero_iff (M₁In (K₁ := K₁) ι h0 M.hD) _).mpr h), rfl⟩

/-- **Soundness of one level.** -/
theorem primExpStepW_sound (W : GFrac (GFrac R)) (k : ℕ) (Ak Q : GFrac (GFrac R)) {c : R}
    {Q' : GFrac (GFrac R)} (h : primExpStepW a W k Ak Q = some (c, Q')) :
    ((M.cf ι h0).sem Q')′ = (M.cf ι h0).sem Ak -
      ((k + 1 : ℕ) : K₂) * (M.cf ι h0).sem W * (M.cf ι h0).sem Q -
      φ₂ (C (φ (C (ι c)))) * (M.cf ι h0).sem W := by
  obtain ⟨-, hsem⟩ := sem_gCodeE (K₂ := K₂) ι h0 M W k Ak Q
  have := limitedExpSol_sound (K₁ := K₁) (K₂ := K₂) ι h0 M.hD a M.hD₂ M.hconst _ W h
  rw [ModelEW.cf] at hsem ⊢
  rw [this, ← hsem]

/-- **Completeness of one level.** -/
theorem primExpStepW_complete (W : GFrac (GFrac R))
    (hW0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) W.2 ≠ 0)
    (hWnd : isDerivExp a W.1 W.2 = false)
    (k : ℕ) (Ak Q : GFrac (GFrac R)) (Pk : K₂) (b : S)
    (hP : Pk′ + ((k + 1 : ℕ) : K₂) * (M.cf ι h0).sem W *
      ((M.cf ι h0).sem Q + φ₂ (C (φ (C b)))) = (M.cf ι h0).sem Ak) :
    ∃ c Q', primExpStepW a W k Ak Q = some (c, Q') ∧
      ∃ b' : S, Pk = (M.cf ι h0).sem Q' + φ₂ (C (φ (C b'))) := by
  obtain ⟨hden, hsem⟩ := sem_gCodeE (K₂ := K₂) ι h0 M W k Ak Q
  have hcast : φ₂ (C (φ (C (((k + 1 : ℕ) : S) * b)))) = ((k + 1 : ℕ) : K₂) * φ₂ (C (φ (C b))) := by
    rw [C_mul, map_mul, C_mul, map_mul, map_natCast (C : S →+* S[X]), map_natCast,
      map_natCast (C : K₁ →+* K₁[X]), map_natCast]
  obtain ⟨c', Q', hsome, hc'⟩ := limitedExpSol_complete (K₁ := K₁) (K₂ := K₂) ι h0 M.hD a M.ha
    M.hD₂ M.hconst (gCodeE a W k Ak Q) W hden hW0 hWnd (((k + 1 : ℕ) : S) * b) Pk (by
      rw [hcast]
      change _ = (M.cf ι h0).sem _ - _ * (M.cf ι h0).sem W
      rw [hsem]
      linear_combination hP)
  have hstep : primExpStepW a W k Ak Q = some (c', Q') := hsome
  refine ⟨c', Q', hstep, ?_⟩
  have hsound := primExpStepW_sound (K₁ := K₁) (K₂ := K₂) ι h0 M W k Ak Q hstep
  have hconst : (Pk - (M.cf ι h0).sem Q')′ = 0 := by
    rw [map_sub, hsound, hc', hcast]
    linear_combination hP
  obtain ⟨b', hb'⟩ := M.hK₂const _ hconst
  exact ⟨b', by rw [← hb']; ring⟩

/-- **Completeness of the loop, with its final state.** -/
theorem primExpLoopW_complete_last (W : GFrac (GFrac R))
    (hW0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 M.hD) W.2 ≠ 0)
    (hWnd : isDerivExp a W.1 W.2 = false)
    (A : ℕ → GFrac (GFrac R)) (p : ℕ → K₂) (k : ℕ)
    (hp : ∀ j, 1 ≤ j → j ≤ k →
      (p j)′ + ((j + 1 : ℕ) : K₂) * (M.cf ι h0).sem W * p (j + 1) = (M.cf ι h0).sem (A j))
    (Q : GFrac (GFrac R)) (b : S) (hb : p (k + 1) = (M.cf ι h0).sem Q + φ₂ (C (φ (C b)))) :
    ∃ L, primExpLoopW a W A k Q = some L ∧
      ∃ b' : S, p 1 = (M.cf ι h0).sem (lastGen Q L) + φ₂ (C (φ (C b'))) := by
  induction k generalizing Q b with
  | zero => exact ⟨[], rfl, b, hb⟩
  | succ k ih =>
    obtain ⟨c, Q', hstep, b', hb'⟩ := primExpStepW_complete (K₁ := K₁) (K₂ := K₂) ι h0 M W hW0
      hWnd (k + 1) (A (k + 1)) Q (p (k + 1)) b (by
        rw [← hb]
        exact hp (k + 1) (by omega) le_rfl)
    obtain ⟨L, hL, b'', hb''⟩ := ih (fun j h1 h2 ↦ hp j h1 (by omega)) Q' b' hb'
    exact ⟨(c, Q') :: L, by simp only [primExpLoopW, hstep, hL, Option.map_some], b'', hb''⟩

end Tower
