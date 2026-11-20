import RischTragerBronstein.Computable.Prim2StepGen

/-!
# The general `t₂`-loop at height three

Coefficients `Aₖ` and states `Q` are general elements of `R(x)(t₁)` (fraction codes).
`prim2LoopGen` runs levels `k, k - 1, …, 1`; `prim2LoopGen_complete_last`: if the coefficient
equations are solvable in a two-level model over extended constants, the loop succeeds and `p₁` is
its last element up to a constant.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- Levels `k, k - 1, …, 1` of the general `t₂`-loop. -/
def prim2LoopGen (En₁ Ed₁ : CPoly R) (Iη₁ : CPoly.RationalIntegral R) (En₂ Ed₂ : CPoly R)
    (Iη₂ : CPoly.RationalIntegral R) (A : ℕ → GFrac (GFrac R)) :
    ℕ → GFrac (GFrac R) → Option (List (R × GFrac (GFrac R)))
  | 0, _ => some []
  | k + 1, Q =>
    match prim2StepGen En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ (k + 1) (A (k + 1)) Q with
    | none => none
    | some cQ => (prim2LoopGen En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A k cQ.2).map (cQ :: ·)

/-- The last element produced by the loop. -/
def lastGen : GFrac (GFrac R) → List (R × GFrac (GFrac R)) → GFrac (GFrac R)
  | Q, [] => Q
  | _, cQ :: L => lastGen cQ.2 L

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]

local notation "φ" => algebraMap S[X] K₁

/-- **Completeness of the general `t₂`-loop, with its final state.** -/
theorem prim2LoopGen_complete_last (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : CPoly.Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂)
    {Iη₁ Iη₂ : CPoly.RationalIntegral R} (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : CPoly.rationalCheck En₂ Ed₂ Iη₂ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (hη0 : CPoly.isZero Iη₁.r = false) (A : ℕ → GFrac (GFrac R)) (p : ℕ → K₂) (k : ℕ)
    (hp : ∀ j, 1 ≤ j → j ≤ k →
      (p j)′ + ((j + 1 : ℕ) : K₂) * algebraMap K₁ K₂ (CPoly.ev K₁ ι (En₂, Ed₂)) * p (j + 1) =
        (M₂In ι h0 M).sem (A j))
    (Q : GFrac (GFrac R)) (b : S)
    (hb : p (k + 1) = (M₂In ι h0 M).sem Q + algebraMap K₁ K₂ (φ (C b))) :
    ∃ L, prim2LoopGen En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A k Q = some L ∧
      ∃ b' : S, p 1 = (M₂In ι h0 M).sem (lastGen Q L) + algebraMap K₁ K₂ (φ (C b')) := by
  induction k generalizing Q b with
  | zero => exact ⟨[], rfl, b, hb⟩
  | succ k ih =>
    obtain ⟨c, Q', hstep, b', hb'⟩ := prim2StepGen_complete (K₁ := K₁) (K₂ := K₂) ι h0 M hcη₁
      hcη₂ hEd₁ hη0 (k + 1) (A (k + 1)) Q (p (k + 1)) b (by
        rw [← hb]
        exact hp (k + 1) (by omega) le_rfl)
    obtain ⟨L, hL, b'', hb''⟩ := ih (fun j h1 h2 ↦ hp j h1 (by omega)) Q' b' hb'
    exact ⟨(c, Q') :: L, by simp only [prim2LoopGen, hstep, hL, Option.map_some], b'', hb''⟩

end Tower
