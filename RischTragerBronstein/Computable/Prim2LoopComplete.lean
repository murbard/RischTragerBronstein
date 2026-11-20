import RischTragerBronstein.Computable.Prim2Loop

/-!
# The `t₂`-loop at height three: completeness

Two-level model `K₁ = S(x)`, `K₂ = K₁(t₁)`. If the coefficient equations
`pⱼ′ + (j + 1) η₂ pⱼ₊₁ = Aⱼ` (`1 ≤ j ≤ k`) have a solution in `K₂` whose top coefficient is the
current `Q` up to a constant, then `prim2Loop` succeeds, and `p₁` is its last polynomial up to a
constant.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁] [IsFractionRing S[X] K₁]
variable [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

/-- The hypotheses on the two-level model, bundled. -/
structure Model2 (ι : R →+* S) (En₁ Ed₁ En₂ Ed₂ : CPoly R) : Prop where
  hD : ∀ P : S[X], P′ = derivative P
  hKconst : ∀ y : K₁, y′ = 0 → ∃ b : S, y = φ (C b)
  hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ev K₁ ι (En₁, Ed₁))) P
  hconst₂ : ∀ P : K₁[X], P′ = 0 → ∃ e : K₁, P = C e
  hK₂const : ∀ y : K₂, y′ = 0 → ∃ b : S, y = algebraMap K₁ K₂ (φ (C b))
  hη₂nd : ∀ (y : K₂) (a : S), a ≠ 0 → y′ ≠ φ₂ (C (φ (C a) * ev K₁ ι (En₂, Ed₂)))

/-- **Completeness of one level.** -/
theorem prim2Step_complete (ι : R →+* S) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂) {Iη₁ Iη₂ : RationalIntegral R}
    (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true) (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true)
    (hEd₁ : toPoly Ed₁ ≠ 0) (hEd₂ : toPoly Ed₂ ≠ 0) (hη0 : isZero Iη₁.r = false)
    (k : ℕ) (Ak Q : Poly2 R) (hA : Ak.Wf) (hQ : Q.Wf) (Pk : K₂) (b : S)
    (hP : Pk′ + ((k + 1 : ℕ) : K₂) * algebraMap K₁ K₂ (ev K₁ ι (En₂, Ed₂)) *
      (ev₂ (K₁ := K₁) ι (φ₂ X) Q.2 Q.1 + algebraMap K₁ K₂ (φ (C b))) =
        ev₂ (K₁ := K₁) ι (φ₂ X) Ak.2 Ak.1) :
    ∃ (c : R) (Q' : Poly2 R), prim2Step En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ k Ak Q = some (c, Q') ∧
      ∃ b' : S, Pk = ev₂ (K₁ := K₁) ι (φ₂ X) Q'.2 Q'.1 + algebraMap K₁ K₂ (φ (C b')) := by
  obtain ⟨hGwf, hGev⟩ := ev₂_gCodes (K₁ := K₁) ι (φ₂ X) En₂ Ed₂ hEd₂ k Ak Q hA hQ
  set G := gCodes En₂ Ed₂ k Ak Q with hG
  have hcast : φ (C (((k + 1 : ℕ) : S) * b)) = ((k + 1 : ℕ) : K₁) * φ (C b) := by
    rw [C_mul, map_mul, map_natCast (C : S →+* S[X]), map_natCast]
  have hpoly : φ₂ (polyOfCodes (K₁ := K₁) ι (fun j ↦ (G.2 j).1) (fun j ↦ (G.2 j).2) G.1) =
      ev₂ (K₁ := K₁) ι (φ₂ X) G.2 G.1 := by
    rw [map_polyOfCodes]
  have hz : Pk′ = φ₂ (polyOfCodes (K₁ := K₁) ι (fun j ↦ (G.2 j).1) (fun j ↦ (G.2 j).2) G.1 -
      C (φ (C (((k + 1 : ℕ) : S) * b)) * ev K₁ ι (En₂, Ed₂))) := by
    rw [map_sub, hpoly, hGev, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K₁ K₁[X] K₂, hcast, map_mul, map_mul, map_natCast]
    linear_combination hP
  obtain ⟨c', P, hcP, -, hconst⟩ := limitedPrimCodes_complete_poly (K₁ := K₁) (K₂ := K₂) ι M.hD
    M.hKconst hcη₁ hcη₂ hEd₁ hη0 M.hD₂ M.hconst₂ M.hη₂nd _ _ G.1 hGwf Pk _ hz
  refine ⟨c', (G.1 + 1, P), by simp only [prim2Step, ← hG, hcP, Option.map_some], ?_⟩
  obtain ⟨b', hb'⟩ := M.hK₂const _ hconst
  exact ⟨b', by rw [← hb']; ring⟩

/-- The last polynomial `Q₁` produced by the loop. -/
def prim2LastQ : Poly2 R → List (R × Poly2 R) → Poly2 R
  | Q, [] => Q
  | _, cQ :: L => prim2LastQ cQ.2 L

/-- **Completeness of the `t₂`-loop, with its final state.** -/
theorem prim2Loop_complete_last (ι : R →+* S) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (M : Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂) {Iη₁ Iη₂ : RationalIntegral R}
    (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true) (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true)
    (hEd₁ : toPoly Ed₁ ≠ 0) (hEd₂ : toPoly Ed₂ ≠ 0) (hη0 : isZero Iη₁.r = false)
    (A : ℕ → Poly2 R) (p : ℕ → K₂) (k : ℕ) (hA : ∀ j, 1 ≤ j → j ≤ k → (A j).Wf)
    (hp : ∀ j, 1 ≤ j → j ≤ k →
      (p j)′ + ((j + 1 : ℕ) : K₂) * algebraMap K₁ K₂ (ev K₁ ι (En₂, Ed₂)) * p (j + 1) =
        ev₂ (K₁ := K₁) ι (φ₂ X) (A j).2 (A j).1)
    (Q : Poly2 R) (hQ : Q.Wf) (b : S)
    (hb : p (k + 1) = ev₂ (K₁ := K₁) ι (φ₂ X) Q.2 Q.1 + algebraMap K₁ K₂ (φ (C b))) :
    ∃ L, prim2Loop En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A k Q = some L ∧ (prim2LastQ Q L).Wf ∧
      ∃ b' : S, p 1 = ev₂ (K₁ := K₁) ι (φ₂ X) (prim2LastQ Q L).2 (prim2LastQ Q L).1 +
        algebraMap K₁ K₂ (φ (C b')) := by
  have ht₁ : (φ₂ X)′ = algebraMap K₁ K₂ (ev K₁ ι (En₁, Ed₁)) := by
    rw [deriv_algebraMap, M.hD₂, implicitDeriv_X, IsScalarTower.algebraMap_apply K₁ K₁[X] K₂,
      Polynomial.algebraMap_eq]
  induction k generalizing Q b with
  | zero => exact ⟨[], rfl, hQ, b, hb⟩
  | succ k ih =>
    obtain ⟨c, Q', hstep, b', hb'⟩ := prim2Step_complete (K₁ := K₁) (K₂ := K₂) ι M hcη₁ hcη₂ hEd₁
      hEd₂ hη0 (k + 1) (A (k + 1)) Q (hA (k + 1) (by omega) le_rfl) hQ (p (k + 1)) b (by
        rw [← hb]
        exact hp (k + 1) (by omega) le_rfl)
    obtain ⟨hQ', -⟩ := prim2Step_sound (K₁ := K₁) (K₂ := K₂) ι M.hD hcη₁ hcη₂ hEd₁ hEd₂ (φ₂ X) ht₁
      (k + 1) (A (k + 1)) Q (hA (k + 1) (by omega) le_rfl) hQ hstep
    obtain ⟨L, hL, hlast, b'', hb''⟩ :=
      ih (fun j h1 h2 ↦ hA j h1 (by omega)) (fun j h1 h2 ↦ hp j h1 (by omega)) Q' hQ' b' hb'
    exact ⟨(c, Q') :: L, by simp only [prim2Loop, hstep, hL, Option.map_some], hlast, b'', hb''⟩

end CPoly
