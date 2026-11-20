import RischTragerBronstein.Computable.LimitedPrimPolyComplete

/-!
# The polynomial part at height three: the `t₂`-loop

Integrand `∑ₖ Aₖ t₂ ^ k`, `Aₖ ∈ R(x)[t₁]` (coefficient codes), two primitives `t₁′ = η₁`, `t₂′ = η₂`.
An antiderivative `∑ Pₖ t₂ ^ k` must satisfy `Pₖ′ + (k + 1) η₂ Pₖ₊₁ = Aₖ` (`k ≥ 1`) with
`Pₖ ∈ C'(x)[t₁]`; writing `Pₖ₊₁ = Qₖ₊₁ + const`, level `k` is the limited-integration problem

  `Aₖ - (k + 1) η₂ Qₖ₊₁ = Qₖ′ + c η₂`   inside `R(x)[t₁]`,

solved by `limitedPrimCodes`. `prim2Step` is one level; `prim2Step_sound` its soundness in every
two-level model.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- A polynomial in `t₁` over `R(x)`: a degree bound and coefficient codes. -/
abbrev Poly2 (R : Type*) := ℕ × (ℕ → CPoly R × CPoly R)

/-- Coefficient codes cut off beyond the degree bound (value `0 / 1`). -/
def trunc (P : Poly2 R) (j : ℕ) : CPoly R × CPoly R := if j ≤ P.1 then P.2 j else ([], [1])

/-- `q · η₂`. -/
def etaMulF (En₂ Ed₂ : CPoly R) (q : CPoly R × CPoly R) : CPoly R × CPoly R :=
  (mul q.1 En₂, mul q.2 Ed₂)

/-- The codes of `Aₖ - (k + 1) η₂ Q`. -/
def gCodes (En₂ Ed₂ : CPoly R) (k : ℕ) (Ak Q : Poly2 R) : Poly2 R :=
  (max Ak.1 Q.1, fun j ↦
    fsub (trunc Ak j) (fsmul ((k + 1 : ℕ) : R) (etaMulF En₂ Ed₂ (trunc Q j))))

/-- One level of the `t₂`-loop. -/
def prim2Step (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (En₂ Ed₂ : CPoly R)
    (Iη₂ : RationalIntegral R) (k : ℕ) (Ak Q : Poly2 R) : Option (R × Poly2 R) :=
  let G := gCodes En₂ Ed₂ k Ak Q
  (limitedPrimCodes En₁ Ed₁ Iη₁ Iη₂ (fun j ↦ (G.2 j).1) (fun j ↦ (G.2 j).2) G.1).map
    fun cP ↦ (cP.1, (G.1 + 1, cP.2))

/-- Levels `k, k - 1, …, 1` of the `t₂`-loop. -/
def prim2Loop (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (En₂ Ed₂ : CPoly R)
    (Iη₂ : RationalIntegral R) (A : ℕ → Poly2 R) : ℕ → Poly2 R → Option (List (R × Poly2 R))
  | 0, _ => some []
  | k + 1, Q =>
    match prim2Step En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ (k + 1) (A (k + 1)) Q with
    | none => none
    | some cQ => (prim2Loop En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A k cQ.2).map (cQ :: ·)

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K₁] [Algebra S[X] K₁] [IsFractionRing S[X] K₁]
variable [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Field K₂] [Differential K₂] [Algebra K₁ K₂] [DifferentialAlgebra K₁ K₂]

local notation "φ" => algebraMap S[X] K₁

/-- Denominators are nonzero up to the degree bound. -/
def Poly2.Wf (P : Poly2 R) : Prop := ∀ j ≤ P.1, toPoly (P.2 j).2 ≠ 0

lemma trunc_den (P : Poly2 R) (hP : P.Wf) (j : ℕ) : toPoly (trunc P j).2 ≠ 0 := by
  unfold trunc
  split_ifs with h
  · exact hP j h
  · simp

/-- Evaluating with a larger bound, after truncation, changes nothing. -/
lemma ev₂_trunc (ι : R →+* S) (t₁ : K₂) (P : Poly2 R) (n : ℕ) (hn : P.1 ≤ n) :
    ev₂ (K₁ := K₁) ι t₁ (trunc P) n = ev₂ (K₁ := K₁) ι t₁ P.2 P.1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero =>
    simp only [ev₂, Nat.add_zero]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [trunc, if_pos (by have := Finset.mem_range.mp hj; omega)]
  | succ m ih =>
    have := ih (Nat.le_add_right _ _)
    rw [ev₂, show P.1 + (m + 1) + 1 = (P.1 + m + 1) + 1 by ring, Finset.sum_range_succ, ← ev₂,
      this, trunc, if_neg (by omega)]
    simp [ev]

theorem ev₂_gCodes (ι : R →+* S) (t₁ : K₂) (En₂ Ed₂ : CPoly R) (hEd₂ : toPoly Ed₂ ≠ 0)
    (k : ℕ) (Ak Q : Poly2 R) (hA : Ak.Wf) (hQ : Q.Wf) :
    (gCodes En₂ Ed₂ k Ak Q).Wf ∧
      ev₂ (K₁ := K₁) ι t₁ (gCodes En₂ Ed₂ k Ak Q).2 (gCodes En₂ Ed₂ k Ak Q).1 =
        ev₂ (K₁ := K₁) ι t₁ Ak.2 Ak.1 -
          ((k + 1 : ℕ) : K₂) * algebraMap K₁ K₂ (ev K₁ ι (En₂, Ed₂)) *
            ev₂ (K₁ := K₁) ι t₁ Q.2 Q.1 := by
  have hden : ∀ j, toPoly (etaMulF En₂ Ed₂ (trunc Q j)).2 ≠ 0 := fun j ↦ by
    simp only [etaMulF, toPoly_mul]
    exact mul_ne_zero (trunc_den Q hQ j) hEd₂
  have hcoef : ∀ j, toPoly ((gCodes En₂ Ed₂ k Ak Q).2 j).2 ≠ 0 ∧
      ev K₁ ι ((gCodes En₂ Ed₂ k Ak Q).2 j) = ev K₁ ι (trunc Ak j) -
        ((k + 1 : ℕ) : K₁) * ev K₁ ι (En₂, Ed₂) * ev K₁ ι (trunc Q j) := fun j ↦ by
    obtain ⟨h1, h2⟩ := ev_fsub (K := K₁) ι (q₁ := trunc Ak j)
      (q₂ := fsmul ((k + 1 : ℕ) : R) (etaMulF En₂ Ed₂ (trunc Q j))) (trunc_den Ak hA j) (hden j)
    refine ⟨h1, ?_⟩
    simp only [gCodes]
    rw [h2, ev_fsmul]
    have hη : ev K₁ ι (etaMulF En₂ Ed₂ (trunc Q j)) =
        ev K₁ ι (En₂, Ed₂) * ev K₁ ι (trunc Q j) := by
      simp only [ev, etaMulF, toPoly_mul, Polynomial.map_mul, map_mul]
      rw [mul_div_mul_comm]
      ring
    have hcast : φ (C (ι ((k + 1 : ℕ) : R))) = ((k + 1 : ℕ) : K₁) := by
      rw [map_natCast ι, map_natCast (C : S →+* S[X]), map_natCast]
    rw [hη, hcast]
    ring
  refine ⟨fun j _ ↦ (hcoef j).1, ?_⟩
  rw [← ev₂_trunc (K₁ := K₁) ι t₁ Ak (max Ak.1 Q.1) (le_max_left _ _),
    ← ev₂_trunc (K₁ := K₁) ι t₁ Q (max Ak.1 Q.1) (le_max_right _ _)]
  simp only [ev₂, gCodes, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have := (hcoef j).2
  simp only [gCodes] at this
  rw [this, map_sub, map_mul, map_mul, map_natCast]
  ring

/-- **Soundness of one level of the `t₂`-loop.** -/
theorem prim2Step_sound (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {En₁ Ed₁ En₂ Ed₂ : CPoly R} {Iη₁ Iη₂ : RationalIntegral R}
    (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true) (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true)
    (hEd₁ : toPoly Ed₁ ≠ 0) (hEd₂ : toPoly Ed₂ ≠ 0) (t₁ : K₂)
    (ht₁ : t₁′ = algebraMap K₁ K₂ (ev K₁ ι (En₁, Ed₁))) (k : ℕ) (Ak Q : Poly2 R) (hA : Ak.Wf)
    (hQ : Q.Wf) {c : R} {Q' : Poly2 R}
    (h : prim2Step En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ k Ak Q = some (c, Q')) :
    Q'.Wf ∧ (ev₂ (K₁ := K₁) ι t₁ Q'.2 Q'.1)′ = ev₂ (K₁ := K₁) ι t₁ Ak.2 Ak.1 -
      ((k + 1 : ℕ) : K₂) * algebraMap K₁ K₂ (ev K₁ ι (En₂, Ed₂)) * ev₂ (K₁ := K₁) ι t₁ Q.2 Q.1 -
      algebraMap K₁ K₂ (φ (C (ι c)) * ev K₁ ι (En₂, Ed₂)) := by
  simp only [prim2Step, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨c₀, P₀⟩, hcP, rfl, rfl⟩ := h
  obtain ⟨hGwf, hGev⟩ := ev₂_gCodes (K₁ := K₁) ι t₁ En₂ Ed₂ hEd₂ k Ak Q hA hQ
  obtain ⟨hden, hder⟩ := limitedPrimCodes_sound_poly (K₁ := K₁) (K₂ := K₂) ι hD hcη₁ hcη₂ hEd₁ t₁
    ht₁ _ _ _ hGwf hcP
  exact ⟨hden, by rw [hder, ← hGev]⟩

end CPoly
