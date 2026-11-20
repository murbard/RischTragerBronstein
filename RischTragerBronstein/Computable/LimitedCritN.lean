import RischTragerBronstein.Computable.LinSolve
import RischTragerBronstein.Computable.LimitedCrit

/-!
# Limited integration over `R(x)` with several parameters: the executable criterion

Given the logarithmic parts `r_f / s_f` of `f` and `rᵢ / sᵢ` of `ηᵢ` (Hermite data),
`CPoly.limitedCritN` finds constants `cᵢ` with

  `r_f / s_f = ∑ cᵢ rᵢ / sᵢ`,

by clearing denominators — `r_f ∏ sᵢ = ∑ cᵢ (rᵢ s_f ∏_{j ≠ i} sⱼ)` — and calling the verified linear
solver. `limitedCritN_sound` / `limitedCritN_complete_map`: a returned list satisfies the cleared
identity; `none` means no constants exist in any extension of the constant field.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R S : Type*} [Field R] [DecidableEq R] [Field S]

/-- `∏ sᵢ`. -/
def prodDen : List (CPoly R × CPoly R) → CPoly R
  | [] => [1]
  | η :: ηs => mul η.2 (prodDen ηs)

/-- The cleared vectors `rᵢ ∏_{j ≠ i} sⱼ`. -/
def clearedNum : List (CPoly R × CPoly R) → List (CPoly R)
  | [] => []
  | η :: ηs => mul η.1 (prodDen ηs) :: (clearedNum ηs).map (mul η.2)

/-- Find `cᵢ` with `r_f ∏ sᵢ = ∑ cᵢ rᵢ s_f ∏_{j ≠ i} sⱼ`. -/
def limitedCritN (rf sf : CPoly R) (ηs : List (CPoly R × CPoly R)) : Option (List R) :=
  linSolve ((clearedNum ηs).map (mul sf)) (mul rf (prodDen ηs))

lemma lcomb_map_mul (m : CPoly R) (cs : List R) (vs : List (CPoly R)) :
    lcomb cs (vs.map (mul m)) = toPoly m * lcomb cs vs := by
  induction cs generalizing vs with
  | nil => simp [lcomb]
  | cons c cs ih =>
    cases vs with
    | nil => simp [lcomb]
    | cons v vs =>
      have := ih vs
      simp only [lcomb, List.map_cons, List.zipWith_cons_cons, List.sum_cons, toPoly_mul] at this ⊢
      rw [this]
      ring

/-- The cleared identity is the fraction identity multiplied by `∏ sᵢ`. -/
lemma lcomb_clearedNum {F : Type*} [Field F] [Algebra R[X] F] (cs : List R)
    (ηs : List (CPoly R × CPoly R))
    (hs : ∀ η ∈ ηs, algebraMap R[X] F (toPoly η.2) ≠ 0) :
    algebraMap R[X] F (lcomb cs (clearedNum ηs)) =
      (List.zipWith (fun c (η : CPoly R × CPoly R) ↦ algebraMap R[X] F (C c) *
        (algebraMap R[X] F (toPoly η.1) / algebraMap R[X] F (toPoly η.2))) cs ηs).sum *
        algebraMap R[X] F (toPoly (prodDen ηs)) := by
  induction cs generalizing ηs with
  | nil => simp [lcomb]
  | cons c cs ih =>
    cases ηs with
    | nil => simp [lcomb, clearedNum]
    | cons η ηs =>
      have h1 := hs η (List.mem_cons_self ..)
      have := ih ηs fun η' hη' ↦ hs η' (List.mem_cons_of_mem _ hη')
      have hl := lcomb_map_mul η.2 cs (clearedNum ηs)
      simp only [lcomb, clearedNum, prodDen, List.zipWith_cons_cons, List.sum_cons, toPoly_mul,
        map_add, map_mul] at this hl ⊢
      rw [hl, map_mul, this]
      field_simp

theorem limitedCritN_sound {rf sf : CPoly R} {ηs : List (CPoly R × CPoly R)} {cs : List R}
    (h : limitedCritN rf sf ηs = some cs) :
    cs.length = ηs.length ∧
      toPoly rf * toPoly (prodDen ηs) = toPoly sf * lcomb cs (clearedNum ηs) := by
  obtain ⟨hl, hc⟩ := linSolve_sound _ _ _ h
  rw [lcomb_map_mul, toPoly_mul] at hc
  refine ⟨?_, hc.symm⟩
  rw [hl, List.length_map]
  clear hl hc h
  induction ηs with
  | nil => rfl
  | cons η ηs ih => simp [clearedNum, ih]

lemma lcombS_map_mul (ι : R →+* S) (m : CPoly R) (cs : List S) (vs : List (CPoly R)) :
    lcombS ι cs (vs.map (mul m)) = (toPoly m).map ι * lcombS ι cs vs := by
  induction cs generalizing vs with
  | nil => simp [lcombS]
  | cons c cs ih =>
    cases vs with
    | nil => simp [lcombS]
    | cons v vs =>
      have := ih vs
      simp only [lcombS, List.map_cons, List.zipWith_cons_cons, List.sum_cons, toPoly_mul,
        Polynomial.map_mul] at this ⊢
      rw [this]
      ring

lemma length_clearedNum (ηs : List (CPoly R × CPoly R)) :
    (clearedNum ηs).length = ηs.length := by
  induction ηs with
  | nil => rfl
  | cons η ηs ih => simp [clearedNum, ih]

/-- **Completeness**: constants in any extension of the constant field force success. -/
theorem limitedCritN_complete_map (ι : R →+* S) {rf sf : CPoly R}
    {ηs : List (CPoly R × CPoly R)} (cs : List S) (hl : cs.length = ηs.length)
    (h : (toPoly rf).map ι * (toPoly (prodDen ηs)).map ι =
      (toPoly sf).map ι * lcombS ι cs (clearedNum ηs)) :
    limitedCritN rf sf ηs ≠ none := by
  refine linSolve_complete_map ι _ _ cs ?_ ?_
  · rw [List.length_map, length_clearedNum, hl]
  · rw [lcombS_map_mul, toPoly_mul, Polynomial.map_mul, h]

-- `1/x + 2/(x+1) = c₁ · 1/x + c₂ · 1/(x+1)`: numerator `3x + 1`, denominator `x² + x`
#eval limitedCritN (R := ℚ) [1, 3] [0, 1, 1] [([1], [0, 1]), ([1], [1, 1])]
-- `1/(x+2)` is not a combination of `1/x`, `1/(x+1)`
#eval limitedCritN (R := ℚ) [1] [2, 1] [([1], [0, 1]), ([1], [1, 1])]

end CPoly
