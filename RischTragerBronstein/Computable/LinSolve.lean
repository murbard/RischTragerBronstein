import RischTragerBronstein.Computable.RDEPoly
import RischTragerBronstein.Computable.EuclidDegree

/-!
# A verified linear solver over the constants

`CPoly.linSolve vs w` finds constants `cᵢ` with `w = ∑ cᵢ vᵢ` (polynomials as coefficient vectors),
by elimination on leading terms.

* `linSolve_sound`: a returned list solves the system;
* `linSolve_complete_map`: `none` means there is no solution over **any** extension of the
  constants (linear systems do not acquire solutions under field extension).

This is the base of parametric problems (limited integration with several parameters).
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R S : Type*} [Field R] [DecidableEq R] [Field S]

/-- `∑ cᵢ vᵢ`. -/
noncomputable def lcomb (cs : List R) (vs : List (CPoly R)) : R[X] :=
  (List.zipWith (fun c v ↦ C c * toPoly v) cs vs).sum

/-- `∑ cᵢ vᵢ` with coefficients in an extension. -/
noncomputable def lcombS (ι : R →+* S) (cs : List S) (vs : List (CPoly R)) : S[X] :=
  (List.zipWith (fun c v ↦ C c * (toPoly v).map ι) cs vs).sum

/-- Remove the `x ^ d` term of `u` using `v` (whose `x ^ d` coefficient is `lc`). -/
def elim (v : CPoly R) (d : ℕ) (lc : R) (u : CPoly R) : CPoly R :=
  sub u (smul (u.getD d 0 / lc) v)

/-- The elimination with fuel (structural recursion, so that the kernel can evaluate it; irreducible
for the elaborator, like the well-founded original). -/
def linSolveF : ℕ → List (CPoly R) → CPoly R → Option (List R)
  | _, [], w => if isZero w then some [] else none
  | 0, _ :: _, _ => none
  | n + 1, v :: vs, w =>
    if isZero v then (linSolveF n vs w).map (0 :: ·)
    else
      let d := (trim v).length - 1
      let lc := lead (trim v)
      match linSolveF n (vs.map (elim v d lc)) (elim v d lc w) with
      | none => none
      | some cs =>
        some ((w.getD d 0 / lc -
          (List.zipWith (fun c u ↦ c * (u.getD d 0 / lc)) cs vs).sum) :: cs)

/-- Solve `w = ∑ cᵢ vᵢ` for constants `cᵢ` (fuel `vs.length` suffices: each step drops one vector). -/
def linSolve (vs : List (CPoly R)) (w : CPoly R) : Option (List R) :=
  linSolveF vs.length vs w

lemma linSolve_nil (w : CPoly R) :
    linSolve ([] : List (CPoly R)) w = if isZero w then some [] else none := by
  simp [linSolve, linSolveF]

lemma linSolve_cons (v : CPoly R) (vs : List (CPoly R)) (w : CPoly R) :
    linSolve (v :: vs) w =
      if isZero v then (linSolve vs w).map (0 :: ·)
      else
        let d := (trim v).length - 1
        let lc := lead (trim v)
        match linSolve (vs.map (elim v d lc)) (elim v d lc w) with
        | none => none
        | some cs =>
          some ((w.getD d 0 / lc -
            (List.zipWith (fun c u ↦ c * (u.getD d 0 / lc)) cs vs).sum) :: cs) := by
  simp only [linSolve, List.length_cons, List.length_map, linSolveF]

attribute [irreducible] linSolveF linSolve

lemma toPoly_elim (v : CPoly R) (d : ℕ) (lc : R) (u : CPoly R) :
    toPoly (elim v d lc u) = toPoly u - C (u.getD d 0 / lc) * toPoly v := by
  rw [elim, toPoly_sub, toPoly_smul]

lemma lcomb_elim (v : CPoly R) (d : ℕ) (lc : R) (cs : List R) (vs : List (CPoly R)) :
    lcomb cs (vs.map (elim v d lc)) =
      lcomb cs vs - C (List.zipWith (fun c u ↦ c * (u.getD d 0 / lc)) cs vs).sum * toPoly v := by
  induction cs generalizing vs with
  | nil => simp [lcomb]
  | cons c cs ih =>
    cases vs with
    | nil => simp [lcomb]
    | cons u us =>
      have := ih us
      simp only [lcomb, List.map_cons, List.zipWith_cons_cons, List.sum_cons, toPoly_elim] at this ⊢
      rw [this, C_add, C_mul]
      ring

theorem linSolve_sound : ∀ (vs : List (CPoly R)) (w : CPoly R) (cs : List R),
    linSolve vs w = some cs → cs.length = vs.length ∧ lcomb cs vs = toPoly w
  | [], w, cs, h => by
    rw [linSolve_nil] at h
    split_ifs at h with hz
    rw [← Option.some.inj h]
    exact ⟨rfl, by simp [lcomb, (isZero_iff _).mp hz]⟩
  | v :: vs, w, cs, h => by
    rw [linSolve_cons] at h
    split_ifs at h with hz
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨cs', hcs', rfl⟩ := h
      obtain ⟨hl, hc⟩ := linSolve_sound vs w cs' hcs'
      refine ⟨by simp [hl], ?_⟩
      simp only [lcomb, List.zipWith_cons_cons, List.sum_cons, (isZero_iff _).mp hz, mul_zero,
        zero_add]
      exact hc
    · simp only at h
      cases hrec : linSolve (vs.map (elim v ((trim v).length - 1) (lead (trim v))))
          (elim v ((trim v).length - 1) (lead (trim v)) w) with
      | none => rw [hrec] at h; exact absurd h (by simp)
      | some cs' =>
        rw [hrec] at h
        simp only [Option.some.injEq] at h
        obtain ⟨hl, hc⟩ := linSolve_sound _ _ cs' hrec
        rw [List.length_map] at hl
        rw [lcomb_elim, toPoly_elim] at hc
        rw [← h]
        refine ⟨by simp [hl], ?_⟩
        simp only [lcomb, List.zipWith_cons_cons, List.sum_cons] at hc ⊢
        rw [C_sub]
        linear_combination hc
termination_by vs => vs.length
decreasing_by all_goals simp

section Complete

variable (ι : R →+* S)

lemma lcombS_elim (v : CPoly R) (d : ℕ) (lc : R) (cs : List S) (vs : List (CPoly R)) :
    lcombS ι cs (vs.map (elim v d lc)) = lcombS ι cs vs -
      C (List.zipWith (fun c u ↦ c * ι (u.getD d 0 / lc)) cs vs).sum * (toPoly v).map ι := by
  induction cs generalizing vs with
  | nil => simp [lcombS]
  | cons c cs ih =>
    cases vs with
    | nil => simp [lcombS]
    | cons u us =>
      have := ih us
      simp only [lcombS, List.map_cons, List.zipWith_cons_cons, List.sum_cons, toPoly_elim,
        Polynomial.map_sub, Polynomial.map_mul, map_C] at this ⊢
      rw [this, C_add, C_mul]
      ring

lemma coeff_elim {v : CPoly R} {d : ℕ} {lc : R} (hv : (toPoly v).coeff d = lc) (hlc : lc ≠ 0)
    (u : CPoly R) : (toPoly (elim v d lc u)).coeff d = 0 := by
  rw [toPoly_elim, coeff_sub, coeff_C_mul, hv, coeff_toPoly]
  field_simp
  ring

lemma coeff_lcombS_elim {v : CPoly R} {d : ℕ} {lc : R} (hv : (toPoly v).coeff d = lc)
    (hlc : lc ≠ 0) (cs : List S) (vs : List (CPoly R)) :
    (lcombS ι cs (vs.map (elim v d lc))).coeff d = 0 := by
  induction cs generalizing vs with
  | nil => simp [lcombS]
  | cons c cs ih =>
    cases vs with
    | nil => simp [lcombS]
    | cons u us =>
      have := ih us
      simp only [lcombS, List.map_cons, List.zipWith_cons_cons, List.sum_cons, coeff_add,
        coeff_C_mul, coeff_map] at this ⊢
      rw [this, coeff_elim hv hlc, map_zero, mul_zero, add_zero]

/-- **Completeness over extensions of the constants.** -/
theorem linSolve_complete_map : ∀ (vs : List (CPoly R)) (w : CPoly R) (cs : List S),
    cs.length = vs.length → lcombS ι cs vs = (toPoly w).map ι → linSolve vs w ≠ none
  | [], w, cs, _, h => by
    have hw : toPoly w = 0 := by
      rw [← Polynomial.map_eq_zero_iff ι.injective, ← h]
      cases cs <;> simp [lcombS]
    rw [linSolve_nil, if_pos ((isZero_iff _).mpr hw)]
    exact Option.some_ne_none _
  | v :: vs, w, [], hl, _ => by simp at hl
  | v :: vs, w, c₀ :: cs, hl, h => by
    have hl' : cs.length = vs.length := by simpa using hl
    rw [linSolve_cons]
    split_ifs with hz
    · have hv0 := (isZero_iff _).mp hz
      simp only [lcombS, List.zipWith_cons_cons, List.sum_cons, hv0, Polynomial.map_zero,
        mul_zero, zero_add] at h
      have := linSolve_complete_map vs w cs hl' h
      intro hn
      rw [Option.map_eq_none_iff] at hn
      exact this hn
    · have hvne : trim v ≠ [] := fun h0 ↦ hz ((isZero_iff _).mpr ((trim_eq_nil_iff v).mp h0))
      obtain ⟨-, hvd, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil hvne
      set d := (trim v).length - 1
      set lc := lead (trim v)
      -- the reduced system is solvable over `S`
      have hred : lcombS ι cs (vs.map (elim v d lc)) = (toPoly (elim v d lc w)).map ι := by
        set σ := (List.zipWith (fun c u ↦ c * ι (u.getD d 0 / lc)) cs vs).sum with hσ
        have hdiff : (toPoly (elim v d lc w)).map ι - lcombS ι cs (vs.map (elim v d lc)) =
            C (c₀ - ι (w.getD d 0 / lc) + σ) * (toPoly v).map ι := by
          rw [lcombS_elim, toPoly_elim, Polynomial.map_sub, Polynomial.map_mul, map_C, ← h]
          simp only [lcombS, List.zipWith_cons_cons, List.sum_cons, C_add, C_sub]
          ring
        have hco := congrArg (fun P : S[X] ↦ P.coeff d) hdiff
        simp only [coeff_sub, coeff_C_mul, coeff_map, coeff_elim hvd hlc0,
          coeff_lcombS_elim ι hvd hlc0, map_zero, sub_zero, hvd] at hco
        have hκ : c₀ - ι (w.getD d 0 / lc) + σ = 0 :=
          (mul_eq_zero.mp hco.symm).resolve_right ((map_ne_zero ι).mpr hlc0)
        rw [hκ, C_0, zero_mul, sub_eq_zero] at hdiff
        exact hdiff.symm
      have := linSolve_complete_map (vs.map (elim v d lc)) (elim v d lc w) cs
        (by rw [List.length_map]; exact hl') hred
      simp only
      cases hrec : linSolve (vs.map (elim v d lc)) (elim v d lc w) with
      | none => exact absurd hrec this
      | some cs' => exact Option.some_ne_none _
termination_by vs => vs.length
decreasing_by all_goals simp

end Complete

-- `x² + 3x + 2 = c₁ (x + 1) + c₂ (x² + x) + c₃ · 1` : `c = (2, 1, 0)`
#eval linSolve (R := ℚ) [[1, 1], [0, 1, 1], [1]] [2, 3, 1]
-- `x² ∉ span (1, x)`
#eval linSolve (R := ℚ) [[1], [0, 1]] [0, 0, 1]
-- the kernel evaluates it
example : linSolve (R := ℚ) [[1, 1], [0, 1, 1], [1]] [2, 3, 1] = some [2, 1, 0] := by decide +kernel

end CPoly
