import RischTragerBronstein.Computable.PrimPoly
import RischTragerBronstein.Computable.LimitedCritNDecide

/-!
# Limited integration inside `R(x)(t₁)`: the executable recursion

Problem: for `A = ∑_{j ≤ d} aⱼ(x) t₁ ^ j` (`t₁′ = η₁`) and `η₂ ∈ R(x)`, find a constant `c` and
`P ∈ R(x)[t₁]` with `P′ = A - c η₂`. By `coeffs_of_deriv_in_primitive` this is

  `pⱼ′ + (j + 1) η₁ pⱼ₊₁ = aⱼ - [j = 0] c η₂`,  `j ≥ 0`.

Levels `j ≥ 1` are the one-parameter loop `primLoop`; level `0` is the two-parameter problem
`a₀ - η₁ Q₁ = p₀′ + b η₁ + c η₂`, solved by `limitedCritN`.

`limitedPrim_complete`: if the coefficient equations have a solution over **any** extension of the
constants, the procedure succeeds.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R S K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K] [Algebra S[X] K] [IsFractionRing S[X] K]
variable [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

/-- Returns the constants `(b, c)` of level `0`: `a₀ - η₁ Q₁ = p₀′ + b η₁ + c η₂`. -/
def limitedPrim (En Ed : CPoly R) (Iη₁ Iη₂ : RationalIntegral R) (A D : ℕ → CPoly R) (d : ℕ) :
    Option (List R) :=
  match primLoop En Ed Iη₁ A D d ([], [1]) with
  | none => none
  | some L =>
    let g := primG En Ed 0 (A 0) (D 0) (primLastQ ([], [1]) L)
    let I := integrateRational g.1 g.2
    limitedCritN I.r I.s [(Iη₁.r, Iη₁.s), (Iη₂.r, Iη₂.s)]

theorem limitedPrim_complete (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (hKconst : ∀ y : K, y′ = 0 → ∃ b : S, y = φ (C b))
    {En Ed En₂ Ed₂ : CPoly R} {Iη₁ Iη₂ : RationalIntegral R}
    (hcη₁ : rationalCheck En Ed Iη₁ = true) (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true)
    (hEd : toPoly Ed ≠ 0) (hη0 : isZero Iη₁.r = false) (A D : ℕ → CPoly R) (d : ℕ)
    (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) (p : ℕ → K) (c : S)
    (hp : ∀ j, 1 ≤ j → j ≤ d →
      (p j)′ + ((j + 1 : ℕ) : K) * ev K ι (En, Ed) * p (j + 1) = ev K ι (A j, D j))
    (hp0 : (p 0)′ + ev K ι (En, Ed) * p 1 = ev K ι (A 0, D 0) - φ (C c) * ev K ι (En₂, Ed₂))
    (hpd : (p (d + 1))′ = 0) :
    limitedPrim En Ed Iη₁ Iη₂ A D d ≠ none := by
  obtain ⟨b₀, hb₀⟩ := hKconst _ hpd
  obtain ⟨L, hL, hlast, b, hb⟩ := primLoop_complete_last (K := K) ι hD hKconst hcη₁ hEd hη0 A D p d
    (fun j _ hj ↦ hD0 j hj) hp ([], [1]) (by simp) b₀ (by rw [hb₀]; simp [ev])
  simp only [limitedPrim, hL]
  set Q₁ := primLastQ ([], [1]) L with hQ₁
  obtain ⟨hg0, hg⟩ := ev_primG (K := K) ι (En := En) (An := A 0) 0 hEd (hD0 0 (Nat.zero_le d)) hlast
  set g := primG En Ed 0 (A 0) (D 0) Q₁ with hgdef
  set I := integrateRational g.1 g.2 with hI
  have hIc : rationalCheck g.1 g.2 I = true := rationalCheck_integrateRational _ _ hg0
  obtain ⟨hdecI, hsqI, hdegI⟩ := rationalCheck_sound_map (K := K) ι hD g.1 g.2 I hIc
  obtain ⟨hdec₁, hsq₁, hdeg₁⟩ := rationalCheck_sound_map (K := K) ι hD En Ed Iη₁ hcη₁
  obtain ⟨hdec₂, hsq₂, hdeg₂⟩ := rationalCheck_sound_map (K := K) ι hD En₂ Ed₂ Iη₂ hcη₂
  intro hnone
  -- `p₀′ = g - b η₁ - c η₂`
  refine limitedCritN_none (K := K) ι hD hsqI hdegI (ηs := [(Iη₁.r, Iη₁.s), (Iη₂.r, Iη₂.s)])
    (fun η hη ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hη
      rcases hη with rfl | rfl
      · exact ⟨hsq₁, hdeg₁⟩
      · exact ⟨hsq₂, hdeg₂⟩) hnone
    (φ ((toPoly I.gn).map ι) / φ ((toPoly I.gd).map ι) + φ ((toPoly I.Q).map ι))
    (fun i ↦ if (i : ℕ) = 0 then
        φ ((toPoly Iη₁.gn).map ι) / φ ((toPoly Iη₁.gd).map ι) + φ ((toPoly Iη₁.Q).map ι)
      else φ ((toPoly Iη₂.gn).map ι) / φ ((toPoly Iη₂.gd).map ι) + φ ((toPoly Iη₂.Q).map ι))
    (fun i ↦ if (i : ℕ) = 0 then b else c) (p 0) ?_
  have hgE : ev K ι (g.1, g.2) = ev K ι g := rfl
  simp only [ev] at hgE hg hp0 hb hdecI hdec₁ hdec₂
  erw [Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false,
    List.getElem_cons_zero, List.getElem_cons_succ, Fin.getElem_fin]
  rw [← hdecI, ← hdec₁, ← hdec₂, hg]
  rw [hb] at hp0
  simp only [Nat.cast_one, Nat.cast_zero, zero_add, one_mul]
  linear_combination hp0

/-- The coefficients produced by the loop: for any prescribed constant `b₁`, there are `pⱼ` solving
the equations of levels `1 … k` with `p₁ = Q₁ + b₁` and `pₖ₊₁ = Q + const`. -/
theorem primLoop_coeffs (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {En Ed : CPoly R} {Iη : RationalIntegral R} (hcη : rationalCheck En Ed Iη = true)
    (hEd : toPoly Ed ≠ 0) (A D : ℕ → CPoly R) (k : ℕ)
    (hD0 : ∀ j, 1 ≤ j → j ≤ k → toPoly (D j) ≠ 0) (Q : CPoly R × CPoly R)
    (hQ : toPoly Q.2 ≠ 0) {L : List (R × (CPoly R × CPoly R))}
    (hL : primLoop En Ed Iη A D k Q = some L) (b₁ : S) :
    ∃ (p : ℕ → K) (γ : S), p (k + 1) = ev K ι Q + φ (C γ) ∧
      (∀ j, 1 ≤ j → j ≤ k →
        (p j)′ + ((j + 1 : ℕ) : K) * ev K ι (En, Ed) * p (j + 1) = ev K ι (A j, D j)) ∧
      p 1 = ev K ι (primLastQ Q L) + φ (C b₁) := by
  induction k generalizing Q L with
  | zero =>
    simp only [primLoop, Option.some.injEq] at hL
    subst hL
    exact ⟨fun _ ↦ ev K ι Q + φ (C b₁), b₁, rfl, fun j h1 h2 ↦ by omega, rfl⟩
  | succ k ih =>
    simp only [primLoop] at hL
    cases hstep : primStep En Ed Iη (k + 1) (A (k + 1)) (D (k + 1)) Q with
    | none => rw [hstep] at hL; exact absurd hL (by simp)
    | some cQ =>
      obtain ⟨c, Q'⟩ := cQ
      rw [hstep] at hL
      simp only [Option.map_eq_some_iff] at hL
      obtain ⟨L', hL', rfl⟩ := hL
      obtain ⟨hQ', hsol⟩ := primStep_sound (K := K) ι hD hcη hEd (hD0 (k + 1) (by omega) le_rfl)
        hQ hstep
      obtain ⟨p, γ', hpk, hpe, hp1⟩ := ih (fun j h1 h2 ↦ hD0 j h1 (by omega)) Q' hQ' hL'
      set γ : S := ι c / ((k + 1 + 1 : ℕ) : S) with hγ
      have hγc : ((k + 1 + 1 : ℕ) : K) * φ (C γ) = φ (C (ι c)) := by
        have hn : (((k + 1 + 1 : ℕ) : K)) = φ (C (((k + 1 + 1 : ℕ) : S))) := by
          rw [map_natCast (C : S →+* S[X]), map_natCast]
        rw [hn, ← map_mul, ← C_mul, hγ,
          mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega) : (((k + 1 + 1 : ℕ) : S)) ≠ 0)]
      have hcγ' : (φ (C γ'))′ = 0 := by rw [deriv_algebraMap, hD, derivative_C, map_zero]
      refine ⟨Function.update p (k + 1 + 1) (ev K ι Q + φ (C γ)), γ, by simp, ?_, ?_⟩
      · intro j h1 h2
        rcases Nat.eq_or_lt_of_le h2 with rfl | hlt
        · rw [Function.update_of_ne (by omega), Function.update_self, hpk, map_add, hcγ',
            add_zero, hsol]
          linear_combination ev K ι (En, Ed) * hγc
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hpe j h1 (by omega)
      · rw [Function.update_of_ne (by omega)]
        exact hp1

/-- **Soundness.** If `limitedPrim` returns `[b, c]`, the coefficient equations of
`P′ = A - c η₂` are solvable in `S(x)`, for every extension `S` of the constants. -/
theorem limitedPrim_sound (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {En Ed En₂ Ed₂ : CPoly R} {Iη₁ Iη₂ : RationalIntegral R}
    (hcη₁ : rationalCheck En Ed Iη₁ = true) (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true)
    (hEd : toPoly Ed ≠ 0) (A D : ℕ → CPoly R) (d : ℕ)
    (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) {cs : List R}
    (h : limitedPrim En Ed Iη₁ Iη₂ A D d = some cs) :
    ∃ p : ℕ → K, (∀ j, 1 ≤ j → j ≤ d →
        (p j)′ + ((j + 1 : ℕ) : K) * ev K ι (En, Ed) * p (j + 1) = ev K ι (A j, D j)) ∧
      (p 0)′ + ev K ι (En, Ed) * p 1 =
        ev K ι (A 0, D 0) - φ (C (ι (cs.getD 1 0))) * ev K ι (En₂, Ed₂) ∧
      (p (d + 1))′ = 0 := by
  simp only [limitedPrim] at h
  cases hL : primLoop En Ed Iη₁ A D d ([], [1]) with
  | none => rw [hL] at h; exact absurd h (by simp)
  | some L =>
    rw [hL] at h
    simp only at h
    obtain ⟨p, γ, hpd, hpe, hp1⟩ := primLoop_coeffs (K := K) ι hD hcη₁ hEd A D d
      (fun j _ hj ↦ hD0 j hj) ([], [1]) (by simp) hL (ι (cs.getD 0 0))
    -- the last fraction has a nonzero denominator
    have hlast : toPoly (primLastQ ([], [1]) L).2 ≠ 0 := by
      have : ∀ (k : ℕ) (Q : CPoly R × CPoly R) (L : List (R × (CPoly R × CPoly R))),
          (∀ j, 1 ≤ j → j ≤ k → toPoly (D j) ≠ 0) → toPoly Q.2 ≠ 0 →
          primLoop En Ed Iη₁ A D k Q = some L → toPoly (primLastQ Q L).2 ≠ 0 := by
        intro k
        induction k with
        | zero =>
          intro Q L _ hQ hL
          simp only [primLoop, Option.some.injEq] at hL
          subst hL
          exact hQ
        | succ k ih =>
          intro Q L hD0' hQ hL
          simp only [primLoop] at hL
          cases hstep : primStep En Ed Iη₁ (k + 1) (A (k + 1)) (D (k + 1)) Q with
          | none => rw [hstep] at hL; exact absurd hL (by simp)
          | some cQ =>
            rw [hstep] at hL
            simp only [Option.map_eq_some_iff] at hL
            obtain ⟨L', hL', rfl⟩ := hL
            obtain ⟨hQ', -⟩ := primStep_sound (K := K) ι hD hcη₁ hEd
              (hD0' (k + 1) (by omega) le_rfl) hQ (c := cQ.1) (Q' := cQ.2) hstep
            exact ih cQ.2 L' (fun j h1 h2 ↦ hD0' j h1 (by omega)) hQ' hL'
      exact this d _ L (fun j _ hj ↦ hD0 j hj) (by simp) hL
    set Q₁ := primLastQ ([], [1]) L with hQ₁
    obtain ⟨hg0, hg⟩ := ev_primG (K := K) ι (En := En) (An := A 0) 0 hEd (hD0 0 (Nat.zero_le d))
      hlast
    set g := primG En Ed 0 (A 0) (D 0) Q₁ with hgdef
    set I := integrateRational g.1 g.2 with hI
    have hIc : rationalCheck g.1 g.2 I = true := rationalCheck_integrateRational _ _ hg0
    obtain ⟨hdecI, hsqI, hdegI⟩ := rationalCheck_sound_map (K := K) ι hD g.1 g.2 I hIc
    obtain ⟨hdec₁, hsq₁, hdeg₁⟩ := rationalCheck_sound_map (K := K) ι hD En Ed Iη₁ hcη₁
    obtain ⟨hdec₂, hsq₂, hdeg₂⟩ := rationalCheck_sound_map (K := K) ι hD En₂ Ed₂ Iη₂ hcη₂
    obtain ⟨y, hy⟩ := limitedCritN_some (K := K) ι hD hsqI hdegI
      (ηs := [(Iη₁.r, Iη₁.s), (Iη₂.r, Iη₂.s)])
      (fun η hη ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hη
        rcases hη with rfl | rfl
        · exact ⟨hsq₁, hdeg₁⟩
        · exact ⟨hsq₂, hdeg₂⟩) h
      (φ ((toPoly I.gn).map ι) / φ ((toPoly I.gd).map ι) + φ ((toPoly I.Q).map ι))
      (fun i ↦ if (i : ℕ) = 0 then
          φ ((toPoly Iη₁.gn).map ι) / φ ((toPoly Iη₁.gd).map ι) + φ ((toPoly Iη₁.Q).map ι)
        else φ ((toPoly Iη₂.gn).map ι) / φ ((toPoly Iη₂.gd).map ι) + φ ((toPoly Iη₂.Q).map ι))
    erw [Fin.sum_univ_two] at hy
    have hgE : ev K ι (g.1, g.2) = ev K ι g := rfl
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false,
      List.getElem_cons_zero, List.getElem_cons_succ, Fin.getElem_fin] at hy
    have hγ0 : (φ (C γ))′ = 0 := by rw [deriv_algebraMap, hD, derivative_C, map_zero]
    refine ⟨Function.update p 0 y, fun j h1 h2 ↦ ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hpe j h1 h2
    · rw [Function.update_self, Function.update_of_ne (by omega), hp1, hy]
      simp only [ev] at hgE hg hdecI hdec₁ hdec₂ ⊢
      rw [← hdecI, ← hdec₁, ← hdec₂, hg]
      simp only [Nat.cast_one, Nat.cast_zero, zero_add, one_mul]
      ring
    · rw [Function.update_of_ne (by omega), hpd]
      simp [ev, hγ0]

end CPoly

namespace CPoly

-- `t₁ = log x`, `η₂ = 1 / (x + 1)`.
-- `A = t₁ / x`: `P = t₁² / 2`, constants `(b, c) = (0, 0)`
#eval limitedPrim (R := ℚ) [1] [0, 1] (integrateRational [1] [0, 1])
  (integrateRational [1] [1, 1]) (fun j ↦ if j = 1 then [1] else []) (fun j ↦ if j = 1 then [0, 1] else [1]) 1
-- `A = 3 / (x + 1) + 2 / x`: `(b, c) = (2, 3)`
#eval limitedPrim (R := ℚ) [1] [0, 1] (integrateRational [1] [0, 1])
  (integrateRational [1] [1, 1]) (fun _ ↦ [2, 5]) (fun _ ↦ [0, 1, 1]) 0
-- `A = 1 / (x + 2)`: impossible
#eval limitedPrim (R := ℚ) [1] [0, 1] (integrateRational [1] [0, 1])
  (integrateRational [1] [1, 1]) (fun _ ↦ [1]) (fun _ ↦ [2, 1]) 0

end CPoly
