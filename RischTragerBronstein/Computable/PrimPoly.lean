import RischTragerBronstein.Computable.PrimTimesPositive
import RischTragerBronstein.Computable.RationalComplete

/-!
# Polynomials in a primitive `t` over `R(x)`: the recursive limited-integration loop

For an integrand `∑_{j ≤ d} fⱼ(x) t ^ j`, `t′ = η(x)` (e.g. `t = log b(x)`), an antiderivative must be
`∑ Pⱼ t ^ j + …` with `Pₖ′ + (k + 1) η Pₖ₊₁ = fₖ` for `k ≥ 1`. Each `Pₖ₊₁` is known up to an additive
constant, `Pₖ₊₁ = Qₖ₊₁ + b`, so level `k` is the **limited integration problem**
`fₖ - (k + 1) η Qₖ₊₁ = Qₖ′ + c η`, solved by `integrateRational` and `limitedCrit`.

* `primStep`: one level; `primLoop`: all levels `k, k - 1, …, 1`.
* `primStep_sound`: the returned `(c, Q')` satisfies `Q'′ = fₖ - (k + 1) η Q - c η`.
* `primStep_complete`, `primLoop_complete`: if the coefficient equations have a solution over any
  extension of the constants, the loop succeeds.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- `G_I - c G_η` as a fraction, where `G_I = I.gn / I.gd + I.Q`. -/
def limitedSol (I Iη : RationalIntegral R) (c : R) : CPoly R × CPoly R :=
  (sub (mul (add I.gn (mul I.Q I.gd)) Iη.gd) (smul c (mul (add Iη.gn (mul Iη.Q Iη.gd)) I.gd)),
    mul I.gd Iη.gd)

/-- The fraction `f - (k + 1) η Q`, `f = An / Ad`, `η = En / Ed`. -/
def primG (En Ed : CPoly R) (k : ℕ) (An Ad : CPoly R) (Q : CPoly R × CPoly R) :
    CPoly R × CPoly R :=
  (sub (mul (mul An Q.2) Ed) (smul ((k + 1 : ℕ) : R) (mul (mul En Q.1) Ad)), mul (mul Ad Q.2) Ed)

/-- One level of the loop: solve `f - (k + 1) η Q = Q'′ + c η` for a constant `c` and `Q' ∈ R(x)`. -/
def primStep (En Ed : CPoly R) (Iη : RationalIntegral R) (k : ℕ) (An Ad : CPoly R)
    (Q : CPoly R × CPoly R) : Option (R × (CPoly R × CPoly R)) :=
  let g := primG En Ed k An Ad Q
  let I := integrateRational g.1 g.2
  match limitedCrit I.r I.s Iη.r Iη.s with
  | none => none
  | some c => some (c, limitedSol I Iη c)

/-- Levels `k, k - 1, …, 1`, starting from `Q = Qₖ₊₁`. -/
def primLoop (En Ed : CPoly R) (Iη : RationalIntegral R) (A D : ℕ → CPoly R) :
    ℕ → CPoly R × CPoly R → Option (List (R × (CPoly R × CPoly R)))
  | 0, _ => some []
  | k + 1, Q =>
    match primStep En Ed Iη (k + 1) (A (k + 1)) (D (k + 1)) Q with
    | none => none
    | some cQ => (primLoop En Ed Iη A D k cQ.2).map (cQ :: ·)

end Defs

variable {R S K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K] [Algebra S[X] K] [IsFractionRing S[X] K]
variable [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

variable (K) in
/-- The value of a fraction in a model `K` of `S(x)`. -/
noncomputable def ev (ι : R →+* S) (q : CPoly R × CPoly R) : K :=
  φ ((toPoly q.1).map ι) / φ ((toPoly q.2).map ι)

lemma map_toPoly_ne_zero (ι : R →+* S) {p : CPoly R} (hp : toPoly p ≠ 0) :
    φ ((toPoly p).map ι) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective S[X] K)).mpr
    ((Polynomial.map_ne_zero_iff ι.injective).mpr hp)

lemma gd_ne_zero_of_rationalCheck {A D : CPoly R} {I : RationalIntegral R}
    (h : rationalCheck A D I = true) : toPoly I.gd ≠ 0 := by
  rw [rationalCheck, Bool.and_eq_true] at h
  exact ((hermiteCheck_iff _ _ _).mp h.1).2.1

lemma ev_primG (ι : R →+* S) {En Ed An Ad : CPoly R} {Q : CPoly R × CPoly R} (k : ℕ)
    (hEd : toPoly Ed ≠ 0) (hAd : toPoly Ad ≠ 0) (hQ : toPoly Q.2 ≠ 0) :
    toPoly (primG En Ed k An Ad Q).2 ≠ 0 ∧
      ev K ι (primG En Ed k An Ad Q) =
        ev K ι (An, Ad) - ((k + 1 : ℕ) : K) * ev K ι (En, Ed) * ev K ι Q := by
  refine ⟨by simp only [primG, toPoly_mul]; exact mul_ne_zero (mul_ne_zero hAd hQ) hEd, ?_⟩
  have h1 := map_toPoly_ne_zero (K := K) ι hEd
  have h2 := map_toPoly_ne_zero (K := K) ι hAd
  have h3 := map_toPoly_ne_zero (K := K) ι hQ
  have hcast : φ (C (ι ((k + 1 : ℕ) : R))) = ((k + 1 : ℕ) : K) := by
    rw [map_natCast ι, map_natCast (C : S →+* S[X]), map_natCast]
  simp only [ev, primG, toPoly_sub, toPoly_mul, toPoly_smul, Polynomial.map_sub,
    Polynomial.map_mul, map_C, map_sub, map_mul, hcast]
  field_simp

/-- The derivative of `limitedSol`. -/
lemma deriv_ev_limitedSol (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {gn gd En Ed : CPoly R} {I Iη : RationalIntegral R}
    (hI : rationalCheck gn gd I = true) (hcη : rationalCheck En Ed Iη = true) {c : R}
    (hcross : toPoly I.r * toPoly Iη.s = C c * toPoly Iη.r * toPoly I.s) :
    toPoly (limitedSol I Iη c).2 ≠ 0 ∧
      (ev K ι (limitedSol I Iη c))′ = ev K ι (gn, gd) - φ (C (ι c)) * ev K ι (En, Ed) := by
  have hgI := gd_ne_zero_of_rationalCheck hI
  have hgη := gd_ne_zero_of_rationalCheck hcη
  refine ⟨by simp only [limitedSol, toPoly_mul]; exact mul_ne_zero hgI hgη, ?_⟩
  obtain ⟨hdecI, hsqI, -⟩ := rationalCheck_sound_map (K := K) ι hD gn gd I hI
  obtain ⟨hdecη, hsqη, -⟩ := rationalCheck_sound_map (K := K) ι hD En Ed Iη hcη
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have h1 := map_toPoly_ne_zero (K := K) ι hgI
  have h2 := map_toPoly_ne_zero (K := K) ι hgη
  have h3 : φ ((toPoly I.s).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsqI.ne_zero
  have h4 : φ ((toPoly Iη.s).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsqη.ne_zero
  have hrs : φ ((toPoly I.r).map ι) / φ ((toPoly I.s).map ι) =
      φ (C (ι c)) * (φ ((toPoly Iη.r).map ι) / φ ((toPoly Iη.s).map ι)) := by
    have := congrArg (fun P : R[X] ↦ φ (P.map ι)) hcross
    simp only [Polynomial.map_mul, map_C, map_mul] at this
    field_simp
    linear_combination this
  have hc' : (φ (C (ι c)))′ = 0 := by rw [deriv_algebraMap, hD, derivative_C, map_zero]
  have hval : ev K ι (limitedSol I Iη c) =
      (φ ((toPoly I.gn).map ι) / φ ((toPoly I.gd).map ι) + φ ((toPoly I.Q).map ι)) -
        φ (C (ι c)) *
          (φ ((toPoly Iη.gn).map ι) / φ ((toPoly Iη.gd).map ι) + φ ((toPoly Iη.Q).map ι)) := by
    simp only [ev, limitedSol, toPoly_sub, toPoly_mul, toPoly_smul, toPoly_add,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, map_C, map_sub, map_mul,
      map_add]
    field_simp
  rw [hval, deriv_sub', Derivation.leibniz, hc']
  simp only [ev, smul_eq_mul, mul_zero, add_zero]
  rw [hdecI, hdecη, hrs]
  ring

/-- **Soundness of one level.** -/
theorem primStep_sound (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {En Ed : CPoly R} {Iη : RationalIntegral R} (hcη : rationalCheck En Ed Iη = true)
    (hEd : toPoly Ed ≠ 0) {k : ℕ} {An Ad : CPoly R} {Q : CPoly R × CPoly R}
    (hAd : toPoly Ad ≠ 0) (hQ : toPoly Q.2 ≠ 0) {c : R} {Q' : CPoly R × CPoly R}
    (h : primStep En Ed Iη k An Ad Q = some (c, Q')) :
    toPoly Q'.2 ≠ 0 ∧
      (ev K ι Q')′ = ev K ι (An, Ad) - ((k + 1 : ℕ) : K) * ev K ι (En, Ed) * ev K ι Q -
        φ (C (ι c)) * ev K ι (En, Ed) := by
  obtain ⟨hg0, hg⟩ := ev_primG (K := K) ι (En := En) (An := An) k hEd hAd hQ
  simp only [primStep] at h
  cases hcrit : limitedCrit (integrateRational (primG En Ed k An Ad Q).1
      (primG En Ed k An Ad Q).2).r (integrateRational (primG En Ed k An Ad Q).1
      (primG En Ed k An Ad Q).2).s Iη.r Iη.s with
  | none => rw [hcrit] at h; exact absurd h (by simp)
  | some c' =>
    rw [hcrit] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hI := rationalCheck_integrateRational (primG En Ed k An Ad Q).1
      (primG En Ed k An Ad Q).2 hg0
    obtain ⟨h1, h2⟩ := deriv_ev_limitedSol (K := K) ι hD hI hcη (limitedCrit_sound hcrit)
    exact ⟨h1, by rw [h2, ← hg]⟩

/-- **Completeness of one level.** If `Pₖ′ + (k + 1) η (Q + b) = f` has a solution `Pₖ` over an
extension of the constants, the step succeeds and `Pₖ` is the computed `Q'` up to a constant. -/
theorem primStep_complete (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (hKconst : ∀ y : K, y′ = 0 → ∃ b : S, y = φ (C b))
    {En Ed : CPoly R} {Iη : RationalIntegral R} (hcη : rationalCheck En Ed Iη = true)
    (hEd : toPoly Ed ≠ 0) (hη0 : isZero Iη.r = false) {k : ℕ} {An Ad : CPoly R}
    {Q : CPoly R × CPoly R} (hAd : toPoly Ad ≠ 0) (hQ : toPoly Q.2 ≠ 0) (Pk : K) (b : S)
    (hP : Pk′ + ((k + 1 : ℕ) : K) * ev K ι (En, Ed) * (ev K ι Q + φ (C b)) = ev K ι (An, Ad)) :
    ∃ (c : R) (Q' : CPoly R × CPoly R), primStep En Ed Iη k An Ad Q = some (c, Q') ∧
      ∃ b' : S, Pk = ev K ι Q' + φ (C b') := by
  obtain ⟨hg0, hg⟩ := ev_primG (K := K) ι (En := En) (An := An) k hEd hAd hQ
  set g := primG En Ed k An Ad Q with hgdef
  set I := integrateRational g.1 g.2 with hIdef
  have hI : rationalCheck g.1 g.2 I = true := rationalCheck_integrateRational _ _ hg0
  obtain ⟨hdecI, hsqI, hdegI⟩ := rationalCheck_sound_map (K := K) ι hD g.1 g.2 I hI
  obtain ⟨hdecη, hsqη, hdegη⟩ := rationalCheck_sound_map (K := K) ι hD En Ed Iη hcη
  have hcast : φ (C (((k + 1 : ℕ) : S) * b)) = ((k + 1 : ℕ) : K) * φ (C b) := by
    rw [C_mul, map_mul, map_natCast (C : S →+* S[X]), map_natCast]
  -- the limited-integration identity over `S`, and its descent to `R`
  have hlim := (limited_integral_iff (K := K) hD _ _ _ _ _ _ hsqI hsqη hdegI hdegη
    (((k + 1 : ℕ) : S) * b)).mp ⟨Pk, by
      have hgE : ev K ι (g.1, g.2) = ev K ι g := rfl
      simp only [ev] at hgE hg hP
      rw [← hdecI, ← hdecη, hcast, hg]
      linear_combination hP⟩
  obtain ⟨c₀, hc₀⟩ := limited_descent ι hlim
  cases hcrit : limitedCrit I.r I.s Iη.r Iη.s with
  | none => exact absurd ⟨c₀, hc₀⟩ (limitedCrit_complete hcrit)
  | some c =>
    have hstep : primStep En Ed Iη k An Ad Q = some (c, limitedSol I Iη c) := by
      simp only [primStep, ← hgdef, ← hIdef, hcrit]
    refine ⟨c, _, hstep, ?_⟩
    obtain ⟨-, hQ'⟩ := primStep_sound (K := K) ι hD hcη hEd hAd hQ hstep
    set Q' := limitedSol I Iη c
    set a : S := ι c - ((k + 1 : ℕ) : S) * b with ha
    have hφa : φ (C a) = φ (C (ι c)) - ((k + 1 : ℕ) : K) * φ (C b) := by
      rw [ha, C_sub, map_sub, hcast]
    have hy : (Pk - ev K ι Q')′ = φ (C a) * ev K ι (En, Ed) := by
      rw [deriv_sub', hQ', hφa]
      linear_combination hP
    have hca' : (φ (C a))′ = 0 := by rw [deriv_algebraMap, hD, derivative_C, map_zero]
    have ha0 : a = 0 := by
      by_contra hne
      -- otherwise `η` would be a derivative
      have hz : (Pk - ev K ι Q' - φ (C a) *
          (φ ((toPoly Iη.gn).map ι) / φ ((toPoly Iη.gd).map ι) + φ ((toPoly Iη.Q).map ι)))′ =
          φ (C a * (toPoly Iη.r).map ι) / φ ((toPoly Iη.s).map ι) := by
        rw [deriv_sub', hy, Derivation.leibniz, hca']
        simp only [ev, smul_eq_mul, mul_zero, add_zero]
        rw [hdecη, map_mul]
        ring
      have hdeg : (C a * (toPoly Iη.r).map ι).degree < ((toPoly Iη.s).map ι).degree := by
        rw [degree_C_mul hne]
        exact hdegη
      have h0 := eq_zero_of_deriv_eq_proper_fraction (K := K) hD _ _ hsqη hdeg _ hz
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact hne (C_eq_zero.mp h0)
      · rw [Polynomial.map_eq_zero_iff ι.injective, ← isZero_iff, hη0] at h0
        exact Bool.noConfusion h0
    rw [ha0, C_0, map_zero, zero_mul] at hy
    obtain ⟨b', hb'⟩ := hKconst _ hy
    exact ⟨b', by rw [← hb']; ring⟩

/-- **Completeness of the loop.** If the coefficient equations `pⱼ′ + (j + 1) η pⱼ₊₁ = fⱼ`,
`1 ≤ j ≤ k`, have a solution over an extension of the constants with `pₖ₊₁ = Q + b`, the loop
succeeds. -/
theorem primLoop_complete (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (hKconst : ∀ y : K, y′ = 0 → ∃ b : S, y = φ (C b))
    {En Ed : CPoly R} {Iη : RationalIntegral R} (hcη : rationalCheck En Ed Iη = true)
    (hEd : toPoly Ed ≠ 0) (hη0 : isZero Iη.r = false) (A D : ℕ → CPoly R) (p : ℕ → K) (k : ℕ)
    (hD0 : ∀ j, 1 ≤ j → j ≤ k → toPoly (D j) ≠ 0)
    (hp : ∀ j, 1 ≤ j → j ≤ k →
      (p j)′ + ((j + 1 : ℕ) : K) * ev K ι (En, Ed) * p (j + 1) = ev K ι (A j, D j))
    (Q : CPoly R × CPoly R) (hQ : toPoly Q.2 ≠ 0) (b : S) (hb : p (k + 1) = ev K ι Q + φ (C b)) :
    primLoop En Ed Iη A D k Q ≠ none := by
  induction k generalizing Q b with
  | zero => simp [primLoop]
  | succ k ih =>
    obtain ⟨c, Q', hstep, b', hb'⟩ := primStep_complete (K := K) ι hD hKconst hcη hEd hη0
      (hD0 (k + 1) (by omega) le_rfl) hQ (p (k + 1)) b (by
        rw [← hb]
        exact hp (k + 1) (by omega) le_rfl)
    obtain ⟨hQ', -⟩ := primStep_sound (K := K) ι hD hcη hEd (hD0 (k + 1) (by omega) le_rfl) hQ hstep
    have := ih (fun j h1 h2 ↦ hD0 j h1 (by omega)) (fun j h1 h2 ↦ hp j h1 (by omega)) Q' hQ' b' hb'
    simp only [primLoop, hstep]
    intro hnone
    rw [Option.map_eq_none_iff] at hnone
    exact this hnone

/-- The last fraction `Q₁` produced by the loop (`Q` itself if the loop is empty). -/
def primLastQ : CPoly R × CPoly R → List (R × (CPoly R × CPoly R)) → CPoly R × CPoly R
  | Q, [] => Q
  | _, cQ :: L => primLastQ cQ.2 L

/-- **Completeness of the loop, with its final state.** Under the hypotheses of
`primLoop_complete`, the loop returns some `L`, its last fraction has a nonzero denominator, and
`p₁` is that fraction up to a constant. -/
theorem primLoop_complete_last (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (hKconst : ∀ y : K, y′ = 0 → ∃ b : S, y = φ (C b))
    {En Ed : CPoly R} {Iη : RationalIntegral R} (hcη : rationalCheck En Ed Iη = true)
    (hEd : toPoly Ed ≠ 0) (hη0 : isZero Iη.r = false) (A D : ℕ → CPoly R) (p : ℕ → K) (k : ℕ)
    (hD0 : ∀ j, 1 ≤ j → j ≤ k → toPoly (D j) ≠ 0)
    (hp : ∀ j, 1 ≤ j → j ≤ k →
      (p j)′ + ((j + 1 : ℕ) : K) * ev K ι (En, Ed) * p (j + 1) = ev K ι (A j, D j))
    (Q : CPoly R × CPoly R) (hQ : toPoly Q.2 ≠ 0) (b : S) (hb : p (k + 1) = ev K ι Q + φ (C b)) :
    ∃ L, primLoop En Ed Iη A D k Q = some L ∧ toPoly (primLastQ Q L).2 ≠ 0 ∧
      ∃ b' : S, p 1 = ev K ι (primLastQ Q L) + φ (C b') := by
  induction k generalizing Q b with
  | zero => exact ⟨[], rfl, hQ, b, hb⟩
  | succ k ih =>
    obtain ⟨c, Q', hstep, b', hb'⟩ := primStep_complete (K := K) ι hD hKconst hcη hEd hη0
      (hD0 (k + 1) (by omega) le_rfl) hQ (p (k + 1)) b (by
        rw [← hb]
        exact hp (k + 1) (by omega) le_rfl)
    obtain ⟨hQ', -⟩ := primStep_sound (K := K) ι hD hcη hEd (hD0 (k + 1) (by omega) le_rfl) hQ hstep
    obtain ⟨L, hL, hlast, b'', hb''⟩ :=
      ih (fun j h1 h2 ↦ hD0 j h1 (by omega)) (fun j h1 h2 ↦ hp j h1 (by omega)) Q' hQ' b' hb'
    exact ⟨(c, Q') :: L, by simp only [primLoop, hstep, hL, Option.map_some], hlast, b'', hb''⟩

end CPoly
