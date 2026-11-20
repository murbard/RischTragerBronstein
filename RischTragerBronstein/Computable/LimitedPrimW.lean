import RischTragerBronstein.Computable.DerivPrimSol
import RischTragerBronstein.Computable.Prim2StepGen
import RischTragerBronstein.Liouville.TwoProperFractions

/-!
# Limited integration in `R(x)(t₁)` with a parameter function having simple poles

Problem: given `G, W ∈ R(x)(t₁)`, find a constant `c` and `y ∈ R(x)(t₁)` with `y′ = G - c W`.

When the Hermite remainder `r_W / s_W` of `W` is non-zero (e.g. `W = u′ / u` with `u ∉ R(x)`:
`t₂ = log u`; or `W = 1 / t₁`: `t₂ = li x`), the simple parts must cancel,
`r_G s_W = c r_W s_G` (`deriv_eq_poly_add_two_proper`), which determines `c`: it is the (constant)
quotient of the two polynomials. `limitedPrimW` computes this candidate and then integrates
`G - c W` inside the field (`derivPrimSol`).

* `limitedPrimW_sound`: a returned `(c, h, P)` is a solution, in every model;
* `limitedPrimW_complete`: if a solution exists over **any** extension of the constants, the
  procedure succeeds and returns that constant.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- The constant `c ∈ R` as an element of `R(x)(t₁)`. -/
def constCode₂ (c : R) : GFrac (GFrac R) := ([([c], [1])], [(ops₁g R).one])

/-- `G - c W` as a fraction code with non-zero denominator. -/
def subSmulCode (En₁ Ed₁ : CPoly R) (G W : GFrac (GFrac R)) (c : R) : GFrac (GFrac R) :=
  normF₂ ((ops₂p En₁ Ed₁).add G ((ops₂p En₁ Ed₁).neg ((ops₂p En₁ Ed₁).mul (constCode₂ c) W)))

/-- The candidate constant: the quotient `r_G s_W / (r_W s_G)`. -/
def limitedConstW (En₁ Ed₁ : CPoly R) (G W : GFrac (GFrac R)) : Option R :=
  let hG := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] G.1 G.2
  let rG := (GPoly.divMod (ops₁g R) hG.b hG.s).2
  let hW := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2
  let rW := (GPoly.divMod (ops₁g R) hW.b hW.s).2
  let q := (GPoly.divMod (ops₁g R) (GPoly.mul (ops₁g R) rG hW.s) (GPoly.mul (ops₁g R) rW hG.s)).1
  let nd := normFrac (q.getD 0 ([], [1]))
  match CPoly.linSolve [nd.2] nd.1 with
  | some [c] => some c
  | _ => none

/-- Limited integration with parameter function `W`: returns `(c, Hermite data, coefficients)`. -/
def limitedPrimW (En₁ Ed₁ : CPoly R) (Iη₁ : CPoly.RationalIntegral R) (G W : GFrac (GFrac R)) :
    Option (R × GPoly.HermiteResult (GFrac R) × (ℕ → CPoly R × CPoly R)) :=
  match limitedConstW En₁ Ed₁ G W with
  | none => none
  | some c =>
    (derivPrimSol En₁ Ed₁ Iη₁ (subSmulCode En₁ Ed₁ G W c).1 (subSmulCode En₁ Ed₁ G W c).2).map
      fun r ↦ (c, r)

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

/-- The model of `R(x)(t₁)` in `K₂`, from the one-level hypotheses. -/
noncomputable def M₂W (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)
    {En₁ Ed₁ : CPoly R}
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P) :
    CField (GFrac (GFrac R)) K₂ (ops₂p En₁ Ed₁) :=
  (M₁In (K₁ := K₁) ι h0 hD).monomialIn [(En₁, Ed₁)] K₂ fun P ↦ by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, sem_M₁In]
    exact hD₂ P

lemma sem_M₂W (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)
    {En₁ Ed₁ : CPoly R}
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P)
    (q : GFrac (GFrac R)) :
    (M₂W (K₂ := K₂) ι h0 hD hD₂).sem q = φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) q.1) /
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) q.2) := rfl

lemma sem_constCode₂ (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)
    {En₁ Ed₁ : CPoly R}
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P) (c : R) :
    (M₂W (K₂ := K₂) ι h0 hD hD₂).sem (constCode₂ c) = φ₂ (C (φ (C (ι c)))) := by
  have h1 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) [(ops₁g R).one] = 1 := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, CField.sem_one, C_1]
  rw [sem_M₂W, constCode₂, h1, map_one, div_one, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero,
    add_zero, sem_M₁In]
  simp [CPoly.ev, CPoly.toPoly]

lemma subSmulCode_spec (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)
    {En₁ Ed₁ : CPoly R}
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P)
    (G W : GFrac (GFrac R)) (c : R) :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (subSmulCode En₁ Ed₁ G W c).2 ≠ 0 ∧
      (M₂W (K₂ := K₂) ι h0 hD hD₂).sem (subSmulCode En₁ Ed₁ G W c) =
        (M₂W (K₂ := K₂) ι h0 hD hD₂).sem G -
          φ₂ (C (φ (C (ι c)))) * (M₂W (K₂ := K₂) ι h0 hD hD₂).sem W := by
  have hsem : (M₂W (K₂ := K₂) ι h0 hD hD₂).sem ((ops₂p En₁ Ed₁).add G ((ops₂p En₁ Ed₁).neg
      ((ops₂p En₁ Ed₁).mul (constCode₂ c) W))) = (M₂W (K₂ := K₂) ι h0 hD hD₂).sem G -
        φ₂ (C (φ (C (ι c)))) * (M₂W (K₂ := K₂) ι h0 hD hD₂).sem W := by
    rw [CField.sem_add, CField.sem_neg, CField.sem_mul, sem_constCode₂]
    ring
  rw [← hsem]
  unfold subSmulCode normF₂
  split_ifs with hz
  · have hz' := (GPoly.isZero_iff (M₁In (K₁ := K₁) ι h0 hD) _).mp hz
    refine ⟨by simp [CField.sem_one], ?_⟩
    rw [sem_M₂W, sem_M₂W, hz']
    simp
  · exact ⟨fun h ↦ hz ((GPoly.isZero_iff (M₁In (K₁ := K₁) ι h0 hD) _).mpr h), rfl⟩

set_option maxHeartbeats 800000 in
/-- **Soundness.** -/
theorem limitedPrimW_sound (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P)
    {En₁ Ed₁ : CPoly R} {Iη₁ : CPoly.RationalIntegral R}
    (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P)
    (hconst₂ : ∀ P : K₁[X], P′ = 0 → ∃ e : K₁, P = C e)
    (G W : GFrac (GFrac R)) {c : R} {hr : GPoly.HermiteResult (GFrac R)}
    {P : ℕ → CPoly R × CPoly R} (hsome : limitedPrimW En₁ Ed₁ Iη₁ G W = some (c, hr, P)) :
    (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) hr.gn) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) hr.gd) +
        CPoly.ev₂ (K₁ := K₁) ι (φ₂ X) P
          ((GPoly.divMod (ops₁g R) hr.b hr.s).1.length + 1))′ =
      (M₂W (K₂ := K₂) ι h0 hD hD₂).sem G -
        φ₂ (C (φ (C (ι c)))) * (M₂W (K₂ := K₂) ι h0 hD hD₂).sem W := by
  simp only [limitedPrimW] at hsome
  cases hc : limitedConstW En₁ Ed₁ G W with
  | none => rw [hc] at hsome; exact absurd hsome (by simp)
  | some c' =>
    rw [hc] at hsome
    simp only [Option.map_eq_some_iff] at hsome
    obtain ⟨⟨hr', P'⟩, hsol, hpair⟩ := hsome
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    obtain ⟨hden, hsem⟩ := subSmulCode_spec (K₂ := K₂) ι h0 hD hD₂ G W c'
    rw [← hsem, sem_M₂W]
    exact derivPrimSol_sound (K₁ := K₁) (K₂ := K₂) ι h0 hD hcη₁ hEd₁ hD₂ hconst₂ _ _ hden hsol

end Tower
