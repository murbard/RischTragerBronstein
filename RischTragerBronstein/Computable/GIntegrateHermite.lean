import RischTragerBronstein.Computable.GHermite
import RischTragerBronstein.Computable.TowerExample

/-!
# A certified tower-level integrator: the Hermite-only case

`GPoly.integrateByHermite O w A D` runs Hermite reduction in `(K(t), t′ = W)` and, when the
certificate passes and no remainder is left, returns the rational part `gn / gd`.

`integrateByHermite_sound`: a returned answer **is an antiderivative** in `RatFunc K` with
`ratFuncOfDeriv W`: `(gn / gd)′ = A / D`.

The models of the tower `ℚ ⊂ ℚ(x) ⊂ ℚ(x)(log x)` are instantiated below (`Tower.M₀`, `Tower.M₁`), so
the computation `∫ dx / (x log² x) = -1 / log x` yields, through this theorem, a statement about the
differential field `RatFunc (RatFunc ℚ)`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace GPoly

variable {α K : Type*} [Field K] [Differential K]

/-- Integrate `A / D ∈ K(t)` when Hermite reduction alone suffices. -/
def integrateByHermite (O : COps α) (w A D : GPoly α) : Option (GPoly α × GPoly α) :=
  let r := hermite O w A D
  if hermiteCheck O w A D r && isZero O r.b then some (r.gn, r.gd) else none

variable {O : COps α} (M : CField α K O)

/-- **A returned answer is an antiderivative.** -/
theorem integrateByHermite_sound {w A D : GPoly α} {g : GPoly α × GPoly α}
    (h : integrateByHermite O w A D = some g) :
    letI := ratFuncOfDeriv (toPoly M w)
    (algebraMap K[X] (RatFunc K) (toPoly M g.1) / algebraMap K[X] (RatFunc K) (toPoly M g.2))′ =
      algebraMap K[X] (RatFunc K) (toPoly M A) / algebraMap K[X] (RatFunc K) (toPoly M D) := by
  simp only [integrateByHermite] at h
  split_ifs at h with hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hcheck, hb⟩ := hc
  obtain ⟨hid, -⟩ := hermiteCheck_sound M w A D _ hcheck
  have hb0 := (isZero_iff M _).mp hb
  rw [← Option.some.inj h, hid, hb0, map_zero, zero_div, add_zero]

end GPoly

namespace Tower

/-- `ℚ` with the trivial derivation. -/
instance : Differential ℚ := ⟨0⟩

/-- the model of level 0. -/
noncomputable def M₀ : CField ℚ ℚ ops₀ := CField.ofDecidableField ℚ fun _ ↦ rfl

/-- the model of level 1: `ℚ(x)`, `x′ = 1`. -/
noncomputable def M₁ :
    @CField (GFrac ℚ) (RatFunc ℚ) _ (ratFuncOfDeriv (GPoly.toPoly M₀ [1])) ops₁ :=
  letI : Differential (RatFunc ℚ) := ratFuncOfDeriv (GPoly.toPoly M₀ [1])
  (M₀.monomial [1]).normalizeBy CPoly.normCoeff fun q ↦ by
    change GFrac.sem M₀ _ = GFrac.sem M₀ q
    have hM₀ : ∀ p : List ℚ, GPoly.toPoly M₀ p = CPoly.toPoly p := fun p ↦ by
      induction p with
      | nil => rfl
      | cons a p ih => rw [GPoly.toPoly_cons, CPoly.toPoly_cons, ih]; rfl
    simp only [GFrac.sem, hM₀]
    exact CPoly.normCoeff_spec (algebraMap ℚ[X] (RatFunc ℚ))
      (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) q

end Tower

open Tower in
-- ∫ dx / (x log² x): an antiderivative is returned (`gn / gd = -1 / t`, unnormalised)
#eval (GPoly.integrateByHermite ops₁ [invX] [invX] [ops₁.zero, ops₁.zero, ops₁.one]).isSome
open Tower in
-- ∫ dx / log² x: Hermite reduction alone does not suffice
#eval (GPoly.integrateByHermite ops₁ [invX] [ops₁.one] [ops₁.zero, ops₁.zero, ops₁.one]).isSome
