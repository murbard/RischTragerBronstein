import RischTragerBronstein.Computable.GIntegrateHermite
import RischTragerBronstein.Liouville.ResidueCriterion

/-!
# Deciding a simple pole at a linear factor, at any tower level

Setting: a computable model `M` of `K` (characteristic zero), a primitive step `t′ = η ∈ K`
(code `w = [η]`), and an integrand `b / (t + e)` with `b, e ∈ K`.

The executable `GPoly.linearPole O η b e` computes the residue `c = b / (η + e′)` and tests whether
it is a constant (`c′ = 0`), using only the model's zero test.

* `linearPole_sound`: if it returns `some c`, then `b / (t + e) = c * (t + e)′ / (t + e)` and
  `c′ = 0`: the integral is `c log (t + e)`.
* `linearPole_none`: if it returns `none` (and `η + e′ ≠ 0`), then `b / (t + e)` is **not** of the
  form `∑ cᵢ uᵢ′ / uᵢ + v′` with constant `cᵢ ∈ K` and `uᵢ, v ∈ K(t)` (residue criterion).

Examples in `ℚ(x)(log x)`: `1 / (x log x)` has the constant residue `1` (`∫ = log log x`), while
`1 / log x` has residue `x`, which is not a constant.
-/

open Polynomial Differential Finset

set_option linter.unusedSectionVars false

namespace GPoly

variable {α K : Type*} [Field K] [CharZero K] [Differential K]

/-- Residue of `b / (t + e)` for `t′ = η`, returned when it is a constant. -/
def linearPole (O : COps α) (η b e : α) : Option α :=
  let d := O.add η (O.deriv e)
  let c := O.mul b (O.inv d)
  if !O.isZero d && O.isZero (O.deriv c) then some c else none

variable {O : COps α} (M : CField α K O)

local notation "φ" => algebraMap K[X] (RatFunc K)

/-- The derivative of `t + e` for `t′ = η`. -/
lemma implicitDeriv_X_add_C (η e : K) :
    implicitDeriv (C η) (X + C e) = C (η + e′) := by
  rw [map_add, implicitDeriv_X, implicitDeriv_C, C_add]

theorem linearPole_sound {η b e c : α} (h : linearPole O η b e = some c) :
    letI := ratFuncOfDeriv (C (M.sem η))
    (M.sem c)′ = 0 ∧
      φ (C (M.sem b)) / φ (X + C (M.sem e)) = φ (C (M.sem c)) * logDeriv (φ (X + C (M.sem e))) := by
  let _ := polynomialOfDeriv (C (M.sem η))
  let _ := ratFuncOfDeriv (C (M.sem η))
  simp only [linearPole] at h
  split_ifs at h with hc
  rw [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, M.isZero_iff, M.isZero_iff] at hc
  obtain ⟨hd, hconst⟩ := hc
  have hcdef : M.sem c = M.sem b / (M.sem η + (M.sem e)′) := by
    rw [← Option.some.inj h, M.sem_mul, M.sem_inv, M.sem_add, M.sem_deriv, div_eq_mul_inv]
  rw [M.sem_add, M.sem_deriv] at hd
  refine ⟨by rw [← M.sem_deriv, ← Option.some.inj h]; exact hconst, ?_⟩
  have hs0 : (X + C (M.sem e) : K[X]) ≠ 0 := (monic_X_add_C _).ne_zero
  have hφs : φ (X + C (M.sem e)) ≠ 0 := RatFunc.algebraMap_ne_zero hs0
  have hder : (φ (X + C (M.sem e)))′ = φ (C (M.sem η + (M.sem e)′)) := by
    rw [ratFuncOfDeriv_algebraMap, implicitDeriv_X_add_C]
  rw [logDeriv, hder, hcdef]
  have hC : (C (M.sem b / (M.sem η + (M.sem e)′)) : K[X]) * C (M.sem η + (M.sem e)′) =
      C (M.sem b) := by rw [← C_mul, div_mul_cancel₀ _ hd]
  rw [← hC, map_mul]
  field_simp

theorem linearPole_none {η b e : α} (hd : M.sem η + (M.sem e)′ ≠ 0)
    (h : linearPole O η b e = none)
    {ι : Type*} (S : Finset ι) (c : ι → K) (hc : ∀ i ∈ S, (c i)′ = 0) (u : ι → RatFunc K)
    (hu : ∀ i ∈ S, u i ≠ 0) (v : RatFunc K) :
    letI := ratFuncOfDeriv (C (M.sem η))
    φ (C (M.sem b)) / φ (X + C (M.sem e)) ≠ ∑ i ∈ S, φ (C (c i)) * logDeriv (u i) + v′ := by
  let _ : Differential K[X] := polynomialOfDeriv (C (M.sem η))
  let _ := ratFuncOfDeriv (C (M.sem η))
  have hDA : DifferentialAlgebra K[X] (RatFunc K) := differentialAlgebra_ofFractionRing _ _
  intro heq
  -- the residue is not a constant
  have hnc : (M.sem b / (M.sem η + (M.sem e)′))′ ≠ 0 := by
    simp only [linearPole] at h
    split_ifs at h with hcond
    rw [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, M.isZero_iff, M.isZero_iff,
      not_and] at hcond
    have := hcond (by rwa [M.sem_add, M.sem_deriv])
    rwa [M.sem_deriv, M.sem_mul, M.sem_inv, M.sem_add, M.sem_deriv, ← div_eq_mul_inv] at this
  -- `s = t + e` is a normal prime
  have hprime : Prime (X + C (M.sem e) : K[X]) :=
    (irreducible_of_degree_eq_one (degree_X_add_C _)).prime
  have hsd : (X + C (M.sem e) : K[X])′ = C (M.sem η + (M.sem e)′) := implicitDeriv_X_add_C _ _
  have hnorm : ¬(X + C (M.sem e) : K[X]) ∣ (X + C (M.sem e) : K[X])′ := by
    rw [hsd]
    intro hdvd
    have := degree_le_of_dvd hdvd (C_ne_zero.mpr hd)
    rw [degree_X_add_C, degree_C hd] at this
    exact absurd this (by norm_num)
  obtain ⟨N, hN, hdvd⟩ := residue_criterion (K := RatFunc K) hprime hnorm (C (M.sem b)) 1
    (fun h1 ↦ hprime.not_isUnit (isUnit_of_dvd_one h1)) S c hc u hu v (by rwa [mul_one])
  rw [mul_one, hsd, ← C_mul, ← C_sub] at hdvd
  -- a linear polynomial dividing a constant: the constant is zero
  have hzero : M.sem b - N * (M.sem η + (M.sem e)′) = 0 := by
    by_contra hne
    have := degree_le_of_dvd hdvd (C_ne_zero.mpr hne)
    rw [degree_X_add_C, degree_C hne] at this
    exact absurd this (by norm_num)
  have hNeq : M.sem b / (M.sem η + (M.sem e)′) = N := by
    rw [div_eq_iff hd]; linear_combination hzero
  exact hnc (by rw [hNeq, hN])

end GPoly

open Tower in
-- ∫ dx / (x log x): residue of (1/x) / t is the constant 1
#eval (GPoly.linearPole ops₁ invX invX ops₁.zero).isSome
open Tower in
-- ∫ dx / log x: residue of 1 / t is x, not a constant
#eval (GPoly.linearPole ops₁ invX ops₁.one ops₁.zero).isSome
