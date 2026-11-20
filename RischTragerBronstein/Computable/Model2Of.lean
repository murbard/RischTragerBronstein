import RischTragerBronstein.Computable.Prim2LoopComplete
import RischTragerBronstein.Liouville.PrimitiveConstants
import RischTragerBronstein.Liouville.HermitePrimitive

/-!
# Building the two-level model from basic hypotheses

`Model2.of`: for `K₁` a model of `S(x)` and `K₂` the fraction field of `K₁[X]` with `t₁′ = η₁`, the
bundled hypotheses `Model2` follow from two facts about `S(x)`:

* `η₁` is not a derivative in `K₁`;
* `η₂ ≠ c η₁ + d′` for every constant `c ∈ S` and `d ∈ K₁`

(both decided executably by `limitedCrit` on Hermite data). In particular the constants of `K₁`
and of `K₂` are those of `S`.
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

/-- The constants of a model of `S(x)` (with `d/dx`) are the elements of `S`. -/
theorem const_of_model (hD : ∀ P : S[X], P′ = derivative P) (y : K₁) (hy : y′ = 0) :
    ∃ b : S, y = φ (C b) := by
  have hnorm : ∀ p : S[X], Irreducible p → ¬p ∣ p′ := fun p hp hdvd ↦ by
    rw [hD] at hdvd
    have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
    have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
    exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
  obtain ⟨-, P, rfl, hP⟩ := deriv_eq_poly_add_proper (K := K₁) hnorm 0 0 1 squarefree_one
    (by simp) y (by rw [hy]; simp)
  rw [hD] at hP
  exact ⟨P.coeff 0, by rw [eq_C_of_derivative_eq_zero hP]; simp⟩

theorem Model2.of (ι : R →+* S) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (hD : ∀ P : S[X], P′ = derivative P)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ev K₁ ι (En₁, Ed₁))) P)
    (hη₁nd : ∀ y : K₁, y′ ≠ ev K₁ ι (En₁, Ed₁))
    (hα : ∀ (c : S) (d : K₁), ev K₁ ι (En₂, Ed₂) ≠ φ (C c) * ev K₁ ι (En₁, Ed₁) + d′) :
    Model2 (K₁ := K₁) (K₂ := K₂) ι En₁ Ed₁ En₂ Ed₂ := by
  have hKconst := const_of_model (K₁ := K₁) hD
  have hconst' : ∀ P : K₁[X], implicitDeriv (C (ev K₁ ι (En₁, Ed₁))) P = 0 →
      ∃ e : K₁, P = C e := fun P hP ↦ const_of_implicitDeriv_eq_zero _ hη₁nd hP
  have hconst₂ : ∀ P : K₁[X], P′ = 0 → ∃ e : K₁, P = C e := fun P hP ↦
    hconst' P (by rw [← hD₂, hP])
  have hnorm₂ : ∀ p : K₁[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive _ hD₂ hconst₂ hp
  have hCφ : ∀ e : K₁, φ₂ (C e) = algebraMap K₁ K₂ e := fun e ↦ by
    rw [IsScalarTower.algebraMap_apply K₁ K₁[X] K₂, Polynomial.algebraMap_eq]
  refine ⟨hD, hKconst, hD₂, hconst₂, fun y hy ↦ ?_, fun y a ha hy ↦ ?_⟩
  · -- constants of `K₂`
    obtain ⟨-, P, rfl, hP⟩ := deriv_eq_poly_add_proper (K := K₂) hnorm₂ 0 0 1 squarefree_one
      (by simp) y (by rw [hy]; simp)
    obtain ⟨e, rfl⟩ := hconst₂ P hP
    have he : e′ = 0 := by
      rw [hD₂, implicitDeriv_C] at hP
      exact C_eq_zero.mp hP
    obtain ⟨b, rfl⟩ := hKconst e he
    exact ⟨b, hCφ _⟩
  · -- `a η₂` is not a derivative in `K₂`
    obtain ⟨-, P, -, hP⟩ := deriv_eq_poly_add_proper (K := K₂) hnorm₂
      (C (φ (C a) * ev K₁ ι (En₂, Ed₂))) 0 1 squarefree_one (by simp) y (by rw [hy]; simp)
    rw [hD₂] at hP
    obtain ⟨c₀, d, hc₀, rfl⟩ := eq_linear_of_deriv_eq_C _ hconst' hP
    obtain ⟨cc, rfl⟩ := hKconst c₀ hc₀
    have hcoef := congrArg (fun Q : K₁[X] ↦ Q.coeff 0) hP
    simp only [map_add, Derivation.leibniz, implicitDeriv_C, implicitDeriv_X, smul_eq_mul,
      coeff_add, coeff_C_mul, coeff_C_zero, mul_coeff_zero, coeff_X_zero, mul_zero, zero_mul,
      add_zero] at hcoef
    have hφa : φ (C a) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective S[X] K₁)).mpr (C_ne_zero.mpr ha)
    have hφa' : (φ (C a))′ = 0 := by rw [deriv_algebraMap, hD, derivative_C, map_zero]
    refine hα (cc / a) (d / φ (C a)) ?_
    have hdiv : (d / φ (C a))′ = d′ / φ (C a) := by
      rw [Derivation.leibniz_div, hφa']
      simp only [smul_eq_mul, mul_zero, sub_zero]
      field_simp
    have hcast : φ (C (cc / a)) = φ (C cc) / φ (C a) := by
      rw [div_eq_mul_inv, C_mul, map_mul, div_eq_mul_inv]
      congr 1
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, ← C_mul, inv_mul_cancel₀ ha, C_1, map_one])
    rw [hdiv, hcast]
    field_simp
    linear_combination -hcoef

end CPoly
