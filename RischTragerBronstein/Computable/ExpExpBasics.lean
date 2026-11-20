import RischTragerBronstein.Computable.RDEExpComplete

/-!
# Two exponentials: the independence certificate and uniqueness

`expIndep a b`: `b′` is not an `R`-multiple of `a′` (checked by `linSolve`). Consequences, over
every extension `S ⊇ R` of the constants: `k b′ + z a′ ≠ 0` for `k ≠ 0` and all integers `z`, and
`y′ + k b′ y = 0` has only the zero solution in `S(x)(exp a)`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- `b′ ∉ R · a′`. -/
def expIndep (a b : CPoly R) : Bool :=
  (CPoly.linSolve [CPoly.deriv a] (CPoly.deriv b)).isNone && !CPoly.isZero (CPoly.deriv a)

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

/-- The certificate gives `k b′ + z a′ ≠ 0` for every non-zero `k ∈ R` and integer `z`. -/
theorem expIndep_comb {a b : CPoly R} (h : expIndep a b = true) (k : R) (hk : k ≠ 0) (z : ℤ) :
    CPoly.toPoly (CPoly.add (CPoly.smul k (CPoly.deriv b)) (CPoly.smul (z : R) (CPoly.deriv a)))
      ≠ 0 := by
  intro h0
  simp only [expIndep, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at h
  obtain ⟨hnone, -⟩ := h
  rw [CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_smul] at h0
  refine CPoly.linSolve_complete_map (RingHom.id R) [CPoly.deriv a] (CPoly.deriv b)
    [-(z : R) / k] rfl ?_ hnone
  simp only [CPoly.lcombS, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
    List.sum_nil, add_zero, Polynomial.map_id]
  have hCk : (C k : R[X]) ≠ 0 := C_ne_zero.mpr hk
  apply mul_left_cancel₀ hCk
  rw [← mul_assoc, ← C_mul, mul_div_cancel₀ _ hk, C_neg]
  linear_combination -h0

/-- `expIndep` implies the `hcomb` hypothesis of `rdeExp_complete` for `g = k b′`. -/
theorem expIndep_hcomb {a b : CPoly R} (h : expIndep a b = true) (k : R) (hk : k ≠ 0) (z : ℤ) :
    CPoly.toPoly (CPoly.add (CPoly.smul k (CPoly.deriv b)) (CPoly.smul (z : R) (CPoly.deriv a)))
      ≠ 0 := expIndep_comb h k hk z

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P) (a : CPoly R)

include h0 hD in
/-- **Uniqueness** in `S(x)(exp a)`: `y′ + g y = 0` forces `y = 0` when `g + z a′ ≠ 0` for all
integers `z`. -/
theorem eq_zero_of_rde_homogeneous_exp (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (g : CPoly R)
    (hcomb : ∀ z : ℤ, CPoly.toPoly (CPoly.add g (CPoly.smul (z : R) (CPoly.deriv a))) ≠ 0)
    (y : K₂) (hy : y′ + φ₂ (C (φ ((CPoly.toPoly g).map ι))) * y = 0) : y = 0 := by
  set gK : K₁ := φ ((CPoly.toPoly g).map ι) with hgK
  have hnorm : ∀ p : K₁[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′ :=
    fun p hm hp hpX hdvd ↦ hpX (by
      have hXp := dvd_X_of_irreducible_special (ηa ι a) hD₂ hconst hp hdvd
      exact eq_of_monic_of_associated hm monic_X
        (associated_of_dvd_dvd (irreducible_X.dvd_symm hp hXp) hXp))
  have hg : ∀ r : ℕ, 0 < r → ∀ e : K₁, e ≠ 0 → e′ + (gK - r * ηa ι a) * e ≠ 0 :=
    fun r _ e he h ↦ by
    have hcr := hcomb (-(r : ℤ))
    refine he (rde_unique_K₁ ι hD _ hcr e 0 0 ?_ (by simp))
    rw [CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_deriv, Polynomial.map_add,
      Polynomial.map_mul, map_C, map_add, map_mul, ← derivative_map]
    simp only [Int.cast_neg, Int.cast_natCast, map_neg, map_natCast, derivative_map]
    linear_combination h
  obtain ⟨Y, hY, hpoly⟩ := rde_denominator_exp (K := K₂) (ηa ι a) hD₂ hnorm gK hg 0 1 0
    (by rw [X_dvd_iff]; simp) y (by rw [hy, map_zero, zero_div])
  simp only [pow_zero, map_one, mul_one] at hY
  by_cases hY0 : Y = 0
  · rw [hY, hY0, map_zero]
  exfalso
  have hgnl : ∀ e : K₁, e ≠ 0 →
      e′ + (gK + ((Y.natDegree : K₁) - (1 : K₁[X]).natDegree) * ηa ι a) * e ≠ 0 :=
    fun e he h ↦ by
      have hcz := hcomb ((Y.natDegree : ℤ) - (1 : K₁[X]).natDegree)
      refine he (rde_unique_K₁ ι hD _ hcz e 0 0 ?_ (by simp))
      rw [CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_deriv, Polynomial.map_add,
        Polynomial.map_mul, map_C, map_add, map_mul, ← derivative_map]
      simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast, derivative_map,
        natDegree_one, Nat.cast_zero, map_zero, sub_zero] at h ⊢
      linear_combination h
  obtain ⟨-, -, hne⟩ := rde_poly_top_exp (ηa ι a) gK hD₂ 1 Y one_ne_zero hY0 hgnl
  rw [Nat.cast_zero, zero_mul, sub_zero] at hpoly
  exact hne (by simpa using hpoly)

end Tower
