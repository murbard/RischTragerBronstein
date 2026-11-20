import RischTragerBronstein.RDE.ExpPolynomial
import RischTragerBronstein.Liouville.Transcendence

/-!
# Exponentials whose argument has positive degree in the tower variable

`K₂ = K₁(t₁)` with `P′ = implicitDeriv w P` on `K₁[X]` and `deg P′ ≤ deg P` (primitive or
exponential `t₁`). For `g ∈ K₁[X]` of positive degree:

* `no_rde_homogeneous_of_pos_degree`: `e′ + g e = 0` has no non-zero solution `e ∈ K₂`
  (degree count on `P′ Q - P Q′ + g P Q = 0`);
* `transcendental_exp_arg`: `t = exp a` with `a′ = g` is transcendental over `K₂`;
* `exp_arg_no_new_constants`: adjoining it creates no new constants.

This covers `x^x = exp (x log x)`, `e^{eˣ}`, `exp (x eˣ)`, …
-/

open Polynomial

namespace Differential

variable {K₁ K₂ : Type*} [Field K₁] [CharZero K₁] [Differential K₁] [Differential K₁[X]]
variable [Field K₂] [Algebra K₁[X] K₂] [IsFractionRing K₁[X] K₂] [Differential K₂]
variable [DifferentialAlgebra K₁[X] K₂]

local notation "φ₂" => algebraMap K₁[X] K₂

/-- **No non-zero solution of `e′ + g e = 0` when `deg g ≥ 1`.** -/
theorem no_rde_homogeneous_of_pos_degree (hder : ∀ P : K₁[X], (P′).natDegree ≤ P.natDegree)
    (g : K₁[X]) (hg : 1 ≤ g.natDegree) (e : K₂) (he : e ≠ 0) : e′ + φ₂ g * e ≠ 0 := by
  intro h
  have hinj : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  obtain ⟨P, Q, hQ, hPQ⟩ := IsFractionRing.div_surjective (A := K₁[X]) e
  have hQ0 : Q ≠ 0 := nonZeroDivisors.ne_zero hQ
  have hφQ : φ₂ Q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hQ0
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact he (by rw [← hPQ, map_zero, zero_div])
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [natDegree_zero] at hg
    exact absurd hg (by omega)
  rw [← hPQ, Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap] at h
  simp only [smul_eq_mul] at h
  have h' : φ₂ (P′ * Q - P * Q′ + g * P * Q) = 0 := by
    simp only [map_add, map_sub, map_mul]
    field_simp at h
    linear_combination h
  have h'' : P′ * Q - P * Q′ + g * P * Q = 0 := hinj (by rw [h', map_zero])
  have hgPQ : (g * P * Q).natDegree = g.natDegree + P.natDegree + Q.natDegree := by
    rw [natDegree_mul (mul_ne_zero hg0 hP0) hQ0, natDegree_mul hg0 hP0]
  have hlt : (P′ * Q - P * Q′).natDegree < (g * P * Q).natDegree := by
    rw [hgPQ]
    refine (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
    · calc (P′ * Q).natDegree ≤ (P′).natDegree + Q.natDegree := natDegree_mul_le
        _ ≤ P.natDegree + Q.natDegree := by have := hder P; omega
        _ < g.natDegree + P.natDegree + Q.natDegree := by omega
    · calc (P * Q′).natDegree ≤ P.natDegree + (Q′).natDegree := natDegree_mul_le
        _ ≤ P.natDegree + Q.natDegree := by have := hder Q; omega
        _ < g.natDegree + P.natDegree + Q.natDegree := by omega
  have hne : P′ * Q - P * Q′ + g * P * Q ≠ 0 := by
    intro h0
    have := congrArg natDegree h0
    rw [natDegree_add_eq_right_of_natDegree_lt hlt, natDegree_zero, hgPQ] at this
    omega
  exact hne h''

variable {E : Type*} [Field E] [Algebra K₂ E] [Differential E] [DifferentialAlgebra K₂ E]
variable [CharZero K₂]

/-- **`exp a` is transcendental over `K₂` when `a′ = g` has positive degree.** -/
theorem transcendental_exp_arg (hder : ∀ P : K₁[X], (P′).natDegree ≤ P.natDegree)
    (g : K₁[X]) (hg : 1 ≤ g.natDegree) {t : E} (ht0 : t ≠ 0)
    (ht : t′ = algebraMap K₂ E (φ₂ g) * t) : Transcendental K₂ t := by
  refine transcendental_exponential (φ₂ g) ht0 ht fun n hn b hb ↦ ?_
  by_contra hb0
  have hg' : 1 ≤ (-(C (n : K₁)) * g).natDegree := by
    rw [natDegree_mul (neg_ne_zero.mpr (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)))
      (fun h0 ↦ by rw [h0, natDegree_zero] at hg; omega), natDegree_neg, natDegree_C]
    omega
  refine no_rde_homogeneous_of_pos_degree hder _ hg' b hb0 ?_
  rw [hb, map_mul, map_neg, show (C (n : K₁) : K₁[X]) = (n : K₁[X]) from map_natCast C n,
    map_natCast]
  ring

variable [Differential K₂[X]]

/-- **No new constants** when adjoining `exp a`, `a′ = g` of positive degree, to `K₂`. -/
theorem exp_arg_no_new_constants (hder : ∀ P : K₁[X], (P′).natDegree ≤ P.natDegree)
    (g : K₁[X]) (hg : 1 ≤ g.natDegree)
    (hD₃ : ∀ P : K₂[X], P′ = implicitDeriv (C (φ₂ g) * X) P)
    (P : K₂[X]) (n : ℕ) (h : P′ * X ^ n = P * (X ^ n)′) : ∃ e : K₂, P = C e * X ^ n := by
  set η := φ₂ g with hη
  refine ⟨P.coeff n, ?_⟩
  have hP : implicitDeriv (C η * X) P = C (n * η) * P := by
    rw [hD₃, hD₃, deriv_X_pow] at h
    have hX : (X : K₂[X]) ^ n ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_right_cancel₀ hX
    rw [h]; ring
  ext j
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with hjn
  · rw [hjn, mul_one]
  rw [mul_zero]
  have hc := congrArg (fun Q : K₂[X] ↦ Q.coeff j) hP
  simp only [coeff_implicitDeriv_C_mul_X, coeff_C_mul] at hc
  have hg0 : g ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hg; omega
  have hg' : 1 ≤ (C ((j : K₁) - n) * g).natDegree := by
    rw [natDegree_mul (C_ne_zero.mpr (sub_ne_zero.mpr (Nat.cast_injective.ne hjn))) hg0,
      natDegree_C]
    omega
  by_contra hne
  refine no_rde_homogeneous_of_pos_degree hder _ hg' (P.coeff j) hne ?_
  rw [map_mul, C_sub, map_sub, show (C (j : K₁) : K₁[X]) = (j : K₁[X]) from map_natCast C j,
    show (C (n : K₁) : K₁[X]) = (n : K₁[X]) from map_natCast C n, map_natCast, map_natCast, ← hη]
  linear_combination hc

end Differential
