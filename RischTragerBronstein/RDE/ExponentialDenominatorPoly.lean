import RischTragerBronstein.RDE.ExponentialDenominator

/-!
# The denominator of the Risch equation in an exponential extension, polynomial coefficient

`K = F(t)`, `t′ = η t`, coefficient `g = G(t) ∈ F[t]` (e.g. `g = n a′` with `a ∈ F[t]`). At `X`
only the constant term `G(0)` matters for the order of a pole: `y′ + G y = A / (X ^ m D₁)` forces
`ord_X y ≥ -m`, provided `u′ + (G(0) - r η) u = 0` has no non-zero solution in `F` for `r > m`.

* `rde_regularAt_X_poly`: `y X ^ m` is regular at `X`;
* `rde_denominator_exp_poly`: `y X ^ m D₁` is a polynomial `Y`, and
  `D₁ Y′ + ((G - m η) D₁ - D₁′) Y = A D₁`.
-/

open Polynomial

namespace Differential

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'] [Differential C'[X]]
variable [Field K] [Algebra C'[X] K] [IsFractionRing C'[X] K] [Differential K]
variable [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

theorem rde_regularAt_X_poly (η : C') (hD : ∀ P : C'[X], P′ = implicitDeriv (C η * X) P)
    (G : C'[X]) (m : ℕ) (hg : ∀ r : ℕ, m < r → ∀ e : C', e ≠ 0 → e′ + (G.coeff 0 - r * η) * e ≠ 0)
    (A D₁ : C'[X]) (hD₁ : ¬X ∣ D₁) (y : K)
    (h : y′ + φ G * y = φ A / (φ X ^ m * φ D₁)) :
    y * φ X ^ m ∈ regularAt K (X : C'[X]) prime_X := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hXp : Prime (X : C'[X]) := prime_X
  have hXm : φ X ∈ regularAt K X hXp := algebraMap_mem_regularAt hXp X
  have hX0 : φ X ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  by_cases hy0 : y = 0
  · rw [hy0, zero_mul]; exact zero_mem _
  obtain ⟨n, u, hu, hy⟩ := exists_zpow_mul_isUnitAt hXp hy0
  rcases le_or_gt (-(m : ℤ)) n with hn | hn
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, n + m = i := ⟨(n + m).toNat, by omega⟩
    rw [hy, mul_comm, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ hX0, add_comm, hi, zpow_natCast]
    exact mul_mem (pow_mem hXm i) (hu.mem_regularAt hXp)
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℕ, m < r ∧ n = -(r : ℤ) := ⟨n.natAbs, by omega, by omega⟩
  exfalso
  have hy' : y = u / φ X ^ r := by rw [hy, zpow_neg, zpow_natCast]; field_simp
  set g₀ := G.coeff 0 with hg₀
  have hG : G = C g₀ + X * G.divX := by rw [hg₀, add_comm, X_mul_divX_add]
  have hXr : (φ X ^ r)′ = φ (C (r * η)) * φ X ^ r := by
    rw [← map_pow, deriv_algebraMap, hD, deriv_X_pow, map_mul, map_pow]
  -- `(y′ + G y) X ^ r = u′ + (g₀ - r η) u + X (G₁ u)`
  have hkey : (y′ + φ G * y) * φ X ^ r =
      u′ + φ (C (g₀ - r * η)) * u + φ X * (φ G.divX * u) := by
    rw [hy', Derivation.leibniz_div, hXr]
    simp only [smul_eq_mul]
    have hXr0 : φ X ^ r ≠ 0 := pow_ne_zero _ hX0
    rw [C_sub, map_sub]
    conv_lhs => rw [hG]
    simp only [map_add, map_mul]
    field_simp
    ring
  have hunit := isUnitAt_X_deriv_add η hD (g₀ - r * η) (hg r hr) hu
  have hφD₁ : φ D₁ ≠ 0 := map_ne_zero_of_not_dvd hXp hD₁
  obtain ⟨j, hj⟩ : ∃ j, r = m + j + 1 := ⟨r - m - 1, by omega⟩
  refine hunit.ne_mul hXp (f := φ A * φ X ^ j / φ D₁ - φ G.divX * u)
    (sub_mem ⟨A * X ^ j, D₁, hD₁, by rw [map_mul, map_pow]; field_simp⟩
      (mul_mem (algebraMap_mem_regularAt hXp _) (hu.mem_regularAt hXp))) ?_
  have := hkey
  rw [h] at this
  have e : φ A / (φ X ^ m * φ D₁) * φ X ^ r = φ X * (φ A * φ X ^ j / φ D₁) := by
    rw [hj, pow_add, pow_add, pow_one]
    field_simp
  rw [e] at this
  linear_combination -this

/-- **The denominator in an exponential extension, polynomial coefficient.** -/
theorem rde_denominator_exp_poly (η : C') (hD : ∀ P : C'[X], P′ = implicitDeriv (C η * X) P)
    (hnorm : ∀ p : C'[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′) (G : C'[X]) (m : ℕ)
    (hg : ∀ r : ℕ, m < r → ∀ e : C', e ≠ 0 → e′ + (G.coeff 0 - r * η) * e ≠ 0)
    (A D₁ : C'[X]) (hD₁ : ¬X ∣ D₁) (y : K)
    (h : y′ + φ G * y = φ A / (φ X ^ m * φ D₁)) :
    ∃ Y : C'[X], y * (φ X ^ m * φ D₁) = φ Y ∧
      D₁ * Y′ + ((G - C (m * η)) * D₁ - D₁′) * Y = A * D₁ := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hD₁0 : D₁ ≠ 0 := fun h0 ↦ hD₁ (h0 ▸ dvd_zero X)
  have hφD₁ : φ D₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD₁0
  have hX0 : φ X ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  obtain ⟨Y, hY⟩ : ∃ Y : C'[X], y * (φ X ^ m * φ D₁) = φ Y := by
    refine exists_polynomial_of_regularAt _ fun p hm hp ↦ ?_
    by_cases hpX : p = X
    · subst hpX
      rw [← mul_assoc]
      exact mul_mem (rde_regularAt_X_poly η hD G m hg A D₁ hD₁ y h)
        (algebraMap_mem_regularAt _ D₁)
    · have hreg := rde_regularAt_of_normal p hp (hnorm p hm hp hpX) (φ G)
        (algebraMap_mem_regularAt hp.prime _) A (X ^ m * D₁)
        (mul_ne_zero (pow_ne_zero _ X_ne_zero) hD₁0) y (by rw [map_mul, map_pow]; exact h)
      rwa [map_mul, map_pow] at hreg
  refine ⟨Y, hY, ?_⟩
  have hyY : y = φ Y / (φ X ^ m * φ D₁) := by rw [← hY]; field_simp
  apply hinj
  simp only [map_add, map_mul, map_sub, ← deriv_algebraMap]
  have hXm' : (φ X ^ m)′ = φ (C (m * η)) * φ X ^ m := by
    rw [← map_pow, deriv_algebraMap, hD, deriv_X_pow, map_mul, map_pow]
  have h2 := h
  rw [hyY, Derivation.leibniz_div, Derivation.leibniz, hXm'] at h2
  simp only [smul_eq_mul] at h2
  have hXm0 : φ X ^ m ≠ 0 := pow_ne_zero _ hX0
  field_simp at h2
  field_simp
  have hCm : φ (C (m * η)) = φ (C (m : C')) * φ (C η) := by rw [C_mul, map_mul]
  rw [hCm] at h2
  linear_combination h2

end Differential
