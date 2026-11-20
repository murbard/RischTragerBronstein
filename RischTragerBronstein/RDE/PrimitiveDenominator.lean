import RischTragerBronstein.RDE.RationalCoeff
import RischTragerBronstein.Liouville.PrimitivePoly

/-!
# The Risch differential equation in a primitive extension: denominator and uniqueness

`K = F(t)` a fraction field of `F[X]` in which every irreducible is normal (`t′ = η ∈ F`), and a
coefficient `g` regular at every prime (`g ∈ F`).

* `rde_denominator_regular`: `y′ + g y = A / D` ⟹ `y D` is a polynomial;
* `rde_poly_of_rde`: with `y = Y / D`: `D Y′ + (g D - D′) Y = A D`;
* `eq_zero_of_rde_homogeneous`: `y′ + g y = 0` and `g` not a logarithmic derivative in `F`
  ⟹ `y = 0` (a solution would have `y′ / y = -g` without poles, hence lie in `F`).
-/

open Polynomial

namespace Differential

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'[X]] [Field K] [Algebra C'[X] K]
variable [IsFractionRing C'[X] K] [Differential K] [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

theorem rde_denominator_regular (hnorm : ∀ p : C'[X], Irreducible p → ¬p ∣ p′)
    (g : K) (hg : ∀ p : C'[X], (hp : Irreducible p) → g ∈ regularAt K p hp.prime)
    (A D : C'[X]) (hD0 : D ≠ 0) (y : K) (h : y′ + g * y = φ A / φ D) :
    ∃ Y : C'[X], y * φ D = φ Y := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  refine exists_polynomial_of_regularAt _ fun p _ hp ↦ ?_
  have hpm : φ p ∈ regularAt K p hp.prime := algebraMap_mem_regularAt hp.prime p
  have hp0 : φ p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
  by_cases hy0 : y = 0
  · rw [hy0, zero_mul]; exact zero_mem _
  obtain ⟨n, u, hu, hy⟩ := exists_zpow_mul_isUnitAt hp.prime hy0
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [hy, zpow_natCast]
    exact mul_mem (mul_mem (pow_mem hpm m) (hu.mem_regularAt hp.prime))
      (algebraMap_mem_regularAt _ D)
  obtain ⟨k, hk1, rfl⟩ : ∃ k : ℕ, k ≠ 0 ∧ n = -(k : ℤ) := ⟨n.natAbs, by omega, by omega⟩
  have hy' : y = u / φ p ^ k := by rw [hy, zpow_neg, zpow_natCast]; field_simp
  have hnat := not_dvd_natCast_polynomial hp.prime
  have hfin : FiniteMultiplicity p D := FiniteMultiplicity.of_not_isUnit hp.not_isUnit hD0
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  set e := multiplicity p D with he
  have hφc : φ c ≠ 0 := map_ne_zero_of_not_dvd hp.prime hpc
  have hrhs : (y′ + g * y) * φ p ^ e ∈ regularAt K p hp.prime := by
    rw [h]
    refine ⟨A, c, hpc, ?_⟩
    rw [hc, map_mul, map_pow]
    field_simp
  have hke : k ≤ e := by
    have hGreg : g ∈ regularAt K p hp.prime := hg p hp
    by_contra hlt
    have hunit := isUnitAt_deriv_pole hp.prime (hnorm p hp) hu k (hnat k hk1)
    rw [← hy'] at hunit
    obtain ⟨j, hj⟩ : ∃ j, k + 1 = e + (j + 1) + 1 := ⟨k - e - 1, by omega⟩
    refine hunit.ne_mul hp.prime
      (f := φ p ^ (j + 1) * ((y′ + g * y) * φ p ^ e) - g * u) ?_ ?_
    · exact sub_mem (mul_mem (pow_mem hpm _) hrhs)
        (mul_mem hGreg (hu.mem_regularAt hp.prime))
    · have hpn : φ p ^ k ≠ 0 := pow_ne_zero _ hp0
      have hGy : g * y * φ p ^ (k + 1) = φ p * (g * u) := by
        rw [hy', pow_succ]
        field_simp
      have hsplit : y′ * φ p ^ (k + 1) = (y′ + g * y) * φ p ^ (k + 1) - g * y * φ p ^ (k + 1) := by
        ring
      rw [hsplit, hGy, hj]
      ring
  obtain ⟨i, hi⟩ : ∃ i, e = k + i := ⟨e - k, by omega⟩
  rw [hy', hc, hi, map_mul, map_pow, pow_add]
  have : u / φ p ^ k * (φ p ^ k * φ p ^ i * φ c) = u * (φ p ^ i * φ c) := by field_simp
  rw [this]
  exact mul_mem (hu.mem_regularAt hp.prime)
    (mul_mem (pow_mem hpm i) (algebraMap_mem_regularAt _ c))

/-- With `y = Y / D`: the polynomial ODE `D Y′ + (g D - D′) Y = A D`. -/
theorem rde_poly_of_rde (g₀ : C'[X]) (A D Y : C'[X]) (hD0 : D ≠ 0) (y : K)
    (hy : y * φ D = φ Y) (h : y′ + φ g₀ * y = φ A / φ D) :
    D * Y′ + (g₀ * D - D′) * Y = A * D := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hφD : φ D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD0
  have hyY : y = φ Y / φ D := by rw [← hy]; field_simp
  apply hinj
  simp only [map_add, map_mul, map_sub, ← deriv_algebraMap]
  rw [← hy, Derivation.leibniz]
  simp only [smul_eq_mul]
  rw [hyY] at h
  have h2 := h
  rw [Derivation.leibniz_div] at h2
  simp only [smul_eq_mul] at h2
  rw [hyY, Derivation.leibniz_div]
  simp only [smul_eq_mul]
  field_simp
  field_simp at h2
  linear_combination h2

/-- **Uniqueness**: `y′ + g y = 0` with `g ∈ F` not the negative of a logarithmic derivative in
`F` forces `y = 0`. -/
theorem eq_zero_of_rde_homogeneous [Differential C'] (hnorm : ∀ p : C'[X], Irreducible p → ¬p ∣ p′)
    (η g₀ : C') (hD : ∀ P : C'[X], P′ = implicitDeriv (C η) P)
    (hgnl : ∀ e : C', e ≠ 0 → e′ + g₀ * e ≠ 0) (y : K) (h : y′ + φ (C g₀) * y = 0) : y = 0 := by
  obtain ⟨Y, hY⟩ := rde_denominator_regular hnorm (φ (C g₀))
    (fun p hp ↦ algebraMap_mem_regularAt hp.prime _) 0 1 one_ne_zero y
    (by rw [h, map_zero, zero_div])
  rw [map_one, mul_one] at hY
  have hpoly := rde_poly_of_rde (K := K) (C g₀) 0 1 Y one_ne_zero y (by rw [map_one, mul_one, hY])
    (by rw [h, map_zero, zero_div])
  have h1 : (1 : C'[X])′ = 0 := by
    rw [hD, ← C_1, implicitDeriv_C, Derivation.map_one_eq_zero, C_0]
  rw [h1, hD] at hpoly
  simp only [one_mul, mul_one, sub_zero, zero_mul] at hpoly
  have hY0 : Y = 0 := by
    by_contra hne
    have hc := congrArg (fun Q : C'[X] ↦ Q.coeff Y.natDegree) hpoly
    simp only [coeff_add, coeff_implicitDeriv_C, coeff_C_mul, coeff_zero] at hc
    rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self Y.natDegree), zero_mul, mul_zero,
      add_zero] at hc
    exact hgnl _ (leadingCoeff_ne_zero.mpr hne) hc
  rw [hY, hY0, map_zero]

end Differential
