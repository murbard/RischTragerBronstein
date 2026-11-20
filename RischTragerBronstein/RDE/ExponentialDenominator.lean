import RischTragerBronstein.RDE.PrimitiveDenominator
import RischTragerBronstein.Liouville.ExponentialPoly

/-!
# The Risch differential equation in an exponential extension: the denominator

`K = F(t)`, `t′ = η t` (`η ∈ F`), coefficient `g ∈ F`. Every irreducible other than `X` is normal;
at `X` the equation `y′ + g y = A / (X ^ m D₁)` (`X ∤ D₁`) forces `ord_X y ≥ -m`, provided
`u′ + (g - r η) u = 0` has no non-zero solution in `F` for `r > m`.

* `rde_regularAt_of_normal`: `y D` is regular at every normal prime;
* `rde_regularAt_X`: `y X ^ m` is regular at `X`;
* `rde_denominator_exp`: `y X ^ m D₁` is a polynomial `Y`, and
  `D₁ Y′ + ((g - m η) D₁ - D₁′) Y = A D₁`.
-/

open Polynomial

namespace Differential

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'] [Differential C'[X]]
variable [Field K] [Algebra C'[X] K] [IsFractionRing C'[X] K] [Differential K]
variable [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

/-- Regularity of `y D` at one normal prime `p` at which `g` is regular. -/
theorem rde_regularAt_of_normal (p : C'[X]) (hp : Irreducible p) (hnorm : ¬p ∣ p′)
    (g : K) (hg : g ∈ regularAt K p hp.prime) (A D : C'[X]) (hD0 : D ≠ 0) (y : K)
    (h : y′ + g * y = φ A / φ D) : y * φ D ∈ regularAt K p hp.prime := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
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
    by_contra hlt
    have hunit := isUnitAt_deriv_pole hp.prime hnorm hu k (hnat k hk1)
    rw [← hy'] at hunit
    obtain ⟨j, hj⟩ : ∃ j, k + 1 = e + (j + 1) + 1 := ⟨k - e - 1, by omega⟩
    refine hunit.ne_mul hp.prime
      (f := φ p ^ (j + 1) * ((y′ + g * y) * φ p ^ e) - g * u) ?_ ?_
    · exact sub_mem (mul_mem (pow_mem hpm _) hrhs)
        (mul_mem hg (hu.mem_regularAt hp.prime))
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

/-- At the special prime `X` of an exponential extension, `u′ + c u` is a unit whenever `u` is,
provided `u₀′ + c u₀ = 0` has no non-zero solution in `F`. -/
theorem isUnitAt_X_deriv_add (η : C') (hD : ∀ P : C'[X], P′ = implicitDeriv (C η * X) P)
    (c : C') (hc : ∀ e : C', e ≠ 0 → e′ + c * e ≠ 0) {u : K} (hu : IsUnitAt K (X : C'[X]) u) :
    IsUnitAt K (X : C'[X]) (u′ + φ (C c) * u) := by
  obtain ⟨N, Dn, hN, hDn, hND⟩ := hu
  have hXp : Prime (X : C'[X]) := prime_X
  have hφDn : φ Dn ≠ 0 := map_ne_zero_of_not_dvd hXp hDn
  have hu' : u = φ N / φ Dn := by rw [← hND]; field_simp
  have hN0 : N.coeff 0 ≠ 0 := fun h0 ↦ hN (X_dvd_iff.mpr h0)
  have hDn0 : Dn.coeff 0 ≠ 0 := fun h0 ↦ hDn (X_dvd_iff.mpr h0)
  refine ⟨N′ * Dn - N * Dn′ + C c * N * Dn, Dn * Dn, ?_,
    fun hdvd ↦ (hXp.dvd_or_dvd hdvd).elim hDn hDn, ?_⟩
  · intro hdvd
    rw [X_dvd_iff] at hdvd
    simp only [coeff_add, coeff_sub, mul_coeff_zero, hD, coeff_implicitDeriv_C_mul_X,
      Nat.cast_zero, zero_mul, mul_zero, add_zero, coeff_C_zero] at hdvd
    have hz : Dn.coeff 0 ^ 2 * ((N.coeff 0 / Dn.coeff 0)′ + c * (N.coeff 0 / Dn.coeff 0)) = 0 := by
      rw [Derivation.leibniz_div]
      simp only [smul_eq_mul]
      field_simp
      linear_combination hdvd
    exact hc _ (div_ne_zero hN0 hDn0)
      ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hDn0))
  · rw [hu', Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap]
    simp only [smul_eq_mul, map_add, map_sub, map_mul]
    field_simp

/-- **The order at `X`.** If `y′ + g y = A / (X ^ m D₁)` with `X ∤ D₁`, then `y X ^ m` is regular
at `X`. -/
theorem rde_regularAt_X (η : C') (hD : ∀ P : C'[X], P′ = implicitDeriv (C η * X) P) (g₀ : C')
    (hg : ∀ r : ℕ, 0 < r → ∀ e : C', e ≠ 0 → e′ + (g₀ - r * η) * e ≠ 0)
    (A D₁ : C'[X]) (m : ℕ) (hD₁ : ¬X ∣ D₁) (y : K)
    (h : y′ + φ (C g₀) * y = φ A / (φ X ^ m * φ D₁)) :
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
  -- `(y′ + g y) X ^ r = u′ + (g - r η) u`, a unit
  have hXr : (φ X ^ r)′ = φ (C (r * η)) * φ X ^ r := by
    rw [← map_pow, deriv_algebraMap, hD, deriv_X_pow, map_mul, map_pow]
  have hkey : (y′ + φ (C g₀) * y) * φ X ^ r = u′ + φ (C (g₀ - r * η)) * u := by
    rw [hy', Derivation.leibniz_div, hXr]
    simp only [smul_eq_mul]
    have hXr0 : φ X ^ r ≠ 0 := pow_ne_zero _ hX0
    rw [C_sub, map_sub]
    field_simp
    ring
  have hunit := isUnitAt_X_deriv_add η hD (g₀ - r * η) (hg r (by omega)) hu
  rw [← hkey, h] at hunit
  -- but `A X ^ r / (X ^ m D₁) = X * (A X ^ (r - m - 1) / D₁)` is in the maximal ideal
  have hφD₁ : φ D₁ ≠ 0 := map_ne_zero_of_not_dvd hXp hD₁
  obtain ⟨j, hj⟩ : ∃ j, r = m + j + 1 := ⟨r - m - 1, by omega⟩
  refine hunit.ne_mul hXp (f := φ A * φ X ^ j / φ D₁) ⟨A * X ^ j, D₁, hD₁, by
    rw [map_mul, map_pow]; field_simp⟩ ?_
  rw [hj, pow_add, pow_add, pow_one]
  field_simp

/-- **The denominator in an exponential extension.** -/
theorem rde_denominator_exp (η : C') (hD : ∀ P : C'[X], P′ = implicitDeriv (C η * X) P)
    (hnorm : ∀ p : C'[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′) (g₀ : C')
    (hg : ∀ r : ℕ, 0 < r → ∀ e : C', e ≠ 0 → e′ + (g₀ - r * η) * e ≠ 0)
    (A D₁ : C'[X]) (m : ℕ) (hD₁ : ¬X ∣ D₁) (y : K)
    (h : y′ + φ (C g₀) * y = φ A / (φ X ^ m * φ D₁)) :
    ∃ Y : C'[X], y * (φ X ^ m * φ D₁) = φ Y ∧
      D₁ * Y′ + (C (g₀ - m * η) * D₁ - D₁′) * Y = A * D₁ := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hD₁0 : D₁ ≠ 0 := fun h0 ↦ hD₁ (h0 ▸ dvd_zero X)
  have hφD₁ : φ D₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD₁0
  have hX0 : φ X ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  obtain ⟨Y, hY⟩ : ∃ Y : C'[X], y * (φ X ^ m * φ D₁) = φ Y := by
    refine exists_polynomial_of_regularAt _ fun p hm hp ↦ ?_
    by_cases hpX : p = X
    · subst hpX
      rw [← mul_assoc]
      exact mul_mem (rde_regularAt_X η hD g₀ hg A D₁ m hD₁ y h)
        (algebraMap_mem_regularAt _ D₁)
    · have hreg := rde_regularAt_of_normal p hp (hnorm p hm hp hpX) (φ (C g₀))
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
  rw [hyY] at hY
  have hXm0 : φ X ^ m ≠ 0 := pow_ne_zero _ hX0
  field_simp at h2
  field_simp
  have hCm : φ (C (m * η)) = φ (C (m : C')) * φ (C η) := by rw [C_mul, map_mul]
  rw [hCm] at h2
  linear_combination h2

end Differential
