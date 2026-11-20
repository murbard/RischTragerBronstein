import RischTragerBronstein.RDE.NoSolution
import RischTragerBronstein.Liouville.MonicPrimes

/-!
# The Risch differential equation with a coefficient that has poles

For `y′ + G y = f` where `G` has a pole of order `m ≥ 2` at a normal prime `p` (the situation of
`G = j a′`, `a` a rational function: the coefficient for `t = exp a`), the term `G y` dominates
`y′` at `p`: a pole of `y` of order `n ≥ 1` produces a pole of `y′ + G y` of order exactly `n + m`.
Hence `n ≤ e - m` when `f` has a pole of order at most `e` — the local denominator bound
(Bronstein, §6.1).
-/

open Polynomial

namespace Differential

variable {A K : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A] [Field K] [Algebra A K]
variable [IsFractionRing A K] [Differential A] [Differential K] [DifferentialAlgebra A K]
variable {p : A} (hp : Prime p)

local notation "φ" => algebraMap A K

include hp in
/-- The product of two units of `O_p` is a unit. -/
lemma IsUnitAt.mul' {g h : K} (hg : IsUnitAt K p g) (hh : IsUnitAt K p h) :
    IsUnitAt K p (g * h) := by
  obtain ⟨a, b, ha, hb, h1⟩ := hg
  obtain ⟨c, d, hc, hd, h2⟩ := hh
  refine ⟨a * c, b * d, fun hdvd ↦ (hp.dvd_or_dvd hdvd).elim ha hc,
    fun hdvd ↦ (hp.dvd_or_dvd hdvd).elim hb hd, ?_⟩
  rw [map_mul, map_mul, ← h1, ← h2]
  ring

include hp in
/-- **Local denominator bound at a pole of the coefficient.** If `G` has a pole of order `m ≥ 2` at
the normal prime `p`, `y` a pole of order `n ≥ 1`, and `y′ + G y` a pole of order at most `e`, then
`n + m ≤ e`. -/
theorem pole_order_le_of_rde (hnorm : ¬p ∣ p′) (hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : A))
    {G w y u : K} {m n e : ℕ} (hm : 2 ≤ m) (hn : n ≠ 0) (hw : IsUnitAt K p w)
    (hG : G * φ p ^ m = w) (hu : IsUnitAt K p u) (hy : y = u / φ p ^ n)
    (h : (y′ + G * y) * φ p ^ e ∈ regularAt K p hp) : n + m ≤ e := by
  by_contra hlt
  have hpm : φ p ∈ regularAt K p hp := algebraMap_mem_regularAt hp p
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  obtain ⟨d, hd⟩ : ∃ d, n + m = e + d + 1 := ⟨n + m - e - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hunit := isUnitAt_deriv_pole hp hnorm hu n (hnat n hn)
  rw [← hy] at hunit
  have hyreg : y′ * φ p ^ (n + 1) ∈ regularAt K p hp := hunit.mem_regularAt hp
  refine (hw.mul' hp hu).ne_mul hp
    (f := (y′ + G * y) * φ p ^ e * φ p ^ d - y′ * φ p ^ (n + 1) * φ p ^ m') ?_ ?_
  · exact sub_mem (mul_mem h (pow_mem hpm d)) (mul_mem hyreg (pow_mem hpm m'))
  · have hpn : φ p ^ n ≠ 0 := pow_ne_zero _ hp0
    have hGy : G * y * φ p ^ (n + (m' + 2)) = w * u := by
      rw [hy, ← hG]
      field_simp
      ring
    have hexp : φ p * ((y′ + G * y) * φ p ^ e * φ p ^ d - y′ * φ p ^ (n + 1) * φ p ^ m') =
        (y′ + G * y) * φ p ^ (e + d + 1) - y′ * φ p ^ (n + (m' + 2)) := by
      ring
    rw [hexp, ← hd, ← hGy]
    ring

section Base

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'[X]] [Field K] [Algebra C'[X] K]
variable [IsFractionRing C'[X] K] [Differential K] [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

/-- **Denominator bound for a rational coefficient.** Over `C(x)`, let `g = Gn / Gd` in lowest
terms have no simple pole (every prime factor of `Gd` is repeated — e.g. `g = j a′`). If
`y′ + g y = A / D`, then `y D` is a polynomial. -/
theorem rde_denominator_rational (hD : ∀ P : C'[X], P′ = derivative P) (Gn Gd A D : C'[X])
    (hD0 : D ≠ 0) (hGd0 : Gd ≠ 0) (hcop : IsCoprime Gn Gd)
    (hsq : ∀ p : C'[X], Irreducible p → p ∣ Gd → p ^ 2 ∣ Gd) (y : K)
    (h : y′ + φ Gn / φ Gd * y = φ A / φ D) : ∃ Y : C'[X], y * φ D = φ Y := by
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
  have hnorm : ¬p ∣ p′ := by
    rw [hD]
    intro hdvd
    have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
    have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
    exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
  have hnat := not_dvd_natCast_polynomial hp.prime
  -- `D = p ^ e * c`
  have hfin : FiniteMultiplicity p D := FiniteMultiplicity.of_not_isUnit hp.not_isUnit hD0
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  set e := multiplicity p D with he
  have hφc : φ c ≠ 0 := map_ne_zero_of_not_dvd hp.prime hpc
  have hrhs : (y′ + φ Gn / φ Gd * y) * φ p ^ e ∈ regularAt K p hp.prime := by
    rw [h]
    refine ⟨A, c, hpc, ?_⟩
    rw [hc, map_mul, map_pow]
    field_simp
  -- `p ^ k ∣ D`
  have hke : k ≤ e := by
    by_cases hpG : p ∣ Gd
    · -- a pole of the coefficient, of order `m ≥ 2`
      have hfinG : FiniteMultiplicity p Gd :=
        FiniteMultiplicity.of_not_isUnit hp.not_isUnit hGd0
      obtain ⟨c₁, hc₁, hpc₁⟩ := hfinG.exists_eq_pow_mul_and_not_dvd
      set m := multiplicity p Gd with hm
      have hm2 : 2 ≤ m := hfinG.le_multiplicity_of_pow_dvd (hsq p hp hpG)
      have hpGn : ¬p ∣ Gn := fun hdvd ↦
        hp.not_isUnit (hcop.isUnit_of_dvd' hdvd hpG)
      have hφc₁ : φ c₁ ≠ 0 := map_ne_zero_of_not_dvd hp.prime hpc₁
      have hw : IsUnitAt K p (φ Gn / φ c₁) := ⟨Gn, c₁, hpGn, hpc₁, by field_simp⟩
      have := pole_order_le_of_rde hp.prime hnorm hnat hm2 hk1 hw
        (by rw [hc₁, map_mul, map_pow]; field_simp) hu hy' hrhs
      omega
    · -- the coefficient is regular at `p`
      have hGreg : φ Gn / φ Gd ∈ regularAt K p hp.prime :=
        ⟨Gn, Gd, hpG, by
          have : φ Gd ≠ 0 := (map_ne_zero_iff _ hinj).mpr hGd0
          field_simp⟩
      by_contra hlt
      have hunit := isUnitAt_deriv_pole hp.prime hnorm hu k (hnat k hk1)
      rw [← hy'] at hunit
      obtain ⟨j, hj⟩ : ∃ j, k + 1 = e + (j + 1) + 1 := ⟨k - e - 1, by omega⟩
      refine hunit.ne_mul hp.prime
        (f := φ p ^ (j + 1) * ((y′ + φ Gn / φ Gd * y) * φ p ^ e) - φ Gn / φ Gd * u) ?_ ?_
      · exact sub_mem (mul_mem (pow_mem hpm _) hrhs)
          (mul_mem hGreg (hu.mem_regularAt hp.prime))
      · have hpn : φ p ^ k ≠ 0 := pow_ne_zero _ hp0
        have hGy : φ Gn / φ Gd * y * φ p ^ (k + 1) = φ p * (φ Gn / φ Gd * u) := by
          rw [hy', pow_succ]
          field_simp
        have hsplit : y′ * φ p ^ (k + 1) =
            (y′ + φ Gn / φ Gd * y) * φ p ^ (k + 1) - φ Gn / φ Gd * y * φ p ^ (k + 1) := by ring
        rw [hsplit, hGy, hj]
        ring
  obtain ⟨i, hi⟩ : ∃ i, e = k + i := ⟨e - k, by omega⟩
  rw [hy', hc, hi, map_mul, map_pow, pow_add]
  have : u / φ p ^ k * (φ p ^ k * φ p ^ i * φ c) = u * (φ p ^ i * φ c) := by field_simp
  rw [this]
  exact mul_mem (hu.mem_regularAt hp.prime)
    (mul_mem (pow_mem hpm i) (algebraMap_mem_regularAt _ c))

/-- **Reduction to a polynomial ODE.** With `y = Y / D`:
`(Gd D) Y′ + (Gn D - Gd D′) Y = A D Gd`. -/
theorem rde_rationalG_iff (hD : ∀ P : C'[X], P′ = derivative P) (Gn Gd A D : C'[X])
    (hD0 : D ≠ 0) (hGd0 : Gd ≠ 0) (hcop : IsCoprime Gn Gd)
    (hsq : ∀ p : C'[X], Irreducible p → p ∣ Gd → p ^ 2 ∣ Gd) :
    (∃ y : K, y′ + φ Gn / φ Gd * y = φ A / φ D) ↔
      ∃ Y : C'[X], Gd * D * derivative Y + (Gn * D - Gd * derivative D) * Y = A * D * Gd := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hφD : φ D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD0
  have hφGd : φ Gd ≠ 0 := (map_ne_zero_iff _ hinj).mpr hGd0
  have hder : ∀ Y : C'[X], (φ Y / φ D)′ = (φ (derivative Y) * φ D - φ Y * φ (derivative D)) /
      φ D ^ 2 := fun Y ↦ by
    rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD, hD]
    simp only [smul_eq_mul]
    ring
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨Y, hY⟩ := rde_denominator_rational hD Gn Gd A D hD0 hGd0 hcop hsq y hy
    have hyY : y = φ Y / φ D := by rw [← hY]; field_simp
    refine ⟨Y, hinj ?_⟩
    rw [hyY, hder] at hy
    simp only [map_add, map_mul, map_sub]
    field_simp at hy
    linear_combination hy
  · rintro ⟨Y, hY⟩
    refine ⟨φ Y / φ D, ?_⟩
    have := congrArg φ hY
    simp only [map_add, map_mul, map_sub] at this
    rw [hder]
    field_simp
    linear_combination this

/-- **The homogeneous equation.** If `η = Gn / Gd ≠ 0` is in lowest terms, without simple poles and
with `deg Gn + 1 ≠ deg Gd`, then `y′ = c η y` (`c ≠ 0` a constant) has only the zero solution in
`C(x)`: no nonzero power of a hyperexponential `t′ = η t` lies in `C(x)`. -/
theorem rde_homogeneous_rational (hD : ∀ P : C'[X], P′ = derivative P) (Gn Gd : C'[X])
    (hGn0 : Gn ≠ 0) (hGd0 : Gd ≠ 0) (hcop : IsCoprime Gn Gd)
    (hsq : ∀ p : C'[X], Irreducible p → p ∣ Gd → p ^ 2 ∣ Gd)
    (hdeg : Gn.natDegree + 1 ≠ Gd.natDegree) (c : C') (hc : c ≠ 0) (y : K)
    (h : y′ = φ (C c) * (φ Gn / φ Gd) * y) : y = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hφGd : φ Gd ≠ 0 := (map_ne_zero_iff _ hinj).mpr hGd0
  have hu : IsUnit (C (-c) : C'[X]) := isUnit_C.mpr (neg_ne_zero.mpr hc).isUnit
  have hcop' : IsCoprime (C (-c) * Gn) Gd := (isCoprime_mul_unit_left_left hu Gn Gd).mpr hcop
  obtain ⟨Y, hY⟩ := rde_denominator_rational hD (C (-c) * Gn) Gd 0 1 one_ne_zero hGd0 hcop' hsq y
    (by rw [h, map_mul, C_neg, map_neg, map_zero, zero_div]; ring)
  rw [map_one, mul_one] at hY
  subst hY
  rw [deriv_algebraMap, hD] at h
  have hpoly : Gd * derivative Y = C c * Gn * Y := by
    apply hinj
    rw [map_mul, map_mul, map_mul, h]
    field_simp
  by_contra hY0
  have hY0' : Y ≠ 0 := fun h0 ↦ hY0 (by rw [h0, map_zero])
  have hR : C c * Gn * Y ≠ 0 := mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hc) hGn0) hY0'
  have hd0 : derivative Y ≠ 0 := fun h0 ↦ hR (by rw [← hpoly, h0, mul_zero])
  have hYdeg : Y.natDegree ≠ 0 := fun h0 ↦ hd0 (by
    rw [eq_C_of_natDegree_eq_zero h0, derivative_C])
  have hderdeg : (derivative Y).natDegree = Y.natDegree - 1 := by
    refine le_antisymm (natDegree_derivative_le Y) (le_natDegree_of_ne_zero ?_)
    rw [coeff_derivative, Nat.sub_add_cancel (Nat.pos_of_ne_zero hYdeg), coeff_natDegree]
    refine mul_ne_zero (leadingCoeff_ne_zero.mpr hY0') ?_
    have : ((Y.natDegree - 1 : ℕ) : C') + 1 = (Y.natDegree : C') := by
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero hYdeg)]
    rw [this]
    exact Nat.cast_ne_zero.mpr hYdeg
  have := congrArg natDegree hpoly
  rw [natDegree_mul hGd0 hd0, natDegree_mul (mul_ne_zero (C_ne_zero.mpr hc) hGn0) hY0',
    natDegree_C_mul hc, hderdeg] at this
  omega

end Base

section Pivot

variable {C' : Type*} [Field C'] [CharZero C']

/-- **Pivot analysis.** For `P₁ = Gd D`, `P₀ = Gn D - Gd D′` with `deg Gn + 1 ≠ deg Gd`: `P₀ ≠ 0`, and
the pivot `k lc₁ + lc₀` (at `dg = max (deg P₁ - 1) (deg P₀)`) can vanish only for `k ≤ deg D`. -/
theorem rde_pivot (Gn Gd D : C'[X]) (hGn0 : Gn ≠ 0) (hGd0 : Gd ≠ 0) (hD0 : D ≠ 0)
    (hdeg : Gn.natDegree + 1 ≠ Gd.natDegree) :
    Gn * D - Gd * derivative D ≠ 0 ∧ ∀ k : ℕ,
      (k : C') * (Gd * D).coeff (max ((Gd * D).natDegree - 1)
          (Gn * D - Gd * derivative D).natDegree + 1) +
        (Gn * D - Gd * derivative D).coeff (max ((Gd * D).natDegree - 1)
          (Gn * D - Gd * derivative D).natDegree) = 0 → k ≤ D.natDegree := by
  have hn₁ : (Gd * D).natDegree = Gd.natDegree + D.natDegree := natDegree_mul hGd0 hD0
  have hnD : (Gn * D).natDegree = Gn.natDegree + D.natDegree := natDegree_mul hGn0 hD0
  have hD'deg : (Gd * derivative D).natDegree ≤ Gd.natDegree + (D.natDegree - 1) :=
    natDegree_mul_le.trans (Nat.add_le_add_left (natDegree_derivative_le D) _)
  rcases Nat.lt_or_ge Gn.natDegree Gd.natDegree with hlt | hge
  · -- `deg Gn + 2 ≤ deg Gd`
    have hB : Gn.natDegree + 2 ≤ Gd.natDegree := by omega
    obtain ⟨n₁, hn₁def⟩ : ∃ n, n = Gd.natDegree + D.natDegree := ⟨_, rfl⟩
    have hGD' : (Gd * derivative D).natDegree ≤ n₁ - 1 := by
      rcases Nat.eq_zero_or_pos D.natDegree with hd0 | hdpos
      · rw [eq_C_of_natDegree_eq_zero hd0, derivative_C, mul_zero, natDegree_zero]
        exact Nat.zero_le _
      · exact hD'deg.trans (by omega)
    have hP₀deg : (Gn * D - Gd * derivative D).natDegree ≤ n₁ - 1 :=
      (natDegree_sub_le _ _).trans (max_le (by rw [hnD]; omega) hGD')
    have hcoeff : (Gn * D - Gd * derivative D).coeff (n₁ - 1) =
        -((D.natDegree : C') * (Gd.leadingCoeff * D.leadingCoeff)) := by
      rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (by rw [hnD]; omega), zero_sub]
      rcases Nat.eq_zero_or_pos D.natDegree with hd0 | hdpos
      · rw [eq_C_of_natDegree_eq_zero hd0, derivative_C, mul_zero, coeff_zero]
        simp [hd0]
      · have : n₁ - 1 = Gd.natDegree + (D.natDegree - 1) := by omega
        rw [this, coeff_mul_add_eq_of_natDegree_le le_rfl (natDegree_derivative_le D),
          coeff_derivative, Nat.sub_add_cancel hdpos]
        simp only [coeff_natDegree]
        have : ((D.natDegree - 1 : ℕ) : C') + 1 = (D.natDegree : C') := by
          rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hdpos]
        rw [this]
        ring
    have hL : Gd.leadingCoeff * D.leadingCoeff ≠ 0 :=
      mul_ne_zero (leadingCoeff_ne_zero.mpr hGd0) (leadingCoeff_ne_zero.mpr hD0)
    refine ⟨fun h0 ↦ ?_, fun k hk ↦ ?_⟩
    · rw [h0, coeff_zero] at hcoeff
      have hd0 : D.natDegree = 0 := by
        by_contra hne
        exact (neg_ne_zero.mpr (mul_ne_zero (Nat.cast_ne_zero.mpr hne) hL)) hcoeff.symm
      rw [eq_C_of_natDegree_eq_zero hd0, derivative_C, mul_zero, sub_zero] at h0
      rw [← eq_C_of_natDegree_eq_zero hd0] at h0
      exact mul_ne_zero hGn0 hD0 h0
    · rw [hn₁, ← hn₁def, max_eq_left hP₀deg, show n₁ - 1 + 1 = n₁ by omega, hcoeff] at hk
      have hlc : (Gd * D).coeff n₁ = Gd.leadingCoeff * D.leadingCoeff := by
        rw [hn₁def, ← hn₁, coeff_natDegree, leadingCoeff_mul]
      rw [hlc] at hk
      have : ((k : C') - D.natDegree) * (Gd.leadingCoeff * D.leadingCoeff) = 0 := by
        linear_combination hk
      have := (mul_eq_zero.mp this).resolve_right hL
      have : (k : C') = (D.natDegree : C') := sub_eq_zero.mp this
      exact (Nat.cast_injective this).le
  · -- `deg Gd ≤ deg Gn`: `Gn D` dominates
    have hlt' : (Gd * derivative D).natDegree < (Gn * D).natDegree ∨ Gd * derivative D = 0 := by
      by_cases h0 : derivative D = 0
      · right; rw [h0, mul_zero]
      · left
        have hdpos : D.natDegree ≠ 0 := fun h ↦ h0 (by
          rw [eq_C_of_natDegree_eq_zero h, derivative_C])
        rw [hnD]
        omega
    have hP₀ : (Gn * D - Gd * derivative D).natDegree = Gn.natDegree + D.natDegree ∧
        (Gn * D - Gd * derivative D).leadingCoeff = Gn.leadingCoeff * D.leadingCoeff := by
      rcases hlt' with h | h
      · rw [natDegree_sub_eq_left_of_natDegree_lt h, hnD]
        refine ⟨rfl, ?_⟩
        rw [leadingCoeff_sub_of_degree_lt (degree_lt_degree h), leadingCoeff_mul]
      · rw [h, sub_zero, hnD, leadingCoeff_mul]
        exact ⟨rfl, rfl⟩
    have hL : Gn.leadingCoeff * D.leadingCoeff ≠ 0 :=
      mul_ne_zero (leadingCoeff_ne_zero.mpr hGn0) (leadingCoeff_ne_zero.mpr hD0)
    refine ⟨fun h0 ↦ hL (by rw [← hP₀.2, h0, leadingCoeff_zero]), fun k hk ↦ ?_⟩
    rw [hP₀.1, hn₁, max_eq_right (by omega),
      coeff_eq_zero_of_natDegree_lt (by rw [hn₁]; omega), mul_zero, zero_add, ← hP₀.1,
      coeff_natDegree, hP₀.2] at hk
    exact absurd hk hL

end Pivot

end Differential
