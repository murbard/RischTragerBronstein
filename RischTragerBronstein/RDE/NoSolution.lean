import RischTragerBronstein.Liouville.PoleOrder
import RischTragerBronstein.Liouville.MonicPrimes
import RischTragerBronstein.Liouville.Reduce

/-!
# Risch differential equations without rational solutions

* `mem_regularAt_of_rde`: if `y′ + G y` is regular at a normal prime `p` and `G` is regular at `p`,
  then `y` is regular at `p` — a solution of a Risch differential equation with polynomial
  coefficients has no poles at normal primes.
* `rde_no_solution`: over `K = C(x)` with `d/dx`, the equation `y′ + g y = f` with `g, f ∈ C[x]`,
  `f ≠ 0` and `deg f < deg g` has no solution `y ∈ K`.

With `g = 2x`, `f = 1` this is the classical obstruction to integrating `exp (x²)` in elementary
terms; it is the prototype of the "no solution" branch of the Risch algorithm, where the absence of
a solution to a Risch differential equation is the *proof* of non-elementarity.
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace Differential

section Local

variable {A K : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A] [Field K] [Algebra A K]
variable [IsFractionRing A K] [Differential A] [Differential K] [DifferentialAlgebra A K]
variable {p : A} (hp : Prime p)

local notation "φ" => algebraMap A K

include hp in
theorem mem_regularAt_of_rde (hnorm : ¬p ∣ p′) (hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : A))
    {y G : K} (hG : G ∈ regularAt K p hp) (h : y′ + G * y ∈ regularAt K p hp) :
    y ∈ regularAt K p hp := by
  have hpm : φ p ∈ regularAt K p hp := algebraMap_mem_regularAt hp p
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  by_cases hy0 : y = 0
  · rw [hy0]; exact zero_mem _
  obtain ⟨n, u, hu, hy⟩ := exists_zpow_mul_isUnitAt hp hy0
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [hy, zpow_natCast]
    exact mul_mem (pow_mem hpm m) (hu.mem_regularAt hp)
  exfalso
  obtain ⟨k, hk1, rfl⟩ : ∃ k : ℕ, k ≠ 0 ∧ n = -(k : ℤ) := ⟨n.natAbs, by omega, by omega⟩
  have hy' : y = u / φ p ^ k := by rw [hy, zpow_neg, zpow_natCast]; field_simp
  have hunit := isUnitAt_deriv_pole hp hnorm hu k (hnat k hk1)
  rw [← hy'] at hunit
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine hunit.ne_mul hp (f := φ p ^ (j + 1) * (y′ + G * y) - G * u) ?_ ?_
  · exact sub_mem (mul_mem (pow_mem hpm _) h) (mul_mem hG (hu.mem_regularAt hp))
  · rw [hy']
    field_simp
    ring

include hp in
/-- If `y′ + G y` has at most a simple pole at the normal prime `p` and `G` is regular at `p`, then
`y` is regular at `p` (a pole of `y` of order `k ≥ 1` would give a pole of order `k + 1 ≥ 2`). -/
theorem mem_regularAt_of_rde' (hnorm : ¬p ∣ p′) (hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : A))
    {y G : K} (hG : G ∈ regularAt K p hp) (h : (y′ + G * y) * φ p ∈ regularAt K p hp) :
    y ∈ regularAt K p hp := by
  have hpm : φ p ∈ regularAt K p hp := algebraMap_mem_regularAt hp p
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  by_cases hy0 : y = 0
  · rw [hy0]; exact zero_mem _
  obtain ⟨n, u, hu, hy⟩ := exists_zpow_mul_isUnitAt hp hy0
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [hy, zpow_natCast]
    exact mul_mem (pow_mem hpm m) (hu.mem_regularAt hp)
  exfalso
  obtain ⟨k, hk1, rfl⟩ : ∃ k : ℕ, k ≠ 0 ∧ n = -(k : ℤ) := ⟨n.natAbs, by omega, by omega⟩
  have hy' : y = u / φ p ^ k := by rw [hy, zpow_neg, zpow_natCast]; field_simp
  have hunit := isUnitAt_deriv_pole hp hnorm hu k (hnat k hk1)
  rw [← hy'] at hunit
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine hunit.ne_mul hp (f := φ p ^ j * ((y′ + G * y) * φ p) - G * u) ?_ ?_
  · exact sub_mem (mul_mem (pow_mem hpm _) h) (mul_mem hG (hu.mem_regularAt hp))
  · rw [hy']
    field_simp
    ring

end Local

section Base

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'[X]] [Field K] [Algebra C'[X] K]
variable [IsFractionRing C'[X] K] [Differential K] [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

/-- Over `C(x)` with `d/dx`: `y′ + g y = f`, `f ≠ 0`, `deg f < deg g`, has no solution. -/
theorem rde_no_solution (hD : ∀ P : C'[X], P′ = derivative P) (g f : C'[X]) (hf : f ≠ 0)
    (hdeg : f.natDegree < g.natDegree) (y : K) : y′ + φ g * y ≠ φ f := by
  intro h
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  -- `y` is a polynomial
  obtain ⟨Y, rfl⟩ : ∃ Y : C'[X], y = φ Y := by
    refine exists_polynomial_of_regularAt y fun p _ hp ↦ ?_
    refine mem_regularAt_of_rde hp.prime ?_ (not_dvd_natCast_polynomial hp.prime)
      (algebraMap_mem_regularAt _ g) (h ▸ algebraMap_mem_regularAt _ f)
    rw [hD]
    intro hdvd
    have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
    have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
    exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
  have hpoly : derivative Y + g * Y = f := by
    apply hinj
    rw [map_add, map_mul, ← hD, ← deriv_algebraMap]
    exact h
  -- degree count
  have hg0 : g ≠ 0 := fun h0 ↦ by simp [h0] at hdeg
  have hY0 : Y ≠ 0 := fun h0 ↦ hf (by rw [← hpoly, h0]; simp)
  have hlt : (derivative Y).degree < (g * Y).degree := by
    refine lt_of_lt_of_le (degree_derivative_lt hY0) ?_
    rw [degree_mul]
    exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hg0)
  have : f.natDegree = g.natDegree + Y.natDegree := by
    rw [← hpoly, add_comm, natDegree_add_eq_left_of_degree_lt hlt, natDegree_mul hg0 hY0]
  omega

/-- Over `C(x)` with `d/dx`: the homogeneous equation `y′ + g y = 0`, `deg g ≥ 1`, has only the zero
solution. (So `exp (∫ g)` is not in `C(x)`, and adjoining it creates no new constants.) -/
theorem rde_homogeneous (hD : ∀ P : C'[X], P′ = derivative P) (g : C'[X])
    (hdeg : 0 < g.natDegree) (y : K) (h : y′ + φ g * y = 0) : y = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  obtain ⟨Y, rfl⟩ : ∃ Y : C'[X], y = φ Y := by
    refine exists_polynomial_of_regularAt y fun p _ hp ↦ ?_
    refine mem_regularAt_of_rde hp.prime ?_ (not_dvd_natCast_polynomial hp.prime)
      (algebraMap_mem_regularAt _ g) (h ▸ zero_mem _)
    rw [hD]
    intro hdvd
    have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
    have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
    exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
  have hpoly : derivative Y + g * Y = 0 := by
    apply hinj
    rw [map_add, map_mul, ← hD, ← deriv_algebraMap, map_zero]
    exact h
  by_contra hY
  have hY0 : Y ≠ 0 := fun h0 ↦ hY (by rw [h0, map_zero])
  have hg0 : g ≠ 0 := fun h0 ↦ by simp [h0] at hdeg
  have hlt : (derivative Y).degree < (g * Y).degree := by
    refine lt_of_lt_of_le (degree_derivative_lt hY0) ?_
    rw [degree_mul]
    exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hg0)
  have hne : derivative Y + g * Y ≠ 0 := by
    rw [add_comm]
    intro h0
    have := degree_add_eq_left_of_degree_lt hlt
    rw [h0, degree_zero] at this
    exact mul_ne_zero hg0 hY0 (degree_eq_bot.mp this.symm)
  exact hne hpoly

/-- Over `C(x)` with `d/dx`, every solution of `y′ + g y = f` with `g, f ∈ C[x]` is a
polynomial. This reduces the Risch differential equation over `C(x)` with polynomial coefficients
to a polynomial problem, which `CPoly.rdeSolve` decides. -/
theorem rde_polynomial_solution (hD : ∀ P : C'[X], P′ = derivative P) (g f : C'[X]) (y : K)
    (h : y′ + φ g * y = φ f) : ∃ Y : C'[X], y = φ Y ∧ derivative Y + g * Y = f := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  obtain ⟨Y, rfl⟩ : ∃ Y : C'[X], y = φ Y := by
    refine exists_polynomial_of_regularAt y fun p _ hp ↦ ?_
    refine mem_regularAt_of_rde hp.prime ?_ (not_dvd_natCast_polynomial hp.prime)
      (algebraMap_mem_regularAt _ g) (h ▸ algebraMap_mem_regularAt _ f)
    rw [hD]
    intro hdvd
    have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
    have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
    exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
  refine ⟨Y, rfl, hinj ?_⟩
  rw [map_add, map_mul, ← hD, ← deriv_algebraMap]
  exact h

/-- The polynomial equation `Y′ + g Y = 0` with `g ≠ 0` has only the zero solution. -/
theorem rde_poly_homogeneous (g Y : C'[X]) (hg : g ≠ 0) (h : derivative Y + g * Y = 0) :
    Y = 0 := by
  by_contra hY0
  have hlt : (derivative Y).degree < (g * Y).degree := by
    refine lt_of_lt_of_le (degree_derivative_lt hY0) ?_
    rw [degree_mul]
    exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hg)
  have := degree_add_eq_right_of_degree_lt hlt
  rw [h, degree_zero] at this
  exact mul_ne_zero hg hY0 (degree_eq_bot.mp this.symm)

/-- Over `C(x)`: `y′ + g y = 0` with `0 ≠ g ∈ C[x]` forces `y = 0`. -/
theorem rde_homogeneous' (hD : ∀ P : C'[X], P′ = derivative P) (g : C'[X]) (hg : g ≠ 0) (y : K)
    (h : y′ + φ g * y = 0) : y = 0 := by
  obtain ⟨Y, rfl, hY⟩ := rde_polynomial_solution hD g 0 y (by rw [map_zero]; exact h)
  rw [rde_poly_homogeneous g Y hg hY, map_zero]

/-- Over `C(x)`: if `b / s` has a genuine simple pole (`s` squarefree and non-constant, `b` coprime
to `s`), then `y′ + g y = b / s` has no solution `y ∈ C(x)` for any polynomial `g`. -/
theorem rde_no_solution_simple_pole (hD : ∀ P : C'[X], P′ = derivative P) (g b s : C'[X])
    (hs : Squarefree s) (hsdeg : 0 < s.natDegree) (hcop : IsCoprime b s) (y : K) :
    y′ + φ g * y ≠ φ b / φ s := by
  intro h
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hs0 : s ≠ 0 := hs.ne_zero
  -- an irreducible factor `p` of `s`
  have hsu : ¬IsUnit s := fun hu ↦ by
    have := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨p, hp, ⟨s₁, rfl⟩⟩ := WfDvdMonoid.exists_irreducible_factor hsu hs0
  have hps₁ : ¬p ∣ s₁ := fun ⟨q, hq⟩ ↦ hp.not_isUnit (hs p ⟨q, by rw [hq]; ring⟩)
  have hpb : ¬p ∣ b := fun hpb ↦
    hp.not_isUnit (hcop.isUnit_of_dvd' hpb (dvd_mul_right p s₁))
  have hφp : φ p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
  have hφs₁ : φ s₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr (right_ne_zero_of_mul hs0)
  have hnorm : ¬p ∣ p′ := by
    rw [hD]
    intro hdvd
    have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
    have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
    exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
  -- `y` is regular at `p`, hence so is `b / s`; but it is not
  have hy : y ∈ regularAt K p hp.prime :=
    mem_regularAt_of_rde' hp.prime hnorm (not_dvd_natCast_polynomial hp.prime)
      (algebraMap_mem_regularAt _ g) (by
        rw [h]
        exact ⟨b, s₁, hps₁, by rw [map_mul]; field_simp⟩)
  have hreg : φ b / φ (p * s₁) ∈ regularAt K p hp.prime := by
    rw [← h]
    exact add_mem (deriv_mem_regularAt _ hy) (mul_mem (algebraMap_mem_regularAt _ g) hy)
  obtain ⟨c, d, hd, hcd⟩ := hreg
  have h2 : φ (b * d) = φ (c * (p * s₁)) := by
    rw [map_mul, map_mul, ← hcd, map_mul]
    field_simp
  have h3 := hinj h2
  have : p ∣ b * d := ⟨c * s₁, by rw [h3]; ring⟩
  exact (hp.prime.dvd_or_dvd this).elim hpb hd

/-- **Denominator bound for the Risch differential equation over `C(x)`.** If
`y′ + g y = A / D` with `g, A, D ∈ C[x]`, and `G` contains `p ^ e` whenever `D` contains
`p ^ (e + 1)` (for instance `G = gcd (D, D′)`), then `y G` is a polynomial: a pole of order `k` of
`y` forces a pole of order `k + 1` of the right-hand side. -/
theorem rde_denominator (hD : ∀ P : C'[X], P′ = derivative P) (g A D G : C'[X]) (hD0 : D ≠ 0)
    (hG : ∀ p : C'[X], Irreducible p → ∀ e : ℕ, p ^ (e + 1) ∣ D → p ^ e ∣ G) (y : K)
    (h : y′ + φ g * y = φ A / φ D) : ∃ Y : C'[X], y * φ G = φ Y := by
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
      (algebraMap_mem_regularAt _ G)
  obtain ⟨k, hk1, rfl⟩ : ∃ k : ℕ, k ≠ 0 ∧ n = -(k : ℤ) := ⟨n.natAbs, by omega, by omega⟩
  have hy' : y = u / φ p ^ k := by rw [hy, zpow_neg, zpow_natCast]; field_simp
  -- `p ^ (k + 1) ∣ D`
  have hpk : p ^ (k + 1) ∣ D := by
    by_contra hnd
    have hnorm : ¬p ∣ p′ := by
      rw [hD]
      intro hdvd
      have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
      have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
      exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
    have hunit := isUnitAt_deriv_pole hp.prime hnorm hu k
      (not_dvd_natCast_polynomial hp.prime k hk1)
    rw [← hy'] at hunit
    -- `D = p ^ e * c` with `e ≤ k`
    have hfin : FiniteMultiplicity p D := FiniteMultiplicity.of_not_isUnit hp.not_isUnit hD0
    obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    set e := multiplicity p D with he
    have hek : e ≤ k := by
      by_contra hlt
      exact hnd ((pow_dvd_pow p (by omega : k + 1 ≤ e)).trans ⟨c, hc⟩)
    have hφc : φ c ≠ 0 := map_ne_zero_of_not_dvd hp.prime hpc
    obtain ⟨j, hj⟩ : ∃ j, k + 1 = e + (j + 1) := ⟨k - e, by omega⟩
    refine hunit.ne_mul hp.prime
      (f := φ p ^ j * (φ A / φ c) - φ g * u) ?_ ?_
    · exact sub_mem (mul_mem (pow_mem hpm j) ⟨A, c, hpc, by field_simp⟩)
        (mul_mem (algebraMap_mem_regularAt _ g) (hu.mem_regularAt hp.prime))
    · have hy'' : y′ = φ A / φ D - φ g * y := by rw [← h]; ring
      have hpow : φ p ^ (k + 1) = φ p ^ e * φ p ^ (j + 1) := by rw [hj, pow_add]
      have hpowk : φ p ^ (k + 1) = φ p ^ k * φ p := pow_succ _ _
      rw [hy'', sub_mul]
      have h1 : φ A / φ D * φ p ^ (k + 1) = φ p * (φ p ^ j * (φ A / φ c)) := by
        rw [hpow, hc, map_mul, map_pow, pow_succ]
        field_simp
      have h2 : φ g * y * φ p ^ (k + 1) = φ p * (φ g * u) := by
        rw [hpowk, hy']
        field_simp
      rw [h1, h2]
      ring
  obtain ⟨G₁, hG₁⟩ := hG p hp k hpk
  rw [hy', hG₁, map_mul, map_pow]
  have : u / φ p ^ k * (φ p ^ k * φ G₁) = u * φ G₁ := by field_simp
  rw [this]
  exact mul_mem (hu.mem_regularAt hp.prime) (algebraMap_mem_regularAt _ G₁)

end Base

end Differential
