import RischTragerBronstein.RDE.RationalCoeff
import RischTragerBronstein.RDE.HomogeneousPolyPart

/-!
# The Risch differential equation over `C(x)` with a coefficient having simple poles

`y′ + g y = A / D`, `g = Gn / Gd` in lowest terms. At a normal prime `p` where `g` has a pole of
order `m ≥ 2` or is regular, a pole of `y` of order `k` gives a pole of `y′ + g y` of order
`k + m` resp. `k + 1` (`RDE/RationalCoeff.lean`). At a **simple** pole of `g` (`Gd = p c₁`,
`p ∤ c₁`), cancellation can occur, exactly when `p ∣ Gn - k p′ c₁`, i.e. when the residue of `g` at
`p` is the integer `k` (Bronstein, §6.1: the *weak normalisation*).

The residue of `g` at a simple pole `p` is `r mod p` where `r Gd′ ≡ Gn (mod S)`, `S` the product of
the simple prime factors of `Gd`. Let `μ ≠ 0` be any polynomial with `S ∣ μ(r)` (an annihilating
polynomial of the residues). Then cancellation at `p` at order `k` forces `μ(k) = 0` and
`p ∣ r - k`; hence the denominator of `y` divides `D · E`, `E = ∏ₖ gcd(S, r - k)^k` over the natural
roots `k` of `μ`.

* `simple_pole_rde`: the local analysis at a simple pole;
* `rde_denominator_rational_W`: the denominator bound `y D E ∈ C[x]`;
* `rde_pivot_W`: the pivot of the polynomial equation can vanish only for
  `k ≤ deg D` or `k = deg D - lc Gn / lc Gd` (when `deg Gn + 1 = deg Gd`);
* `rde_homogeneous_W`: `y′ = c η y` (`c ∈ ℤ ∖ {0}`) has only the zero solution when `η` is not a
  logarithmic derivative of a radical, certified by: a repeated prime in `Gd`, or `deg Gn ≥ deg Gd`,
  or a simple prime `p ∣ S` at which the residue is no rational root of `μ`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Differential

section Local

variable {A K : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A] [Field K] [Algebra A K]
variable [IsFractionRing A K] [Differential A] [Differential K] [DifferentialAlgebra A K]
variable {p : A} (hp : Prime p)

local notation "φ" => algebraMap A K

omit [IsDomain A] [WfDvdMonoid A] [Differential A] [Differential K] [DifferentialAlgebra A K] in
include hp in
/-- An element of `A` lying in the maximal ideal `p O_p` is divisible by `p`. -/
lemma dvd_of_map_eq_mul_regular {a : A} {f : K} (hf : f ∈ regularAt K p hp)
    (h : φ a = φ p * f) : p ∣ a := by
  obtain ⟨m, b, hb, hfb⟩ := hf
  have : φ (a * b) = φ (p * m) := by rw [map_mul, map_mul, h, mul_assoc, hfb]
  have h2 := IsFractionRing.injective A K this
  exact (hp.dvd_or_dvd ⟨m, h2⟩).resolve_right hb

include hp in
/-- The derivative of `u p ^ n` (`n ∈ ℤ`), times `p`: `(u′ p + n u p′) p ^ n`. -/
lemma deriv_mul_zpow_mul (u : K) (n : ℤ) :
    (u * φ p ^ n)′ * φ p = (u′ * φ p + (n : K) * u * φ p′) * φ p ^ n := by
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [zpow_natCast, Derivation.leibniz, Derivation.leibniz_pow, deriv_algebraMap]
    simp only [smul_eq_mul, Int.cast_natCast]
    rcases m with _ | m
    · simp
    · rw [Nat.add_sub_cancel]; push_cast; ring
  · obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k ≠ 0 ∧ n = -(k : ℤ) := ⟨n.natAbs, by omega, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, Derivation.leibniz_div, Derivation.leibniz_pow,
      deriv_algebraMap, Nat.add_sub_cancel]
    simp only [smul_eq_mul]
    have : φ p ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
    field_simp
    push_cast
    ring

include hp in
/-- **Local analysis at a simple pole of the coefficient.** `g = Gn / (p c₁)` with `p ∤ Gn c₁`,
`y = u / p ^ k` (`k ≥ 1`, `u` a unit at `p`) and `(y′ + g y) p ^ e` regular at `p`: either
`k + 1 ≤ e` (no cancellation), or `p ∣ Gn - k p′ c₁`. -/
theorem simple_pole_rde (hnorm : ¬p ∣ p′) (hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : A))
    {Gn c₁ : A} (hGn : ¬p ∣ Gn) (hc₁ : ¬p ∣ c₁) {y u : K} {k e : ℕ} (hk : k ≠ 0)
    (hu : IsUnitAt K p u) (hy : y = u / φ p ^ k)
    (h : (y′ + φ Gn / φ (p * c₁) * y) * φ p ^ e ∈ regularAt K p hp)
    (hcancel : ¬p ∣ Gn - (k : A) * p′ * c₁) : k + 1 ≤ e := by
  by_contra hlt
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  have hc₁0 : φ c₁ ≠ 0 := map_ne_zero_of_not_dvd hp hc₁
  have hpm : φ p ∈ regularAt K p hp := algebraMap_mem_regularAt hp p
  -- `(y′ + g y) p ^ (k + 1) = p u′ + u (Gn - k p′ c₁) / c₁`
  have hform : (y′ + φ Gn / φ (p * c₁) * y) * φ p ^ (k + 1) =
      φ p * u′ + u * (φ (Gn - (k : A) * p′ * c₁) / φ c₁) := by
    have h1 := deriv_mul_zpow_mul hp u (-(k : ℤ))
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, ← hy] at h1
    have hpk : φ p ^ k ≠ 0 := pow_ne_zero _ hp0
    have e1 : (y′ + φ Gn / φ (p * c₁) * y) * φ p ^ (k + 1) =
        (y′ * φ p) * φ p ^ k + φ Gn / φ (p * c₁) * y * φ p ^ (k + 1) := by ring
    rw [e1, h1, hy]
    simp only [map_sub, map_mul, map_natCast, Int.cast_neg, Int.cast_natCast]
    field_simp
    ring
  have hw : IsUnitAt K p (u * (φ (Gn - (k : A) * p′ * c₁) / φ c₁)) :=
    hu.mul' hp ⟨Gn - (k : A) * p′ * c₁, c₁, hcancel, hc₁, by field_simp⟩
  obtain ⟨d, hd⟩ : ∃ d, k + 1 = e + d + 1 := ⟨k - e, by omega⟩
  have hu' : u′ ∈ regularAt K p hp := deriv_mem_regularAt hp (hu.mem_regularAt hp)
  refine hw.ne_mul hp (f := (y′ + φ Gn / φ (p * c₁) * y) * φ p ^ e * φ p ^ d - u′)
    (sub_mem (mul_mem h (pow_mem hpm d)) hu') ?_
  have := hform
  rw [hd, pow_add, pow_add, pow_one] at this
  linear_combination -this

end Local

section Base

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'[X]] [Field K] [Algebra C'[X] K]
variable [IsFractionRing C'[X] K] [Differential K] [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

omit [Differential C'[X]] [Field K] [Algebra C'[X] K] [IsFractionRing C'[X] K] [Differential K]
  [DifferentialAlgebra C'[X] K] in
/-- An irreducible polynomial divides a constant only if the constant is zero. -/
lemma eq_zero_of_irreducible_dvd_C {p : C'[X]} (hp : Irreducible p) {a : C'} (h : p ∣ C a) :
    a = 0 := by
  by_contra ha
  exact hp.not_isUnit (isUnit_of_dvd_unit h (isUnit_C.mpr (Ne.isUnit ha)))

omit [Differential C'[X]] [Field K] [Algebra C'[X] K] [IsFractionRing C'[X] K] [Differential K]
  [DifferentialAlgebra C'[X] K] in
/-- If `S ∣ μ(r)`, `p ∣ S` is irreducible and `p ∣ r - a`, then `μ(a) = 0`. -/
lemma eval_eq_zero_of_dvd_comp {p S r μ : C'[X]} (hp : Irreducible p) (hpS : p ∣ S)
    (hμ : S ∣ μ.comp r) {a : C'} (hpr : p ∣ r - C a) : μ.eval a = 0 := by
  have h1 : r - C a ∣ (μ.map C).eval r - (μ.map C).eval (C a) := sub_dvd_eval_sub r (C a) (μ.map C)
  rw [eval_map, eval_map] at h1
  change r - C a ∣ μ.comp r - μ.comp (C a) at h1
  rw [comp_C] at h1
  have h2 : p ∣ C (μ.eval a) := by
    have : C (μ.eval a) = μ.comp r - (μ.comp r - C (μ.eval a)) := by ring
    rw [this]
    exact dvd_sub (hpS.trans hμ) (hpr.trans h1)
  exact eq_zero_of_irreducible_dvd_C hp h2

omit [Differential C'[X]] [Field K] [Algebra C'[X] K] [IsFractionRing C'[X] K] [Differential K]
  [DifferentialAlgebra C'[X] K] in
lemma not_dvd_derivative_self {p : C'[X]} (hp : Irreducible p) : ¬p ∣ derivative p := by
  intro hdvd
  have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
  have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
  exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))

/-- **Denominator bound with weak normalisation.** `y′ + (Gn / Gd) y = A / D` forces `y D E` to be
a polynomial, where `S` contains the simple primes of `Gd`, `r Gd′ ≡ Gn (mod S)`, `S ∣ μ(r)`, and
`E` is divisible by `p ^ k` for every natural root `k` of `μ` and prime `p ∣ S` with `p ∣ r - k`. -/
theorem rde_denominator_rational_W (hD : ∀ P : C'[X], P′ = derivative P)
    (Gn Gd A D S r μ E : C'[X]) (hD0 : D ≠ 0) (hGd0 : Gd ≠ 0) (hcop : IsCoprime Gn Gd)
    (hS : ∀ p : C'[X], Irreducible p → p ∣ Gd → ¬p ∣ derivative Gd → p ∣ S)
    (hr : S ∣ r * derivative Gd - Gn) (hμ : S ∣ μ.comp r)
    (hE : ∀ k : ℕ, k ≠ 0 → μ.eval (k : C') = 0 → ∀ p : C'[X], Irreducible p → p ∣ S →
      p ∣ r - C (k : C') → p ^ k ∣ E)
    (y : K) (h : y′ + φ Gn / φ Gd * y = φ A / φ D) : ∃ Y : C'[X], y * φ (D * E) = φ Y := by
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
      (algebraMap_mem_regularAt _ _)
  obtain ⟨k, hk1, rfl⟩ : ∃ k : ℕ, k ≠ 0 ∧ n = -(k : ℤ) := ⟨n.natAbs, by omega, by omega⟩
  have hy' : y = u / φ p ^ k := by rw [hy, zpow_neg, zpow_natCast]; field_simp
  have hnorm : ¬p ∣ p′ := by rw [hD]; exact not_dvd_derivative_self hp
  have hnat := not_dvd_natCast_polynomial hp.prime
  have hfin : FiniteMultiplicity p D := FiniteMultiplicity.of_not_isUnit hp.not_isUnit hD0
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  set e := multiplicity p D with he
  have hφc : φ c ≠ 0 := map_ne_zero_of_not_dvd hp.prime hpc
  have hrhs : (y′ + φ Gn / φ Gd * y) * φ p ^ e ∈ regularAt K p hp.prime := by
    rw [h]
    refine ⟨A, c, hpc, ?_⟩
    rw [hc, map_mul, map_pow]
    field_simp
  suffices hdvd : p ^ k ∣ D * E by
    obtain ⟨M, hM⟩ := hdvd
    rw [hy', hM, map_mul, map_pow]
    have : u / φ p ^ k * (φ p ^ k * φ M) = u * φ M := by field_simp
    rw [this]
    exact mul_mem (hu.mem_regularAt hp.prime) (algebraMap_mem_regularAt _ M)
  by_cases hke : k ≤ e
  · exact (pow_dvd_pow p hke).trans (dvd_mul_of_dvd_left ⟨c, hc⟩ _)
  push Not at hke
  by_cases hpG : p ∣ Gd
  · have hfinG : FiniteMultiplicity p Gd :=
      FiniteMultiplicity.of_not_isUnit hp.not_isUnit hGd0
    obtain ⟨c₁, hc₁, hpc₁⟩ := hfinG.exists_eq_pow_mul_and_not_dvd
    set m := multiplicity p Gd with hm
    have hpGn : ¬p ∣ Gn := fun hdvd ↦ hp.not_isUnit (hcop.isUnit_of_dvd' hdvd hpG)
    have hm1 : 1 ≤ m := hfinG.le_multiplicity_of_pow_dvd (by rwa [pow_one])
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · -- a simple pole: cancellation
      have hm1' : m = 1 := by omega
      rw [hm1', pow_one] at hc₁
      have hstep := simple_pole_rde hp.prime hnorm hnat hpGn hpc₁ hk1 hu hy'
        (by rw [← hc₁]; exact hrhs)
      have hcancel : p ∣ Gn - (k : C'[X]) * p′ * c₁ := by
        by_contra hnc
        have := hstep hnc
        omega
      have hGd' : p ∣ Gn - C (k : C') * derivative Gd := by
        rw [hc₁, derivative_mul]
        have : Gn - C (k : C') * (derivative p * c₁ + p * derivative c₁) =
            (Gn - (k : C'[X]) * p′ * c₁) - p * (C (k : C') * derivative c₁) := by
          rw [hD, C_eq_natCast]; ring
        rw [this]
        exact dvd_sub hcancel (dvd_mul_right p _)
      have hpGd' : ¬p ∣ derivative Gd := fun hd ↦ hpGn (by
        have := dvd_add hGd' (dvd_mul_of_dvd_right hd (C (k : C')))
        simpa using this)
      have hpS : p ∣ S := hS p hp hpG hpGd'
      have hpr : p ∣ r - C (k : C') := by
        have h1 : p ∣ (r - C (k : C')) * derivative Gd := by
          have : (r - C (k : C')) * derivative Gd =
              (r * derivative Gd - Gn) + (Gn - C (k : C') * derivative Gd) := by ring
          rw [this]
          exact dvd_add (hpS.trans hr) hGd'
        exact (hp.prime.dvd_or_dvd h1).resolve_right hpGd'
      have hev := eval_eq_zero_of_dvd_comp hp hpS hμ hpr
      exact dvd_mul_of_dvd_right (hE k hk1 hev p hp hpS hpr) D
    · -- a pole of order `m ≥ 2`: no cancellation
      have hφc₁ : φ c₁ ≠ 0 := map_ne_zero_of_not_dvd hp.prime hpc₁
      have hw : IsUnitAt K p (φ Gn / φ c₁) := ⟨Gn, c₁, hpGn, hpc₁, by field_simp⟩
      have := pole_order_le_of_rde hp.prime hnorm hnat hm2 hk1 hw
        (by rw [hc₁, map_mul, map_pow]; field_simp) hu hy' hrhs
      omega
  · -- the coefficient is regular at `p`
    exfalso
    have hGreg : φ Gn / φ Gd ∈ regularAt K p hp.prime :=
      ⟨Gn, Gd, hpG, by
        have : φ Gd ≠ 0 := (map_ne_zero_iff _ hinj).mpr hGd0
        field_simp⟩
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

/-- **The homogeneous equation `y′ = c η y`** (`c ∈ ℤ ∖ {0}`) has only the zero solution when
`η = Gn / Gd` is not the logarithmic derivative of a radical, certified by one of: a repeated prime
factor of `Gd`; `deg Gn ≥ deg Gd`; a simple prime `p ∣ S` at which the residue is no rational root
of `μ`. -/
theorem rde_homogeneous_W (hD : ∀ P : C'[X], P′ = derivative P) (Gn Gd S r μ : C'[X])
    (hGn0 : Gn ≠ 0) (hGd0 : Gd ≠ 0) (hcop : IsCoprime Gn Gd) (hSd : S ∣ Gd)
    (hScop : ∀ p : C'[X], Irreducible p → p ∣ S → ¬p ∣ derivative Gd)
    (hr : S ∣ r * derivative Gd - Gn) (hμ : S ∣ μ.comp r)
    (hcert : (∃ p : C'[X], Irreducible p ∧ p ^ 2 ∣ Gd) ∨ Gd.natDegree ≤ Gn.natDegree ∨
      ∃ p : C'[X], Irreducible p ∧ p ∣ S ∧ ∀ q : ℚ, μ.eval (q : C') = 0 → ¬p ∣ r - C (q : C'))
    (c : ℤ) (hc : c ≠ 0) (y : K) (h : y′ = φ (C (c : C')) * (φ Gn / φ Gd) * y) : y = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hφGd : φ Gd ≠ 0 := (map_ne_zero_iff _ hinj).mpr hGd0
  have hc' : (c : C') ≠ 0 := Int.cast_ne_zero.mpr hc
  have hCc : IsUnit (C (c : C')) := isUnit_C.mpr hc'.isUnit
  by_contra hy0
  -- the local identity at a prime `p` dividing `Gd`: `p u′/u + n p′ = c p Gn / Gd`
  have hlocal : ∀ p : C'[X], Irreducible p → ∃ (u : K) (n : ℤ), IsUnitAt K p u ∧
      φ p * (u′ / u) + (n : K) * φ (derivative p) = φ (C (c : C')) * (φ Gn / φ Gd) * φ p := by
    intro p hp
    obtain ⟨n, u, hu, hy₀⟩ := exists_zpow_mul_isUnitAt hp.prime hy0
    have hy : y = u * φ p ^ n := by rw [hy₀, mul_comm]
    refine ⟨u, n, hu, ?_⟩
    have h1 := deriv_mul_zpow_mul hp.prime u n
    rw [← hy, h, hy, hD] at h1
    have hu0 : u ≠ 0 := fun h0 ↦ hy0 (by rw [hy, h0, zero_mul])
    have hp0 : φ p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
    have hpn : φ p ^ n ≠ 0 := zpow_ne_zero _ hp0
    have := mul_right_cancel₀ hpn (by rw [← h1]; ring :
      φ (C (c : C')) * (φ Gn / φ Gd) * φ p * u * φ p ^ n =
        (u′ * φ p + (n : K) * u * φ (derivative p)) * φ p ^ n)
    apply mul_right_cancel₀ hu0
    rw [this, add_mul, mul_assoc, div_mul_cancel₀ _ hu0]
    ring
  rcases hcert with ⟨p, hp, hp2⟩ | hdeg | ⟨p, hp, hpS, hres⟩
  · -- a pole of order `≥ 2`
    obtain ⟨u, n, hu, hloc⟩ := hlocal p hp
    obtain ⟨w, hw⟩ := hp2
    have hpGn : ¬p ∣ Gn := fun hdvd ↦
      hp.not_isUnit (hcop.isUnit_of_dvd' hdvd (hw ▸ (dvd_pow_self p two_ne_zero).trans ⟨w, rfl⟩))
    have hp0 : φ p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
    have hw0 : φ w ≠ 0 := fun h0 ↦ hφGd (by rw [hw, map_mul, h0, mul_zero])
    have hu0 : u ≠ 0 := fun h0 ↦ by
      obtain ⟨a, b, ha, hb, hab⟩ := hu
      rw [h0, zero_mul] at hab
      exact map_ne_zero_of_not_dvd hp.prime ha hab.symm
    have hreg : u′ / u ∈ regularAt K p hp.prime := by
      rw [div_eq_mul_inv]
      exact mul_mem (deriv_mem_regularAt hp.prime (hu.mem_regularAt hp.prime))
        (hu.inv_mem_regularAt hp.prime)
    have hkey : φ (C (c : C') * Gn) = φ p * (φ w * (φ p * (u′ / u) + (n : K) * φ (derivative p))) := by
      rw [hloc, hw]
      simp only [map_mul, map_pow]
      field_simp
    have := dvd_of_map_eq_mul_regular hp.prime
      (mul_mem (algebraMap_mem_regularAt _ w)
        (add_mem (mul_mem (algebraMap_mem_regularAt _ p) hreg)
          (mul_mem (by
            rw [show (n : K) = φ (n : C'[X]) by simp]
            exact algebraMap_mem_regularAt _ _) (algebraMap_mem_regularAt _ _)))) hkey
    rcases hp.prime.dvd_or_dvd this with h1 | h1
    · exact hp.not_isUnit (isUnit_of_dvd_unit h1 hCc)
    · exact hpGn h1
  · -- `deg Gn ≥ deg Gd`: the polynomial part of `c η` is nonzero
    have hdm := EuclideanDomain.div_add_mod Gn Gd
    have hlt := degree_mod_lt Gn hGd0
    have hQ0 : Gn / Gd ≠ 0 := by
      intro h0
      rw [h0, mul_zero, zero_add] at hdm
      rw [← hdm] at hdeg
      rcases eq_or_ne (Gn % Gd) 0 with h1 | h1
      · exact hGn0 (by rw [← hdm, h1])
      · exact absurd (natDegree_lt_natDegree h1 hlt) (not_lt.mpr hdeg)
    refine no_rde_homogeneous_of_polyPart hD (-(C (c : C') * (Gn / Gd))) (-(C (c : C') * (Gn % Gd)))
      Gd (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr hc') hQ0)) hGd0 ?_ y hy0 ?_
    · rcases eq_or_ne (Gn % Gd) 0 with h1 | h1
      · right; rw [h1, mul_zero, neg_zero]
      · left
        rw [natDegree_neg, natDegree_C_mul hc']
        exact natDegree_lt_natDegree h1 hlt
    · rw [h]
      have : φ (-(C (c : C') * (Gn / Gd))) + φ (-(C (c : C') * (Gn % Gd))) / φ Gd =
          -(φ (C (c : C')) * (φ Gn / φ Gd)) := by
        conv_rhs => rw [← hdm]
        simp only [map_neg, map_mul, map_add]
        field_simp
        ring
      rw [this]
      ring
  · -- a simple pole with a non-rational residue
    obtain ⟨u, n, hu, hloc⟩ := hlocal p hp
    have hpGd' := hScop p hp hpS
    obtain ⟨c₁, hc₁⟩ := hpS.trans hSd
    have hpc₁ : ¬p ∣ c₁ := fun hd ↦ hpGd' (by
      rw [hc₁, derivative_mul]
      exact dvd_add (dvd_mul_of_dvd_right hd _) (dvd_mul_right p _))
    have hpGn : ¬p ∣ Gn := fun hdvd ↦
      hp.not_isUnit (hcop.isUnit_of_dvd' hdvd (hc₁ ▸ dvd_mul_right p c₁))
    have hp0 : φ p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
    have hc₁0 : φ c₁ ≠ 0 := map_ne_zero_of_not_dvd hp.prime hpc₁
    have hu0 : u ≠ 0 := fun h0 ↦ by
      obtain ⟨a, b, ha, hb, hab⟩ := hu
      rw [h0, zero_mul] at hab
      exact map_ne_zero_of_not_dvd hp.prime ha hab.symm
    have hreg : u′ / u ∈ regularAt K p hp.prime := by
      rw [div_eq_mul_inv]
      exact mul_mem (deriv_mem_regularAt hp.prime (hu.mem_regularAt hp.prime))
        (hu.inv_mem_regularAt hp.prime)
    -- `p ∣ c Gn - n p′ c₁`
    have hkey : φ (C (c : C') * Gn - (n : C'[X]) * derivative p * c₁) = φ p * (φ c₁ * (u′ / u)) := by
      have := hloc
      rw [hc₁, map_mul] at this
      have hCc' : φ (C (c : C')) = (c : K) := by rw [C_eq_intCast, map_intCast]
      rw [hCc'] at this
      simp only [map_sub, map_mul, map_intCast]
      field_simp
      field_simp at this
      linear_combination -this
    have h1 := dvd_of_map_eq_mul_regular hp.prime (mul_mem (algebraMap_mem_regularAt _ c₁) hreg) hkey
    -- hence `p ∣ c Gn - n Gd′`
    have h2 : p ∣ C (c : C') * Gn - (n : C'[X]) * derivative Gd := by
      rw [hc₁, derivative_mul]
      have : C (c : C') * Gn - (n : C'[X]) * (derivative p * c₁ + p * derivative c₁) =
          (C (c : C') * Gn - (n : C'[X]) * derivative p * c₁) - p * ((n : C'[X]) * derivative c₁) := by
        ring
      rw [this]
      exact dvd_sub h1 (dvd_mul_right p _)
    -- and `p ∣ (c r - n) Gd′`, so `p ∣ c r - n`
    have h3 : p ∣ (C (c : C') * r - (n : C'[X])) * derivative Gd := by
      have : (C (c : C') * r - (n : C'[X])) * derivative Gd =
          C (c : C') * (r * derivative Gd - Gn) + (C (c : C') * Gn - (n : C'[X]) * derivative Gd) := by
        ring
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_right (hpS.trans hr) _) h2
    have h4 : p ∣ C (c : C') * r - (n : C'[X]) := (hp.prime.dvd_or_dvd h3).resolve_right hpGd'
    have h5 : p ∣ r - C (((n : ℚ) / c : ℚ) : C') := by
      have : C (c : C') * r - (n : C'[X]) = C (c : C') * (r - C (((n : ℚ) / c : ℚ) : C')) := by
        rw [mul_sub, ← C_mul, show (c : C') * (((n : ℚ) / c : ℚ) : C') = (n : C') by
          push_cast; field_simp]
        simp only [C_eq_intCast]
      rw [this] at h4
      exact (hp.prime.dvd_or_dvd h4).resolve_left fun hd ↦ hp.not_isUnit (isUnit_of_dvd_unit hd hCc)
    exact hres _ (eval_eq_zero_of_dvd_comp hp hpS hμ h5) h5

omit [Differential C'[X]] [Field K] [Algebra C'[X] K] [IsFractionRing C'[X] K] [Differential K]
  [DifferentialAlgebra C'[X] K] in
/-- **Pivot analysis without the condition at infinity.** For `P₁ = Gd D`, `P₀ = Gn D - Gd D′ ≠ 0`,
the pivot `k lc₁ + lc₀` (at `dg = max (deg P₁ - 1) (deg P₀)`) can vanish only for `k ≤ deg D`, or,
when `deg Gn + 1 = deg Gd`, for `k = deg D - lc Gn / lc Gd`. -/
theorem rde_pivot_W (Gn Gd D : C'[X]) (hGn0 : Gn ≠ 0) (hGd0 : Gd ≠ 0) (hD0 : D ≠ 0)
    (hP₀ : Gn * D - Gd * derivative D ≠ 0) (k : ℕ)
    (hk : (k : C') * (Gd * D).coeff (max ((Gd * D).natDegree - 1)
          (Gn * D - Gd * derivative D).natDegree + 1) +
        (Gn * D - Gd * derivative D).coeff (max ((Gd * D).natDegree - 1)
          (Gn * D - Gd * derivative D).natDegree) = 0) :
    k ≤ D.natDegree ∨ (Gn.natDegree + 1 = Gd.natDegree ∧
      (k : C') = D.natDegree - Gn.leadingCoeff / Gd.leadingCoeff) := by
  by_cases hdeg : Gn.natDegree + 1 ≠ Gd.natDegree
  · exact Or.inl ((rde_pivot Gn Gd D hGn0 hGd0 hD0 hdeg).2 k hk)
  push Not at hdeg
  right
  refine ⟨hdeg, ?_⟩
  have hn₁ : (Gd * D).natDegree = Gd.natDegree + D.natDegree := natDegree_mul hGd0 hD0
  have hnD : (Gn * D).natDegree = Gn.natDegree + D.natDegree := natDegree_mul hGn0 hD0
  obtain ⟨n₁, hn₁def⟩ : ∃ n, n = Gd.natDegree + D.natDegree := ⟨_, rfl⟩
  have hn₁pos : 1 ≤ n₁ := by omega
  have hGD' : (Gd * derivative D).natDegree ≤ n₁ - 1 := by
    rcases Nat.eq_zero_or_pos D.natDegree with hd0 | hdpos
    · rw [eq_C_of_natDegree_eq_zero hd0, derivative_C, mul_zero, natDegree_zero]
      exact Nat.zero_le _
    · exact natDegree_mul_le.trans (by have := natDegree_derivative_le D; omega)
  have hP₀deg : (Gn * D - Gd * derivative D).natDegree ≤ n₁ - 1 :=
    (natDegree_sub_le _ _).trans (max_le (by rw [hnD]; omega) hGD')
  -- the coefficient of `P₀` at `n₁ - 1`
  have hcoeff : (Gn * D - Gd * derivative D).coeff (n₁ - 1) =
      Gn.leadingCoeff * D.leadingCoeff - (D.natDegree : C') * (Gd.leadingCoeff * D.leadingCoeff) := by
    rw [coeff_sub]
    have hGnD : (Gn * D).coeff (n₁ - 1) = Gn.leadingCoeff * D.leadingCoeff := by
      have : n₁ - 1 = (Gn * D).natDegree := by rw [hnD]; omega
      rw [this, coeff_natDegree, leadingCoeff_mul]
    rw [hGnD]
    rcases Nat.eq_zero_or_pos D.natDegree with hd0 | hdpos
    · rw [eq_C_of_natDegree_eq_zero hd0, derivative_C, mul_zero, coeff_zero]
      simp
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
  have hGd' : Gd.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGd0
  rw [hn₁, ← hn₁def, max_eq_left hP₀deg, show n₁ - 1 + 1 = n₁ by omega, hcoeff] at hk
  have hlc : (Gd * D).coeff n₁ = Gd.leadingCoeff * D.leadingCoeff := by
    rw [hn₁def, ← hn₁, coeff_natDegree, leadingCoeff_mul]
  rw [hlc] at hk
  have : ((k : C') - (D.natDegree - Gn.leadingCoeff / Gd.leadingCoeff)) *
      (Gd.leadingCoeff * D.leadingCoeff) = 0 := by
    field_simp
    linear_combination hk
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hL)

end Base

end Differential
