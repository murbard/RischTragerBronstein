import RischTragerBronstein.RDE.NestedBounds
import RischTragerBronstein.Liouville.ExponentialPoly

/-!
# The special bound for `y′ + h′ y = g` in an exponential extension

`K = F(t)`, `t′ = b t`. The order of `y` at `t = 0` is bounded by that of `g`:

* `rde_special_bound_pole`: if `h` has a pole at `t`, `y` has at most the pole order of `g`
  (`h′` has a pole of the same order as `h`, since `e′ = l b e` has no non-zero solution);
* `rde_special_bound_reg`: if `h ≡ h₀ (mod t)`, `y` has pole order at most `ε'` provided no
  `e′ + (h₀′ - k b) e = 0` (`k > ε'`) has a non-zero solution — the cancellation case, decided in
  towers by the structure theorem.

Values at `t = 0` are handled through congruences `z = z₀ + t r` with `r` regular at `t`.
-/

open Polynomial

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K
local notation "RX" => regularAt K (X : F[X]) prime_X

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
/-- An element regular at `t` is congruent to its value at `0`. -/
lemma exists_val_of_mem_regularAt {z : K} (hz : z ∈ RX) :
    ∃ (z0 : F) (r : K), r ∈ RX ∧ z = φ (C z0) + φ X * r := by
  obtain ⟨a, d, hd, h⟩ := hz
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hd0 : d.coeff 0 ≠ 0 := fun h0 ↦ hd (X_dvd_iff.mpr h0)
  have hφd : φ d ≠ 0 := map_ne_zero_of_not_dvd prime_X hd
  set z0 := a.coeff 0 / d.coeff 0 with hz0
  obtain ⟨q, hq⟩ : X ∣ a - C z0 * d := by
    rw [X_dvd_iff, coeff_sub, coeff_C_mul, hz0]
    field_simp
    ring
  refine ⟨z0, φ q / φ d, ⟨q, d, hd, by field_simp⟩, ?_⟩
  have hz : z = φ a / φ d := by rw [← h]; field_simp
  rw [hz]
  have : φ a = φ (C z0) * φ d + φ X * φ q := by
    rw [← map_mul, ← map_mul, ← map_add, ← hq]; ring
  rw [this]
  field_simp

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
/-- An element congruent to a non-zero constant modulo `t` is a unit at `t`. -/
lemma isUnitAt_of_val {z : K} {z0 : F} {r : K} (hr : r ∈ RX) (hz : z = φ (C z0) + φ X * r)
    (hz0 : z0 ≠ 0) : IsUnitAt K (X : F[X]) z := by
  obtain ⟨a, d, hd, h⟩ := hr
  have hφd : φ d ≠ 0 := map_ne_zero_of_not_dvd prime_X hd
  refine ⟨C z0 * d + X * a, d, fun hdvd ↦ ?_, hd, ?_⟩
  · have h1 : X ∣ C z0 * d := (dvd_add_left (dvd_mul_right X a)).mp hdvd
    rcases (prime_X (R := F)).dvd_or_dvd h1 with h2 | h2
    · exact hz0 (by simpa [X_dvd_iff] using h2)
    · exact hd h2
  · rw [hz, map_add, map_mul, map_mul, ← h]
    ring

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
/-- The value at `0` of a unit at `t` is non-zero. -/
lemma val_ne_zero_of_isUnitAt {z : K} {z0 : F} {r : K} (hr : r ∈ RX)
    (hz : z = φ (C z0) + φ X * r) (hu : IsUnitAt K (X : F[X]) z) : z0 ≠ 0 := by
  rintro rfl
  exact hu.ne_mul prime_X hr (by rw [hz, map_zero, map_zero, zero_add])

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
lemma mem_X_pow_regular_or {y : K} (hy : y ≠ 0) (ε : ℕ) :
    y * φ (X ^ ε) ∈ RX ∨ ∃ (k : ℕ) (u : K), ε < k ∧ IsUnitAt K (X : F[X]) u ∧ y = u / φ (X ^ k) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hX0 : φ (X : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  obtain ⟨n, u, hu, rfl⟩ := exists_zpow_mul_isUnitAt (K := K) (prime_X (R := F)) hy
  by_cases hn : -(ε : ℤ) ≤ n
  · left
    obtain ⟨j, hj⟩ : ∃ j : ℕ, n + ε = j := ⟨(n + ε).toNat, by omega⟩
    have : φ X ^ n * u * φ (X ^ ε) = φ X ^ j * u := by
      rw [map_pow, ← zpow_natCast, ← zpow_natCast, ← hj, zpow_add₀ hX0]; ring
    rw [this]
    exact mul_mem (pow_mem (algebraMap_mem_regularAt _ _) _) (hu.mem_regularAt _)
  · right
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    refine ⟨k, u, by omega, hu, ?_⟩
    rw [hk, zpow_neg, zpow_natCast, map_pow]
    field_simp

variable {b : F} (hDe : ∀ P : F[X], P′ = implicitDeriv (C b * X) P)
include hDe

lemma deriv_phi_X_pow (k : ℕ) : (φ (X ^ k))′ = φ (C ((k : F) * b)) * φ (X ^ k) := by
  rw [deriv_algebraMap, hDe, deriv_X_pow, map_mul]

/-- Congruences modulo `t` are preserved by the derivation. -/
lemma deriv_val {z : K} {z0 : F} {r : K} (hr : r ∈ RX) (hz : z = φ (C z0) + φ X * r) :
    ∃ r' : K, r' ∈ RX ∧ z′ = φ (C z0′) + φ X * r' := by
  refine ⟨φ (C b) * r + r′, add_mem (mul_mem (algebraMap_mem_regularAt _ _) hr)
    (deriv_mem_regularAt _ hr), ?_⟩
  rw [hz, map_add, Derivation.leibniz, deriv_algebraMap, deriv_algebraMap, hDe, hDe,
    implicitDeriv_C, implicitDeriv_X]
  simp only [smul_eq_mul, map_mul]
  ring

/-- `(u / tᵏ)′ tᵏ = u′ - k b u`. -/
lemma deriv_div_X_pow (u : K) (k : ℕ) :
    (u / φ (X ^ k))′ * φ (X ^ k) = u′ - φ (C ((k : F) * b)) * u := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have h0 : φ (X ^ k : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  rw [Derivation.leibniz_div, deriv_phi_X_pow hDe]
  simp only [smul_eq_mul]
  field_simp

/-- **The special bound, `h` regular at `t`.** -/
theorem rde_special_bound_reg (h y g : K) (ε ε' : ℕ) (hεε : ε ≤ ε')
    (hg : g * φ (X ^ ε) ∈ RX) (h0 : F) (rh : K) (hrh : rh ∈ RX) (hh : h = φ (C h0) + φ X * rh)
    (hno : ∀ k : ℕ, ε' < k → ∀ e : F, e ≠ 0 → e′ + (h0′ - k * b) * e ≠ 0)
    (hrde : y′ + h′ * y = g) : y * φ (X ^ ε') ∈ RX := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  by_cases hy0 : y = 0
  · rw [hy0, zero_mul]; exact zero_mem _
  rcases mem_X_pow_regular_or (F := F) (K := K) hy0 ε' with hreg | ⟨k, u, hk, hu, rfl⟩
  · exact hreg
  exfalso
  obtain ⟨u0, ru, hru, hu'⟩ := exists_val_of_mem_regularAt (hu.mem_regularAt prime_X)
  have hu0 := val_ne_zero_of_isUnitAt hru hu' hu
  obtain ⟨r1, hr1, hu1⟩ := deriv_val hDe hru hu'
  obtain ⟨r2, hr2, hh1⟩ := deriv_val hDe hrh hh
  -- `g tᵏ = u′ - k b u + h′ u ≡ u₀′ + (h₀′ - k b) u₀`
  have hgk : g * φ (X ^ k) = φ (C (u0′ + (h0′ - k * b) * u0)) +
      φ X * (r1 - φ (C ((k : F) * b)) * ru + φ (C h0′) * ru + r2 * u) := by
    rw [← hrde, add_mul, deriv_div_X_pow hDe]
    have hX0 : φ (X ^ k : F[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
    have e1 : h′ * (u / φ (X ^ k)) * φ (X ^ k) = h′ * u := by field_simp
    rw [e1, hu1, hh1, hu']
    simp only [map_add, map_mul, map_sub, C_add, C_mul, C_sub]
    ring
  have hunit := isUnitAt_of_val (add_mem (add_mem (sub_mem hr1 (mul_mem
    (algebraMap_mem_regularAt _ _) hru)) (mul_mem (algebraMap_mem_regularAt _ _) hru))
    (mul_mem hr2 (hu.mem_regularAt prime_X))) hgk (hno k hk u0 hu0)
  obtain ⟨j, rfl⟩ : ∃ j, k = ε + 1 + j := ⟨k - (ε + 1), by omega⟩
  refine hunit.ne_mul prime_X (f := g * φ (X ^ ε) * φ (X ^ j))
    (mul_mem hg (algebraMap_mem_regularAt _ _)) ?_
  simp only [map_pow]
  ring

/-- **The special bound, `h` with a pole at `t`.** -/
theorem rde_special_bound_pole (hhom : ∀ l : ℕ, l ≠ 0 → ∀ e : F, e ≠ 0 → e′ ≠ l * b * e)
    (h y g : K) (ε : ℕ) (hg : g * φ (X ^ ε) ∈ RX) (hh : h ∉ RX)
    (hrde : y′ + h′ * y = g) : y * φ (X ^ ε) ∈ RX := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  by_cases hy0 : y = 0
  · rw [hy0, zero_mul]; exact zero_mem _
  rcases mem_X_pow_regular_or (F := F) (K := K) hy0 ε with hreg | ⟨k, u, hk, hu, rfl⟩
  · exact hreg
  exfalso
  have hh0 : h ≠ 0 := fun h0 ↦ hh (h0 ▸ zero_mem _)
  rcases mem_X_pow_regular_or (F := F) (K := K) hh0 0 with hreg | ⟨l, v, hl, hv, rfl⟩
  · exact hh (by simpa using hreg)
  obtain ⟨v0, rv, hrv, hv'⟩ := exists_val_of_mem_regularAt (hv.mem_regularAt prime_X)
  have hv0 := val_ne_zero_of_isUnitAt hrv hv' hv
  obtain ⟨r1, hr1, hv1⟩ := deriv_val hDe hrv hv'
  -- `(v / tˡ)′ tˡ = v′ - l b v ≡ v₀′ - l b v₀ ≠ 0`
  have hV : (v / φ (X ^ l))′ * φ (X ^ l) = φ (C (v0′ - l * b * v0)) +
      φ X * (r1 - φ (C ((l : F) * b)) * rv) := by
    rw [deriv_div_X_pow hDe, hv1, hv']
    simp only [map_add, map_mul, map_sub, C_add, C_mul, C_sub]
    ring
  have hVu := isUnitAt_of_val (sub_mem hr1 (mul_mem (algebraMap_mem_regularAt _ _) hrv)) hV
    (sub_ne_zero.mpr (hhom l (by omega) v0 hv0))
  have hX0 : ∀ n, φ (X ^ n : F[X]) ≠ 0 := fun n ↦
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  -- `g t^(k+l) = (u′ - k b u) tˡ + V u`
  have hgk : g * φ (X ^ k) * φ (X ^ l) =
      ((u / φ (X ^ k))′ * φ (X ^ k)) * φ (X ^ l) + ((v / φ (X ^ l))′ * φ (X ^ l)) * u := by
    rw [← hrde]
    field_simp
  obtain ⟨j, rfl⟩ : ∃ j, k = ε + 1 + j := ⟨k - (ε + 1), by omega⟩
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  refine (hVu.mul' prime_X hu).ne_mul prime_X (f := g * φ (X ^ ε) * φ (X ^ j) * φ (X ^ (l' + 1)) -
    ((u / φ (X ^ (ε + 1 + j)))′ * φ (X ^ (ε + 1 + j))) * φ (X ^ l'))
    (sub_mem (mul_mem (mul_mem hg (algebraMap_mem_regularAt _ _)) (algebraMap_mem_regularAt _ _))
      (mul_mem (by rw [deriv_div_X_pow hDe]; exact sub_mem (deriv_mem_regularAt _
        (hu.mem_regularAt _)) (mul_mem (algebraMap_mem_regularAt _ _) (hu.mem_regularAt _)))
        (algebraMap_mem_regularAt _ _))) ?_
  simp only [map_pow] at hgk ⊢
  linear_combination -hgk
