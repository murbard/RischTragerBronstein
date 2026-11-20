import RischTragerBronstein.Computable.SysDenT
import RischTragerBronstein.Computable.SysDegTV
import RischTragerBronstein.Computable.SysDenAnn

/-!
# Coupled Risch systems: the place `t = 0` with a gauge-triangular non-constant limit

At an exponential level `t′ = b t`, if `A₀(0) = q(0) M₀` and a gauge transformation
`C ∈ GL_n(K)` (with derivative) makes `T = C M₀ C⁻¹ − C′ C⁻¹` upper triangular with diagonal
`pᵢ b + qᵢ cᵢ′/cᵢ`, `pᵢ` not a positive integer, then a solution has no pole at `t = 0` beyond the
right-hand side (`sys_den_zero_gauge`): the leading coefficient `y` of a pole of order `e`
satisfies `y′ − e b y + M₀ y = 0`, so `w = C y` satisfies `w′ − e b w + T w = 0`, and the last
non-zero component gives `wᵢ′ + ((pᵢ − e) b + qᵢ cᵢ′/cᵢ) wᵢ = 0`, impossible
(`hom_ratlog`). This is the case of non-constant curves over an exponential.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K] {n : ℕ}

open Matrix in
/-- **The special place `t = 0` with a gauge-triangular limit.** -/
theorem sys_den_zero_gauge (b : K) (q : K[X]) (hq0 : q.coeff 0 ≠ 0)
    (A0 : Matrix (Fin n) (Fin n) K[X]) (M0 : Fin n → Fin n → K)
    (hA0 : ∀ i j, (A0 i j).coeff 0 = q.coeff 0 * M0 i j)
    (Cm Cim : Matrix (Fin n) (Fin n) K) (hCiC : Cim * Cm = 1)
    (T : Fin n → Fin n → K)
    (hT : ∀ i j, T i j = (Cm * Matrix.of M0 * Cim - Cm.map (fun z ↦ z′) * Cim) i j)
    (htri : ∀ i j : Fin n, j < i → T i j = 0)
    (p qq : Fin n → ℚ) (c : Fin n → K)
    (hdiag : ∀ i, T i i = (p i : K) * b + (qq i : K) * ((c i)′ / c i))
    (hp : ∀ i (k : ℕ), 0 < k → p i ≠ k) (G0 : Fin n → K[X])
    (hom : ∀ z : K, z ≠ 0 → ∀ j : ℤ, j ≠ 0 → z′ + (j : K) * b * z ≠ 0)
    (Z : Fin n → K[X]) (hZ : ∃ i, (Z i).coeff 0 ≠ 0) (e s : ℕ) (u h1 : K[X])
    (hu : u.coeff 0 ≠ 0) (hh1 : h1.coeff 0 ≠ 0)
    (hs : SysSol 0 b q (X ^ s * h1) A0 G0 Z (X ^ e * u)) : e ≤ s := by
  classical
  by_contra hes
  push Not at hes
  obtain ⟨t, rfl⟩ : ∃ t, e = s + t + 1 := ⟨e - s - 1, by omega⟩
  set E : K := ((s + t + 1 : ℕ) : K) with hE
  have hDX : DzL 0 b (X : K[X]) = C b * X := by rw [DzL_X]; simp
  have hDXe : DzL 0 b ((X : K[X]) ^ (s + t + 1)) = C (E * b) * X ^ (s + t + 1) := by
    rw [DzL_pow, hDX, C_mul, hE, ← C_eq_natCast]; ring
  set u0 := u.coeff 0 with hu0d
  set q0 := q.coeff 0 with hq0d
  set y : Fin n → K := fun i ↦ (Z i).coeff 0 / u0 with hy
  -- the leading coefficients: `yᵢ′ − E b yᵢ + ∑ⱼ M₀ᵢⱼ yⱼ = 0`
  have hrow : ∀ i, (y i)′ - E * b * y i + ∑ j, M0 i j * y j = 0 := by
    intro i
    have key : q * h1 * (u * DzL 0 b (Z i) - (C (E * b) * u + DzL 0 b u) * Z i) +
        h1 * u * ∑ j, A0 i j * Z j = q * X ^ (t + 1) * u ^ 2 * G0 i := by
      have h := hs i
      rw [DzL_mul, hDXe] at h
      apply mul_left_cancel₀ (pow_ne_zero (2 * s + t + 1) (X_ne_zero : (X : K[X]) ≠ 0))
      linear_combination h
    set S := ∑ j, M0 i j * (Z j).coeff 0 with hS
    have hsum0 : (∑ j, A0 i j * Z j).coeff 0 = q0 * S := by
      rw [finsetSum_coeff, hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_coeff_zero, hA0]; ring
    have h0 := congrArg (fun P : K[X] ↦ P.coeff 0) key
    simp only [coeff_add, mul_coeff_zero, coeff_sub, coeff_C_zero, coeff_zero_DzL_exp, hsum0,
      coeff_X_pow, if_neg (show 0 ≠ t + 1 by omega), zero_mul, mul_zero] at h0
    have hsumy : ∑ j, M0 i j * y j = S / u0 := by
      rw [hS, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hy]; ring
    set zi := (Z i).coeff 0 with hzi
    have hd : (y i)′ = (u0 * zi′ - zi * u0′) / u0 ^ 2 := by
      rw [hy, Derivation.leibniz_div]; simp only [smul_eq_mul]; ring
    rw [hd, hsumy]
    have hyi : y i = zi / u0 := rfl
    rw [hyi]
    rw [← hu0d, ← hq0d] at h0
    have hq0h : q0 * h1.coeff 0 ≠ 0 := mul_ne_zero hq0 hh1
    have hbr : u0 * zi′ - E * b * u0 * zi - u0′ * zi + u0 * S = 0 := by
      have h2 : q0 * h1.coeff 0 * (u0 * zi′ - E * b * u0 * zi - u0′ * zi + u0 * S) = 0 := by
        linear_combination h0
      exact (mul_eq_zero.mp h2).resolve_left hq0h
    rw [show (u0 * zi′ - zi * u0′) / u0 ^ 2 - E * b * (zi / u0) + S / u0 =
      (u0 * zi′ - E * b * u0 * zi - u0′ * zi + u0 * S) / u0 ^ 2 by field_simp; ring, hbr,
      zero_div]
  -- the gauge-transformed components `w = C y`
  set w : Fin n → K := Cm *ᵥ y with hw
  have hyw : y = Cim *ᵥ w := by rw [hw, Matrix.mulVec_mulVec, hCiC, Matrix.one_mulVec]
  have hderw : ∀ i, (w i)′ = ∑ j, (Cm i j)′ * y j + ∑ j, Cm i j * (y j)′ := fun i ↦ by
    simp only [hw, Matrix.mulVec, dotProduct, map_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  set Cd : Matrix (Fin n) (Fin n) K := Cm.map (fun z ↦ z′) with hCd
  set yd : Fin n → K := fun j ↦ (y j)′ with hyd
  have hTw : ∀ i, ∑ j, T i j * w j = (Cm *ᵥ (Matrix.of M0 *ᵥ y)) i - (Cd *ᵥ y) i := by
    intro i
    have e : (fun i ↦ ∑ j, T i j * w j) =
        (Cm * Matrix.of M0 * Cim - Cd * Cim) *ᵥ w := by
      funext i
      simp only [Matrix.mulVec, dotProduct, hT]
    have := congrFun e i
    rw [this, Matrix.sub_mulVec, Pi.sub_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← hyw, ← Matrix.mulVec_mulVec, ← hyw]
  have hwd : ∀ i, (w i)′ = (Cd *ᵥ y) i + (Cm *ᵥ yd) i := fun i ↦ by
    rw [hderw i]
    simp [Matrix.mulVec, dotProduct, hCd, hyd]
  have hroww : ∀ i, (w i)′ - E * b * w i + ∑ j, T i j * w j = 0 := by
    intro i
    rw [hwd, hTw]
    have h0 : (Cm *ᵥ (fun j ↦ (y j)′ - E * b * y j + ∑ k, M0 j k * y k)) i = 0 := by
      have : (fun j ↦ (y j)′ - E * b * y j + ∑ k, M0 j k * y k) = 0 := funext fun j ↦ hrow j
      rw [this, Matrix.mulVec_zero]; rfl
    have e1 : (Cm *ᵥ (fun j ↦ (y j)′ - E * b * y j + ∑ k, M0 j k * y k)) i =
        (Cm *ᵥ yd) i - E * b * w i + (Cm *ᵥ (Matrix.of M0 *ᵥ y)) i := by
      simp only [Matrix.mulVec, dotProduct, hyd, hw, Matrix.of_apply, mul_add, mul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1; congr 1
      refine Finset.sum_congr rfl fun j _ ↦ by ring
    rw [e1] at h0
    linear_combination h0
  obtain ⟨i1, hi1⟩ := hZ
  have hne : (Finset.univ.filter fun i ↦ w i ≠ 0).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
    have hw0 : w = 0 := funext fun i ↦ by simpa using hemp (Finset.mem_univ i)
    have := congrFun hyw i1
    rw [hw0, Matrix.mulVec_zero] at this
    exact div_ne_zero hi1 hu (by simpa [hy] using this)
  -- the last non-zero component
  set i := (Finset.univ.filter fun i ↦ w i ≠ 0).max' hne
  have hi := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  have hsum : ∑ j, T i j * w j = T i i * w i := by
    refine Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · rw [htri i j hlt, zero_mul]
    · have : w j = 0 := by
        by_contra hy0
        exact absurd (Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy0⟩))
          (not_le.mpr hgt)
      rw [this, mul_zero]
  have heq : (w i)′ + (((p i - (s + t + 1 : ℕ) : ℚ) : K) * b + (qq i : K) * ((c i)′ / c i)) *
      w i = 0 := by
    have := hroww i
    rw [hsum, hdiag, hE] at this
    push_cast at this ⊢
    linear_combination this
  by_cases hr : (p i - (s + t + 1 : ℕ) : ℚ) = 0
  · exact hp i (s + t + 1) (by omega) (by linarith)
  · exact hi (hom_ratlog b hom _ (qq i) hr (c i) _ heq)

open Matrix in
/-- **The special factors with a gauge-triangular limit at `t = 0`** (the hypothesis of
`sys_den_bound'`). -/
theorem sys_den_special_gauge (b : K) (q : K[X]) (hq0 : q.coeff 0 ≠ 0)
    (A0 : Matrix (Fin n) (Fin n) K[X]) (M0 : Fin n → Fin n → K)
    (hA0 : ∀ i j, (A0 i j).coeff 0 = q.coeff 0 * M0 i j)
    (Cm Cim : Matrix (Fin n) (Fin n) K) (hCiC : Cim * Cm = 1)
    (T : Fin n → Fin n → K)
    (hT : ∀ i j, T i j = (Cm * Matrix.of M0 * Cim - Cm.map (fun z ↦ z′) * Cim) i j)
    (htri : ∀ i j : Fin n, j < i → T i j = 0)
    (p qq : Fin n → ℚ) (c : Fin n → K)
    (hdiag : ∀ i, T i i = (p i : K) * b + (qq i : K) * ((c i)′ / c i))
    (hp : ∀ i (k : ℕ), 0 < k → p i ≠ k) (G0 : Fin n → K[X])
    (hom : ∀ z : K, z ≠ 0 → ∀ j : ℤ, j ≠ 0 → z′ + (j : K) * b * z ≠ 0)
    (hnormal : ∀ p : K[X], Irreducible p → p ∣ DzL 0 b p → X ∣ p) :
    ∀ (P : K[X]), Irreducible P → P ∣ DzL 0 b P → ∀ (Z : Fin n → K[X]) (e s : ℕ) (u h1 : K[X]),
      (∃ i, ¬ P ∣ Z i) → ¬ P ∣ u → ¬ P ∣ h1 → SysSol 0 b q (P ^ s * h1) A0 G0 Z (P ^ e * u) →
        e ≤ s := by
  intro P hP hPd Z' e s u h1 hZ' hu hh1 hs'
  obtain ⟨r, hr⟩ := hnormal P hP hPd
  have hru : IsUnit r := (hP.isUnit_or_isUnit hr).resolve_left (not_isUnit_X)
  obtain ⟨c0, hc0, hc0r⟩ := Polynomial.isUnit_iff.mp hru
  have hc0' : c0 ≠ 0 := hc0.ne_zero
  have hPX : P = X * C c0 := by rw [hr, hc0r]
  obtain ⟨i0, hi0⟩ := hZ'
  have hu0 : (C (c0 ^ e) * u).coeff 0 ≠ 0 := by
    rw [coeff_C_mul]
    exact mul_ne_zero (pow_ne_zero _ hc0') (coeff_zero_ne_of_not_dvd' P _ c0 hc0' hPX hu)
  have hh10 : (C (c0 ^ s) * h1).coeff 0 ≠ 0 := by
    rw [coeff_C_mul]
    exact mul_ne_zero (pow_ne_zero _ hc0') (coeff_zero_ne_of_not_dvd' P _ c0 hc0' hPX hh1)
  have e1 : P ^ s * h1 = X ^ s * (C (c0 ^ s) * h1) := by rw [hPX, mul_pow, C_pow]; ring
  have e2 : P ^ e * u = X ^ e * (C (c0 ^ e) * u) := by rw [hPX, mul_pow, C_pow]; ring
  rw [e1, e2] at hs'
  exact sys_den_zero_gauge b q hq0 A0 M0 hA0 Cm Cim hCiC T hT htri p qq c hdiag hp G0 hom Z'
    ⟨i0, coeff_zero_ne_of_not_dvd' P _ c0 hc0' hPX hi0⟩ e s _ _ hu0 hh10 hs'

end Tower.Sys
