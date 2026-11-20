import RischTragerBronstein.Computable.SysDenE
import RischTragerBronstein.Computable.SysDegT
import RischTragerBronstein.Algebraic.QIndep

/-!
# Coupled Risch systems: the place `t = 0` with a triangular rational limit

At an exponential level `t′ = b t`, if `A₀(0) = q(0) b Λ₀` with `Λ₀` a rational triangular matrix
without positive integer diagonal entries, a solution has no pole at `t = 0` beyond the
right-hand side (`sys_den_zero_tri`): the leading coefficient `y` of a pole of order `e`
satisfies `y′ + b (Λ₀ − e) y = 0`, and the extreme non-zero component gives
`yᵢ′ + (Λ₀ᵢᵢ − e) b yᵢ = 0`, impossible at an exponential level unless `Λ₀ᵢᵢ = e`.
This generalizes `sys_den_zero` (`Λ₀ = 0`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K] {n : ℕ}

/-- **The special place `t = 0` with a rational limit triangular after a permutation.** -/
theorem sys_den_zero_perm (b : K) (q : K[X]) (hq0 : q.coeff 0 ≠ 0)
    (A0 : Matrix (Fin n) (Fin n) K[X]) (Λ0 : Fin n → Fin n → ℚ)
    (hA0 : ∀ i j, (A0 i j).coeff 0 = q.coeff 0 * b * (Λ0 i j : K))
    (σ : Equiv.Perm (Fin n))
    (htri : (∀ i j : Fin n, i < j → Λ0 (σ i) (σ j) = 0) ∨ (∀ i j : Fin n, j < i → Λ0 (σ i) (σ j) = 0))
    (hdiag : ∀ i (k : ℕ), 0 < k → Λ0 i i ≠ k) (G0 : Fin n → K[X])
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
  -- the leading coefficients: `yᵢ′ − E b yᵢ + b ∑ⱼ Λᵢⱼ yⱼ = 0`
  have hrow : ∀ i, (y i)′ - E * b * y i + b * ∑ j, (Λ0 i j : K) * y j = 0 := by
    intro i
    have key : q * h1 * (u * DzL 0 b (Z i) - (C (E * b) * u + DzL 0 b u) * Z i) +
        h1 * u * ∑ j, A0 i j * Z j = q * X ^ (t + 1) * u ^ 2 * G0 i := by
      have h := hs i
      rw [DzL_mul, hDXe] at h
      apply mul_left_cancel₀ (pow_ne_zero (2 * s + t + 1) (X_ne_zero : (X : K[X]) ≠ 0))
      linear_combination h
    set S := ∑ j, (Λ0 i j : K) * (Z j).coeff 0 with hS
    have hsum0 : (∑ j, A0 i j * Z j).coeff 0 = q0 * b * S := by
      rw [finsetSum_coeff, hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_coeff_zero, hA0]; ring
    have h0 := congrArg (fun P : K[X] ↦ P.coeff 0) key
    simp only [coeff_add, mul_coeff_zero, coeff_sub, coeff_C_zero, coeff_zero_DzL_exp, hsum0,
      coeff_X_pow, if_neg (show 0 ≠ t + 1 by omega), zero_mul, mul_zero] at h0
    have hsumy : ∑ j, (Λ0 i j : K) * y j = S / u0 := by
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
    have hbr : u0 * zi′ - E * b * u0 * zi - u0′ * zi + u0 * b * S = 0 := by
      have h2 : q0 * h1.coeff 0 * (u0 * zi′ - E * b * u0 * zi - u0′ * zi + u0 * b * S) = 0 := by
        linear_combination h0
      exact (mul_eq_zero.mp h2).resolve_left hq0h
    rw [show (u0 * zi′ - zi * u0′) / u0 ^ 2 - E * b * (zi / u0) + b * (S / u0) =
      (u0 * zi′ - E * b * u0 * zi - u0′ * zi + u0 * b * S) / u0 ^ 2 by field_simp; ring, hbr,
      zero_div]
  -- the permuted components `w = y ∘ σ`
  set w : Fin n → K := fun i ↦ y (σ i) with hw
  set Λσ : Fin n → Fin n → ℚ := fun i j ↦ Λ0 (σ i) (σ j) with hΛσ
  have hroww : ∀ i, (w i)′ - E * b * w i + b * ∑ j, (Λσ i j : K) * w j = 0 := by
    intro i
    have := hrow (σ i)
    rw [← Equiv.sum_comp σ (fun j ↦ (Λ0 (σ i) j : K) * y j)] at this
    exact this
  obtain ⟨i1, hi1⟩ := hZ
  have hne : (Finset.univ.filter fun i ↦ w i ≠ 0).Nonempty :=
    ⟨σ.symm i1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simp only [hw, Equiv.apply_symm_apply]; exact div_ne_zero hi1 hu⟩⟩
  -- the extreme non-zero component
  have hext : ∃ i, w i ≠ 0 ∧ ∑ j, (Λσ i j : K) * w j = (Λσ i i : K) * w i := by
    rcases htri with hlow | hup
    · set i := (Finset.univ.filter fun i ↦ w i ≠ 0).min' hne
      have hi := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
      refine ⟨i, hi, Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)⟩
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have : w j = 0 := by
          by_contra hy0
          exact absurd (Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy0⟩))
            (not_le.mpr hlt)
        rw [this, mul_zero]
      · rw [show Λσ i j = 0 from hlow i j hgt]; simp
    · set i := (Finset.univ.filter fun i ↦ w i ≠ 0).max' hne
      have hi := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
      refine ⟨i, hi, Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)⟩
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · rw [show Λσ i j = 0 from hup i j hlt]; simp
      · have : w j = 0 := by
          by_contra hy0
          exact absurd (Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy0⟩))
            (not_le.mpr hgt)
        rw [this, mul_zero]
  obtain ⟨i, hyi, hsum⟩ := hext
  have heq : (w i)′ + ((Λσ i i - (s + t + 1 : ℕ) : ℚ) : K) * b * w i = 0 := by
    have := hroww i
    rw [hsum, hE] at this
    push_cast at this ⊢
    linear_combination this
  by_cases hr : (Λσ i i - (s + t + 1 : ℕ) : ℚ) = 0
  · exact hdiag (σ i) (s + t + 1) (by omega) (by simp only [hΛσ] at hr; linarith)
  · exact hyi (hom_rat b hom _ hr _ heq)


open Matrix in
/-- **The special place `t = 0` with a rational limit triangular after a rational similarity**
`T = C Λ₀ C⁻¹` (the diagonal of `T`: the eigenvalues of `Λ₀`). -/
theorem sys_den_zero_sim (b : K) (q : K[X]) (hq0 : q.coeff 0 ≠ 0)
    (A0 : Matrix (Fin n) (Fin n) K[X]) (Λ0 : Fin n → Fin n → ℚ)
    (hA0 : ∀ i j, (A0 i j).coeff 0 = q.coeff 0 * b * (Λ0 i j : K))
    (Cq Ciq : Matrix (Fin n) (Fin n) ℚ) (hCiC : Ciq * Cq = 1)
    (htri : (∀ i j : Fin n, i < j → (Cq * Matrix.of Λ0 * Ciq) i j = 0) ∨
      (∀ i j : Fin n, j < i → (Cq * Matrix.of Λ0 * Ciq) i j = 0))
    (hdiag : ∀ i (k : ℕ), 0 < k → (Cq * Matrix.of Λ0 * Ciq) i i ≠ k) (G0 : Fin n → K[X])
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
  -- the leading coefficients: `yᵢ′ − E b yᵢ + b ∑ⱼ Λᵢⱼ yⱼ = 0`
  have hrow : ∀ i, (y i)′ - E * b * y i + b * ∑ j, (Λ0 i j : K) * y j = 0 := by
    intro i
    have key : q * h1 * (u * DzL 0 b (Z i) - (C (E * b) * u + DzL 0 b u) * Z i) +
        h1 * u * ∑ j, A0 i j * Z j = q * X ^ (t + 1) * u ^ 2 * G0 i := by
      have h := hs i
      rw [DzL_mul, hDXe] at h
      apply mul_left_cancel₀ (pow_ne_zero (2 * s + t + 1) (X_ne_zero : (X : K[X]) ≠ 0))
      linear_combination h
    set S := ∑ j, (Λ0 i j : K) * (Z j).coeff 0 with hS
    have hsum0 : (∑ j, A0 i j * Z j).coeff 0 = q0 * b * S := by
      rw [finsetSum_coeff, hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_coeff_zero, hA0]; ring
    have h0 := congrArg (fun P : K[X] ↦ P.coeff 0) key
    simp only [coeff_add, mul_coeff_zero, coeff_sub, coeff_C_zero, coeff_zero_DzL_exp, hsum0,
      coeff_X_pow, if_neg (show 0 ≠ t + 1 by omega), zero_mul, mul_zero] at h0
    have hsumy : ∑ j, (Λ0 i j : K) * y j = S / u0 := by
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
    have hbr : u0 * zi′ - E * b * u0 * zi - u0′ * zi + u0 * b * S = 0 := by
      have h2 : q0 * h1.coeff 0 * (u0 * zi′ - E * b * u0 * zi - u0′ * zi + u0 * b * S) = 0 := by
        linear_combination h0
      exact (mul_eq_zero.mp h2).resolve_left hq0h
    rw [show (u0 * zi′ - zi * u0′) / u0 ^ 2 - E * b * (zi / u0) + b * (S / u0) =
      (u0 * zi′ - E * b * u0 * zi - u0′ * zi + u0 * b * S) / u0 ^ 2 by field_simp; ring, hbr,
      zero_div]
  -- the transformed components `w = C y`
  set Tq : Matrix (Fin n) (Fin n) ℚ := Cq * Matrix.of Λ0 * Ciq with hTq
  set Cm : Matrix (Fin n) (Fin n) K := Cq.map (Rat.castHom K) with hCm
  set Cim : Matrix (Fin n) (Fin n) K := Ciq.map (Rat.castHom K) with hCim
  set Λm : Matrix (Fin n) (Fin n) K := (Matrix.of Λ0).map (Rat.castHom K) with hΛm
  set w : Fin n → K := Cm *ᵥ y with hw
  set Λσ : Fin n → Fin n → ℚ := fun i j ↦ Tq i j with hΛσ
  have hCiCm : Cim * Cm = 1 := by
    rw [hCim, hCm, ← Matrix.map_mul, hCiC, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyw : y = Cim *ᵥ w := by rw [hw, Matrix.mulVec_mulVec, hCiCm, Matrix.one_mulVec]
  have hΛv : ∀ i, ∑ j, (Λ0 i j : K) * y j = (Λm *ᵥ y) i := fun i ↦ by
    simp [Matrix.mulVec, dotProduct, hΛm]
  have hderw : ∀ i, (w i)′ = ∑ j, Cm i j * (y j)′ := fun i ↦ by
    simp only [hw, Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp [hCm, Differential.deriv_ratCast_K]
  have hTv : Cm *ᵥ (Λm *ᵥ y) = Tq.map (Rat.castHom K) *ᵥ w := by
    conv_lhs => rw [hyw]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [hTq, Matrix.map_mul, mul_assoc, hCm, hΛm, hCim]
  have hroww : ∀ i, (w i)′ - E * b * w i + b * ∑ j, (Λσ i j : K) * w j = 0 := by
    intro i
    have h1 : ∑ j, Cm i j * ((y j)′ - E * b * y j + b * ∑ k, (Λ0 j k : K) * y k) = 0 :=
      Finset.sum_eq_zero fun j _ ↦ by rw [hrow j, mul_zero]
    have h2 : ∑ j, Cm i j * (b * ∑ k, (Λ0 j k : K) * y k) = b * (Cm *ᵥ (Λm *ᵥ y)) i := by
      have : (Cm *ᵥ (Λm *ᵥ y)) i = ∑ j, Cm i j * (Λm *ᵥ y) j := rfl
      rw [this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hΛv j]; ring
    have h3 : ∑ j, (Λσ i j : K) * w j = (Tq.map (Rat.castHom K) *ᵥ w) i := by
      simp [Matrix.mulVec, dotProduct, hΛσ]
    rw [hderw, h3, ← hTv]
    have e1 : ∑ j, Cm i j * ((y j)′ - E * b * y j + b * ∑ k, (Λ0 j k : K) * y k) =
        ∑ j, Cm i j * (y j)′ - E * b * w i + ∑ j, Cm i j * (b * ∑ k, (Λ0 j k : K) * y k) := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hw,
        Matrix.mulVec, dotProduct, Finset.mul_sum]
      congr 1; congr 1
      refine Finset.sum_congr rfl fun j _ ↦ by ring
    rw [e1, h2] at h1
    exact h1
  obtain ⟨i1, hi1⟩ := hZ
  have hne : (Finset.univ.filter fun i ↦ w i ≠ 0).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
    have hw0 : w = 0 := funext fun i ↦ by simpa using hemp (Finset.mem_univ i)
    have := congrFun hyw i1
    rw [hw0, Matrix.mulVec_zero] at this
    exact div_ne_zero hi1 hu (by simpa [hy] using this)
  -- the extreme non-zero component
  have hext : ∃ i, w i ≠ 0 ∧ ∑ j, (Λσ i j : K) * w j = (Λσ i i : K) * w i := by
    rcases htri with hlow | hup
    · set i := (Finset.univ.filter fun i ↦ w i ≠ 0).min' hne
      have hi := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
      refine ⟨i, hi, Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)⟩
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have : w j = 0 := by
          by_contra hy0
          exact absurd (Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy0⟩))
            (not_le.mpr hlt)
        rw [this, mul_zero]
      · rw [show Λσ i j = 0 from hlow i j hgt]; simp
    · set i := (Finset.univ.filter fun i ↦ w i ≠ 0).max' hne
      have hi := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
      refine ⟨i, hi, Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)⟩
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · rw [show Λσ i j = 0 from hup i j hlt]; simp
      · have : w j = 0 := by
          by_contra hy0
          exact absurd (Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy0⟩))
            (not_le.mpr hgt)
        rw [this, mul_zero]
  obtain ⟨i, hyi, hsum⟩ := hext
  have heq : (w i)′ + ((Λσ i i - (s + t + 1 : ℕ) : ℚ) : K) * b * w i = 0 := by
    have := hroww i
    rw [hsum, hE] at this
    push_cast at this ⊢
    linear_combination this
  by_cases hr : (Λσ i i - (s + t + 1 : ℕ) : ℚ) = 0
  · exact hdiag i (s + t + 1) (by omega) (by simp only [hΛσ] at hr; linarith)
  · exact hyi (hom_rat b hom _ hr _ heq)


/-- **The special place `t = 0` with a triangular rational limit.** -/
theorem sys_den_zero_tri (b : K) (q : K[X]) (hq0 : q.coeff 0 ≠ 0)
    (A0 : Matrix (Fin n) (Fin n) K[X]) (Λ0 : Fin n → Fin n → ℚ)
    (hA0 : ∀ i j, (A0 i j).coeff 0 = q.coeff 0 * b * (Λ0 i j : K))
    (htri : (∀ i j : Fin n, i < j → Λ0 i j = 0) ∨ (∀ i j : Fin n, j < i → Λ0 i j = 0))
    (hdiag : ∀ i (k : ℕ), 0 < k → Λ0 i i ≠ k) (G0 : Fin n → K[X])
    (hom : ∀ z : K, z ≠ 0 → ∀ j : ℤ, j ≠ 0 → z′ + (j : K) * b * z ≠ 0)
    (Z : Fin n → K[X]) (hZ : ∃ i, (Z i).coeff 0 ≠ 0) (e s : ℕ) (u h1 : K[X])
    (hu : u.coeff 0 ≠ 0) (hh1 : h1.coeff 0 ≠ 0)
    (hs : SysSol 0 b q (X ^ s * h1) A0 G0 Z (X ^ e * u)) : e ≤ s :=
  sys_den_zero_perm b q hq0 A0 Λ0 hA0 (Equiv.refl _) htri hdiag G0 hom Z hZ e s u h1 hu hh1 hs

end Tower.Sys
