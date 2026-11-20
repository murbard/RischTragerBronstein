import RischTragerBronstein.Computable.SysDenT
import Mathlib.LinearAlgebra.Lagrange

/-!
# The place `t = 0` with an annihilated rational limit

At an exponential level `t′ = b t`, if `A₀(0) = q(0) b Λ₀` with `Λ₀` rational and
`∏_{k<N} (Λ₀ − k/N) = 0`, then a solution has no pole at `t = 0` beyond the right-hand side
(`sys_den_zero_ann`): the leading coefficient `y` of a pole of order `e ≥ 1` satisfies
`y′ = b (e − Λ₀) y`; the Lagrange idempotents `Eₖ` of `Λ₀` (`Λ₀ Eₖ = (k/N) Eₖ`, `∑ Eₖ = 1`) split
`y` into components with `zₖ′ + (k/N − e) b zₖ = 0`, which vanish at an exponential level since
`k/N − e ≠ 0`. No triangularization is needed.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K] {n : ℕ}

/-- `(X − vᵢ) Lᵢ = wᵢ ∏ⱼ (X − vⱼ)` for the Lagrange basis. -/
lemma X_sub_mul_basis {F ι : Type*} [Field F] [DecidableEq ι] (s : Finset ι) (v : ι → F) (i : ι)
    (hi : i ∈ s) : (X - C (v i)) * Lagrange.basis s v i =
      C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by
  rw [Lagrange.basis, Lagrange.nodalWeight, Lagrange.nodal, ← Finset.mul_prod_erase s _ hi]
  simp only [Lagrange.basisDivisor, Finset.prod_mul_distrib, map_prod]
  ring

lemma derivation_ratCast_K (D : Derivation ℤ K K) (q : ℚ) : D (q : K) = 0 := by
  have hb : ((q.den : ℤ) : K) * (q : K) = (q.num : K) := by
    rw [Rat.cast_def]
    have : ((q.den : ℤ) : K) ≠ 0 := by exact_mod_cast q.den_nz
    field_simp
    push_cast; ring
  have := congrArg D hb
  rw [Derivation.leibniz, Derivation.map_intCast, Derivation.map_intCast, smul_zero, add_zero,
    smul_eq_mul] at this
  have hd : ((q.den : ℤ) : K) ≠ 0 := by exact_mod_cast q.den_nz
  exact (mul_eq_zero.mp this).resolve_left hd

/-- The nodes `k/N`. -/
def annNodes (N : ℕ) : ℕ → ℚ := fun k ↦ (k : ℚ) / N

lemma annNodes_inj (N : ℕ) (hN : 0 < N) : Set.InjOn (annNodes N) (Finset.range N) := by
  intro a _ b _ h
  simp only [annNodes] at h
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp at h
  exact_mod_cast h

/-- **The special place `t = 0` with an annihilated rational limit.** -/
theorem sys_den_zero_ann (b : K) (q : K[X]) (hq0 : q.coeff 0 ≠ 0)
    (A0 : Matrix (Fin n) (Fin n) K[X]) (Λ0 : Fin n → Fin n → ℚ)
    (hA0 : ∀ i j, (A0 i j).coeff 0 = q.coeff 0 * b * (Λ0 i j : K))
    (N : ℕ) (hN : 0 < N)
    (hP : aeval (Matrix.of Λ0) (Lagrange.nodal (Finset.range N) (annNodes N)) = 0)
    (G0 : Fin n → K[X])
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
  -- the Lagrange idempotents
  set A : Matrix (Fin n) (Fin n) ℚ := Matrix.of Λ0 with hA
  set Eid : ℕ → Matrix (Fin n) (Fin n) ℚ := fun k ↦ aeval A (Lagrange.basis (Finset.range N) (annNodes N) k)
    with hEid
  have hsum : ∑ k ∈ Finset.range N, Eid k = 1 := by
    rw [← map_sum, Lagrange.sum_basis (annNodes_inj N hN) ⟨0, Finset.mem_range.mpr hN⟩, map_one]
  have heig : ∀ k ∈ Finset.range N, A * Eid k = annNodes N k • Eid k := by
    intro k hk
    have h1' := congrArg (aeval A) (X_sub_mul_basis (Finset.range N) (annNodes N) k hk)
    rw [map_mul, map_mul, hP, mul_zero, map_sub, aeval_X, aeval_C, sub_mul] at h1'
    rw [sub_eq_zero] at h1'
    rw [h1', ← Algebra.smul_def]
  have hcomm : ∀ k, Eid k * A = A * Eid k := fun k ↦ by
    have := congrArg (aeval A) (mul_comm (Lagrange.basis (Finset.range N) (annNodes N) k) X)
    simpa [map_mul, aeval_X, hEid] using this
  have hEA : ∀ k ∈ Finset.range N, Eid k * A = annNodes N k • Eid k := fun k hk ↦ by
    rw [hcomm, heig k hk]
  -- the components `zₖ = Eₖ y`
  set z : ℕ → Fin n → K := fun k i ↦ ∑ j, ((Eid k i j : ℚ) : K) * y j with hz
  have hdq : ∀ c : ℚ, ((c : K))′ = 0 := fun c ↦ by
    have := derivation_ratCast_K (Differential.deriv : Derivation ℤ K K) c
    exact this
  have hzero : ∀ k ∈ Finset.range N, ∀ i, z k i = 0 := by
    intro k hk i
    have hvk : annNodes N k < 1 := by
      simp only [annNodes]
      have hN' : (0 : ℚ) < N := by exact_mod_cast hN
      rw [div_lt_one hN']
      exact_mod_cast Finset.mem_range.mp hk
    have hr : (annNodes N k - (s + t + 1 : ℕ) : ℚ) ≠ 0 := by
      have : (1 : ℚ) ≤ ((s + t + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ s + t + 1)
      linarith
    refine hom_rat b hom _ hr (z k i) ?_
    -- `zₖ′ = (e − vₖ) b zₖ`
    have hder : (z k i)′ = ∑ j, ((Eid k i j : ℚ) : K) * (y j)′ := by
      simp only [hz, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Derivation.leibniz, hdq, smul_zero, add_zero, smul_eq_mul]
    have hyd : ∀ j, (y j)′ = E * b * y j - b * ∑ l, (Λ0 j l : K) * y l := fun j ↦ by
      linear_combination hrow j
    have hEAil : ∀ l, ∑ j, ((Eid k i j : ℚ) : K) * (Λ0 j l : K) = ((annNodes N k : ℚ) : K) *
        ((Eid k i l : ℚ) : K) := fun l ↦ by
      have := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ ↦ ((M i l : ℚ) : K)) (hEA k hk)
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, hA, Matrix.of_apply] at this
      push_cast at this
      exact this
    rw [hder]
    simp only [hyd, mul_sub, Finset.sum_sub_distrib]
    have h2 : ∑ j, ((Eid k i j : ℚ) : K) * (b * ∑ l, (Λ0 j l : K) * y l) =
        b * ((annNodes N k : ℚ) : K) * z k i := by
      simp only [Finset.mul_sum, hz]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      have := hEAil l
      calc ∑ j, ((Eid k i j : ℚ) : K) * (b * ((Λ0 j l : K) * y l))
          = b * y l * ∑ j, ((Eid k i j : ℚ) : K) * (Λ0 j l : K) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
        _ = _ := by rw [this]; ring
    rw [h2]
    have h3 : ∑ j, ((Eid k i j : ℚ) : K) * (E * b * y j) = E * b * z k i := by
      simp only [hz, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [h3, hE]
    push_cast
    ring
  -- hence `y = 0`
  obtain ⟨i1, hi1⟩ := hZ
  have hy1 : y i1 ≠ 0 := div_ne_zero hi1 hu
  apply hy1
  have : y i1 = ∑ k ∈ Finset.range N, z k i1 := by
    simp only [hz]
    rw [Finset.sum_comm]
    have hs1 : ∀ j, ∑ k ∈ Finset.range N, ((Eid k i1 j : ℚ) : K) = if i1 = j then 1 else 0 := by
      intro j
      have := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ ↦ ((M i1 j : ℚ) : K)) hsum
      simp only [Matrix.sum_apply, Matrix.one_apply] at this
      push_cast at this
      rw [this]
      split_ifs <;> simp
    simp only [← Finset.sum_mul, hs1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [this]
  exact Finset.sum_eq_zero fun k hk ↦ hzero k hk i1

lemma coeff_zero_ne_of_not_dvd' (p f : K[X]) (c : K) (hc : c ≠ 0)
    (hp : p = X * C c) (hf : ¬ p ∣ f) : f.coeff 0 ≠ 0 := by
  intro h0
  apply hf
  obtain ⟨g, hg⟩ := X_dvd_iff.mpr h0
  exact ⟨C c⁻¹ * g, by rw [hg, hp, mul_assoc, ← mul_assoc (C c), ← C_mul, mul_inv_cancel₀ hc, C_1,
    one_mul]⟩

/-- **The special places at an exponential level** (only `t = 0`) with an annihilated rational limit
of the matrix at `t = 0`: the hypothesis `hspec` of `sys_den_bound'`. -/
theorem sys_den_special_ann (b : K) (q : K[X]) (hq0 : q.coeff 0 ≠ 0)
    (A0 : Matrix (Fin n) (Fin n) K[X]) (Λ0 : Fin n → Fin n → ℚ)
    (hA0 : ∀ i j, (A0 i j).coeff 0 = q.coeff 0 * b * (Λ0 i j : K))
    (N : ℕ) (hN : 0 < N)
    (hP : aeval (Matrix.of Λ0) (Lagrange.nodal (Finset.range N) (annNodes N)) = 0)
    (G0 : Fin n → K[X])
    (hom : ∀ z : K, z ≠ 0 → ∀ j : ℤ, j ≠ 0 → z′ + (j : K) * b * z ≠ 0)
    (hnormal : ∀ p : K[X], Irreducible p → p ∣ DzL 0 b p → X ∣ p) :
    ∀ (p : K[X]), Irreducible p → p ∣ DzL 0 b p → ∀ (Z : Fin n → K[X]) (e s : ℕ) (u h1 : K[X]),
      (∃ i, ¬ p ∣ Z i) → ¬ p ∣ u → ¬ p ∣ h1 → SysSol 0 b q (p ^ s * h1) A0 G0 Z (p ^ e * u) →
        e ≤ s := by
  intro p hp hpd Z' e s u h1 hZ' hu hh1 hs'
  obtain ⟨r, hr⟩ := hnormal p hp hpd
  have hru : IsUnit r := (hp.isUnit_or_isUnit hr).resolve_left (not_isUnit_X)
  obtain ⟨c0, hc0, hc0r⟩ := Polynomial.isUnit_iff.mp hru
  have hc0' : c0 ≠ 0 := hc0.ne_zero
  have hpX : p = X * C c0 := by rw [hr, hc0r]
  obtain ⟨i0, hi0⟩ := hZ'
  have hu0 : (C (c0 ^ e) * u).coeff 0 ≠ 0 := by
    rw [coeff_C_mul]
    exact mul_ne_zero (pow_ne_zero _ hc0') (coeff_zero_ne_of_not_dvd' p _ c0 hc0' hpX hu)
  have hh10 : (C (c0 ^ s) * h1).coeff 0 ≠ 0 := by
    rw [coeff_C_mul]
    exact mul_ne_zero (pow_ne_zero _ hc0') (coeff_zero_ne_of_not_dvd' p _ c0 hc0' hpX hh1)
  have e1 : p ^ s * h1 = X ^ s * (C (c0 ^ s) * h1) := by rw [hpX, mul_pow, C_pow]; ring
  have e2 : p ^ e * u = X ^ e * (C (c0 ^ e) * u) := by rw [hpX, mul_pow, C_pow]; ring
  rw [e1, e2] at hs'
  exact sys_den_zero_ann b q hq0 A0 Λ0 hA0 N hN hP G0 hom Z'
    ⟨i0, coeff_zero_ne_of_not_dvd' p _ c0 hc0' hpX hi0⟩ e s _ _ hu0 hh10 hs'

end Tower.Sys
