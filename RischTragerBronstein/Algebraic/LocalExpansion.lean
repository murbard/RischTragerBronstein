import RischTragerBronstein.Algebraic.LaurentDeriv
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Residues of Laurent series and `n`-th roots of power series

* `res f` = the coefficient of `X⁻¹`; `res_derivative`: derivatives have no residue;
  `res_logDeriv`: the residue of `f′/f` is the order of `f`.
* `exists_pow_eq`: a power series with constant coefficient `βⁿ ≠ 0` has an `n`-th root with
  constant coefficient `β` (Hensel's lemma, `K⟦X⟧` being `X`-adically complete).

These are the local tools for residues of differentials on curves: at a point where `x − α` is a
local parameter, functions expand as Laurent series in `u = x − α`, `d/dx = d/du`.
-/

open HahnSeries PowerSeries

namespace LaurentSeries

variable {K : Type*} [Field K]

/-- The residue: the coefficient of `X⁻¹`. -/
def res (f : K⸨X⸩) : K := f.coeff (-1)

lemma res_add (f g : K⸨X⸩) : res (f + g) = res f + res g := by
  simp [res]

lemma res_derivative (f : K⸨X⸩) : res (derivative K f) = 0 := by
  rw [res, derivative_coeff]; simp

lemma coeff_ofPS_neg (H : K⟦X⟧) {m : ℤ} (hm : m < 0) : (ofPowerSeries ℤ K H).coeff m = 0 := by
  rw [coeff_ofPS, if_neg (by omega)]

/-- **The residue of a logarithmic derivative is the order.** -/
theorem res_logDeriv (f : K⸨X⸩) (hf : f ≠ 0) : res (derivative K f / f) = (f.order : K) := by
  set a := f.order
  set F := f.powerSeriesPart
  have hF0 : PowerSeries.constantCoeff F ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeriesPart_coeff]
    simpa [a] using (not_congr HahnSeries.coeff_order_eq_zero).mpr hf
  have hf' : f = single a (1 : K) * ofPowerSeries ℤ K F := (single_order_mul_powerSeriesPart f).symm
  set Fi := F⁻¹
  have hFFi : F * Fi = 1 := PowerSeries.mul_inv_cancel F hF0
  have hmul : f * (single (-a) (1 : K) * ofPowerSeries ℤ K Fi) = 1 := by
    rw [hf']
    calc single a (1 : K) * ofPowerSeries ℤ K F * (single (-a) (1 : K) * ofPowerSeries ℤ K Fi)
        = (single a (1 : K) * single (-a) (1 : K)) * ofPowerSeries ℤ K (F * Fi) := by
          rw [map_mul]; ring
      _ = 1 := by rw [single_mul_single, add_neg_cancel, mul_one, hFFi]; simp
  have hinv : f⁻¹ = single (-a) (1 : K) * ofPowerSeries ℤ K Fi :=
    (eq_inv_of_mul_eq_one_right hmul).symm
  rw [div_eq_mul_inv, hinv]
  conv_lhs => rw [hf']
  rw [derivative_single_mul_ofPS]
  have e1 : (single a (1 : K) * ofPowerSeries ℤ K (PowerSeries.derivative F) +
      (a : K) • (single (a - 1) (1 : K) * ofPowerSeries ℤ K F)) *
      (single (-a) (1 : K) * ofPowerSeries ℤ K Fi) =
      ofPowerSeries ℤ K (PowerSeries.derivative F * Fi) +
        (a : K) • single (-1) (1 : K) := by
    have s1 : single a (1 : K) * single (-a) 1 = 1 := by
      rw [single_mul_single, add_neg_cancel, one_mul]; rfl
    have s2 : single (a - 1) (1 : K) * single (-a) 1 = single (-1) 1 := by
      rw [single_mul_single, one_mul]; ring_nf
    have hP : ofPowerSeries ℤ K F * ofPowerSeries ℤ K Fi = 1 := by rw [← map_mul, hFFi, map_one]
    have hC : ∀ z : K⸨X⸩, (a : K) • z = HahnSeries.C (a : K) * z := fun z ↦
      (HahnSeries.C_mul_eq_smul).symm
    rw [hC, hC, map_mul]
    linear_combination (ofPowerSeries ℤ K (PowerSeries.derivative F) * ofPowerSeries ℤ K Fi) * s1 +
      (HahnSeries.C (a : K) * ofPowerSeries ℤ K F * ofPowerSeries ℤ K Fi) * s2 +
      (HahnSeries.C (a : K) * single (-1) (1 : K)) * hP
  rw [e1, res, HahnSeries.coeff_add, coeff_ofPS_neg _ (by norm_num), zero_add,
    HahnSeries.coeff_smul, HahnSeries.coeff_single_same, smul_eq_mul, mul_one]

/-- **`n`-th roots of power series** (Hensel). -/
theorem exists_pow_eq (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (P : K⟦X⟧) (β : K) (hβ : β ≠ 0)
    (hP : PowerSeries.constantCoeff P = β ^ n) :
    ∃ Y : K⟦X⟧, Y ^ n = P ∧ PowerSeries.constantCoeff Y = β := by
  set f : Polynomial K⟦X⟧ := Polynomial.X ^ n - Polynomial.C P
  have hmon : f.Monic := Polynomial.monic_X_pow_sub_C P hn.ne'
  set a0 : K⟦X⟧ := PowerSeries.C β
  have h1 : f.eval a0 ∈ Ideal.span {(PowerSeries.X : K⟦X⟧)} := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp [f, a0, hP]
  have h2 : IsUnit (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : K⟦X⟧)})
      (f.derivative.eval a0)) := by
    refine IsUnit.map _ ?_
    have : f.derivative.eval a0 = PowerSeries.C ((n : K) * β ^ (n - 1)) := by
      simp [f, a0, Polynomial.derivative_X_pow]
    rw [this]
    exact (Ne.isUnit (mul_ne_zero hnK (pow_ne_zero _ hβ))).map PowerSeries.C
  obtain ⟨Y, hY, hYa⟩ := HenselianRing.is_henselian f hmon a0 h1 h2
  refine ⟨Y, ?_, ?_⟩
  · have := hY
    simp only [Polynomial.IsRoot, f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at this
    exact this
  · rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, sub_eq_zero] at hYa
    simpa [a0] using hYa

/-- **Uniqueness of `n`-th roots** with a given non-zero constant coefficient. -/
theorem pow_eq_pow_unique (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) {A B : K⟦X⟧}
    (hAB : A ^ n = B ^ n) (h0 : PowerSeries.constantCoeff A = PowerSeries.constantCoeff B)
    (hB : PowerSeries.constantCoeff B ≠ 0) : A = B := by
  by_contra hne
  have hB0 : B ≠ 0 := fun h ↦ hB (by rw [h, map_zero])
  -- `A − B` has positive order; compare lowest terms of `Aⁿ − Bⁿ = (A − B) · ∑ Aⁱ Bⁿ⁻¹⁻ⁱ`
  have hsub : A - B ≠ 0 := sub_ne_zero.mpr hne
  have hfac : A ^ n - B ^ n = (A - B) * ∑ i ∈ Finset.range n, A ^ i * B ^ (n - 1 - i) := by
    rw [← Commute.geom_sum₂_mul (Commute.all A B), mul_comm]
  have hsum0 : PowerSeries.constantCoeff (∑ i ∈ Finset.range n, A ^ i * B ^ (n - 1 - i)) =
      (n : K) * PowerSeries.constantCoeff B ^ (n - 1) := by
    rw [map_sum]
    simp only [map_mul, map_pow, h0]
    rw [Finset.sum_congr rfl fun i hi ↦ by
      rw [← pow_add, show i + (n - 1 - i) = n - 1 by
        have := Finset.mem_range.mp hi; omega]]
    simp
  have hsum : ∑ i ∈ Finset.range n, A ^ i * B ^ (n - 1 - i) ≠ 0 := fun h ↦ by
    have := congrArg PowerSeries.constantCoeff h
    rw [hsum0, map_zero] at this
    exact mul_ne_zero hnK (pow_ne_zero _ hB) this
  have := mul_ne_zero hsub hsum
  rw [← hfac, hAB, sub_self] at this
  exact this rfl

/-- A lower bound on the orders of the terms bounds the order of the sum. -/
lemma le_orderTop_sum {ι : Type*} (s : Finset ι) (t : ι → K⸨X⸩) (c : WithTop ℤ)
    (h : ∀ i ∈ s, c ≤ (t i).orderTop) : c ≤ (∑ i ∈ s, t i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact le_trans (le_min (h j (Finset.mem_insert_self j s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))) HahnSeries.min_orderTop_le_orderTop_add

/-- A strictly minimal term determines the order of the sum. -/
lemma orderTop_sum_eq {ι : Type*} (s : Finset ι) (t : ι → K⸨X⸩) {i0 : ι} (hi0 : i0 ∈ s)
    (h : ∀ i ∈ s, i ≠ i0 → (t i0).orderTop < (t i).orderTop) :
    (∑ i ∈ s, t i).orderTop = (t i0).orderTop := by
  classical
  rw [← Finset.add_sum_erase s t hi0]
  by_cases hne : (∑ i ∈ s.erase i0, t i) = 0
  · rw [hne, add_zero]
  apply HahnSeries.orderTop_add_eq_left
  -- the rest has order strictly larger
  obtain ⟨i1, hi1, hmin⟩ := (s.erase i0).exists_min_image (fun i ↦ (t i).orderTop)
    (Finset.nonempty_of_ne_empty (fun he ↦ hne (by rw [he, Finset.sum_empty])))
  exact lt_of_lt_of_le (h i1 (Finset.mem_of_mem_erase hi1) (Finset.ne_of_mem_erase hi1))
    (le_orderTop_sum _ _ _ hmin)

/-- **Distinct orders**: if the terms have pairwise distinct orders, a lower bound on the order of
the sum bounds every term. -/
theorem le_orderTop_of_sum_distinct {ι : Type*} (s : Finset ι) (t : ι → K⸨X⸩)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (t i).orderTop ≠ (t j).orderTop) (c : WithTop ℤ)
    (h : c ≤ (∑ i ∈ s, t i).orderTop) : ∀ i ∈ s, c ≤ (t i).orderTop := by
  classical
  intro i hi
  obtain ⟨i0, hi0, hmin⟩ := s.exists_min_image (fun i ↦ (t i).orderTop) ⟨i, hi⟩
  rw [orderTop_sum_eq s t hi0 (fun j hj hji0 ↦ lt_of_le_of_ne (hmin j hj)
    (hd i0 hi0 j hj (Ne.symm hji0)))] at h
  exact le_trans h (hmin i hi)

end LaurentSeries
