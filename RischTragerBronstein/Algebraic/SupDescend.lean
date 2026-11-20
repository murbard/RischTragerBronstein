import RischTragerBronstein.Algebraic.SupBranchR

/-!
# Descending bivariate polynomials to a discrete valuation ring

`descend_bivar`: a non-zero `W ∈ K[X][X]` (`K` the fraction field of a DVR `O`) is a non-zero scalar
multiple of a primitive `ψ ∈ O[X][X]` (not all coefficients divisible by `ϖ`).
-/

open Polynomial

namespace Sup

section Frac

variable {O K : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]

local notation "ι" => algebraMap O K

/-- **Clearing denominators** of a bivariate polynomial. -/
lemma exists_integer_bivar (W : K[X][X]) :
    ∃ (d : O) (ψ₀ : O[X][X]), d ≠ 0 ∧
      ψ₀.map (mapRingHom ι) = Polynomial.C (Polynomial.C (ι d)) * W := by
  classical
  set S : Finset K := W.support.biUnion fun j ↦ (W.coeff j).support.image fun a ↦ (W.coeff j).coeff a
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) S
  have hint' : ∀ j a, ∃ z : O, ι z = ι b * (W.coeff j).coeff a := by
    intro j a
    by_cases hja : (W.coeff j).coeff a = 0
    · exact ⟨0, by rw [hja, mul_zero, map_zero]⟩
    have hj : j ∈ W.support := by
      rw [mem_support_iff]; intro h; rw [h, coeff_zero] at hja; exact hja rfl
    have hmem : (W.coeff j).coeff a ∈ S := Finset.mem_biUnion.mpr ⟨j, hj,
      Finset.mem_image.mpr ⟨a, mem_support_iff.mpr hja, rfl⟩⟩
    obtain ⟨z, hz⟩ := hint _ hmem
    exact ⟨z, by rw [hz, Algebra.smul_def]⟩
  choose c hc using hint'
  refine ⟨b, ∑ j ∈ W.support, Polynomial.monomial j
    (∑ a ∈ (W.coeff j).support, Polynomial.monomial a (c j a)), nonZeroDivisors.ne_zero hb, ?_⟩
  ext j a
  rw [coeff_map, coe_mapRingHom, coeff_map, coeff_C_mul, coeff_C_mul, finsetSum_coeff]
  by_cases hj : j ∈ W.support
  · rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [coeff_monomial, if_neg hij])
      (fun h ↦ absurd hj h), coeff_monomial, if_pos rfl, finsetSum_coeff]
    by_cases ha : a ∈ (W.coeff j).support
    · rw [Finset.sum_eq_single a (fun i _ hia ↦ by rw [coeff_monomial, if_neg hia])
        (fun h ↦ absurd ha h), coeff_monomial, if_pos rfl, hc]
    · rw [Finset.sum_eq_zero fun i hi ↦ by
        rw [coeff_monomial, if_neg (fun h ↦ ha (by rw [← h]; exact hi))], map_zero]
      rw [notMem_support_iff.mp ha, mul_zero]
  · rw [Finset.sum_eq_zero fun i hi ↦ by
      rw [coeff_monomial, if_neg (fun h ↦ hj (by rw [← h]; exact hi))]]
    rw [notMem_support_iff.mp hj]
    simp

end Frac

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A non-zero bivariate polynomial is `ϖᵐ` times a primitive one. -/
theorem exists_primitive_bivar {ϖ : O} (hϖ : Irreducible ϖ) {W : O[X][X]} (hW : W ≠ 0) :
    ∃ (m : ℕ) (W' : O[X][X]), W = Polynomial.C (Polynomial.C (ϖ ^ m)) * W' ∧
      ¬ ∀ j, C ϖ ∣ W'.coeff j := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, W.coeff j ≠ 0 := by
    by_contra h; push_neg at h; exact hW (Polynomial.ext h)
  obtain ⟨a, ha⟩ : ∃ a, (W.coeff j).coeff a ≠ 0 := by
    by_contra h; push_neg at h; exact hj (Polynomial.ext h)
  set z := (W.coeff j).coeff a
  have hdivz : ∀ m, Polynomial.C (Polynomial.C (ϖ ^ m)) ∣ W → ϖ ^ m ∣ z := by
    intro m ⟨W', hW'⟩
    refine ⟨(W'.coeff j).coeff a, ?_⟩
    simp only [z, hW', coeff_C_mul]
  obtain ⟨N, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hex : ∃ m, ¬ Polynomial.C (Polynomial.C (ϖ ^ (m + 1))) ∣ W := by
    refine ⟨N, fun hm ↦ ?_⟩
    have := hdivz _ hm
    rw [hv, pow_succ, mul_comm (ϖ ^ N)] at this
    have h3 : ϖ ∣ (v : O) := (mul_dvd_mul_iff_right (pow_ne_zero N hϖ.ne_zero)).mp this
    exact hϖ.not_isUnit (isUnit_of_dvd_unit h3 v.isUnit)
  set m := Nat.find hex
  have hm1 : ¬ Polynomial.C (Polynomial.C (ϖ ^ (m + 1))) ∣ W := Nat.find_spec hex
  have hm : Polynomial.C (Polynomial.C (ϖ ^ m)) ∣ W := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero, map_one, map_one]; exact one_dvd _
    · have := Nat.find_min hex (show m - 1 < m by omega)
      push_neg at this
      rwa [Nat.sub_add_cancel hpos] at this
  obtain ⟨W', hW'⟩ := hm
  refine ⟨m, W', hW', fun hall ↦ hm1 ?_⟩
  have hdiv : Polynomial.C (Polynomial.C ϖ) ∣ W' := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]; exact hall
  rw [hW', pow_succ, map_mul, map_mul]
  exact mul_dvd_mul_left _ hdiv

end DVR

section Descend

variable {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

local notation "ι" => algebraMap O K

/-- **Descending to a primitive polynomial over `O`.** -/
theorem descend_bivar {ϖ : O} (hϖ : Irreducible ϖ) (W : K[X][X]) (hW : W ≠ 0) :
    ∃ (ψ : O[X][X]) (c : K), c ≠ 0 ∧ ψ.map (mapRingHom ι) = Polynomial.C (Polynomial.C c) * W ∧
      ¬ ∀ j, C ϖ ∣ ψ.coeff j := by
  have hι : Function.Injective ι := IsFractionRing.injective O K
  obtain ⟨d, ψ₀, hd, hψ₀⟩ := exists_integer_bivar (O := O) W
  have hψ₀0 : ψ₀ ≠ 0 := by
    intro h0
    rw [h0, Polynomial.map_zero, eq_comm] at hψ₀
    rcases mul_eq_zero.mp hψ₀ with h | h
    · exact hd (hι (by simpa using h))
    · exact hW h
  obtain ⟨m, ψ, hψ, hprim⟩ := exists_primitive_bivar hϖ hψ₀0
  have hϖK : ι (ϖ ^ m) ≠ 0 := (map_ne_zero_iff _ hι).mpr (pow_ne_zero _ hϖ.ne_zero)
  refine ⟨ψ, (ι (ϖ ^ m))⁻¹ * ι d,
    mul_ne_zero (inv_ne_zero hϖK) ((map_ne_zero_iff _ hι).mpr hd), ?_, hprim⟩
  have h1 := hψ₀
  rw [hψ, Polynomial.map_mul, Polynomial.map_C, coe_mapRingHom, Polynomial.map_C] at h1
  have h2 : Polynomial.C (Polynomial.C (ι (ϖ ^ m))) * ψ.map (mapRingHom ι) =
      Polynomial.C (Polynomial.C (ι d)) * W := h1
  calc ψ.map (mapRingHom ι) = Polynomial.C (Polynomial.C ((ι (ϖ ^ m))⁻¹)) *
      (Polynomial.C (Polynomial.C (ι (ϖ ^ m))) * ψ.map (mapRingHom ι)) := by
        rw [← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hϖK, map_one, map_one, one_mul]
    _ = _ := by rw [h2, ← mul_assoc, ← map_mul, ← map_mul]

end Descend

end Sup
