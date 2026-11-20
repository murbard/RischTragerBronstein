import RischTragerBronstein.Jacobian.Helpers

/-!
# Moving functions between the fraction field, the valuation ring and the residue field

* `hnorm_eq_C_mul_wpoly` (field): a non-zero `γ` of pole order `≤ deg Γ` vanishing on `Γ` has norm
  `c · wpoly Γ`, `c ≠ 0`;
* `exists_integer_pair`: clearing denominators;
* `descend`: a non-zero function over `K = Frac O` with pole bound and zeros on a divisor defined
  over `O` gives a primitive function over `O` with the same properties.
-/

open Polynomial

namespace Jac

section Field

variable {k : Type*} [Field k]

theorem hnorm_eq_C_mul_wpoly {f : k[X]} {g : ℕ} (hf : f.natDegree = 2 * g + 1) {Γ : EDiv k}
    (hΓ : (Γ.map Prod.fst).Nodup) {γ : k[X] × k[X]} (hγ0 : γ ≠ (0, 0))
    (hγp : PoleLE g γ (edeg Γ)) (hγ : Vanishes f γ Γ) :
    ∃ c : k, c ≠ 0 ∧ hnorm f γ = C c * wpoly Γ := by
  have hfo : Odd f.natDegree := ⟨g, by omega⟩
  have hN0 := hnorm_ne_zero hfo hγ0
  obtain ⟨q0, hq0⟩ := dvd_hnorm_of_vanishes hΓ hγ
  have hw0 : wpoly Γ ≠ 0 := (wpoly_monic Γ).ne_zero
  have hq00 : q0 ≠ 0 := by rintro rfl; rw [mul_zero] at hq0; exact hN0 hq0
  have hdegN : (hnorm f γ).natDegree ≤ edeg Γ := by
    obtain ⟨ha, hb⟩ := hγp
    unfold hnorm
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_pow]; omega
    · rcases hb with hb | hb
      · simp [hb]
      · refine natDegree_mul_le.trans ?_
        rw [natDegree_pow, hf]; omega
  have hq0d : q0.natDegree = 0 := by
    have := congrArg natDegree hq0
    rw [natDegree_mul hw0 hq00, natDegree_wpoly] at this
    omega
  refine ⟨q0.coeff 0, fun h ↦ ?_, ?_⟩
  · rw [eq_C_of_natDegree_eq_zero hq0d, h, C_0] at hq00; exact hq00 rfl
  · rw [hq0]; nth_rewrite 1 [eq_C_of_natDegree_eq_zero hq0d]; rw [mul_comm]

end Field

section Frac

variable {O K : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]

/-- **Clearing denominators** of a pair. -/
lemma exists_integer_pair (ψ : K[X] × K[X]) :
    ∃ (d : O) (ψ₀ : O[X] × O[X]), d ≠ 0 ∧ ψ₀.1.map (algebraMap O K) = C (algebraMap O K d) * ψ.1 ∧
      ψ₀.2.map (algebraMap O K) = C (algebraMap O K d) * ψ.2 := by
  obtain ⟨b1, hb1m, hb1⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) ψ.1
  obtain ⟨b2, hb2m, hb2⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) ψ.2
  refine ⟨b1 * b2, (C b2 * IsLocalization.integerNormalization (nonZeroDivisors O) ψ.1,
    C b1 * IsLocalization.integerNormalization (nonZeroDivisors O) ψ.2),
    mul_ne_zero (nonZeroDivisors.ne_zero hb1m) (nonZeroDivisors.ne_zero hb2m), ?_, ?_⟩
  · rw [Polynomial.map_mul, hb1, map_C, ← algebraMap_smul K, smul_eq_C_mul, map_mul, C_mul]; ring
  · rw [Polynomial.map_mul, hb2, map_C, ← algebraMap_smul K, smul_eq_C_mul, map_mul, C_mul]; ring

variable [IsDiscreteValuationRing O]

lemma natDegree_map_frac (P : O[X]) : (P.map (algebraMap O K)).natDegree = P.natDegree :=
  natDegree_map_eq_of_injective (IsFractionRing.injective O K) P

/-- **Descending to a primitive function over `O`.** -/
theorem descend {ϖ : O} (hϖ : Irreducible ϖ) {g N : ℕ} {f : O[X]} {Δ : EDiv O}
    (hon : OnCurve f Δ) {ψ : K[X] × K[X]} (hψ0 : ψ ≠ (0, 0)) (hψp : PoleLE g ψ N)
    (hψv : Vanishes (f.map (algebraMap O K)) ψ (emap (algebraMap O K) Δ)) :
    ∃ ψ₁ : O[X] × O[X], ¬ (C ϖ ∣ ψ₁.1 ∧ C ϖ ∣ ψ₁.2) ∧ PoleLE g ψ₁ N ∧ Vanishes f ψ₁ Δ ∧
      ∃ κ : K, κ ≠ 0 ∧ ψ₁.1.map (algebraMap O K) = C κ * ψ.1 ∧
        ψ₁.2.map (algebraMap O K) = C κ * ψ.2 := by
  set ι := algebraMap O K
  have hι : Function.Injective ι := IsFractionRing.injective O K
  obtain ⟨d, ψ₀, hd, h1, h2⟩ := exists_integer_pair (O := O) ψ
  have hψ₀ : ψ₀ ≠ (0, 0) := by
    intro h
    apply hψ0
    have hdK : ι d ≠ 0 := (map_ne_zero_iff ι hι).mpr hd
    rw [h] at h1 h2
    simp only [Polynomial.map_zero] at h1 h2
    exact Prod.ext (by simpa [hd] using h1.symm) (by simpa [hd] using h2.symm)
  obtain ⟨m, a', b', ha', hb', hprim⟩ := exists_primitive_pair hϖ (a := ψ₀.1) (b := ψ₀.2)
    (by simpa using hψ₀)
  have hϖm : ι (ϖ ^ m) ≠ 0 := (map_ne_zero_iff ι hι).mpr (pow_ne_zero m hϖ.ne_zero)
  have hdK : ι d ≠ 0 := (map_ne_zero_iff ι hι).mpr hd
  set κ : K := ι d / ι (ϖ ^ m)
  have hκ : κ ≠ 0 := div_ne_zero hdK hϖm
  have hmapa : a'.map ι = C κ * ψ.1 := by
    have e : C (ι (ϖ ^ m)) * a'.map ι = C (ι d) * ψ.1 := by
      rw [← h1, ha', Polynomial.map_mul, map_C]
    apply mul_left_cancel₀ (C_ne_zero.mpr hϖm)
    rw [e, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hϖm]
  have hmapb : b'.map ι = C κ * ψ.2 := by
    have e : C (ι (ϖ ^ m)) * b'.map ι = C (ι d) * ψ.2 := by
      rw [← h2, hb', Polynomial.map_mul, map_C]
    apply mul_left_cancel₀ (C_ne_zero.mpr hϖm)
    rw [e, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hϖm]
  refine ⟨(a', b'), hprim, ?_, ?_, κ, hκ, hmapa, hmapb⟩
  · obtain ⟨ha, hb⟩ := hψp
    constructor
    · show 2 * a'.natDegree ≤ N
      rw [← natDegree_map_frac (K := K), hmapa, natDegree_C_mul hκ]; exact ha
    · show b' = 0 ∨ 2 * b'.natDegree + 2 * g + 1 ≤ N
      rcases hb with hb | hb
      · left
        apply Polynomial.map_injective ι hι
        rw [hmapb, hb, mul_zero, Polynomial.map_zero]
      · right; rw [← natDegree_map_frac (K := K), hmapb, natDegree_C_mul hκ]; exact hb
  · intro q hq
    obtain ⟨h2q, hq2⟩ := hon q hq
    apply VanishAt.of_map hι h2q hq2
    have := hψv (ι q.1, ι q.2.1, q.2.2) (List.mem_map_of_mem hq)
    have h' := this.C_mul (c := κ)
    simp only at h' ⊢
    rw [hmapa, hmapb]; exact h'

end Frac

end Jac
