import RischTragerBronstein.Liouville.PoleOrder
import RischTragerBronstein.Liouville.MonicPrimes
import RischTragerBronstein.Liouville.Reduce

/-!
# Derivatives have no simple poles

* `mem_regularAt_of_deriv_simple_pole` (any differential domain, normal prime `p`): if `y′` has at
  most a simple pole at `p` (`y′ * p ∈ O_p`), then `y` is regular at `p`.
* `eq_zero_of_deriv_eq_proper_fraction` (over `C(x)`, `d/dx`): if `y′ = r / s` with `s` squarefree
  and `deg r < deg s`, then `r = 0`.

The second statement is the uniqueness half of Hermite reduction: in `f = g′ + r / s` the remainder
`r / s` is determined by `f`, and `f` has an antiderivative **in `C(x)`** if and only if `r = 0`.
It turns the rational integrator into a decision procedure for "is `∫ f` rational?", which is the
base case of the limited-integration problems arising in logarithmic extensions.
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
theorem mem_regularAt_of_deriv_simple_pole (hnorm : ¬p ∣ p′)
    (hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : A)) {y : K} (h : y′ * φ p ∈ regularAt K p hp) :
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
  refine hunit.ne_mul hp (f := φ p ^ j * (y′ * φ p)) (mul_mem (pow_mem hpm j) h) ?_
  ring

end Local

section Base

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'[X]] [Field K] [Algebra C'[X] K]
variable [IsFractionRing C'[X] K] [Differential K] [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

/-- Over `C(x)`: a proper fraction with squarefree denominator is a derivative only if it is `0`. -/
theorem eq_zero_of_deriv_eq_proper_fraction (hD : ∀ P : C'[X], P′ = derivative P)
    (r s : C'[X]) (hs : Squarefree s) (hdeg : r.degree < s.degree) (y : K)
    (h : y′ = φ r / φ s) : r = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hs0 : s ≠ 0 := hs.ne_zero
  have hφs : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0
  -- `y` is a polynomial
  obtain ⟨Y, rfl⟩ : ∃ Y : C'[X], y = φ Y := by
    refine exists_polynomial_of_regularAt y fun p _ hp ↦ ?_
    have hnorm : ¬p ∣ p′ := by
      rw [hD]
      intro hdvd
      have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
      have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
      exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
    refine mem_regularAt_of_deriv_simple_pole hp.prime hnorm
      (not_dvd_natCast_polynomial hp.prime) ?_
    rw [h]
    by_cases hps : p ∣ s
    · obtain ⟨s₁, rfl⟩ := hps
      have hps₁ : ¬p ∣ s₁ := fun ⟨q, hq⟩ ↦
        hp.not_isUnit (hs p ⟨q, by rw [hq]; ring⟩)
      have hφp : φ p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
      have hφs₁ : φ s₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr (right_ne_zero_of_mul hs0)
      exact ⟨r, s₁, hps₁, by rw [map_mul]; field_simp⟩
    · exact ⟨r * p, s, hps, by rw [map_mul]; field_simp⟩
  -- so `Y′ s = r`, impossible by degrees unless `r = 0`
  have hpoly : derivative Y * s = r := by
    apply hinj
    rw [map_mul, ← hD, ← deriv_algebraMap, h]
    field_simp
  by_contra hr0
  have hY' : derivative Y ≠ 0 := fun h0 ↦ hr0 (by rw [← hpoly, h0, zero_mul])
  have : s.degree ≤ r.degree := by
    rw [← hpoly, degree_mul]
    exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hY')
  exact absurd hdeg (not_lt.mpr this)

/-- A proper fraction with squarefree denominator has at most a simple pole at any prime. -/
lemma simple_pole_mem_regularAt {r s p : C'[X]} (hs : Squarefree s) (hp : Irreducible p) :
    φ r / φ s * φ p ∈ regularAt K p hp.prime := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hs0 : s ≠ 0 := hs.ne_zero
  by_cases hps : p ∣ s
  · obtain ⟨s₁, rfl⟩ := hps
    have hps₁ : ¬p ∣ s₁ := fun ⟨q, hq⟩ ↦ hp.not_isUnit (hs p ⟨q, by rw [hq]; ring⟩)
    have hφp : φ p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
    have hφs₁ : φ s₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr (right_ne_zero_of_mul hs0)
    exact ⟨r, s₁, hps₁, by rw [map_mul]; field_simp⟩
  · have hφs : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0
    exact ⟨r * p, s, hps, by rw [map_mul]; field_simp⟩

/-- Over `C(x)`: if a **sum of two** proper fractions with squarefree denominators is a derivative,
it is zero. (No common denominator is needed: the sum still has only simple poles.) -/
theorem sum_eq_zero_of_deriv_eq_sum_proper (hD : ∀ P : C'[X], P′ = derivative P)
    (r₁ s₁ r₂ s₂ : C'[X]) (hs₁ : Squarefree s₁) (hs₂ : Squarefree s₂)
    (hdeg₁ : r₁.degree < s₁.degree) (hdeg₂ : r₂.degree < s₂.degree) (y : K)
    (h : y′ = φ r₁ / φ s₁ + φ r₂ / φ s₂) : φ r₁ / φ s₁ + φ r₂ / φ s₂ = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hs₁0 : s₁ ≠ 0 := hs₁.ne_zero
  have hs₂0 : s₂ ≠ 0 := hs₂.ne_zero
  have hφs₁ : φ s₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs₁0
  have hφs₂ : φ s₂ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs₂0
  obtain ⟨Y, rfl⟩ : ∃ Y : C'[X], y = φ Y := by
    refine exists_polynomial_of_regularAt y fun p _ hp ↦ ?_
    have hnorm : ¬p ∣ p′ := by
      rw [hD]
      intro hdvd
      have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
      have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
      exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
    refine mem_regularAt_of_deriv_simple_pole hp.prime hnorm
      (not_dvd_natCast_polynomial hp.prime) ?_
    rw [h, add_mul]
    exact add_mem (simple_pole_mem_regularAt hs₁ hp) (simple_pole_mem_regularAt hs₂ hp)
  -- `Y′ s₁ s₂ = r₁ s₂ + r₂ s₁`, and the right-hand side has smaller degree than `s₁ s₂`
  have hpoly : derivative Y * (s₁ * s₂) = r₁ * s₂ + r₂ * s₁ := by
    apply hinj
    rw [map_mul, ← hD, ← deriv_algebraMap, h]
    simp only [map_add, map_mul]
    field_simp
  have hY' : derivative Y = 0 := by
    by_contra hne
    have hlt : (r₁ * s₂ + r₂ * s₁).degree < (s₁ * s₂).degree := by
      refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · rw [degree_mul, degree_mul]
        exact WithBot.add_lt_add_right (degree_ne_bot.mpr hs₂0) hdeg₁
      · rw [degree_mul, degree_mul, add_comm s₁.degree]
        exact WithBot.add_lt_add_right (degree_ne_bot.mpr hs₁0) hdeg₂
    have hle : (s₁ * s₂).degree ≤ (derivative Y * (s₁ * s₂)).degree := by
      rw [degree_mul (p := derivative Y)]
      exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hne)
    rw [hpoly] at hle
    exact absurd hlt (not_lt.mpr hle)
  rw [← h, deriv_algebraMap, hD, hY', map_zero]

/-- The same for any finite sum of proper fractions with squarefree denominators: if it is a
derivative in `C(x)`, it vanishes. This is the engine of limited integration with several
parameters. -/
theorem sum_eq_zero_of_deriv_eq_finset_sum (hD : ∀ P : C'[X], P′ = derivative P)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (r s : ι → C'[X])
    (hs : ∀ i ∈ I, Squarefree (s i)) (hdeg : ∀ i ∈ I, (r i).degree < (s i).degree) (y : K)
    (h : y′ = ∑ i ∈ I, φ (r i) / φ (s i)) : ∑ i ∈ I, φ (r i) / φ (s i) = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hs0 : ∀ i ∈ I, s i ≠ 0 := fun i hi ↦ (hs i hi).ne_zero
  have hφs : ∀ i ∈ I, φ (s i) ≠ 0 := fun i hi ↦ (map_ne_zero_iff _ hinj).mpr (hs0 i hi)
  obtain ⟨Y, rfl⟩ : ∃ Y : C'[X], y = φ Y := by
    refine exists_polynomial_of_regularAt y fun p _ hp ↦ ?_
    have hnorm : ¬p ∣ p′ := by
      rw [hD]
      intro hdvd
      have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
      have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
      exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
    refine mem_regularAt_of_deriv_simple_pole hp.prime hnorm
      (not_dvd_natCast_polynomial hp.prime) ?_
    rw [h, Finset.sum_mul]
    exact sum_mem fun i hi ↦ simple_pole_mem_regularAt (hs i hi) hp
  set S := ∏ i ∈ I, s i with hS
  set T := ∑ i ∈ I, r i * ∏ j ∈ I.erase i, s j with hT
  have hS0 : S ≠ 0 := Finset.prod_ne_zero_iff.mpr hs0
  have hsplit : ∀ i ∈ I, S = s i * ∏ j ∈ I.erase i, s j := fun i hi ↦
    (Finset.mul_prod_erase I s hi).symm
  have hpoly : derivative Y * S = T := by
    apply hinj
    rw [map_mul, ← hD, ← deriv_algebraMap, h, hT, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have := hφs i hi
    rw [hsplit i hi, map_mul, map_mul]
    field_simp
  have hY' : derivative Y = 0 := by
    by_contra hne
    have hlt : T.degree < S.degree := by
      refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hS0))]
      intro i hi
      have hP0 : ∏ j ∈ I.erase i, s j ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j hj ↦ hs0 j (Finset.mem_of_mem_erase hj)
      rw [hsplit i hi, degree_mul, degree_mul]
      exact WithBot.add_lt_add_right (degree_ne_bot.mpr hP0) (hdeg i hi)
    have hle : S.degree ≤ (derivative Y * S).degree := by
      rw [degree_mul]
      exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hne)
    rw [hpoly] at hle
    exact absurd hlt (not_lt.mpr hle)
  rw [← h, deriv_algebraMap, hD, hY', map_zero]

/-- **Limited integration over `C(x)`.** Let `f = g_f′ + r_f / s_f` and `η = g_η′ + r_η / s_η` be
Hermite decompositions (squarefree denominators, proper remainders), and `c ∈ C`. Then `f - c η`
has an antiderivative in `C(x)` if and only if `r_f s_η = c r_η s_f`. The condition is linear in `c`,
hence decidable; this is the base case of the limited-integration problems of logarithmic
extensions (`exists_limited_integral_of_liouville`). -/
theorem limited_integral_iff (hD : ∀ P : C'[X], P′ = derivative P) (g_f g_η : K)
    (r_f s_f r_η s_η : C'[X]) (hsf : Squarefree s_f) (hsη : Squarefree s_η)
    (hdf : r_f.degree < s_f.degree) (hdη : r_η.degree < s_η.degree) (c : C') :
    (∃ y : K, y′ = (g_f′ + φ r_f / φ s_f) - φ (C c) * (g_η′ + φ r_η / φ s_η)) ↔
      r_f * s_η = C c * r_η * s_f := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hφsf : φ s_f ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsf.ne_zero
  have hφsη : φ s_η ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsη.ne_zero
  have hc' : (φ (C c))′ = 0 := by rw [deriv_algebraMap, hD, derivative_C, map_zero]
  have hcg : (φ (C c) * g_η)′ = φ (C c) * g_η′ := by
    rw [Derivation.leibniz, hc']; simp [mul_comm]
  constructor
  · rintro ⟨y, hy⟩
    have hdeg₂ : (-(C c * r_η)).degree < s_η.degree := by
      rw [degree_neg]
      refine lt_of_le_of_lt ?_ hdη
      by_cases hc0 : c = 0
      · simp [hc0]
      · rw [degree_C_mul hc0]
    have hsum := sum_eq_zero_of_deriv_eq_sum_proper hD r_f s_f (-(C c * r_η)) s_η hsf hsη hdf
      hdeg₂ (y - g_f + φ (C c) * g_η) (by
        rw [map_add, map_sub, hy, hcg, map_neg, map_mul]
        ring)
    apply hinj
    rw [map_neg, map_mul] at hsum
    rw [map_mul, map_mul, map_mul]
    field_simp at hsum
    linear_combination hsum
  · intro hcross
    refine ⟨g_f - φ (C c) * g_η, ?_⟩
    have hcross' := congrArg φ hcross
    rw [map_mul, map_mul, map_mul] at hcross'
    have hfrac : φ r_f / φ s_f = φ (C c) * (φ r_η / φ s_η) := by
      field_simp
      linear_combination hcross'
    rw [map_sub, hcg, hfrac]
    ring

/-- **Limited integration over `C(x)` with several parameters.** With Hermite decompositions
`f = g_f′ + r_f / s_f` and `ηᵢ = gᵢ′ + rᵢ / sᵢ`, and constants `cᵢ`: `f - ∑ cᵢ ηᵢ` has an
antiderivative in `C(x)` iff the logarithmic parts cancel, `r_f / s_f = ∑ cᵢ rᵢ / sᵢ` — a linear
condition on the `cᵢ`. -/
theorem limited_integral_iff_multi (hD : ∀ P : C'[X], P′ = derivative P) (g_f : K)
    (r_f s_f : C'[X]) (hsf : Squarefree s_f) (hdf : r_f.degree < s_f.degree)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (g : ι → K) (r s : ι → C'[X]) (c : ι → C')
    (hs : ∀ i ∈ I, Squarefree (s i)) (hdeg : ∀ i ∈ I, (r i).degree < (s i).degree) :
    (∃ y : K, y′ = (g_f′ + φ r_f / φ s_f) -
        ∑ i ∈ I, φ (C (c i)) * ((g i)′ + φ (r i) / φ (s i))) ↔
      φ r_f / φ s_f = ∑ i ∈ I, φ (C (c i)) * (φ (r i) / φ (s i)) := by
  have hc' : ∀ i, (φ (C (c i)))′ = 0 := fun i ↦ by
    rw [deriv_algebraMap, hD, derivative_C, map_zero]
  have hcg : ∀ i, (φ (C (c i)) * g i)′ = φ (C (c i)) * (g i)′ := fun i ↦ by
    rw [Derivation.leibniz, hc']; simp [mul_comm]
  constructor
  · rintro ⟨y, hy⟩
    -- `z = y - g_f + ∑ cᵢ gᵢ` has derivative `r_f / s_f - ∑ cᵢ rᵢ / sᵢ`
    set z : K := y - g_f + ∑ i ∈ I, φ (C (c i)) * g i with hz
    let r' : Option ι → C'[X] := fun o ↦ o.elim r_f fun i ↦ -(C (c i) * r i)
    let s' : Option ι → C'[X] := fun o ↦ o.elim s_f s
    have hz' : z′ = ∑ o ∈ Finset.insertNone I, φ (r' o) / φ (s' o) := by
      rw [Finset.sum_insertNone, hz, map_add, map_sub, hy, map_sum]
      simp only [r', s', Option.elim_none, Option.elim_some, hcg, map_neg, map_mul, neg_div,
        Finset.sum_neg_distrib, mul_add, Finset.sum_add_distrib, mul_div_assoc]
      ring
    have h0 := sum_eq_zero_of_deriv_eq_finset_sum (K := K) hD (Finset.insertNone I) r' s'
      (fun o ho ↦ by
        cases o with
        | none => exact hsf
        | some i => exact hs i (Finset.some_mem_insertNone.mp ho))
      (fun o ho ↦ by
        cases o with
        | none => exact hdf
        | some i =>
          have hi := Finset.some_mem_insertNone.mp ho
          simp only [r', s', Option.elim_some, degree_neg]
          by_cases hci : c i = 0
          · rw [hci, C_0, zero_mul, degree_zero]
            exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr (hs i hi).ne_zero)
          · rw [degree_C_mul hci]
            exact hdeg i hi) z hz'
    rw [Finset.sum_insertNone] at h0
    simp only [r', s', Option.elim_none, Option.elim_some, map_neg, map_mul, neg_div,
      Finset.sum_neg_distrib, mul_div_assoc] at h0
    linear_combination h0
  · intro hrel
    refine ⟨g_f - ∑ i ∈ I, φ (C (c i)) * g i, ?_⟩
    rw [map_sub, map_sum, hrel]
    simp only [hcg, mul_add, Finset.sum_add_distrib]
    ring

end Base

end Differential
