import RischTragerBronstein.Computable.RationalDecide
import Mathlib.FieldTheory.Perfect

/-!
# Towards `∫ f(x) log x dx`: the limited-integration criterion over `C(x)`

* `hermiteCheck_sound_map`: the identity certified by `hermiteCheck` holds in **any** fraction field
  `K` of `S[X]` with `d/dx`, for any field extension `ι : R → S` of the coefficient field. (The
  certificate is a polynomial identity, so it survives base change; this is what lets a certificate
  computed over `R` be used over the enlarged constant field produced by the strong Liouville
  theorem.)
* `limited_log_criterion`: if `f = g′ + r / s` with `s` squarefree, `deg r < deg s`, and
  `p₁′ + 2 c / x = f` for some constant `c` and `p₁ ∈ K`, then either `x ∣ s` and
  `r = 2 c (s / x)`, or `r = 0`.

By `exists_limited_integral_of_liouville`, the hypothesis of the second statement is exactly what
elementary integrability of `f log x` forces; its conclusion is decidable from the Hermite data.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R S K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K] [Algebra S[X] K] [IsFractionRing S[X] K]
variable [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

theorem hermiteCheck_sound_map (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (A D : CPoly R) (r : HermiteResult R) (hc : hermiteCheck A D r = true) :
    φ ((toPoly A).map ι) / φ ((toPoly D).map ι) =
      (φ ((toPoly r.gn).map ι) / φ ((toPoly r.gd).map ι))′ +
        φ ((toPoly r.b).map ι) / φ ((toPoly r.s).map ι) ∧
    Squarefree ((toPoly r.s).map ι) := by
  simp only [hermiteCheck, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
    isZero_iff, beq_iff] at hc
  obtain ⟨⟨⟨⟨hD0, hgd⟩, hs⟩, hid⟩, hsq⟩ := hc
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hmap0 : ∀ {P : R[X]}, P ≠ 0 → φ (P.map ι) ≠ 0 := fun hP ↦
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hP)
  refine ⟨?_, ?_⟩
  · have hφD := hmap0 hD0
    have hφgd := hmap0 hgd
    have hφs := hmap0 hs
    rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD, hD]
    simp only [smul_eq_mul, derivative_map]
    have hid' := congrArg (fun P : R[X] ↦ φ (P.map ι)) hid
    simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, Polynomial.map_mul,
      Polynomial.map_add, Polynomial.map_sub, map_mul, map_add, map_sub] at hid'
    field_simp
    linear_combination hid'
  · have hsep : (toPoly r.s).Separable :=
      PerfectField.separable_iff_squarefree.mpr (squarefreeCheck_sound hsq)
    exact hsep.map.squarefree

lemma degree_C_mul_le' (a : S) (q : S[X]) : (C a * q).degree ≤ q.degree := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [degree_C_mul ha]

lemma degree_lt_degree_X_mul {q : S[X]} (hq : q ≠ 0) : q.degree < (X * q).degree := by
  rw [degree_mul, degree_X, degree_eq_natDegree hq, ← Nat.cast_one, ← Nat.cast_add]
  exact_mod_cast (by omega : q.natDegree < 1 + q.natDegree)

theorem limited_log_criterion (hD : ∀ P : S[X], P′ = derivative P) (g : K) (r s : S[X])
    (hs : Squarefree s) (hdeg : r.degree < s.degree) (c : S) (p₁ : K)
    (h : p₁′ + 2 * φ (C c) / φ X = g′ + φ r / φ s) :
    (∃ s' : S[X], s = X * s' ∧ r = C (2 * c) * s') ∨ r = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hs0 : s ≠ 0 := hs.ne_zero
  have hφs : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0
  have hφX : φ X ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hder : (p₁ - g)′ = φ r / φ s - 2 * φ (C c) / φ X := by
    rw [deriv_sub']; linear_combination h
  by_cases hXs : (X : S[X]) ∣ s
  · left
    obtain ⟨s', rfl⟩ := hXs
    refine ⟨s', rfl, ?_⟩
    have hs'0 : s' ≠ 0 := right_ne_zero_of_mul hs0
    have hφs' : φ s' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs'0
    have hdeg' : (r - C (2 * c) * s').degree < (X * s').degree := by
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt hdeg ?_)
      exact lt_of_le_of_lt (degree_C_mul_le' _ _) (degree_lt_degree_X_mul hs'0)
    have := eq_zero_of_deriv_eq_proper_fraction hD (r - C (2 * c) * s') (X * s') hs hdeg' (p₁ - g)
      (by
        rw [hder]
        simp only [map_sub, map_mul, C_mul, C_ofNat, map_ofNat]
        field_simp)
    exact sub_eq_zero.mp this
  · right
    have hrel : IsRelPrime s X :=
      (Irreducible.isRelPrime_iff_not_dvd irreducible_X).mpr hXs |>.symm
    have hsq : Squarefree (s * X) :=
      (squarefree_mul_iff).mpr ⟨hrel, hs, irreducible_X.squarefree⟩
    have hdeg' : (r * X - C (2 * c) * s).degree < (s * X).degree := by
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · rw [degree_mul, degree_mul, degree_X]
        exact WithBot.add_lt_add_right (by simp) hdeg
      · refine lt_of_le_of_lt (degree_C_mul_le' _ _) ?_
        rw [mul_comm]
        exact degree_lt_degree_X_mul hs0
    have h0 := eq_zero_of_deriv_eq_proper_fraction hD (r * X - C (2 * c) * s) (s * X) hsq hdeg'
      (p₁ - g) (by
        rw [hder]
        simp only [map_sub, map_mul, C_mul, C_ofNat, map_ofNat]
        field_simp)
    have hXdvd : (X : S[X]) ∣ C (2 * c) * s := ⟨r, by linear_combination -h0⟩
    have hc0 : C (2 * c) = (0 : S[X]) := by
      by_contra hne
      rcases (prime_X (R := S)).dvd_or_dvd hXdvd with h1 | h1
      · exact not_isUnit_X (isUnit_of_dvd_unit h1
          (isUnit_C.mpr (isUnit_iff_ne_zero.mpr fun h2 ↦ hne (by rw [h2, C_0]))))
      · exact hXs h1
    rw [hc0, zero_mul, sub_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_right X_ne_zero

/-- The certified decomposition `f = (gn / gd + Q)′ + r / s`, in any model and over any extension of
the coefficient field. -/
theorem rationalCheck_sound_map (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (A D : CPoly R) (I : RationalIntegral R) (hc : rationalCheck A D I = true) :
    φ ((toPoly A).map ι) / φ ((toPoly D).map ι) =
      (φ ((toPoly I.gn).map ι) / φ ((toPoly I.gd).map ι) + φ ((toPoly I.Q).map ι))′ +
        φ ((toPoly I.r).map ι) / φ ((toPoly I.s).map ι) ∧
    Squarefree ((toPoly I.s).map ι) ∧
    ((toPoly I.r).map ι).degree < ((toPoly I.s).map ι).degree := by
  rw [rationalCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hH, hlen⟩ := hc
  obtain ⟨hid, hsq⟩ := hermiteCheck_sound_map (K := K) ι hD A D _ hH
  have hdeg := degree_lt_of_trim_length_lt hlen
  refine ⟨?_, hsq, by rwa [degree_map, degree_map]⟩
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hφs : φ ((toPoly I.s).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
  rw [hid, map_add, deriv_algebraMap, hD]
  simp only [toPoly_add, toPoly_mul, toPoly_deriv, Polynomial.map_add, Polynomial.map_mul,
    derivative_map, map_add, map_mul]
  field_simp
  ring

/-- The decidable criterion for `∫ f log x`, in terms of the Hermite remainder `r / s` of `f`. -/
def LogCrit (r s : R[X]) : Prop := (∃ (s' : R[X]) (c : R), s = X * s' ∧ r = C c * s') ∨ r = 0

/-- The criterion descends from an extension of the coefficient field. -/
theorem logCrit_of_map (ι : R →+* S) {r s : R[X]} {c : S}
    (h : (∃ s'' : S[X], s.map ι = X * s'' ∧ r.map ι = C (2 * c) * s'') ∨ r.map ι = 0) :
    LogCrit r s := by
  rcases h with ⟨s'', hs, hr⟩ | h0
  · by_cases hr0 : r = 0
    · exact Or.inr hr0
    left
    -- `X ∣ s` over `R`
    have hs0 : s.coeff 0 = 0 := by
      have := congrArg (fun P : S[X] ↦ P.coeff 0) hs
      simp only [coeff_map, mul_coeff_zero, coeff_X_zero, zero_mul] at this
      exact (map_eq_zero ι).mp this
    obtain ⟨s', rfl⟩ : X ∣ s := X_dvd_iff.mpr hs0
    have hs'' : s'' = s'.map ι := by
      have : X * s'' = X * s'.map ι := by rw [← hs, Polynomial.map_mul, map_X]
      exact mul_left_cancel₀ X_ne_zero this
    have hs'0 : s' ≠ 0 := fun h0 ↦ hr0 (by
      have : r.map ι = 0 := by rw [hr, hs'', h0, Polynomial.map_zero, mul_zero]
      exact (Polynomial.map_eq_zero_iff ι.injective).mp this)
    refine ⟨s', r.leadingCoeff / s'.leadingCoeff, rfl, ?_⟩
    have hlc : ι r.leadingCoeff = 2 * c * ι s'.leadingCoeff := by
      have := congrArg leadingCoeff hr
      rwa [leadingCoeff_map, leadingCoeff_mul, leadingCoeff_C, hs'', leadingCoeff_map] at this
    have hι0 : ι s'.leadingCoeff ≠ 0 := (map_ne_zero ι).mpr (leadingCoeff_ne_zero.mpr hs'0)
    apply Polynomial.map_injective ι ι.injective
    rw [hr, hs'', Polynomial.map_mul, map_C, map_div₀, hlc]
    congr 2
    field_simp
  · exact Or.inr ((Polynomial.map_eq_zero_iff ι.injective).mp h0)

end CPoly
