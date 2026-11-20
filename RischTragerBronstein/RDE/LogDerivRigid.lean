import RischTragerBronstein.Liouville.ProperFraction
import RischTragerBronstein.Liouville.PoleOrder
import RischTragerBronstein.Liouville.MonicPrimes
import RischTragerBronstein.Rational.RationalPart

/-!
# A derivative plus a proper simple-pole fraction which is a logarithmic derivative

In `K = C(x)` (`x′ = 1`): if `W′ + b / s = e′ / e` with `s` squarefree, `deg b < deg s` and
`e ≠ 0`, then `W′ = 0`. (`W` has at most simple poles in its derivative, hence is a polynomial,
and a polynomial derivative equal to a proper fraction vanishes.)
-/

open Polynomial

namespace Differential

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'[X]] [Field K] [Algebra C'[X] K]
variable [IsFractionRing C'[X] K] [Differential K] [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

/-- General form: `b / s` proper, with at most simple poles at every monic irreducible. -/
theorem deriv_eq_zero_of_add_proper_eq_logDeriv' (hD : ∀ P : C'[X], P′ = derivative P)
    (b s : C'[X]) (hs0 : s ≠ 0)
    (hreg : ∀ (p : C'[X]) (hp : Irreducible p), φ b / φ s * φ p ∈ regularAt K p hp.prime)
    (hdeg : b.degree < s.degree) (W e : K) (he : e ≠ 0)
    (h : W′ + φ b / φ s = logDeriv e) : W′ = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hφs : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0
  have hnorm : ∀ p : C'[X], Irreducible p → ¬p ∣ p′ := fun p hp hdvd ↦ by
    rw [hD] at hdvd
    have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
    have hne : derivative p ≠ 0 := fun h0' ↦ hpos (derivative_eq_zero.mp h0')
    exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
  -- `W` is a polynomial
  obtain ⟨P, hP⟩ : ∃ P : C'[X], -W = φ P := by
    refine exists_polynomial_of_regularAt (-W) fun p _ hp ↦ ?_
    refine mem_regularAt_of_liouville_eq' hp.prime (hnorm p hp)
      (not_dvd_natCast_polynomial hp.prime) ({()} : Finset Unit) (fun _ ↦ 1) (fun _ ↦ e) (-W)
      (φ b / φ s) (fun _ _ ↦ one_mem _) (fun _ _ ↦ he) ?_ ?_
    · rw [mul_comm]; exact hreg p hp
    · rw [Finset.sum_singleton, one_mul, map_neg, ← h]; ring
  have hW : W = φ (-P) := by rw [map_neg, ← hP, neg_neg]
  -- a polynomial derivative equal to a proper fraction vanishes
  obtain ⟨a, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := C'[X]) e
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have ha0 : a ≠ 0 := by rintro rfl; exact he (by rw [← hpq, map_zero, zero_div])
  have hφa : φ a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
  have hφq : φ q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq0
  set P' := derivative (-P) with hP'
  have hW' : W′ = φ P' := by rw [hW, deriv_algebraMap, hD]
  rw [hW', ← hpq, logDeriv, Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD,
    hD] at h
  simp only [smul_eq_mul] at h
  have hpoly : a * q * (P' * s + b) = (derivative a * q - a * derivative q) * s := by
    apply hinj
    simp only [map_mul, map_add, map_sub]
    field_simp at h
    linear_combination h
  rw [hW']
  by_contra hne
  have hP'0 : P' ≠ 0 := fun h0 ↦ hne (by rw [h0, map_zero])
  -- degrees
  have hdegL : degree (P' * s + b) = degree (P' * s) := by
    refine degree_add_eq_left_of_degree_lt (lt_of_lt_of_le hdeg ?_)
    rw [degree_mul]; exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hP'0)
  have hL : degree (a * q) + degree s ≤ degree (a * q * (P' * s + b)) := by
    rw [degree_mul (p := a * q), hdegL, degree_mul (p := P')]
    exact add_le_add_right (le_add_of_nonneg_left (zero_le_degree_iff.mpr hP'0)) _
  have hR : degree ((derivative a * q - a * derivative q) * s) < degree (a * q) + degree s := by
    rw [degree_mul (p := _ - _)]
    refine WithBot.add_lt_add_right (by rw [degree_eq_natDegree hs0]; exact WithBot.coe_ne_bot) ?_
    rw [degree_mul]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · rw [degree_mul]
      by_cases hda : derivative a = 0
      · rw [hda, degree_zero, WithBot.bot_add]
        exact WithBot.bot_lt_iff_ne_bot.mpr (by
          rw [Ne, WithBot.add_eq_bot, not_or]
          exact ⟨fun h ↦ ha0 (degree_eq_bot.mp h), fun h ↦ hq0 (degree_eq_bot.mp h)⟩)
      · refine WithBot.add_lt_add_right (fun h ↦ hq0 (degree_eq_bot.mp h)) ?_
        exact degree_derivative_lt ha0
    · rw [degree_mul]
      by_cases hdq : derivative q = 0
      · rw [hdq, degree_zero, WithBot.add_bot]
        exact WithBot.bot_lt_iff_ne_bot.mpr (by
          rw [Ne, WithBot.add_eq_bot, not_or]
          exact ⟨fun h ↦ ha0 (degree_eq_bot.mp h), fun h ↦ hq0 (degree_eq_bot.mp h)⟩)
      · refine WithBot.add_lt_add_left (fun h ↦ ha0 (degree_eq_bot.mp h)) ?_
        exact degree_derivative_lt hq0
  rw [← hpoly] at hR
  exact absurd (lt_of_le_of_lt hL hR) (lt_irrefl _)

theorem deriv_eq_zero_of_add_proper_eq_logDeriv (hD : ∀ P : C'[X], P′ = derivative P)
    (b s : C'[X]) (hs : Squarefree s) (hdeg : b.degree < s.degree) (W e : K) (he : e ≠ 0)
    (h : W′ + φ b / φ s = logDeriv e) : W′ = 0 :=
  deriv_eq_zero_of_add_proper_eq_logDeriv' hD b s hs.ne_zero
    (fun _ hp ↦ simple_pole_mem_regularAt hs hp) hdeg W e he h

/-- Two simple-pole proper fractions. -/
theorem deriv_eq_zero_of_add_proper₂_eq_logDeriv (hD : ∀ P : C'[X], P′ = derivative P)
    (b₁ s₁ b₂ s₂ : C'[X]) (hs₁ : Squarefree s₁) (hs₂ : Squarefree s₂)
    (hdeg₁ : b₁.degree < s₁.degree) (hdeg₂ : b₂.degree < s₂.degree) (W e : K) (he : e ≠ 0)
    (h : W′ + φ b₁ / φ s₁ + φ b₂ / φ s₂ = logDeriv e) : W′ = 0 := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hs₁0 := hs₁.ne_zero
  have hs₂0 := hs₂.ne_zero
  have hφ₁ : φ s₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs₁0
  have hφ₂ : φ s₂ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs₂0
  have hsum : φ b₁ / φ s₁ + φ b₂ / φ s₂ = φ (b₁ * s₂ + b₂ * s₁) / φ (s₁ * s₂) := by
    rw [map_add, map_mul, map_mul, map_mul]; field_simp
  refine deriv_eq_zero_of_add_proper_eq_logDeriv' hD (b₁ * s₂ + b₂ * s₁) (s₁ * s₂)
    (mul_ne_zero hs₁0 hs₂0) (fun p hp ↦ ?_) ?_ W e he (by rw [← hsum, ← add_assoc]; exact h)
  · rw [← hsum, add_mul]
    exact add_mem (simple_pole_mem_regularAt hs₁ hp) (simple_pole_mem_regularAt hs₂ hp)
  · rw [degree_mul]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · rw [degree_mul]
      exact WithBot.add_lt_add_right (fun h ↦ hs₂0 (degree_eq_bot.mp h)) hdeg₁
    · rw [degree_mul, add_comm (degree s₁)]
      exact WithBot.add_lt_add_right (fun h ↦ hs₁0 (degree_eq_bot.mp h)) hdeg₂

end Differential
