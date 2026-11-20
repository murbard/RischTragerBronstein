import RischTragerBronstein.RDE.ExponentialInField
import RischTragerBronstein.Liouville.TwoProperFractions

/-!
# Antiderivatives of a Laurent polynomial plus two proper fractions, in an exponential extension

If `z′ = Λ / t^k + b₁ / s₁ + b₂ / s₂` with `s₁, s₂` squarefree, prime to `t`, all their primes
normal, `deg bᵢ < deg sᵢ`, then `b₁ s₂ + b₂ s₁ = 0` (and `z` is a Laurent polynomial).
-/

open Polynomial

namespace Differential

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'] [Differential C'[X]]
variable [Field K] [Algebra C'[X] K] [IsFractionRing C'[X] K] [Differential K]
variable [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

theorem deriv_eq_laurent_add_two_proper_exp (η : C')
    (hD : ∀ P : C'[X], P′ = implicitDeriv (C η * X) P)
    (hnorm : ∀ p : C'[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′)
    (hη : ∀ r : ℕ, 0 < r → ∀ e : C', e ≠ 0 → e′ - r * η * e ≠ 0)
    (Λ b₁ s₁ b₂ s₂ : C'[X]) (k : ℕ) (hs₁ : Squarefree s₁) (hs₂ : Squarefree s₂)
    (hX₁ : ¬X ∣ s₁) (hX₂ : ¬X ∣ s₂)
    (hdeg₁ : b₁.degree < s₁.degree) (hdeg₂ : b₂.degree < s₂.degree) (z : K)
    (h : z′ = φ Λ / φ X ^ k + φ b₁ / φ s₁ + φ b₂ / φ s₂) :
    b₁ * s₂ + b₂ * s₁ = 0 ∧ ∃ P : C'[X], z = φ P / φ X ^ k := by
  classical
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hs₁0 : s₁ ≠ 0 := hs₁.ne_zero
  have hs₂0 : s₂ ≠ 0 := hs₂.ne_zero
  obtain ⟨u₁, hu₁⟩ := EuclideanDomain.gcd_dvd_left s₁ s₂
  obtain ⟨u₂, hu₂⟩ := EuclideanDomain.gcd_dvd_right s₁ s₂
  set g := EuclideanDomain.gcd s₁ s₂ with hg
  have hg0 : g ≠ 0 := fun h0 ↦ hs₁0 (by rw [hu₁, h0, zero_mul])
  have hu₁0 : u₁ ≠ 0 := fun h0 ↦ hs₁0 (by rw [hu₁, h0, mul_zero])
  have hu₂0 : u₂ ≠ 0 := fun h0 ↦ hs₂0 (by rw [hu₂, h0, mul_zero])
  have hcop : IsCoprime s₁ u₂ := by
    refine isCoprime_of_irreducible_dvd (fun h ↦ hs₁0 h.1) fun p hp hp1 hp2 ↦ ?_
    have hpg : p ∣ g := EuclideanDomain.dvd_gcd hp1 ((hp2.mul_left g).trans (dvd_of_eq hu₂.symm))
    have : p * p ∣ s₂ := (mul_dvd_mul hpg hp2).trans (dvd_of_eq hu₂.symm)
    exact hp.not_isUnit (hs₂ p this)
  have hsq₂' : Squarefree u₂ := hs₂.squarefree_of_dvd ⟨g, hu₂.trans (mul_comm _ _)⟩
  have hsq : Squarefree (s₁ * u₂) := (squarefree_mul_iff).mpr ⟨hcop.isRelPrime, hs₁, hsq₂'⟩
  have hXs : ¬X ∣ s₁ * u₂ := fun hd ↦ (prime_X.dvd_or_dvd hd).elim hX₁ fun h' ↦
    hX₂ ((h'.mul_left g).trans (dvd_of_eq hu₂.symm))
  have hφ : ∀ {P : C'[X]}, P ≠ 0 → φ P ≠ 0 := fun hP ↦ (map_ne_zero_iff _ hinj).mpr hP
  have hform : z′ = φ Λ / φ X ^ k + φ (b₁ * u₂ + b₂ * u₁) / φ (s₁ * u₂) := by
    rw [h, map_add, map_mul, map_mul, map_mul]
    have e₁ : φ s₁ = φ g * φ u₁ := by rw [← map_mul, ← hu₁]
    have e₂ : φ s₂ = φ g * φ u₂ := by rw [← map_mul, ← hu₂]
    rw [e₂, e₁]
    have := hφ hg0; have := hφ hu₁0; have := hφ hu₂0
    field_simp
    ring
  have hdeg : (b₁ * u₂ + b₂ * u₁).degree < (s₁ * u₂).degree := by
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · rw [degree_mul, degree_mul]
      exact WithBot.add_lt_add_right (by rw [Ne, degree_eq_bot]; exact hu₂0) hdeg₁
    · have e : s₁ * u₂ = s₂ * u₁ := by linear_combination u₂ * hu₁ - u₁ * hu₂
      rw [e, degree_mul, degree_mul]
      exact WithBot.add_lt_add_right (by rw [Ne, degree_eq_bot]; exact hu₁0) hdeg₂
  obtain ⟨hb, hP⟩ := deriv_eq_laurent_add_proper_exp η hD hnorm hη Λ _ _ k hsq hXs hdeg z hform
  refine ⟨?_, hP⟩
  have : b₁ * s₂ + b₂ * s₁ = g * (b₁ * u₂ + b₂ * u₁) := by
    linear_combination b₁ * hu₂ + b₂ * hu₁
  rw [this, hb, mul_zero]

end Differential
