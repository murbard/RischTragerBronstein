import RischTragerBronstein.Liouville.ProperFraction

/-!
# Antiderivatives of a polynomial plus two proper fractions

If `z′ = A + b₁ / s₁ + b₂ / s₂` in `F(t)` with `s₁, s₂` squarefree (all primes normal) and
`deg bᵢ < deg sᵢ`, then the fractional part vanishes: `b₁ s₂ + b₂ s₁ = 0`.

This is the cancellation condition of limited integration `G - c W = z′` when the parameter
function `W` has simple poles: `r_G s_W = c r_W s_G`.
-/

open Polynomial

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F[X]] [Field K] [Algebra F[X] K]
variable [IsFractionRing F[X] K] [Differential K] [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

theorem deriv_eq_poly_add_two_proper (hnorm : ∀ p : F[X], Irreducible p → ¬p ∣ p′)
    (A b₁ s₁ b₂ s₂ : F[X]) (hs₁ : Squarefree s₁) (hs₂ : Squarefree s₂)
    (hdeg₁ : b₁.degree < s₁.degree) (hdeg₂ : b₂.degree < s₂.degree) (z : K)
    (h : z′ = φ A + φ b₁ / φ s₁ + φ b₂ / φ s₂) :
    b₁ * s₂ + b₂ * s₁ = 0 ∧ ∃ P : F[X], z = φ P ∧ P′ = A := by
  classical
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hs₁0 : s₁ ≠ 0 := hs₁.ne_zero
  have hs₂0 : s₂ ≠ 0 := hs₂.ne_zero
  -- `s₁ = g u₁`, `s₂ = g u₂` with `u₂` coprime to `s₁`
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
  have hφ : ∀ {P : F[X]}, P ≠ 0 → φ P ≠ 0 := fun hP ↦ (map_ne_zero_iff _ hinj).mpr hP
  have hform : z′ = φ A + φ (b₁ * u₂ + b₂ * u₁) / φ (s₁ * u₂) := by
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
  obtain ⟨hb, hP⟩ := deriv_eq_poly_add_proper hnorm A _ _ hsq hdeg z hform
  refine ⟨?_, hP⟩
  have : b₁ * s₂ + b₂ * s₁ = g * (b₁ * u₂ + b₂ * u₁) := by
    linear_combination b₁ * hu₂ + b₂ * hu₁
  rw [this, hb, mul_zero]

end Differential
