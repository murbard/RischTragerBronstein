import RischTragerBronstein.RDE.ExponentialDenominator
import RischTragerBronstein.Liouville.ProperFraction
import RischTragerBronstein.Liouville.ExponentialCore

/-!
# Antiderivatives inside an exponential extension

`K = F(t)`, `t′ = η t`. If `z′ = Λ / t^k + b / s` with `s` squarefree, prime to `t`, all its
primes normal, and `deg b < deg s`, then `b = 0` and `z = P / t^k` is a Laurent polynomial —
integration inside `F(t)` of a Hermite-reduced element is a Laurent-polynomial problem.
-/

open Polynomial

namespace Differential

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'] [Differential C'[X]]
variable [Field K] [Algebra C'[X] K] [IsFractionRing C'[X] K] [Differential K]
variable [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

theorem deriv_eq_laurent_add_proper_exp (η : C') (hD : ∀ P : C'[X], P′ = implicitDeriv (C η * X) P)
    (hnorm : ∀ p : C'[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′)
    (hη : ∀ r : ℕ, 0 < r → ∀ e : C', e ≠ 0 → e′ - r * η * e ≠ 0)
    (Λ b s : C'[X]) (k : ℕ) (hs : Squarefree s) (hXs : ¬X ∣ s) (hdeg : b.degree < s.degree)
    (z : K) (h : z′ = φ Λ / φ X ^ k + φ b / φ s) :
    b = 0 ∧ ∃ P : C'[X], z = φ P / φ X ^ k := by
  classical
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  have hs0 : s ≠ 0 := hs.ne_zero
  have hφs : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0
  have hX0 : φ X ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hXk : φ X ^ k ≠ 0 := pow_ne_zero _ hX0
  -- `z t^k` is regular everywhere
  have hzreg : ∀ (p : C'[X]) (_ : p.Monic) (hp : Irreducible p),
      z * φ X ^ k ∈ regularAt K p hp.prime := by
    intro p hm hp
    by_cases hpX : p = X
    · subst hpX
      have hrde : z′ + φ (C (0 : C')) * z = φ (Λ * s + b * X ^ k) / (φ X ^ k * φ s) := by
        rw [h, C_0, map_zero, zero_mul, add_zero, map_add, map_mul, map_mul, map_pow]
        field_simp
      exact rde_regularAt_X η hD 0 (fun r hr e he ↦ by
        have := hη r hr e he
        rwa [zero_sub, neg_mul, ← sub_eq_add_neg]) _ _ k hXs z hrde
    · refine mul_mem ?_ (by rw [← map_pow]; exact algebraMap_mem_regularAt _ _)
      refine mem_regularAt_of_deriv_simple_pole hp.prime (hnorm p hm hp hpX)
        (not_dvd_natCast_polynomial hp.prime) ?_
      rw [h, add_mul]
      refine add_mem ?_ (simple_pole_mem_regularAt hs hp)
      have : φ Λ / φ X ^ k * φ p = φ Λ * φ p / φ X ^ k := by ring
      rw [this]
      refine ⟨Λ * p, X ^ k, ?_, by rw [map_mul, map_pow]; field_simp⟩
      intro hdvd
      have := (hp.prime.dvd_of_dvd_pow hdvd)
      exact hpX (eq_of_monic_of_associated hm monic_X
        (associated_of_dvd_dvd this (hp.dvd_symm irreducible_X this)))
  obtain ⟨P, hP⟩ := exists_polynomial_of_regularAt _ hzreg
  have hz : z = φ P / φ X ^ k := by rw [← hP]; field_simp
  refine ⟨?_, P, hz⟩
  -- the proper part must vanish
  have hXk' : (φ X ^ k)′ = φ (C (k * η)) * φ X ^ k := by
    rw [← map_pow, deriv_algebraMap, hD, deriv_X_pow, map_mul, map_pow]
  have hpoly : (P′ - C (k * η) * P - Λ) * s = b * X ^ k := by
    apply hinj
    have h2 := h
    rw [hz, Derivation.leibniz_div, hXk', deriv_algebraMap] at h2
    simp only [smul_eq_mul] at h2
    simp only [map_mul, map_sub, map_pow]
    field_simp at h2
    field_simp
    have hCm : φ (C (k * η)) = φ (C (k : C')) * φ (C η) := by rw [C_mul, map_mul]
    rw [hCm] at h2
    linear_combination h2
  have hdvd : s ∣ b * X ^ k := ⟨P′ - C (k * η) * P - Λ, by rw [← hpoly]; ring⟩
  have hcop : IsCoprime s (X ^ k) := by
    refine IsCoprime.pow_right ?_
    refine isCoprime_of_irreducible_dvd (fun h ↦ hs0 h.1) fun p hp h1 h2 ↦ ?_
    have := hp.dvd_symm irreducible_X h2
    exact hXs (this.trans h1)
  have hsb : s ∣ b := hcop.dvd_of_dvd_mul_right hdvd
  by_contra hb0
  have := Polynomial.degree_le_of_dvd hsb hb0
  exact absurd hdeg (not_lt.mpr this)

end Differential
