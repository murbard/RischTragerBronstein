import RischTragerBronstein.Rational.SquarefreePart
import RischTragerBronstein.Rational.HermiteStep
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# Structural facts for Hermite reduction, for an arbitrary derivation of `F[t]`

`Rational/SquarefreePart.lean` proves the facts behind Mack's Hermite loop for `d/dx`. In a monomial
extension the loop uses the **tower derivation** `D` of `F[t]` (`D t = w`). Here the same facts are
proved for any derivation `′` on `F[t]`:

* `deriv_pow_succ_mul`: `(p ^ (k + 1) * c)′ = p ^ k * w`, and `p ∤ w` when `p` is a **normal**
  irreducible with `p ∤ c` (characteristic zero);
* `dvd_mul_deriv` (F1): if every irreducible factor of `M` divides `S`, then `M ∣ S * M′`
  — for every derivation, no normality needed;
* `isCoprime_of_mul_deriv_eq` (F2): if moreover `S` is squarefree, the irreducible factors of `M`
  are normal, and `S * M′ = M * T`, then `T` is coprime to `M`.
-/

open Polynomial

namespace Differential

variable {F : Type*} [Field F] [Differential F[X]]

/-- `(p ^ (k + 1) * c)′ = p ^ k * ((k + 1) p′ c + p c′)`. -/
lemma deriv_pow_succ_mul_eq (p c : F[X]) (k : ℕ) :
    (p ^ (k + 1) * c)′ = p ^ k * (((k + 1 : ℕ) : F[X]) * p′ * c + p * c′) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  rw [pow_succ]
  ring

/-- For a normal irreducible `p ∤ c`, the multiplicity drops by exactly one. -/
theorem deriv_pow_succ_mul [CharZero F] {p c : F[X]} (hp : Irreducible p) (hnorm : ¬p ∣ p′)
    (hpc : ¬p ∣ c) (k : ℕ) :
    ∃ w : F[X], (p ^ (k + 1) * c)′ = p ^ k * w ∧ ¬p ∣ w := by
  refine ⟨_, deriv_pow_succ_mul_eq p c k, fun hdvd ↦ ?_⟩
  have h1 : p ∣ ((k + 1 : ℕ) : F[X]) * p′ * c := by
    have := dvd_sub hdvd (dvd_mul_right p c′)
    simpa using this
  have hunit : IsUnit (((k + 1 : ℕ) : F[X])) := by
    rw [← C_eq_natCast, isUnit_C, isUnit_iff_ne_zero]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  rcases hp.prime.dvd_or_dvd h1 with h2 | h2
  · rcases hp.prime.dvd_or_dvd h2 with h3 | h3
    · exact hp.not_isUnit (isUnit_of_dvd_unit h3 hunit)
    · exact hnorm h3
  · exact hpc h2

/-- (F1) For **any** derivation: if every irreducible factor of `M` divides `S`, then
`M ∣ S * M′`. -/
theorem dvd_mul_deriv {S : F[X]} (M : F[X])
    (hprimes : ∀ p : F[X], Irreducible p → p ∣ M → p ∣ S) : M ∣ S * M′ := by
  induction M using WfDvdMonoid.induction_on_irreducible with
  | zero => simp
  | unit u hu => exact hu.dvd
  | mul a p ha0 hp ih =>
    have hpS : p ∣ S := hprimes p hp (dvd_mul_right p a)
    have ih' : a ∣ S * a′ := ih fun q hq hqa ↦ hprimes q hq (Dvd.dvd.mul_left hqa p)
    obtain ⟨S₁, hS₁⟩ := hpS
    obtain ⟨b, hb⟩ := ih'
    refine ⟨S₁ * p′ + b, ?_⟩
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    have : S * (p * a′ + a * p′) = p * (S * a′) + S * a * p′ := by ring
    rw [this, hb]
    linear_combination (a * p′) * hS₁

/-- (F2) If `S` is squarefree, the irreducible factors of `M ≠ 0` divide `S` and are normal, and
`S * M′ = M * T`, then `T` is coprime to `M`. -/
theorem isCoprime_of_mul_deriv_eq [CharZero F] {S M T : F[X]} (hS : Squarefree S) (hM0 : M ≠ 0)
    (hprimes : ∀ p : F[X], Irreducible p → p ∣ M → p ∣ S)
    (hnormal : ∀ p : F[X], Irreducible p → p ∣ M → ¬p ∣ p′)
    (hT : S * M′ = M * T) : IsCoprime T M := by
  refine isCoprime_of_irreducible_dvd (fun h ↦ hM0 h.2) fun p hp hpT hpM ↦ ?_
  have hfin : FiniteMultiplicity p M := FiniteMultiplicity.of_not_isUnit hp.not_isUnit hM0
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  obtain ⟨k, hk⟩ : ∃ k, multiplicity p M = k + 1 :=
    ⟨multiplicity p M - 1, by
      have := (multiplicity_ne_zero hfin).mpr hpM
      omega⟩
  rw [hk] at hc
  obtain ⟨w, hw, hpw⟩ := deriv_pow_succ_mul hp (hnormal p hp hpM) hpc k
  obtain ⟨S₁, hS₁⟩ := hprimes p hp hpM
  have hpS₁ : ¬p ∣ S₁ := fun ⟨b, hb⟩ ↦ hp.not_isUnit (hS p ⟨b, by rw [hS₁, hb]; ring⟩)
  have hcancel : S₁ * w = c * T := by
    have : p ^ (k + 1) * (S₁ * w) = p ^ (k + 1) * (c * T) := by
      have h1 : S * M′ = p ^ (k + 1) * (S₁ * w) := by
        rw [hS₁]; conv_lhs => rw [hc, hw]
        rw [pow_succ]; ring
      rw [← h1, hT]; conv_lhs => rw [hc]
      ring
    exact mul_left_cancel₀ (pow_ne_zero _ hp.ne_zero) this
  have : p ∣ S₁ * w := hcancel ▸ Dvd.dvd.mul_left hpT c
  rcases hp.prime.dvd_or_dvd this with h1 | h1
  · exact hpS₁ h1
  · exact hpw h1

end Differential
