import RischTragerBronstein.Rational.Hermite
import RischTragerBronstein.Liouville.ExponentialPoly
import RischTragerBronstein.Liouville.PoleOrder

/-!
# Hermite reduction in an exponential extension

Let `t` be an exponential monomial over `F` (`t′ = η t`) introducing no new constants, `K = F(t)`.

* `dvd_X_of_irreducible_special`: a special irreducible polynomial (`p ∣ p′`) is an associate of
  `t`: `t ∣ p`.
* `hermite_reduction_exponential`: every `a / d ∈ F(t)` is a derivative plus a fraction with
  denominator `t ^ k * s`, `s` squarefree and prime to `t`:

    `a / d = g′ + b / (t ^ k * s)`.

The factor `t ^ k` cannot be removed by integration by parts (`t` is special); it is the Laurent
("reduced") part of Bronstein's Hermite reduction, handled by Risch differential equations.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [Differential K] [DifferentialAlgebra F[X] K]

/-- In an exponential extension without new constants, a special irreducible is an associate
of `t`. -/
theorem dvd_X_of_irreducible_special (η : F) (hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n)
    {p : F[X]} (hp : Irreducible p) (hsp : p ∣ p′) : X ∣ p := by
  have hconst' : ∀ (P : F[X]) (n : ℕ), implicitDeriv (C η * X) P * X ^ n =
      P * implicitDeriv (C η * X) (X ^ n) → ∃ e : F, P = C e * X ^ n :=
    fun P n hP ↦ hconst P n (by rw [hD, hD, hP])
  have hp0 : p ≠ 0 := hp.ne_zero
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  set q := p * C p.leadingCoeff⁻¹ with hq
  have hqm : q.Monic := monic_mul_leadingCoeff_inv hp0
  have hqirr : Irreducible q := irreducible_mul_leadingCoeff_inv.mpr hp
  have hpq : p = q * C p.leadingCoeff := by
    rw [hq, mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
  by_contra hX
  -- `q ≠ X`, so `q` is normal; but `q ∣ q′` follows from `p ∣ p′`
  have hqX : q ≠ X := fun h ↦ hX ⟨C p.leadingCoeff, h ▸ hpq⟩
  refine not_dvd_deriv_of_monic_ne_X η hconst' hqm hqirr hqX ?_
  have hqp : q ∣ p := ⟨C p.leadingCoeff, hpq⟩
  have h1 : q ∣ p′ := hqp.trans hsp
  have hp' : p′ = implicitDeriv (C η * X) q * C p.leadingCoeff + q * C (p.leadingCoeff)′ := by
    rw [hD]
    conv_lhs => rw [hpq]
    rw [Derivation.leibniz, implicitDeriv_C]
    simp only [smul_eq_mul]
    ring
  rw [hp'] at h1
  have h2 : q ∣ implicitDeriv (C η * X) q * C p.leadingCoeff :=
    (dvd_add_left (dvd_mul_right q _)).mp h1
  exact ((isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlc)).dvd_mul_right).mp h2

/-- **Hermite reduction in an exponential extension.** -/
theorem hermite_reduction_exponential (η : F)
    (hD : ∀ P : F[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : F[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : F, P = C e * X ^ n)
    (hinj : Function.Injective (algebraMap F[X] K)) (a d : F[X]) (hd : d ≠ 0) :
    ∃ (g : K) (b s : F[X]) (k : ℕ), Squarefree s ∧ ¬X ∣ s ∧
      algebraMap F[X] K a / algebraMap F[X] K d =
        g′ + algebraMap F[X] K b / algebraMap F[X] K (X ^ k * s) := by
  obtain ⟨g, b, d', hd'0, hd', hf⟩ := hermite_reduction_general (K := K) hinj d hd a
  obtain ⟨k, s, hXs, rfl⟩ := exists_pow_mul_not_dvd (prime_X (R := F)) hd'0
  have hs0 : s ≠ 0 := right_ne_zero_of_mul hd'0
  refine ⟨g, b, s, k, ?_, hXs, hf⟩
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hs0]
  intro q hq hqq
  have hspecial : q ∣ q′ := hd' q hq (Dvd.dvd.mul_left hqq _)
  have hXq : X ∣ q := dvd_X_of_irreducible_special η hD hconst hq hspecial
  exact hXs (hXq.trans ((dvd_mul_right q q).trans hqq))

end Differential
