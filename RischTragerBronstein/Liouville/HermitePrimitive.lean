import RischTragerBronstein.Rational.Hermite
import RischTragerBronstein.Liouville.PrimitivePoly

/-!
# Hermite reduction in a primitive (logarithmic) extension

Let `t` be a primitive monomial over `F` (`t′ = η ∈ F`) introducing no new constants, and `K = F(t)`.
Then every irreducible polynomial of `F[t]` is normal, so `hermite_reduction_of_normal` applies:

**Theorem** (`hermite_reduction_primitive`). Every `a / d ∈ F(t)` is a derivative plus a fraction
with squarefree denominator: `a / d = g′ + b / s`.

This is the first step of the integration algorithm for an arbitrary element of a logarithmic
extension (Bronstein, §5.3): it reduces the problem to simple poles, where the residue criterion
decides.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [Differential K] [DifferentialAlgebra F[X] K]

/-- In a primitive extension without new constants, **every** irreducible polynomial is normal. -/
theorem not_dvd_deriv_of_irreducible_primitive (η : F)
    (hD : ∀ P : F[X], P′ = implicitDeriv (C η) P)
    (hconst : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e) {p : F[X]} (hp : Irreducible p) :
    ¬p ∣ p′ := by
  have hconst' : ∀ P : F[X], implicitDeriv (C η) P = 0 → ∃ e : F, P = C e :=
    fun P hP ↦ hconst P (by rw [hD, hP])
  have hp0 : p ≠ 0 := hp.ne_zero
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  -- the monic associate `q = p / lc`
  set q := p * C p.leadingCoeff⁻¹ with hq
  have hqm : q.Monic := monic_mul_leadingCoeff_inv hp0
  have hqdeg : 0 < q.natDegree := by
    rw [hq, natDegree_mul_C (inv_ne_zero hlc)]; exact hp.natDegree_pos
  have hpq : p = q * C p.leadingCoeff := by
    rw [hq, mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
  intro hdvd
  refine not_dvd_deriv_of_monic η hconst' hqm hqdeg ?_
  -- `q ∣ p ∣ p′ = q′ lc + q lc′`, hence `q ∣ q′ lc`, hence `q ∣ q′`
  have hqp : q ∣ p := ⟨C p.leadingCoeff, hpq⟩
  have h1 : q ∣ p′ := hqp.trans hdvd
  have hp' : p′ = implicitDeriv (C η) q * C p.leadingCoeff + q * C (p.leadingCoeff)′ := by
    rw [hD]
    conv_lhs => rw [hpq]
    rw [Derivation.leibniz, implicitDeriv_C]
    simp only [smul_eq_mul]
    ring
  rw [hp'] at h1
  have h2 : q ∣ implicitDeriv (C η) q * C p.leadingCoeff :=
    (dvd_add_left (dvd_mul_right q _)).mp h1
  have hunit : IsUnit (C p.leadingCoeff) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlc)
  exact (hunit.dvd_mul_right).mp h2

/-- **Hermite reduction in a primitive extension.** -/
theorem hermite_reduction_primitive (η : F) (hD : ∀ P : F[X], P′ = implicitDeriv (C η) P)
    (hconst : ∀ P : F[X], P′ = 0 → ∃ e : F, P = C e)
    (hinj : Function.Injective (algebraMap F[X] K)) (a d : F[X]) (hd : d ≠ 0) :
    ∃ (g : K) (b s : F[X]), Squarefree s ∧
      algebraMap F[X] K a / algebraMap F[X] K d = g′ + algebraMap F[X] K b / algebraMap F[X] K s :=
  hermite_reduction_of_normal hinj
    (fun _ hp ↦ not_dvd_deriv_of_irreducible_primitive η hD hconst hp) d hd a

end Differential
