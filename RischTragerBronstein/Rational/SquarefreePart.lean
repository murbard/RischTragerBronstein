import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The squarefree part `D / gcd (D, D′)`

`squarefree_of_gcd_derivative`: let `D ≠ 0` be a polynomial over a field, `G` a greatest common
divisor of `D` and `D′` (in the sense: `G ∣ D`, `G ∣ D′`, and every common divisor divides `G`), and
`D = G * Q`. Then `Q` is squarefree.

This is the fact underlying squarefree factorisation and Hermite reduction: the denominator
`D* = D / gcd (D, D′)` of the Hermite remainder is squarefree. It is stated with an abstract gcd so
that it applies verbatim to the executable `CPoly.egcd` (`egcd_dvd`, `dvd_egcd`).
-/

open Polynomial

namespace Differential

variable {F : Type*} [Field F]

theorem squarefree_of_gcd_derivative {D G Q : F[X]} (hD0 : D ≠ 0) (hGQ : D = G * Q)
    (hGD' : G ∣ derivative D)
    (hgreatest : ∀ h : F[X], h ∣ D → h ∣ derivative D → h ∣ G) : Squarefree Q := by
  have hQ0 : Q ≠ 0 := fun h ↦ hD0 (by rw [hGQ, h, mul_zero])
  have hG0 : G ≠ 0 := fun h ↦ hD0 (by rw [hGQ, h, zero_mul])
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hQ0]
  intro q hq hqq
  have hqD : q ∣ D := hGQ ▸ Dvd.dvd.mul_left ((dvd_mul_right q q).trans hqq) G
  -- `D = q ^ (k + 1) * c` with `q ∤ c`
  have hfin : FiniteMultiplicity q D := FiniteMultiplicity.of_not_isUnit hq.not_isUnit hD0
  obtain ⟨c, hc, hqc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  obtain ⟨k, hk⟩ : ∃ k, multiplicity q D = k + 1 :=
    ⟨multiplicity q D - 1, by
      have := (multiplicity_ne_zero hfin).mpr hqD
      omega⟩
  rw [hk] at hc
  -- `q ^ k` is a common divisor of `D` and `D′`, hence divides `G`
  have h1 : q ^ k ∣ D := hc ▸ Dvd.dvd.mul_right (pow_dvd_pow q (Nat.le_succ k)) c
  have h2 : q ^ k ∣ derivative D := by
    rw [hc, derivative_mul, derivative_pow, Nat.add_sub_cancel, pow_succ]
    exact dvd_add (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _) _)
      (Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _)
  obtain ⟨G₁, hG₁⟩ := hgreatest _ h1 h2
  -- cancel `q ^ k`: `q * c = G₁ * Q`
  have hcancel : q * c = G₁ * Q := by
    have : q ^ k * (q * c) = q ^ k * (G₁ * Q) := by
      rw [← mul_assoc, ← pow_succ, ← hc, hGQ, hG₁]; ring
    exact mul_left_cancel₀ (pow_ne_zero k hq.ne_zero) this
  -- `q² ∣ Q ∣ q c` forces `q ∣ c`
  have : q * q ∣ q * c := hcancel ▸ Dvd.dvd.mul_left hqq G₁
  exact hqc ((mul_dvd_mul_iff_left hq.ne_zero).mp this)

/-- An irreducible polynomial over a field of characteristic zero does not divide its
derivative. -/
lemma not_dvd_derivative_of_irreducible [CharZero F] {p : F[X]} (hp : Irreducible p) :
    ¬p ∣ derivative p := by
  intro hdvd
  have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
  have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
  exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))

/-- **Multiplicities drop by exactly one under differentiation** (characteristic zero): if
`D = p ^ (k + 1) * c` with `p` irreducible and `p ∤ c`, then `D′ = p ^ k * w` with `p ∤ w`. -/
theorem derivative_pow_succ_mul [CharZero F] {p c : F[X]} (hp : Irreducible p) (hpc : ¬p ∣ c)
    (k : ℕ) :
    ∃ w : F[X], derivative (p ^ (k + 1) * c) = p ^ k * w ∧ ¬p ∣ w := by
  refine ⟨C ((k + 1 : ℕ) : F) * derivative p * c + p * derivative c, ?_, ?_⟩
  · rw [derivative_mul, derivative_pow, Nat.add_sub_cancel, pow_succ]
    simp only [map_natCast, Nat.cast_add, Nat.cast_one]
    ring
  · intro hdvd
    have h1 : p ∣ C ((k + 1 : ℕ) : F) * derivative p * c := by
      have := dvd_sub hdvd (dvd_mul_right p (derivative c))
      simpa using this
    have hunit : IsUnit (C ((k + 1 : ℕ) : F)) :=
      isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)))
    rcases hp.prime.dvd_or_dvd h1 with h2 | h2
    · rcases hp.prime.dvd_or_dvd h2 with h3 | h3
      · exact hp.not_isUnit (isUnit_of_dvd_unit h3 hunit)
      · exact not_dvd_derivative_of_irreducible hp h3
    · exact hpc h2

/-- A squarefree polynomial all of whose irreducible factors divide `S` divides `S`. -/
theorem dvd_of_squarefree_of_irreducible_dvd {Q S : F[X]} (hQ : Squarefree Q)
    (h : ∀ p : F[X], Irreducible p → p ∣ Q → p ∣ S) : Q ∣ S := by
  induction Q using WfDvdMonoid.induction_on_irreducible with
  | zero => exact absurd hQ not_squarefree_zero
  | unit u hu => exact hu.dvd
  | mul a p ha0 hp ih =>
    have hpa : ¬p ∣ a := fun ⟨b, hb⟩ ↦
      hp.not_isUnit (hQ p ⟨b, by rw [hb]; ring⟩)
    have hcop : IsCoprime p a := hp.coprime_iff_not_dvd.mpr hpa
    exact hcop.mul_dvd (h p hp (dvd_mul_right p a))
      (ih (hQ.of_mul_right) fun q hq hqa ↦ h q hq (Dvd.dvd.mul_left hqa p))

variable [CharZero F]

/-- (F2) If `S` is squarefree, every irreducible factor of `M ≠ 0` divides `S`, and
`S * M′ = M * T`, then `T` is coprime to `M`. -/
theorem isCoprime_of_mul_derivative_eq {S M T : F[X]} (hS : Squarefree S) (hM0 : M ≠ 0)
    (hprimes : ∀ p : F[X], Irreducible p → p ∣ M → p ∣ S)
    (hT : S * derivative M = M * T) : IsCoprime T M := by
  refine isCoprime_of_irreducible_dvd (fun h ↦ hM0 h.2) fun p hp hpT hpM ↦ ?_
  -- `M = p ^ (k + 1) * c`, `M′ = p ^ k * w`, `S = p * S₁`, all cofactors prime to `p`
  have hfin : FiniteMultiplicity p M := FiniteMultiplicity.of_not_isUnit hp.not_isUnit hM0
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  obtain ⟨k, hk⟩ : ∃ k, multiplicity p M = k + 1 :=
    ⟨multiplicity p M - 1, by
      have := (multiplicity_ne_zero hfin).mpr hpM
      omega⟩
  rw [hk] at hc
  obtain ⟨w, hw, hpw⟩ := derivative_pow_succ_mul hp hpc k
  obtain ⟨S₁, hS₁⟩ := hprimes p hp hpM
  have hpS₁ : ¬p ∣ S₁ := fun ⟨b, hb⟩ ↦
    hp.not_isUnit (hS p ⟨b, by rw [hS₁, hb]; ring⟩)
  -- cancel `p ^ (k + 1)`
  have hcancel : S₁ * w = c * T := by
    have : p ^ (k + 1) * (S₁ * w) = p ^ (k + 1) * (c * T) := by
      have h1 : S * derivative M = p ^ (k + 1) * (S₁ * w) := by
        rw [hS₁, hc, hw, pow_succ]; ring
      rw [← h1, hT, hc]; ring
    exact mul_left_cancel₀ (pow_ne_zero _ hp.ne_zero) this
  have : p ∣ S₁ * w := hcancel ▸ Dvd.dvd.mul_left hpT c
  rcases hp.prime.dvd_or_dvd this with h1 | h1
  · exact hpS₁ h1
  · exact hpw h1

/-- Every irreducible factor of `D` divides the squarefree part `Q = D / gcd (D, D′)`
(characteristic zero). -/
theorem irreducible_dvd_sqfreePart {D G Q : F[X]} (hD0 : D ≠ 0) (hGQ : D = G * Q)
    (hGD' : G ∣ derivative D) {p : F[X]} (hp : Irreducible p) (hpD : p ∣ D) : p ∣ Q := by
  by_contra hpQ
  have hfin : FiniteMultiplicity p D := FiniteMultiplicity.of_not_isUnit hp.not_isUnit hD0
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  obtain ⟨k, hk⟩ : ∃ k, multiplicity p D = k + 1 :=
    ⟨multiplicity p D - 1, by
      have := (multiplicity_ne_zero hfin).mpr hpD
      omega⟩
  rw [hk] at hc
  obtain ⟨w, hw, hpw⟩ := derivative_pow_succ_mul hp hpc k
  -- `p ^ (k + 1) ∣ G * Q` and `p ∤ Q`, so `p ^ (k + 1) ∣ G ∣ D′ = p ^ k * w`
  have h1 : p ^ (k + 1) ∣ G * Q := hGQ ▸ hc ▸ dvd_mul_right _ _
  have h2 : p ^ (k + 1) ∣ G := hp.prime.pow_dvd_of_dvd_mul_right (k + 1) hpQ h1
  have h3 : p ^ (k + 1) ∣ p ^ k * w := by
    rw [← hw, ← hc]; exact h2.trans hGD'
  rw [pow_succ] at h3
  exact hpw ((mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).mp h3)

/-- (F1) If every irreducible factor of `M ≠ 0` divides `S`, then `M ∣ S * M′`. -/
theorem dvd_mul_derivative {S M : F[X]} (hM0 : M ≠ 0)
    (hprimes : ∀ p : F[X], Irreducible p → p ∣ M → p ∣ S) : M ∣ S * derivative M := by
  classical
  -- `G = gcd (M, M′)`, `M = G Q` with `Q` squarefree, `M′ = G W`
  set G := EuclideanDomain.gcd M (derivative M) with hG
  obtain ⟨Q, hQ⟩ : G ∣ M := EuclideanDomain.gcd_dvd_left _ _
  obtain ⟨W, hW⟩ : G ∣ derivative M := EuclideanDomain.gcd_dvd_right _ _
  have hQsq : Squarefree Q := squarefree_of_gcd_derivative hM0 hQ
    (EuclideanDomain.gcd_dvd_right _ _) fun h h1 h2 ↦ EuclideanDomain.dvd_gcd h1 h2
  have hQS : Q ∣ S := dvd_of_squarefree_of_irreducible_dvd hQsq fun p hp hpQ ↦
    hprimes p hp (hQ ▸ Dvd.dvd.mul_left hpQ G)
  obtain ⟨S₂, hS₂⟩ := hQS
  exact ⟨S₂ * W, by rw [hS₂]; nth_rewrite 1 [hW]; rw [hQ]; ring⟩

end Differential
