import RischTragerBronstein.Rational.HermiteReduce
import RischTragerBronstein.Differential.Monomial
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Hermite reduction

**Theorem.** Let `F` be a field of characteristic zero and give `F[t]` a derivation for which every
irreducible polynomial is *normal* (`p ∤ p′`). Then every fraction `a / d` is, modulo a derivative,
a fraction with squarefree denominator:

  `a / d = g′ + b / s`,  `s` squarefree.

For `d/dx` on `F[x]` every irreducible is normal, which gives Hermite reduction for `F(x)`
(`hermite_reduction_ratFunc`). For a general monomial extension the hypothesis fails exactly at the
special polynomials, which is why Bronstein's general Hermite reduction has a third, "reduced" part.

The proof is the algorithm: while `d` is not squarefree, pick an irreducible `p` with `p² ∣ d`,
write `d = p ^ k * c` with `p ∤ c`, lower the pole at `p` to a simple one by `hermite_reduce_pow`,
and recurse on the new denominator `c * p`, of smaller degree.
-/

open Polynomial

namespace Differential

variable {F : Type*} [Field F] [CharZero F]

lemma isUnit_natCast_polynomial (n : ℕ) (hn : n ≠ 0) : IsUnit (n : F[X]) := by
  rw [← C_eq_natCast, isUnit_C, isUnit_iff_ne_zero]
  exact Nat.cast_ne_zero.mpr hn

section General

variable [Differential F[X]] {K : Type*} [Field K] [Differential K]
variable [Algebra F[X] K] [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

/-- Hermite reduction when all irreducible polynomials are normal. -/
theorem hermite_reduction_of_normal (hinj : Function.Injective φ)
    (hnorm : ∀ p : F[X], Irreducible p → ¬p ∣ p′) (d : F[X]) (hd : d ≠ 0) (a : F[X]) :
    ∃ (g : K) (b s : F[X]), Squarefree s ∧ φ a / φ d = g′ + φ b / φ s := by
  induction hN : d.natDegree using Nat.strong_induction_on generalizing d a with
  | _ N ih =>
  by_cases hsq : Squarefree d
  · exact ⟨0, a, d, hsq, by simp⟩
  -- an irreducible `p` with `p² ∣ d`
  obtain ⟨x, hxd, hxu⟩ : ∃ x, x * x ∣ d ∧ ¬IsUnit x := by
    simpa [Squarefree] using hsq
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hd (by simpa using hxd)
  obtain ⟨p, hp, hpx⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx0
  have hp2 : p ^ 2 ∣ d := (pow_two p ▸ mul_dvd_mul hpx hpx).trans hxd
  -- `d = p ^ (m + 2) * c` with `p ∤ c`
  have hfin : FiniteMultiplicity p d := FiniteMultiplicity.of_not_isUnit hp.not_isUnit hd
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  obtain ⟨m, hm⟩ : ∃ m, multiplicity p d = m + 2 :=
    ⟨multiplicity p d - 2, by have := hfin.le_multiplicity_of_pow_dvd hp2; omega⟩
  rw [hm] at hc
  have hp0 : p ≠ 0 := hp.ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hd (by simpa using hc)
  -- `p` is normal with respect to `c`
  have hcop : IsCoprime (c * p′) p := by
    refine (hp.coprime_iff_not_dvd.mpr fun h ↦ ?_).symm
    rcases hp.prime.dvd_or_dvd h with h | h
    · exact hpc h
    · exact hnorm p hp h
  obtain ⟨g₁, b₁, h₁⟩ := hermite_reduce_pow (K := K) isUnit_natCast_polynomial c p
    ((map_ne_zero_iff _ hinj).mpr hc0) ((map_ne_zero_iff _ hinj).mpr hp0) hcop (m + 1) a
  -- recurse on `c * p`
  have hdeg : (c * p).natDegree < N := by
    have hpd : 0 < p.natDegree := hp.natDegree_pos
    rw [← hN, hc, natDegree_mul (pow_ne_zero _ hp0) hc0, natDegree_pow,
      natDegree_mul hc0 hp0]
    nlinarith
  obtain ⟨g₂, b₂, s, hs, h₂⟩ := ih _ hdeg (c * p) (mul_ne_zero hc0 hp0) b₁ rfl
  refine ⟨g₁ + g₂, b₂, s, hs, ?_⟩
  rw [map_mul] at h₂
  rw [map_add, hc, map_mul, map_pow, mul_comm (φ p ^ (m + 2)), show m + 2 = m + 1 + 1 from rfl,
    h₁, h₂]
  ring

/-- **Hermite reduction in a general monomial extension** (Bronstein, Theorem 5.3.1, denominator
part). For an arbitrary derivation on `F[t]`, every `a / d` is a derivative plus a fraction whose
denominator has **no repeated normal irreducible factor**: any irreducible `p` with `p² ∣ d'` is
special (`p ∣ p′`). When all irreducibles are normal this is `hermite_reduction_of_normal`; for
`t = exp a` the only possible repeated factor is `t` itself. -/
theorem hermite_reduction_general (hinj : Function.Injective φ) (d : F[X]) (hd : d ≠ 0)
    (a : F[X]) :
    ∃ (g : K) (b d' : F[X]), d' ≠ 0 ∧ (∀ p : F[X], Irreducible p → p * p ∣ d' → p ∣ p′) ∧
      φ a / φ d = g′ + φ b / φ d' := by
  induction hN : d.natDegree using Nat.strong_induction_on generalizing d a with
  | _ N ih =>
  by_cases hrep : ∃ p : F[X], Irreducible p ∧ p * p ∣ d ∧ ¬p ∣ p′
  swap
  · refine ⟨0, a, d, hd, fun p hp hpp ↦ ?_, by simp⟩
    by_contra hnp
    exact hrep ⟨p, hp, hpp, hnp⟩
  obtain ⟨p, hp, hpp, hnorm⟩ := hrep
  have hp2 : p ^ 2 ∣ d := by rwa [pow_two]
  have hfin : FiniteMultiplicity p d := FiniteMultiplicity.of_not_isUnit hp.not_isUnit hd
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  obtain ⟨m, hm⟩ : ∃ m, multiplicity p d = m + 2 :=
    ⟨multiplicity p d - 2, by have := hfin.le_multiplicity_of_pow_dvd hp2; omega⟩
  rw [hm] at hc
  have hp0 : p ≠ 0 := hp.ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hd (by simpa using hc)
  have hcop : IsCoprime (c * p′) p := by
    refine (hp.coprime_iff_not_dvd.mpr fun h ↦ ?_).symm
    rcases hp.prime.dvd_or_dvd h with h | h
    · exact hpc h
    · exact hnorm h
  obtain ⟨g₁, b₁, h₁⟩ := hermite_reduce_pow (K := K) isUnit_natCast_polynomial c p
    ((map_ne_zero_iff _ hinj).mpr hc0) ((map_ne_zero_iff _ hinj).mpr hp0) hcop (m + 1) a
  have hdeg : (c * p).natDegree < N := by
    have hpd : 0 < p.natDegree := hp.natDegree_pos
    rw [← hN, hc, natDegree_mul (pow_ne_zero _ hp0) hc0, natDegree_pow,
      natDegree_mul hc0 hp0]
    nlinarith
  obtain ⟨g₂, b₂, d', hd'0, hd', h₂⟩ := ih _ hdeg (c * p) (mul_ne_zero hc0 hp0) b₁ rfl
  refine ⟨g₁ + g₂, b₂, d', hd'0, hd', ?_⟩
  rw [map_mul] at h₂
  rw [map_add, hc, map_mul, map_pow, mul_comm (φ p ^ (m + 2)), show m + 2 = m + 1 + 1 from rfl,
    h₁, h₂]
  ring

end General

variable [Differential F]

/-- **Hermite reduction for `F(x)`.** Every rational function is a derivative plus a fraction
with squarefree denominator. -/
theorem hermite_reduction_ratFunc (h : ∀ a : F, a′ = 0) (f : RatFunc F) :
    letI := ratFuncOfDeriv (1 : F[X])
    ∃ (g : RatFunc F) (b s : F[X]), Squarefree s ∧
      f = g′ + algebraMap F[X] (RatFunc F) b / algebraMap F[X] (RatFunc F) s := by
  let _ := polynomialOfDeriv (1 : F[X])
  let _ := ratFuncOfDeriv (1 : F[X])
  have : DifferentialAlgebra F[X] (RatFunc F) := differentialAlgebra_ofFractionRing _ _
  have hnorm : ∀ p : F[X], Irreducible p → ¬p ∣ p′ := by
    intro p hp hdvd
    change p ∣ implicitDeriv 1 p at hdvd
    rw [implicitDeriv_one_of_trivial h] at hdvd
    have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
    have hne : derivative p ≠ 0 := fun h0 ↦ hpos (derivative_eq_zero.mp h0)
    exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
  obtain ⟨g, b, s, hs, hf⟩ := hermite_reduction_of_normal (K := RatFunc F)
    (RatFunc.algebraMap_injective F) hnorm f.denom f.denom_ne_zero f.num
  exact ⟨g, b, s, hs, by rw [← hf, f.num_div_denom]⟩

end Differential
