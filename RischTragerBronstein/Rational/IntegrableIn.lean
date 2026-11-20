import RischTragerBronstein.Rational.Integrable
import RischTragerBronstein.Liouville.SimpleTranscendental
import RischTragerBronstein.Liouville.Transcendence

/-!
# Rational functions of `x` are elementary-integrable over any differential field containing `x`

`hasElementaryIntegral_rational_in`: let `K` be a differential field of characteristic zero
containing a field `R` of constants and an element `x` with `x′ = 1`. Then for all `A, D ∈ R[X]`,
`D ≠ 0`, and all `w ∈ K`, the element `w′ + A(x) / D(x)` has an elementary integral over `K`.

This generalises `ratFunc_hasElementaryIntegral` (`K = R(x)`, `w = 0`). It is the form needed
inside towers: e.g. `∫ f(x) log x dx = (…)′ - ∫ g(x) / x dx`, where the last integrand is rational
in `x` but must be integrated over `K = R(x, log x)`.

Proof: Hermite reduction inside the subfield `R⟮x⟯ ⊆ K` (a fraction field of `R[X]`), then partial
fractions over the splitting field of the squarefree denominator **over `K`**.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Differential

universe u

variable {R : Type*} {K : Type u} [Field R] [CharZero R] [Differential R] [Field K]
variable [Differential K] [Algebra R K] [DifferentialAlgebra R K]

theorem hasElementaryIntegral_rational_in (h0 : ∀ r : R, r′ = 0) (x : K) (hx : x′ = 1)
    (A D : R[X]) (hD0 : D ≠ 0) (w : K) :
    HasElementaryIntegral (w′ + aeval x A / aeval x D) := by
  have hcharK : CharZero K := charZero_of_injective_algebraMap (algebraMap R K).injective
  -- the subfield `R(x)` of `K`
  have htr : Transcendental R x :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx]; exact one_ne_zero)
  have hw : x′ = aeval x (1 : R[X]) := by rw [hx, map_one]
  let _ := algebraAdjoinSimple (F := R) x
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x 1 hw)
  have hFR : IsFractionRing R[X] R⟮x⟯ := isFractionRing_adjoin_simple x htr
  have hDA : DifferentialAlgebra R[X] R⟮x⟯ := differentialAlgebra_adjoin_simple x 1 hw
  have hDpoly : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  let φ : R[X] →+* R⟮x⟯ := algebraMap R[X] R⟮x⟯
  have hinj : Function.Injective φ := IsFractionRing.injective R[X] R⟮x⟯
  have hcoe : ∀ P : R[X], ((φ P : R⟮x⟯) : K) = aeval x P := algebraMap_adjoinSimple x
  -- Hermite reduction in `R(x)`
  have hnorm : ∀ p : R[X], Irreducible p → ¬p ∣ p′ := by
    intro p hp hdvd
    rw [hDpoly] at hdvd
    have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
    have hne : derivative p ≠ 0 := fun h ↦ hpos (derivative_eq_zero.mp h)
    exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
  obtain ⟨g, b, s, hsq, hf⟩ := hermite_reduction_of_normal (K := R⟮x⟯) hinj hnorm D hD0 A
  have hs0 : s ≠ 0 := hsq.ne_zero
  have hφs : φ s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs0
  obtain ⟨Q, hQ⟩ := exists_derivative_eq (b / s)
  have hQ' : (φ Q)′ = φ (b / s) := by rw [deriv_algebraMap, hDpoly, hQ]
  have hf2 : φ A / φ D = (g + φ Q)′ + φ (b % s) / φ s := by
    have hb : φ b = φ s * φ (b / s) + φ (b % s) := by
      rw [← map_mul, ← map_add, EuclideanDomain.div_add_mod]
    rw [map_add, hQ', hf, hb]
    simp only [φ] at hφs ⊢
    field_simp
    ring
  -- the same identity in `K`
  have hfK : aeval x A / aeval x D =
      ((g + φ Q : R⟮x⟯) : K)′ + aeval x (b % s) / aeval x s := by
    have := congrArg (fun y : R⟮x⟯ ↦ (y : K)) hf2
    simp only [IntermediateField.coe_div, IntermediateField.coe_add, hcoe] at this
    rw [this]
    rfl
  -- partial fractions over the splitting field of `s` over `K`
  let sK : K[X] := s.map (algebraMap R K)
  let L := sK.SplittingField
  let _ : Differential L := differentialFiniteDimensional K L
  have hDAL : DifferentialAlgebra K L := differentialAlgebraFiniteDimensional
  refine HasElementaryIntegral.of_extension (K := L) isElementaryExtension_of_finiteDimensional ?_
  let xL : L := algebraMap K L x
  have hxL : xL′ = 1 := by
    change (algebraMap K L x)′ = 1
    rw [deriv_algebraMap, hx, map_one]
  have hF : ∀ a : R, algebraMap R L a ∈ constants L := fun a ↦ by
    rw [mem_constants, IsScalarTower.algebraMap_apply R K L, deriv_algebraMap, deriv_algebraMap,
      h0, map_zero, map_zero]
  have hsplit : (s.map (algebraMap R L)).Splits := by
    have := SplittingField.splits sK
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  obtain ⟨l, hl, hpf⟩ := partial_fractions_logDeriv hF xL hxL (b % s) s
    (PerfectField.separable_iff_squarefree.mpr hsq) hsplit (degree_mod_lt b hs0)
  have hbridge : ∀ P : R[X], algebraMap K L (aeval x P) = aeval xL P := fun P ↦
    (aeval_algebraMap_apply L x P).symm
  have key : algebraMap K L (w′ + aeval x A / aeval x D) =
      (algebraMap K L (w + ((g + φ Q : R⟮x⟯) : K)))′ +
        (l.map fun p ↦ p.1 * logDeriv p.2).sum := by
    rw [hfK, deriv_algebraMap]
    simp only [map_add, map_div₀, hbridge, hpf]
    ring
  rw [key]
  exact hasElementaryIntegral_of_liouville_form _ l hl

end Differential
