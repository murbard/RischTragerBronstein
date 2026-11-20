import RischTragerBronstein.Rational.Hermite
import RischTragerBronstein.Rational.PartialFractions
import RischTragerBronstein.Elementary.LiouvilleForm
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Perfect

/-!
# Every rational function has an elementary integral

**Theorem** (`ratFunc_hasElementaryIntegral`). Let `F` be a field of characteristic zero with the
trivial derivation. Every `f ∈ F(x)` has an elementary integral over `(F(x), d/dx)`.

This is the completeness statement for the rational case of the Risch algorithm: there, the answer
"no elementary integral" never occurs. The proof follows the algorithm:

1. Hermite reduction: `f = g′ + b / s` with `s` squarefree;
2. Euclidean division `b = s q + r` and integration of the polynomial `q`;
3. over the splitting field `L` of `s` over `F(x)` — a finite, hence elementary, extension — the
   proper fraction `r / s` is a constant combination of logarithmic derivatives of the `x - α`.
-/

open Polynomial

namespace Differential

universe u

variable {F : Type u} [Field F] [CharZero F]

/-- Polynomials over a field of characteristic zero have polynomial antiderivatives. -/
lemma exists_derivative_eq (q : F[X]) : ∃ Q : F[X], derivative Q = q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨P, rfl⟩ := hp
    obtain ⟨Q, rfl⟩ := hq
    exact ⟨P + Q, derivative_add⟩
  | monomial n a =>
    refine ⟨monomial (n + 1) (a / (n + 1 : F)), ?_⟩
    rw [derivative_monomial, Nat.add_sub_cancel]
    congr 1
    have : (n + 1 : F) ≠ 0 := Nat.cast_add_one_ne_zero n
    push_cast
    field_simp

variable [Differential F]

theorem ratFunc_hasElementaryIntegral (h : ∀ a : F, a′ = 0) (f : RatFunc F) :
    letI := ratFuncOfDeriv (1 : F[X])
    HasElementaryIntegral f := by
  let _ := polynomialOfDeriv (1 : F[X])
  let _ := ratFuncOfDeriv (1 : F[X])
  have hDAF : DifferentialAlgebra F (RatFunc F) := differentialAlgebra_ratFuncOfDeriv 1
  have hDAP : DifferentialAlgebra F[X] (RatFunc F) := differentialAlgebra_ofFractionRing _ _
  let φ : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F)
  -- 1. Hermite reduction
  obtain ⟨g, b, s, hsq, hf⟩ := hermite_reduction_ratFunc h f
  have hs0 : s ≠ 0 := hsq.ne_zero
  have hφs : φ s ≠ 0 := RatFunc.algebraMap_ne_zero hs0
  -- 2. Euclidean division and the polynomial part
  obtain ⟨Q, hQ⟩ := exists_derivative_eq (b / s)
  have hQ' : (φ Q)′ = φ (b / s) := by
    rw [deriv_algebraMap (A := F[X]) (B := RatFunc F) Q]
    change φ (implicitDeriv 1 Q) = _
    rw [implicitDeriv_one_of_trivial h, hQ]
  have hf2 : f = (g + φ Q)′ + φ (b % s) / φ s := by
    have hb : φ b = φ s * φ (b / s) + φ (b % s) := by
      rw [← map_mul, ← map_add, EuclideanDomain.div_add_mod]
    rw [map_add, hQ', hf]
    change g′ + φ b / φ s = _
    rw [hb]
    field_simp
    ring
  -- 3. the splitting field of `s` over `F(x)`
  let sK : (RatFunc F)[X] := s.map (algebraMap F (RatFunc F))
  let L := sK.SplittingField
  have : CharZero (RatFunc F) := charZero_of_injective_algebraMap (algebraMap F (RatFunc F)).injective
  let _ : Differential L := differentialFiniteDimensional (RatFunc F) L
  have hDAL : DifferentialAlgebra (RatFunc F) L := differentialAlgebraFiniteDimensional
  refine HasElementaryIntegral.of_extension (K := L) isElementaryExtension_of_finiteDimensional ?_
  let x : L := algebraMap (RatFunc F) L RatFunc.X
  have hx : x′ = 1 := by
    change (algebraMap (RatFunc F) L RatFunc.X)′ = 1
    rw [deriv_algebraMap, ratFuncOfDeriv_X, map_one, map_one]
  have hF : ∀ a : F, algebraMap F L a ∈ constants L := fun a ↦ by
    rw [mem_constants, IsScalarTower.algebraMap_apply F (RatFunc F) L, deriv_algebraMap,
      deriv_algebraMap, h, map_zero, map_zero]
  have hsplit : (s.map (algebraMap F L)).Splits := by
    have := SplittingField.splits sK
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  obtain ⟨l, hl, hpf⟩ := partial_fractions_logDeriv hF x hx (b % s) s
    (PerfectField.separable_iff_squarefree.mpr hsq) hsplit (degree_mod_lt b hs0)
  have hbridge : ∀ p : F[X], algebraMap (RatFunc F) L (φ p) = aeval x p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow, map_mul, map_pow,
        aeval_C, aeval_X]
      change algebraMap (RatFunc F) L (algebraMap F[X] (RatFunc F) (C a)) *
        algebraMap (RatFunc F) L (algebraMap F[X] (RatFunc F) X) ^ n = _
      rw [RatFunc.algebraMap_C, RatFunc.algebraMap_X, ← RatFunc.algebraMap_eq_C,
        ← IsScalarTower.algebraMap_apply]
  have key : algebraMap (RatFunc F) L f = (algebraMap (RatFunc F) L (g + φ Q))′ +
      (l.map fun p ↦ p.1 * logDeriv p.2).sum := by
    rw [hf2, map_add, map_div₀, hbridge, hbridge, hpf, deriv_algebraMap]
  rw [key]
  exact hasElementaryIntegral_of_liouville_form _ l hl

instance instCharZeroRatFunc : CharZero (RatFunc F) :=
  charZero_of_injective_algebraMap (algebraMap F (RatFunc F)).injective

open scoped Classical in
/-- **The integral of a rational function, explicitly.** If `f = g′ + r / s` in `F(x)` with `s`
squarefree and `deg r < deg s`, then over the splitting field `L` of `s` over `F(x)`

  `f = (g)′ + ∑_{s(α) = 0} (r(α) / s′(α)) * (x - α)′ / (x - α)`,

i.e. `∫ f = g + ∑ (r(α) / s′(α)) log (x - α)`; in particular `f` has an elementary integral. -/
theorem ratFunc_integral_explicit (h : ∀ a : F, a′ = 0) (g : RatFunc F) (r s : F[X])
    (hsq : Squarefree s) (hdeg : r.degree < s.degree) :
    letI := ratFuncOfDeriv (1 : F[X])
    letI : Differential (s.map (algebraMap F (RatFunc F))).SplittingField :=
      differentialFiniteDimensional (RatFunc F) _
    (algebraMap (RatFunc F) (s.map (algebraMap F (RatFunc F))).SplittingField
        (g′ + algebraMap F[X] (RatFunc F) r / algebraMap F[X] (RatFunc F) s) =
      (algebraMap (RatFunc F) (s.map (algebraMap F (RatFunc F))).SplittingField g)′ +
        ∑ α ∈ (s.map (algebraMap F (s.map (algebraMap F (RatFunc F))).SplittingField)).roots.toFinset,
          (aeval α r / aeval α (derivative s)) *
            logDeriv (algebraMap (RatFunc F) _ RatFunc.X - α)) ∧
    HasElementaryIntegral (g′ + algebraMap F[X] (RatFunc F) r / algebraMap F[X] (RatFunc F) s) := by
  let _ := polynomialOfDeriv (1 : F[X])
  let _ := ratFuncOfDeriv (1 : F[X])
  have hDAF : DifferentialAlgebra F (RatFunc F) := differentialAlgebra_ratFuncOfDeriv 1
  let φ : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F)
  let L := (s.map (algebraMap F (RatFunc F))).SplittingField
  let _ : Differential L := differentialFiniteDimensional (RatFunc F) L
  have hDAL : DifferentialAlgebra (RatFunc F) L := differentialAlgebraFiniteDimensional
  let x : L := algebraMap (RatFunc F) L RatFunc.X
  have hx : x′ = 1 := by
    change (algebraMap (RatFunc F) L RatFunc.X)′ = 1
    rw [deriv_algebraMap, ratFuncOfDeriv_X, map_one, map_one]
  have hF : ∀ a : F, algebraMap F L a ∈ constants L := fun a ↦ by
    rw [mem_constants, IsScalarTower.algebraMap_apply F (RatFunc F) L, deriv_algebraMap,
      deriv_algebraMap, h, map_zero, map_zero]
  have hsplit : (s.map (algebraMap F L)).Splits := by
    have := SplittingField.splits (s.map (algebraMap F (RatFunc F)))
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  obtain ⟨hroots, hpf⟩ := partial_fractions_logDeriv_explicit hF x hx r s
    (PerfectField.separable_iff_squarefree.mpr hsq) hsplit hdeg
  have hbridge : ∀ p : F[X], algebraMap (RatFunc F) L (φ p) = aeval x p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow, map_mul, map_pow,
        aeval_C, aeval_X]
      change algebraMap (RatFunc F) L (algebraMap F[X] (RatFunc F) (C a)) *
        algebraMap (RatFunc F) L (algebraMap F[X] (RatFunc F) X) ^ n = _
      rw [RatFunc.algebraMap_C, RatFunc.algebraMap_X, ← RatFunc.algebraMap_eq_C,
        ← IsScalarTower.algebraMap_apply]
  have key : algebraMap (RatFunc F) L (g′ + φ r / φ s) = (algebraMap (RatFunc F) L g)′ +
      ∑ α ∈ (s.map (algebraMap F L)).roots.toFinset,
        (aeval α r / aeval α (derivative s)) * logDeriv (x - α) := by
    rw [map_add, map_div₀, hbridge, hbridge, hpf, deriv_algebraMap]
  refine ⟨key, HasElementaryIntegral.of_extension (K := L)
    isElementaryExtension_of_finiteDimensional ?_⟩
  rw [key, ← Finset.sum_map_toList]
  have := hasElementaryIntegral_of_liouville_form (algebraMap (RatFunc F) L g)
    ((s.map (algebraMap F L)).roots.toFinset.toList.map fun α ↦
      (aeval α r / aeval α (derivative s), x - α)) (by
    intro p hp
    obtain ⟨α, hα, rfl⟩ := List.mem_map.mp hp
    rw [Finset.mem_toList] at hα
    refine ⟨?_, (hroots α hα).2⟩
    rw [← mem_constants]
    exact div_mem (aeval_mem_constants hF r (hroots α hα).1)
      (aeval_mem_constants hF _ (hroots α hα).1))
  rwa [List.map_map] at this

end Differential
