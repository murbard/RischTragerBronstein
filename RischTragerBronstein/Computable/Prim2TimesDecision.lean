import RischTragerBronstein.Computable.Prim2TimesPositive
import RischTragerBronstein.Computable.LimitedPrimCodes
import RischTragerBronstein.Computable.Prim2Base

/-!
# Height three: the class `A(t₁) t₂` is decided

`K = R(x)(t₁)(t₂)`, two primitives over `R(x)`. For `A = ∑ aⱼ(x) t₁ ^ j`:

1. `limitedPrimCodes` looks for a constant `c` and `P ∈ R(x)[t₁]` with `P′ = A - c η₂`; if there are
   none, `A t₂` is not elementary (`not_hasElementaryIntegral_prim2Times`);
2. otherwise `A t₂ = (P t₂ + (c / 2) t₂²)′ - P η₂`, and `P η₂ ∈ R(x)[t₁]` is decided by the
   height-two loop `primLoop` (`prim2Base_decides`).

`integratePrim2Times_decides`: both directions, no assumption on constants.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

theorem prim2Times_reduce_codes (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ En₂ Ed₂ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (t : K) (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)))
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true)
    (d : ℕ) (A D : ℕ → CPoly R) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) {c : R}
    {Pc : ℕ → CPoly R × CPoly R}
    (hsome : limitedPrimCodes En₁ Ed₁ Iη₁ Iη₂ A D d = some (c, Pc)) :
    (∀ j ≤ d + 1, toPoly (Pc j).2 ≠ 0) ∧
      (HasElementaryIntegral (algebraMap F₀ K (∑ j ∈ Finset.range (d + 1),
          aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j) * t) ↔
        HasElementaryIntegral (algebraMap F₀ K (∑ j ∈ Finset.range (d + 1 + 1),
          aeval x₀ (toPoly (mul (Pc j).1 En₂)) / aeval x₀ (toPoly (mul (Pc j).2 Ed₂)) *
            t₁ ^ j))) := by
  classical
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R F₀ := ⟨fun r ↦ by rw [hR, h0, map_zero]⟩
  -- the model `R(x₀) ⊆ F₀`
  have htr : Transcendental R x₀ :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx₀]; exact one_ne_zero)
  have hw : x₀′ = aeval x₀ (1 : R[X]) := by rw [hx₀, map_one]
  let _ := algebraAdjoinSimple (F := R) x₀
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x₀⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hFR : IsFractionRing R[X] R⟮x₀⟯ := isFractionRing_adjoin_simple x₀ htr
  have hDA : DifferentialAlgebra R[X] R⟮x₀⟯ := differentialAlgebra_adjoin_simple x₀ 1 hw
  have hDpoly : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x₀⟯ P : R⟮x₀⟯) : F₀) = aeval x₀ P :=
    algebraMap_adjoinSimple x₀
  have hderiv : ∀ y : R⟮x₀⟯, ((y′ : R⟮x₀⟯) : F₀) = (y : F₀)′ := fun _ ↦ rfl
  have hEd : toPoly Ed₁ ≠ 0 := by
    have h := hcη₁
    rw [rationalCheck, Bool.and_eq_true] at h
    exact ((hermiteCheck_iff _ _ _).mp h.1).1
  obtain ⟨hden, hpe, hp0, hpd⟩ := limitedPrimCodes_sound (K := R⟮x₀⟯) (RingHom.id R) hDpoly hcη₁
    hcη₂ hEd A D d hD0 hsome
  set p : ℕ → R⟮x₀⟯ := fun j ↦ ev R⟮x₀⟯ (RingHom.id R) (Pc j) with hp
  have hevc : ∀ q : CPoly R × CPoly R, ((ev R⟮x₀⟯ (RingHom.id R) q : R⟮x₀⟯) : F₀) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    simp only [ev, Polynomial.map_id, IntermediateField.coe_div, hcoe]
  set η₁ : F₀ := aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁) with hη₁
  set η₂ : F₀ := aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂) with hη₂
  let q : ℕ → F₀ := fun j ↦ ((p j : R⟮x₀⟯) : F₀)
  have hnat : ∀ n : ℕ, (((n : R⟮x₀⟯)) : F₀) = (n : F₀) := fun n ↦ by
    rw [← map_natCast (algebraMap R⟮x₀⟯ F₀)]; rfl
  have hq : ∀ j, q j = aeval x₀ (toPoly (Pc j).1) / aeval x₀ (toPoly (Pc j).2) :=
    fun j ↦ hevc (Pc j)
  have hqe : ∀ j, 1 ≤ j → j ≤ d → (q j)′ + ((j + 1 : ℕ) : F₀) * η₁ * q (j + 1) =
      aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) := fun j h1 h2 ↦ by
    have := congrArg (fun z : R⟮x₀⟯ ↦ (z : F₀)) (hpe j h1 h2)
    simp only [IntermediateField.coe_add, MulMemClass.coe_mul, hderiv, hevc, hnat] at this
    rw [hq, hq]
    exact this
  have hq0 : (q 0)′ + η₁ * q 1 =
      aeval x₀ (toPoly (A 0)) / aeval x₀ (toPoly (D 0)) - algebraMap R F₀ (c) * η₂ := by
    have := congrArg (fun z : R⟮x₀⟯ ↦ (z : F₀)) hp0
    simp only [IntermediateField.coe_add, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, hderiv,
      hevc, hcoe, aeval_C, RingHom.id_apply] at this
    rw [hq, hq]
    exact this
  have hqd : (q (d + 1))′ = 0 := by
    have := congrArg (fun z : R⟮x₀⟯ ↦ (z : F₀)) hpd
    simp only [hderiv] at this
    exact this.trans (ZeroMemClass.coe_zero _)
  set P : F₀ := ∑ j ∈ Finset.range (d + 1 + 1), q j * t₁ ^ j with hP
  have hP' : P′ = (∑ j ∈ Finset.range (d + 1),
        aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j) -
      algebraMap R F₀ (c) * η₂ := by
    rw [hP, deriv_sum_mul_pow t₁ η₁ ht₁ q (d + 1), hqd, zero_mul, add_zero,
      Finset.sum_range_succ' _ d, Finset.sum_range_succ' (fun j ↦
        aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j) d]
    have h1 : ∑ j ∈ Finset.range d, ((q (j + 1))′ + ((j + 1 + 1 : ℕ) : F₀) * η₁ * q (j + 1 + 1)) *
        t₁ ^ (j + 1) = ∑ j ∈ Finset.range d,
        aeval x₀ (toPoly (A (j + 1))) / aeval x₀ (toPoly (D (j + 1))) * t₁ ^ (j + 1) :=
      Finset.sum_congr rfl fun j hj ↦ by
        rw [hqe (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)]
    rw [h1]
    simp only [pow_zero, mul_one, Nat.cast_one, zero_add, one_mul]
    rw [hq0]
    ring
  refine ⟨hden, ?_⟩
  -- `A t₂ = (P t₂ + (c / 2) t₂²)′ - P η₂`
  set fA : F₀ := ∑ j ∈ Finset.range (d + 1),
    aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j with hfA
  set γ : K := algebraMap F₀ K (algebraMap R F₀ (c / 2)) with hγ
  have hγ' : γ′ = 0 := by rw [hγ, deriv_algebraMap, hR, map_zero]
  have hγ2 : γ * 2 = algebraMap F₀ K (algebraMap R F₀ (c)) := by
    rw [hγ, map_div₀, map_div₀, map_ofNat, map_ofNat]
    exact div_mul_cancel₀ _ two_ne_zero
  set W : K := algebraMap F₀ K P * t + γ * (t * t) with hW
  have hW' : W′ = algebraMap F₀ K fA * t + algebraMap F₀ K (P * η₂) := by
    rw [hW, map_add, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz, hγ', ht,
      deriv_algebraMap, hP', map_sub, map_mul, map_mul, ← hγ2]
    simp only [smul_eq_mul]
    ring
  have hPη : P * η₂ = ∑ j ∈ Finset.range (d + 1 + 1),
      aeval x₀ (toPoly (mul (Pc j).1 En₂)) / aeval x₀ (toPoly (mul (Pc j).2 Ed₂)) * t₁ ^ j := by
    rw [hP, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hq j, toPoly_mul, toPoly_mul, map_mul, map_mul, hη₂, mul_div_mul_comm]
    ring
  rw [← hPη]
  have hsplit : algebraMap F₀ K fA * t = W′ - algebraMap F₀ K (P * η₂) := by rw [hW']; ring
  constructor
  · intro h
    have h1 := (h.sub_in (hasElementaryIntegralIn_deriv W)).neg
    have heq : -(algebraMap F₀ K fA * t - W′) = algebraMap F₀ K (P * η₂) := by rw [hsplit]; ring
    rwa [heq] at h1
  · intro h
    have h1 := h.neg.add_in (hasElementaryIntegralIn_deriv W)
    have heq : -algebraMap F₀ K (P * η₂) + W′ = algebraMap F₀ K fA * t := by rw [hsplit]; ring
    rwa [heq] at h1


section Decide

variable {R : Type*} [Field R] [DecidableEq R]

/-- **The integrator for the class `A(t₁) t₂`** (two primitives over `R(x)`). -/
def integratePrim2Times (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (En₂ Ed₂ : CPoly R)
    (Iη₂ : RationalIntegral R) (A D : ℕ → CPoly R) (d : ℕ) : Bool :=
  match limitedPrimCodes En₁ Ed₁ Iη₁ Iη₂ A D d with
  | none => false
  | some cP =>
    (primLoop En₁ Ed₁ Iη₁ (fun j ↦ mul (cP.2 j).1 En₂) (fun j ↦ mul (cP.2 j).2 Ed₂) (d + 1)
      ([], [1])).isSome

end Decide

variable [Algebra R K] [IsScalarTower R F₀ K]

/-- **Height three: `A(t₁) t₂` is decided**, both directions, no assumption on constants. -/
theorem integratePrim2Times_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ En₂ Ed₂ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)))
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (d : ℕ) (A D : ℕ → CPoly R) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) :
    HasElementaryIntegral (algebraMap F₀ K (∑ j ∈ Finset.range (d + 1),
        aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j) * t) ↔
      integratePrim2Times En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A D d = true := by
  have hEd₂ : toPoly Ed₂ ≠ 0 := by
    have h := hcη₂
    rw [rationalCheck, Bool.and_eq_true] at h
    exact ((hermiteCheck_iff _ _ _).mp h.1).1
  cases hc : limitedPrimCodes En₁ Ed₁ Iη₁ Iη₂ A D d with
  | none =>
    have hnone : limitedPrim En₁ Ed₁ Iη₁ Iη₂ A D d = none := by
      have := limitedPrimCodes_isSome En₁ Ed₁ Iη₁ Iη₂ A D d
      rw [hc] at this
      exact Option.isNone_iff_eq_none.mp (by rw [Option.isNone_iff_eq_none]
                                             exact Option.not_isSome_iff_eq_none.mp
                                               (by rw [← this]; simp))
    simp only [integratePrim2Times, hc]
    refine ⟨fun h ↦ ?_, fun h ↦ absurd h (by simp)⟩
    exact absurd h (not_hasElementaryIntegral_prim2Times hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t
      hgen ht Iη₁ Iη₂ hcη₁ hcη₂ hη₁0 hindep d A D hD0 hnone)
  | some cP =>
    obtain ⟨c, Pc⟩ := cP
    obtain ⟨hden, hred⟩ := prim2Times_reduce_codes hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ t ht Iη₁ Iη₂
      hcη₁ hcη₂ d A D hD0 hc
    simp only [integratePrim2Times, hc]
    rw [hred]
    exact prim2Base_decides hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t hgen ht Iη₁ Iη₂ hcη₁ hcη₂
      hη₁0 hindep (d + 1) (fun j ↦ mul (Pc j).1 En₂) (fun j ↦ mul (Pc j).2 Ed₂)
      (fun j hj ↦ by rw [toPoly_mul]; exact mul_ne_zero (hden j hj) hEd₂)

end CPoly

namespace CPoly

-- `t₁ = log x`, `t₂ = log (x + 1)`
-- `∫ log x · log (x + 1) dx` : not elementary (dilogarithm)
#eval integratePrim2Times (R := ℚ) [1] [0, 1] (integrateRational [1] [0, 1]) [1] [1, 1]
  (integrateRational [1] [1, 1]) (fun j ↦ if j = 1 then [1] else []) (fun _ ↦ [1]) 1
-- `∫ log (x + 1) / (x + 1) dx = log² (x + 1) / 2` : elementary
#eval integratePrim2Times (R := ℚ) [1] [0, 1] (integrateRational [1] [0, 1]) [1] [1, 1]
  (integrateRational [1] [1, 1]) (fun _ ↦ [1]) (fun _ ↦ [1, 1]) 0
-- `∫ log (x + 1) / x dx` : not elementary
#eval integratePrim2Times (R := ℚ) [1] [0, 1] (integrateRational [1] [0, 1]) [1] [1, 1]
  (integrateRational [1] [1, 1]) (fun _ ↦ [1]) (fun _ ↦ [0, 1]) 0
-- `∫ (log x / (x + 1) + log (x + 1) / x) dx = log x · log (x + 1)` : the `t₂`-part alone is `log(x+1)/x` ✗,
-- but `∫ log (x + 1) dx` ✓
#eval integratePrim2Times (R := ℚ) [1] [0, 1] (integrateRational [1] [0, 1]) [1] [1, 1]
  (integrateRational [1] [1, 1]) (fun _ ↦ [1]) (fun _ ↦ [1]) 0
-- independence of the two logarithms
#eval limitedCrit (R := ℚ) (integrateRational [1] [1, 1]).r (integrateRational [1] [1, 1]).s
  (integrateRational [1] [0, 1]).r (integrateRational [1] [0, 1]).s

end CPoly
