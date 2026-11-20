import RischTragerBronstein.Computable.Prim2TimesStrong
import RischTragerBronstein.Elementary.Sum

/-!
# Height three: `A(t₁) t₂` — the reduction when `limitedPrim` succeeds

If `limitedPrim` returns `[b, c]`, there is an explicit `P ∈ R(x)(t₁)` (a polynomial in `t₁`) with
`P′ = A - c η₂`, and

  `A t₂ = (P t₂ + (c / 2) t₂²)′ - P η₂`.

Hence `A t₂` has an elementary integral over `K = R(x)(t₁)(t₂)` **iff** `P η₂ ∈ R(x)(t₁)` has one.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

/-- Differentiating a polynomial in a primitive `t`, coefficientwise. -/
lemma deriv_sum_mul_pow {L : Type*} [Field L] [Differential L] (t η : L) (ht : t′ = η)
    (p : ℕ → L) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), p j * t ^ j)′ =
      ∑ j ∈ Finset.range n, ((p j)′ + ((j + 1 : ℕ) : L) * η * p (j + 1)) * t ^ j +
        (p n)′ * t ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, map_add, ih, Finset.sum_range_succ, Derivation.leibniz,
      Derivation.leibniz_pow, ht]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
    push_cast
    ring

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

theorem prim2Times_reduce (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ En₂ Ed₂ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (t : K) (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)))
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true)
    (d : ℕ) (A D : ℕ → CPoly R) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) {cs : List R}
    (hsome : limitedPrim En₁ Ed₁ Iη₁ Iη₂ A D d = some cs) :
    ∃ P : F₀, P′ = (∑ j ∈ Finset.range (d + 1),
          aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j) -
        algebraMap R F₀ (cs.getD 1 0) * (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) ∧
      (HasElementaryIntegral (algebraMap F₀ K (∑ j ∈ Finset.range (d + 1),
          aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j) * t) ↔
        HasElementaryIntegral (algebraMap F₀ K
          (P * (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂))))) := by
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
  obtain ⟨p, hpe, hp0, hpd⟩ := limitedPrim_sound (K := R⟮x₀⟯) (RingHom.id R) hDpoly hcη₁ hcη₂ hEd
    A D d hD0 hsome
  have hevc : ∀ q : CPoly R × CPoly R, ((ev R⟮x₀⟯ (RingHom.id R) q : R⟮x₀⟯) : F₀) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    simp only [ev, Polynomial.map_id, IntermediateField.coe_div, hcoe]
  set η₁ : F₀ := aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁) with hη₁
  set η₂ : F₀ := aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂) with hη₂
  let q : ℕ → F₀ := fun j ↦ ((p j : R⟮x₀⟯) : F₀)
  have hnat : ∀ n : ℕ, (((n : R⟮x₀⟯)) : F₀) = (n : F₀) := fun n ↦ by
    rw [← map_natCast (algebraMap R⟮x₀⟯ F₀)]; rfl
  have hqe : ∀ j, 1 ≤ j → j ≤ d → (q j)′ + ((j + 1 : ℕ) : F₀) * η₁ * q (j + 1) =
      aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) := fun j h1 h2 ↦ by
    have := congrArg (fun z : R⟮x₀⟯ ↦ (z : F₀)) (hpe j h1 h2)
    simp only [IntermediateField.coe_add, MulMemClass.coe_mul, hderiv, hevc, hnat] at this
    exact this
  have hq0 : (q 0)′ + η₁ * q 1 =
      aeval x₀ (toPoly (A 0)) / aeval x₀ (toPoly (D 0)) - algebraMap R F₀ (cs.getD 1 0) * η₂ := by
    have := congrArg (fun z : R⟮x₀⟯ ↦ (z : F₀)) hp0
    simp only [IntermediateField.coe_add, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, hderiv,
      hevc, hcoe, aeval_C, RingHom.id_apply] at this
    exact this
  have hqd : (q (d + 1))′ = 0 := by
    have := congrArg (fun z : R⟮x₀⟯ ↦ (z : F₀)) hpd
    simp only [hderiv] at this
    exact this.trans (ZeroMemClass.coe_zero _)
  set P : F₀ := ∑ j ∈ Finset.range (d + 1 + 1), q j * t₁ ^ j with hP
  have hP' : P′ = (∑ j ∈ Finset.range (d + 1),
        aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j) -
      algebraMap R F₀ (cs.getD 1 0) * η₂ := by
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
  refine ⟨P, hP', ?_⟩
  -- `A t₂ = (P t₂ + (c / 2) t₂²)′ - P η₂`
  set fA : F₀ := ∑ j ∈ Finset.range (d + 1),
    aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j with hfA
  set γ : K := algebraMap F₀ K (algebraMap R F₀ (cs.getD 1 0 / 2)) with hγ
  have hγ' : γ′ = 0 := by rw [hγ, deriv_algebraMap, hR, map_zero]
  have hγ2 : γ * 2 = algebraMap F₀ K (algebraMap R F₀ (cs.getD 1 0)) := by
    rw [hγ, map_div₀, map_div₀, map_ofNat, map_ofNat]
    exact div_mul_cancel₀ _ two_ne_zero
  set W : K := algebraMap F₀ K P * t + γ * (t * t) with hW
  have hW' : W′ = algebraMap F₀ K fA * t + algebraMap F₀ K (P * η₂) := by
    rw [hW, map_add, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz, hγ', ht,
      deriv_algebraMap, hP', map_sub, map_mul, map_mul, ← hγ2]
    simp only [smul_eq_mul]
    ring
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

end CPoly
