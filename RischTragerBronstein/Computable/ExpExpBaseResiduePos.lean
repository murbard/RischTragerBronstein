import RischTragerBronstein.Computable.ExpExpBaseResidue
import RischTragerBronstein.Computable.Prim2BaseResiduePos

/-!
# Two exponentials, level `0`: the positive residue answer

For `bc / sc ∈ R(x)(t₁)`, `t₁ = exp a₁`, with the residue test passing (and `sc` squarefree, prime
to `t₁`, `deg bc < deg sc`): an elementary integral over every extension of any `K ⊇ F₀`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

set_option maxHeartbeats 1600000 in
theorem hasElementaryIntegralIn_expExpBaseResidue (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a : CPoly R) (ha : trim (deriv a) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a)) * t₁)
    (bc sc : GPoly (GFrac R))
    (hsqc : GPoly.squarefreeCheck (Tower.ops₁g R) sc = true)
    (hXs : (GPoly.splitX (Tower.ops₁g R) sc).1 = 0)
    (hlen : (GPoly.trim (Tower.ops₁g R) bc).length < (GPoly.trim (Tower.ops₁g R) sc).length)
    (hres : GPoly.residueCheck (Tower.ops₁g R) (Tower.expW a) bc sc = true) :
    HasElementaryIntegralIn
      (algebraMap F₀ K (Tower.valP x₀ t₁ bc / Tower.valP x₀ t₁ sc)) := by
  classical
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R F₀ := ⟨fun r ↦ by rw [hR, h0, map_zero]⟩
  -- level one: `R(x₀) ⊆ F₀`
  have htr : Transcendental R x₀ :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx₀]; exact one_ne_zero)
  have hw : x₀′ = aeval x₀ (1 : R[X]) := by rw [hx₀, map_one]
  let _ := algebraAdjoinSimple (F := R) x₀
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x₀⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hFR : IsFractionRing R[X] R⟮x₀⟯ := isFractionRing_adjoin_simple x₀ htr
  have hDA : DifferentialAlgebra R[X] R⟮x₀⟯ := differentialAlgebra_adjoin_simple x₀ 1 hw
  have hDA' : DifferentialAlgebra R⟮x₀⟯ F₀ :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hchar1 : CharZero R⟮x₀⟯ := charZero_of_injective_algebraMap (algebraMap R R⟮x₀⟯).injective
  have hD : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x₀⟯ P : R⟮x₀⟯) : F₀) = aeval x₀ P :=
    algebraMap_adjoinSimple x₀
  have hevc : ∀ q : CPoly R × CPoly R, algebraMap R⟮x₀⟯ F₀ (ev R⟮x₀⟯ (RingHom.id R) q) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    change ((ev R⟮x₀⟯ (RingHom.id R) q : R⟮x₀⟯) : F₀) = _
    simp only [ev, Polynomial.map_id, IntermediateField.coe_div, hcoe]
  set η₁' : R⟮x₀⟯ := algebraMap R[X] R⟮x₀⟯ (derivative (toPoly a)) with hη₁'
  have hη₁E : algebraMap R⟮x₀⟯ F₀ η₁' = aeval x₀ (derivative (toPoly a)) := hcoe _
  have ht₁' : t₁′ = algebraMap R⟮x₀⟯ F₀ η₁' * t₁ := by rw [ht₁, hη₁E]
  have hA'0 : derivative (toPoly a) ≠ 0 := fun h' ↦ ha ((trim_eq_nil_iff _).mpr (by
    rw [toPoly_deriv, h']))
  have htr1 : Transcendental R⟮x₀⟯ t₁ := by
    refine transcendental_exponential η₁' ht₁0 ht₁' fun n hn b hb ↦ ?_
    refine rde_homogeneous' (K := R⟮x₀⟯) hD (-(C (n : R) * derivative (toPoly a)))
      (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) hA'0)) b (by
        rw [hb, map_neg, map_mul, ← hη₁']
        have : algebraMap R[X] R⟮x₀⟯ (C (n : R)) = (n : R⟮x₀⟯) := by
          rw [show (C (n : R) : R[X]) = (n : R[X]) from map_natCast C n, map_natCast]
        rw [this]
        ring)
  have hST : IsScalarTower R⟮x₀⟯ F₀ K := inferInstance
  have hDAK : DifferentialAlgebra R⟮x₀⟯ K := ⟨fun a ↦ by
    change (algebraMap F₀ K (algebraMap R⟮x₀⟯ F₀ a))′ = algebraMap F₀ K (algebraMap R⟮x₀⟯ F₀ a′)
    rw [deriv_algebraMap, deriv_algebraMap]⟩
  set M₁ := Tower.M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD with hM₁
  have hvalP : ∀ q : GPoly (GFrac R), aeval t₁ (GPoly.toPoly M₁ q) = Tower.valP x₀ t₁ q :=
    fun q ↦ by
      rw [GPoly.toPoly_eq_sum_range _ q ([], [1])]
      simp only [Tower.valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, hM₁, Tower.sem_M₁In,
        hevc]
  have hvalK : ∀ q : GPoly (GFrac R), aeval (algebraMap F₀ K t₁) (GPoly.toPoly M₁ q) =
      algebraMap F₀ K (Tower.valP x₀ t₁ q) := fun q ↦ by
    rw [aeval_algebraMap_apply, hvalP]
  set Sp := GPoly.toPoly M₁ sc with hSp
  have hsq : Squarefree Sp := GPoly.squarefreeCheck_sound M₁ hsqc
  have hS0 : Sp ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ Sp := by
    have := GPoly.toPoly_splitX M₁ sc
    rw [hXs, pow_zero, one_mul] at this
    rw [hSp, this]
    exact GPoly.not_X_dvd_splitX M₁ sc hS0
  -- no new constants in `R(x₀)(t₁)`
  let _ := algebraAdjoinSimple (F := R⟮x₀⟯) t₁
  let _ : Differential (R⟮x₀⟯)[X] := polynomialOfDeriv (C η₁' * X)
  have hW : GPoly.toPoly M₁ (Tower.expW a) = C η₁' * X := by
    rw [hM₁, Tower.toPoly_expW_In, Tower.ηa, Polynomial.map_id]
  have hw1 : t₁′ = aeval t₁ (C η₁' * X : (R⟮x₀⟯)[X]) := by
    rw [map_mul, aeval_C, aeval_X, ht₁']
  let _ : Differential (R⟮x₀⟯)⟮t₁⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t₁ (C η₁' * X) hw1)
  have hFR2 : IsFractionRing (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ := isFractionRing_adjoin_simple t₁ htr1
  have hDA2 : DifferentialAlgebra (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ :=
    differentialAlgebra_adjoin_simple t₁ (C η₁' * X) hw1
  have hdega : 1 ≤ (toPoly a).natDegree := by
    by_contra hlt
    have h0' : derivative (toPoly a) = 0 := by
      rw [eq_C_of_natDegree_eq_zero (by omega : (toPoly a).natDegree = 0), derivative_C]
    exact hA'0 h0'
  have hconst : ∀ (P : (R⟮x₀⟯)[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ →
      ∃ e : R⟮x₀⟯, P = C e * X ^ n :=
    exp_polynomial_no_new_constants (F := R⟮x₀⟯) (C' := R) hD (toPoly a) hdega (fun P ↦ rfl)
  have hnormal : ∀ p : (R⟮x₀⟯)[X], Irreducible p → p ∣ Sp → ¬p ∣ p′ := fun p hp hpS hp' ↦
    hXS ((dvd_X_of_irreducible_special η₁' (fun P ↦ rfl) hconst hp hp').trans hpS)
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M₁ (Tower.expW a)) Sp) Sp := by
    rw [hW]
    exact isCoprime_deriv_of_squarefree hsq hnormal
  have hr := GPoly.residuePoly_spec M₁ (Tower.expW a) bc sc hS0 hcop
  rw [hW] at hr
  have hT := (GPoly.residueCheck_iff M₁ (Tower.expW a) bc sc hS0).mp hres
  have hdeg := GPoly.degree_lt_of_trim_length_lt M₁ hlen
  have hst : aeval (algebraMap F₀ K t₁) Sp ≠ 0 := by
    rw [hvalK, ← hvalP]
    exact (_root_.map_ne_zero _).mpr
      ((map_ne_zero_iff _ (transcendental_iff_injective.mp htr1)).mpr hS0)
  have ht₁K : algebraMap F₀ K t₁ ≠ 0 := (_root_.map_ne_zero _).mpr ht₁0
  have := hasElementaryIntegralIn_of_residueTest (F := R⟮x₀⟯) (E := K) (algebraMap F₀ K t₁) 0 η₁'
    (by rw [deriv_algebraMap, ht₁', map_zero, zero_add, map_mul]; rfl)
    (algebraMap F₀ K t₁) ht₁K
    (by
      rw [logDeriv, deriv_algebraMap, ht₁', map_mul, mul_div_assoc, div_self ht₁K, mul_one]
      rfl) Sp (GPoly.toPoly M₁ bc) _
    (PerfectField.separable_iff_squarefree.mpr hsq) hst hdeg (by
      have hid : implicitDeriv (C η₁' * X) Sp = mapCoeffs Sp + (C 0 + C η₁' * X) * derivative Sp := by
        simp [implicitDeriv]
      rw [← hid]
      exact hr) hT
  rwa [hvalK, hvalK, ← map_div₀] at this

end CPoly
