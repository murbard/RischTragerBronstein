import RischTragerBronstein.Computable.PrimHexpLoopWPositive
import RischTragerBronstein.Computable.PrimHexpBaseFull

/-!
# Log-type primitive over an exponential: polynomials in `t₂` with coefficients in `R(x)(exp a₁)`

`integratePrimHexpPoly` runs the loop `primExpLoopW` (one limited integration problem with
parameter function `W = U′ / U` per power of `t₂`) and hands the level-0 remainder
`A₀ - W Q₁ ∈ R(x)(exp a₁)` to the height-two integrator `integrateExp`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section F0

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀] [CPoly.HasRatRoots R] [HasNatTest R]

set_option maxHeartbeats 1600000 in
theorem valG_gCodeH_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (Hn Hd μ : CPoly R) (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0)
    (hcop : IsCoprime (toPoly Hn) (toPoly Hd)) (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd) * t₁)
    (W : GFrac (GFrac R)) (k : ℕ) (Ak Q : GFrac (GFrac R)) :
    GPoly.isZero (ops₁g R) (gCodeH Hn Hd W k Ak Q).2 = false ∧
    valG x₀ t₁ (gCodeH Hn Hd W k Ak Q) = valG x₀ t₁ Ak -
      ((k + 1 : ℕ) : F₀) * valG x₀ t₁ W * valG x₀ t₁ Q := by
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
  set η₁' : R⟮x₀⟯ := algebraMap R[X] R⟮x₀⟯ (toPoly Hn) / algebraMap R[X] R⟮x₀⟯ (toPoly Hd)
    with hη₁'
  have hη₁E : algebraMap R⟮x₀⟯ F₀ η₁' = aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd) := by
    rw [hη₁', map_div₀]
    change ((algebraMap R[X] R⟮x₀⟯ (toPoly Hn) : R⟮x₀⟯) : F₀) /
      ((algebraMap R[X] R⟮x₀⟯ (toPoly Hd) : R⟮x₀⟯) : F₀) = _
    rw [hcoe, hcoe]
  have ht₁' : t₁′ = algebraMap R⟮x₀⟯ F₀ η₁' * t₁ := by rw [ht₁, hη₁E]
  have htr1 : Transcendental R⟮x₀⟯ t₁ := by
    refine transcendental_exponential η₁' ht₁0 ht₁' fun n hn b hb ↦ ?_
    refine CPoly.hyperexpW_homogeneous (K := R⟮x₀⟯) (RingHom.id R) hD hHn0 hHd0 hcop hcert (n : ℤ)
      (by exact_mod_cast hn) b (by
        rw [hb, hη₁', Polynomial.map_id, Polynomial.map_id,
          show algebraMap R[X] R⟮x₀⟯ (C (((n : ℕ) : ℤ) : R)) = (n : R⟮x₀⟯) by
            rw [Int.cast_natCast, show (C (n : R) : R[X]) = (n : R[X]) from map_natCast C n,
              map_natCast]])
  have hw1 : t₁′ = aeval t₁ (C η₁' * X : (R⟮x₀⟯)[X]) := by
    rw [map_mul, aeval_C, aeval_X, ht₁']
  let _ := algebraAdjoinSimple (F := R⟮x₀⟯) t₁
  let _ : Differential (R⟮x₀⟯)[X] := polynomialOfDeriv (C η₁' * X)
  let _ : Differential (R⟮x₀⟯)⟮t₁⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t₁ (C η₁' * X) hw1)
  have hFR2 : IsFractionRing (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ := isFractionRing_adjoin_simple t₁ htr1
  have hDA2 : DifferentialAlgebra (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ :=
    differentialAlgebra_adjoin_simple t₁ (C η₁' * X) hw1
  have hηa : ηh (K₁ := R⟮x₀⟯) (RingHom.id R) Hn Hd = η₁' := by
    rw [ηh, Polynomial.map_id, Polynomial.map_id]
  have hD₂ : ∀ P : (R⟮x₀⟯)[X], P′ = implicitDeriv (C (ηh (K₁ := R⟮x₀⟯) (RingHom.id R) Hn Hd) * X) P :=
    fun P ↦ by rw [hηa]; rfl
  have hM : ModelHW (K₁ := R⟮x₀⟯) (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) Hn Hd μ :=
    ModelHW.of (RingHom.id R) hD hHn0 hHd0 hcop hcert hD₂
  -- values of codes in `F₀`
  have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      valP x₀ t₁ q := fun q ↦ by
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, sem_M₁In, hevc]
  have hsemG : ∀ q : GFrac (GFrac R),
      (((hM.cf (RingHom.id R) h0).sem q : (R⟮x₀⟯)⟮t₁⟯) : F₀) = valG x₀ t₁ q := fun q ↦ by
    rw [ModelHW.cf, sem_M₂H, IntermediateField.coe_div, hvalP, hvalP, valG]
  obtain ⟨hden, hsem⟩ := sem_gCodeH (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) h0 hM W k Ak Q
  refine ⟨Bool.eq_false_iff.mpr fun hz ↦ hden ((GPoly.isZero_iff _ _).mp hz), ?_⟩
  have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀)) hsem
  have hnat : (((k + 1 : ℕ) : (R⟮x₀⟯)⟮t₁⟯) : F₀) = ((k + 1 : ℕ) : F₀) := by
    rw [← map_natCast (algebraMap (R⟮x₀⟯)⟮t₁⟯ F₀)]; rfl
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hsemG, hnat] at this
  exact this

end F0

section Decide

variable {R : Type*} [Field R] [DecidableEq R] [CPoly.HasRatRoots R] [HasNatTest R]

/-- The integrator for `∑ₖ Aₖ t₂ ^ k`, `t₂′ = W ∈ R(x)(exp a)`. -/
def integratePrimHexpPoly (Hn Hd μ : CPoly R) (W : GFrac (GFrac R))
    (A : ℕ → GFrac (GFrac R)) (d₂ : ℕ) : Bool :=
  match primHexpLoopW Hn Hd μ W A d₂ ([], [(ops₁g R).one]) with
  | none => false
  | some L =>
    let G := gCodeH Hn Hd W 0 (A 0) (lastGen ([], [(ops₁g R).one]) L)
    integrateHyperexpW Hn Hd μ G.1 G.2

end Decide

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]
variable [CPoly.HasRatRoots R] [HasNatTest R]

/-- **Log-type primitive over an exponential, polynomial part: decided**, both directions. -/
theorem integratePrimHexpPoly_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (Hn Hd μ : CPoly R) (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0)
    (hcop : IsCoprime (toPoly Hn) (toPoly Hd)) (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd) * t₁)
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (W U : GFrac (GFrac R))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (valG x₀ t₁ W))
    (hW0 : GPoly.isZero (ops₁g R) W.2 = false)
    (hWnd : isDerivHexp Hn Hd μ W.1 W.2 = false)
    (hU0 : (ops₂h Hn Hd).isZero U = false)
    (hlog : (ops₂h Hn Hd).isZero ((ops₂h Hn Hd).add ((ops₂h Hn Hd).mul W U)
      ((ops₂h Hn Hd).neg ((ops₂h Hn Hd).deriv U))) = true)
    (d₂ : ℕ) (A : ℕ → GFrac (GFrac R)) :
    HasElementaryIntegral (∑ k ∈ Finset.range (d₂ + 1),
        algebraMap F₀ K (valG x₀ t₁ (A k)) * t ^ k) ↔
      integratePrimHexpPoly Hn Hd μ W A d₂ = true := by
  unfold integratePrimHexpPoly
  cases hL : primHexpLoopW Hn Hd μ W A d₂ ([], [(ops₁g R).one]) with
  | none =>
    simp only [Bool.false_eq_true, iff_false]
    rintro ⟨E, _, _, _, _, hE, g, hg⟩
    exact not_elementary_primHexpPolyW hR x₀ t₁ hx₀ Hn Hd μ hHn0 hHd0 hcop hcert ht₁0 ht₁ hgen₀ W t hgen ht
      hW0 hWnd d₂ A hL E hE g hg
  | some L =>
    simp only
    have hanti := primHexpLoopW_antiderivative (K := K) hR x₀ t₁ hx₀ hHn0 hHd0 hcop hcert ht₁0 ht₁ W t ht A d₂ _ hL
    have hQ0 : valG x₀ t₁ (([], [(ops₁g R).one]) : GFrac (GFrac R)) = 0 := by
      simp [valG, valP]
    rw [hQ0, map_zero, map_zero, zero_mul, zero_add] at hanti
    obtain ⟨hden, hval⟩ := valG_gCodeH_F₀ hR x₀ t₁ hx₀ Hn Hd μ hHn0 hHd0 hcop hcert ht₁0 ht₁ W 0 (A 0)
      (lastGen ([], [(ops₁g R).one]) L)
    rw [hanti, hasElementaryIntegral_deriv_add_iff,
      ← primHexpBaseGen_decides (K := K) hR x₀ t₁ hx₀ Hn Hd μ hHn0 hHd0 hcop hcert ht₁0 ht₁ hgen₀ W U t hgen ht
        hW0 hWnd hU0 hlog _ _ hden, Prod.mk.eta, hval]
    simp only [zero_add, Nat.cast_one, one_mul, map_sub, map_mul]

end Tower
