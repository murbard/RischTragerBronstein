import RischTragerBronstein.Computable.Prim2PolyStrong
import RischTragerBronstein.Computable.Prim2Base

/-!
# Height three, polynomial part: the explicit antiderivative and the decision

If the `t₂`-loop returns `L`, then with the explicit `W = prim2W … L ∈ K`

  `∑_{k ≤ d₂} Aₖ t₂ ^ k = W′ + (A₀ - η₂ Q₁)`,

and the remainder `A₀ - η₂ Q₁ ∈ R(x)[t₁]` is decided by the height-two loop (`prim2Base_decides`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K]

/-- Soundness of one level of the `t₂`-loop, read in `F₀ = R(x₀)(t₁)`. -/
theorem prim2Step_sound_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    {Iη₁ Iη₂ : RationalIntegral R} (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (k : ℕ) (Ak Q : Poly2 R) (hA : Ak.Wf) (hQ : Q.Wf)
    {c : R} {Q' : Poly2 R} (h : prim2Step En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ k Ak Q = some (c, Q')) :
    Q'.Wf ∧ (valF₀ x₀ t₁ Q')′ = valF₀ x₀ t₁ Ak -
      ((k + 1 : ℕ) : F₀) * (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) * valF₀ x₀ t₁ Q -
      algebraMap R F₀ c * (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) := by
  classical
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R F₀ := ⟨fun r ↦ by rw [hR, h0, map_zero]⟩
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
  have hDpoly : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x₀⟯ P : R⟮x₀⟯) : F₀) = aeval x₀ P :=
    algebraMap_adjoinSimple x₀
  have hevc : ∀ q : CPoly R × CPoly R, algebraMap R⟮x₀⟯ F₀ (ev R⟮x₀⟯ (RingHom.id R) q) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    change ((ev R⟮x₀⟯ (RingHom.id R) q : R⟮x₀⟯) : F₀) = _
    simp only [ev, Polynomial.map_id, IntermediateField.coe_div, hcoe]
  have hval : ∀ P : Poly2 R, ev₂ (K₁ := R⟮x₀⟯) (RingHom.id R) t₁ P.2 P.1 = valF₀ x₀ t₁ P :=
    fun P ↦ by simp only [ev₂, valF₀, hevc]
  have hEd : ∀ {En Ed : CPoly R} {I : RationalIntegral R}, rationalCheck En Ed I = true →
      toPoly Ed ≠ 0 := fun hc ↦ by
    have h := hc
    rw [rationalCheck, Bool.and_eq_true] at h
    exact ((hermiteCheck_iff _ _ _).mp h.1).1
  obtain ⟨hwf, hder⟩ := prim2Step_sound (K₁ := R⟮x₀⟯) (K₂ := F₀) (RingHom.id R) hDpoly hcη₁ hcη₂
    (hEd hcη₁) (hEd hcη₂) t₁ (by rw [ht₁, hevc]) k Ak Q hA hQ h
  refine ⟨hwf, ?_⟩
  rw [hval, hval, hval, hevc] at hder
  rw [hder, map_mul, hevc]
  congr 2
  change ((algebraMap R[X] R⟮x₀⟯ (C c) : R⟮x₀⟯) : F₀) = _
  rw [hcoe, aeval_C]

/-- The closed-form part of the antiderivative, read off from the output of `prim2Loop`. -/
noncomputable def prim2W (x₀ t₁ : F₀) (t : K) : ℕ → Poly2 R → List (R × Poly2 R) → K
  | _, Q, [] => algebraMap F₀ K (valF₀ x₀ t₁ Q) * t
  | m, Q, cQ :: L =>
    (algebraMap F₀ K (valF₀ x₀ t₁ Q) + algebraMap F₀ K (algebraMap R F₀ (cQ.1 / (m : R)))) * t ^ m +
      prim2W x₀ t₁ t (m - 1) cQ.2 L

/-- **The result is an antiderivative** (height three, polynomial part). -/
theorem prim2Loop_antiderivative (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {En₁ Ed₁ En₂ Ed₂ : CPoly R}
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁)) (t : K)
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)))
    {Iη₁ Iη₂ : RationalIntegral R} (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (A : ℕ → Poly2 R) (hA : ∀ k, (A k).Wf) (k : ℕ)
    (Q : Poly2 R) (hQ : Q.Wf) {L : List (R × Poly2 R)}
    (hL : prim2Loop En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A k Q = some L) :
    (prim2LastQ Q L).Wf ∧
      (algebraMap F₀ K (valF₀ x₀ t₁ Q))′ * t ^ (k + 1) +
          ∑ j ∈ Finset.range (k + 1), algebraMap F₀ K (valF₀ x₀ t₁ (A j)) * t ^ j =
        (prim2W x₀ t₁ t (k + 1) Q L)′ + (algebraMap F₀ K (valF₀ x₀ t₁ (A 0)) -
          algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) *
            algebraMap F₀ K (valF₀ x₀ t₁ (prim2LastQ Q L))) := by
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  have hcharK : CharZero K := charZero_of_injective_algebraMap (algebraMap F₀ K).injective
  induction k generalizing Q L with
  | zero =>
    simp only [prim2Loop, Option.some.injEq] at hL
    subst hL
    refine ⟨hQ, ?_⟩
    rw [prim2W, prim2LastQ, Derivation.leibniz, ht]
    simp only [smul_eq_mul, zero_add, pow_one, Finset.range_one, Finset.sum_singleton, pow_zero,
      mul_one]
    ring
  | succ k ih =>
    simp only [prim2Loop] at hL
    cases hstep : prim2Step En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ (k + 1) (A (k + 1)) Q with
    | none => rw [hstep] at hL; exact absurd hL (by simp)
    | some cQ =>
      obtain ⟨c, Q'⟩ := cQ
      rw [hstep] at hL
      simp only [Option.map_eq_some_iff] at hL
      obtain ⟨L', hL', rfl⟩ := hL
      obtain ⟨hQ', hsol⟩ := prim2Step_sound_F₀ hR x₀ t₁ hx₀ ht₁ hcη₁ hcη₂ (k + 1) (A (k + 1)) Q
        (hA (k + 1)) hQ hstep
      obtain ⟨hlast, hrec⟩ := ih Q' hQ' hL'
      refine ⟨hlast, ?_⟩
      set γ : K := algebraMap F₀ K (algebraMap R F₀ (c / ((k + 1 + 1 : ℕ) : R))) with hγ
      have hγ' : γ′ = 0 := by rw [hγ, deriv_algebraMap, hR, map_zero]
      have hγc : ((k + 1 + 1 : ℕ) : K) * γ = algebraMap F₀ K (algebraMap R F₀ c) := by
        rw [hγ, map_div₀, map_div₀, map_natCast, map_natCast]
        exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))
      set q : K := algebraMap F₀ K (valF₀ x₀ t₁ Q) with hq
      set η₂ : K := algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) with hη₂
      have hX : ((q + γ) * t ^ (k + 1 + 1))′ = q′ * t ^ (k + 1 + 1) +
          ((k + 1 + 1 : ℕ) : K) * (q + γ) * η₂ * t ^ (k + 1) := by
        rw [Derivation.leibniz, map_add, hγ', Derivation.leibniz_pow, ht]
        simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, add_zero]
        ring
      have hW : prim2W x₀ t₁ t (k + 1 + 1) Q ((c, Q') :: L') =
          (q + γ) * t ^ (k + 1 + 1) + prim2W x₀ t₁ t (k + 1) Q' L' := rfl
      have hsolK := congrArg (algebraMap F₀ K) hsol
      rw [← deriv_algebraMap] at hsolK
      simp only [map_sub, map_mul, map_natCast] at hsolK
      rw [hW, prim2LastQ, map_add, hX, Finset.sum_range_succ _ (k + 1)]
      linear_combination hrec - t ^ (k + 1) * hsolK - η₂ * t ^ (k + 1) * hγc

/-- The value of `gCodes` in `F₀`. -/
theorem valF₀_gCodes (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0) (x₀ t₁ : F₀) (hx₀ : x₀′ = 1)
    (En₂ Ed₂ : CPoly R) (hEd₂ : toPoly Ed₂ ≠ 0) (k : ℕ) (Ak Q : Poly2 R) (hA : Ak.Wf)
    (hQ : Q.Wf) :
    (gCodes En₂ Ed₂ k Ak Q).Wf ∧ valF₀ x₀ t₁ (gCodes En₂ Ed₂ k Ak Q) = valF₀ x₀ t₁ Ak -
      ((k + 1 : ℕ) : F₀) * (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) * valF₀ x₀ t₁ Q := by
  classical
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R F₀ := ⟨fun r ↦ by rw [hR, h0, map_zero]⟩
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
  have hDpoly : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x₀⟯ P : R⟮x₀⟯) : F₀) = aeval x₀ P :=
    algebraMap_adjoinSimple x₀
  have hevc : ∀ q : CPoly R × CPoly R, algebraMap R⟮x₀⟯ F₀ (ev R⟮x₀⟯ (RingHom.id R) q) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    change ((ev R⟮x₀⟯ (RingHom.id R) q : R⟮x₀⟯) : F₀) = _
    simp only [ev, Polynomial.map_id, IntermediateField.coe_div, hcoe]
  have hval : ∀ P : Poly2 R, ev₂ (K₁ := R⟮x₀⟯) (RingHom.id R) t₁ P.2 P.1 = valF₀ x₀ t₁ P :=
    fun P ↦ by simp only [ev₂, valF₀, hevc]
  obtain ⟨hwf, hev⟩ := ev₂_gCodes (K₁ := R⟮x₀⟯) (K₂ := F₀) (RingHom.id R) t₁ En₂ Ed₂ hEd₂ k Ak Q
    hA hQ
  refine ⟨hwf, ?_⟩
  rw [hval, hval, hval, hevc] at hev
  exact hev

section Decide

variable {R : Type*} [Field R] [DecidableEq R]

/-- **The integrator for polynomials in `t₂` over `R(x)[t₁]`** (two primitives over `R(x)`). -/
def integratePrim2Poly (En₁ Ed₁ : CPoly R) (Iη₁ : RationalIntegral R) (En₂ Ed₂ : CPoly R)
    (Iη₂ : RationalIntegral R) (A : ℕ → Poly2 R) (d₂ : ℕ) : Bool :=
  match prim2Loop En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A d₂ (0, fun _ ↦ ([], [1])) with
  | none => false
  | some L =>
    let G := gCodes En₂ Ed₂ 0 (A 0) (prim2LastQ (0, fun _ ↦ ([], [1])) L)
    (primLoop En₁ Ed₁ Iη₁ (fun j ↦ (G.2 j).1) (fun j ↦ (G.2 j).2) G.1 ([], [1])).isSome

end Decide

variable [Algebra R K] [IsScalarTower R F₀ K] [CharZero K]

/-- **Height three: polynomials in `t₂` with coefficients in `R(x)[t₁]` are decided**, both
directions, no assumption on constants. -/
theorem integratePrim2Poly_decides {K : Type u} [Field K] [Algebra F₀ K] [Algebra R K]
    [IsScalarTower R F₀ K] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]
    (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ En₂ Ed₂ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)))
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (d₂ : ℕ) (A : ℕ → Poly2 R) (hA : ∀ k, (A k).Wf) :
    HasElementaryIntegral (∑ k ∈ Finset.range (d₂ + 1),
        algebraMap F₀ K (valF₀ x₀ t₁ (A k)) * t ^ k) ↔
      integratePrim2Poly En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A d₂ = true := by
  have hEd₂ : toPoly Ed₂ ≠ 0 := by
    have h := hcη₂
    rw [rationalCheck, Bool.and_eq_true] at h
    exact ((hermiteCheck_iff _ _ _).mp h.1).1
  cases hL : prim2Loop En₁ Ed₁ Iη₁ En₂ Ed₂ Iη₂ A d₂ (0, fun _ ↦ ([], [1])) with
  | none =>
    simp only [integratePrim2Poly, hL]
    refine ⟨fun h ↦ ?_, fun h ↦ absurd h (by simp)⟩
    exact absurd h (not_hasElementaryIntegral_prim2Poly hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t
      hgen ht Iη₁ Iη₂ hcη₁ hcη₂ hη₁0 hindep d₂ A hA hL)
  | some L =>
    have hQ₀ : Poly2.Wf ((0, fun _ ↦ ([], [1])) : Poly2 R) := fun j _ ↦ by
      change toPoly ([1] : CPoly R) ≠ 0
      simp
    obtain ⟨hlast, hanti⟩ := prim2Loop_antiderivative (K := K) hR x₀ t₁ hx₀ ht₁ t ht hcη₁ hcη₂ A
      hA d₂ _ hQ₀ hL
    have hz : (algebraMap F₀ K (valF₀ x₀ t₁ ((0, fun _ ↦ ([], [1])) : Poly2 R)))′ = 0 := by
      simp [valF₀]
    rw [hz, zero_mul, zero_add] at hanti
    obtain ⟨hGwf, hGval⟩ := valF₀_gCodes hR x₀ t₁ hx₀ En₂ Ed₂ hEd₂ 0 (A 0)
      (prim2LastQ (0, fun _ ↦ ([], [1])) L) (hA 0) hlast
    set G := gCodes En₂ Ed₂ 0 (A 0) (prim2LastQ (0, fun _ ↦ ([], [1])) L) with hG
    set W := prim2W x₀ t₁ t (d₂ + 1) ((0, fun _ ↦ ([], [1])) : Poly2 R) L with hW
    have hrem : algebraMap F₀ K (valF₀ x₀ t₁ (A 0)) -
        algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) *
          algebraMap F₀ K (valF₀ x₀ t₁ (prim2LastQ (0, fun _ ↦ ([], [1])) L)) =
        algebraMap F₀ K (valF₀ x₀ t₁ G) := by
      rw [hGval, map_sub, map_mul, map_mul, map_natCast]
      simp
    rw [hrem] at hanti
    simp only [integratePrim2Poly, hL]
    rw [← hG, hanti]
    have hbase := prim2Base_decides (K := K) hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t hgen ht Iη₁
      Iη₂ hcη₁ hcη₂ hη₁0 hindep G.1 (fun j ↦ (G.2 j).1) (fun j ↦ (G.2 j).2) hGwf
    change HasElementaryIntegral (algebraMap F₀ K (valF₀ x₀ t₁ G)) ↔ _ at hbase
    rw [← hbase]
    constructor
    · intro h
      have := h.sub_in (hasElementaryIntegralIn_deriv W)
      rwa [add_sub_cancel_left] at this
    · intro h
      have := h.add_in (hasElementaryIntegralIn_deriv W)
      rwa [add_comm] at this

end CPoly

namespace CPoly

-- `t₁ = log x`, `t₂ = log (x + 1)`; coefficient of `t₂ ^ k` is a polynomial in `t₁`
/-- `log (x + 1)²`. -/
def exA₁ : ℕ → Poly2 ℚ := fun k ↦ if k = 2 then (0, fun _ ↦ ([1], [1])) else (0, fun _ ↦ ([], [1]))
/-- `log x · log (x + 1)²`. -/
def exA₂ : ℕ → Poly2 ℚ := fun k ↦
  if k = 2 then (1, fun j ↦ if j = 1 then ([1], [1]) else ([], [1])) else (0, fun _ ↦ ([], [1]))
/-- `log (x + 1)² / (x + 1) + log x / x · log (x + 1)`. -/
def exA₃ : ℕ → Poly2 ℚ := fun k ↦
  if k = 2 then (0, fun _ ↦ ([1], [1, 1]))
  else if k = 1 then (1, fun j ↦ if j = 1 then ([1], [0, 1]) else ([], [1]))
  else (0, fun _ ↦ ([], [1]))

-- `∫ log² (x + 1) dx` ✓
#eval integratePrim2Poly (R := ℚ) [1] [0, 1] (integrateRational [1] [0, 1]) [1] [1, 1]
  (integrateRational [1] [1, 1]) exA₁ 2
-- `∫ log x · log² (x + 1) dx` ✗
#eval integratePrim2Poly (R := ℚ) [1] [0, 1] (integrateRational [1] [0, 1]) [1] [1, 1]
  (integrateRational [1] [1, 1]) exA₂ 2
-- `∫ (log² (x + 1) / (x + 1) + (log x / x) log (x + 1)) dx`
#eval integratePrim2Poly (R := ℚ) [1] [0, 1] (integrateRational [1] [0, 1]) [1] [1, 1]
  (integrateRational [1] [1, 1]) exA₃ 2

end CPoly
