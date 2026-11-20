import RischTragerBronstein.Computable.RDENonCancelExpBound
import RischTragerBronstein.Computable.ExpExpLaurentPositive

/-!
# The non-cancellation solver over `R(x)(exp a₁)` read in `F₀`, and the Laurent antiderivative

`rdeNCExp_sound_F₀`: the solution `Y / D` of `y′ + z a′ y = A / D` (`a′` the value of the code `ηc`)
read in an abstract field `F₀ ⊇ R` with `x₀′ = 1`, `t₁′ = a₁′(x₀) t₁`;
`expArgExpLaurent_antiderivative`: with `t′ = a′ t` in `K ⊇ F₀`, `∑_{j ≠ n} (Yⱼ / Dⱼ) t^j / t^n` is
an antiderivative of the Laurent part.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [HasNatTest R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

set_option maxHeartbeats 1600000 in
theorem rdeNCExp_sound_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a₁ : CPoly R) (ha₁ : trim (deriv a₁) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a₁)) * t₁)
    (z : ℤ) (ηc A D : GPoly (GFrac R))
    (hD0 : GPoly.isZero (ops₁g R) D = false) {Y : GPoly (GFrac R)}
    (h : rdeNCExpB a₁ (GPoly.smul (ops₁g R) (constZ z) ηc) A D = some Y) :
    (valP x₀ t₁ Y / (t₁ ^ specialBound a₁ (normFrac (GPoly.coeffAt (ops₁g R)
        (GPoly.smul (ops₁g R) (constZ z) ηc) 0)) (GPoly.splitX (ops₁g R) D).1 *
        valP x₀ t₁ (GPoly.splitX (ops₁g R) D).2))′ +
      (z : F₀) * valP x₀ t₁ ηc * (valP x₀ t₁ Y / (t₁ ^ specialBound a₁ (normFrac
        (GPoly.coeffAt (ops₁g R) (GPoly.smul (ops₁g R) (constZ z) ηc) 0))
        (GPoly.splitX (ops₁g R) D).1 * valP x₀ t₁ (GPoly.splitX (ops₁g R) D).2)) =
      valP x₀ t₁ A / valP x₀ t₁ D := by
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
  set η₁' : R⟮x₀⟯ := algebraMap R[X] R⟮x₀⟯ (derivative (toPoly a₁)) with hη₁'
  have hη₁E : algebraMap R⟮x₀⟯ F₀ η₁' = aeval x₀ (derivative (toPoly a₁)) := hcoe _
  have ht₁' : t₁′ = algebraMap R⟮x₀⟯ F₀ η₁' * t₁ := by rw [ht₁, hη₁E]
  have hA'0 : derivative (toPoly a₁) ≠ 0 := fun h' ↦ ha₁ ((trim_eq_nil_iff _).mpr (by
    rw [toPoly_deriv, h']))
  have htr1 : Transcendental R⟮x₀⟯ t₁ := by
    refine transcendental_exponential η₁' ht₁0 ht₁' fun n hn b hb ↦ ?_
    refine rde_homogeneous' (K := R⟮x₀⟯) hD (-(C (n : R) * derivative (toPoly a₁)))
      (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) hA'0)) b (by
        rw [hb, map_neg, map_mul, ← hη₁']
        have : algebraMap R[X] R⟮x₀⟯ (C (n : R)) = (n : R⟮x₀⟯) := by
          rw [show (C (n : R) : R[X]) = (n : R[X]) from map_natCast C n, map_natCast]
        rw [this]
        ring)
  have hw1 : t₁′ = aeval t₁ (C η₁' * X : (R⟮x₀⟯)[X]) := by
    rw [map_mul, aeval_C, aeval_X, ht₁']
  let _ := algebraAdjoinSimple (F := R⟮x₀⟯) t₁
  let _ : Differential (R⟮x₀⟯)[X] := polynomialOfDeriv (C η₁' * X)
  let _ : Differential (R⟮x₀⟯)⟮t₁⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t₁ (C η₁' * X) hw1)
  have hFR2 : IsFractionRing (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ := isFractionRing_adjoin_simple t₁ htr1
  have hDA2 : DifferentialAlgebra (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ :=
    differentialAlgebra_adjoin_simple t₁ (C η₁' * X) hw1
  have hηa : ηa (K₁ := R⟮x₀⟯) (RingHom.id R) a₁ = η₁' := by
    rw [ηa, Polynomial.map_id]
  have hD₂ : ∀ P : (R⟮x₀⟯)[X], P′ = implicitDeriv (C (ηa (K₁ := R⟮x₀⟯) (RingHom.id R) a₁) * X) P :=
    fun P ↦ by rw [hηa]; rfl
  have hD0' : GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) D ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) D).mpr hz] at hD0
    exact Bool.noConfusion hD0
  have hsound := rdeNCExpB_sound (K₁ := R⟮x₀⟯) (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) h0 hD a₁ hD₂
    (GPoly.smul (ops₁g R) (constZ z) ηc) A D hD0' h
  rw [GPoly.toPoly_smul, sem_constZ, map_mul] at hsound
  have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      valP x₀ t₁ q := fun q ↦ by
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, sem_M₁In, hevc]
  have hzF : ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (C (z : R⟮x₀⟯)) : (R⟮x₀⟯)⟮t₁⟯) : F₀) = (z : F₀) := by
    rw [algebraMap_adjoinSimple, aeval_C]
    simp
  have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀)) hsound
  have hderiv : ∀ y : (R⟮x₀⟯)⟮t₁⟯, ((y′ : (R⟮x₀⟯)⟮t₁⟯) : F₀) = (y : F₀)′ := fun _ ↦ rfl
  have hXF : ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ X : (R⟮x₀⟯)⟮t₁⟯) : F₀) = t₁ := by
    rw [algebraMap_adjoinSimple, aeval_X]
  simp only [hderiv, IntermediateField.coe_add, IntermediateField.coe_div, MulMemClass.coe_mul,
    SubmonoidClass.coe_pow, hvalP, hzF, hXF] at this
  exact this

variable {K : Type*} [Field K] [Algebra F₀ K] [Differential K] [DifferentialAlgebra F₀ K]

/-- **The Laurent part is integrated**: `W = ∑_{j ≠ n} (Yⱼ / Dⱼ) t₂^j / t₂^n`. -/
theorem expArgExpLaurent_antiderivative (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a₁ : CPoly R) (ha₁ : trim (deriv a₁) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a₁)) * t₁)
    (ηc : GPoly (GFrac R)) (t : K) (ht0 : t ≠ 0)
    (ht : t′ = algebraMap F₀ K (valP x₀ t₁ ηc) * t)
    (N n : ℕ) (A : ℕ → GFrac (GFrac R)) (Y : ℕ → GPoly (GFrac R))
    (hD0 : ∀ j < N, GPoly.isZero (ops₁g R) (A j).2 = false)
    (hsome : ∀ j < N, j ≠ n → rdeNCExpB a₁ (GPoly.smul (ops₁g R) (constZ ((j : ℤ) - n)) ηc)
      (A j).1 (A j).2 = some (Y j)) :
    (∑ j ∈ (Finset.range N).erase n,
        algebraMap F₀ K (valP x₀ t₁ (Y j) / (t₁ ^ specialBound a₁ (normFrac (GPoly.coeffAt (ops₁g R)
          (GPoly.smul (ops₁g R) (constZ ((j : ℤ) - n)) ηc) 0)) (GPoly.splitX (ops₁g R) (A j).2).1 *
          valP x₀ t₁ (GPoly.splitX (ops₁g R) (A j).2).2)) * t ^ j / t ^ n)′ =
      ∑ j ∈ (Finset.range N).erase n, algebraMap F₀ K (valG x₀ t₁ (A j)) * t ^ j / t ^ n := by
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  have hcharK : CharZero K := charZero_of_injective_algebraMap (algebraMap F₀ K).injective
  rw [map_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  obtain ⟨hjn, hjN⟩ := Finset.mem_erase.mp hj
  have hjN' := Finset.mem_range.mp hjN
  have hsol := rdeNCExp_sound_F₀ hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ _ _ _ _ (hD0 j hjN')
    (hsome j hjN' hjn)
  have hg : (((j : ℤ) - n : ℤ) : F₀) = (j : F₀) - n := by push_cast; ring
  rw [hg] at hsol
  rw [deriv_mul_pow_div_pow _ t _ ht0 ht, valG, ← map_natCast (algebraMap F₀ K) j,
    ← map_natCast (algebraMap F₀ K) n, ← map_sub, ← map_mul, deriv_algebraMap, ← map_mul,
    ← map_add, hsol]

end Tower
