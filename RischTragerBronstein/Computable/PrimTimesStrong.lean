import RischTragerBronstein.Computable.LimitedCrit
import RischTragerBronstein.Computable.LogTimesStrong

/-!
# `∫ f(x) t dx` for a primitive `t` over `R(x)`: the negative answer

`not_hasElementaryIntegral_primTimes`: let `K` be generated over constants `R` by `x` (`x′ = 1`) and
`t` with `t′ = η(x)`, `η = En / Ed ∈ R(x)` — for instance `t = log b(x)`, `η = b′ / b`. Let
`f = A / D`, and let `If`, `Iη` be certified Hermite data for `f` and `η`
(`rationalCheck`), with `Iη.r ≠ 0` (so `η` has no rational antiderivative and `t` is a genuinely new
function). If the executable `limitedCrit` finds **no** constant `c` with `f - c η` rationally
integrable, then `f t` has no elementary integral over `K` — with no assumption on constants.

This generalises `not_hasElementaryIntegral_logTimes` (`η = 1 / x`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field K] [Algebra R K]
variable [Differential K]

theorem not_elementary_primTimes (hR : ∀ r : R, (algebraMap R K r)′ = 0)
    (x t : K) (hx : x′ = 1) (En Ed : CPoly R)
    (ht : t′ = aeval x (toPoly En) / aeval x (toPoly Ed))
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (A D : CPoly R) (If Iη : RationalIntegral R) (hcf' : rationalCheck A D If = true)
    (hcη : rationalCheck En Ed Iη = true) (hη0 : isZero Iη.r = false)
    (hcrit : limitedCrit If.r If.s Iη.r Iη.s = none)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    [CharZero K] (hE : IsElementaryExtension K E) (g : E) :
    g′ ≠ algebraMap K E (aeval x (toPoly A) / aeval x (toPoly D) * t) := by
  intro hg
  classical
  set ψ := algebraMap K E with hψ
  have hcharE : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  -- the field of constants of `E`, as a base field with the trivial derivation
  let Cc := constants E
  let _ : Differential Cc := ⟨0⟩
  have hCc0 : ∀ c : Cc, c′ = 0 := fun _ ↦ rfl
  have hDAc : DifferentialAlgebra Cc E := ⟨fun c ↦ c.2⟩
  have hcharC : CharZero Cc := ⟨fun m n h ↦ by
    have := congrArg (fun z : Cc ↦ (z : E)) h
    simpa using this⟩
  -- `R → Const E`
  let ι : R →+* Cc :=
    { toFun := fun r ↦ ⟨ψ (algebraMap R K r), by
        rw [mem_constants, hψ, deriv_algebraMap, hR, map_zero]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ ↦ Subtype.ext (by simp) }
  have hι : ∀ (P : R[X]) (z : K), aeval (ψ z) (P.map ι) = ψ (aeval z P) := fun P z ↦ by
    rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
    rfl
  set xE := ψ x with hxE
  set tE := ψ t with htE
  have hxE' : xE′ = 1 := by rw [hxE, hψ, deriv_algebraMap, hx, map_one]
  -- (1) `x` is transcendental over the constants
  have htrx : Transcendental Cc xE :=
    transcendental_of_deriv_ne_zero hCc0 (by rw [hxE']; exact one_ne_zero)
  -- the field `F₁ = C'(x)`
  have hw : xE′ = aeval xE (1 : Cc[X]) := by rw [hxE', map_one]
  let _ := algebraAdjoinSimple (F := Cc) xE
  let _ : Differential Cc[X] := polynomialOfDeriv (1 : Cc[X])
  let _ : Differential Cc⟮xE⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple xE 1 hw)
  have hFR : IsFractionRing Cc[X] Cc⟮xE⟯ := isFractionRing_adjoin_simple xE htrx
  have hDA1 : DifferentialAlgebra Cc[X] Cc⟮xE⟯ := differentialAlgebra_adjoin_simple xE 1 hw
  have hDA1E : DifferentialAlgebra Cc⟮xE⟯ E :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple xE 1 hw)
  have hchar1 : CharZero Cc⟮xE⟯ :=
    charZero_of_injective_algebraMap (algebraMap Cc Cc⟮xE⟯).injective
  have hD : ∀ P : Cc[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial hCc0 P
  set η₁ : Cc⟮xE⟯ := algebraMap Cc[X] Cc⟮xE⟯ ((toPoly En).map ι) /
    algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Ed).map ι) with hη₁
  have hval : ∀ P : R[X], algebraMap Cc⟮xE⟯ E (algebraMap Cc[X] Cc⟮xE⟯ (P.map ι)) =
      ψ (aeval x P) := fun P ↦ (algebraMap_adjoinSimple xE _).trans (hι _ x)
  have htE'' : tE′ = algebraMap Cc⟮xE⟯ E η₁ := by
    rw [hη₁, map_div₀, hval, hval, htE, hψ, deriv_algebraMap, ht, map_div₀]
  -- certified Hermite data of `η` and `f` over `C'(x)`
  obtain ⟨hdecη, hsqη, hdegη⟩ := rationalCheck_sound_map (K := Cc⟮xE⟯) ι hD En Ed Iη hcη
  obtain ⟨hdecf, hsqf, hdegf⟩ := rationalCheck_sound_map (K := Cc⟮xE⟯) ι hD A D If hcf'
  have hrη0 : (toPoly Iη.r).map ι ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff ι.injective, ← isZero_iff, hη0]
    exact Bool.noConfusion
  -- (2) `t` is transcendental over `C'(x)`: `η` is not a derivative there
  have htrt : Transcendental Cc⟮xE⟯ tE := by
    refine transcendental_primitive η₁ htE'' fun b hb ↦ hrη0 ?_
    refine eq_zero_of_deriv_eq_proper_fraction (K := Cc⟮xE⟯) hD _ _ hsqη hdegη
      (b - (algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Iη.gn).map ι) /
        algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Iη.gd).map ι) +
        algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Iη.Q).map ι))) ?_
    rw [deriv_sub', hb, hη₁, hdecη]
    ring
  -- (3) all constants of `E` lie in `F₁`
  have hconst1 : ∀ z ∈ (Cc⟮xE⟯)⟮tE⟯, z′ = 0 → z ∈ Set.range (algebraMap Cc⟮xE⟯ E) :=
    fun z _ hz ↦ ⟨algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩, rfl⟩
  -- (4) the strong Liouville theorem
  obtain ⟨κ, s, c, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g hg
  -- `K(Const E) ⊆ F₁(t)`
  set B : IntermediateField Cc⟮xE⟯ E := (Cc⟮xE⟯)⟮tE⟯ with hB
  have hBconst : ∀ z : E, z′ = 0 → z ∈ B := fun z hz ↦
    B.algebraMap_mem (algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩)
  have hBx : xE ∈ B := B.algebraMap_mem ⟨xE, mem_adjoin_simple_self Cc xE⟩
  have hBt : tE ∈ B := mem_adjoin_simple_self _ tE
  let T : IntermediateField R K :=
    { carrier := {k | ψ k ∈ B}
      mul_mem' := fun {k l} hk hl ↦ by
        change ψ (k * l) ∈ B; rw [map_mul]; exact mul_mem hk hl
      one_mem' := by change ψ 1 ∈ B; rw [map_one]; exact one_mem _
      add_mem' := fun {k l} hk hl ↦ by
        change ψ (k + l) ∈ B; rw [map_add]; exact add_mem hk hl
      zero_mem' := by change ψ 0 ∈ B; rw [map_zero]; exact zero_mem _
      algebraMap_mem' := fun r ↦ hBconst _ (by rw [hψ, deriv_algebraMap, hR, map_zero])
      inv_mem' := fun k hk ↦ by
        change ψ k⁻¹ ∈ B; rw [map_inv₀]; exact inv_mem hk }
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← hgen, adjoin_le_iff]
    rintro k (rfl | rfl)
    · exact hBx
    · exact hBt
  have hKB : ∀ k : K, ψ k ∈ B := fun k ↦ by
    have : k ∈ T := hT ▸ IntermediateField.mem_top
    exact this
  have hcf : ∀ z ∈ constField K E, z ∈ B := by
    let N : IntermediateField K E := { B.toSubfield with algebraMap_mem' := hKB }
    have : constField K E ≤ N := adjoin_le_iff.mpr fun z hz ↦ hBconst z hz
    exact fun z hz ↦ this hz
  -- (5) the limited-integration criterion over `C'(x)`
  let c' : κ → Cc⟮xE⟯ := fun i ↦
    if hi : i ∈ s then algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩ else 0
  set f₁ : Cc⟮xE⟯ := algebraMap Cc[X] Cc⟮xE⟯ ((toPoly A).map ι) /
    algebraMap Cc[X] Cc⟮xE⟯ ((toPoly D).map ι) with hf₁
  obtain ⟨c₂, p₁, hc₂, hp₁⟩ := limited_step_primitive (F := Cc⟮xE⟯) tE htrt η₁ htE'' hconst1 s c' u
    (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) v (hcf _ hv) f₁ 0 (by
      rw [hf₁, map_div₀, hval, hval, map_zero, add_zero, htE, ← map_div₀, ← map_mul, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)
  have hc₂E : ((c₂ : Cc⟮xE⟯) : E)′ = 0 := congrArg Subtype.val hc₂
  have hc₂eq : c₂ = algebraMap Cc[X] Cc⟮xE⟯ (C ⟨(c₂ : E), hc₂E⟩) := by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, aeval_C]
    rfl
  -- `f₁ - 2 c₂ η₁ = p₁′` is a derivative: the limited-integration identity holds over `C'`
  have hlim := (limited_integral_iff (K := Cc⟮xE⟯) hD _ _ _ _ _ _ hsqf hsqη hdegf hdegη
    (2 * ⟨(c₂ : E), hc₂E⟩)).mp ⟨p₁, by
      rw [← hdecf, ← hdecη, ← hp₁, C_mul, map_mul, ← hc₂eq]
      simp only [C_ofNat, map_ofNat]
      ring⟩
  obtain ⟨c₀, hc₀⟩ := limited_descent ι hlim
  exact limitedCrit_complete hcrit ⟨c₀, hc₀⟩

/-- If `limitedCrit` finds no constant, `f(x) t` has no elementary integral. -/
theorem not_hasElementaryIntegral_primTimes {K : Type*} [Field K] [Algebra R K] [Differential K]
    [CharZero K] (hR : ∀ r : R, (algebraMap R K r)′ = 0) (x t : K) (hx : x′ = 1)
    (En Ed : CPoly R) (ht : t′ = aeval x (toPoly En) / aeval x (toPoly Ed))
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (A D : CPoly R) (If Iη : RationalIntegral R) (hcf' : rationalCheck A D If = true)
    (hcη : rationalCheck En Ed Iη = true) (hη0 : isZero Iη.r = false)
    (hcrit : limitedCrit If.r If.s Iη.r Iη.s = none) :
    ¬HasElementaryIntegral (aeval x (toPoly A) / aeval x (toPoly D) * t) := by
  rintro ⟨E, _, _, _, _, hE, g, hg⟩
  exact not_elementary_primTimes hR x t hx En Ed ht hgen A D If Iη hcf' hcη hη0 hcrit E hE g hg

end CPoly
