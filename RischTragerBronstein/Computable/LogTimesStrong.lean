import RischTragerBronstein.Computable.LogTimes
import RischTragerBronstein.Computable.ExpPolyStrong

/-!
# `∫ f(x) log x dx`: the negative answer

`not_elementary_logTimes`: let `K` be a differential field of characteristic zero generated over a
field `R` of constants by `x` and `t` with `x′ = 1`, `t′ = 1 / x` (so `t = log x`). Let
`f = A / D ∈ R(x)` have certified decomposition `f = g′ + r / s` (`rationalCheck`). If the decidable
criterion `LogCrit r s` fails — i.e. neither `r = 0` nor (`x ∣ s` and `r = c (s / x)`) — then
`f(x) t` has **no antiderivative in any elementary extension of `K`**, with no assumption on
constants.

Example: `f = 1 / (x + 1)`: `∫ log x / (x + 1) dx` (a dilogarithm) is not elementary.

The proof has the same architecture as for `p exp a` (`ExpPolyStrong.lean`): strong Liouville
theorem; `x` and then `t` stay transcendental over the constants of the extension
(`transcendental_primitive`, since `1 / x` is not a derivative); the limited-integration criterion
(`limited_step_primitive`); and the criterion over the enlarged constant field descends to `R`
(`limited_log_criterion`, `logCrit_of_map`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field K] [Algebra R K]
variable [Differential K]

theorem not_elementary_logTimes (hR : ∀ r : R, (algebraMap R K r)′ = 0)
    (x t : K) (hx : x′ = 1) (ht : t′ = x⁻¹)
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (A D : CPoly R) (I : RationalIntegral R) (hc : rationalCheck A D I = true)
    (hcrit : ¬LogCrit (toPoly I.r) (toPoly I.s))
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
  have htE' : tE′ = xE⁻¹ := by rw [htE, hψ, deriv_algebraMap, ht, map_inv₀]
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
  have hinjφ : Function.Injective (algebraMap Cc[X] Cc⟮xE⟯) := IsFractionRing.injective _ _
  have hφX : algebraMap Cc[X] Cc⟮xE⟯ X ≠ 0 := (map_ne_zero_iff _ hinjφ).mpr X_ne_zero
  set η₁ : Cc⟮xE⟯ := (algebraMap Cc[X] Cc⟮xE⟯ X)⁻¹ with hη₁
  have hXE : algebraMap Cc⟮xE⟯ E (algebraMap Cc[X] Cc⟮xE⟯ X) = xE := by
    have := algebraMap_adjoinSimple xE (X : Cc[X])
    rwa [aeval_X] at this
  have htE'' : tE′ = algebraMap Cc⟮xE⟯ E η₁ := by rw [hη₁, map_inv₀, hXE, htE']
  -- (2) `t = log x` is transcendental over `C'(x)`: `1 / x` is not a derivative there
  have htrt : Transcendental Cc⟮xE⟯ tE := by
    refine transcendental_primitive η₁ htE'' fun b hb ↦ ?_
    have := eq_zero_of_deriv_eq_proper_fraction (K := Cc⟮xE⟯) hD 1 X
      irreducible_X.squarefree (by rw [degree_one, degree_X]; exact zero_lt_one) b
      (by rw [hb, hη₁, map_one, one_div])
    exact one_ne_zero this
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
      have hA : algebraMap Cc⟮xE⟯ E (algebraMap Cc[X] Cc⟮xE⟯ ((toPoly A).map ι)) =
          ψ (aeval x (toPoly A)) := (algebraMap_adjoinSimple xE _).trans (hι _ x)
      have hDd : algebraMap Cc⟮xE⟯ E (algebraMap Cc[X] Cc⟮xE⟯ ((toPoly D).map ι)) =
          ψ (aeval x (toPoly D)) := (algebraMap_adjoinSimple xE _).trans (hι _ x)
      rw [hf₁, map_div₀, hA, hDd, map_zero, add_zero, htE, ← map_div₀, ← map_mul, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)
  -- the constant `c₂` comes from `Const E`
  have hc₂E : ((c₂ : Cc⟮xE⟯) : E)′ = 0 := congrArg Subtype.val hc₂
  have hc₂eq : c₂ = algebraMap Cc[X] Cc⟮xE⟯ (C ⟨(c₂ : E), hc₂E⟩) := by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, aeval_C]
    rfl
  obtain ⟨hdec, hsq, hdeg⟩ := rationalCheck_sound_map (K := Cc⟮xE⟯) ι hD A D I hc
  have hcritC := limited_log_criterion (K := Cc⟮xE⟯) hD _ _ _ hsq hdeg ⟨(c₂ : E), hc₂E⟩ p₁ (by
    rw [← hdec, ← hf₁, ← hp₁, hη₁, ← hc₂eq]
    ring)
  exact hcrit (logCrit_of_map ι hcritC)

/-- If the criterion fails, `f(x) log x` has no elementary integral. -/
theorem not_hasElementaryIntegral_logTimes {K : Type*} [Field K] [Algebra R K] [Differential K]
    [CharZero K] (hR : ∀ r : R, (algebraMap R K r)′ = 0) (x t : K) (hx : x′ = 1)
    (ht : t′ = x⁻¹) (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (A D : CPoly R) (I : RationalIntegral R) (hc : rationalCheck A D I = true)
    (hcrit : ¬LogCrit (toPoly I.r) (toPoly I.s)) :
    ¬HasElementaryIntegral (aeval x (toPoly A) / aeval x (toPoly D) * t) := by
  rintro ⟨E, _, _, _, _, hE, g, hg⟩
  exact not_elementary_logTimes hR x t hx ht hgen A D I hc hcrit E hE g hg

/-- The certificate for `1 / (x + 1)`, checked by the kernel. -/
theorem rationalCheck_one_div_x_add_one :
    rationalCheck ([1] : CPoly ℚ) [1, 1] ⟨[], [1], [], [1], [1, 1]⟩ = true := by decide +kernel

/-- The criterion fails for `1 / (x + 1)`: so `∫ log x / (x + 1) dx` is not elementary. -/
theorem not_logCrit_one_div_x_add_one :
    ¬LogCrit (toPoly ([1] : CPoly ℚ)) (toPoly ([1, 1] : CPoly ℚ)) := by
  rintro (⟨s', c, hs, -⟩ | h0)
  · have := congrArg (fun P : ℚ[X] ↦ P.coeff 0) hs
    simp at this
  · have := congrArg (fun P : ℚ[X] ↦ P.coeff 0) h0
    simp at this

end CPoly
