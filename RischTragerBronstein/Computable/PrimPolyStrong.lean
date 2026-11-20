import RischTragerBronstein.Computable.PrimPoly
import RischTragerBronstein.Computable.PrimTimesStrong

/-!
# Polynomials in a primitive `t` over `R(x)`: the negative answer

Integrand `∑_{j ≤ d} fⱼ(x) t ^ j`, `t′ = η(x) ∈ R(x)` with no rational antiderivative (e.g.
`t = log b(x)`), `fⱼ = Aⱼ / Dⱼ`. If the recursive limited-integration loop `primLoop` fails, the
integrand has **no elementary integral** over `K = R(x, t)` — with no assumption on constants.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field K] [Algebra R K]
variable [Differential K]

theorem not_elementary_primPoly (hR : ∀ r : R, (algebraMap R K r)′ = 0)
    (x t : K) (hx : x′ = 1) (En Ed : CPoly R)
    (ht : t′ = aeval x (toPoly En) / aeval x (toPoly Ed))
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (Iη : RationalIntegral R) (hcη : rationalCheck En Ed Iη = true) (hη0 : isZero Iη.r = false)
    (d : ℕ) (A D : ℕ → CPoly R) (hD0 : ∀ j, 1 ≤ j → j ≤ d → toPoly (D j) ≠ 0)
    (hnone : primLoop En Ed Iη A D d ([], [1]) = none)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    [CharZero K] (hE : IsElementaryExtension K E) (g : E) :
    g′ ≠ algebraMap K E (∑ j ∈ Finset.range (d + 1),
      aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j) := by
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
  -- (5) the coefficient equations over `C'(x)`
  let c' : κ → Cc⟮xE⟯ := fun i ↦
    if hi : i ∈ s then algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩ else 0
  let Ap : (Cc⟮xE⟯)[X] := ∑ j ∈ Finset.range (d + 1), C (ev Cc⟮xE⟯ ι (A j, D j)) * X ^ j
  have hfr : ∀ P Q : CPoly R, algebraMap Cc⟮xE⟯ E (ev Cc⟮xE⟯ ι (P, Q)) =
      ψ (aeval x (toPoly P) / aeval x (toPoly Q)) := fun P Q ↦ by
    simp only [ev]
    rw [map_div₀, hval, hval, map_div₀]
  have hAp : aeval tE Ap = ψ (∑ j ∈ Finset.range (d + 1),
      aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j) := by
    simp only [Ap, map_sum, map_mul, map_pow, aeval_C, aeval_X, hfr]
    rfl
  have hcoeffAp : ∀ j, j ≤ d → Ap.coeff j = ev Cc⟮xE⟯ ι (A j, D j) := fun j hj ↦ by
    simp only [Ap, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h'
      exact absurd (Finset.mem_range.mpr (by omega)) h'
  have hdegAp : Ap.natDegree ≤ d := by
    refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.mp hj; omega)
  obtain ⟨p, hp, hpd⟩ := coeffs_step_primitive (F := Cc⟮xE⟯) tE htrt η₁ htE'' hconst1 s c' u
    (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) v (hcf _ hv) Ap (by
      rw [hAp, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)
  -- constants of `C'(x)` come from `C'`
  have hKconst : ∀ y : Cc⟮xE⟯, y′ = 0 → ∃ b : Cc, y = algebraMap Cc[X] Cc⟮xE⟯ (C b) :=
    fun y hy ↦ by
      have hyE : ((y : Cc⟮xE⟯) : E)′ = 0 := congrArg Subtype.val hy
      refine ⟨⟨(y : E), hyE⟩, ?_⟩
      apply Subtype.ext
      rw [algebraMap_adjoinSimple, aeval_C]
      rfl
  obtain ⟨b, hb⟩ := hKconst _ (hpd d hdegAp)
  have hEd : toPoly Ed ≠ 0 := by
    have h := hcη
    rw [rationalCheck, Bool.and_eq_true] at h
    exact ((hermiteCheck_iff _ _ _).mp h.1).1
  refine primLoop_complete (K := Cc⟮xE⟯) ι hD hKconst hcη hEd hη0 A D p d hD0
    (fun j h1 h2 ↦ ?_) ([], [1]) (by simp) b ?_ hnone
  · rw [← hcoeffAp j h2]
    exact hp j h1
  · rw [hb]
    simp [ev]

/-- If `primLoop` fails, the polynomial in `t` has no elementary integral. -/
theorem not_hasElementaryIntegral_primPoly {K : Type*} [Field K] [Algebra R K] [Differential K]
    [CharZero K] (hR : ∀ r : R, (algebraMap R K r)′ = 0) (x t : K) (hx : x′ = 1)
    (En Ed : CPoly R) (ht : t′ = aeval x (toPoly En) / aeval x (toPoly Ed))
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (Iη : RationalIntegral R) (hcη : rationalCheck En Ed Iη = true) (hη0 : isZero Iη.r = false)
    (d : ℕ) (A D : ℕ → CPoly R) (hD0 : ∀ j, 1 ≤ j → j ≤ d → toPoly (D j) ≠ 0)
    (hnone : primLoop En Ed Iη A D d ([], [1]) = none) :
    ¬HasElementaryIntegral (∑ j ∈ Finset.range (d + 1),
      aeval x (toPoly (A j)) / aeval x (toPoly (D j)) * t ^ j) := by
  rintro ⟨E, _, _, _, _, hE, g, hg⟩
  exact not_elementary_primPoly hR x t hx En Ed ht hgen Iη hcη hη0 d A D hD0 hnone E hE g hg

end CPoly
