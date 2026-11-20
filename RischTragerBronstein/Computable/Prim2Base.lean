import RischTragerBronstein.Computable.Prim2TimesStrong
import RischTragerBronstein.Computable.PrimPolyPositive

/-!
# Height three: elements of `R(x)[t₁]` inside `R(x)(t₁)(t₂)` — the negative answer

For `A = ∑ aⱼ(x) t₁ ^ j` viewed in `K = R(x)(t₁)(t₂)` (two primitives over `R(x)`): if the
one-parameter loop `primLoop` fails on `A`, then `A` has no elementary integral over `K` either.
The second primitive cannot help: by Liouville's theorem at the step `t₂`, `A - c₀ η₂` would have
a Liouville form over `C'(x)(t₁)`, and `c₀ η₂` only affects the coefficient of `t₁ ^ 0`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R F₀ K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K]

set_option maxHeartbeats 1600000 in
theorem not_elementary_prim2Base (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ En₂ Ed₂ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)))
    (Iη₁ Iη₂ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (hη₁0 : isZero Iη₁.r = false)
    (hindep : limitedCrit Iη₂.r Iη₂.s Iη₁.r Iη₁.s = none)
    (d : ℕ) (A D : ℕ → CPoly R) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0)
    (hnone : primLoop En₁ Ed₁ Iη₁ A D d ([], [1]) = none)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    [CharZero K] (hE : IsElementaryExtension K E) (g : E) :
    g′ ≠ algebraMap K E (algebraMap F₀ K (∑ j ∈ Finset.range (d + 1),
      aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j)) := by
  intro hg
  classical
  set ψ := algebraMap K E with hψ
  have hcharE : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  -- the field of constants of `E`, as a base field with the trivial derivation
  let Cc := constants E
  let _ : Differential Cc := ⟨0⟩
  have hCc0 : ∀ c : Cc, c′ = 0 := fun _ ↦ rfl
  have hDAc : DifferentialAlgebra Cc E := ⟨fun c ↦ c.2⟩
  have hcharC : CharZero Cc := ⟨fun m n h ↦ by
    have := congrArg (fun z : Cc ↦ (z : E)) h
    simpa using this⟩
  -- `F₀ → E`
  let j₀ : F₀ →+* E := ψ.comp (algebraMap F₀ K)
  have hj₀' : ∀ f : F₀, (j₀ f)′ = j₀ f′ := fun f ↦ by
    change (ψ (algebraMap F₀ K f))′ = ψ (algebraMap F₀ K f′)
    rw [hψ, deriv_algebraMap, deriv_algebraMap]
  have hRE : ∀ r : R, (j₀ (algebraMap R F₀ r))′ = 0 := fun r ↦ by
    rw [hj₀', hR, map_zero]
  -- `R → Const E`
  let ι : R →+* Cc :=
    { toFun := fun r ↦ ⟨j₀ (algebraMap R F₀ r), by rw [mem_constants]; exact hRE r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ ↦ Subtype.ext (by simp) }
  have hι : ∀ (P : R[X]) (z : F₀), aeval (j₀ z) (P.map ι) = j₀ (aeval z P) := fun P z ↦ by
    rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
    rfl
  set xE := j₀ x₀ with hxE
  set tE := ψ t with htE
  have hxE' : xE′ = 1 := by rw [hxE, hj₀', hx₀, map_one]
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
  have hvalE : ∀ P : R[X], algebraMap Cc⟮xE⟯ E (algebraMap Cc[X] Cc⟮xE⟯ (P.map ι)) =
      j₀ (aeval x₀ P) := fun P ↦ (algebraMap_adjoinSimple xE _).trans (hι _ x₀)
  have hKconst₁ : ∀ y : Cc⟮xE⟯, y′ = 0 → ∃ b : Cc, y = algebraMap Cc[X] Cc⟮xE⟯ (C b) :=
    fun y hy ↦ by
      have hyE : ((y : Cc⟮xE⟯) : E)′ = 0 := congrArg Subtype.val hy
      refine ⟨⟨(y : E), hyE⟩, ?_⟩
      apply Subtype.ext
      rw [algebraMap_adjoinSimple, aeval_C]
      rfl
  -- `η₁`, `η₂` in `F₁ = C'(x)`
  set η₁' : Cc⟮xE⟯ := algebraMap Cc[X] Cc⟮xE⟯ ((toPoly En₁).map ι) /
    algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Ed₁).map ι) with hη₁'
  set η₂' : Cc⟮xE⟯ := algebraMap Cc[X] Cc⟮xE⟯ ((toPoly En₂).map ι) /
    algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Ed₂).map ι) with hη₂'
  set t1E := j₀ t₁ with ht1E
  have hη₁E : algebraMap Cc⟮xE⟯ E η₁' =
      j₀ (aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁)) := by
    rw [hη₁', map_div₀, hvalE, hvalE, map_div₀]
  have hη₂E : algebraMap Cc⟮xE⟯ E η₂' =
      j₀ (aeval x₀ (toPoly En₂) / aeval x₀ (toPoly Ed₂)) := by
    rw [hη₂', map_div₀, hvalE, hvalE, map_div₀]
  have ht1E' : t1E′ = algebraMap Cc⟮xE⟯ E η₁' := by
    rw [ht1E, hj₀', ht₁, hη₁E]
  have htE'₁ : tE′ = algebraMap Cc⟮xE⟯ E η₂' := by
    rw [htE, hψ, deriv_algebraMap, ht, hη₂E]
    rfl
  obtain ⟨hdec₁, hsq₁, hdeg₁⟩ := rationalCheck_sound_map (K := Cc⟮xE⟯) ι hD En₁ Ed₁ Iη₁ hcη₁
  obtain ⟨hdec₂, hsq₂, hdeg₂⟩ := rationalCheck_sound_map (K := Cc⟮xE⟯) ι hD En₂ Ed₂ Iη₂ hcη₂
  have hrη0 : (toPoly Iη₁.r).map ι ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff ι.injective, ← isZero_iff, hη₁0]
    exact Bool.noConfusion
  have hη₁nd : ∀ y : Cc⟮xE⟯, y′ ≠ η₁' := fun y hy ↦ hrη0 <| by
    refine eq_zero_of_deriv_eq_proper_fraction (K := Cc⟮xE⟯) hD _ _ hsq₁ hdeg₁
      (y - (algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Iη₁.gn).map ι) /
        algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Iη₁.gd).map ι) +
        algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Iη₁.Q).map ι))) ?_
    rw [deriv_sub', hy, hη₁', hdec₁]
    ring
  -- (2) `t₁` is transcendental over `F₁`
  have htr1 : Transcendental Cc⟮xE⟯ t1E := transcendental_primitive η₁' ht1E' hη₁nd
  -- the field `F₂ = F₁(t₁)`
  have hw1 : t1E′ = aeval t1E (C η₁' : (Cc⟮xE⟯)[X]) := by rw [aeval_C, ht1E']
  let _ := algebraAdjoinSimple (F := Cc⟮xE⟯) t1E
  let _ : Differential (Cc⟮xE⟯)[X] := polynomialOfDeriv (C η₁')
  let _ : Differential (Cc⟮xE⟯)⟮t1E⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t1E (C η₁') hw1)
  have hFR2 : IsFractionRing (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ := isFractionRing_adjoin_simple t1E htr1
  have hDA2 : DifferentialAlgebra (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ :=
    differentialAlgebra_adjoin_simple t1E (C η₁') hw1
  have hDA2E : DifferentialAlgebra (Cc⟮xE⟯)⟮t1E⟯ E :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple t1E (C η₁') hw1)
  have hchar2 : CharZero (Cc⟮xE⟯)⟮t1E⟯ :=
    charZero_of_injective_algebraMap (algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯).injective
  have hconst1 : ∀ z ∈ (Cc⟮xE⟯)⟮t1E⟯, z′ = 0 → z ∈ Set.range (algebraMap Cc⟮xE⟯ E) :=
    fun z _ hz ↦ ⟨algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩, rfl⟩
  -- (3) `t₂` is transcendental over `F₂`: `η₂ - c η₁` is never a derivative
  have hα : ∀ c₀ d₀ : Cc⟮xE⟯, c₀′ = 0 → η₂' ≠ c₀ * η₁' + d₀′ := by
    intro c₀ d₀ hc₀ heq
    obtain ⟨cc, hcc⟩ := hKconst₁ c₀ hc₀
    have hlim := (limited_integral_iff (K := Cc⟮xE⟯) hD _ _ _ _ _ _ hsq₂ hsq₁ hdeg₂ hdeg₁ cc).mp
      ⟨d₀, by rw [← hdec₂, ← hdec₁, ← hη₂', ← hη₁', ← hcc, heq]; ring⟩
    obtain ⟨c₁, hc₁⟩ := limited_descent ι hlim
    exact limitedCrit_complete hindep ⟨c₁, hc₁⟩
  set η₂'' : (Cc⟮xE⟯)⟮t1E⟯ := algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯ η₂' with hη₂''
  have htE'' : tE′ = algebraMap (Cc⟮xE⟯)⟮t1E⟯ E η₂'' := htE'₁
  have htr2 : Transcendental (Cc⟮xE⟯)⟮t1E⟯ tE :=
    transcendental_second_primitive t1E tE htr1 η₁' η₂' ht1E' htE'₁ hconst1 hα fun _ ↦ rfl
  have hconst2 : ∀ z ∈ ((Cc⟮xE⟯)⟮t1E⟯)⟮tE⟯, z′ = 0 →
      z ∈ Set.range (algebraMap (Cc⟮xE⟯)⟮t1E⟯ E) :=
    fun z _ hz ↦ ⟨algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯ (algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩), rfl⟩
  -- (4) the strong Liouville theorem
  obtain ⟨κ, s, c, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g hg
  set B₂ : IntermediateField (Cc⟮xE⟯)⟮t1E⟯ E := ((Cc⟮xE⟯)⟮t1E⟯)⟮tE⟯ with hB₂
  have hBconst : ∀ z : E, z′ = 0 → z ∈ B₂ := fun z hz ↦
    B₂.algebraMap_mem (algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯ (algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩))
  -- `F₀ = R(x₀, t₁)` maps into `F₂`
  have hxF₂ : xE ∈ (Cc⟮xE⟯)⟮t1E⟯ :=
    ((Cc⟮xE⟯)⟮t1E⟯).algebraMap_mem ⟨xE, mem_adjoin_simple_self Cc xE⟩
  have ht₁F₂ : t1E ∈ (Cc⟮xE⟯)⟮t1E⟯ := mem_adjoin_simple_self _ t1E
  have hF₀ : ∀ f : F₀, j₀ f ∈ (Cc⟮xE⟯)⟮t1E⟯ := by
    let T₀ : IntermediateField R F₀ :=
      { carrier := {f | j₀ f ∈ (Cc⟮xE⟯)⟮t1E⟯}
        mul_mem' := fun {k l} hk hl ↦ by
          change j₀ (k * l) ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_mul]; exact mul_mem hk hl
        one_mem' := by change j₀ 1 ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_one]; exact one_mem _
        add_mem' := fun {k l} hk hl ↦ by
          change j₀ (k + l) ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_add]; exact add_mem hk hl
        zero_mem' := by change j₀ 0 ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_zero]; exact zero_mem _
        algebraMap_mem' := fun r ↦
          ((Cc⟮xE⟯)⟮t1E⟯).algebraMap_mem (algebraMap Cc Cc⟮xE⟯ (ι r))
        inv_mem' := fun k hk ↦ by
          change j₀ k⁻¹ ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_inv₀]; exact inv_mem hk }
    have hT₀ : T₀ = ⊤ := by
      rw [eq_top_iff, ← hgen₀, adjoin_le_iff]
      rintro k (rfl | rfl)
      · exact hxF₂
      · exact ht₁F₂
    intro f
    have : f ∈ T₀ := hT₀ ▸ IntermediateField.mem_top
    exact this
  let j : F₀ →+* (Cc⟮xE⟯)⟮t1E⟯ := j₀.codRestrict _ hF₀
  let T : IntermediateField F₀ K :=
    { carrier := {k | ψ k ∈ B₂}
      mul_mem' := fun {k l} hk hl ↦ by
        change ψ (k * l) ∈ B₂; rw [map_mul]; exact mul_mem hk hl
      one_mem' := by change ψ 1 ∈ B₂; rw [map_one]; exact one_mem _
      add_mem' := fun {k l} hk hl ↦ by
        change ψ (k + l) ∈ B₂; rw [map_add]; exact add_mem hk hl
      zero_mem' := by change ψ 0 ∈ B₂; rw [map_zero]; exact zero_mem _
      algebraMap_mem' := fun f ↦ B₂.algebraMap_mem (j f)
      inv_mem' := fun k hk ↦ by
        change ψ k⁻¹ ∈ B₂; rw [map_inv₀]; exact inv_mem hk }
  have hT' : T = ⊤ := by
    rw [eq_top_iff, ← hgen, adjoin_le_iff]
    rintro k rfl
    exact mem_adjoin_simple_self _ tE
  have hKB : ∀ k : K, ψ k ∈ B₂ := fun k ↦ by
    have : k ∈ T := hT' ▸ IntermediateField.mem_top
    exact this
  have hcf : ∀ z ∈ constField K E, z ∈ B₂ := by
    let N : IntermediateField K E := { B₂.toSubfield with algebraMap_mem' := hKB }
    have : constField K E ≤ N := adjoin_le_iff.mpr fun z hz ↦ hBconst z hz
    exact fun z hz ↦ this hz
  -- (5) the limited-integration criterion over `F₂`
  let c' : κ → (Cc⟮xE⟯)⟮t1E⟯ := fun i ↦
    if hi : i ∈ s then algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯
      (algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩) else 0
  set fA : F₀ := ∑ i ∈ Finset.range (d + 1),
    aeval x₀ (toPoly (A i)) / aeval x₀ (toPoly (D i)) * t₁ ^ i with hfA
  obtain ⟨e, c₀, d₀, he, hc₀, hrel₀⟩ := liouville_step_primitive (F := (Cc⟮xE⟯)⟮t1E⟯) tE htr2 η₂''
    htE'' hconst2 s c' u (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) v (hcf _ hv)
    (j fA) (by
      change j₀ fA = _
      have h1 : j₀ fA = ψ (algebraMap F₀ K fA) := rfl
      rw [h1, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)
  -- (6) a Liouville identity in `F₂ = F₁(t₁)` for `A - c₀ η₂`, with constants from `F₁`
  set Apoly : (Cc⟮xE⟯)[X] := ∑ i ∈ Finset.range (d + 1),
    C (ev Cc⟮xE⟯ ι (A i, D i)) * X ^ i with hApoly
  have hc₀E : ((c₀ : (Cc⟮xE⟯)⟮t1E⟯) : E)′ = 0 := congrArg Subtype.val hc₀
  set cc : Cc := ⟨(c₀ : E), hc₀E⟩ with hcc
  have hjA : j fA = algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ Apoly := by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple]
    change j₀ fA = _
    simp only [hfA, hApoly, map_sum, map_mul, map_pow, map_div₀, aeval_C, aeval_X, ev, hvalE]
    rfl
  have hcst : algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯
      (C (algebraMap Cc[X] Cc⟮xE⟯ (C cc) * η₂')) = c₀ * η₂'' := by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, aeval_C]
    change ((algebraMap Cc[X] Cc⟮xE⟯ (C cc) * η₂' : Cc⟮xE⟯) : E) = _
    rw [IntermediateField.coe_mul, algebraMap_adjoinSimple, aeval_C]
    rfl
  let c₁ : κ → Cc⟮xE⟯ := fun i ↦
    if hi : i ∈ s then algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩ else 0
  have hc₁ : ∀ i ∈ s, algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (C (c₁ i)) = c' i := fun i hi ↦ by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, aeval_C]
    simp only [c₁, c', dif_pos hi]
    rfl
  have hliou : algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯
        (Apoly - C (algebraMap Cc[X] Cc⟮xE⟯ (C cc) * η₂')) =
      ∑ i ∈ s, algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (C (c₁ i)) * logDeriv (e i) + d₀′ := by
    rw [map_sub, ← hjA, hcst, hrel₀, Finset.sum_congr rfl fun i hi ↦ by rw [← hc₁ i hi]]
    ring
  have hconstP : ∀ P : (Cc⟮xE⟯)[X], P′ = 0 → ∃ e : Cc⟮xE⟯, P = C e := fun P hP ↦
    const_of_implicitDeriv_eq_zero η₁' hη₁nd hP
  obtain ⟨p, hpe, hpd⟩ := exists_coeffs_of_liouville_primitive (K := (Cc⟮xE⟯)⟮t1E⟯) η₁'
    (fun _ ↦ rfl) hconstP s c₁ e he d₀ _ hliou
  have hcoeffA : ∀ i, i ≤ d → Apoly.coeff i = ev Cc⟮xE⟯ ι (A i, D i) := fun i hi ↦ by
    simp only [hApoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h'
      exact absurd (Finset.mem_range.mpr (by omega)) h'
  have hdegA : (Apoly - C (algebraMap Cc[X] Cc⟮xE⟯ (C cc) * η₂')).natDegree ≤ d := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by rw [natDegree_C]; exact Nat.zero_le _))
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.mp hi; omega)
  have hEd : toPoly Ed₁ ≠ 0 := by
    have h := hcη₁
    rw [rationalCheck, Bool.and_eq_true] at h
    exact ((hermiteCheck_iff _ _ _).mp h.1).1
  obtain ⟨b, hb⟩ := hKconst₁ _ (hpd d hdegA)
  refine primLoop_complete (K := Cc⟮xE⟯) ι hD hKconst₁ hcη₁ hEd hη₁0 A D p d
    (fun i _ hi ↦ hD0 i hi) (fun i h1 h2 ↦ ?_) ([], [1]) (by simp) b ?_ hnone
  · have := hpe i h1
    rw [coeff_sub, coeff_C, if_neg (by omega), sub_zero, hcoeffA i h2] at this
    exact this
  · rw [hb]
    simp [ev]

/-- **Polynomials in `t₁` inside a tower of two primitives: decided by `primLoop`.** -/
theorem prim2Base_decides {K : Type*} [Field K] [Algebra F₀ K] [Algebra R K]
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
    (d : ℕ) (A D : ℕ → CPoly R) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) :
    HasElementaryIntegral (algebraMap F₀ K (∑ j ∈ Finset.range (d + 1),
        aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j)) ↔
      (primLoop En₁ Ed₁ Iη₁ A D d ([], [1])).isSome = true := by
  constructor
  · intro h
    by_contra hnone
    rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnone
    obtain ⟨E, _, _, _, _, hE, g, hg⟩ := h
    exact not_elementary_prim2Base hR x₀ t₁ hx₀ En₁ Ed₁ En₂ Ed₂ ht₁ hgen₀ t hgen ht Iη₁ Iη₂ hcη₁
      hcη₂ hη₁0 hindep d A D hD0 hnone E hE g hg
  · intro hsome
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp hsome
    have hRK : ∀ r : R, (algebraMap R K r)′ = 0 := fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R F₀ K, deriv_algebraMap, hR, map_zero]
    let _ : Differential R := ⟨0⟩
    have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
    have hDAR : DifferentialAlgebra R K := ⟨fun r ↦ by rw [hRK, h0, map_zero]⟩
    have haevx : ∀ P : R[X], aeval (algebraMap F₀ K x₀) P = algebraMap F₀ K (aeval x₀ P) :=
      fun P ↦ aeval_algebraMap_apply K x₀ P
    have := hasElementaryIntegral_primPoly h0 (algebraMap F₀ K x₀) (algebraMap F₀ K t₁)
      (by rw [deriv_algebraMap, hx₀, map_one]) En₁ Ed₁
      (by rw [deriv_algebraMap, ht₁, map_div₀, haevx, haevx]) Iη₁ hcη₁ d A D hD0 hL
    simpa only [map_sum, map_mul, map_pow, map_div₀, haevx] using this

end CPoly
