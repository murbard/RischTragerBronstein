import RischTragerBronstein.Computable.ExpArgPrimLaurentStrong
import RischTragerBronstein.Computable.NestedLogBase
import RischTragerBronstein.Liouville.StepExponential

/-!
# An exponential over `R(x)(t₁)`: elements of `R(x)[t₁]` at level `0`

`K = R(x)(t₁)(exp a)`. For `A = ∑ aⱼ(x) t₁ ^ j`: `A` has an elementary integral over `K` iff
`primLoop` succeeds. Liouville's theorem at the exponential step leaves the term
`(∑ cᵢ mᵢ) a′`, which is the derivative of `(∑ cᵢ mᵢ) a ∈ C'(x)`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R F₀ K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K]

set_option maxHeartbeats 3200000 in
theorem not_elementary_expArgPrimBase (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (a : GPoly (GFrac R))
    (hηc : 2 ≤ (GPoly.trim (Tower.ops₁g R) (GPoly.derivT (Tower.ops₁g R) [(En₁, Ed₁)] a)).length)
    (t : K) (ht0 : t ≠ 0) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K
      (Tower.valP x₀ t₁ (GPoly.derivT (Tower.ops₁g R) [(En₁, Ed₁)] a)) * t)
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
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
  let j₀' : F₀ →+* E := ψ.comp (algebraMap F₀ K)
  have hj₀' : ∀ f : F₀, (j₀' f)′ = j₀' f′ := fun f ↦ by
    change (ψ (algebraMap F₀ K f))′ = ψ (algebraMap F₀ K f′)
    rw [hψ, deriv_algebraMap, deriv_algebraMap]
  have hRE : ∀ r : R, (j₀' (algebraMap R F₀ r))′ = 0 := fun r ↦ by
    rw [hj₀', hR, map_zero]
  -- `R → Const E`
  let ι : R →+* Cc :=
    { toFun := fun r ↦ ⟨j₀' (algebraMap R F₀ r), by rw [mem_constants]; exact hRE r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ ↦ Subtype.ext (by simp) }
  have hι : ∀ (P : R[X]) (z : F₀), aeval (j₀' z) (P.map ι) = j₀' (aeval z P) := fun P z ↦ by
    rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
    rfl
  set xE := j₀' x₀ with hxE
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
      j₀' (aeval x₀ P) := fun P ↦ (algebraMap_adjoinSimple xE _).trans (hι _ x₀)
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
  set t1E := j₀' t₁ with ht1E
  have hη₁E : algebraMap Cc⟮xE⟯ E η₁' =
      j₀' (aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁)) := by
    rw [hη₁', map_div₀, hvalE, hvalE, map_div₀]
  have ht1E' : t1E′ = algebraMap Cc⟮xE⟯ E η₁' := by
    rw [ht1E, hj₀', ht₁, hη₁E]
  obtain ⟨hdec₁, hsq₁, hdeg₁⟩ := rationalCheck_sound_map (K := Cc⟮xE⟯) ι hD En₁ Ed₁ Iη₁ hcη₁
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
  have hF₀ : ∀ f : F₀, j₀' f ∈ (Cc⟮xE⟯)⟮t1E⟯ := by
    let T₀ : IntermediateField R F₀ :=
      { carrier := {f | j₀' f ∈ (Cc⟮xE⟯)⟮t1E⟯}
        mul_mem' := fun {k l} hk hl ↦ by
          change j₀' (k * l) ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_mul]; exact mul_mem hk hl
        one_mem' := by change j₀' 1 ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_one]; exact one_mem _
        add_mem' := fun {k l} hk hl ↦ by
          change j₀' (k + l) ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_add]; exact add_mem hk hl
        zero_mem' := by change j₀' 0 ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_zero]; exact zero_mem _
        algebraMap_mem' := fun r ↦
          ((Cc⟮xE⟯)⟮t1E⟯).algebraMap_mem (algebraMap Cc Cc⟮xE⟯ (ι r))
        inv_mem' := fun k hk ↦ by
          change j₀' k⁻¹ ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_inv₀]; exact inv_mem hk }
    have hT₀ : T₀ = ⊤ := by
      rw [eq_top_iff, ← hgen₀, adjoin_le_iff]
      rintro k (rfl | rfl)
      · exact hxF₂
      · exact ht₁F₂
    intro f
    have : f ∈ T₀ := hT₀ ▸ IntermediateField.mem_top
    exact this
  let j : F₀ →+* (Cc⟮xE⟯)⟮t1E⟯ := j₀'.codRestrict _ hF₀
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
  -- (6) the two-level model `F₁ ⊆ F₂`
  have hST : IsScalarTower Cc⟮xE⟯ (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      apply Subtype.ext
      rw [Polynomial.algebraMap_eq, algebraMap_adjoinSimple, aeval_C]
      rfl
  have hDA12 : DifferentialAlgebra Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯ := ⟨fun a ↦ Subtype.ext rfl⟩
  have hconstP : ∀ P : (Cc⟮xE⟯)[X], P′ = 0 → ∃ e : Cc⟮xE⟯, P = C e := fun P hP ↦
    const_of_implicitDeriv_eq_zero η₁' hη₁nd hP
  have hK₂const : ∀ y : (Cc⟮xE⟯)⟮t1E⟯, y′ = 0 → ∃ b : Cc,
      y = algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯ (algebraMap Cc[X] Cc⟮xE⟯ (C b)) := fun y hy ↦ by
    have hyE : ((y : (Cc⟮xE⟯)⟮t1E⟯) : E)′ = 0 := congrArg Subtype.val hy
    refine ⟨⟨(y : E), hyE⟩, ?_⟩
    apply Subtype.ext
    change (y : E) = ((algebraMap Cc[X] Cc⟮xE⟯ (C (⟨(y : E), hyE⟩ : Cc)) : Cc⟮xE⟯) : E)
    rw [algebraMap_adjoinSimple, aeval_C]
    rfl
  have hEd₁ : toPoly Ed₁ ≠ 0 := by
    have h := hcη₁
    rw [rationalCheck, Bool.and_eq_true] at h
    exact ((hermiteCheck_iff _ _ _).mp h.1).1
  -- values of codes in `F₂`
  have hvalP : ∀ q : GPoly (GFrac R), algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯
      (GPoly.toPoly (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) q) = j (Tower.valP x₀ t₁ q) := fun q ↦ by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    change _ = j₀' (Tower.valP x₀ t₁ q)
    simp only [Tower.valP, map_sum, map_mul, map_pow, map_div₀, aeval_C, aeval_X,
      Tower.sem_M₁In, ev, hvalE]
    rfl
  have hM : Tower.ModelW (K₁ := Cc⟮xE⟯) (K₂ := (Cc⟮xE⟯)⟮t1E⟯) ι En₁ Ed₁ :=
    { hD := hD
      hKconst := hKconst₁
      hD₂ := fun _ ↦ rfl
      hconst₂ := hconstP
      hK₂const := fun y hy ↦ by
        obtain ⟨b, hb⟩ := hK₂const y hy
        exact ⟨b, by rw [hb, IsScalarTower.algebraMap_apply Cc⟮xE⟯ (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯,
          Polynomial.algebraMap_eq]⟩ }
  have hsemG : ∀ q : GFrac (GFrac R),
      (hM.cf ι hCc0).sem q = j (Tower.valG x₀ t₁ q) :=
    fun q ↦ by rw [Tower.sem_M₂W, hvalP, hvalP, Tower.valG, map_div₀]
  -- (3) `t₂ = exp a` is transcendental over `F₂`: `a′` has positive degree in `t₁`
  set M₁ := Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD with hM₁
  set ηc : GPoly (GFrac R) := GPoly.derivT (Tower.ops₁g R) [(En₁, Ed₁)] a with hηcdef
  set η₂'' : (Cc⟮xE⟯)⟮t1E⟯ := j (Tower.valP x₀ t₁ ηc) with hη₂''
  have hη₂'' : η₂'' = algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (GPoly.toPoly M₁ ηc) := (hvalP ηc).symm
  have htE0 : tE ≠ 0 := fun h ↦ ht0 ((map_eq_zero_iff ψ (algebraMap K E).injective).mp h)
  have htE'' : tE′ = algebraMap (Cc⟮xE⟯)⟮t1E⟯ E η₂'' * tE := by
    rw [htE, hψ, deriv_algebraMap, ht, map_mul]
    rfl
  have hDW : ∀ P : (Cc⟮xE⟯)[X], P′ = implicitDeriv (GPoly.toPoly M₁ [(En₁, Ed₁)]) P := fun P ↦ by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, hM₁, Tower.sem_M₁In]
    rfl
  have hder : ∀ P : (Cc⟮xE⟯)[X], (P′).natDegree ≤ P.natDegree := fun P ↦
    Tower.natDegree_implicitDeriv_C_le η₁' P
  have hnorm₂ : ∀ p : (Cc⟮xE⟯)[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive η₁' (fun _ ↦ rfl) hconstP hp
  have htηc : GPoly.trim (Tower.ops₁g R) ηc ≠ [] := fun h0 ↦ by rw [h0] at hηc; simp at hηc
  have hgdeg : 1 ≤ (GPoly.toPoly M₁ ηc).natDegree := by
    have := (GPoly.natDegree_toPoly_of_trim_ne_nil M₁ htηc).1
    omega
  have htr2 : Transcendental (Cc⟮xE⟯)⟮t1E⟯ tE :=
    transcendental_exp_arg (K₂ := (Cc⟮xE⟯)⟮t1E⟯) hder (GPoly.toPoly M₁ ηc) hgdeg htE0
      (by rw [htE'', hη₂''])
  -- (5) Liouville's theorem at the exponential step
  set fA : F₀ := ∑ j ∈ Finset.range (d + 1),
    aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j with hfA
  obtain ⟨e, m, d₀, he, hrel₀⟩ := liouville_step_exponential (F := (Cc⟮xE⟯)⟮t1E⟯) tE htr2 η₂''
    htE'' hconst2 s c' u (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) v (hcf _ hv)
    (j fA) (by
      change j₀' fA = _
      have h1 : j₀' fA = ψ (algebraMap F₀ K fA) := rfl
      rw [h1, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)
  -- absorb `(∑ cᵢ mᵢ) η₂` into the derivative
  set aP : (Cc⟮xE⟯)⟮t1E⟯ := j (Tower.valP x₀ t₁ a) with haP
  have haP' : aP′ = η₂'' := by
    rw [haP, ← hvalP, deriv_algebraMap, hDW, ← GPoly.toPoly_derivT, hvalP]
  have hc' : ∀ i ∈ s, (c' i)′ = 0 := fun i hi ↦ by
    simp only [c', dif_pos hi]
    exact Subtype.ext (hdata i hi).1
  set cst : (Cc⟮xE⟯)⟮t1E⟯ := ∑ i ∈ s, c' i * (m i : (Cc⟮xE⟯)⟮t1E⟯) with hcst
  have hcst' : cst′ = 0 := by
    rw [hcst, map_sum]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [Derivation.leibniz, hc' i hi, Derivation.map_intCast]
    simp
  have hrel : j fA = ∑ i ∈ s, c' i * logDeriv (e i) + (d₀ + cst * aP)′ := by
    rw [map_add, Derivation.leibniz, hcst', haP', hrel₀]
    simp only [smul_eq_mul, zero_mul, add_zero]
    ring
  let c₁ : κ → Cc⟮xE⟯ := fun i ↦
    if hi : i ∈ s then algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩ else 0
  have hc₁ : ∀ i ∈ s, algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (C (c₁ i)) = c' i := fun i hi ↦ by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, aeval_C]
    simp only [c₁, c', dif_pos hi]
    rfl
  set Apoly : (Cc⟮xE⟯)[X] := ∑ i ∈ Finset.range (d + 1),
    C (ev Cc⟮xE⟯ ι (A i, D i)) * X ^ i with hApoly
  have hjA : j fA = algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ Apoly := by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple]
    change j₀' fA = _
    simp only [hfA, hApoly, map_sum, map_mul, map_pow, map_div₀, aeval_C, aeval_X, ev, hvalE]
    rfl
  have hliou : algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ Apoly =
      ∑ i ∈ s, algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (C (c₁ i)) * logDeriv (e i) +
        (d₀ + cst * aP)′ := by
    rw [← hjA, hrel, Finset.sum_congr rfl fun i hi ↦ by rw [← hc₁ i hi]]
  obtain ⟨p, hpe, hpd⟩ := exists_coeffs_of_liouville_primitive (K := (Cc⟮xE⟯)⟮t1E⟯) η₁'
    (fun _ ↦ rfl) hconstP s c₁ e he _ _ hliou
  have hcoeffA : ∀ i, i ≤ d → Apoly.coeff i = ev Cc⟮xE⟯ ι (A i, D i) := fun i hi ↦ by
    simp only [hApoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h'
      exact absurd (Finset.mem_range.mpr (by omega)) h'
  have hdegA : Apoly.natDegree ≤ d := by
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.mp hi; omega)
  obtain ⟨b, hb⟩ := hKconst₁ _ (hpd d hdegA)
  refine primLoop_complete (K := Cc⟮xE⟯) ι hD hKconst₁ hcη₁ hEd₁ hη₁0 A D p d
    (fun i _ hi ↦ hD0 i hi) (fun i h1 h2 ↦ ?_) ([], [1]) (by simp) b ?_ hnone
  · have := hpe i h1
    rw [hcoeffA i h2] at this
    exact this
  · rw [hb]
    simp [ev]

/-- **Polynomials in `t₁` under an exponential: decided by `primLoop`.** -/
theorem expArgPrimBase_decides {K : Type*} [Field K] [Algebra F₀ K] [Algebra R K]
    [IsScalarTower R F₀ K] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]
    (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (a : GPoly (GFrac R))
    (hηc : 2 ≤ (GPoly.trim (Tower.ops₁g R) (GPoly.derivT (Tower.ops₁g R) [(En₁, Ed₁)] a)).length)
    (t : K) (ht0 : t ≠ 0) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K
      (Tower.valP x₀ t₁ (GPoly.derivT (Tower.ops₁g R) [(En₁, Ed₁)] a)) * t)
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (d : ℕ) (A D : ℕ → CPoly R) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) :
    HasElementaryIntegral (algebraMap F₀ K (∑ j ∈ Finset.range (d + 1),
        aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j)) ↔
      (primLoop En₁ Ed₁ Iη₁ A D d ([], [1])).isSome = true := by
  constructor
  · intro h
    by_contra hnone
    rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnone
    obtain ⟨E, _, _, _, _, hE, g, hg⟩ := h
    exact not_elementary_expArgPrimBase hR x₀ t₁ hx₀ En₁ Ed₁ ht₁ hgen₀ a hηc t ht0 hgen ht Iη₁ hcη₁
      hη₁0 d A D hD0 hnone E hE g hg
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
