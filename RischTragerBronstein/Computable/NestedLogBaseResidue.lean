import RischTragerBronstein.Computable.Prim2PolyWStrong
import RischTragerBronstein.Computable.Prim2BaseResidue

/-!
# Nested logarithm `t₂ = log u`, `u ∈ R(x)(t₁)`: level `0`, simple poles — the negative answer

For `α = Ap(t₁) + b(t₁) / s(t₁) ∈ R(x)(t₁)` viewed in `K = R(x)(t₁)(t₂)` with `t₂′ = W = u′ / u`
(certified on codes): if the residue test at `t₁` fails, `α` has no elementary integral over `K`.
Liouville's theorem at `t₂` leaves `α - c₀ W`, and `c₀ W = c₀ u′ / u` is itself a logarithmic
derivative — one more term of the Liouville sum over `C'(x)(t₁)`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R F₀ K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K]

set_option maxHeartbeats 3200000 in
theorem not_elementary_nestedLogBaseResidue (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (W U : GFrac (GFrac R))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (Tower.valG x₀ t₁ W))
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (hW0 : GPoly.isZero (Tower.ops₁g R) W.2 = false)
    (hWnd : Tower.isDerivPrim En₁ Ed₁ Iη₁ W.1 W.2 = false)
    (hU0 : (Tower.ops₂p En₁ Ed₁).isZero U = false)
    (hlog : (Tower.ops₂p En₁ Ed₁).isZero ((Tower.ops₂p En₁ Ed₁).add
      ((Tower.ops₂p En₁ Ed₁).mul W U)
      ((Tower.ops₂p En₁ Ed₁).neg ((Tower.ops₂p En₁ Ed₁).deriv U))) = true)
    (Ap bc sc : GPoly (GFrac R))
    (hsqc : GPoly.squarefreeCheck (Tower.ops₁g R) sc = true)
    (hcopc : GPoly.coprimeDerivCheck (Tower.ops₁g R) [(En₁, Ed₁)] sc = true)
    (hres : GPoly.residueCheck (Tower.ops₁g R) [(En₁, Ed₁)] bc sc = false)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    [CharZero K] (hE : IsElementaryExtension K E) (g : E) :
    g′ ≠ algebraMap K E (algebraMap F₀ K
      (Tower.valP x₀ t₁ Ap + Tower.valP x₀ t₁ bc / Tower.valP x₀ t₁ sc)) := by
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
  set t1E := j₀ t₁ with ht1E
  have hη₁E : algebraMap Cc⟮xE⟯ E η₁' =
      j₀ (aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁)) := by
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
    change _ = j₀ (Tower.valP x₀ t₁ q)
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
  -- (3) `t₂` is transcendental over `F₂`: `W` is not a derivative
  set η₂'' : (Cc⟮xE⟯)⟮t1E⟯ := j (Tower.valG x₀ t₁ W) with hη₂''
  have htE'' : tE′ = algebraMap (Cc⟮xE⟯)⟮t1E⟯ E η₂'' := by
    rw [htE, hψ, deriv_algebraMap, ht]
    rfl
  have hW0' : GPoly.toPoly (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) W.2 ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) W.2).mpr hz] at hW0
    exact Bool.noConfusion hW0
  have hη₂nd : ∀ y : (Cc⟮xE⟯)⟮t1E⟯, y′ ≠ η₂'' := fun y hy ↦ by
    have := Tower.isDerivPrim_complete (K₁ := Cc⟮xE⟯) (K₂ := (Cc⟮xE⟯)⟮t1E⟯) ι hCc0 hD hKconst₁
      hcη₁ hEd₁ hη₁0 (fun _ ↦ rfl) hconstP W.1 W.2 hW0' y (by
        rw [hy, hη₂'', ← hsemG, Tower.sem_M₂W])
    rw [hWnd] at this
    exact Bool.noConfusion this
  have htr2 : Transcendental (Cc⟮xE⟯)⟮t1E⟯ tE := transcendental_primitive η₂'' htE'' hη₂nd
  -- (5) Liouville's theorem at `t₂`
  set fA : F₀ := Tower.valP x₀ t₁ Ap + Tower.valP x₀ t₁ bc / Tower.valP x₀ t₁ sc with hfA
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
  -- `W = u′ / u`
  set uF : (Cc⟮xE⟯)⟮t1E⟯ := (hM.cf ι hCc0).sem U with huF
  have huF0 : uF ≠ 0 := fun h0 ↦ by
    rw [((hM.cf ι hCc0).isZero_iff U).mpr h0] at hU0
    exact Bool.noConfusion hU0
  have hlogF : η₂'' = logDeriv uF := by
    have := ((hM.cf ι hCc0).isZero_iff _).mp hlog
    rw [CField.sem_add, CField.sem_neg, CField.sem_mul, CField.sem_deriv, hsemG W] at this
    rw [logDeriv, eq_div_iff huF0]
    linear_combination this
  -- (6) the residue test over `F₁ = C'(x)` at the step `t₁`
  have hc₀E : ((c₀ : (Cc⟮xE⟯)⟮t1E⟯) : E)′ = 0 := congrArg Subtype.val hc₀
  set cc : Cc := ⟨(c₀ : E), hc₀E⟩ with hcc
  have hcst : algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (C (algebraMap Cc Cc⟮xE⟯ cc)) = c₀ := by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, aeval_C]
    rfl
  let c₁ : Option κ → Cc⟮xE⟯ := fun o ↦ match o with
    | none => algebraMap Cc Cc⟮xE⟯ cc
    | some i => if hi : i ∈ s then algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩ else 0
  let e₁ : Option κ → (Cc⟮xE⟯)⟮t1E⟯ := fun o ↦ match o with
    | none => uF
    | some i => e i
  have hc₁ : ∀ i ∈ s, algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (C (c₁ (some i))) = c' i :=
    fun i hi ↦ by
      apply Subtype.ext
      rw [algebraMap_adjoinSimple, aeval_C]
      simp only [c₁, c', dif_pos hi]
      rfl
  have hc₁' : ∀ o ∈ Finset.insertNone s, (c₁ o)′ = 0 := fun o ho ↦ by
    cases o with
    | none => exact Subtype.ext hc₀E
    | some i =>
      have hi : i ∈ s := Finset.some_mem_insertNone.mp ho
      simp only [c₁, dif_pos hi]
      exact Subtype.ext (hdata i hi).1
  have he₁ : ∀ o ∈ Finset.insertNone s, e₁ o ≠ 0 := fun o ho ↦ by
    cases o with
    | none => exact huF0
    | some i => exact he i (Finset.some_mem_insertNone.mp ho)
  set M₁ := Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD with hM₁
  set Sp := GPoly.toPoly M₁ sc with hSp
  have hsq : Squarefree Sp := GPoly.squarefreeCheck_sound M₁ hsqc
  have hS0 : Sp ≠ 0 := hsq.ne_zero
  have hWη : GPoly.toPoly M₁ [(En₁, Ed₁)] = C η₁' := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, hM₁, Tower.sem_M₁In]
    rfl
  have hcop := GPoly.coprimeDerivCheck_sound M₁ hcopc
  have hr := GPoly.residuePoly_spec M₁ [(En₁, Ed₁)] bc sc hS0 hcop
  rw [hWη] at hr
  set Bp : (Cc⟮xE⟯)[X] := GPoly.toPoly M₁ Ap * Sp + GPoly.toPoly M₁ bc with hBp
  have hr' : Sp ∣ GPoly.toPoly M₁ (GPoly.residuePoly (Tower.ops₁g R) [(En₁, Ed₁)] bc sc) * Sp′ -
      Bp := by
    have hS' : Sp′ = implicitDeriv (C η₁') Sp := rfl
    rw [hS', hBp]
    have : ∀ r' : (Cc⟮xE⟯)[X], r' * implicitDeriv (C η₁') Sp -
        (GPoly.toPoly M₁ Ap * Sp + GPoly.toPoly M₁ bc) =
        (r' * implicitDeriv (C η₁') Sp - GPoly.toPoly M₁ bc) - GPoly.toPoly M₁ Ap * Sp :=
      fun r' ↦ by ring
    rw [this]
    exact dvd_sub hr (dvd_mul_left _ _)
  have hinj₂ : Function.Injective (algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯) :=
    IsFractionRing.injective _ _
  have hφS : algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ Sp ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hS0
  have hliou : algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ Bp /
      algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ Sp =
      ∑ o ∈ Finset.insertNone s,
        algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (C (c₁ o)) * logDeriv (e₁ o) + d₀′ := by
    have hjα : j fA = algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (GPoly.toPoly M₁ Ap) +
        algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (GPoly.toPoly M₁ bc) /
          algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ Sp := by
      rw [hfA, map_add, map_div₀, hvalP, hvalP, hvalP]
    rw [hBp, map_add, map_mul, add_div, mul_div_assoc, div_self hφS, mul_one,
      Finset.sum_insertNone, Finset.sum_congr rfl fun i hi ↦ by rw [hc₁ i hi]]
    change _ = algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (C (algebraMap Cc Cc⟮xE⟯ cc)) * logDeriv uF +
      ∑ i ∈ s, c' i * logDeriv (e i) + d₀′
    rw [hcst, ← hlogF]
    have := hrel₀
    rw [hjα] at this
    linear_combination this
  have hdvd := dvd_residueTest (K := (Cc⟮xE⟯)⟮t1E⟯) hsq
    (fun p hp _ ↦ not_dvd_deriv_of_irreducible_primitive η₁' (fun _ ↦ rfl) hconstP hp) hr'
    (Finset.insertNone s) c₁ hc₁' e₁ he₁ d₀ hliou
  have := (GPoly.residueCheck_iff M₁ [(En₁, Ed₁)] bc sc hS0).mpr hdvd
  rw [hres] at this
  exact Bool.noConfusion this

end CPoly
