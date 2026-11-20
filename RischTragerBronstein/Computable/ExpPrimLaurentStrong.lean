import RischTragerBronstein.Computable.Prim2PolyWStrong
import RischTragerBronstein.Computable.RDEPrimComplete
import RischTragerBronstein.Computable.ExpLaurentRat
import RischTragerBronstein.Liouville.StepExponentialLaurent

/-!
# An exponential over `R(x)(t₁)`: Laurent polynomials in `t₂ = exp a`, the negative answer

`K = R(x)(t₁)(t₂)`, `t₁′ = η₁ ∈ R(x)`, `t₂ = exp a(x)` with `a ∈ R[x]` non-constant. For a Laurent
polynomial `∑_{j ≠ n} Aⱼ t₂^{j-n}` (`Aⱼ ∈ R(x)(t₁)` codes) plus a level-0 part: if the Risch
differential equation `y′ + (j₀ - n) a′ y = A_{j₀}` has no solution in `R(x)(t₁)` (`rdePrim`), the
integrand has no elementary integral over `K`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R F₀ K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K]

set_option maxHeartbeats 3200000 in
theorem not_elementary_expPrimLaurent (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (En₁ Ed₁ : CPoly R)
    (ht₁ : t₁′ = aeval x₀ (toPoly En₁) / aeval x₀ (toPoly Ed₁))
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (a : CPoly R) (ha : trim (deriv a) ≠ [])
    (t : K) (ht0 : t ≠ 0) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (aeval x₀ (derivative (toPoly a))) * t)
    (Iη₁ : RationalIntegral R) (hcη₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hη₁0 : isZero Iη₁.r = false)
    (N n : ℕ) (A : ℕ → GFrac (GFrac R)) (A₀ : F₀)
    (hD0 : ∀ j < N, GPoly.isZero (Tower.ops₁g R) (A j).2 = false)
    (j₀ : ℕ) (hj₀ : j₀ < N) (hj₀n : j₀ ≠ n)
    (hnone : Tower.rdePrim En₁ Ed₁ (expCoeffZ a ((j₀ : ℤ) - n)) (A j₀).1 (A j₀).2 = none)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    [CharZero K] (hE : IsElementaryExtension K E) (g : E) :
    g′ ≠ algebraMap K E (algebraMap F₀ K A₀ + ∑ j ∈ (Finset.range N).erase n,
      algebraMap F₀ K (Tower.valG x₀ t₁ (A j)) * t ^ j / t ^ n) := by
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
  -- (3) `t₂ = exp a` is transcendental over `F₂`
  set A' : Cc[X] := (derivative (toPoly a)).map ι with hA'
  have hA'0 : A' ≠ 0 := by
    rw [hA', Ne, Polynomial.map_eq_zero_iff ι.injective, ← toPoly_deriv]
    exact fun h ↦ ha ((trim_eq_nil_iff _).mpr h)
  set η₂' : Cc⟮xE⟯ := algebraMap Cc[X] Cc⟮xE⟯ A' with hη₂'
  set η₂'' : (Cc⟮xE⟯)⟮t1E⟯ := algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯ η₂' with hη₂''
  have htE0 : tE ≠ 0 := fun h ↦ ht0 ((map_eq_zero_iff ψ (algebraMap K E).injective).mp h)
  have hη₂E : algebraMap (Cc⟮xE⟯)⟮t1E⟯ E η₂'' = j₀' (aeval x₀ (derivative (toPoly a))) := by
    change ((η₂' : Cc⟮xE⟯) : E) = _
    rw [hη₂', algebraMap_adjoinSimple, hA', hι]
  have htE'' : tE′ = algebraMap (Cc⟮xE⟯)⟮t1E⟯ E η₂'' * tE := by
    rw [htE, hψ, deriv_algebraMap, ht, hη₂E, map_mul]
    rfl
  have hgnl₁ : ∀ (m : ℕ), m ≠ 0 → ∀ e : Cc⟮xE⟯, e ≠ 0 → e′ + -(m * η₂') * e ≠ 0 :=
    fun m hm e he h ↦ he (rde_homogeneous' (K := Cc⟮xE⟯) hD (-(C (m : Cc) * A'))
      (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hm)) hA'0)) e (by
        rw [map_neg, map_mul, ← hη₂']
        have : algebraMap Cc[X] Cc⟮xE⟯ (C (m : Cc)) = (m : Cc⟮xE⟯) := by
          rw [show (C (m : Cc) : Cc[X]) = (m : Cc[X]) from map_natCast C m, map_natCast]
        rw [this]
        linear_combination h))
  have hnorm₂ : ∀ p : (Cc⟮xE⟯)[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive η₁' (fun _ ↦ rfl) hconstP hp
  have htr2 : Transcendental (Cc⟮xE⟯)⟮t1E⟯ tE := by
    refine transcendental_exponential η₂'' htE0 htE'' fun m hm b hb ↦ ?_
    refine eq_zero_of_rde_homogeneous (K := (Cc⟮xE⟯)⟮t1E⟯) hnorm₂ η₁' (-(m * η₂'))
      (fun _ ↦ rfl) (hgnl₁ m hm) b ?_
    rw [hb, hη₂'', IsScalarTower.algebraMap_apply Cc⟮xE⟯ (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯,
      Polynomial.algebraMap_eq, C_neg, C_mul, map_neg, map_mul, map_natCast (C : Cc⟮xE⟯ →+* _),
      map_natCast]
    ring
  -- (5) the Laurent step
  let fr : GFrac (GFrac R) → (Cc⟮xE⟯)⟮t1E⟯ := fun q ↦ j (Tower.valG x₀ t₁ q)
  let Ap : ((Cc⟮xE⟯)⟮t1E⟯)[X] := C (j A₀) * X ^ n +
    ∑ k ∈ (Finset.range N).erase n, C (fr (A k)) * X ^ k
  have htn : tE ^ n ≠ 0 := pow_ne_zero _ htE0
  have hjE : ∀ f : F₀, algebraMap (Cc⟮xE⟯)⟮t1E⟯ E (j f) = ψ (algebraMap F₀ K f) := fun f ↦ rfl
  have hAp : aeval tE Ap / tE ^ n = ψ (algebraMap F₀ K A₀ + ∑ k ∈ (Finset.range N).erase n,
      algebraMap F₀ K (Tower.valG x₀ t₁ (A k)) * t ^ k / t ^ n) := by
    simp only [Ap, map_add, map_sum, map_mul, map_pow, aeval_C, aeval_X, hjE, fr]
    rw [add_div, Finset.sum_div, mul_div_assoc, div_self htn, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [map_div₀, map_mul, map_pow]
    rfl
  have hcoeff : Ap.coeff j₀ = fr (A j₀) := by
    simp only [Ap, coeff_add, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [if_neg hj₀n, mul_zero, zero_add, Finset.sum_eq_single j₀]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h'
      exact absurd (Finset.mem_erase.mpr ⟨hj₀n, Finset.mem_range.mpr hj₀⟩) h'
  obtain ⟨y, hy⟩ := (rde_step_exponential_laurent (F := (Cc⟮xE⟯)⟮t1E⟯) tE htr2 η₂'' htE'' hconst2
    s c' u (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) v (hcf _ hv) Ap n (by
      rw [hAp, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)).1 j₀ hj₀n
  rw [hcoeff] at hy
  -- (6) `rdePrim` is complete
  have hz : (((j₀ : ℤ) - n : ℤ) : R) ≠ 0 :=
    Int.cast_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hj₀n))
  have hg0 : toPoly (expCoeffZ a ((j₀ : ℤ) - n)) ≠ 0 := by
    rw [expCoeffZ, toPoly_smul]
    exact mul_ne_zero (C_ne_zero.mpr hz) fun h0 ↦ ha ((trim_eq_nil_iff _).mpr h0)
  have hA0' : GPoly.toPoly (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) (A j₀).2 ≠ 0 := fun hz' ↦ by
    have := hD0 j₀ hj₀
    rw [(GPoly.isZero_iff (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) _).mpr hz'] at this
    exact Bool.noConfusion this
  have hsome := Tower.rdePrim_complete (K₁ := Cc⟮xE⟯) (K₂ := (Cc⟮xE⟯)⟮t1E⟯) ι hCc0 hD
    (fun _ ↦ rfl) hconstP (expCoeffZ a ((j₀ : ℤ) - n)) hg0 (A j₀).1 (A j₀).2 hA0' y (by
      rw [← Tower.sem_M₂W (K₂ := (Cc⟮xE⟯)⟮t1E⟯) ι hCc0 hD (fun _ ↦ rfl), hsemG]
      change _ = fr (A j₀)
      rw [← hy]
      congr 2
      rw [expCoeffZ, toPoly_smul, toPoly_deriv, Polynomial.map_mul, map_C, map_mul, ← hA',
        ← hη₂', hη₂'', IsScalarTower.algebraMap_apply Cc⟮xE⟯ (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯,
        Polynomial.algebraMap_eq, map_mul]
      have hcast : algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (C (algebraMap Cc[X] Cc⟮xE⟯
          (C (ι (((j₀ : ℤ) - n : ℤ) : R))))) = (j₀ : (Cc⟮xE⟯)⟮t1E⟯) - n := by
        simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
      rw [map_mul, hcast])
  rw [hnone] at hsome
  exact Bool.noConfusion hsome

end CPoly
