import RischTragerBronstein.Computable.PrimResidueStrong
import RischTragerBronstein.Computable.ExpPolyRat
import RischTragerBronstein.Computable.RDERationalG
import RischTragerBronstein.Computable.HyperexpWCert
import RischTragerBronstein.Liouville.StepResidueTestExp

/-!
# Simple poles in a hyperexponential `t′ = η t`, `η ∈ R(x)`: the negative answer

`F₀ = R(x₀)`, `K = F₀(t)`, `t′ = η t`, `η = Gn / Gd` in lowest terms, arbitrary, with the monomial
certificate `hyperexpMonomialCheck Gn Gd μ`. Let `sd ∈ F₀[t]` be squarefree with
`t ∤ sd`, and let the integrand be `B / (sd t ^ k)` with `B ≡ b t ^ k (mod sd)`; `r` a residue
polynomial of `b / sd`. If the residue test fails, the integrand has **no elementary integral** over
`K` — with no assumption on constants.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R F₀ K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [HasRatRoots R]

theorem not_elementary_hyperexpResidueW (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ : F₀) (hx₀ : x₀′ = 1) (hgen₀ : adjoin R {x₀} = (⊤ : IntermediateField R F₀))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht0 : t ≠ 0) (Gn Gd μ : CPoly R)
    (hGn0 : toPoly Gn ≠ 0) (hGd0 : toPoly Gd ≠ 0) (hcop : IsCoprime (toPoly Gn) (toPoly Gd))
    (hcert : hyperexpMonomialCheck Gn Gd μ = true)
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd)) * t)
    (Bn b sd r : F₀[X]) (k : ℕ) (hsd : Squarefree sd) (hX : ¬X ∣ sd) (hBn : sd ∣ Bn - b * X ^ k)
    (hr : sd ∣ r * (mapCoeffs sd +
      C (aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd)) * X * derivative sd) - b)
    (hT : ¬sd ∣ residueTest r sd)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    [CharZero K] (hE : IsElementaryExtension K E) (g : E) :
    g′ ≠ algebraMap K E (aeval t Bn / (aeval t sd * t ^ k)) := by
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
  -- `F₀ = R(x₀)` maps into `F₁`
  have hF₀ : ∀ f : F₀, j₀ f ∈ Cc⟮xE⟯ := by
    let T₀ : IntermediateField R F₀ :=
      { carrier := {f | j₀ f ∈ Cc⟮xE⟯}
        mul_mem' := fun {k l} hk hl ↦ by
          change j₀ (k * l) ∈ Cc⟮xE⟯; rw [map_mul]; exact mul_mem hk hl
        one_mem' := by change j₀ 1 ∈ Cc⟮xE⟯; rw [map_one]; exact one_mem _
        add_mem' := fun {k l} hk hl ↦ by
          change j₀ (k + l) ∈ Cc⟮xE⟯; rw [map_add]; exact add_mem hk hl
        zero_mem' := by change j₀ 0 ∈ Cc⟮xE⟯; rw [map_zero]; exact zero_mem _
        algebraMap_mem' := fun r ↦ (Cc⟮xE⟯).algebraMap_mem (ι r)
        inv_mem' := fun k hk ↦ by
          change j₀ k⁻¹ ∈ Cc⟮xE⟯; rw [map_inv₀]; exact inv_mem hk }
    have hT₀ : T₀ = ⊤ := by
      rw [eq_top_iff, ← hgen₀, adjoin_le_iff]
      rintro k rfl
      exact mem_adjoin_simple_self Cc xE
    intro f
    have : f ∈ T₀ := hT₀ ▸ IntermediateField.mem_top
    exact this
  let j : F₀ →+* Cc⟮xE⟯ := j₀.codRestrict _ hF₀
  have hjE : ∀ f : F₀, algebraMap Cc⟮xE⟯ E (j f) = j₀ f := fun _ ↦ rfl
  have hj : ∀ a : F₀, j a′ = (j a)′ := fun a ↦ Subtype.ext (hj₀' a).symm
  have hval : ∀ P : R[X], algebraMap Cc[X] Cc⟮xE⟯ (P.map ι) = j (aeval x₀ P) := fun P ↦ by
    apply Subtype.ext
    exact (algebraMap_adjoinSimple xE _).trans (hι _ x₀)
  set η₀ : F₀ := aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd) with hη₀
  set η₁ : Cc⟮xE⟯ := j η₀ with hη₁
  have hη₁' : η₁ = algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Gn).map ι) /
      algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Gd).map ι) := by
    rw [hη₁, hη₀, map_div₀, hval, hval]
  have htE0 : tE ≠ 0 := (map_ne_zero ψ).mpr ht0
  have htE'' : tE′ = algebraMap Cc⟮xE⟯ E η₁ * tE := by
    rw [htE, hψ, deriv_algebraMap, ht, map_mul]
    rfl
  have hGnS : (toPoly Gn).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hGn0
  have hGdS : (toPoly Gd).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hGd0
  have hcopS : IsCoprime ((toPoly Gn).map ι) ((toPoly Gd).map ι) := hcop.map (mapRingHom ι)
  -- (2) `t` is transcendental over `C'(x)`
  have htrt : Transcendental Cc⟮xE⟯ tE := by
    refine transcendental_exponential η₁ htE0 htE'' fun m hm y hy ↦ ?_
    refine hyperexpW_homogeneous (K := Cc⟮xE⟯) ι hD hGn0 hGd0 hcop hcert (m : ℤ)
      (by exact_mod_cast hm) y ?_
    have : algebraMap Cc[X] Cc⟮xE⟯ (C (((m : ℕ) : ℤ) : Cc)) = (m : Cc⟮xE⟯) := by
      rw [Int.cast_natCast, show (C (m : Cc) : Cc[X]) = (m : Cc[X]) from map_natCast C m,
        map_natCast]
    rw [hy, this, ← hη₁']
  -- (3) all constants of `E` lie in `F₁`
  have hconst1 : ∀ z ∈ (Cc⟮xE⟯)⟮tE⟯, z′ = 0 → z ∈ Set.range (algebraMap Cc⟮xE⟯ E) :=
    fun z _ hz ↦ ⟨algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩, rfl⟩
  -- (4) the strong Liouville theorem
  obtain ⟨κ, s, c, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g hg
  -- `K(Const E) ⊆ F₁(t)`
  set B : IntermediateField Cc⟮xE⟯ E := (Cc⟮xE⟯)⟮tE⟯ with hB
  have hBconst : ∀ z : E, z′ = 0 → z ∈ B := fun z hz ↦
    B.algebraMap_mem (algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩)
  have hBt : tE ∈ B := mem_adjoin_simple_self _ tE
  let T : IntermediateField F₀ K :=
    { carrier := {k | ψ k ∈ B}
      mul_mem' := fun {k l} hk hl ↦ by
        change ψ (k * l) ∈ B; rw [map_mul]; exact mul_mem hk hl
      one_mem' := by change ψ 1 ∈ B; rw [map_one]; exact one_mem _
      add_mem' := fun {k l} hk hl ↦ by
        change ψ (k + l) ∈ B; rw [map_add]; exact add_mem hk hl
      zero_mem' := by change ψ 0 ∈ B; rw [map_zero]; exact zero_mem _
      algebraMap_mem' := fun f ↦ B.algebraMap_mem (j f)
      inv_mem' := fun k hk ↦ by
        change ψ k⁻¹ ∈ B; rw [map_inv₀]; exact inv_mem hk }
  have hT' : T = ⊤ := by
    rw [eq_top_iff, ← hgen, adjoin_le_iff]
    rintro k rfl
    exact hBt
  have hKB : ∀ k : K, ψ k ∈ B := fun k ↦ by
    have : k ∈ T := hT' ▸ IntermediateField.mem_top
    exact this
  have hcf : ∀ z ∈ constField K E, z ∈ B := by
    let N : IntermediateField K E := { B.toSubfield with algebraMap_mem' := hKB }
    have : constField K E ≤ N := adjoin_le_iff.mpr fun z hz ↦ hBconst z hz
    exact fun z hz ↦ this hz
  -- (5) the residue test over `C'(x)`
  let c' : κ → Cc⟮xE⟯ := fun i ↦
    if hi : i ∈ s then algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩ else 0
  have hc' : ∀ i ∈ s, (c' i)′ = 0 := fun i hi ↦ by
    simp only [c', dif_pos hi]
    exact Subtype.ext (hdata i hi).1
  have haev : ∀ P : F₀[X], aeval tE (P.map j) = ψ (aeval t P) := fun P ↦ by
    rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
    rfl
  have hsd₁ : Squarefree (sd.map j) :=
    ((PerfectField.separable_iff_squarefree.mpr hsd).map).squarefree
  have hr₁ : sd.map j ∣ r.map j * (mapCoeffs (sd.map j) + C η₁ * X * derivative (sd.map j)) -
      b.map j := by
    have := Polynomial.map_dvd j hr
    rwa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, map_C, map_X, mapCoeffs_map j hj, ← derivative_map] at this
  have hX₁ : ¬X ∣ sd.map j := fun hd ↦ hX (by
    rwa [← Polynomial.map_X j, Polynomial.map_dvd_map' j] at hd)
  have hB₁ : sd.map j ∣ Bn.map j - b.map j * X ^ k := by
    have := Polynomial.map_dvd j hBn
    rwa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X] at this
  have hdvd := residueTest_step_exponential (F := Cc⟮xE⟯) tE htrt η₁ htE'' hconst1 s c' u
    (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) hc' v (hcf _ hv) (Bn.map j) (b.map j)
    (sd.map j) (r.map j) k hsd₁ hX₁ hB₁ hr₁ (by
      rw [haev, haev, ← map_pow, ← map_mul, ← map_div₀, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)
  rw [← residueTest_map j hj, Polynomial.map_dvd_map' j] at hdvd
  exact hT hdvd

/-- If the residue test fails, `B / (sd t ^ k)` has no elementary integral. -/
theorem not_hasElementaryIntegral_hyperexpResidueW {K : Type*} [Field K] [Algebra F₀ K] [Algebra R K]
    [IsScalarTower R F₀ K] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]
    (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ : F₀) (hx₀ : x₀′ = 1) (hgen₀ : adjoin R {x₀} = (⊤ : IntermediateField R F₀))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht0 : t ≠ 0) (Gn Gd μ : CPoly R)
    (hGn0 : toPoly Gn ≠ 0) (hGd0 : toPoly Gd ≠ 0) (hcop : IsCoprime (toPoly Gn) (toPoly Gd))
    (hcert : hyperexpMonomialCheck Gn Gd μ = true)
    (ht : t′ = algebraMap F₀ K (aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd)) * t)
    (B b sd r : F₀[X]) (k : ℕ) (hsd : Squarefree sd) (hX : ¬X ∣ sd) (hB : sd ∣ B - b * X ^ k)
    (hr : sd ∣ r * (mapCoeffs sd +
      C (aeval x₀ (toPoly Gn) / aeval x₀ (toPoly Gd)) * X * derivative sd) - b)
    (hT : ¬sd ∣ residueTest r sd) :
    ¬HasElementaryIntegral (aeval t B / (aeval t sd * t ^ k)) := by
  rintro ⟨E, _, _, _, _, hE, g, hg⟩
  exact not_elementary_hyperexpResidueW hR x₀ hx₀ hgen₀ t hgen ht0 Gn Gd μ hGn0 hGd0 hcop hcert ht
    B b sd r k hsd hX hB hr hT E hE g hg

end CPoly
