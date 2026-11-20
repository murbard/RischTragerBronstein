import RischTragerBronstein.Computable.ExpHexpLaurentStrong
import RischTragerBronstein.Computable.RDENonCancelHexp
import RischTragerBronstein.RDE.ExpArgConstants

/-!
# An exponential with argument in the tower over `R(x)(t₁)`: Laurent polynomials, the negative answer

`K = R(x)(t₁)(t₂)`, `t₁′ = η t₁`, `t₂ = exp a` with `a ∈ R(x)[t₁]`, `a′ = ηc` of positive
`t₁`-degree (`e^{eˣ}`, `exp (x eˣ)`, …). For a Laurent polynomial
`∑_{j ≠ n} Aⱼ t₂^{j-n}` plus a level-0 part: if the non-cancellation Risch equation
`y′ + (j₀ - n) a′ y = A_{j₀}` has no solution in `R(x)(t₁)` (`rdeNCHexpB`), the integrand has no
elementary integral over `K`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R F₀ K : Type*} [Field R] [DecidableEq R] [CharZero R] [HasNatTest R] [Field F₀]
variable [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K]
variable [CPoly.HasRatRoots R] [HasNatTest R]

set_option maxHeartbeats 3200000 in
theorem not_elementary_expArgHexpLaurent (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (Hn Hd μ : CPoly R) (hHn0 : toPoly Hn ≠ 0) (hHd0 : toPoly Hd ≠ 0)
    (hcop : IsCoprime (toPoly Hn) (toPoly Hd)) (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd) * t₁)
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (a : GPoly (GFrac R)) (hηc : 2 ≤ (GPoly.trim (Tower.ops₁g R) (GPoly.derivT (Tower.ops₁g R) (Tower.hexpW Hn Hd) a)).length)
    (t : K) (ht0 : t ≠ 0) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (Tower.valP x₀ t₁ (GPoly.derivT (Tower.ops₁g R) (Tower.hexpW Hn Hd) a)) * t)
    (N n : ℕ) (A : ℕ → GFrac (GFrac R)) (A₀ : F₀)
    (hD0 : ∀ j < N, GPoly.isZero (Tower.ops₁g R) (A j).2 = false)
    (j₀ : ℕ) (hj₀ : j₀ < N) (hj₀n : j₀ ≠ n)
    (hnone : Tower.rdeNCHexpB Hn Hd (Tower.normFrac (GPoly.coeffAt (Tower.ops₁g R) a 0)) ((j₀ : ℤ) - n) (GPoly.smul (Tower.ops₁g R) (Tower.constZ ((j₀ : ℤ) - n)) (GPoly.derivT (Tower.ops₁g R) (Tower.hexpW Hn Hd) a))
      (A j₀).1 (A j₀).2 = none)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    [CharZero K] (hE : IsElementaryExtension K E) (g : E) :
    g′ ≠ algebraMap K E (algebraMap F₀ K A₀ + ∑ j ∈ (Finset.range N).erase n,
      algebraMap F₀ K (Tower.valG x₀ t₁ (A j)) * t ^ j / t ^ n) := by
  intro hg
  classical
  set ηc := GPoly.derivT (Tower.ops₁g R) (Tower.hexpW Hn Hd) a with hηcdef
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
  set η₁' : Cc⟮xE⟯ := algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Hn).map ι) /
    algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Hd).map ι) with hη₁'
  set t1E := j₀' t₁ with ht1E
  have hη₁E : algebraMap Cc⟮xE⟯ E η₁' = j₀' (aeval x₀ (toPoly Hn) / aeval x₀ (toPoly Hd)) := by
    rw [hη₁', map_div₀, hvalE, hvalE, map_div₀]
  have ht1E' : t1E′ = algebraMap Cc⟮xE⟯ E η₁' * t1E := by
    rw [ht1E, hj₀', ht₁, hη₁E, map_mul]
  have ht1E0 : t1E ≠ 0 := fun h ↦ ht₁0 ((map_eq_zero_iff j₀' j₀'.injective).mp h)
  -- (2) `t₁` is transcendental over `F₁`
  have htr1 : Transcendental Cc⟮xE⟯ t1E := by
    refine transcendental_exponential η₁' ht1E0 ht1E' fun n hn b hb ↦ ?_
    refine CPoly.hyperexpW_homogeneous (K := Cc⟮xE⟯) ι hD hHn0 hHd0 hcop hcert (n : ℤ)
      (by exact_mod_cast hn) b (by
        rw [hb, hη₁', show algebraMap Cc[X] Cc⟮xE⟯ (C (((n : ℕ) : ℤ) : Cc)) = (n : Cc⟮xE⟯) by
          rw [Int.cast_natCast, show (C (n : Cc) : Cc[X]) = (n : Cc[X]) from map_natCast C n,
            map_natCast]])
  -- the field `F₂ = F₁(t₁)`
  have hw1 : t1E′ = aeval t1E (C η₁' * X : (Cc⟮xE⟯)[X]) := by
    rw [map_mul, aeval_C, aeval_X, ht1E']
  let _ := algebraAdjoinSimple (F := Cc⟮xE⟯) t1E
  let _ : Differential (Cc⟮xE⟯)[X] := polynomialOfDeriv (C η₁' * X)
  let _ : Differential (Cc⟮xE⟯)⟮t1E⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t1E (C η₁' * X) hw1)
  have hFR2 : IsFractionRing (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ := isFractionRing_adjoin_simple t1E htr1
  have hDA2 : DifferentialAlgebra (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ :=
    differentialAlgebra_adjoin_simple t1E (C η₁' * X) hw1
  have hDA2E : DifferentialAlgebra (Cc⟮xE⟯)⟮t1E⟯ E :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple t1E (C η₁' * X) hw1)
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
  have hηa : Tower.ηh (K₁ := Cc⟮xE⟯) ι Hn Hd = η₁' := rfl
  have hD₂ : ∀ P : (Cc⟮xE⟯)[X], P′ = implicitDeriv (C (Tower.ηh (K₁ := Cc⟮xE⟯) ι Hn Hd) * X) P :=
    fun P ↦ by rw [hηa]; rfl
  have hconst : ∀ (P : (Cc⟮xE⟯)[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ →
      ∃ e : Cc⟮xE⟯, P = C e * X ^ n :=
    hyperexp_no_new_constants_W ((toPoly Hn).map ι) ((toPoly Hd).map ι)
      (fun c hc y hy ↦ CPoly.hyperexpW_homogeneous (K := Cc⟮xE⟯) ι hD hHn0 hHd0 hcop hcert c hc y hy)
      (fun P ↦ by rw [hD₂, hηa, hη₁'])
  have hK₂const : ∀ y : (Cc⟮xE⟯)⟮t1E⟯, y′ = 0 → ∃ b : Cc,
      y = algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯ (algebraMap Cc[X] Cc⟮xE⟯ (C b)) := fun y hy ↦ by
    have hyE : ((y : (Cc⟮xE⟯)⟮t1E⟯) : E)′ = 0 := congrArg Subtype.val hy
    refine ⟨⟨(y : E), hyE⟩, ?_⟩
    apply Subtype.ext
    change (y : E) = ((algebraMap Cc[X] Cc⟮xE⟯ (C (⟨(y : E), hyE⟩ : Cc)) : Cc⟮xE⟯) : E)
    rw [algebraMap_adjoinSimple, aeval_C]
    rfl
  -- values of codes in `F₂`
  have hvalP : ∀ q : GPoly (GFrac R), algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯
      (GPoly.toPoly (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) q) = j (Tower.valP x₀ t₁ q) := fun q ↦ by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    change _ = j₀' (Tower.valP x₀ t₁ q)
    simp only [Tower.valP, map_sum, map_mul, map_pow, map_div₀, aeval_C, aeval_X,
      Tower.sem_M₁In, ev, hvalE]
    rfl
  let M₂E : CField (GFrac (GFrac R)) (Cc⟮xE⟯)⟮t1E⟯ ((Tower.ops₁g R).monomial (Tower.hexpW Hn Hd)) :=
    (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD).monomialIn (Tower.hexpW Hn Hd) (Cc⟮xE⟯)⟮t1E⟯ fun P ↦ by
      rw [Tower.toPoly_hexpW_In]; exact hD₂ P
  have hsemG : ∀ q : GFrac (GFrac R), M₂E.sem q = j (Tower.valG x₀ t₁ q) := fun q ↦ by
    change algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (GPoly.toPoly (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) q.1) /
      algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (GPoly.toPoly (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) q.2) = _
    rw [hvalP, hvalP, Tower.valG, map_div₀]
  -- (3) `t₂ = exp a` is transcendental over `F₂`: `a′` has positive degree in `t₁`
  set M₁ := Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD with hM₁
  set η₂'' : (Cc⟮xE⟯)⟮t1E⟯ := j (Tower.valP x₀ t₁ ηc) with hη₂''
  have hη₂'' : η₂'' = algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (GPoly.toPoly M₁ ηc) := (hvalP ηc).symm
  have htE0 : tE ≠ 0 := fun h ↦ ht0 ((map_eq_zero_iff ψ (algebraMap K E).injective).mp h)
  have htE'' : tE′ = algebraMap (Cc⟮xE⟯)⟮t1E⟯ E η₂'' * tE := by
    rw [htE, hψ, deriv_algebraMap, ht, map_mul]
    rfl
  have hder : ∀ P : (Cc⟮xE⟯)[X], (P′).natDegree ≤ P.natDegree := fun P ↦ by
    rw [hD₂]; exact Tower.natDegree_implicitDeriv_C_mul_X_le _ P
  have htηc : GPoly.trim (Tower.ops₁g R) ηc ≠ [] := fun h0 ↦ by rw [h0] at hηc; simp at hηc
  have hgdeg : 1 ≤ (GPoly.toPoly M₁ ηc).natDegree := by
    have := (GPoly.natDegree_toPoly_of_trim_ne_nil M₁ htηc).1
    omega
  have htr2 : Transcendental (Cc⟮xE⟯)⟮t1E⟯ tE :=
    transcendental_exp_arg (K₂ := (Cc⟮xE⟯)⟮t1E⟯) hder (GPoly.toPoly M₁ ηc) hgdeg htE0
      (by rw [htE'', hη₂''])
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
  rw [hcoeff] at hy  -- (6) `rdeNCExp` is complete
  have hz : (((j₀ : ℤ) - n : ℤ) : R) ≠ 0 :=
    Int.cast_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hj₀n))
  set cc : GFrac R := Tower.constZ ((j₀ : ℤ) - n) with hccdef
  have hsemc : M₁.sem cc = (j₀ : Cc⟮xE⟯) - n := by
    rw [hM₁, hccdef, Tower.sem_constZ]
    push_cast
    ring
  have hsemc0 : M₁.sem cc ≠ 0 := by
    rw [hsemc]; exact sub_ne_zero.mpr (by exact_mod_cast hj₀n)
  have hg' : 1 ≤ (GPoly.toPoly M₁ (GPoly.smul (Tower.ops₁g R) cc ηc)).natDegree := by
    rw [GPoly.toPoly_smul, natDegree_C_mul hsemc0]
    exact hgdeg
  have hA0' : GPoly.toPoly M₁ (A j₀).2 ≠ 0 := fun hz' ↦ by
    have := hD0 j₀ hj₀
    rw [(GPoly.isZero_iff M₁ _).mpr hz'] at this
    exact Bool.noConfusion this
  have hsome := Tower.rdeNCHexpB_complete (K₁ := Cc⟮xE⟯) (K₂ := (Cc⟮xE⟯)⟮t1E⟯) ι hCc0 hD Hn Hd μ
    hHn0 hHd0 hcop hcert hD₂ hconst (Tower.normFrac (GPoly.coeffAt (Tower.ops₁g R) a 0))
    (Tower.normFrac_den_ne_zero _) ((j₀ : ℤ) - n) (GPoly.smul (Tower.ops₁g R) cc ηc)
    (A j₀).1 (A j₀).2 hg' (by
      rw [hccdef, hηcdef]; exact Tower.coeff_zero_smul_derivT_hexpW ι hCc0 hD Hn Hd a _) hA0' y (by
      change _ = M₂E.sem (A j₀)
      rw [hsemG]
      change _ = fr (A j₀)
      rw [← hy, GPoly.toPoly_smul, map_mul, hsemc, ← hη₂'', C_sub, map_sub,
        show (C (j₀ : Cc⟮xE⟯) : (Cc⟮xE⟯)[X]) = (j₀ : (Cc⟮xE⟯)[X]) from map_natCast C j₀,
        show (C (n : Cc⟮xE⟯) : (Cc⟮xE⟯)[X]) = (n : (Cc⟮xE⟯)[X]) from map_natCast C n,
        map_natCast, map_natCast])
  rw [hnone] at hsome
  exact Bool.noConfusion hsome

end CPoly
