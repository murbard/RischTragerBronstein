import RischTragerBronstein.Computable.ExpPoly
import RischTragerBronstein.Computable.RDEPolyMap
import RischTragerBronstein.Liouville.Strong
import RischTragerBronstein.Liouville.Transcendence

/-!
# `∫ p(x) exp (a(x)) dx`: the negative answer, unconditionally

`not_elementary_of_integrateExpPoly_none`: let `K` be a differential field of characteristic zero
generated over a field `R` of constants by `x` and `t`, with `x′ = 1`, `t ≠ 0`, `t′ = a′(x) t`
(so `t = exp (a(x))`), where `a ∈ R[x]` has degree at least one. If
`CPoly.integrateExpPoly p a = none`, then `p(x) t` has **no antiderivative in any elementary
extension `E` of `K`** — with no assumption on the constants of `E`.

Proof. Let `C' = Const E`. Inside `E`: `x` is transcendental over `C'` (its derivative is not
zero), and `t` is transcendental over `F₁ = C'(x)` (`transcendental_exponential`, using that
`b′ = n a′ b` has no nonzero solution in `C'(x)`). By the strong Liouville theorem, an
antiderivative yields a Liouville form with data in `K(C') ⊆ F₁(t)`; the Risch differential equation
criterion gives `y ∈ C'(x)` with `y′ + a′ y = p`, necessarily a polynomial over `C'`; and the
solver's completeness over the extension `C' / R` says there is none.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field K] [Algebra R K]
variable [Differential K]

theorem not_elementary_of_integrateExpPoly_none (hR : ∀ r : R, (algebraMap R K r)′ = 0)
    (x t : K) (hx : x′ = 1) (ht0 : t ≠ 0) (a p : CPoly R)
    (ht : t′ = aeval x (derivative (toPoly a)) * t)
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (ha : trim (deriv a) ≠ []) (hnone : integrateExpPoly p a = none)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    [CharZero K] (hE : IsElementaryExtension K E) (g : E) :
    g′ ≠ algebraMap K E (aeval x (toPoly p) * t) := by
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
  have htE0 : tE ≠ 0 := (map_ne_zero ψ).mpr ht0
  set A' : Cc[X] := (derivative (toPoly a)).map ι with hA'
  have htE' : tE′ = aeval xE A' * tE := by
    rw [htE, hψ, deriv_algebraMap, ht, map_mul, hA', hι]
  have hA'0 : A' ≠ 0 := by
    rw [hA', Ne, Polynomial.map_eq_zero_iff ι.injective, ← toPoly_deriv]
    obtain ⟨-, hlc, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil ha
    intro h0
    rw [h0, coeff_zero] at hlc
    exact hlc0 hlc.symm
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
  set η₁ : Cc⟮xE⟯ := algebraMap Cc[X] Cc⟮xE⟯ A' with hη₁
  have hη₁E : algebraMap Cc⟮xE⟯ E η₁ = aeval xE A' := algebraMap_adjoinSimple xE A'
  have htE'' : tE′ = algebraMap Cc⟮xE⟯ E η₁ * tE := by rw [hη₁E, htE']
  -- (2) `t` is transcendental over `C'(x)`
  have htrt : Transcendental Cc⟮xE⟯ tE := by
    refine transcendental_exponential η₁ htE0 htE'' fun n hn b hb ↦ ?_
    refine rde_homogeneous' (K := Cc⟮xE⟯) hD (-(C (n : Cc) * A')) ?_ b ?_
    · exact neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) hA'0)
    · rw [hb, map_neg, map_mul, ← hη₁]
      have : algebraMap Cc[X] Cc⟮xE⟯ (C (n : Cc)) = (n : Cc⟮xE⟯) := by
        rw [show (C (n : Cc) : Cc[X]) = (n : Cc[X]) from map_natCast C n, map_natCast]
      rw [this]
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
  -- (5) the Risch differential equation over `C'(x)`
  let c' : κ → Cc⟮xE⟯ := fun i ↦
    if hi : i ∈ s then algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩ else 0
  obtain ⟨y, hy⟩ := rde_step_exponential (F := Cc⟮xE⟯) tE htrt η₁ htE'' hconst1 s c' u
    (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) v (hcf _ hv)
    (algebraMap Cc[X] Cc⟮xE⟯ ((toPoly p).map ι)) (by
      have hfE : algebraMap Cc⟮xE⟯ E (algebraMap Cc[X] Cc⟮xE⟯ ((toPoly p).map ι)) =
          aeval xE ((toPoly p).map ι) := algebraMap_adjoinSimple xE _
      have hpx : aeval xE ((toPoly p).map ι) = ψ (aeval x (toPoly p)) := hι _ x
      rw [hfE, hpx, htE, ← map_mul, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)
  obtain ⟨Y, -, hY⟩ := rde_polynomial_solution (K := Cc⟮xE⟯) hD A' ((toPoly p).map ι) y hy
  exact rdeSolve_complete_map ι ha hnone ⟨Y, by rw [toPoly_deriv]; exact hY⟩

/-- **`none` means: no elementary integral**, in the sense of the specification
`Differential.HasElementaryIntegral`, with no side condition on constants. -/
theorem not_hasElementaryIntegral_of_integrateExpPoly_none {K : Type*} [Field K] [Algebra R K]
    [Differential K] [CharZero K] (hR : ∀ r : R, (algebraMap R K r)′ = 0)
    (x t : K) (hx : x′ = 1) (ht0 : t ≠ 0) (a p : CPoly R)
    (ht : t′ = aeval x (derivative (toPoly a)) * t)
    (hgen : adjoin R {x, t} = (⊤ : IntermediateField R K))
    (ha : trim (deriv a) ≠ []) (hnone : integrateExpPoly p a = none) :
    ¬HasElementaryIntegral (aeval x (toPoly p) * t) := by
  rintro ⟨E, _, _, _, _, hE, g, hg⟩
  exact not_elementary_of_integrateExpPoly_none hR x t hx ht0 a p ht hgen ha hnone E hE g hg

end CPoly
