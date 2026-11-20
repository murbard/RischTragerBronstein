import RischTragerBronstein.Elementary.AlgDeriv
import RischTragerBronstein.Elementary.Sum

/-!
# Elementary integrability is invariant under algebraic extensions of the base

Let `K / F` be an algebraic extension of differential fields of characteristic zero (not
necessarily finite, e.g. the extension by the algebraic closure of the constants) and `f ∈ F`.

* **`hasElementaryIntegral_isAlgebraic_iff`**: `f` has an elementary integral over `K` iff it has
  one over `F`;
* **`HasElementaryIntegralIn.of_isAlgebraic`**: if `f` has an elementary integral over every
  elementary extension of `K`, it has one over every elementary extension of `F`.

`→` of the first is the finite-support descent (`HasElementaryIntegral.of_isAlgebraic`). For the
rest, an elementary extension `E` of `F` and `K` are put in a common differential field, the
algebraic closure `Ē` of `E` (whose derivation is `algDifferential`): `K` embeds in `Ē` over `F`
compatibly with the derivations (`algHom_deriv`), the tower of `E / F` generates an elementary
tower `M` of `Ē / K`, and `M` is algebraic over `E` (`exists_compositum`).
-/

open IntermediateField Polynomial

namespace Differential

universe u

variable {F K : Type u} [Field F] [Field K] [CharZero F] [Differential F] [Differential K]
  [Algebra F K] [DifferentialAlgebra F K]

/-- **The compositum** of `K` (algebraic over `F`) and an elementary extension `E` of `F`: a
differential field `M`, elementary over `K` and algebraic over `E`, in which the two images of
`F` agree. -/
theorem exists_compositum (halg : Algebra.IsAlgebraic F K) (E : Type u) [Field E] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] (hE : IsElementaryExtension F E) :
    ∃ (M : Type u) (_ : Field M) (_ : Differential M) (_ : Algebra K M)
      (_ : DifferentialAlgebra K M) (_ : Algebra E M) (_ : DifferentialAlgebra E M),
      IsElementaryExtension K M ∧ Algebra.IsAlgebraic E M ∧
      ∀ f : F, algebraMap K M (algebraMap F K f) = algebraMap E M (algebraMap F E f) := by
  classical
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  set Ē := AlgebraicClosure E
  haveI hDAF : DifferentialAlgebra F Ē :=
    ⟨fun a ↦ by
      rw [IsScalarTower.algebraMap_apply F E Ē, deriv_algebraMap, deriv_algebraMap,
        ← IsScalarTower.algebraMap_apply]⟩
  -- `K` inside `Ē`
  let ι : K →ₐ[F] Ē := IsAlgClosed.lift
  have hι : ∀ k : K, (ι k)′ = ι k′ := fun k ↦ by
    have hint : IsIntegral F k := (halg.isAlgebraic k).isIntegral
    exact (algHom_deriv ι ι.injective k (minpoly.irreducible hint).separable).symm
  letI : Algebra K Ē := ι.toRingHom.toAlgebra
  haveI : IsScalarTower F K Ē := IsScalarTower.of_algebraMap_eq fun a ↦ (ι.commutes a).symm
  haveI hDAK : DifferentialAlgebra K Ē := ⟨fun k ↦ hι k⟩
  -- the tower of `E`, over `K`
  have h1 := IsElementaryTower.map (F := F) (K := E) (L := Ē) hE
  have h2 := IsElementaryTower.baseChange (F := F) (F' := K) h1
  set N : IntermediateField K Ē :=
    IntermediateField.adjoin K ((⊤ : IntermediateField F E).map (IsScalarTower.toAlgHom F E Ē) :
      Set Ē) with hN
  have hc : DerivClosed N := h2.derivClosed
  letI : Differential N := differentialOfDerivClosed hc
  have hcoe : ∀ z : N, ((z′ : N) : Ē) = (z : Ē)′ := fun z ↦ coe_deriv_of_derivClosed hc z
  have hEN : ∀ e : E, algebraMap E Ē e ∈ N := fun e ↦
    subset_adjoin K _ ⟨e, IntermediateField.mem_top, rfl⟩
  -- `E` inside `N`
  let jE : E →+* N :=
    { toFun := fun e ↦ ⟨algebraMap E Ē e, hEN e⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ ↦ Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _) }
  letI : Algebra E N := jE.toAlgebra
  have hDAKN : DifferentialAlgebra K N :=
    ⟨fun k ↦ Subtype.val_injective (by
      rw [hcoe]
      exact hι k)⟩
  have hDAEN : DifferentialAlgebra E N :=
    ⟨fun e ↦ Subtype.val_injective (by
      rw [hcoe]
      exact deriv_algebraMap (A := E) (B := Ē) e)⟩
  refine ⟨N, inferInstance, inferInstance, inferInstance, hDAKN, inferInstance, hDAEN,
    h2.isElementaryExtension_sub hc, ⟨fun z ↦ ?_⟩, fun f ↦ ?_⟩
  · -- `N` is algebraic over `E`
    obtain ⟨p, hp0, hp⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := E) (z : Ē))
    refine ⟨p, hp0, Subtype.val_injective ?_⟩
    let φ : N →ₐ[E] Ē :=
      { toRingHom := N.val.toRingHom
        commutes' := fun _ ↦ rfl }
    have := Polynomial.aeval_algHom_apply φ z p
    change aeval (z : Ē) p = φ (aeval z p) at this
    change φ (aeval z p) = φ 0
    rw [← this, hp, map_zero]
  · apply Subtype.val_injective
    change ι (algebraMap F K f) = algebraMap E Ē (algebraMap F E f)
    rw [ι.commutes, ← IsScalarTower.algebraMap_apply]

/-- **Ascent**: an elementary integral over `F` gives one over every algebraic extension. -/
theorem HasElementaryIntegral.to_isAlgebraic (halg : Algebra.IsAlgebraic F K) {f : F}
    (h : HasElementaryIntegral f) : HasElementaryIntegral (algebraMap F K f) := by
  obtain ⟨E, _, _, _, _, hE, g, hg⟩ := h
  obtain ⟨M, _, _, _, hDAK, _, hDAE, hMK, -, hcomp⟩ := exists_compositum halg E hE
  refine ⟨M, inferInstance, inferInstance, inferInstance, hDAK, hMK, algebraMap E M g, ?_⟩
  rw [deriv_algebraMap, hg, hcomp]

/-- **Elementary integrability is invariant under algebraic extensions of the base.** -/
theorem hasElementaryIntegral_isAlgebraic_iff (halg : Algebra.IsAlgebraic F K) (f : F) :
    HasElementaryIntegral (algebraMap F K f) ↔ HasElementaryIntegral f :=
  ⟨HasElementaryIntegral.of_isAlgebraic halg, HasElementaryIntegral.to_isAlgebraic halg⟩

/-- **Integrals over every elementary extension descend** along an algebraic extension. -/
theorem HasElementaryIntegralIn.of_isAlgebraic (halg : Algebra.IsAlgebraic F K) {f : F}
    (h : HasElementaryIntegralIn (algebraMap F K f)) : HasElementaryIntegralIn f := by
  intro E _ _ _ _ hE
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨M, _, _, _, hDAK, _, hDAE, hMK, hMalg, hcomp⟩ := exists_compositum halg E hE
  have := h M hMK
  rw [hcomp] at this
  exact HasElementaryIntegral.of_isAlgebraic hMalg this

end Differential
