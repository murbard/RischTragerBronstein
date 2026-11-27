import RischTragerBronstein.Elementary.Closed
import RischTragerBronstein.Elementary.Algebraic
import RischTragerBronstein.Elementary.Logarithm
import RischTragerBronstein.Elementary.Sum
import RischTragerBronstein.Elementary.LiouvilleForm
import RischTragerBronstein.Liouville.Strong
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Elementary integrals persist over elementary extensions, and add up

Two elementary extensions of `F` need not visibly have a common extension. They do for the
purpose of integration: by the strong Liouville theorem an elementary integral of `f` is
`v + ∑ cᵢ log uᵢ` with `v`, `uᵢ` in `F(c₁, …, c_r)` for finitely many new constants, and constants
can be adjoined to any differential extension `M` of `F` simultaneously (a transcendental one as
a new transcendental constant `X` of `M(X)`, the logarithm of `1`; an algebraic one in a finite
extension of `M`).

* `exists_ext_adjoin_const`: one constant.
* `exists_ext_adjoin_consts`: finitely many.
* **`HasElementaryIntegral.hasElementaryIntegralIn`**: an elementary integral over `F` gives one
  over every differential extension field, in particular over every elementary extension.
* **`HasElementaryIntegral.add`**: `∫ f₁` and `∫ f₂` elementary imply `∫ (f₁ + f₂)` elementary
  (`.sub`, `.sum`, `.const_mul`, `.linear`).
* `hasElementaryIntegral_elementary_iff`: integrability over `F` and over an elementary extension
  of `F` are the same.
-/

open Polynomial IntermediateField
open scoped nonZeroDivisors

namespace Differential

universe u

section Step

variable {A K : Type u} [Field A] [Field K] [Differential A] [Differential K] [Algebra A K]
  [DifferentialAlgebra A K]

lemma derivClosed_adjoin_const (s : K) (hs : s′ = 0) : DerivClosed A⟮s⟯ := by
  have := (derivClosed_bot (F := A) (K := K)).adjoin s (by rw [hs]; exact zero_mem _)
  rwa [bot_sup_eq] at this

/-- A ring morphism out of `A(s)` commutes with the derivations as soon as it does on `A` and
at `s`. -/
lemma ringHom_deriv_adjoin_simple {M₁ : Type*} [Field M₁] [Differential M₁] (s : K)
    (hc : DerivClosed A⟮s⟯) (ψ : A⟮s⟯ →+* M₁)
    (hA : ∀ a : A, (ψ (algebraMap A A⟮s⟯ a))′ = ψ (algebraMap A A⟮s⟯ a′))
    (hsψ : (ψ (AdjoinSimple.gen A s))′ = ψ ⟨s′, hc s (mem_adjoin_simple_self A s)⟩) :
    ∀ z : A⟮s⟯, (ψ z)′ = ψ ⟨(z : K)′, hc z z.2⟩ := by
  have key : ∀ x (hx : x ∈ A⟮s⟯), (ψ ⟨x, hx⟩)′ = ψ ⟨x′, hc x hx⟩ := by
    let S : IntermediateField A K :=
      { carrier := {x | ∃ hx : x ∈ A⟮s⟯, (ψ ⟨x, hx⟩)′ = ψ ⟨x′, hc x hx⟩}
        mul_mem' := fun {x y} hx hy ↦ by
          obtain ⟨hx, ihx⟩ := hx
          obtain ⟨hy, ihy⟩ := hy
          refine ⟨mul_mem hx hy, ?_⟩
          have e1 : (⟨x * y, mul_mem hx hy⟩ : A⟮s⟯) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
          have e2 : (⟨(x * y)′, hc _ (mul_mem hx hy)⟩ : A⟮s⟯) =
              ⟨x, hx⟩ * ⟨y′, hc y hy⟩ + ⟨y, hy⟩ * ⟨x′, hc x hx⟩ :=
            Subtype.ext (show (x * y)′ = x * y′ + y * x′ by rw [Derivation.leibniz]; rfl)
          rw [e1, map_mul, Derivation.leibniz, ihx, ihy, smul_eq_mul, smul_eq_mul, e2, map_add,
            map_mul, map_mul]
        one_mem' := ⟨one_mem _, by
          have e1 : (⟨1, one_mem _⟩ : A⟮s⟯) = 1 := rfl
          have e2 : (⟨(1 : K)′, hc _ (one_mem _)⟩ : A⟮s⟯) = 0 := Subtype.ext (by simp)
          rw [e1, e2, map_one, map_zero]
          simp⟩
        add_mem' := fun {x y} hx hy ↦ by
          obtain ⟨hx, ihx⟩ := hx
          obtain ⟨hy, ihy⟩ := hy
          refine ⟨add_mem hx hy, ?_⟩
          have e1 : (⟨x + y, add_mem hx hy⟩ : A⟮s⟯) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
          have e2 : (⟨(x + y)′, hc _ (add_mem hx hy)⟩ : A⟮s⟯) =
              ⟨x′, hc x hx⟩ + ⟨y′, hc y hy⟩ := Subtype.ext (map_add _ x y)
          rw [e1, map_add, map_add, ihx, ihy, e2, map_add]
        zero_mem' := ⟨zero_mem _, by
          have e1 : (⟨0, zero_mem _⟩ : A⟮s⟯) = 0 := rfl
          have e2 : (⟨(0 : K)′, hc _ (zero_mem _)⟩ : A⟮s⟯) = 0 := Subtype.ext (by simp)
          rw [e1, e2, map_zero]
          simp⟩
        algebraMap_mem' := fun a ↦ ⟨A⟮s⟯.algebraMap_mem a, by
          refine (hA a).trans (congrArg ψ (Subtype.ext ?_))
          exact (deriv_algebraMap a).symm⟩
        inv_mem' := fun x hx ↦ by
          obtain ⟨hx, ih⟩ := hx
          refine ⟨inv_mem hx, ?_⟩
          have e1 : (⟨x⁻¹, inv_mem hx⟩ : A⟮s⟯) = (⟨x, hx⟩ : A⟮s⟯)⁻¹ := rfl
          have e2 : (⟨(x⁻¹)′, hc _ (inv_mem hx)⟩ : A⟮s⟯) =
              -((⟨x, hx⟩ : A⟮s⟯)⁻¹) ^ 2 * ⟨x′, hc x hx⟩ :=
            Subtype.ext (show (x⁻¹)′ = -x⁻¹ ^ 2 * x′ by rw [Derivation.leibniz_inv]; rfl)
          rw [e1, map_inv₀, Derivation.leibniz_inv, ih, smul_eq_mul, e2, map_mul, map_neg,
            map_pow, map_inv₀] }
    have hsS : A⟮s⟯ ≤ S := by
      rw [adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨mem_adjoin_simple_self A s, hsψ⟩
    intro x hx
    obtain ⟨_, h⟩ := hsS hx
    exact h
  rintro ⟨z, hz⟩
  exact key z hz

variable [CharZero A]

/-- **Adjoining a constant simultaneously.** If `s ∈ K` is a constant and `M` is any differential
field over `A`, some elementary extension `M₁` of `M` receives `A(s)` compatibly with the
derivations. -/
theorem exists_ext_adjoin_const {M : Type u} [Field M] [Differential M] [Algebra A M]
    [DifferentialAlgebra A M] (s : K) (hs : s′ = 0) (hc : DerivClosed A⟮s⟯) :
    ∃ (M₁ : Type u) (_ : Field M₁) (_ : Differential M₁) (_ : Algebra M M₁)
      (_ : DifferentialAlgebra M M₁),
      IsElementaryExtension M M₁ ∧ ∃ ψ : A⟮s⟯ →+* M₁,
        (∀ z : A⟮s⟯, (ψ z)′ = ψ ⟨(z : K)′, hc z z.2⟩) ∧
        ∀ a : A, ψ (algebraMap A A⟮s⟯ a) = algebraMap M M₁ (algebraMap A M a) := by
  classical
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap A M).injective
  by_cases halg : IsAlgebraic A s
  · -- an algebraic constant: a root of its minimal polynomial in a finite extension of `M`
    have hint : IsIntegral A s := halg.isIntegral
    set P : M[X] := (minpoly A s).map (algebraMap A M) with hP
    have hPu : ¬IsUnit P := by
      intro hu
      have h0 := natDegree_eq_zero_of_isUnit hu
      rw [hP, natDegree_map] at h0
      exact (minpoly.natDegree_pos hint).ne' h0
    obtain ⟨q, hqm, hqirr, hqdvd⟩ := exists_monic_irreducible_factor P hPu
    haveI : Fact (Irreducible q) := ⟨hqirr⟩
    haveI : Fact q.Monic := ⟨hqm⟩
    haveI : FiniteDimensional M (AdjoinRoot q) := (AdjoinRoot.powerBasis hqirr.ne_zero).finite
    haveI hDAA : DifferentialAlgebra A (AdjoinRoot q) :=
      ⟨fun a ↦ by
        rw [IsScalarTower.algebraMap_apply A M (AdjoinRoot q), deriv_algebraMap,
          deriv_algebraMap, ← IsScalarTower.algebraMap_apply]⟩
    have hroot : (minpoly A s).eval₂ (Algebra.ofId A (AdjoinRoot q)) (AdjoinRoot.root q) = 0 := by
      have h1 : P.eval₂ (AdjoinRoot.of q) (AdjoinRoot.root q) = 0 := by
        obtain ⟨r, hr⟩ := hqdvd
        rw [hr, eval₂_mul, AdjoinRoot.eval₂_root, zero_mul]
      rw [hP, eval₂_map] at h1
      exact h1
    let ι : A⟮s⟯ →ₐ[A] AdjoinRoot q :=
      (AdjoinRoot.liftAlgHom (minpoly A s) (Algebra.ofId A (AdjoinRoot q)) (AdjoinRoot.root q)
        hroot).comp (adjoinRootEquivAdjoin A hint).symm.toAlgHom
    letI := differentialOfDerivClosed hc
    haveI : DifferentialAlgebra A A⟮s⟯ := ⟨fun a ↦ Subtype.ext (deriv_algebraMap a)⟩
    haveI : Algebra.IsAlgebraic A A⟮s⟯ := isAlgebraic_adjoin_simple hint
    refine ⟨AdjoinRoot q, inferInstance, inferInstance, inferInstance, inferInstance,
      isElementaryExtension_of_finiteDimensional, ι.toRingHom, fun z ↦ ?_, fun a ↦ ?_⟩
    · exact (algHom_deriv ι ι.toRingHom.injective z
        (minpoly.irreducible (Algebra.IsIntegral.isIntegral z)).separable).symm
    · exact (ι.commutes a).trans (IsScalarTower.algebraMap_apply A M (AdjoinRoot q) a)
  · -- a transcendental constant: a new transcendental constant over `M`
    have htr : Transcendental A s := halg
    letI : Differential (RatFunc M) := ratFuncOfDeriv (C (logDeriv (1 : M)))
    haveI hDA : DifferentialAlgebra M (RatFunc M) :=
      differentialAlgebra_ratFuncOfDeriv (C (logDeriv (1 : M)))
    obtain ⟨hE, hX⟩ := isElementaryExtension_log (1 : M) one_ne_zero
    have hX0 : (RatFunc.X : RatFunc M)′ = 0 := by
      rw [hX, logDeriv_one, map_zero]
    let φ : A[X] →+* RatFunc M :=
      (algebraMap M[X] (RatFunc M)).comp (Polynomial.mapRingHom (algebraMap A M))
    have hφinj : Function.Injective φ :=
      (RatFunc.algebraMap_injective M).comp (Polynomial.map_injective _ (algebraMap A M).injective)
    have hφ : A[X]⁰ ≤ (RatFunc M)⁰.comap φ := fun p hp ↦ by
      rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
      exact (map_ne_zero_iff φ hφinj).mpr (nonZeroDivisors.ne_zero hp)
    let ψ : A⟮s⟯ →+* RatFunc M :=
      (RatFunc.liftRingHom φ hφ).comp
        ((RatFunc.algEquivOfTranscendental s htr).symm : A⟮s⟯ →+* RatFunc A)
    have hext : ∀ a : A, ψ (algebraMap A A⟮s⟯ a) = algebraMap M (RatFunc M) (algebraMap A M a) := by
      intro a
      change RatFunc.liftRingHom φ hφ
        ((RatFunc.algEquivOfTranscendental s htr).symm (algebraMap A A⟮s⟯ a)) = _
      rw [AlgEquiv.commutes, RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C,
        RatFunc.liftRingHom_algebraMap]
      change algebraMap M[X] (RatFunc M) ((C a).map (algebraMap A M)) = _
      rw [Polynomial.map_C, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
    have hgen : ψ (AdjoinSimple.gen A s) = RatFunc.X := by
      change RatFunc.liftRingHom φ hφ
        ((RatFunc.algEquivOfTranscendental s htr).symm (AdjoinSimple.gen A s)) = _
      rw [RatFunc.algEquivOfTranscendental_symm_gen, ← RatFunc.algebraMap_X,
        RatFunc.liftRingHom_algebraMap]
      change algebraMap M[X] (RatFunc M) ((X : A[X]).map (algebraMap A M)) = _
      rw [Polynomial.map_X, RatFunc.algebraMap_X]
    refine ⟨RatFunc M, inferInstance, inferInstance, inferInstance, hDA, hE, ψ, ?_, hext⟩
    refine ringHom_deriv_adjoin_simple s hc ψ (fun a ↦ ?_) ?_
    · rw [hext, hext, deriv_algebraMap, deriv_algebraMap]
    · rw [hgen, hX0]
      have : (⟨s′, hc s (mem_adjoin_simple_self A s)⟩ : A⟮s⟯) = 0 := Subtype.ext hs
      rw [this, map_zero]

end Step

/-- **Adjoining finitely many constants simultaneously.** If `K` is generated over `A` by
finitely many constants and `M` is any differential field over `A`, some elementary extension
`M₁` of `M` receives `K` compatibly with the derivations. -/
theorem exists_ext_adjoin_consts (n : ℕ) : ∀ (A K M : Type u) [Field A] [Field K] [Field M]
    [Differential A] [Differential K] [Differential M] [Algebra A K] [DifferentialAlgebra A K]
    [Algebra A M] [DifferentialAlgebra A M] [CharZero A] (l : List K), l.length = n →
    (∀ s ∈ l, s′ = 0) → IntermediateField.adjoin A {x | x ∈ l} = ⊤ →
    ∃ (M₁ : Type u) (_ : Field M₁) (_ : Differential M₁) (_ : Algebra M M₁)
      (_ : DifferentialAlgebra M M₁),
      IsElementaryExtension M M₁ ∧ ∃ ψ : K →+* M₁,
        (∀ z : K, (ψ z)′ = ψ z′) ∧
        ∀ a : A, ψ (algebraMap A K a) = algebraMap M M₁ (algebraMap A M a) := by
  induction n with
  | zero =>
    intro A K M _ _ _ _ _ _ _ _ _ _ _ l hl _ hgen
    obtain rfl := List.length_eq_zero_iff.mp hl
    have hbot : (⊥ : IntermediateField A K) = ⊤ := by
      rw [← hgen]
      simp
    have hsurj : Function.Surjective (algebraMap A K) := fun z ↦ by
      have hz : z ∈ (⊥ : IntermediateField A K) := by rw [hbot]; exact mem_top
      exact IntermediateField.mem_bot.mp hz
    let e : A ≃+* K := RingEquiv.ofBijective (algebraMap A K) ⟨(algebraMap A K).injective, hsurj⟩
    let ψ : K →+* M := (algebraMap A M).comp (e.symm : K →+* A)
    have hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A M a := fun a ↦
      congrArg (algebraMap A M) (e.symm_apply_apply a)
    have hMM : IsElementaryExtension M M := by
      have h' : (⊥ : IntermediateField M M) = ⊤ :=
        eq_top_iff.mpr fun x _ ↦ IntermediateField.mem_bot.mpr ⟨x, rfl⟩
      unfold IsElementaryExtension
      rw [← h']
      exact IsElementaryTower.base
    refine ⟨M, inferInstance, inferInstance, inferInstance, ⟨fun _ ↦ rfl⟩, hMM, ψ, fun z ↦ ?_,
      fun a ↦ hψ a⟩
    obtain ⟨a, rfl⟩ := hsurj z
    rw [hψ, deriv_algebraMap, deriv_algebraMap, hψ]
  | succ n ih =>
    intro A K M _ _ _ _ _ _ _ _ _ _ _ l hl hconst hgen
    obtain ⟨s, l', rfl⟩ : ∃ s l', l = s :: l' := by
      cases l with
      | nil => simp at hl
      | cons s l' => exact ⟨s, l', rfl⟩
    have hs0 : s′ = 0 := hconst s (by simp)
    have hc := derivClosed_adjoin_const (A := A) s hs0
    obtain ⟨M₁, _, _, _, hDA₁, hE₁, ψ₁, hψ₁d, hψ₁a⟩ := exists_ext_adjoin_const (M := M) s hs0 hc
    letI := differentialOfDerivClosed hc
    haveI : DifferentialAlgebra A⟮s⟯ K := differentialAlgebra_of_derivClosed hc
    letI : Algebra A⟮s⟯ M₁ := ψ₁.toAlgebra
    haveI : DifferentialAlgebra A⟮s⟯ M₁ := ⟨fun z ↦ hψ₁d z⟩
    haveI : CharZero A⟮s⟯ := charZero_of_injective_algebraMap (algebraMap A A⟮s⟯).injective
    have hgen' : IntermediateField.adjoin A⟮s⟯ {x | x ∈ l'} = ⊤ := by
      apply IntermediateField.restrictScalars_injective A
      rw [adjoin_adjoin_left, restrictScalars_top, ← hgen]
      congr 1
      ext x
      simp
    obtain ⟨M₂, _, _, _, hDA₂, hE₂, ψ₂, hd₂, ha₂⟩ :=
      ih A⟮s⟯ K M₁ l' (by simpa using hl) (fun t ht ↦ hconst t (by simp [ht])) hgen'
    letI : Algebra M M₂ := ((algebraMap M₁ M₂).comp (algebraMap M M₁)).toAlgebra
    haveI : IsScalarTower M M₁ M₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hDA : DifferentialAlgebra M M₂ :=
      ⟨fun a ↦ by
        change (algebraMap M₁ M₂ (algebraMap M M₁ a))′ = algebraMap M₁ M₂ (algebraMap M M₁ a′)
        rw [deriv_algebraMap, deriv_algebraMap]⟩
    refine ⟨M₂, inferInstance, inferInstance, inferInstance, hDA, hE₁.trans hE₂, ψ₂, hd₂,
      fun a ↦ ?_⟩
    exact (ha₂ (algebraMap A A⟮s⟯ a)).trans (congrArg (algebraMap M₁ M₂) (hψ₁a a))


section Main

variable {F : Type u} [Field F] [Differential F] [CharZero F]

/-- **A Liouville form over `F(Const K)` lives over finitely many constants**: there is a
differential field `K₀` generated over `F` by finitely many constants in which `f` has a
Liouville form. -/
theorem exists_const_gen_liouville {K : Type u} [Field K] [Differential K] [Algebra F K]
    [DifferentialAlgebra F K] (f : F) (h : LiouvilleIn (constField F K) (algebraMap F K f)) :
    ∃ (K₀ : Type u) (_ : Field K₀) (_ : Differential K₀) (_ : Algebra F K₀)
      (_ : DifferentialAlgebra F K₀) (l : List K₀), (∀ s ∈ l, s′ = 0) ∧
      IntermediateField.adjoin F {x : K₀ | x ∈ l} = ⊤ ∧
      ∃ (ι : Type) (sI : Finset ι) (c u : ι → K₀) (v : K₀),
        (∀ i ∈ sI, (c i)′ = 0 ∧ u i ≠ 0) ∧
        algebraMap F K₀ f = ∑ i ∈ sI, c i * logDeriv (u i) + v′ := by
  classical
  obtain ⟨ι, sI, c, u, v, hdata, hv, heq⟩ := h
  -- finitely many constants generate the data
  have hfin : ∀ x ∈ constField F K, ∃ T : Finset K, (∀ t ∈ T, t′ = 0) ∧
      x ∈ IntermediateField.adjoin F (T : Set K) := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := exists_finset_of_mem_adjoin hx
    exact ⟨T, fun t ht ↦ hT ht, hxT⟩
  obtain ⟨Tv, hTv, hvT⟩ := hfin v hv
  have hui : ∀ i, ∃ T : Finset K, (∀ t ∈ T, t′ = 0) ∧
      (i ∈ sI → u i ∈ IntermediateField.adjoin F (T : Set K) ∧ c i ∈ T) := by
    intro i
    by_cases hi : i ∈ sI
    · obtain ⟨T, hT, huT⟩ := hfin (u i) (hdata i hi).2.1
      refine ⟨insert (c i) T, ?_, fun _ ↦ ⟨?_, Finset.mem_insert_self _ _⟩⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact (hdata i hi).1
        · exact hT t ht
      · exact IntermediateField.adjoin.mono F _ _ (by simp) huT
    · exact ⟨∅, by simp, fun h ↦ absurd h hi⟩
  choose Tu hTu hTu' using hui
  set T : Finset K := Tv ∪ sI.biUnion Tu with hTdef
  have hTc : ∀ t ∈ T, t′ = 0 := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact hTv t ht
    · obtain ⟨i, -, hti⟩ := Finset.mem_biUnion.mp ht
      exact hTu i t hti
  have hTv_le : (Tv : Set K) ⊆ T := by
    intro t ht
    exact Finset.mem_union_left _ ht
  have hTu_le : ∀ i ∈ sI, (Tu i : Set K) ⊆ T := by
    intro i hi t ht
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, ht⟩)
  set K₀ : IntermediateField F K := IntermediateField.adjoin F (T : Set K) with hK₀
  have hK : DerivClosed K₀ := by
    have := (derivClosed_bot (F := F) (K := K)).adjoin_set (T : Set K)
      (fun x hx ↦ by rw [hTc x hx]; exact zero_mem _)
    rwa [bot_sup_eq] at this
  letI := differentialOfDerivClosed hK
  haveI : DifferentialAlgebra F K₀ := ⟨fun a ↦ Subtype.ext (deriv_algebraMap a)⟩
  -- the generators, in `K₀`
  let l : List K₀ := T.attach.toList.map fun t ↦ ⟨t.1, subset_adjoin F _ t.2⟩
  have hlc : ∀ s ∈ l, s′ = 0 := by
    intro s hs
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hs
    exact Subtype.ext (hTc t.1 t.2)
  have hlgen : IntermediateField.adjoin F {x : K₀ | x ∈ l} = ⊤ := by
    apply IntermediateField.map_injective K₀.val
    rw [adjoin_map, ← AlgHom.fieldRange_eq_map, fieldRange_val]
    change IntermediateField.adjoin F (K₀.val '' {x | x ∈ l}) =
      IntermediateField.adjoin F (T : Set K)
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hy
      exact t.2
    · intro hx
      exact ⟨⟨x, subset_adjoin F _ hx⟩, List.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩, rfl⟩
  -- the Liouville form, in `K₀`
  have hvK : v ∈ K₀ := IntermediateField.adjoin.mono F _ _ hTv_le hvT
  have huK : ∀ i ∈ sI, u i ∈ K₀ := fun i hi ↦
    IntermediateField.adjoin.mono F _ _ (hTu_le i hi) (hTu' i hi).1
  have hcK : ∀ i ∈ sI, c i ∈ K₀ := fun i hi ↦ subset_adjoin F _ (hTu_le i hi (hTu' i hi).2)
  let v' : K₀ := ⟨v, hvK⟩
  let u' : ι → K₀ := fun i ↦ if hi : i ∈ sI then ⟨u i, huK i hi⟩ else 1
  let c' : ι → K₀ := fun i ↦ if hi : i ∈ sI then ⟨c i, hcK i hi⟩ else 0
  have hK₀eq : algebraMap F K₀ f = ∑ i ∈ sI, c' i * logDeriv (u' i) + v'′ := by
    apply Subtype.ext
    change algebraMap F K f = ((∑ i ∈ sI, c' i * logDeriv (u' i) + v'′ : K₀) : K)
    rw [heq, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    exact Finset.sum_congr rfl fun i hi ↦ by simp only [c', u', dif_pos hi]; rfl
  have hc'0 : ∀ i ∈ sI, (c' i)′ = 0 := fun i hi ↦ by
    simp only [c', dif_pos hi]
    exact Subtype.ext (hdata i hi).1
  have hu'0 : ∀ i ∈ sI, u' i ≠ 0 := fun i hi ↦ by
    simp only [u', dif_pos hi]
    exact fun h0 ↦ (hdata i hi).2.2 (congrArg Subtype.val h0)
  exact ⟨K₀, inferInstance, inferInstance, inferInstance, inferInstance, l, hlc, hlgen, ι, sI, c', u',
    v', fun i hi ↦ ⟨hc'0 i hi, hu'0 i hi⟩, hK₀eq⟩

/-- **An elementary integral persists over every differential extension field** of the base:
if `∫ f` is elementary over `F`, it is elementary over `E`. -/
theorem HasElementaryIntegral.over_ext {f : F} (h : HasElementaryIntegral f) (E : Type u)
    [Field E] [Differential E] [Algebra F E] [DifferentialAlgebra F E] :
    HasElementaryIntegral (algebraMap F E f) := by
  classical
  obtain ⟨E₂, _, _, _, _, hE₂, g, hg⟩ := h
  obtain ⟨K₀, _, _, _, _, l, hlc, hlgen, ι, sI, c', u', v', hcu, hK₀eq⟩ :=
    exists_const_gen_liouville f (liouville_strong hE₂ f g hg)
  have hc'0 : ∀ i ∈ sI, (c' i)′ = 0 := fun i hi ↦ (hcu i hi).1
  have hu'0 : ∀ i ∈ sI, u' i ≠ 0 := fun i hi ↦ (hcu i hi).2
  obtain ⟨M₁, _, _, _, hDA₁, hE₁, ψ, hψd, hψa⟩ :=
    exists_ext_adjoin_consts l.length F K₀ E l rfl hlc hlgen
  -- transported to `M₁`
  have hform := hasElementaryIntegral_of_liouville_form (ψ v')
    (sI.toList.map fun i ↦ (ψ (c' i), ψ (u' i))) (by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      have hi' := Finset.mem_toList.mp hi
      exact ⟨by rw [hψd, hc'0 i hi', map_zero], (map_ne_zero ψ).mpr (hu'0 i hi')⟩)
  have hval : (ψ v')′ + ((sI.toList.map fun i ↦ (ψ (c' i), ψ (u' i))).map
      fun p ↦ p.1 * logDeriv p.2).sum = algebraMap E M₁ (algebraMap F E f) := by
    rw [← hψa f, hK₀eq, map_add, map_sum, List.map_map, Finset.sum_map_toList, add_comm, hψd]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Function.comp, logDeriv, map_mul, map_div₀, hψd]
  rw [hval] at hform
  exact HasElementaryIntegral.of_extension hE₁ hform

/-- **An elementary integral over `F` is one over every elementary extension of `F`.** -/
theorem HasElementaryIntegral.hasElementaryIntegralIn {f : F} (h : HasElementaryIntegral f) :
    HasElementaryIntegralIn f :=
  fun E _ _ _ _ _ ↦ h.over_ext E

/-- `HasElementaryIntegral` and its extension-stable form are equivalent. -/
theorem hasElementaryIntegralIn_iff {f : F} :
    HasElementaryIntegralIn f ↔ HasElementaryIntegral f :=
  ⟨HasElementaryIntegralIn.hasElementaryIntegral, HasElementaryIntegral.hasElementaryIntegralIn⟩

/-- **Elementary integrability is additive.** -/
theorem HasElementaryIntegral.add {f₁ f₂ : F} (h₁ : HasElementaryIntegral f₁)
    (h₂ : HasElementaryIntegral f₂) : HasElementaryIntegral (f₁ + f₂) :=
  h₁.add_in h₂.hasElementaryIntegralIn

theorem HasElementaryIntegral.sub {f₁ f₂ : F} (h₁ : HasElementaryIntegral f₁)
    (h₂ : HasElementaryIntegral f₂) : HasElementaryIntegral (f₁ - f₂) :=
  h₁.sub_in h₂.hasElementaryIntegralIn

/-- If `∫ f₂` is elementary, then `∫ (f₁ + f₂)` is elementary iff `∫ f₁` is. -/
theorem hasElementaryIntegral_add_iff_left {f₁ f₂ : F} (h₂ : HasElementaryIntegral f₂) :
    HasElementaryIntegral (f₁ + f₂) ↔ HasElementaryIntegral f₁ :=
  ⟨fun h ↦ by simpa using h.sub h₂, fun h ↦ h.add h₂⟩

theorem HasElementaryIntegral.sum {ι : Type*} (s : Finset ι) (f : ι → F)
    (h : ∀ i ∈ s, HasElementaryIntegral (f i)) : HasElementaryIntegral (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f HasElementaryIntegral (fun a b ha hb ↦ ha.add hb) ?_ h
  simpa using hasElementaryIntegral_of_deriv (0 : F)

/-- **Integrability is the same over the base and over any elementary extension of it.** -/
theorem hasElementaryIntegral_elementary_iff {K : Type u} [Field K] [Differential K] [Algebra F K]
    [DifferentialAlgebra F K] (hK : IsElementaryExtension F K) (f : F) :
    HasElementaryIntegral (algebraMap F K f) ↔ HasElementaryIntegral f :=
  ⟨HasElementaryIntegral.of_extension hK, fun h ↦ h.over_ext K⟩

omit [CharZero F] in
/-- Constant multiples of elementarily integrable functions are elementarily integrable. -/
theorem HasElementaryIntegral.const_mul {f : F} (h : HasElementaryIntegral f) (c : F)
    (hc : c′ = 0) : HasElementaryIntegral (c * f) := by
  obtain ⟨K, _, _, _, _, hK, g, hg⟩ := h
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, hK,
    algebraMap F K c * g, ?_⟩
  rw [Derivation.leibniz, hg, deriv_algebraMap, hc, map_zero, smul_zero, add_zero, smul_eq_mul,
    map_mul]

/-- **Linearity over the constants**: `∫ (c₁ f₁ + c₂ f₂)` is elementary when `∫ f₁`, `∫ f₂` are
and `c₁`, `c₂` are constants. -/
theorem HasElementaryIntegral.linear {f₁ f₂ : F} (h₁ : HasElementaryIntegral f₁)
    (h₂ : HasElementaryIntegral f₂) (c₁ c₂ : F) (hc₁ : c₁′ = 0) (hc₂ : c₂′ = 0) :
    HasElementaryIntegral (c₁ * f₁ + c₂ * f₂) :=
  (h₁.const_mul c₁ hc₁).add (h₂.const_mul c₂ hc₂)

end Main

end Differential
