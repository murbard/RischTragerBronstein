import RischTragerBronstein.Elementary.FiniteBase
import RischTragerBronstein.Elementary.Closed

/-!
# Descent of elementary integrals along algebraic extensions of the base

* `IsElementaryTower.isElementaryExtension_sub`: an elementary tower `M` of `K / F` is an
  elementary extension of `F` in its own right (with the derivation of `K` restricted to `M`).
* **`HasElementaryIntegral.of_isAlgebraic`**: if `K / F` is algebraic (not necessarily finite) and
  `f ∈ F` has an elementary integral over `K`, it has one over `F`.

The proof of the descent is a finite-support argument: an elementary tower over `K` only uses
finitely many elements of `K` (the coefficients of the rational expressions of the data of each
step); adjoining them to `F` first — they are algebraic — and then the same generators gives an
elementary tower over `F` containing the antiderivative.
-/

open IntermediateField Polynomial

namespace Differential

universe u v

section Sub

variable {F : Type u} {K : Type v} [Field F] [Field K] [Differential F] [Differential K]
  [Algebra F K] [DifferentialAlgebra F K]

/-- An elementary tower `N ≤ M`, restricted to `M`. -/
lemma IsElementaryTower.restrict_le {M : IntermediateField F K} (hc : DerivClosed M) :
    letI := differentialOfDerivClosed hc
    ∀ {N : IntermediateField F K}, IsElementaryTower N → ∀ h : N ≤ M,
      IsElementaryTower (IntermediateField.restrict h) := by
  letI := differentialOfDerivClosed hc
  have hcoe : ∀ z : M, ((z′ : M) : K) = (z : K)′ := fun z ↦ coe_deriv_of_derivClosed hc z
  intro N hN
  induction hN with
  | base =>
    intro h
    have : IntermediateField.restrict h = ⊥ := by
      apply IntermediateField.lift_injective
      rw [IntermediateField.lift_restrict, IntermediateField.lift_bot]
    rw [this]
    exact .base
  | adjoin E t _ ht ih =>
    intro h
    have hE : E ≤ M := le_trans le_sup_left h
    have htM : t ∈ M := h ((le_sup_right : F⟮t⟯ ≤ E ⊔ F⟮t⟯) (mem_adjoin_simple_self F t))
    set t' : M := ⟨t, htM⟩ with ht'
    have heq : IntermediateField.restrict h = IntermediateField.restrict hE ⊔ F⟮t'⟯ := by
      apply IntermediateField.lift_injective
      rw [IntermediateField.lift_restrict, IntermediateField.lift_sup,
        IntermediateField.lift_restrict, IntermediateField.lift_adjoin_simple]
    rw [heq]
    refine .adjoin _ _ (ih hE) ?_
    have hmem : ∀ a (ha : a ∈ E), (⟨a, hE ha⟩ : M) ∈ IntermediateField.restrict hE := fun a ha ↦
      (IntermediateField.mem_restrict hE _).mpr ha
    rcases ht with ⟨p, hp0, hp⟩ | ⟨a, ha, ha0, hta⟩ | ⟨ht0, a, ha, hta⟩
    · left
      let e : E →+* IntermediateField.restrict hE :=
        { toFun := fun a ↦ ⟨⟨a, hE a.2⟩, hmem a a.2⟩
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      have he : Function.Injective e := fun x y hxy ↦
        Subtype.ext (congrArg (fun z : IntermediateField.restrict hE ↦ ((z : M) : K)) hxy)
      refine ⟨p.map e, (Polynomial.map_ne_zero_iff he).mpr hp0, ?_⟩
      apply Subtype.val_injective
      have h2 : ((Polynomial.aeval t' (p.map e) : M) : K) = Polynomial.aeval t p := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.aeval_def]
        exact (Polynomial.hom_eval₂ p ((algebraMap (IntermediateField.restrict hE) M).comp e)
          (M.val : M →+* K) t').trans rfl
      rw [h2, hp]
      rfl
    · right; left
      refine ⟨⟨a, hE ha⟩, hmem a ha, fun h0 ↦ ha0 (congrArg Subtype.val h0), ?_⟩
      apply Subtype.val_injective
      unfold logDeriv at hta ⊢
      rw [hcoe, IntermediateField.coe_div, hcoe]
      exact hta
    · right; right
      refine ⟨fun h0 ↦ ht0 (congrArg Subtype.val h0), ⟨a, hE ha⟩, hmem a ha, ?_⟩
      apply Subtype.val_injective
      unfold logDeriv at hta ⊢
      rw [IntermediateField.coe_div, hcoe, hcoe]
      exact hta

/-- **An elementary tower is an elementary extension of the base.** -/
theorem IsElementaryTower.isElementaryExtension_sub {M : IntermediateField F K}
    (hM : IsElementaryTower M) (hc : DerivClosed M) :
    letI := differentialOfDerivClosed hc
    IsElementaryExtension F M := by
  letI := differentialOfDerivClosed hc
  have := IsElementaryTower.restrict_le hc hM le_rfl
  have htop : IntermediateField.restrict (le_refl M) = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_restrict, IntermediateField.lift_top]
  unfold IsElementaryExtension
  rwa [htop] at this

end Sub

section Descent

variable {F K : Type u} [Field F] [Field K] [CharZero F] [Differential F] [Differential K]
  [Algebra F K] [DifferentialAlgebra F K]

open Classical in
/-- The coefficients `c₀, …, c_d` of a polynomial over an intermediate field, in the ambient field. -/
noncomputable def coefSet {L : Type*} [Field L] [Algebra K L] (M : IntermediateField K L)
    (p : M[X]) : Finset L :=
  (Finset.range (p.natDegree + 1)).image fun i ↦ ((p.coeff i : M) : L)

lemma coeff_mem_of_coefSet {L : Type*} [Field L] [Algebra K L] [Algebra F L]
    (M : IntermediateField K L) (N : IntermediateField F L) (p : M[X])
    (h : (coefSet M p : Set L) ⊆ N) (i : ℕ) : ((p.coeff i : M) : L) ∈ N := by
  classical
  by_cases hi : i ≤ p.natDegree
  · refine h (Finset.mem_coe.mpr ?_)
    unfold coefSet
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact zero_mem _

lemma aeval_mem_of_coefSet {L : Type*} [Field L] [Algebra K L] [Algebra F L]
    (M : IntermediateField K L) (N : IntermediateField F L) (p : M[X])
    (h : (coefSet M p : Set L) ⊆ N) (t : L) (ht : t ∈ N) : aeval t p ∈ N := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact mul_mem (coeff_mem_of_coefSet M N p h i) (pow_mem ht i)

/-- A polynomial over `M` whose coefficients lie in `N`, as a polynomial over `N`. -/
lemma isAlgebraic_of_coefSet {L : Type*} [Field L] [Algebra K L] [Algebra F L]
    (M : IntermediateField K L) (N : IntermediateField F L) (p : M[X]) (hp0 : p ≠ 0)
    (h : (coefSet M p : Set L) ⊆ N) (t : L) (hp : aeval t p = 0) : IsAlgebraic N t := by
  classical
  set q : N[X] := ∑ i ∈ Finset.range (p.natDegree + 1),
    monomial i (⟨((p.coeff i : M) : L), coeff_mem_of_coefSet M N p h i⟩ : N) with hq
  refine ⟨q, ?_, ?_⟩
  · intro h0
    have hc := congrArg (fun r ↦ r.coeff p.natDegree) h0
    simp only [hq, finset_sum_coeff, coeff_monomial, coeff_zero] at hc
    rw [Finset.sum_eq_single p.natDegree (fun b _ hb ↦ if_neg hb)
      (fun hn ↦ absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) hn), if_pos rfl] at hc
    have : ((p.coeff p.natDegree : M) : L) = 0 := congrArg Subtype.val hc
    exact hp0 (leadingCoeff_eq_zero.mp (Subtype.val_injective this))
  · rw [hq, map_sum]
    have : aeval t p = ∑ i ∈ Finset.range (p.natDegree + 1), ((p.coeff i : M) : L) * t ^ i := by
      rw [aeval_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Algebra.smul_def]; rfl
    rw [← hp, this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [aeval_monomial]
    rfl

variable {L : Type u} [Field L] [Differential L] [Algebra K L] [DifferentialAlgebra K L]
  [Algebra F L] [IsScalarTower F K L]

/-- **Finite support**: every finite subset of an elementary tower over `K` (`K / F` algebraic)
lies in an elementary tower over `F`. -/
lemma IsElementaryTower.finite_support (halg : Algebra.IsAlgebraic F K)
    {M : IntermediateField K L} (hM : IsElementaryTower M) :
    ∀ X : Finset L, (X : Set L) ⊆ M → ∃ N : IntermediateField F L, IsElementaryTower N ∧
      (X : Set L) ⊆ N := by
  classical
  induction hM with
  | base =>
    intro X hX
    refine ⟨IntermediateField.adjoin F (X : Set L), isElementaryTower_adjoin_finset X fun x hx ↦ ?_,
      subset_adjoin F _⟩
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp (hX hx)
    rw [← hk]
    exact (halg.isAlgebraic k).algebraMap
  | adjoin E t _ ht ih =>
    intro X hX
    -- every element is a rational expression in `t` over `E`
    have hrep : ∀ x ∈ E ⊔ K⟮t⟯, ∃ r s : E[X], x = aeval t r / aeval t s := by
      intro x hx
      rw [← IntermediateField.restrictScalars_adjoin_eq_sup] at hx
      exact (IntermediateField.mem_adjoin_simple_iff (F := E) x).mp hx
    choose! r s hrs using hrep
    -- the data of `t`
    obtain ⟨D, hD⟩ : ∃ D : Finset L, (D : Set L) ⊆ E ∧ ∀ N : IntermediateField F L,
        (D : Set L) ⊆ N → IsElementaryOver N t := by
      rcases ht with ⟨p, hp0, hp⟩ | ⟨a, ha, ha0, hta⟩ | ⟨ht0, a, ha, hta⟩
      · refine ⟨coefSet E p, fun z hz ↦ ?_, fun N hN ↦
          Or.inl (isAlgebraic_of_coefSet E N p hp0 hN t hp)⟩
        have hz' := Finset.mem_coe.mp hz
        unfold coefSet at hz'
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz'
        exact (p.coeff i).2
      · refine ⟨{a}, by simpa using ha, fun N hN ↦ Or.inr (Or.inl ⟨a, ?_, ha0, hta⟩)⟩
        exact hN (by simp)
      · refine ⟨{a}, by simpa using ha, fun N hN ↦ Or.inr (Or.inr ⟨ht0, a, ?_, hta⟩)⟩
        exact hN (by simp)
    set X' : Finset L := D ∪ X.biUnion fun x ↦ coefSet E (r x) ∪ coefSet E (s x) with hX'
    have hX'E : (X' : Set L) ⊆ E := by
      intro z hz
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hz) with hz | hz
      · exact hD.1 hz
      · obtain ⟨x, -, hz⟩ := Finset.mem_biUnion.mp hz
        rcases Finset.mem_union.mp hz with hz | hz <;>
        · unfold coefSet at hz
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
          exact SetLike.coe_mem _
    obtain ⟨N, hN, hXN⟩ := ih X' hX'E
    have hDN : (D : Set L) ⊆ N := fun z hz ↦ hXN (Finset.mem_coe.mpr (Finset.mem_union_left _ hz))
    refine ⟨N ⊔ F⟮t⟯, .adjoin N t hN (hD.2 N hDN), fun x hx ↦ ?_⟩
    have hx' := hX hx
    rw [hrs x hx']
    have htN : t ∈ N ⊔ F⟮t⟯ := (le_sup_right : F⟮t⟯ ≤ N ⊔ F⟮t⟯) (mem_adjoin_simple_self F t)
    have hsub : ∀ p ∈ [r x, s x], (coefSet E p : Set L) ⊆ (N ⊔ F⟮t⟯ : IntermediateField F L) := by
      intro p hp z hz
      refine (le_sup_left : N ≤ N ⊔ F⟮t⟯) (hXN (Finset.mem_coe.mpr (Finset.mem_union_right _ ?_)))
      refine Finset.mem_biUnion.mpr ⟨x, hx, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact Finset.mem_union_left _ hz
      · exact Finset.mem_union_right _ hz
    exact div_mem (aeval_mem_of_coefSet E _ _ (hsub _ (by simp)) t htN)
      (aeval_mem_of_coefSet E _ _ (hsub _ (by simp)) t htN)

end Descent

section DescentMain

variable {F K : Type u} [Field F] [Field K] [CharZero F] [Differential F] [Differential K]
  [Algebra F K] [DifferentialAlgebra F K]

/-- **Descent along an algebraic extension of the base**: if `K / F` is algebraic and `f ∈ F`
has an elementary integral over `K`, it has one over `F`. -/
theorem HasElementaryIntegral.of_isAlgebraic (halg : Algebra.IsAlgebraic F K) {f : F}
    (h : HasElementaryIntegral (algebraMap F K f)) : HasElementaryIntegral f := by
  obtain ⟨L, _, _, _, _, hL, g, hg⟩ := h
  let _ : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI hDA : DifferentialAlgebra F L :=
    ⟨fun a ↦ by
      change (algebraMap K L (algebraMap F K a))′ = algebraMap K L (algebraMap F K a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  obtain ⟨N, hN, hgN⟩ := IsElementaryTower.finite_support halg hL {g} (by simp)
  have hc : DerivClosed N := hN.derivClosed
  letI := differentialOfDerivClosed hc
  have hgN' : g ∈ N := hgN (by simp)
  have hDAN : DifferentialAlgebra F N :=
    ⟨fun a ↦ Subtype.val_injective (by
      rw [coe_deriv_of_derivClosed hc]
      exact deriv_algebraMap (A := F) (B := L) a)⟩
  refine ⟨N, inferInstance, inferInstance, inferInstance, hDAN, hN.isElementaryExtension_sub hc,
    ⟨g, hgN'⟩, ?_⟩
  apply Subtype.val_injective
  rw [coe_deriv_of_derivClosed hc, hg]
  rfl

end DescentMain

end Differential
