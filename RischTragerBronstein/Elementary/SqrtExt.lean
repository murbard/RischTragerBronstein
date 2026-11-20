import RischTragerBronstein.Elementary.Algebraic
import RischTragerBronstein.Elementary.Trans
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Adjoining the square root of a constant

For a differential field `L` of characteristic zero and a non-zero constant `d`, there is an
elementary (finite algebraic) extension `L'` of `L` containing a constant `s` with `s² = d`
(`exists_sqrt_ext`): `L` itself if `d` is a square there, else `L[X]/(X² − d)` with its unique
derivation (Mathlib). Used to remove "`√d` is a constant of the base field" hypotheses.
-/

open Polynomial

universe u

namespace Differential

/-- **A square root of a constant, in an elementary extension.** -/
theorem exists_sqrt_ext {L : Type u} [Field L] [Differential L] [CharZero L] (d : L)
    (hd : d′ = 0) (hd0 : d ≠ 0) :
    ∃ (L' : Type u) (_ : Field L') (_ : Differential L') (_ : Algebra L L')
      (_ : DifferentialAlgebra L L'), IsElementaryExtension L L' ∧
        ∃ s : L', s ^ 2 = algebraMap L L' d ∧ s′ = 0 ∧
          ∀ z : L', ∃ u v : L, z = algebraMap L L' u + algebraMap L L' v * s := by
  -- `s² = d` with `d′ = 0` forces `s′ = 0`
  have key : ∀ {M : Type u} [Field M] [Differential M] [CharZero M] (s c : M),
      s ^ 2 = c → c′ = 0 → c ≠ 0 → s′ = 0 := by
    intro M _ _ _ s c hs hc hc0
    have hs0 : s ≠ 0 := by rintro rfl; apply hc0; rw [← hs]; ring
    have := congrArg (fun z : M ↦ z′) hs
    simp only [pow_two, Derivation.leibniz, smul_eq_mul, hc] at this
    have h2 : (2 * s) * s′ = 0 := by linear_combination this
    exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero hs0)
  by_cases hsq : ∃ s : L, s ^ 2 = d
  · obtain ⟨s, hs⟩ := hsq
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_, s, by simpa using hs,
      key s d hs hd hd0, fun z ↦ ⟨z, 0, by simp⟩⟩
    have h : (⊥ : IntermediateField L L) = ⊤ :=
      eq_top_iff.mpr fun x _ ↦ IntermediateField.mem_bot.mpr ⟨x, rfl⟩
    unfold IsElementaryExtension
    rw [← h]
    exact IsElementaryTower.base
  · push_neg at hsq
    set p : L[X] := X ^ 2 - C d with hp
    have hpdeg : p.natDegree = 2 := by rw [hp]; compute_degree!
    have hmon : p.Monic := by rw [hp]; monicity!
    have hirr : Irreducible p := by
      refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hpdeg]; decide) fun x hx ↦ ?_
      apply hsq x
      have := hx.eq_zero
      simp only [hp, eval_sub, eval_pow, eval_X, eval_C] at this
      linear_combination this
    haveI : Fact (Irreducible p) := ⟨hirr⟩
    haveI : Fact p.Monic := ⟨hmon⟩
    haveI : Module.Finite L (AdjoinRoot p) := hmon.finite_adjoinRoot
    haveI : FiniteDimensional L (AdjoinRoot p) := this
    haveI : CharZero (AdjoinRoot p) :=
      charZero_of_injective_algebraMap (algebraMap L (AdjoinRoot p)).injective
    have hroot : AdjoinRoot.root p ^ 2 = algebraMap L (AdjoinRoot p) d := by
      have := AdjoinRoot.eval₂_root p
      simp only [hp, eval₂_sub, eval₂_X_pow, eval₂_C] at this
      rw [← AdjoinRoot.algebraMap_eq] at this
      linear_combination this
    refine ⟨AdjoinRoot p, inferInstance, inferInstance, inferInstance, inferInstance,
      isElementaryExtension_of_finiteDimensional, AdjoinRoot.root p, hroot, ?_, ?_⟩
    · refine key _ _ hroot (by rw [deriv_algebraMap, hd, map_zero]) ?_
      exact (map_ne_zero_iff _ (algebraMap L (AdjoinRoot p)).injective).mpr hd0
    · intro z
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
      have hmod : AdjoinRoot.mk p q = AdjoinRoot.mk p (q %ₘ p) := by
        rw [AdjoinRoot.mk_eq_mk]
        refine ⟨q /ₘ p, ?_⟩
        have := modByMonic_add_div q p
        linear_combination -this
      have hdeg : (q %ₘ p).natDegree ≤ 1 := by
        have := natDegree_modByMonic_lt q hmon (by intro h; rw [h] at hpdeg; simp at hpdeg)
        rw [hpdeg] at this; omega
      rw [hmod, eq_X_add_C_of_natDegree_le_one hdeg]
      refine ⟨(q %ₘ p).coeff 0, (q %ₘ p).coeff 1, ?_⟩
      simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
      rw [AdjoinRoot.algebraMap_eq]
      ring


private lemma deriv_ratCast_S {M : Type*} [Field M] [CharZero M] [Differential M] (q : ℚ) :
    ((q : M))′ = 0 := by
  have hd : ((q.den : ℤ) : M) ≠ 0 := by exact_mod_cast q.den_nz
  have e : (q : M) * ((q.den : ℤ) : M) = ((q.num : ℤ) : M) := by
    rw [← Rat.cast_intCast, ← Rat.cast_intCast, ← Rat.cast_mul]
    congr 1
    exact_mod_cast Rat.mul_den_eq_num q
  have := congrArg (fun z : M ↦ z′) e
  simp only [Derivation.leibniz, Derivation.map_intCast, smul_eq_mul, mul_zero, zero_add] at this
  exact (mul_eq_zero.mp this).resolve_left hd

/-- **Square roots of finitely many rational constants, in one elementary extension.** -/
theorem exists_sqrts_ext {L : Type u} [Field L] [Differential L] [CharZero L] :
    ∀ ds : List ℚ, (∀ d ∈ ds, d ≠ 0) →
      ∃ (L' : Type u) (_ : Field L') (_ : Differential L') (_ : Algebra L L')
        (_ : DifferentialAlgebra L L'), IsElementaryExtension L L' ∧ CharZero L' ∧
          ∀ d ∈ ds, ∃ s : L', s ^ 2 = ((d : ℚ) : L') ∧ s′ = 0
  | [], _ => by
    refine ⟨L, inferInstance, inferInstance, Algebra.id L, ⟨fun _ ↦ rfl⟩, ?_, inferInstance,
      by simp⟩
    have h' : (⊥ : IntermediateField L L) = ⊤ :=
      eq_top_iff.mpr fun x _ ↦ IntermediateField.mem_bot.mpr ⟨x, rfl⟩
    unfold IsElementaryExtension
    rw [← h']
    exact IsElementaryTower.base
  | d :: ds, hds => by
    obtain ⟨L1, _, _, _, _, hE1, _, hr1⟩ := exists_sqrts_ext (L := L) ds fun d' hd' ↦
      hds d' (List.mem_cons_of_mem _ hd')
    obtain ⟨L2, _, _, _, _, hE2, sq, hsq2, hsq', -⟩ := exists_sqrt_ext (((d : ℚ) : L1))
      (deriv_ratCast_S _) (by exact_mod_cast hds d List.mem_cons_self)
    letI : Algebra L L2 := ((algebraMap L1 L2).comp (algebraMap L L1)).toAlgebra
    haveI : IsScalarTower L L1 L2 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hDA : DifferentialAlgebra L L2 :=
      ⟨fun a ↦ by
        change (algebraMap L1 L2 (algebraMap L L1 a))′ = algebraMap L1 L2 (algebraMap L L1 a′)
        rw [deriv_algebraMap, deriv_algebraMap]⟩
    have : CharZero L2 := charZero_of_injective_algebraMap (algebraMap L L2).injective
    refine ⟨L2, inferInstance, inferInstance, inferInstance, hDA, hE1.trans hE2, this, ?_⟩
    intro d' hd'
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact ⟨sq, by rw [hsq2, map_ratCast], hsq'⟩
    · obtain ⟨s1, hs1, hs1'⟩ := hr1 d' hd'
      exact ⟨algebraMap L1 L2 s1, by rw [← map_pow, hs1, map_ratCast],
        by rw [deriv_algebraMap, hs1', map_zero]⟩

end Differential
