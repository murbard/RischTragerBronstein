import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Discriminant

/-!
# The resultant as a product over roots, and the discriminant of a power basis

* `resultant_eq_prod_eval`: for `f` monic and split, `Res(f, g) = ∏_{f(α) = 0} g(α)`;
* `discr_eq_resultant`: the discriminant of the power basis of a root `y` of a monic
  irreducible separable `f` is `± Res(f, f′)`.

Used to bound the denominators of integral elements in the power basis
(`discr_mul_isIntegral_mem_adjoin`).
-/

open Polynomial

namespace Curves

section ProdRoots

variable {E : Type*} [Field E]

/-- **The resultant as a product of values at the roots.** -/
theorem resultant_eq_prod_eval (f g : E[X]) (hf : f.Monic) (hs : f.Splits) (hg : g ≠ 0)
    (hgs : g.Splits) :
    resultant f g f.natDegree g.natDegree = (f.roots.map fun α ↦ g.eval α).prod := by
  set c := g.leadingCoeff with hc
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hg
  set g1 := Polynomial.C c⁻¹ * g with hg1
  have hg1m : g1.Monic := by
    rw [Monic, hg1, leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hc0]
  have hgg1 : g = Polynomial.C c * g1 := by
    rw [hg1, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc0, Polynomial.C_1, one_mul]
  have hdeg1 : g1.natDegree = g.natDegree := by
    rw [hg1, natDegree_C_mul (inv_ne_zero hc0)]
  have hg1s : g1.Splits := by
    rw [hg1]; exact hgs.C_mul _
  rw [hgg1, resultant_C_mul_right, natDegree_C_mul hc0]
  rw [resultant_eq_prod_roots_sub f g1 hf hg1m hs hg1s, Multiset.prod_map_product_eq_prod_prod]
  have hcard : f.roots.card = f.natDegree := (hs.natDegree_eq_card_roots).symm
  have hval : ∀ α, eval α (Polynomial.C c * g1) = c * (g1.roots.map fun β ↦ α - β).prod := fun α ↦ by
    rw [eval_mul, eval_C, hg1s.eval_eq_prod_roots, hg1m.leadingCoeff, one_mul]
  simp only [hval]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]

end ProdRoots

section Discr

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

/-- **The discriminant of a power basis is `± Res(f, f′)`**, `f` the minimal polynomial. -/
theorem discr_eq_resultant (pb : PowerBasis K L) :
    Algebra.discr K pb.basis = (-1) ^ (Module.finrank K L * (Module.finrank K L - 1) / 2) *
      resultant (minpoly K pb.gen) (derivative (minpoly K pb.gen)) (minpoly K pb.gen).natDegree
        (derivative (minpoly K pb.gen)).natDegree := by
  classical
  rw [Algebra.discr_powerBasis_eq_norm]
  congr 1
  set E := AlgebraicClosure L
  set f := minpoly K pb.gen with hfdef
  have hfm : f.Monic := minpoly.monic pb.isIntegral_gen
  have hsep : f.Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hf' : derivative f ≠ 0 := by
    intro h0
    have := hsep
    rw [separable_def, h0, isCoprime_zero_right] at this
    exact (minpoly.not_isUnit K pb.gen) this
  apply (algebraMap K E).injective
  rw [Algebra.norm_eq_prod_embeddings K E, ← resultant_map_map,
    ← natDegree_map_eq_of_injective (algebraMap K E).injective f,
    ← natDegree_map_eq_of_injective (algebraMap K E).injective (derivative f),
    resultant_eq_prod_eval (f.map (algebraMap K E)) ((derivative f).map (algebraMap K E))
      (hfm.map _) (IsAlgClosed.splits _) ((Polynomial.map_ne_zero_iff (algebraMap K E).injective).mpr hf')
      (IsAlgClosed.splits _)]
  have h1 : ∀ σ : L →ₐ[K] E, σ (aeval pb.gen (derivative f)) =
      eval (σ pb.gen) ((derivative f).map (algebraMap K E)) := fun σ ↦ by
    rw [← aeval_algHom_apply, aeval_def, eval_map]
  simp_rw [h1]
  have hnd : ((f.map (algebraMap K E)).roots).Nodup := nodup_roots (hsep.map)
  rw [Fintype.prod_equiv pb.liftEquiv' (fun σ ↦ eval (σ pb.gen) ((derivative f).map (algebraMap K E)))
    (fun y ↦ eval y.1 ((derivative f).map (algebraMap K E)))
    (fun σ ↦ by rw [PowerBasis.liftEquiv'_apply_coe])]
  rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr hnd]
  exact fun _ ↦ rfl

end Discr

end Curves
