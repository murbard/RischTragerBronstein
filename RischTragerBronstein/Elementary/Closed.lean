import RischTragerBronstein.Elementary.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.Minpoly.Field

/-!
# The fields of an elementary tower are differential subfields

`IsElementaryTower.derivClosed`: every intermediate field `M` of an elementary tower of `K / F` is
closed under the derivation of `K`. Hence `M` is a differential field in its own right
(`differentialOfDerivClosed`), and `F → M → K` are morphisms of differential fields. This is what
allows one-step results about `M(t) / M` — Liouville's theorem, in particular — to be applied along
a tower given abstractly as a chain of subfields of `K`.
-/

open IntermediateField Polynomial

namespace Differential

variable {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K] [DifferentialAlgebra F K]

/-- `M` is closed under the derivation of `K`. -/
def DerivClosed (M : IntermediateField F K) : Prop := ∀ x ∈ M, x′ ∈ M

/-- The differential structure induced on a derivation-closed intermediate field. -/
@[reducible] def differentialOfDerivClosed {M : IntermediateField F K} (h : DerivClosed M) :
    Differential M :=
  ⟨{  toFun := fun x ↦ ⟨(x : K)′, h x x.2⟩
      map_add' := fun x y ↦ Subtype.ext (by simp)
      map_smul' := fun n x ↦ Subtype.ext (by simp)
      map_one_eq_zero' := Subtype.ext (by simp)
      leibniz' := fun x y ↦ Subtype.ext (by simp [Derivation.leibniz]) }⟩

lemma coe_deriv_of_derivClosed {M : IntermediateField F K} (h : DerivClosed M) (x : M) :
    letI := differentialOfDerivClosed h
    ((x′ : M) : K) = (x : K)′ := rfl

lemma differentialAlgebra_of_derivClosed {M : IntermediateField F K} (h : DerivClosed M) :
    letI := differentialOfDerivClosed h
    DifferentialAlgebra M K :=
  letI := differentialOfDerivClosed h
  ⟨fun _ ↦ rfl⟩

lemma derivClosed_bot : DerivClosed (⊥ : IntermediateField F K) := by
  intro x hx
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hx
  rw [deriv_algebraMap]
  exact (⊥ : IntermediateField F K).algebraMap_mem _

/-- If `M` is derivation-closed and `t′ ∈ M(t)`, then `M(t)` is derivation-closed. -/
lemma DerivClosed.adjoin {M : IntermediateField F K} (hM : DerivClosed M) (t : K)
    (ht : t′ ∈ M ⊔ F⟮t⟯) : DerivClosed (M ⊔ F⟮t⟯) := by
  set N := M ⊔ F⟮t⟯ with hN
  -- the subfield of `N` of elements whose derivative is in `N`
  let S : IntermediateField F K :=
    { carrier := {x | x ∈ N ∧ x′ ∈ N}
      mul_mem' := fun {x y} hx hy ↦ ⟨mul_mem hx.1 hy.1, by
        rw [Derivation.leibniz]
        exact add_mem (mul_mem hx.1 hy.2) (mul_mem hy.1 hx.2)⟩
      one_mem' := ⟨one_mem _, by simp⟩
      add_mem' := fun {x y} hx hy ↦ ⟨add_mem hx.1 hy.1, by
        rw [map_add]; exact add_mem hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, by simp⟩
      algebraMap_mem' := fun a ↦ ⟨N.algebraMap_mem a, by
        rw [deriv_algebraMap]; exact N.algebraMap_mem _⟩
      inv_mem' := fun x hx ↦ ⟨inv_mem hx.1, by
        rw [Derivation.leibniz_inv]
        exact mul_mem (neg_mem (pow_mem (inv_mem hx.1) 2)) hx.2⟩ }
  have hMS : M ≤ S := fun x hx ↦
    ⟨(le_sup_left : M ≤ N) hx, (le_sup_left : M ≤ N) (hM x hx)⟩
  have htS : F⟮t⟯ ≤ S := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨(le_sup_right : F⟮t⟯ ≤ N) (mem_adjoin_simple_self F t), ht⟩
  intro x hx
  exact ((sup_le hMS htS) hx).2

variable [CharZero F]

/-- The derivative of an element algebraic over a derivation-closed `M` lies in `M(t)`. -/
lemma deriv_mem_of_isAlgebraic {M : IntermediateField F K} (hM : DerivClosed M) {t : K}
    (ht : IsAlgebraic M t) : t′ ∈ M ⊔ F⟮t⟯ := by
  let _ := differentialOfDerivClosed hM
  have hDA : DifferentialAlgebra M K := differentialAlgebra_of_derivClosed hM
  set N := M ⊔ F⟮t⟯
  have htN : t ∈ N := (le_sup_right : F⟮t⟯ ≤ N) (mem_adjoin_simple_self F t)
  have haeval : ∀ q : M[X], aeval t q ∈ N := fun q ↦ by
    rw [aeval_eq_sum_range]
    refine sum_mem fun i _ ↦ ?_
    rw [Algebra.smul_def]
    exact mul_mem ((le_sup_left : M ≤ N) (q.coeff i).2) (pow_mem htN i)
  have hint : IsIntegral M t := ht.isIntegral
  have : CharZero M := charZero_of_injective_algebraMap (algebraMap F M).injective
  set p := minpoly M t
  have hsep : p.Separable := (minpoly.irreducible hint).separable
  have hp : aeval t p = 0 := minpoly.aeval M t
  have hne : aeval t (derivative p) ≠ 0 := hsep.aeval_derivative_ne_zero hp
  have h := deriv_aeval_eq t p
  rw [hp, map_zero] at h
  have : t′ = -aeval t (mapCoeffs p) / aeval t (derivative p) := by
    field_simp
    linear_combination -h
  rw [this]
  exact div_mem (neg_mem (haeval _)) (haeval _)

/-- **Every field of an elementary tower is a differential subfield.** -/
theorem IsElementaryTower.derivClosed {M : IntermediateField F K} (hM : IsElementaryTower M) :
    DerivClosed M := by
  induction hM with
  | base => exact derivClosed_bot
  | adjoin E t _ ht ih =>
    refine ih.adjoin t ?_
    have htN : t ∈ E ⊔ F⟮t⟯ := (le_sup_right : F⟮t⟯ ≤ _) (mem_adjoin_simple_self F t)
    have hE : E ≤ E ⊔ F⟮t⟯ := le_sup_left
    rcases ht with ht | ⟨a, ha, -, hta⟩ | ⟨ht0, a, ha, hta⟩
    · exact deriv_mem_of_isAlgebraic ih ht
    · rw [hta, logDeriv]
      exact div_mem (hE (ih a ha)) (hE ha)
    · have : t′ = a′ * t := by
        rw [logDeriv, div_eq_iff ht0] at hta
        exact hta
      rw [this]
      exact mul_mem (hE (ih a ha)) htN

end Differential
