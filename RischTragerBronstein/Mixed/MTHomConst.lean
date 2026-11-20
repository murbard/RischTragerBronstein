import RischTragerBronstein.Mixed.MTCert

/-!
# No exponential of a constant multiple of an exponent

At an exponential level `t = exp a` with the certificate's check (`a′` not a rational combination
of the generators' derivatives), **no `z ≠ 0` in `Fₘ` satisfies `z′ + γ a′ z = 0` for a constant
`γ ≠ 0`** (`hom_const`), even when `γ` is irrational: by the structure theorem `−γ a` is a constant
combination of the generators up to a constant, and differentiating gives a relation among the
derivatives with coefficient `−γ` at `a′`, which `no_rel_gensD` (through `mrel_complete`) forces to
vanish. This is what an irrational eigenvalue `γ` of a limit matrix needs.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **`z′ + γ a′ z = 0` has no non-zero solution in `Fₘ` for a constant `γ ≠ 0`.** -/
theorem hom_const (m : ℕ) (hM : T.MixHyp m) {a : LC m}
    (hc2 : ∀ u ∈ mrel Fc ks m ((MO Fc ks m).deriv a :: gensDC Fc ks m), u.getD 0 0 = 0)
    (γ : Cc) (hγ : γ ≠ 0) (z : L) (hz : z ∈ T.F m) (hz0 : z ≠ 0) :
    z′ + algebraMap Cc L γ * (T.ev m a)′ * z ≠ 0 := by
  intro h0
  have hZ : -(algebraMap Cc L γ * T.ev m a) ∈ T.F m :=
    neg_mem (mul_mem (T.const_mem m γ) (T.ev_mem m a))
  have hK : (algebraMap Cc L γ)′ = 0 := by rw [deriv_algebraMap, T.hC, map_zero]
  have hd : (-(algebraMap Cc L γ * T.ev m a))′ =
      ∑ i ∈ ({0} : Finset ℕ), algebraMap Cc L 1 * logDeriv ((fun _ : ℕ ↦ z) i) := by
    simp only [Finset.sum_singleton, map_one, one_mul, logDeriv]
    rw [map_neg, Derivation.leibniz, hK, smul_zero, add_zero, smul_eq_mul, eq_div_iff hz0]
    linear_combination -h0
  obtain ⟨q, κ, hq⟩ := T.mix_structure m hM _ hZ {0} (fun _ ↦ 1) (fun _ ↦ z)
    (fun _ _ ↦ ⟨hz, hz0⟩) hd
  have hd' := T.deriv_structure m _ q κ hq
  have hrel : algebraMap Cc L (-γ) * (T.ev m a)′ =
      ∑ i ∈ Finset.range m, algebraMap Cc L (q i) * (T.genX i)′ := by
    rw [← hd', map_neg, map_neg, Derivation.leibniz, hK, smul_zero, add_zero, smul_eq_mul]
    ring
  have := T.no_rel_gensD m hM.tr hc2 (-γ) q hrel
  exact hγ (neg_eq_zero.mp this)

end MTower

end Curves.MT
