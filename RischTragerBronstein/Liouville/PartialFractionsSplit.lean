import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.BigOperators.Field
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Splits

/-!
# Partial fractions for a split separable denominator

If `p` splits with simple roots and `deg q < deg p`, then for `x` not a root of `p`

  `q(x) / p(x) = ∑_{p(α) = 0} q(α) / p′(α) · 1 / (x - α)`.

This is Lagrange interpolation in its first barycentric form.
-/

open Polynomial Finset

namespace Polynomial

variable {L : Type*} [Field L] [DecidableEq L]

theorem eval_div_eq_sum_roots {p q : L[X]} (hp : p.Splits) (hsep : p.Separable)
    (hdeg : q.degree < p.degree) {x : L} (hx : eval x p ≠ 0) :
    eval x q / eval x p =
      ∑ α ∈ p.roots.toFinset, eval α q / eval α (derivative p) * (x - α)⁻¹ := by
  have hp0 : p ≠ 0 := fun h ↦ by simp [h] at hx
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  set Rts := p.roots.toFinset with hRts
  have hnodal : p = C p.leadingCoeff * Lagrange.nodal Rts id := by
    conv_lhs => rw [hp.eq_prod_roots]
    rw [Lagrange.nodal_eq, Finset.prod_eq_multiset_prod, hRts, Multiset.toFinset_val,
      (nodup_roots hsep).dedup]
    rfl
  have hinj : Set.InjOn (id : L → L) Rts := Function.injective_id.injOn
  have hcard : p.degree = (#Rts : ℕ) := by
    conv_lhs => rw [hnodal]
    rw [degree_C_mul hlc, Lagrange.degree_nodal]
  have hq := Lagrange.eq_interpolate (s := Rts) (v := id) hinj (hcard ▸ hdeg)
  have hxα : ∀ α ∈ Rts, x ≠ id α := fun α hα hxα ↦ by
    rw [hRts, Multiset.mem_toFinset, mem_roots hp0] at hα
    exact hx (by rw [hxα]; exact hα)
  have hevq := Lagrange.eval_interpolate_not_at_node (r := fun α ↦ eval (id α) q) hxα
  rw [← hq] at hevq
  have hevp : eval x p = p.leadingCoeff * eval x (Lagrange.nodal Rts id) := by
    conv_lhs => rw [hnodal]
    rw [eval_mul, eval_C]
  have hnx : eval x (Lagrange.nodal Rts id) ≠ 0 := fun h0 ↦ hx (by rw [hevp, h0, mul_zero])
  rw [hevq, hevp, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  have hder : eval α (derivative p) =
      p.leadingCoeff * eval α (derivative (Lagrange.nodal Rts id)) := by
    conv_lhs => rw [hnodal]
    rw [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
  have hw := Lagrange.nodalWeight_eq_eval_derivative_nodal (s := Rts) (v := id) hα
  have hw0 := Lagrange.nodalWeight_ne_zero hinj hα
  have hd0 : eval α (derivative (Lagrange.nodal Rts id)) ≠ 0 := fun h0 ↦ by
    rw [hw] at hw0
    exact hw0 (by rw [show id α = α from rfl, h0, inv_zero])
  rw [hder, hw]
  simp only [id]
  field_simp

end Polynomial
