import RischTragerBronstein.Algebraic.SupKernel
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.KummerExtension

/-!
# The norm of `∑ Wⱼ(x) yʲ` as a resultant

`resN f n W = Res_Y(Yⁿ − f(X), W(X, Y)) ∈ R[X]`, an explicit polynomial norm of the function
`W = ∑ Wⱼ(x) yʲ` on `yⁿ = f(x)`, defined over any commutative ring and compatible with ring maps
(`resN_map`). At a point `(z, Y)` of the curve over a domain containing a primitive `n`-th root
of unity it is the product of the values at the `n` points above `z` (`resN_eval`).
-/

open Polynomial

namespace Sup

section Ring

variable {R : Type*} [CommRing R]

/-- The norm `Res_Y(Yⁿ − f, W)`. -/
noncomputable def resN (f : R[X]) (n : ℕ) (W : R[X][X]) : R[X] :=
  resultant (X ^ n - Polynomial.C f) W n (n - 1)

lemma resN_map {S : Type*} [CommRing S] (φ : R →+* S) (f : R[X]) (n : ℕ) (W : R[X][X]) :
    (resN f n W).map φ = resN (f.map φ) n (W.map (mapRingHom φ)) := by
  rw [resN, resN, ← coe_mapRingHom, ← resultant_map_map]
  congr 1
  simp [Polynomial.map_sub, Polynomial.map_pow]

lemma resN_eval_eq (f : R[X]) (n : ℕ) (W : R[X][X]) (z : R) :
    (resN f n W).eval z = resultant (X ^ n - Polynomial.C (f.eval z))
      (W.map (evalRingHom z)) n (n - 1) := by
  rw [resN, ← coe_evalRingHom, ← resultant_map_map]
  congr 1
  simp [Polynomial.map_sub, Polynomial.map_pow]

end Ring

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **The norm at a point** is the product of the values at the points above it. -/
theorem resN_eval (f : R[X]) {n : ℕ} (hn : 0 < n) {ζ : R} (hζ : IsPrimitiveRoot ζ n)
    (W : R[X][X]) (hW : W.natDegree ≤ n - 1) (z Y : R) (hY : Y ^ n = f.eval z) :
    (resN f n W).eval z = ∏ k ∈ Finset.range n, evalW W z (ζ ^ k * Y) := by
  rw [resN_eval_eq]
  have hsplit : X ^ n - Polynomial.C (f.eval z) = ∏ k ∈ Finset.range n,
      (X - Polynomial.C (ζ ^ k * Y)) := X_pow_sub_C_eq_prod hζ hn hY
  have hmon : (X ^ n - Polynomial.C (f.eval z)).Monic := monic_X_pow_sub_C _ hn.ne'
  have hdeg : (X ^ n - Polynomial.C (f.eval z)).natDegree = n := natDegree_X_pow_sub_C
  have hspl : (X ^ n - Polynomial.C (f.eval z)).Splits := by
    rw [hsplit]
    exact Splits.prod fun k _ ↦ Splits.X_sub_C _
  have hWd : (W.map (evalRingHom z)).natDegree ≤ n - 1 := natDegree_map_le.trans hW
  have := resultant_eq_prod_eval _ _ (n - 1) hWd hspl
  rw [hdeg, hmon.leadingCoeff, one_pow, one_mul] at this
  rw [this]
  have hms : ∏ k ∈ Finset.range n, (X - Polynomial.C (ζ ^ k * Y)) =
      (((Finset.range n).val.map fun k ↦ ζ ^ k * Y).map fun a ↦ X - Polynomial.C a).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  rw [hsplit, hms, roots_multiset_prod_X_sub_C, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

end Domain

end Sup
