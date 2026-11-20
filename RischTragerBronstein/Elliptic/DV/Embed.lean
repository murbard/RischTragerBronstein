import RischTragerBronstein.Elliptic.DV.GoodRed
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RingTheory.AdjoinRoot

/-!
# Torsion bounds over number fields via embeddings into `ℚ_p`

* `torsion_order_le_field`: for any field `K` with a `ℚ`-embedding `K → ℚ_p` (`p` odd, good
  reduction), torsion points of `y² = x³ + ax² + bx + c` over `K` have order `≤ #(Option Ẽ(𝔽_p))`;
* `hensel_root`: a simple root of `f ∈ ℤ[x]` modulo `p` lifts to a root in `ℤ_p`;
* `torsion_order_le_adjoin`: hence the bound for `K = ℚ[x]/(f)` whenever `f` has a simple root
  modulo `p`.
-/

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

namespace EllDV

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime] (a b c : ℤ)

/-- **The bound over any field embedded in `ℚ_p`.** -/
theorem torsion_order_le_field {K : Type*} [Field K] [CharZero K] [DecidableEq K] (φ : K →ₐ[ℚ] ℚ_[p])
    (hp2 : p ≠ 2) (hgood : goodRedMod p a b c) (P : (W K a b c).toAffine.Point)
    (ht : IsOfFinAddOrder P) : addOrderOf P ≤ Fintype.card (Option (RedPts p a b c)) := by
  let m : (W K a b c).toAffine.Point →+ (W ℚ_[p] a b c).toAffine.Point :=
    Point.map (W' := (W0 a b c)) φ
  have hm : Function.Injective m := Point.map_injective φ
  have hord : addOrderOf (m P) = addOrderOf P := addOrderOf_injective m hm P
  rw [← hord]
  exact torsion_order_le a b c hp2 (goodRed_of_mod a b c hgood) (m P)
    ((isOfFinAddOrder_iff_nsmul_eq_zero.mpr (by
      obtain ⟨n, hn, hnP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ht
      exact ⟨n, hn, by rw [← map_nsmul, hnP, map_zero]⟩)))

/-- **Hensel**: a simple root modulo `p` lifts. -/
theorem hensel_root (f : ℤ[X]) (s : ZMod p) (hs : (f.map (Int.castRingHom (ZMod p))).eval s = 0)
    (hs' : ((derivative f).map (Int.castRingHom (ZMod p))).eval s ≠ 0) :
    ∃ z : ℤ_[p], f.aeval z = 0 := by
  set a : ℤ_[p] := (s.val : ℤ_[p])
  have ha : PadicInt.toZMod a = s := by
    simp only [a, map_natCast, ZMod.natCast_zmod_val]
  have hev : ∀ g : ℤ[X], PadicInt.toZMod (g.aeval a) = (g.map (Int.castRingHom (ZMod p))).eval s := by
    intro g
    rw [aeval_def, eval_map, ← ha, hom_eval₂]
    congr 1
    ext n
    simp
  have h1 : ‖(f.aeval a : ℚ_[p])‖ < 1 := by
    rw [norm_lt_one_iff_toZMod, hev]; exact hs
  have h2 : ‖((derivative f).aeval a : ℚ_[p])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
    rw [norm_lt_one_iff_toZMod, hev]; exact hs'
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := f) (a := a) (by
    change ‖(f.aeval a : ℚ_[p])‖ < ‖((derivative f).aeval a : ℚ_[p])‖ ^ 2
    rw [h2, one_pow]; exact h1)
  exact ⟨z, hz⟩

/-- **The bound over `ℚ[x]/(f)`** when `f` has a simple root modulo `p`. -/
theorem torsion_order_le_adjoin (fQ : ℚ[X]) [Fact (Irreducible fQ)] (f : ℤ[X])
    (hfQ : fQ = f.map (Int.castRingHom ℚ))
    (s : ZMod p) (hs : (f.map (Int.castRingHom (ZMod p))).eval s = 0)
    (hs' : ((derivative f).map (Int.castRingHom (ZMod p))).eval s ≠ 0)
    (hp2 : p ≠ 2) (hgood : goodRedMod p a b c)
    (P : (W (AdjoinRoot fQ) a b c).toAffine.Point)
    (ht : IsOfFinAddOrder P) : addOrderOf P ≤ Fintype.card (Option (RedPts p a b c)) := by
  subst hfQ
  obtain ⟨z, hz⟩ := hensel_root f s hs hs'
  have hcoe : ∀ g : ℤ[X], aeval (z : ℚ_[p]) (g.map (Int.castRingHom ℚ)) =
      ((g.aeval z : ℤ_[p]) : ℚ_[p]) := by
    intro g
    induction g using Polynomial.induction_on' with
    | add g h hg hh => simp only [Polynomial.map_add, map_add, hg, hh, PadicInt.coe_add]
    | monomial n k => simp
  have hroot : (f.map (Int.castRingHom ℚ)).eval₂ (Algebra.ofId ℚ ℚ_[p]) (z : ℚ_[p]) = 0 := by
    change eval₂ (algebraMap ℚ ℚ_[p]) (z : ℚ_[p]) _ = 0
    rw [← aeval_def, hcoe f, hz]
    rfl
  exact torsion_order_le_field a b c
    (AdjoinRoot.liftAlgHom (f.map (Int.castRingHom ℚ)) (Algebra.ofId ℚ ℚ_[p]) (z : ℚ_[p]) hroot)
    hp2 hgood P ht

end EllDV
