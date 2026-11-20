import RischTragerBronstein.Algebraic.HypCertComplete
import RischTragerBronstein.Algebraic.EllQuartic

/-!
# Genus-two examples

In any differential field `E = Kc(x)(y)` with constants `Kc`, `x′ = 1`, `y² = x⁵ − x` (genus 2):

* `∫ dx / (x² √(x⁵ − x))` is **not** elementary;
* `∫ (3x⁴ + 1) / (2x √(x⁵ − x)) dx = √(x⁵ − x) / x` is: the algorithm answers yes.
-/

open Polynomial Differential

namespace EllAlgo.Genus2Example

/-- `x⁵ − x`. -/
def pG : CPoly ℚ := [0, -1, 0, 0, 0, 1]

lemma toPoly_pG : CPoly.toPoly pG = X ^ 5 - X := by
  simp [pG, CPoly.toPoly]; ring

lemma squarefree_pG : Squarefree (CPoly.toPoly pG) :=
  (sepCheck_sound (by decide +kernel : sepCheck pG = true)).squarefree

lemma odd_pG : Odd (CPoly.toPoly pG).natDegree := by
  rw [toPoly_pG, show (X ^ 5 - X : ℚ[X]).natDegree = 5 by compute_degree!]; decide

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ dx / (x² √(x⁵ − x))` is not elementary** (genus 2, a double pole at a branch point). -/
theorem genus2_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 5 - x) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬HasElementaryIntegral (1 / (x ^ 2 * y)) := by
  have hy' : y ^ 2 = aeval x (CPoly.toPoly pG) := by rw [toPoly_pG]; simp [hy]
  have hd : CPoly.hypCertDecide pG [1] [0, 0, 1] = some false := by decide +kernel
  obtain ⟨W, V, B0, hD, hV, hid, hdeg, hb⟩ := CPoly.hypCertDecide_spec _ _ _ _ hd
  have := hyp_decides_cert hC hCall x y hx pG squarefree_pG odd_pG hy' hgen _ _ _ _ _ hD hV hid
    hdeg
  rw [show aeval x (CPoly.toPoly ([1] : CPoly ℚ)) = 1 by simp [CPoly.toPoly],
    show aeval x (CPoly.toPoly ([0, 0, 1] : CPoly ℚ)) = x ^ 2 by simp [CPoly.toPoly]; ring] at this
  rw [this]
  intro h0
  exact Bool.false_ne_true (hb.mpr h0)

/-- `∫ (3x⁴ + 1) / (2x √(x⁵ − x)) dx = √(x⁵ − x)/x`: the algorithm answers yes. -/
theorem genus2_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 5 - x) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral ((3 * x ^ 4 + 1) / (2 * x * y)) := by
  have hy' : y ^ 2 = aeval x (CPoly.toPoly pG) := by rw [toPoly_pG]; simp [hy]
  have hd : CPoly.hypCertDecide pG [1, 0, 0, 0, 3] [0, 2] = some true := by decide +kernel
  obtain ⟨W, V, B0, hD, hV, hid, hdeg, hb⟩ := CPoly.hypCertDecide_spec _ _ _ _ hd
  have := hyp_decides_cert hC hCall x y hx pG squarefree_pG odd_pG hy' hgen _ _ _ _ _ hD hV hid
    hdeg
  rw [show aeval x (CPoly.toPoly ([1, 0, 0, 0, 3] : CPoly ℚ)) = 3 * x ^ 4 + 1 by
      simp [CPoly.toPoly]; ring,
    show aeval x (CPoly.toPoly ([0, 2] : CPoly ℚ)) = 2 * x by simp [CPoly.toPoly]] at this
  exact this.mpr (hb.mp rfl)

end EllAlgo.Genus2Example
