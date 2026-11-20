import RischTragerBronstein.Algebraic.HypLogField
import RischTragerBronstein.Algebraic.EllIrrationalExample
import Mathlib.Algebra.QuadraticAlgebra.Basic
import RischTragerBronstein.Algebraic.EllQuadOrbit

/-!
# An irrational-residue elliptic integral proved elementary

On `E : y² = x³ + 2x² − 2x`, the points `P = (√2, 2)` and `σP = (−√2, 2)` satisfy `2(P − σP) = 0`.
The integrand `(2x² + 4) / ((x² − 2) y)` has the irrational residues `±√2` at `P`, `σP` and no
holomorphic remainder, so it is elementary:
`∫ (2x² + 4) dx / ((x² − 2)√(x³ + 2x² − 2x)) = (√2/2) log((a + b y)/(x² − 2)²)` with `a, b ∈ ℚ(√2)[x]`
found by the Riemann–Roch search over `ℚ(√2)` (`logCertF`) and checked by the kernel
(`logCheckF_sound`). (Without the term `2/y`, i.e. for `8/((x² − 2) y)`, the remainder `−2 dx/y`
makes the integral non-elementary.)
-/

open Polynomial Differential

namespace EllAlgo.IrrationalElemExample

open CPoly

abbrev Q2 := QuadraticAlgebra ℚ 2 0

instance : Fact (¬IsSquare (2 : ℚ)) := ⟨by
  rintro ⟨q, hq⟩
  have h2 : ((q : ℝ)) ^ 2 = 2 := by rw [sq]; exact_mod_cast hq.symm
  apply irrational_sqrt_two
  refine ⟨|q|, ?_⟩
  push_cast
  rw [← Real.sqrt_sq_eq_abs, h2]⟩

/-- `x³ + 2x² − 2x` over `ℚ(√2)`. -/
def p : CPoly Q2 := [0, -2, 2, 1]

/-- The certificate found by `logCertF p [(√2, 2, 2), (−√2, 2, −2)]`. -/
def ca : CPoly Q2 := [⟨0, -1 / 2⟩, ⟨0, 4⟩, ⟨0, -7 / 2⟩, ⟨0, -2⟩, ⟨0, -1 / 8⟩]
def cb : CPoly Q2 := [-2, 4, 1]
def cd : CPoly Q2 := [4, 0, -4, 0, 1]

lemma hcheck : logCheckF p [4, 0, 2] [-2, 0, 1] [] [1] [(⟨0, 1 / 2⟩, ca, cb, cd)] = true := by
  decide +kernel

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ (2x² + 4) dx / ((x² − 2)√(x³ + 2x² − 2x))` is elementary** (constants containing `√2`). -/
theorem ex_irrational_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 2 * x ^ 2 - 2 * x) (s2 : Kc) (hs2 : s2 ^ 2 = 2) :
    HasElementaryIntegral ((2 * x ^ 2 + 4) / ((x ^ 2 - 2) * y)) := by
  let ι : Q2 →+* Kc := (QuadraticAlgebra.lift ⟨s2, by rw [← sq, hs2]; simp⟩ :
    Q2 →ₐ[ℚ] Kc).toRingHom
  have hq : ∀ q : ℚ, ι (q : Q2) = (q : Kc) := fun q ↦ map_ratCast ι q
  have hev : ∀ l : List ℚ, evF ι x (l.map (fun q : ℚ ↦ (q : Q2))) = aeval x (toPoly l) := by
    intro l
    induction l with
    | nil => simp [evF, CPoly.toPoly]
    | cons q l ih =>
      simp only [List.map_cons, evF, toPoly_cons, Polynomial.map_add, Polynomial.map_mul, map_C,
        Polynomial.map_X, map_add, map_mul, aeval_C, aeval_X] at ih ⊢
      rw [ih, hq]
      simp
  have hp : evF ι x p = x ^ 3 + 2 * x ^ 2 - 2 * x := by
    have := hev [0, -2, 2, 1]
    simp only [List.map_cons, List.map_nil] at this
    rw [show p = [((0 : ℚ) : Q2), ((-2 : ℚ) : Q2), ((2 : ℚ) : Q2), ((1 : ℚ) : Q2)] by
      simp [p], this]
    simp [CPoly.toPoly]; ring
  have h := logCheckF_sound hC ι x y hx p [4, 0, 2] [-2, 0, 1] [] [1] _ (by rw [hp]; exact hy) hcheck
  have hA : evF ι x ([4, 0, 2] : CPoly Q2) = 2 * x ^ 2 + 4 := by
    have := hev [4, 0, 2]
    simp only [List.map_cons, List.map_nil] at this
    rw [show ([4, 0, 2] : CPoly Q2) = [((4 : ℚ) : Q2), ((0 : ℚ) : Q2), ((2 : ℚ) : Q2)] by
      simp, this]
    simp [CPoly.toPoly]; ring
  have hD : evF ι x ([-2, 0, 1] : CPoly Q2) = x ^ 2 - 2 := by
    have := hev [-2, 0, 1]
    simp only [List.map_cons, List.map_nil] at this
    rw [show ([-2, 0, 1] : CPoly Q2) = [((-2 : ℚ) : Q2), ((0 : ℚ) : Q2), ((1 : ℚ) : Q2)] by
      simp, this]
    simp [CPoly.toPoly]; ring
  rwa [hA, hD] at h

lemma hcheck8 : logCheckFB p [8] [-2, 0, 1] [] [1] [-2] [(⟨0, 1 / 2⟩, ca, cb, cd)] = true := by
  decide +kernel

/-- **`∫ 8 dx / ((x² − 2)√(x³ + 2x² − 2x))` is not elementary**: the torsion conditions hold
(`2(P − σP) = 0`) but the log part leaves the holomorphic remainder `−2 dx / y`. -/
theorem ex_irrational_remainder_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 2 * x ^ 2 - 2 * x) (hgen : ∀ z : E, InHyp Kc x y z)
    (s2 : Kc) (hs2 : s2 ^ 2 = 2) :
    ¬HasElementaryIntegral (8 / ((x ^ 2 - 2) * y)) := by
  let ι : Q2 →+* Kc := (QuadraticAlgebra.lift ⟨s2, by rw [← sq, hs2]; simp⟩ :
    Q2 →ₐ[ℚ] Kc).toRingHom
  have hq : ∀ q : ℚ, ι (q : Q2) = (q : Kc) := fun q ↦ map_ratCast ι q
  have hev : ∀ l : List ℚ, evF ι x (l.map (fun q : ℚ ↦ (q : Q2))) = aeval x (toPoly l) := by
    intro l
    induction l with
    | nil => simp [evF, CPoly.toPoly]
    | cons q l ih =>
      simp only [List.map_cons, evF, toPoly_cons, Polynomial.map_add, Polynomial.map_mul, map_C,
        Polynomial.map_X, map_add, map_mul, aeval_C, aeval_X] at ih ⊢
      rw [ih, hq]
      simp
  set pQ : CPoly ℚ := [0, -2, 2, 1] with hpQd
  have hpQ : evF ι x p = aeval x (toPoly pQ) := by
    have := hev [0, -2, 2, 1]
    simp only [List.map_cons, List.map_nil] at this
    rw [show p = [((0 : ℚ) : Q2), ((-2 : ℚ) : Q2), ((2 : ℚ) : Q2), ((1 : ℚ) : Q2)] by
      simp [p], this]
  have hpQe : aeval x (toPoly pQ) = x ^ 3 + 2 * x ^ 2 - 2 * x := by
    simp [pQ, CPoly.toPoly]; ring
  have hsqQ : Squarefree (toPoly pQ) := CPoly.squarefreeCheck_sound (by decide +kernel)
  have hdegQ : (toPoly pQ).natDegree = 3 := by
    rw [show toPoly pQ = X ^ 3 + C 2 * X ^ 2 + C (-2) * X by
      simp [pQ, CPoly.toPoly]; ring]
    compute_degree!
  have hB0 : evF ι x ([-2] : CPoly Q2) = aeval x (C (-2 : ℚ)) := by
    have := hev [-2]
    simp only [List.map_cons, List.map_nil] at this
    rw [show ([-2] : CPoly Q2) = [((-2 : ℚ) : Q2)] by simp, this]
    simp [CPoly.toPoly]
  have h := not_elem_of_logCheckFB hC hCall ι x y hx pQ hsqQ (by rw [hdegQ]; decide)
    (by rw [hpQe]; exact hy) hgen p [8] [-2, 0, 1] [] [1] [-2] _ hpQ (C (-2)) hB0
    (by simp) (by rw [hdegQ, natDegree_C]; norm_num) hcheck8
  have hA : evF ι x ([8] : CPoly Q2) = 8 := by
    have := hev [8]
    simp only [List.map_cons, List.map_nil] at this
    rw [show ([8] : CPoly Q2) = [((8 : ℚ) : Q2)] by simp, this]
    simp [CPoly.toPoly]
  have hD : evF ι x ([-2, 0, 1] : CPoly Q2) = x ^ 2 - 2 := by
    have := hev [-2, 0, 1]
    simp only [List.map_cons, List.map_nil] at this
    rw [show ([-2, 0, 1] : CPoly Q2) = [((-2 : ℚ) : Q2), ((0 : ℚ) : Q2), ((1 : ℚ) : Q2)] by
      simp, this]
    simp [CPoly.toPoly]; ring
  rwa [hA, hD] at h

end EllAlgo.IrrationalElemExample
