import RischTragerBronstein.Computable.CurveModel

/-!
# Curve codes as fractions `W(x, y)/Q(x)`

A curve code (a list of `R(x)`-codes, the coefficients of `1, y, y², …`) is converted to a pair
`(W, Q)`, `W ∈ R[x][y]`, `Q ∈ R[x]`, `Q ≠ 0`, with the same value: `codeQ` is the product of the
denominators (zero denominators, which denote the value `0`, are replaced by `1` first), and
`codeW` the numerators brought to that denominator.

* `sem_codeFrac`: `Q(x) · value(a) = W(x, y)`.
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup

section Frac

variable {R : Type*} [Field R] [DecidableEq R]

/-- Replace a zero denominator (value `0`) by the code `0/1`. -/
def cleanQ' (q : GFrac R) : GFrac R := if isZero q.2 then ([], [1]) else q

/-- The product of the denominators. -/
def codeQ : List (GFrac R) → CPoly R
  | [] => [1]
  | q :: a => mul (cleanQ' q).2 (codeQ a)

/-- The numerators over the common denominator. -/
def codeW : List (GFrac R) → BPoly R
  | [] => []
  | q :: a => mul (cleanQ' q).1 (codeQ a) :: (codeW a).map (mul (cleanQ' q).2)

lemma cleanQ'_den_ne_zero (q : GFrac R) : toPoly (cleanQ' q).2 ≠ 0 := by
  unfold cleanQ'
  split_ifs with h
  · simp [CPoly.toPoly]
  · exact fun h0 ↦ h ((isZero_iff _).mpr h0)

lemma codeQ_ne_zero : ∀ a : List (GFrac R), toPoly (codeQ a) ≠ 0
  | [] => by simp [codeQ, CPoly.toPoly]
  | q :: a => by
    rw [codeQ, toPoly_mul]; exact mul_ne_zero (cleanQ'_den_ne_zero q) (codeQ_ne_zero a)

lemma length_codeW : ∀ a : List (GFrac R), (codeW a).length = a.length
  | [] => rfl
  | q :: a => by simp [codeW, length_codeW a]

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E]
variable (ι : R →+* Kc) (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)

omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] in
lemma aeval_x_ne_zero' (P : Kc[X]) (hP : P ≠ 0) : aeval S.x P ≠ 0 := fun h ↦ S.htr ⟨P, hP, h⟩

lemma sem_cleanQ' (q : GFrac R) :
    (xModel ι hC S hx).sem (cleanQ' q) = (xModel ι hC S hx).sem q := by
  unfold cleanQ'
  split_ifs with h
  · rw [sem_xModel, sem_xModel, (isZero_iff q.2).mp h]
    simp [CPoly.toPoly]
  · rfl

/-- **The value of a curve code as a fraction.** -/
theorem sem_codeFrac : ∀ a : List (GFrac R),
    (((toB (codeW a)).map (mapRingHom ι)).map (aeval S.x).toRingHom).eval S.y =
      aeval S.x ((toPoly (codeQ a)).map ι) *
        (GPoly.toPoly (xModel ι hC S hx) a).eval S.y
  | [] => by simp [codeW, codeQ, CPoly.toPoly]
  | q :: a => by
    have ih := sem_codeFrac a
    have hd := aeval_x_ne_zero' S _ ((Polynomial.map_ne_zero_iff ι.injective).mpr
      (cleanQ'_den_ne_zero q))
    rw [codeW, codeQ, toB_cons, GPoly.toPoly_cons, ← sem_cleanQ' ι hC S hx q, sem_xModel]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      eval_add, eval_mul, eval_C, eval_X, toPoly_mul, map_mul, coe_mapRingHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    have hmapW : ∀ W : BPoly R, toB (W.map (mul (cleanQ' q).2)) =
        Polynomial.C (toPoly (cleanQ' q).2) * toB W := fun W ↦ by
      induction W with
      | nil => simp
      | cons c W ihW => rw [List.map_cons, toB_cons, toB_cons, ihW, toPoly_mul]; simp; ring
    rw [hmapW, Polynomial.map_mul, Polynomial.map_mul, eval_mul, Polynomial.map_C,
      Polynomial.map_C, eval_C]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_mapRingHom] at ih ⊢
    rw [ih]
    field_simp

end Frac

end Curves
