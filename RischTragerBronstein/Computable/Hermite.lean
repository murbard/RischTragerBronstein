import RischTragerBronstein.Computable.Euclid
import RischTragerBronstein.Differential.Monomial
import Mathlib.FieldTheory.Separable

/-!
# Executable Hermite reduction, with a verified certificate checker

* `CPoly.hermite A D` runs Mack's linear Hermite reduction (Bronstein, §2.2) on `A / D` and returns
  `gn, gd, b, s`, intended to satisfy `A / D = (gn / gd)′ + b / s` with `s` squarefree.
* `CPoly.hermiteCheck` is a decidable certificate for such an output: one polynomial identity and a
  Bézout certificate of squarefreeness.
* `CPoly.hermiteCheck_sound`: **if the check passes, the identity holds in `RatFunc R`** and `s` is
  squarefree.

So the executable output is trusted only through the checker, whose soundness is proved; nothing
about the reduction loop itself is assumed. (That the check always passes on the output of
`hermite` is the completeness statement, mirrored abstractly by `hermite_reduction_ratFunc`.)
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R]

/-- Quotient of the division. -/
def div (p d : CPoly R) : CPoly R := (divMod p d).1

/-- A (non-normalised) greatest common divisor. -/
def gcd (p q : CPoly R) : CPoly R := trim (egcd p q).1

/-- Solve `s * a + t * b = c` with `s` reduced modulo `b` (assuming `gcd a b` is a constant). -/
def solveBezout (a b c : CPoly R) : CPoly R × CPoly R :=
  let e := egcd a b
  let γ := lead (trim e.1)
  let s := (divMod (smul (1 / γ) (mul c e.2.1)) b).2
  (s, div (sub c (mul s a)) b)

/-- Output of Hermite reduction: `A / D = (gn / gd)′ + b / s`. -/
structure HermiteResult (R : Type*) where
  /-- numerator of the rational part -/
  gn : CPoly R
  /-- denominator of the rational part -/
  gd : CPoly R
  /-- numerator of the remaining integrand -/
  b : CPoly R
  /-- squarefree denominator of the remaining integrand -/
  s : CPoly R
deriving Repr

/-- Mack's loop. State: rational part `gn / gd`, remaining integrand `A / (Ds * Dm)`. -/
def hermiteLoop : ℕ → CPoly R → CPoly R → CPoly R → CPoly R → CPoly R → HermiteResult R
  | 0, gn, gd, A, Ds, Dm => ⟨gn, gd, A, mul Ds Dm⟩
  | fuel + 1, gn, gd, A, Ds, Dm =>
    if (trim Dm).length ≤ 1 then ⟨trim gn, trim gd, trim A, trim (mul Ds Dm)⟩
    else
      let Dm2 := gcd Dm (deriv Dm)
      let Dms := div Dm Dm2
      let BC := solveBezout (neg (div (mul Ds (deriv Dm)) Dm)) Dms A
      let A' := sub BC.2 (div (mul (deriv BC.1) Ds) Dms)
      hermiteLoop fuel (add (mul gn Dm) (mul BC.1 gd)) (mul gd Dm) A' Ds Dm2

/-- Hermite reduction of `A / D`. -/
def hermite (A D : CPoly R) : HermiteResult R :=
  let Dm := gcd D (deriv D)
  hermiteLoop D.length [] [1] A (div D Dm) Dm

/-- Certificate of squarefreeness: the extended gcd of `s` and `s′` is a nonzero constant. -/
def squarefreeCheck (s : CPoly R) : Bool := (trim (egcd s (deriv s)).1).length == 1

/-- Certificate for `A / D = (gn / gd)′ + b / s`, `s` squarefree. -/
def hermiteCheck (A D : CPoly R) (r : HermiteResult R) : Bool :=
  !isZero D && !isZero r.gd && !isZero r.s &&
  beq (mul (mul A (mul r.gd r.gd)) r.s)
    (add (mul (mul (sub (mul (deriv r.gn) r.gd) (mul r.gn (deriv r.gd))) D) r.s)
      (mul (mul r.b D) (mul r.gd r.gd))) &&
  squarefreeCheck r.s

lemma trim_singleton {p : CPoly R} {γ : R} (h : trim p = [γ]) : γ ≠ 0 ∧ toPoly p = C γ := by
  refine ⟨?_, by rw [← toPoly_trim, h]; simp⟩
  have h' : p.reverse.dropWhile (· = 0) = [γ] := by
    have := congrArg List.reverse h
    rwa [trim, List.reverse_reverse, List.reverse_singleton] at this
  have := List.head_dropWhile_not (fun x : R ↦ decide (x = 0)) (l := p.reverse)
    (by rw [h']; simp)
  simpa [h'] using this

theorem squarefreeCheck_sound {s : CPoly R} (h : squarefreeCheck s = true) :
    Squarefree (toPoly s) := by
  rw [squarefreeCheck, beq_iff_eq] at h
  obtain ⟨γ, hγ⟩ := List.length_eq_one_iff.mp h
  obtain ⟨hγ0, hg⟩ := trim_singleton hγ
  have hbez := egcd_spec s (deriv s)
  rw [hg, toPoly_deriv] at hbez
  refine Separable.squarefree ⟨C γ⁻¹ * toPoly (egcd s (deriv s)).2.1,
    C γ⁻¹ * toPoly (egcd s (deriv s)).2.2, ?_⟩
  have : C γ⁻¹ * C γ = (1 : R[X]) := by rw [← C_mul, inv_mul_cancel₀ hγ0, C_1]
  linear_combination C γ⁻¹ * hbez + this

variable [Differential R]

open Differential in
/-- **Soundness of the Hermite certificate.** -/
theorem hermiteCheck_sound (h0 : ∀ a : R, a′ = 0) (A D : CPoly R) (r : HermiteResult R)
    (hc : hermiteCheck A D r = true) :
    letI := ratFuncOfDeriv (1 : R[X])
    algebraMap R[X] (RatFunc R) (toPoly A) / algebraMap R[X] (RatFunc R) (toPoly D) =
      (algebraMap R[X] (RatFunc R) (toPoly r.gn) / algebraMap R[X] (RatFunc R) (toPoly r.gd))′ +
        algebraMap R[X] (RatFunc R) (toPoly r.b) / algebraMap R[X] (RatFunc R) (toPoly r.s) ∧
    Squarefree (toPoly r.s) := by
  let _ := polynomialOfDeriv (1 : R[X])
  let _ := ratFuncOfDeriv (1 : R[X])
  simp only [hermiteCheck, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
    isZero_iff, beq_iff] at hc
  obtain ⟨⟨⟨⟨hD, hgd⟩, hs⟩, hid⟩, hsq⟩ := hc
  refine ⟨?_, squarefreeCheck_sound hsq⟩
  set φ := algebraMap R[X] (RatFunc R)
  have hφD : φ (toPoly D) ≠ 0 := RatFunc.algebraMap_ne_zero hD
  have hφgd : φ (toPoly r.gd) ≠ 0 := RatFunc.algebraMap_ne_zero hgd
  have hφs : φ (toPoly r.s) ≠ 0 := RatFunc.algebraMap_ne_zero hs
  have hquot := ofFractionRing_deriv_div R[X] (RatFunc R) (toPoly r.gn) (toPoly r.gd) hgd
  rw [hquot]
  change _ = φ (implicitDeriv 1 (toPoly r.gn) * toPoly r.gd -
    toPoly r.gn * implicitDeriv 1 (toPoly r.gd)) / φ (toPoly r.gd) ^ 2 + _
  rw [implicitDeriv_one_of_trivial h0, implicitDeriv_one_of_trivial h0]
  have hid' := congrArg φ hid
  simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, map_mul, map_add, map_sub] at hid'
  simp only [map_mul, map_sub]
  field_simp
  linear_combination hid'

end CPoly

-- ∫ 1 / (x³ + x²) dx: rational part `-1/x`, remaining integrand with squarefree denominator.
#eval CPoly.hermite ([1] : CPoly ℚ) [0, 0, 1, 1]
#eval CPoly.hermiteCheck ([1] : CPoly ℚ) [0, 0, 1, 1] (CPoly.hermite [1] [0, 0, 1, 1])
-- ∫ (x⁷ - 24x⁴ - 4x² + 8x - 8) / (x⁸ + 6x⁶ + 12x⁴ + 8x²) dx   (Bronstein, Example 2.2.1)
#eval CPoly.hermite ([-8, 8, -4, 0, -24, 0, 0, 1] : CPoly ℚ) [0, 0, 8, 0, 12, 0, 6, 0, 1]
#eval CPoly.hermiteCheck ([-8, 8, -4, 0, -24, 0, 0, 1] : CPoly ℚ) [0, 0, 8, 0, 12, 0, 6, 0, 1]
  (CPoly.hermite [-8, 8, -4, 0, -24, 0, 0, 1] [0, 0, 8, 0, 12, 0, 6, 0, 1])
