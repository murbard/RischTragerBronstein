import RischTragerBronstein.Computable.Hermite
import RischTragerBronstein.Rational.Integrable
import Mathlib.Data.List.GetD

/-!
# A verified executable integrator for rational functions

`CPoly.integrateRational A D` integrates `A / D ∈ R(x)`. Its output `gn, gd, Q, r, s` denotes

  `∫ A / D = gn / gd + Q + ∑_{s(α) = 0} (r(α) / s′(α)) log (x - α)`.

`CPoly.rationalCheck` is a decidable certificate for such an output, and
`CPoly.rationalCheck_sound` proves that an accepted output is correct: `A / D = g′ + r / s` with
`g = gn / gd + Q`, `s` squarefree and `deg r < deg s`, whence — by `ratFunc_integral_explicit` —
the displayed formula is an antiderivative in the splitting field of `s`, and `A / D` has an
elementary integral.

In the rational case the answer "no elementary integral" never occurs
(`ratFunc_hasElementaryIntegral`), so there is no negative certificate to produce.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R]

/-- Auxiliary function for `integ`. -/
def integAux : ℕ → CPoly R → CPoly R
  | _, [] => []
  | n, a :: p => (a / n) :: integAux (n + 1) p

/-- A polynomial antiderivative (in characteristic zero). -/
def integ (p : CPoly R) : CPoly R := 0 :: integAux 1 p

/-- `∫ A / D = gn / gd + Q + ∑_{s(α) = 0} (r(α) / s′(α)) log (x - α)`. -/
structure RationalIntegral (R : Type*) where
  /-- numerator of the rational part -/
  gn : CPoly R
  /-- denominator of the rational part -/
  gd : CPoly R
  /-- polynomial part -/
  Q : CPoly R
  /-- numerator of the logarithmic part -/
  r : CPoly R
  /-- squarefree denominator of the logarithmic part -/
  s : CPoly R
deriving Repr

/-- Integrate `A / D`: Hermite reduction, Euclidean division, integration of the quotient. -/
def integrateRational (A D : CPoly R) : RationalIntegral R :=
  let h := hermite A D
  let qr := divMod h.b h.s
  ⟨h.gn, h.gd, trim (integ qr.1), trim qr.2, h.s⟩

/-- Certificate for the output of `integrateRational`. -/
def rationalCheck (A D : CPoly R) (I : RationalIntegral R) : Bool :=
  hermiteCheck A D ⟨I.gn, I.gd, add (mul (deriv I.Q) I.s) I.r, I.s⟩ &&
    decide ((trim I.r).length < (trim I.s).length)

lemma degree_toPoly_lt (p : CPoly R) : (toPoly p).degree < p.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPoly, List.getD_eq_default _ _ hm]

lemma getLast_trim_ne_zero (p : CPoly R) (h : trim p ≠ []) : (trim p).getLast h ≠ 0 := by
  have h' : p.reverse.dropWhile (· = 0) ≠ [] := fun h0 ↦ h (by rw [trim, h0]; rfl)
  have := List.head_dropWhile_not (fun x : R ↦ decide (x = 0)) (l := p.reverse) h'
  simp only [trim, List.getLast_reverse]
  simpa using this

lemma degree_lt_of_trim_length_lt {r s : CPoly R} (h : (trim r).length < (trim s).length) :
    (toPoly r).degree < (toPoly s).degree := by
  rw [← toPoly_trim r, ← toPoly_trim s]
  have hne : trim s ≠ [] := fun h0 ↦ by simp [h0] at h
  have hcoeff : (toPoly (trim s)).coeff ((trim s).length - 1) ≠ 0 := by
    rw [coeff_toPoly, List.getD_eq_getElem _ _ (by
      have := List.length_pos_of_ne_nil hne; omega), ← List.getLast_eq_getElem hne]
    exact getLast_trim_ne_zero s hne
  refine lt_of_lt_of_le (degree_toPoly_lt _) (le_trans ?_ (le_degree_of_ne_zero hcoeff))
  exact_mod_cast Nat.le_sub_one_of_lt h

variable [CharZero R] [Differential R]

open Differential in
/-- **Soundness of the rational integrator.** -/
theorem rationalCheck_sound (h0 : ∀ a : R, a′ = 0) (A D : CPoly R) (I : RationalIntegral R)
    (hc : rationalCheck A D I = true) :
    letI := ratFuncOfDeriv (1 : R[X])
    (algebraMap R[X] (RatFunc R) (toPoly A) / algebraMap R[X] (RatFunc R) (toPoly D) =
      (algebraMap R[X] (RatFunc R) (toPoly I.gn) / algebraMap R[X] (RatFunc R) (toPoly I.gd) +
          algebraMap R[X] (RatFunc R) (toPoly I.Q))′ +
        algebraMap R[X] (RatFunc R) (toPoly I.r) / algebraMap R[X] (RatFunc R) (toPoly I.s)) ∧
    Squarefree (toPoly I.s) ∧ (toPoly I.r).degree < (toPoly I.s).degree ∧
    HasElementaryIntegral
      (algebraMap R[X] (RatFunc R) (toPoly A) / algebraMap R[X] (RatFunc R) (toPoly D)) := by
  let _ := polynomialOfDeriv (1 : R[X])
  let _ := ratFuncOfDeriv (1 : R[X])
  have hDAP : DifferentialAlgebra R[X] (RatFunc R) := differentialAlgebra_ofFractionRing _ _
  rw [rationalCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hH, hlen⟩ := hc
  obtain ⟨hid, hsq⟩ := hermiteCheck_sound h0 A D _ hH
  have hdeg := degree_lt_of_trim_length_lt hlen
  set φ := algebraMap R[X] (RatFunc R)
  have hs0 : toPoly I.s ≠ 0 := hsq.ne_zero
  have hφs : φ (toPoly I.s) ≠ 0 := RatFunc.algebraMap_ne_zero hs0
  have hQ : (φ (toPoly I.Q))′ = φ (derivative (toPoly I.Q)) := by
    rw [deriv_algebraMap (A := R[X]) (B := RatFunc R)]
    change φ (implicitDeriv 1 (toPoly I.Q)) = _
    rw [implicitDeriv_one_of_trivial h0]
  have hmain : φ (toPoly A) / φ (toPoly D) =
      (φ (toPoly I.gn) / φ (toPoly I.gd) + φ (toPoly I.Q))′ + φ (toPoly I.r) / φ (toPoly I.s) := by
    rw [hid, deriv_add_const_mul_one, hQ]
    simp only [toPoly_add, toPoly_mul, toPoly_deriv, map_add, map_mul]
    field_simp
    ring
  refine ⟨hmain, hsq, hdeg, ?_⟩
  rw [hmain]
  exact (ratFunc_integral_explicit h0 _ _ _ hsq hdeg).2

end CPoly

-- ∫ 1 / (x³ + x²) dx = -1/x + ∑_{α² + α = 0} ((-1) / (2α + 1)) log (x - α)
#eval CPoly.integrateRational ([1] : CPoly ℚ) [0, 0, 1, 1]
#eval CPoly.rationalCheck ([1] : CPoly ℚ) [0, 0, 1, 1] (CPoly.integrateRational [1] [0, 0, 1, 1])
-- ∫ (x⁴ + 1) / (x² + 1) dx: polynomial part and a logarithmic part over the roots of x² + 1
#eval CPoly.integrateRational ([1, 0, 0, 0, 1] : CPoly ℚ) [1, 0, 1]
#eval CPoly.rationalCheck ([1, 0, 0, 0, 1] : CPoly ℚ) [1, 0, 1]
  (CPoly.integrateRational [1, 0, 0, 0, 1] [1, 0, 1])
