import RischTragerBronstein.Algebraic.Genus0Auto
import RischTragerBronstein.Algebraic.HypDecide

/-!
# Euler's substitution `t = y − s x` for `y² = s²x² + bx + c`

`x = (c − t²)/(2st − b)`, `y = (st² − bt + sc)/(2st − b)`, `1/t′ = −2(st² − bt + sc)/(2st − b)²`
(`euler_sq`); with `genus0_decides` this gives `genus0_sq_decides`: every tower of logarithms and
exponentials over `Kc(x, √(s²x² + bx + c))` (`b² ≠ 4s²c`) is decided.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.Genus0Auto

open Tower Tower.PrimN Tower.NestP Tower.NestM Tower.NestX CPoly

/-- The data `(P, Q, R, ρ)` of Euler's substitution (`S = Q`). -/
def eulerP (s b c : ℚ) : CPoly ℚ := [c, 0, -1]
def eulerQ (s b c : ℚ) : CPoly ℚ := [-b, 2 * s]
def eulerR (s b c : ℚ) : CPoly ℚ := [s * c, -b, s]
def eulerρ (s b c : ℚ) : Code 1 :=
  (([-2 * s * c, 2 * b, -2 * s] : CPoly ℚ), ([b ^ 2, -4 * s * b, 4 * s ^ 2] : CPoly ℚ))

section Euler

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma ev_list3 (t : E) (a₀ a₁ a₂ : ℚ) :
    ev (Kc := Kc) t ([a₀, a₁, a₂] : CPoly ℚ) = a₀ + a₁ * t + a₂ * t ^ 2 := by
  simp [ev, CPoly.toPoly]; ring

lemma ev_list2 (t : E) (a₀ a₁ : ℚ) : ev (Kc := Kc) t ([a₀, a₁] : CPoly ℚ) = a₀ + a₁ * t := by
  simp [ev, CPoly.toPoly]

/-- **Euler's substitution.** -/
lemma euler_sq (hC : ∀ c : Kc, c′ = 0) (s b c : ℚ) (hs : s ≠ 0) (hdisc : b ^ 2 - 4 * s ^ 2 * c ≠ 0)
    (x y : E) (hx : x′ = 1) (hy : y ^ 2 = s ^ 2 * x ^ 2 + b * x + c) :
    ev (Kc := Kc) (y - s * x) (eulerQ s b c) ≠ 0 ∧
    x = ev (Kc := Kc) (y - s * x) (eulerP s b c) / ev (Kc := Kc) (y - s * x) (eulerQ s b c) ∧
    y = ev (Kc := Kc) (y - s * x) (eulerR s b c) / ev (Kc := Kc) (y - s * x) (eulerQ s b c) ∧
    (y - s * x)′ * evx Kc (y - s * x) (eulerρ s b c) = 1 := by
  set t := y - s * x with ht
  clear_value t
  have hsE : (s : E) ≠ 0 := by exact_mod_cast hs
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  -- `x (2st − b) = c − t²`
  have hrel : x * (2 * s * t - b) = c - t ^ 2 := by
    rw [ht]; linear_combination hy
  have hQ0 : (2 * s * t - b : E) ≠ 0 := by
    intro h0
    have htc : t ^ 2 = c := by rw [h0, mul_zero] at hrel; linear_combination hrel
    apply hdisc
    have : ((b ^ 2 - 4 * s ^ 2 * c : ℚ) : E) = 0 := by
      push_cast; linear_combination (-((b : E) + 2 * s * t)) * h0 + 4 * (s : E) ^ 2 * htc
    exact_mod_cast this
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hy
    let pK : Kc[X] := C (s ^ 2 : Kc) * X ^ 2 + C (b : Kc) * X + C (c : Kc)
    have hp0 : pK ≠ 0 := by
      have hd : pK.natDegree = 2 := natDegree_quadratic (by exact_mod_cast pow_ne_zero 2 hs)
      intro h; rw [h] at hd; simp at hd
    apply aeval_ne_zero_of_tr x htrK hp0
    simp only [pK, map_add, map_mul, map_pow, aeval_C, aeval_X, map_ratCast]
    linear_combination -hy
  have hQ : ev (Kc := Kc) t (eulerQ s b c) = 2 * s * t - b := by
    rw [eulerQ, ev_list2]; push_cast; ring
  have hP : ev (Kc := Kc) t (eulerP s b c) = c - t ^ 2 := by
    rw [eulerP, ev_list3]; push_cast; ring
  have hR : ev (Kc := Kc) t (eulerR s b c) = s * t ^ 2 - b * t + s * c := by
    rw [eulerR, ev_list3]; push_cast; ring
  -- `t′ = −(2st − b)/(2y)`
  have htd : t′ * (2 * y) = -(2 * s * t - b) := by
    have h := congrArg (fun z : E ↦ z′) hrel
    simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, map_sub, map_mul, hx,
      deriv_ratCast_L] at h
    have hsd : (s : E)′ = 0 := deriv_ratCast_L _
    have hbd : (b : E)′ = 0 := deriv_ratCast_L _
    have hcd : (c : E)′ = 0 := deriv_ratCast_L _
    have h2d : (2 : E)′ = 0 := by
      have := deriv_ratCast_L (L := E) 2; simpa using this
    simp only [hsd, hbd, hcd, h2d, Derivation.leibniz, smul_eq_mul] at h
    have hyt : y = t + s * x := by rw [ht]; ring
    rw [hyt]
    linear_combination h
  refine ⟨by rw [hQ]; exact hQ0, ?_, ?_, ?_⟩
  · rw [hP, hQ, eq_div_iff hQ0]; exact hrel
  · rw [hR, hQ, eq_div_iff hQ0]
    have hyt : y = t + s * x := by rw [ht]; ring
    rw [hyt]; linear_combination s * hrel
  · have hyv : y * (2 * s * t - b) = s * t ^ 2 - b * t + s * c := by
      have hyt : y = t + s * x := by rw [ht]; ring
      rw [hyt]; linear_combination s * hrel
    have hρv : evx Kc t (eulerρ s b c) = -2 * y / (2 * s * t - b) := by
      simp only [PrimN.evx, eulerρ]
      have e1 := ev_list3 (Kc := Kc) t (-2 * s * c) (2 * b) (-2 * s)
      have e2 := ev_list3 (Kc := Kc) t (b ^ 2) (-4 * s * b) (4 * s ^ 2)
      simp only [ev] at e1 e2
      rw [e1, e2]
      push_cast
      have hden : (b : E) ^ 2 + -4 * s * b * t + 4 * s ^ 2 * t ^ 2 ≠ 0 := by
        rw [show (b : E) ^ 2 + -4 * s * b * t + 4 * s ^ 2 * t ^ 2 = (2 * s * t - b) ^ 2 by ring]
        exact pow_ne_zero _ hQ0
      rw [div_eq_div_iff hden hQ0]
      linear_combination 2 * (2 * s * t - b) * hyv
    have htv : t′ = -(2 * s * t - b) / (2 * y) := by
      rw [eq_div_iff (mul_ne_zero two_ne_zero hy0)]; exact htd
    rw [hρv, htv]
    field_simp

/-- **Towers over `Kc(x, √(s²x² + bx + c))` are decided** (`s ≠ 0`, `b² ≠ 4s²c`): `certX` and
`elemNX` on the tower translated by Euler's substitution `t = y − s x`. -/
theorem genus0_sq_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (s b c : ℚ) (hs : s ≠ 0) (hdisc : b ^ 2 - 4 * s ^ 2 * c ≠ 0)
    (hy : y ^ 2 = s ^ 2 * x ^ 2 + b * x + c)
    (iks : (m : ℕ) → IKind m) (ilv : (m : ℕ) → ICode m) (ts : ℕ → E)
    (hts : ∀ m, (ts m)′ = kderI Kc x y ts m (iks m))
    (hts0 : ∀ m (a : ICode m), iks m = .exp a → ts m ≠ 0) (hwk : ∀ m, wfK m (iks m) = true)
    (n : ℕ) (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc (insert x (insert y (ts '' Set.Iio n))))
    (hcert : certX (fun m ↦ trK (eulerP s b c) (eulerQ s b c) (eulerR s b c) (eulerQ s b c)
      (eulerρ s b c) m (iks m))
      (fun m ↦ tr (eulerP s b c) (eulerQ s b c) (eulerR s b c) (eulerQ s b c) m (ilv m)) n = true)
    (A : ICode n) (hwA : wfI n A = true) :
    HasElementaryIntegral (evI Kc x y ts n A) ↔
      elemNX (fun m ↦ trK (eulerP s b c) (eulerQ s b c) (eulerR s b c) (eulerQ s b c)
        (eulerρ s b c) m (iks m))
        (fun m ↦ tr (eulerP s b c) (eulerQ s b c) (eulerR s b c) (eulerQ s b c) m (ilv m)) n
        (scal (eulerρ s b c) n
          (tr (eulerP s b c) (eulerQ s b c) (eulerR s b c) (eulerQ s b c) n A)) = true := by
  obtain ⟨hQ, hxt, hyt, hρ⟩ := euler_sq hC s b c hs hdisc x y hx hy
  exact genus0_decides hC hCall x y (y - s * x) hx _ _ _ _ _ hQ hQ hxt hyt hρ iks ilv ts hts hts0
    hwk n hgen hcert A hwA

end Euler

end Tower.Genus0Auto
