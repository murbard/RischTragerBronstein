import RischTragerBronstein.Algebraic.Genus0AutoRoot

/-!
# The substitution `t = (y − y₀)/(x − x₀)` through a rational point

For `y² = y₀² + d (x − x₀) + a (x − x₀)²` (any conic with the rational point `(x₀, y₀)`,
`d² ≠ 4a y₀²`): `x = x₀ + (d − 2y₀t)/(t² − a)`, `y = y₀ + t (x − x₀)`, `1/t′ = −2y/(t² − a)`
(`euler_pt`); `genus0_pt_decides`: every tower of logarithms and exponentials over `Kc(x, √q)`,
`q` any non-degenerate quadratic over `ℚ` whose conic has a rational point off infinity, is
decided. (With `genus0_sq_decides` for the points at infinity, only pointless conics remain.)
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.Genus0Auto

open Tower Tower.PrimN Tower.NestP Tower.NestM Tower.NestX CPoly

def ptP (x₀ y₀ a d : ℚ) : CPoly ℚ := [d - a * x₀, -2 * y₀, x₀]
def ptQ (x₀ y₀ a d : ℚ) : CPoly ℚ := [-a, 0, 1]
def ptR (x₀ y₀ a d : ℚ) : CPoly ℚ := [-a * y₀, d, -y₀]
def ptρ (x₀ y₀ a d : ℚ) : Code 1 :=
  (([2 * a * y₀, -2 * d, 2 * y₀] : CPoly ℚ), ([a ^ 2, 0, -2 * a, 0, 1] : CPoly ℚ))

section Pt

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The rational-point substitution.** -/
lemma euler_pt (hC : ∀ c : Kc, c′ = 0) (x₀ y₀ a d : ℚ) (hdisc : d ^ 2 - 4 * a * y₀ ^ 2 ≠ 0)
    (x y : E) (hx : x′ = 1) (hy : y ^ 2 = y₀ ^ 2 + d * (x - x₀) + a * (x - x₀) ^ 2) :
    ev (Kc := Kc) ((y - y₀) / (x - x₀)) (ptQ x₀ y₀ a d) ≠ 0 ∧
    x = ev (Kc := Kc) ((y - y₀) / (x - x₀)) (ptP x₀ y₀ a d) /
      ev (Kc := Kc) ((y - y₀) / (x - x₀)) (ptQ x₀ y₀ a d) ∧
    y = ev (Kc := Kc) ((y - y₀) / (x - x₀)) (ptR x₀ y₀ a d) /
      ev (Kc := Kc) ((y - y₀) / (x - x₀)) (ptQ x₀ y₀ a d) ∧
    ((y - y₀) / (x - x₀))′ * evx Kc ((y - y₀) / (x - x₀)) (ptρ x₀ y₀ a d) = 1 := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hxe : x - (x₀ : E) ≠ 0 := by
    intro h0
    have := congrArg (fun z : E ↦ z′) h0
    simp only [map_sub, hx, deriv_ratCast_L, sub_zero, map_zero] at this
    exact one_ne_zero this
  set t := (y - y₀) / (x - x₀) with ht
  have hyt : y = y₀ + t * (x - x₀) := by rw [ht]; field_simp; ring
  clear_value t
  set u := x - (x₀ : E) with hu
  -- `u (t² − a) = d − 2y₀t`
  have hrel : u * (t ^ 2 - a) = d - 2 * y₀ * t := by
    have h := hy
    rw [hyt] at h
    have : u * (u * (t ^ 2 - a) - (d - 2 * y₀ * t)) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hxe)
  have hQ0 : (t ^ 2 - a : E) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hrel
    apply hdisc
    have : ((d ^ 2 - 4 * a * y₀ ^ 2 : ℚ) : E) = 0 := by
      push_cast
      linear_combination (-((d : E) + 2 * y₀ * t)) * hrel + 4 * (y₀ : E) ^ 2 * h0
    exact_mod_cast this
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hy
    have hud : u′ = 1 := by
      rw [hu, map_sub, hx, deriv_ratCast_L, sub_zero]
    have htrU : Transcendental Kc u :=
      transcendental_of_deriv_ne_zero hC (by rw [hud]; exact one_ne_zero)
    let pK : Kc[X] := C ((a : ℚ) : Kc) * X ^ 2 + C ((d : ℚ) : Kc) * X + C ((y₀ ^ 2 : ℚ) : Kc)
    have hp0 : pK ≠ 0 := by
      intro h
      have h2 := congrArg (coeff · 2) h
      have h1 := congrArg (coeff · 1) h
      have h0' := congrArg (coeff · 0) h
      simp only [pK, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at h2 h1 h0'
      norm_num at h2 h1 h0'
      apply hdisc
      rw [h2, h1, h0']; ring
    apply aeval_ne_zero_of_tr u htrU hp0
    simp only [pK, map_add, map_mul, map_pow, aeval_C, aeval_X, map_ratCast]
    push_cast
    linear_combination -hy
  have hQ : ev (Kc := Kc) t (ptQ x₀ y₀ a d) = t ^ 2 - a := by
    rw [ptQ, ev_list3]; push_cast; ring
  have hP : ev (Kc := Kc) t (ptP x₀ y₀ a d) = x₀ * t ^ 2 - 2 * y₀ * t + d - a * x₀ := by
    rw [ptP, ev_list3]; push_cast; ring
  have hR : ev (Kc := Kc) t (ptR x₀ y₀ a d) = -y₀ * t ^ 2 + d * t - a * y₀ := by
    rw [ptR, ev_list3]; push_cast; ring
  have hyv : y * (t ^ 2 - a) = -y₀ * t ^ 2 + d * t - a * y₀ := by
    rw [hyt]; linear_combination t * hrel
  refine ⟨by rw [hQ]; exact hQ0, ?_, ?_, ?_⟩
  · rw [hP, hQ, eq_div_iff hQ0]
    have : x = u + x₀ := by rw [hu]; ring
    rw [this]; linear_combination hrel
  · rw [hR, hQ, eq_div_iff hQ0]; exact hyv
  · have htd : t′ * (2 * y) = -(t ^ 2 - a) := by
      have h := congrArg (fun z : E ↦ z′) hrel
      have had : (a : E)′ = 0 := deriv_ratCast_L _
      have hdd : (d : E)′ = 0 := deriv_ratCast_L _
      have hy0d : (y₀ : E)′ = 0 := deriv_ratCast_L _
      have hx0d : (x₀ : E)′ = 0 := deriv_ratCast_L _
      have h2d : (2 : E)′ = 0 := by
        have := deriv_ratCast_L (L := E) 2; simpa using this
      rw [hu] at h
      simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, map_sub, hx, had, hdd,
        hy0d, hx0d, h2d] at h
      rw [hyt]
      linear_combination h
    have htv : t′ = -(t ^ 2 - a) / (2 * y) := by
      rw [eq_div_iff (mul_ne_zero two_ne_zero hy0)]; exact htd
    have hρv : evx Kc t (ptρ x₀ y₀ a d) = -2 * y / (t ^ 2 - a) := by
      simp only [PrimN.evx, ptρ]
      have e1 := ev_list3 (Kc := Kc) t (2 * a * y₀) (-2 * d) (2 * y₀)
      have e2 : ev (Kc := Kc) t ([a ^ 2, 0, -2 * a, 0, 1] : CPoly ℚ) = (t ^ 2 - a) ^ 2 := by
        simp [ev, CPoly.toPoly, map_ofNat]; ring
      simp only [ev] at e1 e2
      rw [e1, e2]
      push_cast
      rw [div_eq_div_iff (pow_ne_zero 2 hQ0) hQ0]
      linear_combination 2 * (t ^ 2 - a) * hyv
    rw [hρv, htv]
    field_simp

/-- **Towers over `Kc(x, √q)`, `q` a conic with the rational point `(x₀, y₀)`, are decided.** -/
theorem genus0_pt_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (x₀ y₀ a d : ℚ) (hdisc : d ^ 2 - 4 * a * y₀ ^ 2 ≠ 0)
    (hy : y ^ 2 = y₀ ^ 2 + d * (x - x₀) + a * (x - x₀) ^ 2)
    (iks : (m : ℕ) → IKind m) (ilv : (m : ℕ) → ICode m) (ts : ℕ → E)
    (hts : ∀ m, (ts m)′ = kderI Kc x y ts m (iks m))
    (hts0 : ∀ m (b : ICode m), iks m = .exp b → ts m ≠ 0) (hwk : ∀ m, wfK m (iks m) = true)
    (n : ℕ) (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc (insert x (insert y (ts '' Set.Iio n))))
    (hcert : certX (fun m ↦ trK (ptP x₀ y₀ a d) (ptQ x₀ y₀ a d) (ptR x₀ y₀ a d) (ptQ x₀ y₀ a d)
      (ptρ x₀ y₀ a d) m (iks m))
      (fun m ↦ tr (ptP x₀ y₀ a d) (ptQ x₀ y₀ a d) (ptR x₀ y₀ a d) (ptQ x₀ y₀ a d) m (ilv m)) n
        = true)
    (Aint : ICode n) (hwA : wfI n Aint = true) :
    HasElementaryIntegral (evI Kc x y ts n Aint) ↔
      elemNX (fun m ↦ trK (ptP x₀ y₀ a d) (ptQ x₀ y₀ a d) (ptR x₀ y₀ a d) (ptQ x₀ y₀ a d)
        (ptρ x₀ y₀ a d) m (iks m))
        (fun m ↦ tr (ptP x₀ y₀ a d) (ptQ x₀ y₀ a d) (ptR x₀ y₀ a d) (ptQ x₀ y₀ a d) m (ilv m)) n
        (scal (ptρ x₀ y₀ a d) n
          (tr (ptP x₀ y₀ a d) (ptQ x₀ y₀ a d) (ptR x₀ y₀ a d) (ptQ x₀ y₀ a d) n Aint)) = true := by
  obtain ⟨hQ, hxt, hyt, hρ⟩ := euler_pt hC x₀ y₀ a d hdisc x y hx hy
  exact genus0_decides hC hCall x y ((y - y₀) / (x - x₀)) hx _ _ _ _ _ hQ hQ hxt hyt hρ iks ilv
    ts hts hts0 hwk n hgen hcert Aint hwA

end Pt

end Tower.Genus0Auto
