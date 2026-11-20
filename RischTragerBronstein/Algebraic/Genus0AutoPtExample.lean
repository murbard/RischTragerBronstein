import RischTragerBronstein.Algebraic.Genus0AutoPt
import RischTragerBronstein.Algebraic.Genus0AutoRootExample

/-!
# Automatic genus-zero towers through a rational point: `√(3x² + 1)`

`y² = 3x² + 1` has no rational root and a non-square leading coefficient, but the rational point
`(0, 1)`; with `θ = log x`, decided by `genus0_pt_decides` (`t = (y − 1)/x`), computed and
kernel-checked:
* `∫ log x / √(3x² + 1) dx` is **not** elementary;
* `∫ x log x / √(3x² + 1) dx` is elementary.
-/

open Polynomial Differential IntermediateField

namespace Tower.Genus0Auto.PtExample

open Tower Tower.PrimN Tower.NestP Tower.NestM Tower.NestX CPoly Tower.Genus0Auto.Example
open Tower.Genus0Auto.RootExample (iksL ilvL)

/-- `1/y = y/(3x² + 1)`. -/
def yinv3 : ICode 0 := ((([] : CPoly ℚ), ([1] : CPoly ℚ)), (([1] : CPoly ℚ), ([1, 0, 3] : CPoly ℚ)))
/-- `x/y`. -/
def xyinv3 : ICode 0 := ((([] : CPoly ℚ), ([1] : CPoly ℚ)), (([0, 1] : CPoly ℚ), ([1, 0, 3] : CPoly ℚ)))
def B1 : ICode 1 := ([iconst 0 0, yinv3], [iconst 0 1])
def B2 : ICode 1 := ([iconst 0 0, xyinv3], [iconst 0 1])

set_option maxRecDepth 100000

theorem certP : certX (fun m ↦ trK (ptP 0 1 3 0) (ptQ 0 1 3 0) (ptR 0 1 3 0) (ptQ 0 1 3 0)
    (ptρ 0 1 3 0) m (iksL m))
    (fun m ↦ tr (ptP 0 1 3 0) (ptQ 0 1 3 0) (ptR 0 1 3 0) (ptQ 0 1 3 0) m (ilvL m)) 1 = true := by
  decide +kernel

theorem pans1 : elemNX (fun m ↦ trK (ptP 0 1 3 0) (ptQ 0 1 3 0) (ptR 0 1 3 0) (ptQ 0 1 3 0)
    (ptρ 0 1 3 0) m (iksL m))
    (fun m ↦ tr (ptP 0 1 3 0) (ptQ 0 1 3 0) (ptR 0 1 3 0) (ptQ 0 1 3 0) m (ilvL m)) 1
    (scal (ptρ 0 1 3 0) 1 (tr (ptP 0 1 3 0) (ptQ 0 1 3 0) (ptR 0 1 3 0) (ptQ 0 1 3 0) 1 B1))
      = false := by
  decide +kernel

theorem pans2 : elemNX (fun m ↦ trK (ptP 0 1 3 0) (ptQ 0 1 3 0) (ptR 0 1 3 0) (ptQ 0 1 3 0)
    (ptρ 0 1 3 0) m (iksL m))
    (fun m ↦ tr (ptP 0 1 3 0) (ptQ 0 1 3 0) (ptR 0 1 3 0) (ptQ 0 1 3 0) m (ilvL m)) 1
    (scal (ptρ 0 1 3 0) 1 (tr (ptP 0 1 3 0) (ptQ 0 1 3 0) (ptR 0 1 3 0) (ptQ 0 1 3 0) 1 B2))
      = true := by
  decide +kernel

section Apply

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

theorem log_tower3 (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y θ : E) (hx : x′ = 1)
    (hy : y ^ 2 = 3 * x ^ 2 + 1) (hθ : θ′ = 1 / x)
    (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc ({x, y, θ} : Set E)) (A : ICode 1)
    (hwA : wfI 1 A = true) :
    HasElementaryIntegral (evI Kc x y (fun m ↦ if m = 0 then θ else 1) 1 A) ↔
      elemNX (fun m ↦ trK (ptP 0 1 3 0) (ptQ 0 1 3 0) (ptR 0 1 3 0) (ptQ 0 1 3 0)
        (ptρ 0 1 3 0) m (iksL m))
        (fun m ↦ tr (ptP 0 1 3 0) (ptQ 0 1 3 0) (ptR 0 1 3 0) (ptQ 0 1 3 0) m (ilvL m)) 1
        (scal (ptρ 0 1 3 0) 1
          (tr (ptP 0 1 3 0) (ptQ 0 1 3 0) (ptR 0 1 3 0) (ptQ 0 1 3 0) 1 A)) = true := by
  refine genus0_pt_decides hC hCall x y hx 0 1 3 0 (by norm_num) (by rw [hy]; push_cast; ring)
    iksL ilvL _ (fun m ↦ ?_) (fun m a hk ↦ ?_) (fun m ↦ ?_) 1 (fun z ↦ ?_) certP A hwA
  · rcases m with _ | m
    · show θ′ = PrimN.evx Kc x _ + PrimN.evx Kc x _ * y
      simp [PrimN.evx, CPoly.toPoly, hθ]
    · simp only [iksL, kderI, evI_iconst, Rat.cast_zero, Derivation.map_zero, zero_mul,
        show m + 1 ≠ 0 from Nat.succ_ne_zero m, if_false, Derivation.map_one_eq_zero]
  · rcases m with _ | m
    · simp [iksL] at hk
    · simp
  · rcases m with _ | m
    · decide
    · simp [wfK, iksL, wfI_iconst]
  · refine (IntermediateField.adjoin_le_iff.mpr ?_) (hgen z)
    intro w hw
    rcases hw with rfl | rfl | rfl
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · refine IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ ⟨0, by simp, by simp⟩))

lemma y_ne_zero3 (x y : E) (hx : x′ = 1) (hy : y ^ 2 = 3 * x ^ 2 + 1) : y ≠ 0 := by
  intro h0; rw [h0] at hy
  have h1 := congrArg (fun z : E ↦ z′) hy
  have h3d : (3 : E)′ = 0 := by
    have := deriv_ratCast_L (L := E) 3; simpa using this
  simp only [pow_two, Derivation.leibniz, smul_eq_mul, hx, map_add, h3d,
    Derivation.map_one_eq_zero, mul_zero, zero_mul, map_zero, mul_one, add_zero, zero_add] at h1
  have hx0 : x = 0 := by
    have : (6 : E) * x = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  rw [hx0] at hy; norm_num at hy

/-- **`∫ log x / √(3x² + 1) dx` is not elementary.** -/
theorem log_div_sqrt3_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y θ : E) (hx : x′ = 1)
    (hy : y ^ 2 = 3 * x ^ 2 + 1) (hθ : θ′ = 1 / x)
    (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc ({x, y, θ} : Set E)) :
    ¬HasElementaryIntegral (θ / y) := by
  have h := log_tower3 hC hCall x y θ hx hy hθ hgen B1 (by decide)
  rw [pans1] at h
  have hy0 := y_ne_zero3 x y hx hy
  set ts : ℕ → E := fun m ↦ if m = 0 then θ else 1
  have e : evI Kc x y ts 1 B1 = θ / y := by
    rw [show evI Kc x y ts 1 B1 = (evI Kc x y ts 0 (iconst 0 0) + ts 0 *
        (evI Kc x y ts 0 yinv3 + ts 0 * 0)) / (evI Kc x y ts 0 (iconst 0 1) + ts 0 * 0) from rfl,
      evI_iconst, evI_iconst]
    have hyv : evI Kc x y ts 0 yinv3 = 1 / y := by
      show PrimN.evx Kc x _ + PrimN.evx Kc x _ * y = 1 / y
      simp [PrimN.evx, yinv3, CPoly.toPoly, map_ofNat]
      rw [show (1 + x * (x * 3) : E) = y ^ 2 by rw [hy]; ring]
      field_simp
    rw [hyv]; simp [ts, div_eq_mul_inv]
  rw [e] at h
  intro h'
  exact Bool.false_ne_true (h.mp h')

/-- **`∫ x log x / √(3x² + 1) dx` is elementary.** -/
theorem xlog_div_sqrt3_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y θ : E) (hx : x′ = 1)
    (hy : y ^ 2 = 3 * x ^ 2 + 1) (hθ : θ′ = 1 / x)
    (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc ({x, y, θ} : Set E)) :
    HasElementaryIntegral (x * θ / y) := by
  have h := log_tower3 hC hCall x y θ hx hy hθ hgen B2 (by decide)
  rw [pans2] at h
  have hy0 := y_ne_zero3 x y hx hy
  set ts : ℕ → E := fun m ↦ if m = 0 then θ else 1
  have e : evI Kc x y ts 1 B2 = x * θ / y := by
    rw [show evI Kc x y ts 1 B2 = (evI Kc x y ts 0 (iconst 0 0) + ts 0 *
        (evI Kc x y ts 0 xyinv3 + ts 0 * 0)) / (evI Kc x y ts 0 (iconst 0 1) + ts 0 * 0) from rfl,
      evI_iconst, evI_iconst]
    have hyv : evI Kc x y ts 0 xyinv3 = x / y := by
      show PrimN.evx Kc x _ + PrimN.evx Kc x _ * y = x / y
      simp [PrimN.evx, xyinv3, CPoly.toPoly, map_ofNat]
      rw [show (1 + x * (x * 3) : E) = y ^ 2 by rw [hy]; ring]
      field_simp
    rw [hyv]; simp [ts, div_eq_mul_inv]; ring
  rw [e] at h
  exact h.mpr rfl

end Apply

end Tower.Genus0Auto.PtExample
