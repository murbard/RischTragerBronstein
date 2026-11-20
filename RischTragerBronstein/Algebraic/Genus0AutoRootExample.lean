import RischTragerBronstein.Algebraic.Genus0AutoRoot
import RischTragerBronstein.Algebraic.Genus0AutoExample

/-!
# Automatic genus-zero towers through a rational root: `√(2x² − 2)`

Over `Kc(x, y)`, `y² = 2x² − 2 = (x − 1)(2x + 2)` (leading coefficient not a square), with
`θ = log x`, decided by `genus0_root_decides` (`t = y/(x − 1)`), computed and kernel-checked:
* `∫ log x / √(2x² − 2) dx` is **not** elementary;
* `∫ x log x / √(2x² − 2) dx` is elementary.
-/

open Polynomial Differential IntermediateField

namespace Tower.Genus0Auto.RootExample

open Tower Tower.PrimN Tower.NestP Tower.NestM Tower.NestX CPoly Tower.Genus0Auto.Example

/-- `θ′ = 1/x`; padding levels `exp 0`. -/
def iksL : (m : ℕ) → IKind m
  | 0 => .prim ((([1] : CPoly ℚ), ([0, 1] : CPoly ℚ)), (([] : CPoly ℚ), ([1] : CPoly ℚ)))
  | m + 1 => .exp (iconst (m + 1) 0)
/-- `θ = log x`. -/
def ilvL : (m : ℕ) → ICode m
  | 0 => xcode
  | m + 1 => iconst (m + 1) 1
/-- `1/y = y/(2x² − 2)`. -/
def yinv : ICode 0 := ((([] : CPoly ℚ), ([1] : CPoly ℚ)), (([1] : CPoly ℚ), ([-2, 0, 2] : CPoly ℚ)))
/-- `x/y = x y/(2x² − 2)`. -/
def xyinv : ICode 0 := ((([] : CPoly ℚ), ([1] : CPoly ℚ)), (([0, 1] : CPoly ℚ), ([-2, 0, 2] : CPoly ℚ)))
def A1 : ICode 1 := ([iconst 0 0, yinv], [iconst 0 1])
def A2 : ICode 1 := ([iconst 0 0, xyinv], [iconst 0 1])

set_option maxRecDepth 100000

theorem certL : certX (fun m ↦ trK (rootP 1 2 2) (rootQ 1 2 2) (rootR 1 2 2) (rootQ 1 2 2)
    (rootρ 1 2 2) m (iksL m))
    (fun m ↦ tr (rootP 1 2 2) (rootQ 1 2 2) (rootR 1 2 2) (rootQ 1 2 2) m (ilvL m)) 1 = true := by
  decide +kernel

theorem ans1 : elemNX (fun m ↦ trK (rootP 1 2 2) (rootQ 1 2 2) (rootR 1 2 2) (rootQ 1 2 2)
    (rootρ 1 2 2) m (iksL m))
    (fun m ↦ tr (rootP 1 2 2) (rootQ 1 2 2) (rootR 1 2 2) (rootQ 1 2 2) m (ilvL m)) 1
    (scal (rootρ 1 2 2) 1 (tr (rootP 1 2 2) (rootQ 1 2 2) (rootR 1 2 2) (rootQ 1 2 2) 1 A1))
      = false := by
  decide +kernel

theorem ans2 : elemNX (fun m ↦ trK (rootP 1 2 2) (rootQ 1 2 2) (rootR 1 2 2) (rootQ 1 2 2)
    (rootρ 1 2 2) m (iksL m))
    (fun m ↦ tr (rootP 1 2 2) (rootQ 1 2 2) (rootR 1 2 2) (rootQ 1 2 2) m (ilvL m)) 1
    (scal (rootρ 1 2 2) 1 (tr (rootP 1 2 2) (rootQ 1 2 2) (rootR 1 2 2) (rootQ 1 2 2) 1 A2))
      = true := by
  decide +kernel

section Apply

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

theorem log_tower (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y θ : E) (hx : x′ = 1)
    (hy : y ^ 2 = 2 * x ^ 2 - 2) (hθ : θ′ = 1 / x)
    (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc ({x, y, θ} : Set E)) (A : ICode 1)
    (hwA : wfI 1 A = true) :
    HasElementaryIntegral (evI Kc x y (fun m ↦ if m = 0 then θ else 1) 1 A) ↔
      elemNX (fun m ↦ trK (rootP 1 2 2) (rootQ 1 2 2) (rootR 1 2 2) (rootQ 1 2 2)
        (rootρ 1 2 2) m (iksL m))
        (fun m ↦ tr (rootP 1 2 2) (rootQ 1 2 2) (rootR 1 2 2) (rootQ 1 2 2) m (ilvL m)) 1
        (scal (rootρ 1 2 2) 1
          (tr (rootP 1 2 2) (rootQ 1 2 2) (rootR 1 2 2) (rootQ 1 2 2) 1 A)) = true := by
  refine genus0_root_decides hC hCall x y hx 1 2 2 (by norm_num) (by rw [hy]; push_cast; ring)
    iksL ilvL _ (fun m ↦ ?_) (fun m a hk ↦ ?_) (fun m ↦ ?_) 1 (fun z ↦ ?_) certL A hwA
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

lemma y_ne_zero (x y : E) (hx : x′ = 1) (hy : y ^ 2 = 2 * x ^ 2 - 2) : y ≠ 0 := by
  intro h0; rw [h0] at hy
  have h1 := congrArg (fun z : E ↦ z′) hy
  have h2d : (2 : E)′ = 0 := by
    have := deriv_ratCast_L (L := E) 2; simpa using this
  simp only [pow_two, Derivation.leibniz, smul_eq_mul, hx, map_sub, h2d, mul_zero, zero_mul,
    map_zero, mul_one, add_zero, zero_add] at h1
  have hx0 : x = 0 := by
    have : (4 : E) * x = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  rw [hx0] at hy; norm_num at hy

/-- **`∫ log x / √(2x² − 2) dx` is not elementary.** -/
theorem log_div_sqrt_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y θ : E) (hx : x′ = 1)
    (hy : y ^ 2 = 2 * x ^ 2 - 2) (hθ : θ′ = 1 / x)
    (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc ({x, y, θ} : Set E)) :
    ¬HasElementaryIntegral (θ / y) := by
  have h := log_tower hC hCall x y θ hx hy hθ hgen A1 (by decide)
  rw [ans1] at h
  have hy0 := y_ne_zero x y hx hy
  set ts : ℕ → E := fun m ↦ if m = 0 then θ else 1
  have e : evI Kc x y ts 1 A1 = θ / y := by
    rw [show evI Kc x y ts 1 A1 = (evI Kc x y ts 0 (iconst 0 0) + ts 0 *
        (evI Kc x y ts 0 yinv + ts 0 * 0)) / (evI Kc x y ts 0 (iconst 0 1) + ts 0 * 0) from rfl,
      evI_iconst, evI_iconst]
    have hyv : evI Kc x y ts 0 yinv = 1 / y := by
      show PrimN.evx Kc x _ + PrimN.evx Kc x _ * y = 1 / y
      simp [PrimN.evx, yinv, CPoly.toPoly, map_ofNat]
      rw [show (-2 + x * (x * 2) : E) = y ^ 2 by rw [hy]; ring]
      field_simp
    rw [hyv]; simp [ts, div_eq_mul_inv]
  rw [e] at h
  intro h'
  exact Bool.false_ne_true (h.mp h')

/-- **`∫ x log x / √(2x² − 2) dx` is elementary.** -/
theorem xlog_div_sqrt_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y θ : E) (hx : x′ = 1)
    (hy : y ^ 2 = 2 * x ^ 2 - 2) (hθ : θ′ = 1 / x)
    (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc ({x, y, θ} : Set E)) :
    HasElementaryIntegral (x * θ / y) := by
  have h := log_tower hC hCall x y θ hx hy hθ hgen A2 (by decide)
  rw [ans2] at h
  have hy0 := y_ne_zero x y hx hy
  set ts : ℕ → E := fun m ↦ if m = 0 then θ else 1
  have e : evI Kc x y ts 1 A2 = x * θ / y := by
    rw [show evI Kc x y ts 1 A2 = (evI Kc x y ts 0 (iconst 0 0) + ts 0 *
        (evI Kc x y ts 0 xyinv + ts 0 * 0)) / (evI Kc x y ts 0 (iconst 0 1) + ts 0 * 0) from rfl,
      evI_iconst, evI_iconst]
    have hyv : evI Kc x y ts 0 xyinv = x / y := by
      show PrimN.evx Kc x _ + PrimN.evx Kc x _ * y = x / y
      simp [PrimN.evx, xyinv, CPoly.toPoly, map_ofNat]
      rw [show (-2 + x * (x * 2) : E) = y ^ 2 by rw [hy]; ring]
      field_simp
    rw [hyv]; simp [ts, div_eq_mul_inv]; ring
  rw [e] at h
  exact h.mpr rfl

end Apply

end Tower.Genus0Auto.RootExample
