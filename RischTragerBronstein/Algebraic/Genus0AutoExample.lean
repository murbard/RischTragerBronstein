import RischTragerBronstein.Algebraic.Genus0AutoSq

/-!
# Automatic genus-zero towers: `asinh`

Over `Kc(x, y)`, `y² = x² + 1`, with `θ = log(x + y)` (`θ′ = 1/y`), decided by
`genus0_sq_decides` (Euler's substitution `t = y − x`, everything computed and kernel-checked):
* `∫ θ / x dx` (`∫ asinh(x)/x`) is **not** elementary;
* `∫ θ dx` (`∫ asinh x`) is elementary.
-/

open Polynomial Differential IntermediateField

namespace Tower.Genus0Auto.Example

open Tower Tower.PrimN Tower.NestP Tower.NestM Tower.NestX CPoly

/-- A rational constant as an input code. -/
def iconst : (m : ℕ) → ℚ → ICode m
  | 0, c => ((([c] : CPoly ℚ), ([1] : CPoly ℚ)), (([] : CPoly ℚ), ([1] : CPoly ℚ)))
  | m + 1, c => ([iconst m c], [iconst m 1])

/-- `θ′ = 1/y = y/(x² + 1)`; padding levels `exp 0`. -/
def iksA : (m : ℕ) → IKind m
  | 0 => .prim ((([] : CPoly ℚ), ([1] : CPoly ℚ)), (([1] : CPoly ℚ), ([1, 0, 1] : CPoly ℚ)))
  | m + 1 => .exp (iconst (m + 1) 0)

/-- `θ = log(x + y)`. -/
def ilvA : (m : ℕ) → ICode m
  | 0 => ((([0, 1] : CPoly ℚ), ([1] : CPoly ℚ)), (([1] : CPoly ℚ), ([1] : CPoly ℚ)))
  | m + 1 => iconst (m + 1) 1

/-- `x`. -/
def xcode : ICode 0 := ((([0, 1] : CPoly ℚ), ([1] : CPoly ℚ)), (([] : CPoly ℚ), ([1] : CPoly ℚ)))
/-- `θ / x`. -/
def AA : ICode 1 := ([iconst 0 0, iconst 0 1], [xcode])
/-- `θ`. -/
def AB : ICode 1 := ([iconst 0 0, iconst 0 1], [iconst 0 1])

set_option maxRecDepth 100000

theorem certA : certX (fun m ↦ trK (eulerP 1 0 1) (eulerQ 1 0 1) (eulerR 1 0 1) (eulerQ 1 0 1)
    (eulerρ 1 0 1) m (iksA m))
    (fun m ↦ tr (eulerP 1 0 1) (eulerQ 1 0 1) (eulerR 1 0 1) (eulerQ 1 0 1) m (ilvA m)) 1 = true := by
  decide +kernel

theorem ansA : elemNX (fun m ↦ trK (eulerP 1 0 1) (eulerQ 1 0 1) (eulerR 1 0 1) (eulerQ 1 0 1)
    (eulerρ 1 0 1) m (iksA m))
    (fun m ↦ tr (eulerP 1 0 1) (eulerQ 1 0 1) (eulerR 1 0 1) (eulerQ 1 0 1) m (ilvA m)) 1
    (scal (eulerρ 1 0 1) 1 (tr (eulerP 1 0 1) (eulerQ 1 0 1) (eulerR 1 0 1) (eulerQ 1 0 1) 1 AA))
      = false := by
  decide +kernel

theorem ansB : elemNX (fun m ↦ trK (eulerP 1 0 1) (eulerQ 1 0 1) (eulerR 1 0 1) (eulerQ 1 0 1)
    (eulerρ 1 0 1) m (iksA m))
    (fun m ↦ tr (eulerP 1 0 1) (eulerQ 1 0 1) (eulerR 1 0 1) (eulerQ 1 0 1) m (ilvA m)) 1
    (scal (eulerρ 1 0 1) 1 (tr (eulerP 1 0 1) (eulerQ 1 0 1) (eulerR 1 0 1) (eulerQ 1 0 1) 1 AB))
      = true := by
  decide +kernel

section Apply

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma evI_iconst (x y : E) (ts : ℕ → E) : ∀ (m : ℕ) (c : ℚ), evI Kc x y ts m (iconst m c) = c
  | 0, c => by simp [evI, iconst, PrimN.evx, CPoly.toPoly]
  | m + 1, c => by
    simp only [evI, iconst, List.foldr_cons, List.foldr_nil, mul_zero, add_zero,
      evI_iconst x y ts m, Rat.cast_one, div_one]

lemma wfI_iconst : ∀ (m : ℕ) (c : ℚ), wfI m (iconst m c) = true
  | 0, c => by simp only [wfI, iconst]; decide
  | m + 1, c => by simp [wfI, iconst, wfI_iconst m]

/-- The common setting: `y² = x² + 1`, `θ′ = 1/y`, `E = Kc(x, y, θ)`. -/
theorem asinh_tower (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y θ : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 2 + 1) (hθ : θ′ = 1 / y)
    (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc ({x, y, θ} : Set E)) (A : ICode 1)
    (hwA : wfI 1 A = true) :
    HasElementaryIntegral (evI Kc x y (fun m ↦ if m = 0 then θ else 1) 1 A) ↔
      elemNX (fun m ↦ trK (eulerP 1 0 1) (eulerQ 1 0 1) (eulerR 1 0 1) (eulerQ 1 0 1)
        (eulerρ 1 0 1) m (iksA m))
        (fun m ↦ tr (eulerP 1 0 1) (eulerQ 1 0 1) (eulerR 1 0 1) (eulerQ 1 0 1) m (ilvA m)) 1
        (scal (eulerρ 1 0 1) 1
          (tr (eulerP 1 0 1) (eulerQ 1 0 1) (eulerR 1 0 1) (eulerQ 1 0 1) 1 A)) = true := by
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0] at hy
    have h1 := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul, hx, map_add, Derivation.map_one_eq_zero,
      mul_zero, add_zero, zero_mul, map_zero, mul_one] at h1
    have hx0 : x = 0 := by
      have : (2 : E) * x = 0 := by linear_combination -h1
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero
    rw [hx0] at hy; norm_num at hy
  refine genus0_sq_decides hC hCall x y hx 1 0 1 (by norm_num) (by norm_num)
    (by rw [hy]; push_cast; ring) iksA ilvA _ (fun m ↦ ?_) (fun m a hk ↦ ?_) (fun m ↦ ?_) 1
    (fun z ↦ ?_) certA A hwA
  · rcases m with _ | m
    · simp only [iksA, kderI, evI, PrimN.evx, CPoly.toPoly, if_true]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        map_add, map_mul, aeval_C, aeval_X, eq_ratCast, mul_zero, add_zero, Polynomial.map_zero,
        map_zero, zero_div, zero_add, Rat.cast_one, Polynomial.map_one, map_one, div_one, one_mul]
      rw [hθ]
      have h1x : (1 : E) + x ^ 2 ≠ 0 := by rw [add_comm, ← hy]; exact pow_ne_zero 2 hy0
      field_simp
      first | linear_combination hy | linear_combination -hy
    · simp only [iksA, kderI, evI_iconst, Rat.cast_zero, Derivation.map_zero, zero_mul,
        show m + 1 ≠ 0 from Nat.succ_ne_zero m, if_false, Derivation.map_one_eq_zero]
  · rcases m with _ | m
    · simp [iksA] at hk
    · simp
  · rcases m with _ | m
    · decide
    · simp [wfK, iksA, wfI_iconst]
  · refine (IntermediateField.adjoin_le_iff.mpr ?_) (hgen z)
    intro w hw
    rcases hw with rfl | rfl | rfl
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · refine IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ ⟨0, by simp, by simp⟩))

/-- **`∫ log(x + √(x² + 1)) / x dx` is not elementary** — found automatically. -/
theorem asinh_div_x_not_elementary' (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y θ : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 2 + 1) (hθ : θ′ = 1 / y)
    (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc ({x, y, θ} : Set E)) :
    ¬HasElementaryIntegral (θ / x) := by
  have h := asinh_tower hC hCall x y θ hx hy hθ hgen AA (by decide)
  rw [ansA] at h
  have e : evI Kc x y (fun m ↦ if m = 0 then θ else 1) 1 AA = θ / x := by
    set ts : ℕ → E := fun m ↦ if m = 0 then θ else 1
    rw [show evI Kc x y ts 1 AA = (evI Kc x y ts 0 (iconst 0 0) + ts 0 *
        (evI Kc x y ts 0 (iconst 0 1) + ts 0 * 0)) / (evI Kc x y ts 0 xcode + ts 0 * 0) from rfl,
      evI_iconst, evI_iconst]
    have hxc : evI Kc x y ts 0 xcode = x := by
      show PrimN.evx Kc x _ + PrimN.evx Kc x _ * y = x
      simp [PrimN.evx, xcode, CPoly.toPoly]
    rw [hxc]
    simp [ts]
  rw [e] at h
  intro h'
  exact Bool.false_ne_true (h.mp h')

/-- **`∫ log(x + √(x² + 1)) dx` is elementary** — found automatically. -/
theorem asinh_elementary' (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y θ : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 2 + 1) (hθ : θ′ = 1 / y)
    (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc ({x, y, θ} : Set E)) :
    HasElementaryIntegral θ := by
  have h := asinh_tower hC hCall x y θ hx hy hθ hgen AB (by decide)
  rw [ansB] at h
  have e : evI Kc x y (fun m ↦ if m = 0 then θ else 1) 1 AB = θ := by
    set ts : ℕ → E := fun m ↦ if m = 0 then θ else 1
    rw [show evI Kc x y ts 1 AB = (evI Kc x y ts 0 (iconst 0 0) + ts 0 *
        (evI Kc x y ts 0 (iconst 0 1) + ts 0 * 0)) / (evI Kc x y ts 0 (iconst 0 1) + ts 0 * 0)
        from rfl, evI_iconst, evI_iconst]
    simp [ts]
  rw [e] at h
  exact h.mpr rfl

end Apply

end Tower.Genus0Auto.Example
