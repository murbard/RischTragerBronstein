import RischTragerBronstein.Computable.NestXDecide

/-!
# Mixed towers of logarithms and exponentials: examples

Certificates and answers are computed by the kernel; `nestX_decides` turns them into theorems about
any differential field `E` generated over its constants by the tower.

* `t₀ = log x`, `t₁ = exp(x + t₀ / 2) = √x eˣ`: `∫ √x eˣ dx` is **not** elementary;
* `t₀ = log x`, `t₁ = exp(x t₀) = xˣ`: `∫ xˣ dx` is **not** elementary,
  `∫ (1 + log x) xˣ dx = xˣ` is;
* `t₀ = eˣ`, `t₁ = log(eˣ + 1)`: `∫ log(eˣ + 1) dx` is **not** elementary.
-/

open Differential

namespace Tower.NestX.Examples

open Tower.PrimN Tower.NestP Tower.NestM

def r (n d : CPoly ℚ) : Code 1 := (n, d)
def one₁ : Code 1 := r [1] [1]
def zero₁ : Code 1 := r [] [1]
def one₂ : Code 2 := ([one₁], [one₁])
def zero₂ : Code 2 := ([], [one₁])
/-- `t₁`. -/
def T1 : Code 3 := ([zero₂, one₂], [one₂])
/-- `(1 + t₀) t₁`. -/
def dxx : Code 3 := ([zero₂, ([one₁, one₁], [one₁])], [one₂])

/-- `t₀ = log x`, `t₁ = exp(x + t₀ / 2)`. -/
def ksA : (m : ℕ) → KindN m
  | 0 => .prim (r [1] [0, 1])
  | 1 => .exp ([r [0, 1] [1], r [1/2] [1]], [one₁])
  | m + 2 => .exp (constC (m + 3) 0)
/-- `t₀ = log x`, `t₁ = exp(x t₀)`. -/
def ksC : (m : ℕ) → KindN m
  | 0 => .prim (r [1] [0, 1])
  | 1 => .exp ([zero₁, r [0, 1] [1]], [one₁])
  | m + 2 => .exp (constC (m + 3) 0)
/-- The logarithm argument `x` at level `0`. -/
def lvA : (m : ℕ) → Code (m + 1)
  | 0 => r [0, 1] [1]
  | m + 1 => constC (m + 2) 1
/-- `t₀ = eˣ`, `t₁ = log(eˣ + 1)`. -/
def ksB : (m : ℕ) → KindN m
  | 0 => .exp (r [0, 1] [1])
  | 1 => .prim ([zero₁, one₁], [one₁, one₁])
  | m + 2 => .exp (constC (m + 3) 0)
def lvB : (m : ℕ) → Code (m + 1)
  | 0 => constC 1 1
  | 1 => ([one₁, one₁], [one₁])
  | m + 2 => constC (m + 3) 1

set_option maxRecDepth 100000

theorem certA : certX ksA lvA 2 = true := by decide +kernel
theorem certC : certX ksC lvA 2 = true := by decide +kernel
theorem certB : certX ksB lvB 2 = true := by decide +kernel

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc]

lemma val_T1 {ks : (m : ℕ) → KindN m} (T : NestMTower Kc E ks) (h : T.Tr 2) :
    (((T.MP 2 h).sem T1 : T.F 2) : E) = T.ts 1 := by
  refine (T.sem_MP 2 h _).trans ?_
  simp [evN, PrimN.evx, T1, one₂, zero₂, one₁, zero₁, r, CPoly.toPoly, List.foldr]

lemma val_dxx {ks : (m : ℕ) → KindN m} (T : NestMTower Kc E ks) (h : T.Tr 2) :
    (((T.MP 2 h).sem dxx : T.F 2) : E) = (1 + T.ts 0) * T.ts 1 := by
  refine (T.sem_MP 2 h _).trans ?_
  simp [evN, PrimN.evx, dxx, one₂, zero₂, one₁, zero₁, r, CPoly.toPoly, List.foldr, mul_comm]

/-- **`∫ √x eˣ dx` is not elementary** (`t₀ = log x`, `t₁ = exp(x + t₀ / 2)`). -/
theorem sqrt_exp_not_elementary (T : NestMTower Kc E ksA) (hgen : T.F 2 = ⊤) :
    ¬HasElementaryIntegral (T.ts 1) := by
  rw [← val_T1 T ((T.xspecs lvA 2 certA).hyp.tr)]
  exact fun h ↦ absurd ((T.nestX_decides lvA 2 hgen certA _).mp h) (by decide +kernel)

/-- **`∫ xˣ dx` is not elementary** (`t₀ = log x`, `t₁ = exp(x t₀)`). -/
theorem x_pow_x_not_elementary (T : NestMTower Kc E ksC) (hgen : T.F 2 = ⊤) :
    ¬HasElementaryIntegral (T.ts 1) := by
  rw [← val_T1 T ((T.xspecs lvA 2 certC).hyp.tr)]
  exact fun h ↦ absurd ((T.nestX_decides lvA 2 hgen certC _).mp h) (by decide +kernel)

/-- `∫ (1 + log x) xˣ dx = xˣ`: the algorithm answers yes. -/
theorem x_pow_x_deriv_elementary (T : NestMTower Kc E ksC) (hgen : T.F 2 = ⊤) :
    HasElementaryIntegral ((1 + T.ts 0) * T.ts 1) := by
  rw [← val_dxx T ((T.xspecs lvA 2 certC).hyp.tr)]
  exact (T.nestX_decides lvA 2 hgen certC _).mpr (by decide +kernel)

/-- **`∫ log(eˣ + 1) dx` is not elementary** (`t₀ = eˣ`, `t₁ = log(eˣ + 1)`). -/
theorem log_exp_add_one_not_elementary (T : NestMTower Kc E ksB) (hgen : T.F 2 = ⊤) :
    ¬HasElementaryIntegral (T.ts 1) := by
  rw [← val_T1 T ((T.xspecs lvB 2 certB).hyp.tr)]
  exact fun h ↦ absurd ((T.nestX_decides lvB 2 hgen certB _).mp h) (by decide +kernel)

end Tower.NestX.Examples
