import RischTragerBronstein.Computable.NestPDecide

/-!
# Towers of nested primitives: examples

In any differential field `E` generated over its constants by `x`, `t₀ = log x`,
`t₁ = log log x` (`t₀′ = 1/x`, `t₁′ = 1/(x t₀)`) — `nestN_decides`; certificates and answers are
computed by the kernel.

* `∫ dx / log x` (the logarithmic integral) is **not** elementary; `∫ dx/(x log x) = log log x` is.
* `∫ log log x dx` is **not** elementary; `∫ log log x/(x log x) dx = (log log x)²/2` is;
  `∫ (log log x + 1/log x) dx = x log log x` is (two non-elementary integrals cancelling).
-/

open Differential

namespace Tower.NestP.Examples

open Tower.PrimN

def r (n d : CPoly ℚ) : Code 1 := (n, d)
def one₁ : Code 1 := r [1] [1]
def zero₁ : Code 1 := r [] [1]
def one₂ : Code 2 := ([one₁], [one₁])
def zero₂ : Code 2 := ([], [one₁])
/-- `1/(x t₀)`. -/
def invxT0 : Code 2 := ([r [1] [0, 1]], [zero₁, one₁])
/-- `1/t₀`. -/
def invT0 : Code 2 := ([one₁], [zero₁, one₁])

/-- `t₀ = log x`, `t₁ = log log x` (higher levels unused). -/
def ηs : (m : ℕ) → Code (m + 1)
  | 0 => r [1] [0, 1]
  | 1 => invxT0
  | m + 2 => ([], [oneC (m + 2)])

set_option maxRecDepth 100000

theorem cert1 : nestCert ηs 1 = true := by decide +kernel
theorem cert2 : nestCert ηs 2 = true := by decide +kernel

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc]

lemma val_invT0 (T : NestTower Kc E ηs) (h : T.Tr 1) :
    (((T.MP 1 h).sem invT0 : T.F 1) : E) = 1 / T.ts 0 := by
  refine (T.sem_MP 1 h _).trans ?_
  simp [evN, evP, evx, invT0, one₁, zero₁, r, CPoly.toPoly, List.foldr]

lemma val_T1 (T : NestTower Kc E ηs) (h : T.Tr 2) :
    (((T.MP 2 h).sem (([zero₂, one₂], [one₂]) : Code 3) : T.F 2) : E) = T.ts 1 := by
  refine (T.sem_MP 2 h _).trans ?_
  simp [evN, evP, evx, one₂, zero₂, one₁, zero₁, r, CPoly.toPoly, List.foldr]

/-- **The logarithmic integral `∫ dx / log x` is not elementary.** -/
theorem li_not_elementary (T : NestTower Kc E ηs) (hgen : T.F 1 = ⊤) :
    ¬HasElementaryIntegral (1 / T.ts 0) := by
  rw [← val_invT0 T (T.tr_of_ND (T.nd_of_nestCert 1 cert1))]
  exact fun h ↦ absurd ((T.nestN_decides 1 hgen cert1 _).mp h) (by decide +kernel)

/-- `∫ dx/(x log x) = log log x`: the algorithm answers yes. -/
theorem inv_x_log_elementary (T : NestTower Kc E ηs) (hgen : T.F 1 = ⊤) :
    HasElementaryIntegral ((((T.MP 1 (T.tr_of_ND (T.nd_of_nestCert 1 cert1))).sem invxT0 :
      T.F 1) : E)) :=
  (T.nestN_decides 1 hgen cert1 _).mpr (by decide +kernel)

/-- **`∫ log log x dx` is not elementary.** -/
theorem log_log_not_elementary (T : NestTower Kc E ηs) (hgen : T.F 2 = ⊤) :
    ¬HasElementaryIntegral (T.ts 1) := by
  rw [← val_T1 T (T.tr_of_ND (T.nd_of_nestCert 2 cert2))]
  exact fun h ↦ absurd ((T.nestN_decides 2 hgen cert2 _).mp h) (by decide +kernel)

/-- `∫ log log x/(x log x) dx = (log log x)²/2`: the algorithm answers yes. -/
theorem log_log_deriv_elementary (T : NestTower Kc E ηs) (hgen : T.F 2 = ⊤) :
    HasElementaryIntegral ((((T.MP 2 (T.tr_of_ND (T.nd_of_nestCert 2 cert2))).sem
      (([zero₂, invxT0], [one₂]) : Code 3) : T.F 2) : E)) :=
  (T.nestN_decides 2 hgen cert2 _).mpr (by decide +kernel)

/-- `∫ (log log x + 1/log x) dx = x log log x`: two non-elementary integrals cancel. -/
theorem log_log_li_elementary (T : NestTower Kc E ηs) (hgen : T.F 2 = ⊤) :
    HasElementaryIntegral ((((T.MP 2 (T.tr_of_ND (T.nd_of_nestCert 2 cert2))).sem
      (([invT0, one₂], [one₂]) : Code 3) : T.F 2) : E)) :=
  (T.nestN_decides 2 hgen cert2 _).mpr (by decide +kernel)

end Tower.NestP.Examples
