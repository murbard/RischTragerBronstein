import RischTragerBronstein.Computable.MixNDecide

/-!
# Mixed towers of logarithms and exponentials: examples

In any differential field `E` generated over its constants by `x` and the `tᵢ`, with the stated
derivatives (`mixN_decides`); certificates and answers are computed by the kernel.

* `ℚ(x, exp(x²))`: `∫ exp(x²)` is **not** elementary.
* `ℚ(x, log x, eˣ)`: `∫ eˣ log x` is not elementary; `∫ eˣ (log x + 1/x) = eˣ log x` is.
* `ℚ(x, eˣ, exp(x²))`: `∫ eˣ exp(x²)` is not elementary.
* `ℚ(x, log x, log (x + 1), eˣ)` (height 3): `∫ eˣ log x` is not elementary;
  `∫ eˣ (log (x + 1) + 1/(x + 1))` is.
* exponentials of rational functions: `∫ exp(1/x)` is not elementary, `∫ exp(1/x)/x²` is;
  in `ℚ(x, log x, exp(1/x))`, `∫ exp(1/x) log x` is not elementary and
  `∫ exp(1/x) (1/x - log x/x²) = exp(1/x) log x` is.
* hyperexponentials (exponents with simple poles): `∫ exp(arctan x)` and `∫ exp(arctan x) log x`
  are not elementary, `∫ exp(arctan x)/(x² + 1)` and
  `∫ exp(arctan x) (1/x + log x/(x² + 1)) = exp(arctan x) log x` are; with the degenerate pair
  `t₀′ = 6 t₀/(x³ - 2)`, `t₁′ = 6x t₁/(x³ - 2)`, `∫ t₀ t₁` is not elementary and
  `∫ (6 + 6x)/(x³ - 2) t₀ t₁ = t₀ t₁` is; at height three, `∫ exp(arctan x) log x` is not
  elementary in `ℚ(x, log x, eˣ, exp(arctan x))`.
-/

open Differential

namespace Tower.MixN.Examples

open Tower.PrimN

def r (n d : CPoly ℚ) : Code 1 := (n, d)
def one₁ : Code 1 := r [1] [1]
def zero₁ : Code 1 := r [] [1]
def c2 (q : Code 1) : Code 2 := ([q], [one₁])
/-- `t₀`, as a code of `ℚ(x)(t₀)`. -/
def T1 : Code 2 := ([zero₁, one₁], [one₁])
def one₂ : Code 2 := c2 one₁
def zero₂ : Code 2 := ([], [one₁])
def c3 (q : Code 2) : Code 3 := ([q], [one₂])
def one₃ : Code 3 := c3 one₂
def zero₃ : Code 3 := ([], [one₂])

/-- `log x`, `log (x + 1)`, `eˣ`, `exp(x²)`, `exp(1/x)`. -/
def lx : Kind := .prim (r [1] [0, 1])
def lx1 : Kind := .prim (r [1] [1, 1])
def ex : Kind := .exp (r [1] [1])
def ex2 : Kind := .exp (r [0, 2] [1])
/-- `exp (1/x)`: `b = -1/x²`. -/
def e1x : Kind := .exp (r [-1] [0, 0, 1])
/-- `exp (arctan x)`: `b = 1/(x² + 1)` (a hyperexponential: `b` has simple poles). -/
def eat : Kind := .exp (r [1] [1, 0, 1])
/-- A degenerate pair: `bᵢ = 6/(x³ - 2)`, `6x/(x³ - 2)` (shared simple poles, no Hermite part). -/
def e6 : Kind := .exp (r [6] [-2, 0, 0, 1])
def e6x : Kind := .exp (r [0, 6] [-2, 0, 0, 1])

set_option maxRecDepth 100000

theorem cert_ex2 : mixCert [ex2] 1 = true := by decide +kernel
theorem cert_lx_ex : mixCert [lx, ex] 2 = true := by decide +kernel
theorem cert_ex_ex2 : mixCert [ex, ex2] 2 = true := by decide +kernel
theorem cert_lx_lx1_ex : mixCert [lx, lx1, ex] 3 = true := by decide +kernel
theorem cert_e1x : mixCert [e1x] 1 = true := by decide +kernel
theorem cert_lx_e1x : mixCert [lx, e1x] 2 = true := by decide +kernel
theorem cert_eat : mixCert [eat] 1 = true := by decide +kernel
theorem cert_lx_eat : mixCert [lx, eat] 2 = true := by decide +kernel
theorem cert_e6_e6x : mixCert [e6, e6x] 2 = true := by decide +kernel
theorem cert_lx_ex_eat : mixCert [lx, ex, eat] 3 = true := by decide +kernel

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc]

/-- The value of the code `t₀` at level `1`. -/
lemma val_T1 {ks : List Kind} (T : MixTower Kc E ks) (h : T.Tr 1) :
    (((T.MP 1 h).sem T1 : T.F 1) : E) = T.ts 0 := by
  have h0 : T.Tr 0 := fun i hi ↦ h i (by omega)
  have hz₁ : (T.MP 0 h0).sem zero₁ = 0 := (T.MP 0 h0).sem_zero
  have ho₁ : (T.MP 0 h0).sem one₁ = 1 := (T.MP 0 h0).sem_one
  show ((T.phi 0 (GPoly.toPoly (T.MP 0 h0) [zero₁, one₁]) /
    T.phi 0 (GPoly.toPoly (T.MP 0 h0) [one₁]) : T.F 1) : E) = _
  rw [IntermediateField.coe_div, T.coe_phi, T.coe_phi]
  simp [GPoly.toPoly_cons, hz₁, ho₁]

/-- The value of the code `t₀ t₁` at level `2`. -/
lemma val_T1T2 {ks : List Kind} (T : MixTower Kc E ks) (h : T.Tr 2) :
    (((T.MP 2 h).sem (([zero₂, T1], [one₂]) : Code 3) : T.F 2) : E) = T.ts 0 * T.ts 1 := by
  have h1 : T.Tr 1 := fun i hi ↦ h i (by omega)
  have hz₂ : (T.MP 1 h1).sem zero₂ = 0 := (T.MP 1 h1).sem_zero
  have ho₂ : (T.MP 1 h1).sem one₂ = 1 := (T.MP 1 h1).sem_one
  have ht1 := val_T1 T h1
  show ((T.phi 1 (GPoly.toPoly (T.MP 1 h1) [zero₂, T1]) /
    T.phi 1 (GPoly.toPoly (T.MP 1 h1) [one₂]) : T.F 2) : E) = _
  rw [IntermediateField.coe_div, T.coe_phi, T.coe_phi]
  simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, hz₂, ho₂, map_mul, Polynomial.aeval_C,
    Polynomial.aeval_X, mul_zero, add_zero, map_zero, map_one, div_one, zero_add]
  rw [show algebraMap (T.F 1) E ((T.MP 1 h1).sem T1) = T.ts 0 from ht1]
  ring

/-- **`∫ exp(x²) dx` is not elementary.** -/
theorem exp_sq_not_elementary (T : MixTower Kc E [ex2]) (hgen : T.F 1 = ⊤) :
    ¬HasElementaryIntegral (T.ts 0) := by
  rw [← val_T1 T (T.tr_noHom_of_ND 1 (T.nd_of_mixCert 1 cert_ex2)).1]
  exact fun h ↦ absurd ((T.mixN_decides 1 hgen cert_ex2 _).mp h) (by decide +kernel)

/-- **`∫ eˣ log x dx` is not elementary** (`t₀ = log x`, `t₁ = eˣ`). -/
theorem exp_log_not_elementary (T : MixTower Kc E [lx, ex]) (hgen : T.F 2 = ⊤) :
    ¬HasElementaryIntegral (T.ts 0 * T.ts 1) := by
  rw [← val_T1T2 T (T.tr_noHom_of_ND 2 (T.nd_of_mixCert 2 cert_lx_ex)).1]
  exact fun h ↦ absurd ((T.mixN_decides 2 hgen cert_lx_ex _).mp h) (by decide +kernel)

/-- `∫ eˣ (log x + 1/x) dx = eˣ log x`: the algorithm answers yes. -/
theorem exp_log_deriv_elementary (T : MixTower Kc E [lx, ex]) (hgen : T.F 2 = ⊤) :
    HasElementaryIntegral ((((T.MP 2 (T.tr_noHom_of_ND 2 (T.nd_of_mixCert 2 cert_lx_ex)).1).sem
      (([zero₂, ([r [1] [0, 1], one₁], [one₁])], [one₂]) : Code 3) : T.F 2) : E)) :=
  (T.mixN_decides 2 hgen cert_lx_ex _).mpr (by decide +kernel)

/-- **`∫ eˣ exp(x²) dx` is not elementary.** -/
theorem exp_exp_sq_not_elementary (T : MixTower Kc E [ex, ex2]) (hgen : T.F 2 = ⊤) :
    ¬HasElementaryIntegral (T.ts 0 * T.ts 1) := by
  rw [← val_T1T2 T (T.tr_noHom_of_ND 2 (T.nd_of_mixCert 2 cert_ex_ex2)).1]
  exact fun h ↦ absurd ((T.mixN_decides 2 hgen cert_ex_ex2 _).mp h) (by decide +kernel)

/-- Height three: `∫ eˣ log x dx` is not elementary in `ℚ(x, log x, log (x + 1), eˣ)`. -/
theorem height3_not_elementary (T : MixTower Kc E [lx, lx1, ex]) (hgen : T.F 3 = ⊤) :
    ¬HasElementaryIntegral ((((T.MP 3 (T.tr_noHom_of_ND 3 (T.nd_of_mixCert 3
      cert_lx_lx1_ex)).1).sem (([zero₃, c3 T1], [one₃]) : Code 4) : T.F 3) : E)) :=
  fun h ↦ absurd ((T.mixN_decides 3 hgen cert_lx_lx1_ex _).mp h) (by decide +kernel)

/-- Height three: `∫ eˣ (log (x + 1) + 1/(x + 1)) dx = eˣ log (x + 1)`. -/
theorem height3_elementary (T : MixTower Kc E [lx, lx1, ex]) (hgen : T.F 3 = ⊤) :
    HasElementaryIntegral ((((T.MP 3 (T.tr_noHom_of_ND 3 (T.nd_of_mixCert 3
      cert_lx_lx1_ex)).1).sem (([zero₃, ([c2 (r [1] [1, 1]), one₂], [one₂])], [one₃]) : Code 4) :
        T.F 3) : E)) :=
  (T.mixN_decides 3 hgen cert_lx_lx1_ex _).mpr (by decide +kernel)

/-- **`∫ exp(1/x) dx` is not elementary.** -/
theorem exp_inv_not_elementary (T : MixTower Kc E [e1x]) (hgen : T.F 1 = ⊤) :
    ¬HasElementaryIntegral (T.ts 0) := by
  rw [← val_T1 T (T.tr_noHom_of_ND 1 (T.nd_of_mixCert 1 cert_e1x)).1]
  exact fun h ↦ absurd ((T.mixN_decides 1 hgen cert_e1x _).mp h) (by decide +kernel)

/-- `∫ exp(1/x)/x² dx = -exp(1/x)`: the algorithm answers yes. -/
theorem exp_inv_deriv_elementary (T : MixTower Kc E [e1x]) (hgen : T.F 1 = ⊤) :
    HasElementaryIntegral ((((T.MP 1 (T.tr_noHom_of_ND 1 (T.nd_of_mixCert 1 cert_e1x)).1).sem
      (([zero₁, r [1] [0, 0, 1]], [one₁]) : Code 2) : T.F 1) : E)) :=
  (T.mixN_decides 1 hgen cert_e1x _).mpr (by decide +kernel)

/-- **`∫ exp(1/x) log x dx` is not elementary** (`t₀ = log x`, `t₁ = exp(1/x)`). -/
theorem exp_inv_log_not_elementary (T : MixTower Kc E [lx, e1x]) (hgen : T.F 2 = ⊤) :
    ¬HasElementaryIntegral (T.ts 0 * T.ts 1) := by
  rw [← val_T1T2 T (T.tr_noHom_of_ND 2 (T.nd_of_mixCert 2 cert_lx_e1x)).1]
  exact fun h ↦ absurd ((T.mixN_decides 2 hgen cert_lx_e1x _).mp h) (by decide +kernel)

/-- `∫ exp(1/x) (1/x - log x/x²) dx = exp(1/x) log x`: the algorithm answers yes. -/
theorem exp_inv_log_deriv_elementary (T : MixTower Kc E [lx, e1x]) (hgen : T.F 2 = ⊤) :
    HasElementaryIntegral ((((T.MP 2 (T.tr_noHom_of_ND 2 (T.nd_of_mixCert 2 cert_lx_e1x)).1).sem
      (([zero₂, ([r [1] [0, 1], r [-1] [0, 0, 1]], [one₁])], [one₂]) : Code 3) : T.F 2) : E)) :=
  (T.mixN_decides 2 hgen cert_lx_e1x _).mpr (by decide +kernel)

/-- **`∫ exp(arctan x) dx` is not elementary.** -/
theorem exp_arctan_not_elementary (T : MixTower Kc E [eat]) (hgen : T.F 1 = ⊤) :
    ¬HasElementaryIntegral (T.ts 0) := by
  rw [← val_T1 T (T.tr_noHom_of_ND 1 (T.nd_of_mixCert 1 cert_eat)).1]
  exact fun h ↦ absurd ((T.mixN_decides 1 hgen cert_eat _).mp h) (by decide +kernel)

/-- `∫ exp(arctan x)/(x² + 1) dx = exp(arctan x)`: the algorithm answers yes. -/
theorem exp_arctan_deriv_elementary (T : MixTower Kc E [eat]) (hgen : T.F 1 = ⊤) :
    HasElementaryIntegral ((((T.MP 1 (T.tr_noHom_of_ND 1 (T.nd_of_mixCert 1 cert_eat)).1).sem
      (([zero₁, r [1] [1, 0, 1]], [one₁]) : Code 2) : T.F 1) : E)) :=
  (T.mixN_decides 1 hgen cert_eat _).mpr (by decide +kernel)

/-- **`∫ exp(arctan x) log x dx` is not elementary** (`t₀ = log x`, `t₁ = exp(arctan x)`). -/
theorem exp_arctan_log_not_elementary (T : MixTower Kc E [lx, eat]) (hgen : T.F 2 = ⊤) :
    ¬HasElementaryIntegral (T.ts 0 * T.ts 1) := by
  rw [← val_T1T2 T (T.tr_noHom_of_ND 2 (T.nd_of_mixCert 2 cert_lx_eat)).1]
  exact fun h ↦ absurd ((T.mixN_decides 2 hgen cert_lx_eat _).mp h) (by decide +kernel)

/-- `∫ exp(arctan x) (1/x + log x/(x² + 1)) dx = exp(arctan x) log x`. -/
theorem exp_arctan_log_deriv_elementary (T : MixTower Kc E [lx, eat]) (hgen : T.F 2 = ⊤) :
    HasElementaryIntegral ((((T.MP 2 (T.tr_noHom_of_ND 2 (T.nd_of_mixCert 2 cert_lx_eat)).1).sem
      (([zero₂, ([r [1] [0, 1], r [1] [1, 0, 1]], [one₁])], [one₂]) : Code 3) : T.F 2) : E)) :=
  (T.mixN_decides 2 hgen cert_lx_eat _).mpr (by decide +kernel)

/-- **A degenerate pair of hyperexponentials**: `∫ t₀ t₁ dx` is not elementary. -/
theorem degenerate_pair_not_elementary (T : MixTower Kc E [e6, e6x]) (hgen : T.F 2 = ⊤) :
    ¬HasElementaryIntegral (T.ts 0 * T.ts 1) := by
  rw [← val_T1T2 T (T.tr_noHom_of_ND 2 (T.nd_of_mixCert 2 cert_e6_e6x)).1]
  exact fun h ↦ absurd ((T.mixN_decides 2 hgen cert_e6_e6x _).mp h) (by decide +kernel)

/-- `∫ (6 + 6x)/(x³ - 2) t₀ t₁ dx = t₀ t₁` for the degenerate pair. -/
theorem degenerate_pair_elementary (T : MixTower Kc E [e6, e6x]) (hgen : T.F 2 = ⊤) :
    HasElementaryIntegral ((((T.MP 2 (T.tr_noHom_of_ND 2 (T.nd_of_mixCert 2 cert_e6_e6x)).1).sem
      (([zero₂, ([zero₁, r [6, 6] [-2, 0, 0, 1]], [one₁])], [one₂]) : Code 3) : T.F 2) : E)) :=
  (T.mixN_decides 2 hgen cert_e6_e6x _).mpr (by decide +kernel)

/-- Height three: `∫ exp(arctan x) log x dx` is not elementary in
`ℚ(x, log x, eˣ, exp(arctan x))`. -/
theorem height3_hexp_not_elementary (T : MixTower Kc E [lx, ex, eat]) (hgen : T.F 3 = ⊤) :
    ¬HasElementaryIntegral ((((T.MP 3 (T.tr_noHom_of_ND 3 (T.nd_of_mixCert 3
      cert_lx_ex_eat)).1).sem (([zero₃, c3 T1], [one₃]) : Code 4) : T.F 3) : E)) :=
  fun h ↦ absurd ((T.mixN_decides 3 hgen cert_lx_ex_eat _).mp h) (by decide +kernel)

end Tower.MixN.Examples
