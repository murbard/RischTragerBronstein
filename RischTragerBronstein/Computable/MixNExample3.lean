import RischTragerBronstein.Computable.MixNDecide

/-!
# Mixed towers: a relation space of dimension three

The exponents `bᵢ = 1/(x² - 2)`, `1/(x² - 3)`, `1/(x² - 5)` (`tᵢ = exp ∫ bᵢ`) have no Hermite part:
their space of Hermite-part relations has dimension three. The tower certificate `mixCert` now
covers it: `s = (x² - 2)(x² - 3)(x² - 5)` is factored by Kronecker's method, each factor is
certified irreducible over `ℚ` (`CPoly.Kron.irredQ_sound`), and no non-zero combination of the
residues is rational at every root (`CPoly.Kron.genResCert_sound`). In `ℚ(x, t₀, t₁, t₂)`:

* `∫ t₀ t₁ t₂ dx` is **not** elementary;
* `∫ (b₀ + b₁ + b₂) t₀ t₁ t₂ dx = t₀ t₁ t₂` is.
-/

open Differential

namespace Tower.MixN.Examples3

open Tower.PrimN

def r (n d : CPoly ℚ) : Code 1 := (n, d)
def one₁ : Code 1 := r [1] [1]
def zero₁ : Code 1 := r [] [1]
def T1 : Code 2 := ([zero₁, one₁], [one₁])
def one₂ : Code 2 := ([one₁], [one₁])
def zero₂ : Code 2 := ([], [one₁])
def one₃ : Code 3 := ([one₂], [one₂])
def zero₃ : Code 3 := ([], [one₂])

/-- `tᵢ′ = tᵢ / (x² - k)`. -/
def ea2 : Kind := .exp (r [1] [-2, 0, 1])
def ea3 : Kind := .exp (r [1] [-3, 0, 1])
def ea5 : Kind := .exp (r [1] [-5, 0, 1])

/-- `t₀ t₁ t₂`. -/
def P3 : Code 4 := ([zero₃, (([zero₂, T1], [one₂]) : Code 3)], [one₃])
/-- `(b₀ + b₁ + b₂) t₀ t₁ t₂`, `b₀ + b₁ + b₂ = (3x⁴ - 20x² + 31)/((x² - 2)(x² - 3)(x² - 5))`. -/
def B3 : Code 4 := ([zero₃, (([zero₂, ([zero₁, r [31, 0, -20, 0, 3] [-30, 0, 31, 0, -10, 0, 1]],
  [one₁])], [one₂]) : Code 3)], [one₃])

set_option maxRecDepth 100000

theorem cert3 : mixCert [ea2, ea3, ea5] 3 = true := by decide +kernel

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc]

/-- **`∫ t₀ t₁ t₂ dx` is not elementary** (three hyperexponentials, relation space of dimension
three). -/
theorem three_hexp_not_elementary (T : MixTower Kc E [ea2, ea3, ea5]) (hgen : T.F 3 = ⊤) :
    ¬HasElementaryIntegral ((((T.MP 3 (T.tr_noHom_of_ND 3 (T.nd_of_mixCert 3 cert3)).1).sem P3 :
      T.F 3) : E)) :=
  fun h ↦ absurd ((T.mixN_decides 3 hgen cert3 _).mp h) (by decide +kernel)

/-- `∫ (b₀ + b₁ + b₂) t₀ t₁ t₂ dx = t₀ t₁ t₂`: the algorithm answers yes. -/
theorem three_hexp_elementary (T : MixTower Kc E [ea2, ea3, ea5]) (hgen : T.F 3 = ⊤) :
    HasElementaryIntegral ((((T.MP 3 (T.tr_noHom_of_ND 3 (T.nd_of_mixCert 3 cert3)).1).sem B3 :
      T.F 3) : E)) :=
  (T.mixN_decides 3 hgen cert3 _).mpr (by decide +kernel)

end Tower.MixN.Examples3
