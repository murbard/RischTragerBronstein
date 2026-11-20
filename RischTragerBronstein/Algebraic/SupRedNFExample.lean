import RischTragerBronstein.Algebraic.SupRedOracle
import RischTragerBronstein.Algebraic.NumField

/-!
# A cube-root example over `ℚ(ζ₃)`, decided by the kernel

On `y³ = x² + 1` (genus 1), with data in `F = ℚ(ζ₃) = NF (x² + x + 1)` (so that the fibre points
`(0, ζ₃ᵏ)` are defined) and the two-prime torsion oracle over `F`:

* `∫ ∛(x² + 1)/x dx` **is** elementary (residues `ζ₃ᵏ` at `(0, ζ₃ᵏ)`; the components are torsion);
* `∫ ∛(x² + 1) dx` is **not** elementary.
-/

open Polynomial Differential CPoly IntermediateField NFC

namespace Sup

namespace NFExample3

/-- `x² + x + 1`. -/
abbrev M3 : CPoly ℚ := [1, 1, 1]

instance : Fact (Irreducible (toPoly M3)) := ⟨Kron.irredQ_sound _ (by decide +kernel)⟩

/-- `ζ₃`. -/
abbrev θ : NF M3 := mk M3 [0, 1]

/-- `x² + 1` over `F`. -/
abbrev f3 : CPoly (NF M3) := [1, 0, 1]

lemma toPoly_f3 : CPoly.toPoly f3 = X ^ 2 + 1 := by
  simp [CPoly.toPoly]; ring

lemma natDegree_f3 : (CPoly.toPoly f3).natDegree = f3.length - 1 := by
  rw [toPoly_f3]; simp

lemma squarefree_f3 : Squarefree (CPoly.toPoly f3) := by
  rw [toPoly_f3]
  refine Polynomial.Separable.squarefree ⟨1, -(Polynomial.C (1 / 2 : NF M3)) * X, ?_⟩
  haveI : Infinite (NF M3) := Infinite.of_injective _ Nat.cast_injective
  refine Polynomial.funext fun r ↦ ?_
  simp [derivative_X_pow]
  have h2 : (2 : NF M3) ≠ 0 := two_ne_zero
  field_simp
  ring

lemma zeta3 : IsPrimitiveRoot θ 3 :=
  IsPrimitiveRoot.mk_of_lt θ (by norm_num) (by decide +kernel) fun l hl hl3 ↦ by
    interval_cases l <;> decide +kernel

/-- The torsion oracle over `F`. -/
noncomputable abbrev tors3 := torsOracle (nfRedAt (M := M3) [1, 1, 1]) [13, 19, 31] 30 f3 3

lemma tors3_spec : TorsSpecN f3 3 tors3 :=
  torsOracle_spec _ (fun p _ R h ↦ nfRedAt_valid [1, 1, 1] (by simp [CPoly.toPoly]) p R h)
    _ _ squarefree_f3 (by decide)

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma spec (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (hy : y ^ 3 = x ^ 2 + 1)
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (ι : NF M3 →+* Kc) (B B₁ : BPoly (NF M3))
    (hBn : B.length ≤ 3) (hB₁n : B₁.length ≤ 3) (hB₁0 : (toB B₁).coeff 0 = 0) {m : ℕ}
    (a b : Fin m → NF M3) (G : Fin m → BPoly (NF M3)) (hGn : ∀ i, (G i).length ≤ 3)
    (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0)
    (hbf : ∀ i, b i ^ 3 = (CPoly.toPoly f3).eval (a i)) (ans : Bool)
    (h : superLogDecide f3 3 θ tors3 B B₁ a b G = some ans) :
    ans = true ↔ HasElementaryIntegral (integrandE ι x y f3 B B₁ a G) :=
  superLogDecide_spec hC x y hx ι f3 (by norm_num) squarefree_f3 natDegree_f3 (by decide)
    (by decide) (by rw [toPoly_f3]; simp [hy]) hgen zeta3 _ tors3_spec B B₁ hBn hB₁n hB₁0 a b G
    hGn ha hb hbf ans h

/-- **`∫ ∛(x² + 1)/x dx` is elementary.** -/
theorem cbrt_over_x_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 3 = x ^ 2 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (ι : NF M3 →+* Kc) :
    HasElementaryIntegral (y / x) := by
  have := (spec hC x y hx hy hgen ι [] [] (by decide) (by decide) (by simp) ![0] ![1]
    ![[[], [1]]] (fun i ↦ by fin_cases i; decide) (fun i j _ ↦ Subsingleton.elim i j)
    (fun i ↦ by fin_cases i; exact one_ne_zero) (fun i ↦ by fin_cases i; simp [toPoly_f3]) true
    (by decide +kernel)).mp rfl
  convert this using 1
  simp [integrandE, exC, evalE_cons, evalE_X, evalE_C, CPoly.toPoly]

/-- **`∫ ∛(x² + 1) dx` is not elementary.** -/
theorem cbrt_not_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 3 = x ^ 2 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (ι : NF M3 →+* Kc) :
    ¬HasElementaryIntegral y := by
  have := spec hC x y hx hy hgen ι [[], [1]] [] (by decide) (by decide) (by simp) ![] ![] ![]
    (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0) false
    (by decide +kernel)
  simp only [Bool.false_eq_true, false_iff] at this
  convert this using 2
  simp [integrandE, exC, evalE_cons, evalE_X, evalE_C, CPoly.toPoly]

end NFExample3

end Sup
