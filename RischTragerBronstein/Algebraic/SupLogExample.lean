import RischTragerBronstein.Algebraic.SupLogOracle

/-!
# Examples of the superelliptic logarithmic-part procedure

In any differential field `E = Kc(x)(y)` with constants `Kc`, `x′ = 1`, `y² = x³ + 1`:

* `∫ √(x³+1)/x dx` **is** elementary (it is `(2/3)√(x³+1) + (1/3) log((y − 1)/(y + 1))`; the
  residue divisor has order `3` in the Jacobian);
* `∫ (√(x³+1)/x − (3/2) x/√(x³+1)) dx` is **not** elementary (same logarithmic part, but the
  remainder is a differential of the second kind that is not exact);
* `∫ dx/√(x³+1)` is **not** elementary.

All three are decided by `superLogDecide` with the search oracle `torsSearch`; the kernel runs the
procedure (`decide +kernel`).
-/

open Polynomial Differential CPoly IntermediateField

namespace Sup

/-- `ℚ` with its trivial `ℚ`-basis. -/
instance ratCoords : EllQuad.QCoords ℚ where
  dim := 1
  coord := fun _ ↦ LinearMap.id
  bvec := fun _ ↦ 1
  repr := fun z ↦ by simp

namespace LogExample

/-- `x³ + 1`. -/
def fE : CPoly ℚ := [1, 0, 0, 1]

lemma toPoly_fE : CPoly.toPoly fE = X ^ 3 + 1 := by
  simp [fE, CPoly.toPoly]; ring

lemma natDegree_fE : (CPoly.toPoly fE).natDegree = fE.length - 1 := by
  rw [toPoly_fE]; simp [fE]

lemma squarefree_fE : Squarefree (CPoly.toPoly fE) := by
  rw [toPoly_fE]
  refine Polynomial.Separable.squarefree ⟨1, -(Polynomial.C (1 / 3 : ℚ) * X), ?_⟩
  rw [derivative_add, derivative_X_pow, derivative_one, add_zero]
  have h3 : Polynomial.C (1 / 3 : ℚ) * Polynomial.C ((3 : ℕ) : ℚ) = 1 := by
    rw [← Polynomial.C_mul]; norm_num
  linear_combination (-(X ^ 3)) * h3

lemma zeta_E : IsPrimitiveRoot (-1 : ℚ) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)

variable {Kc E : Type} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma hyE {x y : E} (hy : y ^ 2 = x ^ 3 + 1) :
    y ^ 2 = aeval x ((CPoly.toPoly fE).map (algebraMap ℚ Kc)) := by
  rw [toPoly_fE]; simp [hy]

/-- The decision, instantiated. -/
lemma spec (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (hy : y ^ 2 = x ^ 3 + 1)
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (B B₁ : BPoly ℚ) (hBn : B.length ≤ 2) (hB₁n : B₁.length ≤ 2)
    (hB₁0 : (toB B₁).coeff 0 = 0) {m : ℕ} (a b : Fin m → ℚ) (G : Fin m → BPoly ℚ)
    (hGn : ∀ i, (G i).length ≤ 2) (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0)
    (hbf : ∀ i, b i ^ 2 = (CPoly.toPoly fE).eval (a i)) (ans : Bool)
    (h : superLogDecide fE 2 (-1) (torsSearch fE 2 6) B B₁ a b G = some ans) :
    ans = true ↔ HasElementaryIntegral (integrandE (algebraMap ℚ Kc) x y fE B B₁ a G) :=
  superLogDecide_spec hC x y hx (algebraMap ℚ Kc) fE (by norm_num) squarefree_fE natDegree_fE
    (by decide) (by decide) (hyE hy) hgen zeta_E _ (torsSearch_spec fE (by norm_num) 6) B B₁
    hBn hB₁n hB₁0 a b G hGn ha hb hbf ans h

/-- **`∫ √(x³+1)/x dx` is elementary.** -/
theorem sqrt_over_x_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) :
    HasElementaryIntegral (y / x) := by
  have := (spec hC x y hx hy hgen [] [] (by decide) (by decide) (by simp) ![0] ![1]
    ![[[], [1]]] (fun i ↦ by fin_cases i; decide) (fun i j _ ↦ Subsingleton.elim i j)
    (fun i ↦ by fin_cases i; norm_num) (fun i ↦ by fin_cases i; simp [toPoly_fE]) true
    (by decide +kernel)).mp rfl
  convert this using 1
  simp [integrandE, exC, evalE_cons, evalE_X, evalE_C, CPoly.toPoly]

/-- **`∫ (√(x³+1)/x − (3/2) x/√(x³+1)) dx` is not elementary.** -/
theorem sqrt_over_x_minus_not_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) :
    ¬HasElementaryIntegral (y / x - 3 / 2 * x * y / (x ^ 3 + 1)) := by
  have := spec hC x y hx hy hgen [] [[], [0, -3/2]] (by decide) (by decide) (by simp) ![0] ![1]
    ![[[], [1]]] (fun i ↦ by fin_cases i; decide) (fun i j _ ↦ Subsingleton.elim i j)
    (fun i ↦ by fin_cases i; norm_num) (fun i ↦ by fin_cases i; simp [toPoly_fE]) false
    (by decide +kernel)
  simp only [Bool.false_eq_true, false_iff] at this
  convert this using 2
  simp [integrandE, exC, evalE_cons, evalE_X, evalE_C, CPoly.toPoly, fE]
  rw [show (algebraMap Kc E) 3 = 3 from map_ofNat _ 3, show (algebraMap Kc E) 2 = 2 from map_ofNat _ 2]
  ring

/-- **`∫ dx/√(x³+1)` is not elementary.** -/
theorem inv_sqrt_not_elementary (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 1) (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) :
    ¬HasElementaryIntegral (y / (x ^ 3 + 1)) := by
  have := spec hC x y hx hy hgen [] [[], [1]] (by decide) (by decide) (by simp) ![] ![] ![]
    (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0)
    false (by decide +kernel)
  simp only [Bool.false_eq_true, false_iff] at this
  convert this using 2
  simp [integrandE, exC, evalE_cons, evalE_X, evalE_C, CPoly.toPoly, fE]
  ring

end LogExample

end Sup
