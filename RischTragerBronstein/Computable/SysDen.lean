import RischTragerBronstein.Computable.SysLoop

/-!
# Coupled Risch systems: the denominator bound at a normal place (indicial equation)

For `Y′ + A Y = G` over `K(t)` with `t′ = w0 + b t`, at an irreducible `p ∈ K[t]` where `A` has at
most a simple pole (`A = A₀ / p`): if `Y = Z / pᵉ` with `p ∤ Z`, multiplying by `pᵉ⁺¹` gives
`p Z′ + (A₀ − e p′) Z = pᵉ⁺¹ G`. Hence either `G` has a pole of order `≥ e + 1` at `p`, or `e` is a
root of the **indicial equation** `p ∣ det(A₀ − e p′ I)` (`sys_den_indicial`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K] (w0 b : K) {n : ℕ}

/-- **The indicial equation at a simple pole.** If `p Z′ + (A₀ − e p′) Z ≡ 0 (mod p)` with `p ∤ Z`,
then `p ∣ det(A₀ − e p′ I)`. -/
theorem sys_den_indicial (p : K[X]) (hp : Irreducible p) (Z : Fin n → K[X]) (hZ : ∃ i, ¬ p ∣ Z i)
    (e : ℕ) (A0 : Fin n → Fin n → K[X])
    (hdiv : ∀ i, p ∣ p * DzL w0 b (Z i) + ∑ j, (A0 i j - if i = j then (e : K[X]) * DzL w0 b p else 0) * Z j) :
    p ∣ (Matrix.of fun i j ↦ A0 i j - if i = j then (e : K[X]) * DzL w0 b p else 0).det := by
  classical
  haveI := Fact.mk hp
  set φ : K[X] →+* AdjoinRoot p := AdjoinRoot.mk p with hφ
  set Mt : Matrix (Fin n) (Fin n) K[X] :=
    Matrix.of fun i j ↦ A0 i j - if i = j then (e : K[X]) * DzL w0 b p else 0 with hMt
  set z : Fin n → AdjoinRoot p := fun i ↦ φ (Z i) with hz
  have hz0 : z ≠ 0 := by
    obtain ⟨i, hi⟩ := hZ
    intro h
    apply hi
    have := congrFun h i
    simpa [hz, hφ, AdjoinRoot.mk_eq_zero] using this
  have hker : (Mt.map φ).mulVec z = 0 := by
    funext i
    have h := hdiv i
    rw [← AdjoinRoot.mk_eq_zero] at h
    simp only [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, zero_add, map_sum] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hMt, Matrix.of_apply, hz, Pi.zero_apply]
    rw [← h]
  have hdet : (Mt.map φ).det = 0 := (Matrix.exists_mulVec_eq_zero_iff).mp ⟨z, hz0, hker⟩
  have e : (Mt.map φ).det = φ Mt.det := (RingHom.map_det φ Mt).symm
  rw [e] at hdet
  exact AdjoinRoot.mk_eq_zero.mp hdet

end Tower.Sys
