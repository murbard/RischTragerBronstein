import RischTragerBronstein.Torsion.Emit

/-!
# A front end for integrands on curves over `ℚ`

`curveProbQ Fc A D`: the integrand `A(x, y)/D(x)` on `F(x, y) = 0` (`F` monic in `y`), with the
smallest admissible weight at infinity (`autoK`). `decideCurveQ` runs the whole decision
(`decideLoop` from `ℚ`, fast root finder, primes chosen by `autoPairs`, integral-basis weight
`autoKI`), and `emitCurveQ` produces the Lean file of certificates for its answer.
**`decideCurveQ_spec`**: every answer is correct.
-/

namespace Curves

open CPoly Sup

/-- The smallest weight `k` with `deg Fⱼ ≤ k` and `deg Fⱼ + k j ≤ k n` (the conditions of
`CurveProb.valid` on the curve). -/
def autoK (Fc : BPoly ℚ) : ℕ :=
  let n := Fc.length - 1
  ((List.range 256).find? fun k ↦
    (List.range Fc.length).all fun j ↦ decide ((Fc.getD j []).length ≤ k + 1) &&
      decide ((Fc.getD j []).length + k * j ≤ k * n + 1)).getD 0

/-- The smallest weight for the integral basis above infinity (`InvOK k (k n) 0 F`). -/
def autoKI (Fc : BPoly ℚ) : ℕ :=
  let n := Fc.length - 1
  ((List.range 256).find? fun k ↦ 0 < k && invOKb k (k * n) Fc).getD 1

/-- The integrand `A(x, y)/D(x)` on `F(x, y) = 0`. -/
def curveProbQ (Fc A : BPoly ℚ) (D : CPoly ℚ) : CurveProb ℚ :=
  ⟨Fc, Fc.length - 1, autoK Fc, A, D, [], ⟨1, [], 0⟩⟩

theorem irredQ_X : Kron.irredQ [0, 1] = true := by decide +kernel

/-- **The decision** for an integrand over `ℚ` (search bound `fuel` for the number fields). -/
def decideCurveQ (Fc A : BPoly ℚ) (D : CPoly ℚ) (fuel : ℕ := 4) : Option Bool :=
  decideLoop (curveProbQ Fc A D) true (autoKI Fc) [0, 8, 16] 2 10 16 10 12 [] fuel [0, 1] irredQ_X

/-- **The certificate file** for the answer (`none` if the search fails). -/
def emitCurveQ (name : String) (Fc A : BPoly ℚ) (D : CPoly ℚ) (fuel : ℕ := 4) : Option String :=
  emitLoop (curveProbQ Fc A D) name true (autoKI Fc) [0, 8, 16] 2 10 16 10 12 [] fuel [0, 1]
    irredQ_X

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

open IntermediateField Differential Polynomial in
/-- **Soundness of the front end.** -/
theorem decideCurveQ_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (Fc A : BPoly ℚ) (D : CPoly ℚ)
    (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc))) (fuel : ℕ) (b : Bool)
    (h : decideCurveQ Fc A D fuel = some b) :
    HasElementaryIntegral ((S.fE (curveProbQ Fc A D) (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) ↔
      b = true :=
  decideLoop_spec hC S hx hgen (curveProbQ Fc A D) hSF true (autoKI Fc) [0, 8, 16] 2 10 16 10 12 []
    fuel [0, 1] irredQ_X b h

end Main

end Curves
