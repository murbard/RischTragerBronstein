import RischTragerBronstein.Computable.KronComplete

/-!
# A fast irreducibility test over `ℚ`

`irredQF` is `irredQ` with the exhaustive Kronecker search for a factor of degree `e` skipped
whenever the factor degrees modulo some prime exclude `e` (`DegCert.degExcluded_sound`,
`noFactor_complete`). `irredQ_eq_irredQF` makes it the compiled code of `irredQ`.
-/

open Polynomial

namespace CPoly

namespace Kron

/-- `irredQ`, trying the degree certificates first. -/
def irredQF (F : CPoly ℚ) : Bool :=
  F.all (fun q ↦ q.den == 1) && gcdL (F.map Rat.num) == 1 && decide (1 ≤ degC F) &&
    (let Ss := DegCert.degSets F
     (List.range (degC F / 2)).all fun e ↦ DegCert.degExcluded Ss (e + 1) || noFactor F (e + 1))

@[csimp] theorem irredQ_eq_irredQF : @irredQ = @irredQF := by
  funext F
  unfold irredQ irredQF
  dsimp only
  by_cases h1 : 1 ≤ degC F
  · have hF0 : toPoly F ≠ 0 := fun h0 ↦ by
      have : trim F = [] := (trim_eq_nil_iff F).mpr h0
      rw [degC, this] at h1
      simp at h1
    congr 1
    congr 1
    funext e
    by_cases hx : DegCert.degExcluded (DegCert.degSets F) (e + 1) = true
    · rw [hx, Bool.true_or]
      exact noFactor_complete F hF0 (e + 1) fun g hg ↦ DegCert.degExcluded_sound F (e + 1) hx g hg
    · rw [Bool.not_eq_true] at hx
      rw [hx, Bool.false_or]
  · simp [h1]

end Kron

end CPoly
