import RischTragerBronstein.Computable.GEuclidDegree

/-!
# Reducing a fraction of polynomial codes

`GPoly.redFrac O (p, d)` divides `p` and `d` by their executable gcd when both divisions are exact
(checked), then by the leading coefficient of the new denominator (so that coefficients stay
small), and otherwise leaves the fraction unchanged. `redFrac_spec`: in any model, the reduced
fraction has the same value (`p' d = p d'`, `d' ≠ 0`).
-/

open Polynomial

namespace GPoly

variable {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

variable (O) in
/-- Divide numerator and denominator by their gcd (when exact). -/
def redFrac (q : GPoly α × GPoly α) : GPoly α × GPoly α :=
  if isZero O q.2 then q else
    let g := (egcd O q.1 q.2).1
    let a := divMod O q.1 g
    let b := divMod O q.2 g
    if isZero O a.2 && isZero O b.2 && !isZero O b.1 then
      let c := O.inv (lead O (trim O b.1))
      (smul O c a.1, smul O c b.1)
    else q

/-- **The reduced fraction has the same value.** -/
theorem redFrac_spec (q : GPoly α × GPoly α) (hq : toPoly M q.2 ≠ 0) :
    toPoly M (redFrac O q).1 * toPoly M q.2 = toPoly M q.1 * toPoly M (redFrac O q).2 ∧
      toPoly M (redFrac O q).2 ≠ 0 := by
  unfold redFrac
  have hz : isZero O q.2 = false := by
    cases h : isZero O q.2
    · rfl
    · exact absurd ((isZero_iff M _).mp h) hq
  rw [if_neg (by simp [hz])]
  dsimp only
  split_ifs with hc
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨ha, hb⟩, hb1⟩ := hc
    have ha0 := (isZero_iff M _).mp ha
    have hb0 := (isZero_iff M _).mp hb
    have hsa := divMod_spec M q.1 (egcd O q.1 q.2).1
    have hsb := divMod_spec M q.2 (egcd O q.1 q.2).1
    rw [ha0, add_zero] at hsa
    rw [hb0, add_zero] at hsb
    have hbne : toPoly M (divMod O q.2 (egcd O q.1 q.2).1).1 ≠ 0 := fun h0 ↦ by
      rw [(isZero_iff M _).mpr h0] at hb1; exact Bool.noConfusion hb1
    have hc : M.sem (O.inv (lead O (trim O (divMod O q.2 (egcd O q.1 q.2).1).1))) ≠ 0 := by
      rw [M.sem_inv, ← leadingCoeff_toPoly M hbne]
      exact inv_ne_zero (leadingCoeff_ne_zero.mpr hbne)
    simp only [toPoly_smul]
    refine ⟨?_, mul_ne_zero (C_ne_zero.mpr hc) hbne⟩
    rw [hsa, hsb]; ring
  · exact ⟨by ring, hq⟩

end GPoly
