import RischTragerBronstein.Computable.GWF
import RischTragerBronstein.Mixed.KXCertBridge

/-!
# Well-formed codes are closed under the curve operations

`WF r`: the fraction `r` has a non-zero denominator. The operations of `ℚ(x)` (`xOps`, normalized by
`redFrac`) preserve it (`pres_xOps`), hence (`GPoly.pres_algExt`) so do the operations of the
function field of a linear base curve (`pres_curveOps`); `codeOKb` is exactly `AllW WF`. So every
code built by the operations from well-formed codes is well formed — e.g. `kxD` (`codeOKb_kxD`).
-/

open Polynomial

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

/-- A fraction with a non-zero denominator. -/
def WF (r : GFrac ℚ) : Prop := CPoly.isZero r.2 = false

lemma WF_iff (r : GFrac ℚ) : WF r ↔ CPoly.toPoly r.2 ≠ 0 := by
  rw [WF, Bool.eq_false_iff, Ne, CPoly.isZero_iff]

section Q

local instance instDiffQ : Differential ℚ := ⟨0⟩

/-- `ℚ` as its own computable model. -/
noncomputable abbrev M0 : CField ℚ ℚ (COps.ofDecidableField ℚ) :=
  CField.ofDecidableField ℚ (fun _ ↦ rfl)

lemma toPoly_M0 : ∀ p : GPoly ℚ, GPoly.toPoly M0 p = CPoly.toPoly p
  | [] => rfl
  | a :: p => by simp [GPoly.toPoly_cons, CPoly.toPoly, toPoly_M0 p]; rfl

lemma isZero_M0 (p : GPoly ℚ) : GPoly.isZero (COps.ofDecidableField ℚ) p = CPoly.isZero p := rfl

lemma isZero_mul (p q : GPoly ℚ) (hp : CPoly.isZero p = false) (hq : CPoly.isZero q = false) :
    CPoly.isZero (GPoly.mul (COps.ofDecidableField ℚ) p q) = false := by
  rw [← isZero_M0, Bool.eq_false_iff, Ne, GPoly.isZero_iff M0, GPoly.toPoly_mul, toPoly_M0,
    toPoly_M0]
  rw [Bool.eq_false_iff, Ne, CPoly.isZero_iff] at hp hq
  exact mul_ne_zero hp hq

lemma isZero_smul (c : ℚ) (hc : c ≠ 0) (p : GPoly ℚ) (hp : CPoly.isZero p = false) :
    CPoly.isZero (GPoly.smul (COps.ofDecidableField ℚ) c p) = false := by
  rw [← isZero_M0, Bool.eq_false_iff, Ne, GPoly.isZero_iff M0, GPoly.toPoly_smul, toPoly_M0]
  rw [Bool.eq_false_iff, Ne, CPoly.isZero_iff] at hp
  exact mul_ne_zero (C_ne_zero.mpr hc) hp

/-- `redFrac` keeps a non-zero denominator. -/
lemma WF_redFrac (q : GFrac ℚ) (hq : WF q) : WF (GPoly.redFrac (COps.ofDecidableField ℚ) q) := by
  unfold GPoly.redFrac
  split_ifs with h1
  · exact hq
  · dsimp only
    split_ifs with h2
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
      show CPoly.isZero (GPoly.smul _ _ _) = false
      refine isZero_smul _ ?_ _ h2.2
      have hne := GPoly.lead_trim_ne (O := COps.ofDecidableField ℚ) _
        (GPoly.trim_ne_nil_of_isZero _ (by rw [isZero_M0]; exact h2.2))
      simp only [COps.ofDecidableField, decide_eq_false_iff_not] at hne ⊢
      exact inv_ne_zero hne
    · exact hq

/-- **`ℚ(x)` operations preserve well-formedness.** -/
theorem pres_xOps : (xOps).Pres WF where
  zero := by show CPoly.isZero [1] = false; decide
  one := by show CPoly.isZero [1] = false; decide
  add a b ha hb := by
    refine WF_redFrac _ ?_
    show WF (if GPoly.isZero _ a.2 then b else if GPoly.isZero _ b.2 then a else _)
    split_ifs
    · exact hb
    · exact ha
    · exact isZero_mul _ _ ha hb
  neg a ha := WF_redFrac _ ha
  mul a b ha hb := WF_redFrac _ (isZero_mul _ _ ha hb)
  inv a _ hz := by
    refine WF_redFrac _ ?_
    show CPoly.isZero a.1 = false
    have : (GPoly.isZero (COps.ofDecidableField ℚ) a.1 || GPoly.isZero _ a.2) = false := hz
    simp only [Bool.or_eq_false_iff] at this
    rw [← isZero_M0]; exact this.1
  deriv a ha := WF_redFrac _ (isZero_mul _ _ ha ha)
  natCast n := by show CPoly.isZero [1] = false; decide

end Q

/-- `codeOKb` is `AllW WF`. -/
lemma codeOKb_iff (b : LC 0) : codeOKb b = true ↔ GPoly.AllW WF b := by
  unfold codeOKb GPoly.AllW WF
  rw [List.all_eq_true]
  simp

/-- **The curve operations preserve well-formedness** (linear base). -/
theorem pres_curveOps (c0f : CPoly ℚ) : (curveOps [c0f, [1]]).Pres (GPoly.AllW WF) := by
  have hP : GPoly.AllW WF (curveCodes [c0f, [1]]) := by
    intro r hr
    simp only [curveCodes, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl <;> (show CPoly.isZero [1] = false; decide)
  have hnz : GPoly.isZero xOps (curveCodes [c0f, [1]]) = false := by
    simp only [curveCodes, List.map_cons, List.map_nil, GPoly.isZero, List.all_cons, List.all_nil,
      Bool.and_true]
    have : xOps.isZero ([1], [1]) = false := by decide
    rw [this, Bool.and_false]
  exact GPoly.pres_algExt pres_xOps _ hP
    (pres_xOps.inv _ (GPoly.W_lead pres_xOps _ (GPoly.allW_trim _ hP))
      (GPoly.lead_trim_ne _ (GPoly.trim_ne_nil_of_isZero _ hnz)))

/-- **`kxD` is well formed** when `g` and the poles are. -/
lemma codeOKb_kxD (c0f : CPoly ℚ) (ks : (m : ℕ) → KindC m) (g : LC 0) (cs : List (LC 0))
    (hg : codeOKb g = true) (hcs : ∀ c ∈ cs, codeOKb c = true) (q : ℕ) :
    codeOKb (kxD [c0f, [1]] ks 0 g cs q) = true := by
  have hP := pres_curveOps c0f
  have hq : GPoly.AllW WF (kqC [c0f, [1]] ks 0 cs q) := by
    rw [← codeOKb_iff]
    unfold kqC
    rcases Nat.lt_or_ge q cs.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact hcs _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ h]; rfl
  rw [codeOKb_iff]
  unfold kxD subC
  exact hP.add _ _ (hP.mul _ _ (hP.deriv _ ((codeOKb_iff g).mp hg)) hq) (hP.neg _ (hP.deriv _ hq))

end Curves.MT
