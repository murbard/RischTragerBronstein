import RischTragerBronstein.Mixed.NKExactTLVG

/-!
# Staged kernel evaluation of the exact-part tests

The kernel keeps every intermediate reduction of one `decide +kernel` check, so long computations
run out of memory. These lemmas split a test into stages: a first stage computing the data that the
next stage consumes (checked against a literal by `decide +kernel` in its own declaration), then the
next stage run on the literal.

* `exactTLVGpre`: the change of basis of `exactTLVG` (the data handed to `exactWRVLG`);
  `exactTLVG_stage`: `exactTLVG = exactTLVGpre.bind exactWRVLG`.
-/

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The first stage of `exactTLVG`: `N`, the reduced matrix and right-hand sides. -/
def exactTLVGpre (m : ℕ) (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1))))
    (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    Option (ℕ × List (List (LC (m + 1))) × List (LC (m + 1)) × List (List (LC (m + 1)))) :=
  let O1 := MOr Fc ks (m + 1)
  let N := P.length - 1
  let tm : ℕ → ℕ → LC (m + 1) := fun i j ↦ (Tc.getD i []).getD j O1.zero
  let ti : ℕ → ℕ → LC (m + 1) := fun i j ↦ (Ti.getD i []).getD j O1.zero
  if !(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || N = 0 ||
    !(prodIdC Fc ks m N tm ti && prodIdC Fc ks m N ti tm) then none else
  match dThetaC O1 P with
  | none => none
  | some dθ =>
    let mθ : ℕ → ℕ → LC (m + 1) := fun i j ↦ (dPowC O1 P dθ i).getD j O1.zero
    let Mw := (List.range N).map fun i ↦ (List.range N).map fun j ↦
      lsumC O1 ((List.range N).map fun l ↦ O1.mul (O1.add (O1.deriv (tm i l))
        (lsumC O1 ((List.range N).map fun k ↦ O1.mul (tm i k) (mθ k l)))) (ti l j))
    let cw : List (LC (m + 1)) → List (LC (m + 1)) := fun g ↦ (List.range N).map fun j ↦
      lsumC O1 ((List.range N).map fun k ↦ O1.mul (g.getD k O1.zero) (ti k j))
    some (N, Mw.map fun l ↦ l.map (redC Fc ks m), (cw f).map (redC Fc ks m),
      gs.map fun g ↦ (cw g).map (redC Fc ks m))

theorem exactTLVG_stage (m : ℕ) (η : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (r : ℕ → ℤ) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    exactTLVG Fc ks m η rde dg C Ci r P Tc Ti f gs =
      (exactTLVGpre Fc ks m P Tc Ti f gs).bind fun d ↦
        exactWRVLG Fc ks m η rde dg C Ci d.1 d.2.1 d.2.2.1 d.2.2.2 r := by
  unfold exactTLVG exactTLVGpre
  dsimp only
  split_ifs
  · rfl
  · rcases dThetaC (MOr Fc ks (m + 1)) P with _ | dθ <;> rfl

/-- Decidable equality of codes of level `1` (lists of fractions over `LC 0`). -/
instance instDecEqLC0 : DecidableEq (LC 0) :=
  inferInstanceAs (DecidableEq (List (List ℚ × List ℚ)))

instance instDecEqLCs (m : ℕ) [DecidableEq (LC m)] : DecidableEq (LC (m + 1)) :=
  inferInstanceAs (DecidableEq (List (LC m) × List (LC m)))

end Curves.MT
