import RischTragerBronstein.Mixed.NKStageC
import RischTragerBronstein.Mixed.NKExactC2
import RischTragerBronstein.Mixed.NKExactTL

/-!
# Staged kernel evaluation of `exactC2` and `exactTL`

The first stage of each test as data: `N`, the rows `A₀ j i`, the denominators `q`, `h`, the
right-hand sides (`exactC2sys`, `exactTLsys`), and `exactC2_stage`, `exactTL_stage`: the test is the
solver run on that data. The solver stages are those of `Mixed/NKStageC`.
-/

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The data of a system: `N`, rows of `A₀`, `q`, `h`, rows of the right-hand sides. -/
abbrev SysData (m : ℕ) : Type :=
  ℕ × List (List (GPoly (LC m))) × GPoly (LC m) × GPoly (LC m) × List (List (GPoly (LC m)))

/-- Run a solver on system data. -/
def runSys {m : ℕ} (solve : SysSolver m) (d : SysData m) : Option Bool :=
  exactCans (solve d.1 (matFn d.2.1 []) d.2.2.1 d.2.2.2.1 (d.2.2.2.2.map fun l ↦ listFn l []))

lemma matFn_rows {m N : ℕ} (g : ℕ → ℕ → GPoly (LC m)) :
    (matFn ((List.range N).map fun j ↦ (List.range N).map fun i ↦ g j i) [] :
      Fin N → Fin N → GPoly (LC m)) = fun (j i : Fin N) ↦ g j i := by
  funext j i; simp [matFn, List.getD_eq_getElem?_getD, j.2, i.2]

lemma listFn_row {m N : ℕ} (g : ℕ → GPoly (LC m)) :
    (listFn ((List.range N).map g) [] : Fin N → GPoly (LC m)) = fun (j : Fin N) ↦ g j := by
  funext j; simp [listFn, List.getD_eq_getElem?_getD, j.2]

lemma listFn_rows {β : Type} {m N : ℕ} (L : List β) (c : β → ℕ → GPoly (LC m)) :
    ((L.map fun g ↦ (List.range N).map (c g)).map fun l ↦ (listFn l [] : Fin N → GPoly (LC m))) =
      L.map fun g (j : Fin N) ↦ c g j := by
  rw [List.map_map]
  exact List.map_congr_left fun g _ ↦ listFn_row (c g)

/-- The first stage of `exactC2`. -/
def exactC2sys (m : ℕ) (P : GPoly (LC (m + 1))) (f g : List (LC (m + 1))) : Option (SysData m) :=
  let O1 := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
  let O := MO Fc ks m
  let N := P.length - 1
  if !(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || N = 0 then none else
  match dThetaC O1 P with
  | none => none
  | some dθ =>
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (dPowC O1 P dθ i).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten ++ f ++ g
    let q := lcmGL O (ent.map Prod.snd)
    let cofs := ent.map fun c ↦ cofC O q c.2
    if !(cofs.all Prod.fst) then none else
    let num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2
    some (N, (List.range N).map (fun j ↦ (List.range N).map fun i ↦
      num ((M.getD i []).getD j O1.zero)), q, q,
      [(List.range N).map fun j ↦ num (f.getD j O1.zero),
       (List.range N).map fun j ↦ num (g.getD j O1.zero)])

theorem exactC2_stage (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f g : List (LC (m + 1))) :
    exactC2 Fc ks m η lim P f g =
      (exactC2sys Fc ks m P f g).bind (runSys (primSysC Fc ks m η lim)) := by
  unfold exactC2 exactC2sys
  dsimp only
  split_ifs with h1
  · rfl
  · rcases dThetaC ((MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))) P with _ | dθ
    · rfl
    · dsimp only
      split_ifs with h2
      · rfl
      · simp only [Option.bind_some, runSys, exactCans, List.map_cons, List.map_nil]
        rw [matFn_rows, listFn_row, listFn_row]
        split <;> simp_all

/-- The first stage of `exactTL`. -/
def exactTLsys (m : ℕ) (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1))))
    (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) : Option (SysData m) :=
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
    let Mc := (List.range N).map fun i ↦ (List.range N).map fun j ↦
      lsumC O1 ((List.range N).map fun l ↦ O1.mul (O1.add (O1.deriv (tm i l))
        (lsumC O1 ((List.range N).map fun k ↦ O1.mul (tm i k) (mθ k l)))) (ti l j))
    let cw : List (LC (m + 1)) → List (LC (m + 1)) := fun g ↦ (List.range N).map fun j ↦
      lsumC O1 ((List.range N).map fun k ↦ O1.mul (g.getD k O1.zero) (ti k j))
    let f' := cw f
    let gs' := gs.map cw
    let O1' := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
    let O := MO Fc ks m
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (Mc.getD i []).getD j O1'.zero
    let ent : List (LC (m + 1)) := M.flatten
    let q := lcmGL O (ent.map Prod.snd)
    let hq := lcmGL O ((f' ++ gs'.flatten).map Prod.snd)
    if !((ent.map fun c ↦ cofC O q c.2).all Prod.fst &&
        ((f' ++ gs'.flatten).map fun c ↦ cofC O hq c.2).all Prod.fst) then none else
    let num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2
    let numF : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O hq c.2).2
    some (N, (List.range N).map (fun j ↦ (List.range N).map fun i ↦
      num ((M.getD i []).getD j O1'.zero)), q, hq,
      (f' :: gs').map fun g ↦ (List.range N).map fun j ↦ numF (g.getD j O1'.zero))

theorem exactTL_stage (m : ℕ) (solve : SysSolver m) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    exactTL Fc ks m solve P Tc Ti f gs = (exactTLsys Fc ks m P Tc Ti f gs).bind (runSys solve) := by
  unfold exactTL exactTLsys exactWL
  dsimp only
  split_ifs with h1 h2
  · rfl
  · exfalso; simp [h2] at h1
  · rcases dThetaC (MOr Fc ks (m + 1)) P with _ | dθ
    · rfl
    · dsimp only
      split_ifs with h3
      · rfl
      · simp only [Option.bind_some, runSys, exactCans]
        rw [matFn_rows, listFn_rows]
        generalize solve _ _ _ _ _ = o
        cases o <;> rfl

end Curves.MT
