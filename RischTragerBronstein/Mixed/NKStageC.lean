import RischTragerBronstein.Mixed.NKStage
import RischTragerBronstein.Mixed.NKExactCodes

/-!
# Staged kernel evaluation of `exactC` (primitive level)

* `exactCsys`: the system that `exactC` hands to `primSysC` (as data: `N`, the matrix rows, `q`,
  the right-hand side); `exactC_stage`: `exactC = exactCsys.bind (primSysC …)`.
* `primSysCB`: `primSysC` after the indicial bound `B`; `primSysC_stage`:
  `primSysC = (monic check) (indBound2 …).bind (primSysCB …)`.

Each stage can then be checked by `decide +kernel` against literal data in its own declaration.
-/

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The first stage of `exactC`: `N`, the rows `A₀ j i`, the denominator `q`, the right-hand side. -/
def exactCsys (m : ℕ) (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) :
    Option (ℕ × List (List (GPoly (LC m))) × GPoly (LC m) × List (GPoly (LC m))) :=
  let O1 := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
  let O := MO Fc ks m
  let N := P.length - 1
  if !(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || N = 0 then none else
  match dThetaC O1 P with
  | none => none
  | some dθ =>
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (dPowC O1 P dθ i).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten ++ f
    let q := lcmGL O (ent.map Prod.snd)
    let cofs := ent.map fun c ↦ cofC O q c.2
    if !(cofs.all Prod.fst) then none else
    let num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2
    some (N, (List.range N).map (fun j ↦ (List.range N).map fun i ↦
      num ((M.getD i []).getD j O1.zero)), q, (List.range N).map fun j ↦ num (f.getD j O1.zero))

/-- The answer of `exactC` read off a solver output. -/
def exactCans {m n : ℕ} (o : Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m))))) :
    Option Bool :=
  o.map fun r ↦ r.2.any fun b ↦ b.1.getD 0 0 != 0

theorem exactC_stage (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) :
    exactC Fc ks m η lim P f = (exactCsys Fc ks m P f).bind fun d ↦
      exactCans (primSysC Fc ks m η lim d.1 (matFn d.2.1 []) d.2.2.1 d.2.2.1
        [listFn d.2.2.2 []]) := by
  unfold exactC exactCsys
  dsimp only
  split_ifs with h1
  · rfl
  · rcases dThetaC ((MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))) P with _ | dθ
    · rfl
    · dsimp only
      split_ifs with h2
      · rfl
      · simp only [Option.bind_some, exactCans]
        have hA : ∀ (N : ℕ) (g : ℕ → ℕ → GPoly (LC m)),
            (matFn ((List.range N).map fun j ↦ (List.range N).map fun i ↦ g j i) [] :
              Fin N → Fin N → GPoly (LC m)) = fun (j i : Fin N) ↦ g j i := by
          intro N g; funext j i
          simp [matFn, List.getD_eq_getElem?_getD, j.2, i.2]
        have hG : ∀ (N : ℕ) (g : ℕ → GPoly (LC m)),
            (listFn ((List.range N).map g) [] : Fin N → GPoly (LC m)) = fun (j : Fin N) ↦ g j := by
          intro N g; funext j
          simp [listFn, List.getD_eq_getElem?_getD, j.2]
        rw [hA, hG]
        split <;> simp_all

/-- `primSysC` after the indicial bound `B`. -/
def primSysCB (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))
    (B : ℕ) : Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))) :=
  let O := MO Fc ks m
  let cst := mcst Fc ks m
  let W := wSys Fc ks m η n A0 q h G0 B
  let δ := degG O W.a
  let la := O.inv (leadG O W.a)
  let PA : Fin n → Fin n → LC m := fun i j ↦ if i = j then la else O.zero
  let β : Fin n → Fin n → LC m := vecM fun i ↦ vecM fun j ↦
    O.mul la ((W.BW i j).getD (δ - 1) O.zero)
  let okB := (List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
    decide ((GPoly.trim O (W.BW i j)).length ≤ δ)
  if !okB then none else
  match specBound2 Fc ks m n lim η β with
  | none => none
  | some Bs =>
    let Ncl := (W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0
    let N' := max Bs (Ncl - (δ - 1))
    some (W.Den, polySysC O η O.zero (fun i j ↦ if i = j then W.a else []) W.BW cst W.Cl δ false
      PA PA (fun _ ws ↦ vecLim O cst lim ws) (mrel Fc ks m) (N' + 1))

theorem primSysC_stage (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))
    (hmon : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) h) = true) :
    primSysC Fc ks m η lim n A0 q h G0 =
      (indBound2 Fc ks m (degG (MO Fc ks m) q) n q (DzLC (MO Fc ks m) η (MO Fc ks m).zero q)
        A0).bind (primSysCB Fc ks m η lim n A0 q h G0) := by
  unfold primSysC
  dsimp only
  rw [hmon]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rcases indBound2 Fc ks m (degG (MO Fc ks m) q) n q (DzLC (MO Fc ks m) η (MO Fc ks m).zero q)
    A0 with _ | B <;> rfl

/-- `primSysCB` once the system `W` is computed. -/
def primSysCW (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (W : WSys m n) : Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))) :=
  let O := MO Fc ks m
  let cst := mcst Fc ks m
  let δ := degG O W.a
  let la := O.inv (leadG O W.a)
  let PA : Fin n → Fin n → LC m := fun i j ↦ if i = j then la else O.zero
  let β : Fin n → Fin n → LC m := vecM fun i ↦ vecM fun j ↦
    O.mul la ((W.BW i j).getD (δ - 1) O.zero)
  let okB := (List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
    decide ((GPoly.trim O (W.BW i j)).length ≤ δ)
  if !okB then none else
  match specBound2 Fc ks m n lim η β with
  | none => none
  | some Bs =>
    let Ncl := (W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0
    let N' := max Bs (Ncl - (δ - 1))
    some (W.Den, polySysC O η O.zero (fun i j ↦ if i = j then W.a else []) W.BW cst W.Cl δ false
      PA PA (fun _ ws ↦ vecLim O cst lim ws) (mrel Fc ks m) (N' + 1))

theorem primSysCB_eq (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))
    (B : ℕ) : primSysCB Fc ks m η lim n A0 q h G0 B =
      primSysCW Fc ks m η lim n (wSys Fc ks m η n A0 q h G0 B) := rfl

/-- The β matrix of `primSysCW` (the input of `specBound2`). -/
def betaW (m n : ℕ) (W : WSys m n) : Fin n → Fin n → LC m :=
  vecM fun i ↦ vecM fun j ↦ (MO Fc ks m).mul ((MO Fc ks m).inv (leadG (MO Fc ks m) W.a))
    ((W.BW i j).getD (degG (MO Fc ks m) W.a - 1) (MO Fc ks m).zero)

/-- The `okB` check of `primSysCW`. -/
def okBW (m n : ℕ) (W : WSys m n) : Bool :=
  (List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
    decide ((GPoly.trim (MO Fc ks m) (W.BW i j)).length ≤ degG (MO Fc ks m) W.a)

theorem primSysCW_eq (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (W : WSys m n) (hok : okBW Fc ks m n W = true) (Bs : ℕ)
    (hBs : specBound2 Fc ks m n lim η (betaW Fc ks m n W) = some Bs) :
    primSysCW Fc ks m η lim n W = some (W.Den, polySysC (MO Fc ks m) η (MO Fc ks m).zero
      (fun i j ↦ if i = j then W.a else []) W.BW (mcst Fc ks m) W.Cl (degG (MO Fc ks m) W.a) false
      (fun i j ↦ if i = j then (MO Fc ks m).inv (leadG (MO Fc ks m) W.a) else (MO Fc ks m).zero)
      (fun i j ↦ if i = j then (MO Fc ks m).inv (leadG (MO Fc ks m) W.a) else (MO Fc ks m).zero)
      (fun _ ws ↦ vecLim (MO Fc ks m) (mcst Fc ks m) lim ws) (mrel Fc ks m)
      (max Bs ((W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0 -
        (degG (MO Fc ks m) W.a - 1)) + 1)) := by
  unfold primSysCW
  unfold okBW at hok
  unfold betaW at hBs
  dsimp only
  rw [hok]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hBs]

end Curves.MT

namespace Tower.Sys

open Tower.NestP Tower.NestM

variable {α : Type} (O : COps α) {n : ℕ} (w0 b : α) (A B : Fin n → Fin n → GPoly α)
  (cst : ℚ → α) (Cl : List (Fin n → GPoly α)) (δ : ℕ)

/-- A basis read from data. -/
def toFns (L : List (List ℚ × List (GPoly α))) : List (List ℚ × (Fin n → GPoly α)) :=
  L.map fun p ↦ (p.1, listFn p.2 [])

/-- A basis as data. -/
def toDat (X : List (List ℚ × (Fin n → GPoly α))) : List (List ℚ × List (GPoly α)) :=
  X.map fun p ↦ (p.1, matL p.2)

lemma toFns_toDat (X : List (List ℚ × (Fin n → GPoly α))) : toFns (toDat X) = X := by
  simp only [toFns, toDat, List.map_map]
  conv_rhs => rw [← List.map_id X]
  exact List.map_congr_left fun p _ ↦ by simp [listFn_matL]

/-- The final phase of `polySysC` (after the coefficient loop). -/
def polySysFin (rel : List α → List (List ℚ)) (Bs : List (List ℚ × (Fin n → GPoly α))) :
    List (List ℚ × (Fin n → GPoly α)) :=
  let Rs := residsC O w0 b A B cst Cl Bs
  let Qd := residLen Rs
  let U := relRun O cst rel Bs.length (residVals O Rs Qd) (n * Qd)
  U.map fun u ↦ (vcomb Cl.length u (Bs.map Prod.fst), vecM fun i ↦
    sumC O (List.range Bs.length) fun l ↦
      GPoly.smul O (cst (u.getD l 0)) ((Bs.getD l ([], fun _ ↦ [])).2 i))

theorem polySysC_eq (alg : Bool) (PA PB : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α)))
    (rel : List α → List (List ℚ)) (N : ℕ) :
    polySysC O w0 b A B cst Cl δ alg PA PB lowerC rel N =
      polySysFin O w0 b A B cst Cl rel (loopC O w0 b A B cst Cl δ alg PA PB lowerC N
        (initC Cl.length)) := rfl

theorem loopC_succ_diff (PA PB : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α))) (k : ℕ)
    (Bs : List (List ℚ × (Fin n → GPoly α))) :
    loopC O w0 b A B cst Cl δ false PA PB lowerC (k + 1) Bs =
      loopC O w0 b A B cst Cl δ false PA PB lowerC k (stepDiffC O w0 b A B cst Cl δ PA lowerC k Bs) :=
  rfl

/-- One staged step: if the data of the step from `S` is `S'`, the loop continues from `S'`. -/
theorem loopC_kstage (PA PB : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α))) (k : ℕ)
    (S S' : List (List ℚ × List (GPoly α)))
    (h : toDat (stepDiffC O w0 b A B cst Cl δ PA lowerC k (toFns S)) = S') :
    loopC O w0 b A B cst Cl δ false PA PB lowerC (k + 1) (toFns S) =
      loopC O w0 b A B cst Cl δ false PA PB lowerC k (toFns S') := by
  rw [loopC_succ_diff, ← h, toFns_toDat]

theorem loopC_zero' (alg : Bool) (PA PB : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α)))
    (Bs : List (List ℚ × (Fin n → GPoly α))) :
    loopC O w0 b A B cst Cl δ alg PA PB lowerC 0 Bs = Bs := rfl

theorem initC_stage (L : ℕ) (S : List (List ℚ × List (GPoly α)))
    (h : toDat (initC (n := n) (α := α) L) = S) : initC L = toFns (n := n) S := by
  rw [← h, toFns_toDat]

/-- `stepDiffC` with the right-hand sides `rkL` supplied as data. -/
def stepDiffR (PA : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α))) (k : ℕ)
    (Bs : List (List ℚ × (Fin n → GPoly α))) (R : List (List α)) :
    List (List ℚ × (Fin n → GPoly α)) :=
  ((lowerC k ((R.map fun r ↦ mvL O PA r).map fun l ↦ listFn l O.zero)).map fun r ↦
    (vcomb Cl.length r.1 (Bs.map Prod.fst), diffNew O cst k Bs r)).map fun p ↦ (p.1, listFn p.2 [])

theorem stepDiffC_R (PA : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α))) (k : ℕ)
    (Bs : List (List ℚ × (Fin n → GPoly α))) :
    stepDiffC O w0 b A B cst Cl δ PA lowerC k Bs =
      stepDiffR O cst Cl PA lowerC k Bs (Bs.map (rkL O w0 b A B cst Cl δ k)) := by
  unfold stepDiffC stepDiffR
  rw [List.map_map (g := fun r ↦ mvL O PA r)]
  rfl

/-- One staged step with the right-hand sides checked separately. -/
theorem loopC_kstageR (PA PB : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α))) (k : ℕ)
    (S S' : List (List ℚ × List (GPoly α))) (R : List (List α))
    (hR : (toFns S).map (rkL O w0 b A B cst Cl δ k) = R)
    (h : toDat (stepDiffR O cst Cl PA lowerC k (toFns S) R) = S') :
    loopC O w0 b A B cst Cl δ false PA PB lowerC (k + 1) (toFns S) =
      loopC O w0 b A B cst Cl δ false PA PB lowerC k (toFns S') := by
  rw [loopC_succ_diff, stepDiffC_R, hR, ← h, toFns_toDat]

/-- The final phase with the residuals supplied as data. -/
def polySysFinR (rel : List α → List (List ℚ)) (Bs : List (List ℚ × (Fin n → GPoly α)))
    (RL : List (List (GPoly α))) : List (List ℚ × (Fin n → GPoly α)) :=
  let Rs : List (Fin n → GPoly α) := RL.map fun l ↦ listFn l []
  let Qd := residLen Rs
  let U := relRun O cst rel Bs.length (residVals O Rs Qd) (n * Qd)
  U.map fun u ↦ (vcomb Cl.length u (Bs.map Prod.fst), vecM fun i ↦
    sumC O (List.range Bs.length) fun l ↦
      GPoly.smul O (cst (u.getD l 0)) ((Bs.getD l ([], fun _ ↦ [])).2 i))

theorem polySysFin_R (rel : List α → List (List ℚ)) (Bs : List (List ℚ × (Fin n → GPoly α)))
    (RL : List (List (GPoly α)))
    (hR : Bs.map (fun bb ↦ matL fun i ↦ resQVC O w0 b A B cst Cl bb.1 bb.2 i) = RL) :
    polySysFin O w0 b A B cst Cl rel Bs = polySysFinR O cst Cl rel Bs RL := by
  unfold polySysFin polySysFinR residsC
  rw [hR]

/-- Solutions one level down as data. -/
def toDatV (X : List (List ℚ × (Fin n → α))) : List (List ℚ × List α) :=
  X.map fun p ↦ (p.1, matL p.2)

/-- Solutions one level down read from data. -/
def toFnsV (L : List (List ℚ × List α)) : List (List ℚ × (Fin n → α)) :=
  L.map fun p ↦ (p.1, listFn p.2 O.zero)

lemma toFnsV_toDatV (X : List (List ℚ × (Fin n → α))) : toFnsV O (toDatV X) = X := by
  simp only [toFnsV, toDatV, List.map_map]
  conv_rhs => rw [← List.map_id X]
  exact List.map_congr_left fun p _ ↦ by simp [listFn_matL]

/-- `stepDiffR` with the lower solutions supplied. -/
def stepDiffL (k : ℕ) (Bs : List (List ℚ × (Fin n → GPoly α)))
    (Ls : List (List ℚ × (Fin n → α))) : List (List ℚ × (Fin n → GPoly α)) :=
  (Ls.map fun r ↦ (vcomb Cl.length r.1 (Bs.map Prod.fst), diffNew O cst k Bs r)).map
    fun p ↦ (p.1, listFn p.2 [])

theorem stepDiffR_L (PA : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α))) (k : ℕ)
    (Bs : List (List ℚ × (Fin n → GPoly α))) (R : List (List α)) (Lw : List (List ℚ × List α))
    (hL : toDatV (lowerC k ((R.map fun r ↦ mvL O PA r).map fun l ↦ listFn l O.zero)) = Lw) :
    stepDiffR O cst Cl PA lowerC k Bs R = stepDiffL O cst Cl k Bs (toFnsV O Lw) := by
  rw [← hL, toFnsV_toDatV]
  rfl

/-- The final phase with the constant relations `U` supplied. -/
def polySysFinU (Bs : List (List ℚ × (Fin n → GPoly α))) (U : List (List ℚ)) :
    List (List ℚ × (Fin n → GPoly α)) :=
  U.map fun u ↦ (vcomb Cl.length u (Bs.map Prod.fst), vecM fun i ↦
    sumC O (List.range Bs.length) fun l ↦
      GPoly.smul O (cst (u.getD l 0)) ((Bs.getD l ([], fun _ ↦ [])).2 i))

theorem polySysFinR_U (rel : List α → List (List ℚ)) (Bs : List (List ℚ × (Fin n → GPoly α)))
    (RL : List (List (GPoly α))) (U : List (List ℚ))
    (hU : relRun O cst rel Bs.length (residVals O (RL.map fun l ↦ listFn (n := n) l [])
      (residLen (RL.map fun l ↦ listFn (n := n) l []))) (n * residLen (RL.map fun l ↦ listFn (n := n) l [])) = U) :
    polySysFinR O cst Cl rel Bs RL = polySysFinU O cst Cl Bs U := by
  unfold polySysFinR polySysFinU
  dsimp only
  rw [hU]

theorem relRun_stage (rel : List α → List (List ℚ)) (p : ℕ) (vals : ℕ → List α) (x : ℕ)
    (U U' : List (List ℚ)) (hx : relRun O cst rel p vals x = U)
    (h : relStep O cst rel p (vals x) U = U') : relRun O cst rel p vals (x + 1) = U' := by
  rw [← h, ← hx]; rfl

theorem relRun_zero' (rel : List α → List (List ℚ)) (p : ℕ) (vals : ℕ → List α) (U : List (List ℚ))
    (h : (List.range p).map (unitV p) = U) : relRun O cst rel p vals 0 = U := h

theorem vlRun_stage (L : ℕ) (lim : List α → List (List ℚ × α)) (ws : List (Fin n → α)) (i : ℕ)
    (hi : i < n) (E E' : List (List ℚ × List α)) (hE : vlRun O cst L lim ws i = E)
    (h : vlStep O cst L lim ws ⟨i, hi⟩ E = E') : vlRun O cst L lim ws (i + 1) = E' := by
  rw [vlRun, dite_cond_eq_true (eq_true hi), hE, h]

theorem vlRun_zero' (L : ℕ) (lim : List α → List (List ℚ × α)) (ws : List (Fin n → α)) :
    vlRun O cst L lim ws 0 = vlInit L := rfl

end Tower.Sys
