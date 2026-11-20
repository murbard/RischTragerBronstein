import RischTragerBronstein.Mixed.NKStageC2
import RischTragerBronstein.Mixed.SysExpT

/-!
# Staged kernel evaluation of `expSysT` (exponential level, triangular limit)

`expSysT_stage`: after the front checks, `expSysT` is the indicial bound followed by `expSysTB`;
`expSysTB_eq`: `expSysTB` is `expSysTW` on the system `wSysE`; `expSysTW_eq`: with the check `okBE`
passed, `expSysTW` is the polynomial solver `polySysC` with the lower solver `triSys`. The loop stages
are those of `Mixed/NKStageC`.
-/

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- `expSysT` once the system `W` is computed. -/
def expSysTW (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (W : WSys m n) : Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))) :=
  let O := MO Fc ks m
  let cst := mcst Fc ks m
  let bc := O.deriv a
  let δ := degG O W.a
  let dD := degG O W.Den
  let Ll := lamList Fc ks m bc n W.BW δ dD
  let Λ : Fin n → Fin n → ℚ := fun i j ↦ (Ll.getD i []).getD j 0
  let okB := (List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
    decide ((GPoly.trim O (W.BW i j)).length ≤ δ + 1) &&
    O.isZero (O.add ((W.BW i j).getD δ O.zero)
      (O.neg (O.mul (cst (Λ i j - if i = j then (dD : ℚ) else 0)) bc))) &&
    (decide ((j : ℕ) < i) → Λ i j == 0)
  if !okB then none else
  let Ncl := (W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0
  let N' := max (triBd dD ((List.finRange n).map fun i ↦ Λ i i)) (Ncl - δ)
  let PA : Fin n → Fin n → LC m := fun i j ↦ if i = j then O.inv (leadG O W.a) else O.zero
  some (W.Den, polySysC O O.zero bc (fun i j ↦ if i = j then W.a else []) W.BW cst W.Cl δ false
    PA PA (fun k ws ↦ triSys O cst (fun i ↦ rdeD (O.mul (cst ((k : ℚ) - dD + Λ i i)) a))
      (fun i j ↦ O.mul (cst (Λ i j)) bc) ws) (mrel Fc ks m) (N' + 1))

/-- `expSysT` after the indicial bound `B`. -/
def expSysTB (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))
    (B : ℕ) : Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))) :=
  expSysTW Fc ks m a rdeD n (wSysE Fc ks m ((MO Fc ks m).deriv a) n A0 q h G0 B)

theorem expSysT_stage (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m))
    (G0 : List (Fin n → GPoly (LC m)))
    (hmon : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) h) = true)
    (hq0 : (MO Fc ks m).isZero (q.getD 0 (MO Fc ks m).zero) = false)
    (hz : zeroOK Fc ks m ((MO Fc ks m).deriv a) n A0 q = true) :
    expSysT Fc ks m a rdeD n A0 q h G0 =
      (indBound2 Fc ks m (degG (MO Fc ks m) q) n q
        (DzLC (MO Fc ks m) (MO Fc ks m).zero ((MO Fc ks m).deriv a) q) A0).bind
        (expSysTB Fc ks m a rdeD n A0 q h G0) := by
  unfold expSysT
  dsimp only
  rw [hmon, hq0, hz]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rcases indBound2 Fc ks m (degG (MO Fc ks m) q) n q
    (DzLC (MO Fc ks m) (MO Fc ks m).zero ((MO Fc ks m).deriv a) q) A0 with _ | B <;> rfl

/-- The check `okB` of `expSysTW`. -/
def okBE (m : ℕ) (a : LC m) (n : ℕ) (W : WSys m n) : Bool :=
  let O := MO Fc ks m
  let cst := mcst Fc ks m
  let bc := O.deriv a
  let δ := degG O W.a
  let dD := degG O W.Den
  let Ll := lamList Fc ks m bc n W.BW δ dD
  let Λ : Fin n → Fin n → ℚ := fun i j ↦ (Ll.getD i []).getD j 0
  (List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
    decide ((GPoly.trim O (W.BW i j)).length ≤ δ + 1) &&
    O.isZero (O.add ((W.BW i j).getD δ O.zero)
      (O.neg (O.mul (cst (Λ i j - if i = j then (dD : ℚ) else 0)) bc))) &&
    (decide ((j : ℕ) < i) → Λ i j == 0)

/-- The matrix `Λ` of `expSysTW`. -/
def lamE (m : ℕ) (a : LC m) (n : ℕ) (W : WSys m n) : Fin n → Fin n → ℚ :=
  fun i j ↦ ((lamList Fc ks m ((MO Fc ks m).deriv a) n W.BW (degG (MO Fc ks m) W.a)
    (degG (MO Fc ks m) W.Den)).getD i []).getD j 0

/-- The lower solver of `expSysTW`. -/
def lowE (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (W : WSys m n) : ℕ → List (Fin n → LC m) → List (List ℚ × (Fin n → LC m)) :=
  fun k ws ↦ triSys (MO Fc ks m) (mcst Fc ks m) (fun i ↦ rdeD ((MO Fc ks m).mul
    ((mcst Fc ks m) ((k : ℚ) - degG (MO Fc ks m) W.Den + lamE Fc ks m a n W i i)) a))
    (fun i j ↦ (MO Fc ks m).mul ((mcst Fc ks m) (lamE Fc ks m a n W i j)) ((MO Fc ks m).deriv a)) ws

/-- The degree bound of `expSysTW`. -/
def NpE (m : ℕ) (a : LC m) (n : ℕ) (W : WSys m n) : ℕ :=
  max (triBd (degG (MO Fc ks m) W.Den) ((List.finRange n).map fun i ↦ lamE Fc ks m a n W i i))
    ((W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0 -
      degG (MO Fc ks m) W.a)

theorem expSysTW_eq (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (W : WSys m n) (hok : okBE Fc ks m a n W = true) :
    expSysTW Fc ks m a rdeD n W = some (W.Den, polySysC (MO Fc ks m) (MO Fc ks m).zero
      ((MO Fc ks m).deriv a) (fun i j ↦ if i = j then W.a else []) W.BW (mcst Fc ks m) W.Cl
      (degG (MO Fc ks m) W.a) false
      (fun i j ↦ if i = j then (MO Fc ks m).inv (leadG (MO Fc ks m) W.a) else (MO Fc ks m).zero)
      (fun i j ↦ if i = j then (MO Fc ks m).inv (leadG (MO Fc ks m) W.a) else (MO Fc ks m).zero)
      (lowE Fc ks m a rdeD n W) (mrel Fc ks m) (NpE Fc ks m a n W + 1)) := by
  unfold okBE at hok
  unfold expSysTW
  simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false]
  rfl

end Curves.MT
