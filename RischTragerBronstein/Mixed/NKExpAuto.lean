import RischTragerBronstein.Mixed.NKExpDecide
import RischTragerBronstein.Mixed.SysTriQ

/-!
# Triangularizing the limit at infinity by a constant change of basis

`exactTA`: if `exactT` answers `none` in the basis `w = Tc θ`, compute (untrusted) the limit matrix
`Λ` at infinity of the exponential system, a rational `C` triangularizing it (`triCQ`), and retry in
the bases `C w`, `C⁻ᵀ w`. Any answer is an answer of `exactT` for some basis
(`exactTA_spec`), so `nk_iffET` applies (`nk_iffETA`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The limit matrix at infinity of the exponential system in the basis `Tc θ` (untrusted). -/
def lamInfE (m : ℕ) (a : LC m) (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) :
    Option (List (List ℚ)) :=
  let O1 := MOr Fc ks (m + 1)
  let N := P.length - 1
  let tm : ℕ → ℕ → LC (m + 1) := fun i j ↦ (Tc.getD i []).getD j O1.zero
  let ti : ℕ → ℕ → LC (m + 1) := fun i j ↦ (Ti.getD i []).getD j O1.zero
  match dThetaC O1 P with
  | none => none
  | some dθ =>
    let mθ : ℕ → ℕ → LC (m + 1) := fun i j ↦ (dPowC O1 P dθ i).getD j O1.zero
    let Mw := (List.range N).map fun i ↦ (List.range N).map fun j ↦
      lsumC O1 ((List.range N).map fun l ↦ O1.mul (O1.add (O1.deriv (tm i l))
        (lsumC O1 ((List.range N).map fun k ↦ O1.mul (tm i k) (mθ k l)))) (ti l j))
    let O1n := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
    let O := MO Fc ks m
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (Mw.getD i []).getD j O1n.zero
    let q := lcmGL O (M.flatten.map Prod.snd)
    let A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
      GPoly.mul O ((M.getD i []).getD j O1n.zero).1 (cofC O q ((M.getD i []).getD j O1n.zero).2).2
    let bc := O.deriv a
    match indBound2 Fc ks m (degG O q) N q (DzLC O O.zero bc q) A0 with
    | none => none
    | some B =>
      let W := wSysE Fc ks m bc N A0 q [O.one] [] B
      some (lamList Fc ks m bc N W.BW (degG O W.a) (degG O W.Den))

/-- `C · Tc` and `Ti · Ci` for rational `C`, `Ci`. -/
def rowMix (m n : ℕ) (C : QMat) (Tc : List (List (LC (m + 1)))) : List (List (LC (m + 1))) :=
  let O1 := MOr Fc ks (m + 1)
  (List.range n).map fun r ↦ (List.range n).map fun j ↦
    lsumC O1 ((List.range n).map fun k ↦ O1.mul (mcst Fc ks (m + 1) (C r k))
      ((Tc.getD k []).getD j O1.zero))
def colMix (m n : ℕ) (Ti : List (List (LC (m + 1)))) (Ci : QMat) : List (List (LC (m + 1))) :=
  let O1 := MOr Fc ks (m + 1)
  (List.range n).map fun i ↦ (List.range n).map fun r ↦
    lsumC O1 ((List.range n).map fun k ↦ O1.mul ((Ti.getD i []).getD k O1.zero)
      (mcst Fc ks (m + 1) (Ci k r)))

/-- The candidate bases. -/
def basisCands (m : ℕ) (a : LC m) (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) :
    List (List (List (LC (m + 1))) × List (List (LC (m + 1)))) :=
  let n := P.length - 1
  match lamInfE Fc ks m a P Tc Ti with
  | none => []
  | some Λ =>
    match triCQ n (fun i j ↦ (Λ.getD i []).getD j 0) with
    | none => []
    | some (C, Ci) =>
      [(rowMix Fc ks m n C Tc, colMix Fc ks m n Ti Ci),
        (rowMix Fc ks m n (fun i j ↦ Ci j i) Tc, colMix Fc ks m n Ti (fun i j ↦ C j i))]

/-- **`exactT` with an automatic constant change of basis at infinity.** -/
def exactTA (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) :
    Option Bool :=
  ((Tc, Ti) :: basisCands Fc ks m a P Tc Ti).findSome? fun B ↦
    exactT Fc ks m (expSysT Fc ks m a rdeD) P B.1 B.2 f

lemma exactTA_spec {m : ℕ} {a : LC m} {rdeD : LC m → List (LC m) → List (List ℚ × LC m)}
    {P : GPoly (LC (m + 1))} {Tc Ti : List (List (LC (m + 1)))} {f : List (LC (m + 1))}
    {res : Bool} (h : exactTA Fc ks m a rdeD P Tc Ti f = some res) :
    ∃ Tc' Ti' : List (List (LC (m + 1))),
      exactT Fc ks m (expSysT Fc ks m a rdeD) P Tc' Ti' f = some res := by
  obtain ⟨B, -, hB⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨B.1, B.2, hB⟩

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The decision with an automatic basis at infinity** (`exactTA`). -/
theorem nk_iffETA (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTA Fc ks m a (rdeE Fc ks lv m) (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  obtain ⟨Tc', Ti', h⟩ := exactTA_spec Fc ks hres
  exact T.nk_iffET hmon hdeg m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp Tc' Ti' res h

end MTower

end Curves.MT
