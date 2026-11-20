import RischTragerBronstein.Mixed.NKLogDecideT
import RischTragerBronstein.Mixed.NKExpAuto

/-!
# Shearing the basis at multiple finite poles (untrusted search)

At a multiple factor `g` of the denominator of the derivation matrix, a singular leading matrix
makes the system solvers answer `none` (the case of Moser reduction). Changing the basis by
shearings `wᵢ ↦ wᵢ/gᵏ` (`i ∈ S`) is the elementary step of that reduction, and it produces e.g. the
integral basis `(1, θ/t)` from `(1, θ)`. `exactTS` tries the shearings of `Tc` by the repeated part
`g = gcd(q, q′)` (`k ≤ 2`, all subsets `S`). Any answer is an `exactT` answer for some basis
(`exactTS_spec`), so the decisions `nk_iffT` (logarithmic level) and `nk_iffET` (exponential
level) apply (`nk_iffTS`, `nk_iffETS`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The (untrusted) denominator of the derivation matrix in the basis `Tc θ`. -/
def matDen (m : ℕ) (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) :
    Option (GPoly (LC m)) :=
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
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (Mw.getD i []).getD j O1n.zero
    some (lcmGL (MO Fc ks m) (M.flatten.map Prod.snd))

/-- The shearing of `(Tc, Ti)` by `gᵏ` on the rows in the bitmask `S`. -/
def shear (m n : ℕ) (g : GPoly (LC m)) (k S : ℕ) (Tc Ti : List (List (LC (m + 1)))) :
    List (List (LC (m + 1))) × List (List (LC (m + 1))) :=
  let O1 := MOr Fc ks (m + 1)
  let O := MO Fc ks m
  let gk : LC (m + 1) := (sysPowC O g k, [O.one])
  let gki : LC (m + 1) := ([O.one], sysPowC O g k)
  let inS : ℕ → Bool := fun i ↦ S.testBit i
  ((List.range n).map fun i ↦ (List.range n).map fun j ↦
      if inS i then O1.mul gki ((Tc.getD i []).getD j O1.zero) else (Tc.getD i []).getD j O1.zero,
    (List.range n).map fun i ↦ (List.range n).map fun j ↦
      if inS j then O1.mul ((Ti.getD i []).getD j O1.zero) gk else (Ti.getD i []).getD j O1.zero)

/-- The shearing factors: the repeated part `gcd(q, q′)`, `X` if `q(0) = 0`, and `X − c` for the
rational roots `c` of `q` when its coefficients are rational. -/
def shearFactors (m : ℕ) (q : GPoly (LC m)) : List (GPoly (LC m)) :=
  let O := MO Fc ks m
  let g := GPoly.gcd O q (GPoly.derivX O q)
  let rat : List (Option ℚ) := q.map (ratValC Fc ks m)
  let roots : List ℚ :=
    if rat.all Option.isSome then ratRootsF (rat.map (·.getD 0)) else []
  (if degG O g = 0 then [] else [g]) ++
    (if O.isZero (q.getD 0 O.zero) then [[O.zero, O.one]] else []) ++
    ((roots.filter (· ≠ 0)).map fun c ↦ [mcst Fc ks m (-c), O.one])

/-- The candidate sheared bases. -/
def shearCands (m : ℕ) (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) :
    List (List (List (LC (m + 1))) × List (List (LC (m + 1)))) :=
  let n := P.length - 1
  match matDen Fc ks m P Tc Ti with
  | none => []
  | some q =>
    (shearFactors Fc ks m q).flatMap fun g ↦
      (List.range 2).flatMap fun k ↦ (List.range (2 ^ n)).map fun S ↦
        shear Fc ks m n g (k + 1) S Tc Ti

/-- The bases reached by up to `d` shearing steps. -/
def shearTree (m : ℕ) (P : GPoly (LC (m + 1))) :
    ℕ → List (List (LC (m + 1))) × List (List (LC (m + 1))) →
      List (List (List (LC (m + 1))) × List (List (LC (m + 1))))
  | 0, B => [B]
  | d + 1, B => B :: (shearCands Fc ks m P B.1 B.2).flatMap (shearTree m P d)

/-- **`exactT` with shearings at finite poles** (two reduction steps). -/
def exactTS (m : ℕ) (solve : SysSolver m) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) : Option Bool :=
  (shearTree Fc ks m P 2 (Tc, Ti)).findSome? fun B ↦ exactT Fc ks m solve P B.1 B.2 f

lemma exactTS_spec {m : ℕ} {solve : SysSolver m} {P : GPoly (LC (m + 1))}
    {Tc Ti : List (List (LC (m + 1)))} {f : List (LC (m + 1))} {res : Bool}
    (h : exactTS Fc ks m solve P Tc Ti f = some res) :
    ∃ Tc' Ti' : List (List (LC (m + 1))), exactT Fc ks m solve P Tc' Ti' f = some res := by
  obtain ⟨B, -, hB⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨B.1, B.2, hB⟩

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The logarithmic-level decision with sheared bases.** -/
theorem nk_iffTS (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTS Fc ks m (primSysC Fc ks m η (paramLimC Fc ks lv m)) (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  obtain ⟨Tc', Ti', h⟩ := exactTS_spec Fc ks hres
  exact T.nk_iffT hmon hdeg m hn hc hk Pp hsh θ hθ hgen s hs fp Tc' Ti' res h

/-- **The exponential-level decision with sheared bases.** -/
theorem nk_iffETS (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTS Fc ks m (expSysT Fc ks m a (rdeE Fc ks lv m)) (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  obtain ⟨Tc', Ti', h⟩ := exactTS_spec Fc ks hres
  exact T.nk_iffET hmon hdeg m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp Tc' Ti' res h

end MTower

end Curves.MT
