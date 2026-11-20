import RischTragerBronstein.Mixed.FrontSqrtPole
import RischTragerBronstein.Mixed.FrontSqrtW
import RischTragerBronstein.Mixed.KQWit
import RischTragerBronstein.Mixed.KXWit

/-!
# The square-root front end with poles: the antiderivative

`frontSqrtPEW` mirrors `frontSqrtPE` (`frontSqrtPEW_isSome`) and returns the witness of `kqDecideCW`
(below a logarithm) or `kxDecideCW` (below an exponential), valid for every realization
(`frontSqrtPEW_valid`; explicit antiderivatives by `kq_param_antiderivative`, `sqcols_antiderivative`,
`SqCol.logs`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

/-- The antiderivative found by the pole front end. -/
inductive PoleW where
  | kq (m : ℕ) (w : KQW m)
  | kx (m : ℕ) (w : KXW m)

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **`frontSqrtPE` with the antiderivative.** -/
def frontSqrtPEW (E a e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    Option (Option PoleW) :=
  match E.nodesOf.length with
  | 0 => none
  | m + 1 =>
    let K := ksOf Fc E
    let lv := lvOf Fc E
    let O := MO Fc K m
    if !(curveShape Fc && certC Fc K lv (m + 1)) then none else
    match comp Fc E.nodesOf K (m + 1) a, comp Fc E.nodesOf K (m + 1) e1,
      allSomeL (cs.map fun c ↦ comp Fc E.nodesOf K m c) with
    | some qa, some q1, some cq =>
      if degG O qa.2 ≠ 0 ∨ GPoly.isZero O qa.2 = true then none else
      let A := qa.1.map (O.mul (O.inv (qa.2.getD 0 O.zero)))
      if !(GPoly.squarefreeCheck O A) ∨ degG O A % 2 = 0 then none else
      let sA := stripG O A q1.2.length q1.2
      match divLins Fc m K cq sA.1 with
      | none => none
      | some D1 =>
        match K m with
        | .exp g =>
          let st := stripG O (tX Fc K m) D1.length D1
          if degG O st.1 ≠ 0 ∨ GPoly.isZero O st.1 = true then none else
          (kxDecideCW Fc K lv m g A (q1.1.map (O.mul (O.inv (st.1.getD 0 O.zero)))) st.2 sA.2 cq
            (fun fK ↦ searchCert fK 2) ps bound rs).map (Option.map (PoleW.kx m))
        | .prim η =>
          if degG O D1 ≠ 0 ∨ GPoly.isZero O D1 = true then none else
          (kqDecideCW Fc K lv m η A (q1.1.map (O.mul (O.inv (D1.getD 0 O.zero)))) sA.2 cq ps bound rs
            (fun fK ↦ searchCert fK 2)).map (Option.map (PoleW.kq m))
    | _, _, _ => none

/-- **`frontSqrtPEW` answers as `frontSqrtPE`.** -/
theorem frontSqrtPEW_isSome (E a e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    (frontSqrtPEW Fc E a e1 cs ps bound rs).map Option.isSome = frontSqrtPE Fc E a e1 cs ps bound rs := by
  unfold frontSqrtPEW frontSqrtPE frontSqrtPEWith
  rcases E.nodesOf.length with _ | m
  · rfl
  dsimp only
  split_ifs
  · rfl
  rcases comp Fc E.nodesOf (ksOf Fc E) (m + 1) a with _ | qa
  · rfl
  rcases comp Fc E.nodesOf (ksOf Fc E) (m + 1) e1 with _ | q1
  · rfl
  rcases allSomeL (cs.map fun c ↦ comp Fc E.nodesOf (ksOf Fc E) m c)
    with _ | cq
  · rfl
  dsimp only
  split_ifs
  all_goals (try rfl)
  all_goals (rcases divLins Fc m (ksOf Fc E) cq _ with _ | D1)
  all_goals (try rfl)
  all_goals (rcases ksOf Fc E m with η | g)
  all_goals (try dsimp only)
  all_goals (try split_ifs)
  all_goals (first
    | rfl
    | (rw [map_map_isSomeF, kqDecideCW_isSome]; rfl)
    | (rw [map_map_isSomeF, kxDecideCW_isSome]; rfl))

/-- **`frontSqrtP` with the antiderivative.** -/
def frontSqrtPW (a e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    Option (Option PoleW) :=
  frontSqrtPEW Fc (spE a e1 cs) a e1 cs ps bound rs

theorem frontSqrtPW_isSome (a e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    (frontSqrtPW Fc a e1 cs ps bound rs).map Option.isSome = frontSqrtP Fc a e1 cs ps bound rs :=
  frontSqrtPEW_isSome Fc _ a e1 cs ps bound rs

universe u

variable {Fc}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **Validity of an antiderivative found by the pole front end**: the data of a Kummer decision
whose witness is valid. -/
def PoleW.Valid {ks : (m : ℕ) → KindC m} (T : MTower Fc ks Cc L) (lv : (m : ℕ) → LC m) (θ f : L) :
    PoleW → Prop
  | .kq m w => ∃ (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)),
      f = T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
        (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ ∧ MTower.KQW.Valid T m η A B l cs θ w
  | .kx m w => ∃ (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)),
      f = T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ ∧ θ ^ 2 = T.evP m A ∧
        MTower.KXW.Valid T lv m A B kt l cs w

/-- **Every antiderivative returned by `frontSqrtPEW` is valid.** -/
theorem frontSqrtPEW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (E a e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (w : PoleW)
    (hb : frontSqrtPEW Fc E a e1 cs ps bound rs = some (some w))
    (T : MTower Fc (ksOf Fc E) Cc L) (hn : T.n = E.nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE Fc T E.nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F E.nodesOf.length) {θ}) :
    PoleW.Valid T (lvOf Fc E) θ (evE Fc T E.nodesOf e1 * θ) w := by
  classical
  unfold frontSqrtPEW at hb
  obtain ⟨m, hlen⟩ : ∃ m, E.nodesOf.length = m + 1 := by
    rcases h0 : E.nodesOf.length with _ | m
    · rw [h0] at hb; cases hb
    · exact ⟨m, rfl⟩
  rw [hlen] at hb hn hgen
  dsimp only at hb
  by_cases hcs : (curveShape Fc && certC Fc (ksOf Fc E) (lvOf Fc E) (m + 1)) = true
  swap
  · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hcs)] at hb; cases hb
  rw [if_neg (by rw [hcs]; decide)] at hb
  obtain ⟨hsh, hc⟩ := Bool.and_eq_true_iff.mp hcs
  have MS := T.mspecs hmon hdeg (lvOf Fc E) (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  rcases hqa : comp Fc E.nodesOf (ksOf Fc E) (m + 1) a with _ | qa
  · rw [hqa] at hb; cases hb
  rcases hq1 : comp Fc E.nodesOf (ksOf Fc E) (m + 1) e1 with _ | q1
  · rw [hqa, hq1] at hb; cases hb
  rcases hcq : allSomeL (cs.map fun c ↦ comp Fc E.nodesOf (ksOf Fc E) m c)
    with _ | cq
  · rw [hqa, hq1, hcq] at hb; cases hb
  rw [hqa, hq1, hcq] at hb
  dsimp only at hb
  have hva := comp_spec Fc T E.nodesOf (m + 1) hTr a qa hqa
  have hv1 := comp_spec Fc T E.nodesOf (m + 1) hTr e1 q1 hq1
  by_cases hd1 : degG (MO Fc (ksOf Fc E) m) qa.2 ≠ 0 ∨
      GPoly.isZero (MO Fc (ksOf Fc E) m) qa.2 = true
  · rw [if_pos hd1] at hb; cases hb
  rw [if_neg hd1] at hb
  push Not at hd1
  have hd1' : GPoly.isZero (MO Fc (ksOf Fc E) m) qa.2 = false := by simpa using hd1.2
  set A := qa.1.map ((MO Fc (ksOf Fc E) m).mul ((MO Fc (ksOf Fc E) m).inv
    (qa.2.getD 0 (MO Fc (ksOf Fc E) m).zero))) with hA
  by_cases hd2 : (!GPoly.squarefreeCheck (MO Fc (ksOf Fc E) m) A) = true ∨
      degG (MO Fc (ksOf Fc E) m) A % 2 = 0
  · rw [if_pos hd2] at hb; cases hb
  rw [if_neg hd2] at hb
  push Not at hd2
  have hθA : θ ^ 2 = T.evP m A := by
    rw [hθ, ← hva, hA, ev_constDen T m hTm qa hd1.1 hd1']
  have hsqc : GPoly.squarefreeCheck (MO Fc (ksOf Fc E) m) A = true := by simpa using hd2.1
  have hodd : degG (MO Fc (ksOf Fc E) m) A % 2 = 1 := by omega
  have hdegpos : 0 < degG (MO Fc (ksOf Fc E) m) A := by omega
  have hcop : Nat.Coprime 2 (degG (MO Fc (ksOf Fc E) m) A) :=
    Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd)
  have haev : ∀ q, T.evP m q = aeval (T.ts m) (GPoly.toPoly (T.MP m hTm) q) := fun q ↦
    (T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm) q).symm
  have hsA := stripG_spec (MO Fc (ksOf Fc E) m) (T.MP m hTm) A q1.2.length q1.2
  rcases hD1 : divLins Fc m (ksOf Fc E) cq
    (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1 with _ | D1
  · rw [hD1] at hb; cases hb
  rw [hD1] at hb
  dsimp only at hb
  have hdl := divLins_spec T m hTm cq _ D1 hD1
  have hq2 : T.evP m q1.2 = T.evP m A ^ (stripG (MO Fc (ksOf Fc E) m) A q1.2.length
      q1.2).2 * (T.evP m (prodLinG Fc (ksOf Fc E) m cq) * T.evP m D1) := by
    rw [haev q1.2, hsA, map_mul, map_pow, ← haev, ← haev, hdl]
  split at hb
  · -- below an exponential
    rename_i g hkg
    by_cases hd3 : degG (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m)
        (tX Fc (ksOf Fc E) m) D1.length D1).1 ≠ 0 ∨ GPoly.isZero
        (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m)
        (tX Fc (ksOf Fc E) m) D1.length D1).1 = true
    · rw [if_pos hd3] at hb; cases hb
    rw [if_neg hd3] at hb
    push Not at hd3
    obtain ⟨hcv, hcne⟩ := evP_const T m hTm _ hd3.1 (by simpa using hd3.2)
    have hst := stripG_spec (MO Fc (ksOf Fc E) m) (T.MP m hTm)
      (tX Fc (ksOf Fc E) m) D1.length D1
    have hD1v : T.evP m D1 = T.ts m ^ (stripG (MO Fc (ksOf Fc E) m)
        (tX Fc (ksOf Fc E) m) D1.length D1).2 * T.ev m ((stripG
        (MO Fc (ksOf Fc E) m) (tX Fc (ksOf Fc E) m) D1.length D1).1.getD 0
        (MO Fc (ksOf Fc E) m).zero) := by
      rw [haev D1, hst, map_mul, map_pow, T.toPoly_tX m hTm, aeval_X, ← haev, hcv]
    obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨w', rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
    refine ⟨A, _, _, _, cq, ?_, hθA, T.kxDecideCW_valid hmon hdeg m hn hc g A _ _ _ cq _ ps bound rs
      w' ho⟩
    rw [← hv1, ev_pair_scale T m hTm q1 (kxDen Fc (ksOf Fc E) m A
      (stripG (MO Fc (ksOf Fc E) m) (tX Fc (ksOf Fc E) m) D1.length D1).2
      (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).2 cq) _ hcne (by
      rw [hq2, hD1v]
      simp only [kxDen, haev (GPoly.mul _ _ _), GPoly.toPoly_mul, map_mul, ← haev,
        T.evP_monoG m hTm, T.evP_powG m hTm]
      ring)]
  · -- below a logarithm
    rename_i η hkη
    by_cases hd3 : degG (MO Fc (ksOf Fc E) m) D1 ≠ 0 ∨
        GPoly.isZero (MO Fc (ksOf Fc E) m) D1 = true
    · rw [if_pos hd3] at hb; cases hb
    rw [if_neg hd3] at hb
    push Not at hd3
    obtain ⟨hcv, hcne⟩ := evP_const T m hTm D1 hd3.1 (by simpa using hd3.2)
    obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨w', rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
    refine ⟨η, A, _, _, cq, ?_, T.kqDecideCW_valid hmon hdeg m hn hc hkη A hdegpos θ hθA _ _ cq
      ps bound rs _ w' ho⟩
    rw [← hv1, ev_pair_scale T m hTm q1 (GPoly.mul (MO Fc (ksOf Fc E) m)
      (prodLinG Fc (ksOf Fc E) m cq) (powG (MO Fc (ksOf Fc E) m) A _)) _ hcne (by
      rw [hq2, hcv, haev (GPoly.mul _ _ _), GPoly.toPoly_mul, map_mul, ← haev, ← haev,
        T.evP_powG m hTm]
      ring)]

/-- **Every antiderivative returned by `frontSqrtPW` is valid.** -/
theorem frontSqrtPW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (a e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (w : PoleW)
    (hb : frontSqrtPW Fc a e1 cs ps bound rs = some (some w))
    (T : MTower Fc (ksOf Fc (spE a e1 cs)) Cc L) (hn : T.n = (spE a e1 cs).nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE Fc T (spE a e1 cs).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (spE a e1 cs).nodesOf.length) {θ}) :
    PoleW.Valid T (lvOf Fc (spE a e1 cs)) θ (evE Fc T (spE a e1 cs).nodesOf e1 * θ) w :=
  frontSqrtPEW_valid hmon hdeg _ a e1 cs ps bound rs w hb T hn θ hθ hgen

end Curves.MT.Front
