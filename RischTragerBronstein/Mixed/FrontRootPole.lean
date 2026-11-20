import RischTragerBronstein.Mixed.FrontSqrtPole
import RischTragerBronstein.Mixed.KVMain

/-!
# The `n`-th root front end with poles, over a logarithm

`frontRootPE M n j zN gs E a e₁ cs`: decides `∫ e₁ θʲ`, `θⁿ = a`, when the top generator of the
tower of `E` is a logarithm, `a` compiles to a squarefree polynomial `A(t)` in it of degree prime
to `n`, and the denominator of `e₁` is `c ∏(t − c_q) Aˡ` for the poles `c_q` given as expressions
of the level below the top (`cs`), checked by exact divisions (`divLins`): dispatched to
`kvDecide`, with the number field `ℚ[X]/(M)` containing a primitive `n`-th root of unity `zN` and
the `n`-th roots `gs` of the residue invariants supplied (and checked by `kvDecide`).
`frontRootPE_sound`: every answer is correct, for every realization of the compiled tower and
every `n`-th root `θ` of `a` generating `L` over it.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- The `n`-th root front end with poles over a given tower expression `E`. -/
def frontRootPE (M : CPoly ℚ) [∀ m, Fact (Irreducible (toPoly (liftQ Fc m M)))] (n j : ℕ)
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (E a e1 : EE) (cs : List EE)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
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
      if !(GPoly.squarefreeCheck O A) ∨ degG O A = 0 ∨ Nat.gcd n (degG O A) ≠ 1 then none else
      let sA := stripG O A q1.2.length q1.2
      match divLins Fc m K cq sA.1 with
      | none => none
      | some D1 =>
        match K m with
        | .exp _ => none
        | .prim η =>
          if degG O D1 ≠ 0 ∨ GPoly.isZero O D1 = true then none else
          kvDecide Fc K lv m n j η M zN gs A (q1.1.map (O.mul (O.inv (D1.getD 0 O.zero)))) sA.2 cq
            ps bound rs
    | _, _, _ => none

/-- **The front end for `∫ e₁ θʲ`, `θⁿ = a`, with poles `cs`**, over the tower of `a`, `e₁` and
the poles. -/
def frontRootP (M : CPoly ℚ) [∀ m, Fact (Irreducible (toPoly (liftQ Fc m M)))] (n j : ℕ)
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (a e1 : EE) (cs : List EE)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  frontRootPE Fc M n j zN gs (spE a e1 cs) a e1 cs ps bound rs

universe u

variable {Fc} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **Every answer of `frontRootPE` is correct**: for every realization and `n`-th root `θ` of
`a` generating the extension, `∫ e₁ θʲ` is elementary iff the answer is `true`. -/
theorem frontRootPE_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (M : CPoly ℚ) [∀ m, Fact (Irreducible (toPoly (liftQ Fc m M)))] (n j : ℕ)
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (E a e1 : EE) (cs : List EE)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool)
    (hb : frontRootPE Fc M n j zN gs E a e1 cs ps bound rs = some b)
    (T : MTower Fc (ksOf Fc E) Cc L) (hn : T.n = E.nodesOf.length) (θ : L)
    (hθ : θ ^ n = evE Fc T E.nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F E.nodesOf.length) {θ}) :
    HasElementaryIntegral (evE Fc T E.nodesOf e1 * θ ^ j) ↔ b = true := by
  classical
  unfold frontRootPE at hb
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
      degG (MO Fc (ksOf Fc E) m) A = 0 ∨ Nat.gcd n (degG (MO Fc (ksOf Fc E) m) A) ≠ 1
  · rw [if_pos hd2] at hb; cases hb
  rw [if_neg hd2] at hb
  push Not at hd2
  obtain ⟨hsq, hdeg0, hgcd⟩ := hd2
  have hθA : θ ^ n = T.evP m A := by
    rw [hθ, ← hva, hA, ev_constDen T m hTm qa hd1.1 hd1']
  have hsqc : GPoly.squarefreeCheck (MO Fc (ksOf Fc E) m) A = true := by simpa using hsq
  have hdegpos : 0 < degG (MO Fc (ksOf Fc E) m) A := by omega
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
  · cases hb
  rename_i η hkη
  by_cases hd3 : degG (MO Fc (ksOf Fc E) m) D1 ≠ 0 ∨
      GPoly.isZero (MO Fc (ksOf Fc E) m) D1 = true
  · rw [if_pos hd3] at hb; cases hb
  rw [if_neg hd3] at hb
  push Not at hd3
  obtain ⟨hcv, hcne⟩ := evP_const T m hTm D1 hd3.1 (by simpa using hd3.2)
  have hdec := T.kvDecide_correct hmon hdeg m hn hc hkη n j M zN gs A hsqc hdegpos hgcd θ hθA
    hgen _ _ cq ps bound rs b hb
  rw [← hv1, ev_pair_scale T m hTm q1 (kvDen Fc (ksOf Fc E) m A _ cq) _ hcne (by
    rw [hq2, hcv, kvDen, haev (GPoly.mul _ _ _), GPoly.toPoly_mul, map_mul, ← haev, ← haev,
      T.evP_powG m hTm]
    ring)]
  exact hdec

/-- **Every answer of `frontRootP` is correct.** -/
theorem frontRootP_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (M : CPoly ℚ) [∀ m, Fact (Irreducible (toPoly (liftQ Fc m M)))] (n j : ℕ)
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (a e1 : EE) (cs : List EE)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool)
    (hb : frontRootP Fc M n j zN gs a e1 cs ps bound rs = some b)
    (T : MTower Fc (ksOf Fc (spE a e1 cs)) Cc L) (hn : T.n = (spE a e1 cs).nodesOf.length) (θ : L)
    (hθ : θ ^ n = evE Fc T (spE a e1 cs).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (spE a e1 cs).nodesOf.length) {θ}) :
    HasElementaryIntegral (evE Fc T (spE a e1 cs).nodesOf e1 * θ ^ j) ↔ b = true :=
  frontRootPE_sound hmon hdeg M n j zN gs _ a e1 cs ps bound rs b hb T hn θ hθ hgen

end Curves.MT.Front
