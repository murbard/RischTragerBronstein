import RischTragerBronstein.Mixed.FrontSqrtPoleNCComplete
import RischTragerBronstein.Mixed.KXInputCheck

/-!
# Eventual decisions for accepted cubic expressions

`frontSqrtPCubicCheck` runs the pole parser with an input-checking backend. It accepts only
exponential top levels and cubic data covered by the completeness theorem. Passing this
executable check guarantees (unconditionally) eventual success of the automatic expression search.
The check itself does not decide whether the integral is elementary.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT.Front

open CPoly Sup Curves.LT Tower.NestM Tower.NestX Tower.Sys

universe u

variable (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))]

/-- Check that an expression compiles to cubic exponential data covered by completeness. -/
def frontSqrtPCubicCheck (E a e1 : EE) (cs : List EE) : Bool :=
  match E.nodesOf.length with
  | 0 => false
  | m + 1 =>
    match ksOf [c0, [1]] E m with
    | .prim _ => false
    | .exp _ =>
      (frontSqrtPEWith [c0, [1]]
        (fun K _ m g A B kt l cq ↦ some (kxInputCheck c0 K m g A B kt l cq))
        E a e1 cs [] 0 (fun _ ↦ 0)).getD false

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- An accepted cubic expression has a successful finite parameter choice. -/
theorem frontSqrtPCubicCheck_attempt (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (E a e1 : EE) (cs : List EE)
    (hcheck : frontSqrtPCubicCheck c0 E a e1 cs = true)
    (T : MTower [c0, [1]] (ksOf [c0, [1]] E) Cc L) (hn : T.n = E.nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE [c0, [1]] T E.nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F E.nodesOf.length) {θ}) :
    ∃ bound rs nmax kmax b,
      frontSqrtPNCE c0 E a e1 cs (primesBelow bound) bound rs nmax kmax = some b := by
  classical
  unfold frontSqrtPCubicCheck at hcheck
  obtain ⟨m, hlen⟩ : ∃ m, E.nodesOf.length = m + 1 := by
    rcases h0 : E.nodesOf.length with _ | m
    · simp [h0] at hcheck
    · exact ⟨m, rfl⟩
  rw [hlen] at hcheck hn hgen
  dsimp only at hcheck
  rcases hk : ksOf [c0, [1]] E m with η | g
  · simp [hk] at hcheck
  rw [hk] at hcheck
  have hb : frontSqrtPEWith [c0, [1]]
      (fun K _ m g A B kt l cq ↦ some (kxInputCheck c0 K m g A B kt l cq))
      E a e1 cs [] 0 (fun _ ↦ 0) = some true := by
    generalize frontSqrtPEWith [c0, [1]] _ E a e1 cs [] 0 (fun _ ↦ 0) = q at hcheck ⊢
    cases q <;> simpa using hcheck
  unfold frontSqrtPEWith at hb
  rw [hlen] at hb
  dsimp only at hb
  by_cases hcert : (curveShape [c0, [1]] &&
      certC [c0, [1]] (ksOf [c0, [1]] E) (lvOf [c0, [1]] E) (m + 1)) = true
  swap
  · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hcert)] at hb
    cases hb
  rw [if_neg (by rw [hcert]; decide)] at hb
  have hc := (Bool.and_eq_true_iff.mp hcert).2
  have hTr := (T.mspecs hmon hdeg (lvOf [c0, [1]] E) (m + 1) (by omega) hc).hyp.tr
  have hTm := hTr.of_succ
  rcases hqa : comp [c0, [1]] E.nodesOf (ksOf [c0, [1]] E) (m + 1) a with _ | qa
  · rw [hqa] at hb; cases hb
  rcases hq1 : comp [c0, [1]] E.nodesOf (ksOf [c0, [1]] E) (m + 1) e1 with _ | q1
  · rw [hqa, hq1] at hb; cases hb
  rcases hcq : allSomeL (cs.map fun c ↦ comp [c0, [1]] E.nodesOf
      (ksOf [c0, [1]] E) m c) with _ | cq
  · rw [hqa, hq1, hcq] at hb; cases hb
  rw [hqa, hq1, hcq] at hb
  dsimp only at hb
  let O := MO [c0, [1]] (ksOf [c0, [1]] E) m
  by_cases hd1 : degG O qa.2 ≠ 0 ∨ GPoly.isZero O qa.2 = true
  · rw [if_pos hd1] at hb; cases hb
  rw [if_neg hd1] at hb
  let A := qa.1.map (O.mul (O.inv (qa.2.getD 0 O.zero)))
  by_cases hd2 : (!GPoly.squarefreeCheck O A) = true ∨ degG O A % 2 = 0
  · rw [if_pos hd2] at hb; cases hb
  rw [if_neg hd2] at hb
  have hsqc : GPoly.squarefreeCheck O A = true := by
    have := (not_or.mp hd2).1
    simpa using this
  have hθA : θ ^ 2 = T.evP m A := by
    have hva := comp_spec [c0, [1]] T E.nodesOf (m + 1) hTr a qa hqa
    have hd1' := not_or.mp hd1
    rw [hθ, ← hva]
    exact (ev_constDen T m hTm qa (not_not.mp hd1'.1) (by simpa using hd1'.2)).symm
  rcases hD1 : divLins [c0, [1]] m (ksOf [c0, [1]] E) cq
      (stripG O A q1.2.length q1.2).1 with _ | D1
  · rw [hD1] at hb; cases hb
  rw [hD1] at hb
  dsimp only at hb
  rw [hk] at hb
  dsimp only at hb
  let st := stripG O (tX [c0, [1]] (ksOf [c0, [1]] E) m) D1.length D1
  by_cases hd3 : degG O st.1 ≠ 0 ∨ GPoly.isZero O st.1 = true
  · rw [if_pos hd3] at hb; cases hb
  rw [if_neg hd3] at hb
  let B := q1.1.map (O.mul (O.inv (st.1.getD 0 O.zero)))
  let l := (stripG O A q1.2.length q1.2).2
  have hinput : kxInputCheck c0 (ksOf [c0, [1]] E) m g A B st.2 l cq = true :=
    Option.some.inj hb
  obtain ⟨hdeg3, hr0, hok, hrep, hAw, hBw, hcsw, hgw⟩ :=
    (kxInputCheck_spec c0 (ksOf [c0, [1]] E) m g A B st.2 l cq).mp hinput
  obtain ⟨rs, Bd, hBd⟩ := T.kxDecideNC_decides c0 hmon hdeg m hn hc hk A hsqc hdeg3 θ hθA hgen B st.2 l cq
      hr0 hok hrep hAw hBw hcsw hgw
  obtain ⟨N, hN⟩ := hBd Bd le_rfl
  obtain ⟨K, hK⟩ := hN N le_rfl
  obtain ⟨b, hb, -⟩ := hK K le_rfl
  refine ⟨Bd, rs, N, K, b, ?_⟩
  dsimp only [O, A, B, st, l] at hd1 hd2 hd3 hD1 hb
  simpa only [frontSqrtPNCE, frontSqrtPEWith, hlen, hcert, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, hqa, hq1, hcq, hd1, hd2, hD1, hk, hd3] using hb

/-- The automatic expression search eventually decides every cubic input passing the check; no
mathematical hypothesis beyond a realization. -/
theorem frontSqrtPAutoE_decides (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (E a e1 : EE) (cs : List EE)
    (hcheck : frontSqrtPCubicCheck c0 E a e1 cs = true)
    (T : MTower [c0, [1]] (ksOf [c0, [1]] E) Cc L) (hn : T.n = E.nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE [c0, [1]] T E.nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F E.nodesOf.length) {θ}) :
    ∃ N0 b, (∀ N, N0 ≤ N → frontSqrtPAutoE c0 E a e1 cs N = some b) ∧
      (HasElementaryIntegral (evE [c0, [1]] T E.nodesOf e1 * θ) ↔ b = true) := by
  obtain ⟨Bd, rs, nmax, kmax, b, hb⟩ :=
    frontSqrtPCubicCheck_attempt c0 hmon hdeg E a e1 cs hcheck T hn θ hθ hgen
  obtain ⟨⟨N0, hN⟩, hs⟩ := frontSqrtPAutoE_decides_of_attempt c0 hmon hdeg E a e1 cs
    Bd rs nmax kmax b hb T hn θ hθ hgen
  exact ⟨N0, b, hN, hs⟩

/-- End-to-end eventual completeness for accepted cubic pole expressions. -/
theorem frontSqrtPAuto_decides (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (a e1 : EE) (cs : List EE)
    (hcheck : frontSqrtPCubicCheck c0 (spE a e1 cs) a e1 cs = true)
    (T : MTower [c0, [1]] (ksOf [c0, [1]] (spE a e1 cs)) Cc L)
    (hn : T.n = (spE a e1 cs).nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE [c0, [1]] T (spE a e1 cs).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (spE a e1 cs).nodesOf.length) {θ}) :
    ∃ N0 b, (∀ N, N0 ≤ N → frontSqrtPAuto c0 a e1 cs N = some b) ∧
      (HasElementaryIntegral (evE [c0, [1]] T (spE a e1 cs).nodesOf e1 * θ) ↔ b = true) :=
  frontSqrtPAutoE_decides c0 hmon hdeg _ a e1 cs hcheck T hn θ hθ hgen

end Curves.MT.Front
