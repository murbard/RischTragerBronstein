import RischTragerBronstein.Mixed.FrontExpr
import RischTragerBronstein.Mixed.KEMain
import RischTragerBronstein.Mixed.KPDecideMain2
import RischTragerBronstein.Mixed.SysPrim

/-!
# The front end with a square root over the top level

`frontSqrt a e₁`: decides `∫ e₁ √a` for expressions `a`, `e₁` in `x`, `y`, `exp`, `log`, when
`a` is a polynomial `A(t)` in the top generator `t` of the compiled tower (`a`'s denominator is a
constant), squarefree of odd degree, and the denominator of `e₁` is `c tᵏ Aˡ` below an exponential
(`keDecide`, also `A(0) ≠ 0`) or `c Aˡ` below a logarithm (`kpDecideK`, which always answers). The factors are found by
exact divisions (`stripG`). `frontSqrt_sound`: every answer is correct for every realization of
the compiled tower and every square root `θ` of `a` generating `L` over it.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

section Strip

variable {α : Type} (O : COps α)

/-- Divide by `d` as long as the division is exact, at most `fuel` times. -/
def stripG (d : GPoly α) : ℕ → GPoly α → GPoly α × ℕ
  | 0, p => (p, 0)
  | fuel + 1, p =>
    if GPoly.isZero O (GPoly.divMod O p d).2 then
      ((stripG d fuel (GPoly.divMod O p d).1).1, (stripG d fuel (GPoly.divMod O p d).1).2 + 1)
    else (p, 0)

lemma stripG_spec {K : Type*} [Field K] [Differential K] (M : CField α K O) (d : GPoly α) :
    ∀ fuel p, GPoly.toPoly M p =
      GPoly.toPoly M d ^ (stripG O d fuel p).2 * GPoly.toPoly M (stripG O d fuel p).1
  | 0, p => by simp [stripG]
  | fuel + 1, p => by
    unfold stripG
    split_ifs with h
    · have hs := GPoly.divMod_spec M p d
      rw [(GPoly.isZero_iff M _).mp h, add_zero] at hs
      rw [hs, stripG_spec M d fuel (GPoly.divMod O p d).1]
      ring
    · simp

/-- A polynomial code of degree `0` that is not zero is the constant `c ≠ 0`. -/
lemma toPoly_const {K : Type*} [Field K] [Differential K] (M : CField α K O) (p : GPoly α)
    (hd : degG O p = 0) (hz : GPoly.isZero O p = false) :
    GPoly.toPoly M p = Polynomial.C (M.sem (p.getD 0 O.zero)) ∧ M.sem (p.getD 0 O.zero) ≠ 0 := by
  have hne : GPoly.toPoly M p ≠ 0 := fun h0 ↦ by
    have := (GPoly.isZero_iff M p).mpr h0
    rw [hz] at this; cases this
  rw [degG_eq M] at hd
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hd
  rw [coeff_toPoly_sem] at hC
  refine ⟨hC, fun h0 ↦ hne ?_⟩
  rw [hC, h0, map_zero]

end Strip

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- The combined expression whose nodes make the tower. -/
def sqE (a e1 : EE) : EE := EE.add a e1

/-- **The front end for `∫ e₁ √a`** over the tower of the nodes of `E` (`a` a polynomial in the
top generator). -/
def frontSqrtE (E a e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  match E.nodesOf.length with
  | 0 => none
  | m + 1 =>
    let K := ksOf Fc E
    let lv := lvOf Fc E
    let O := MO Fc K m
    if !(curveShape Fc && certC Fc K lv (m + 1)) then none else
    match comp Fc E.nodesOf K (m + 1) a, comp Fc E.nodesOf K (m + 1) e1 with
    | some qa, some q1 =>
      if degG O qa.2 ≠ 0 ∨ GPoly.isZero O qa.2 = true then none else
      let A := qa.1.map (O.mul (O.inv (qa.2.getD 0 O.zero)))
      if !(GPoly.squarefreeCheck O A) ∨ degG O A % 2 = 0 then none else
      let sA := stripG O A q1.2.length q1.2
      match K m with
      | .exp g =>
        if O.isZero (A.getD 0 O.zero) = true then none else
        let st := stripG O (tX Fc K m) sA.1.length sA.1
        if degG O st.1 ≠ 0 ∨ GPoly.isZero O st.1 = true then none else
        keDecide Fc K lv m A (q1.1.map (O.mul (O.inv (st.1.getD 0 O.zero)))) st.2 sA.2 ps bound rs
      | .prim η =>
        if degG O sA.1 ≠ 0 ∨ GPoly.isZero O sA.1 = true then none else
        some (kpDecideK Fc K lv m 1 2 A (q1.1.map (O.mul (O.inv (sA.1.getD 0 O.zero)))) sA.2)
    | _, _ => none

/-- **The front end for `∫ e₁ √a`** (`a` a polynomial in the top generator). -/
def frontSqrt (a e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  frontSqrtE Fc (sqE a e1) a e1 ps bound rs

universe u

variable {Fc} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

section Values

variable (T : MTower Fc ks Cc L) (m : ℕ) (h : T.Tr m)
include h

/-- The value of a code of degree `0`. -/
lemma evP_const (p : GPoly (LC m)) (hd : degG (MO Fc ks m) p = 0)
    (hz : GPoly.isZero (MO Fc ks m) p = false) :
    T.evP m p = T.ev m (p.getD 0 (MO Fc ks m).zero) ∧ T.ev m (p.getD 0 (MO Fc ks m).zero) ≠ 0 := by
  obtain ⟨hC, hne⟩ := toPoly_const (MO Fc ks m) (T.MP m h) p hd hz
  rw [← T.aeval_toPoly (T.MP m h) (T.sem_MP m h), hC, aeval_C, IntermediateField.algebraMap_apply,
    T.sem_MP m h]
  refine ⟨rfl, fun h0 ↦ hne (Subtype.ext ?_)⟩
  rw [T.sem_MP m h]; exact h0

/-- **The value of a fraction with constant denominator**: `p/c = (c⁻¹ p)`. -/
lemma ev_constDen (q : LC (m + 1)) (hd : degG (MO Fc ks m) q.2 = 0)
    (hz : GPoly.isZero (MO Fc ks m) q.2 = false) :
    T.evP m (q.1.map ((MO Fc ks m).mul ((MO Fc ks m).inv (q.2.getD 0 (MO Fc ks m).zero)))) =
      T.ev (m + 1) q := by
  obtain ⟨hv, hne⟩ := evP_const T m h q.2 hd hz
  rw [T.evP_mapMul m h, show T.ev (m + 1) q = T.evP m q.1 / T.evP m q.2 from rfl, hv,
    ← T.sem_MP m h, (T.MP m h).sem_inv, IntermediateField.coe_inv, T.sem_MP m h]
  rw [div_eq_inv_mul]

/-- **The value of a fraction with denominator `c tᵏ Aˡ`.** -/
lemma ev_stripE (q : LC (m + 1)) (A : GPoly (LC m)) (f1 f2 : ℕ)
    (hd : degG (MO Fc ks m) (stripG (MO Fc ks m) (tX Fc ks m) f2
      (stripG (MO Fc ks m) A f1 q.2).1).1 = 0)
    (hz : GPoly.isZero (MO Fc ks m) (stripG (MO Fc ks m) (tX Fc ks m) f2
      (stripG (MO Fc ks m) A f1 q.2).1).1 = false) :
    T.ev (m + 1) q = T.evP m (q.1.map ((MO Fc ks m).mul ((MO Fc ks m).inv
      ((stripG (MO Fc ks m) (tX Fc ks m) f2 (stripG (MO Fc ks m) A f1 q.2).1).1.getD 0
        (MO Fc ks m).zero)))) /
      (T.ts m ^ (stripG (MO Fc ks m) (tX Fc ks m) f2 (stripG (MO Fc ks m) A f1 q.2).1).2 *
        T.evP m A ^ (stripG (MO Fc ks m) A f1 q.2).2) := by
  set O := MO Fc ks m
  set sA := stripG O A f1 q.2
  set st := stripG O (tX Fc ks m) f2 sA.1
  obtain ⟨hv, hne⟩ := evP_const T m h st.1 hd hz
  have haev : ∀ p, T.evP m p = aeval (T.ts m) (GPoly.toPoly (T.MP m h) p) := fun p ↦
    (T.aeval_toPoly (T.MP m h) (T.sem_MP m h) p).symm
  have h1 := stripG_spec O (T.MP m h) A f1 q.2
  have h2 := stripG_spec O (T.MP m h) (tX Fc ks m) f2 sA.1
  have hden : T.evP m q.2 = T.evP m A ^ sA.2 * (T.ts m ^ st.2 * T.ev m (st.1.getD 0 O.zero)) := by
    rw [haev q.2, h1, map_mul, map_pow, h2, map_mul, map_pow, T.toPoly_tX m h, aeval_X, ← haev A,
      ← haev st.1, hv]
  have hinv : T.ev m (O.inv (st.1.getD 0 O.zero)) = (T.ev m (st.1.getD 0 O.zero))⁻¹ := by
    rw [← T.sem_MP m h, (T.MP m h).sem_inv, IntermediateField.coe_inv, T.sem_MP m h]
  rw [show T.ev (m + 1) q = T.evP m q.1 / T.evP m q.2 from rfl, hden, T.evP_mapMul m h, hinv]
  field_simp

/-- **The value of a fraction with denominator `c Aˡ`.** -/
lemma ev_stripP (q : LC (m + 1)) (A : GPoly (LC m)) (f1 : ℕ)
    (hd : degG (MO Fc ks m) (stripG (MO Fc ks m) A f1 q.2).1 = 0)
    (hz : GPoly.isZero (MO Fc ks m) (stripG (MO Fc ks m) A f1 q.2).1 = false) :
    T.ev (m + 1) q = T.evP m (q.1.map ((MO Fc ks m).mul ((MO Fc ks m).inv
      ((stripG (MO Fc ks m) A f1 q.2).1.getD 0 (MO Fc ks m).zero)))) /
      T.evP m A ^ (stripG (MO Fc ks m) A f1 q.2).2 := by
  set O := MO Fc ks m
  set sA := stripG O A f1 q.2
  obtain ⟨hv, hne⟩ := evP_const T m h sA.1 hd hz
  have haev : ∀ p, T.evP m p = aeval (T.ts m) (GPoly.toPoly (T.MP m h) p) := fun p ↦
    (T.aeval_toPoly (T.MP m h) (T.sem_MP m h) p).symm
  have h1 := stripG_spec O (T.MP m h) A f1 q.2
  have hden : T.evP m q.2 = T.evP m A ^ sA.2 * T.ev m (sA.1.getD 0 O.zero) := by
    rw [haev q.2, h1, map_mul, map_pow, ← haev A, ← haev sA.1, hv]
  have hinv : T.ev m (O.inv (sA.1.getD 0 O.zero)) = (T.ev m (sA.1.getD 0 O.zero))⁻¹ := by
    rw [← T.sem_MP m h, (T.MP m h).sem_inv, IntermediateField.coe_inv, T.sem_MP m h]
  rw [show T.ev (m + 1) q = T.evP m q.1 / T.evP m q.2 from rfl, hden, T.evP_mapMul m h, hinv]
  field_simp

end Values

section Sound

/-- **Every answer of `frontSqrtE` is correct**: for every realization `T` of the compiled tower
and every square root `θ` of `a` generating `L` over it, `∫ e₁ θ` is elementary iff the answer
is `true`. -/
theorem frontSqrtE_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (E a e1 : EE)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool) (hb : frontSqrtE Fc E a e1 ps bound rs = some b)
    (T : MTower Fc (ksOf Fc E) Cc L) (hn : T.n = E.nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE Fc T E.nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F E.nodesOf.length) {θ}) :
    HasElementaryIntegral (evE Fc T E.nodesOf e1 * θ) ↔ b = true := by
  classical
  unfold frontSqrtE at hb
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
  rw [hqa, hq1] at hb
  dsimp only at hb
  have hva := comp_spec Fc T E.nodesOf (m + 1) hTr a qa hqa
  have hv1 := comp_spec Fc T E.nodesOf (m + 1) hTr e1 q1 hq1
  by_cases hd1 : degG (MO Fc (ksOf Fc E) m) qa.2 ≠ 0 ∨ GPoly.isZero (MO Fc (ksOf Fc E) m) qa.2 = true
  · rw [if_pos hd1] at hb; cases hb
  rw [if_neg hd1] at hb
  push Not at hd1
  have hd1' : GPoly.isZero (MO Fc (ksOf Fc E) m) qa.2 = false := by simpa using hd1.2
  set A := qa.1.map ((MO Fc (ksOf Fc E) m).mul ((MO Fc (ksOf Fc E) m).inv (qa.2.getD 0 (MO Fc (ksOf Fc E) m).zero))) with hA
  by_cases hd2 : (!GPoly.squarefreeCheck (MO Fc (ksOf Fc E) m) A) = true ∨ degG (MO Fc (ksOf Fc E) m) A % 2 = 0
  · rw [if_pos hd2] at hb; cases hb
  rw [if_neg hd2] at hb
  push Not at hd2
  have hθA : θ ^ 2 = T.evP m A := by
    rw [hθ, ← hva, hA, ev_constDen T m hTm qa hd1.1 hd1']
  have hsqc : GPoly.squarefreeCheck (MO Fc (ksOf Fc E) m) A = true := by simpa using hd2.1
  have hodd : degG (MO Fc (ksOf Fc E) m) A % 2 = 1 := by omega
  have hdegpos : 0 < degG (MO Fc (ksOf Fc E) m) A := by omega
  have hcop : Nat.Coprime 2 (degG (MO Fc (ksOf Fc E) m) A) := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd)
  split at hb
  · -- below an exponential
    rename_i g hkg
    by_cases hz : (MO Fc (ksOf Fc E) m).isZero (A.getD 0 (MO Fc (ksOf Fc E) m).zero) = true
    · rw [if_pos hz] at hb; cases hb
    rw [if_neg hz] at hb
    by_cases hd3 : degG (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) (tX Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1.length
        (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1).1 ≠ 0 ∨ GPoly.isZero (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) (tX Fc (ksOf Fc E) m)
        (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1.length (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1).1 = true
    · rw [if_pos hd3] at hb; cases hb
    rw [if_neg hd3] at hb
    push Not at hd3
    have ha0 : (MO Fc (ksOf Fc E) m).isZero (A.getD 0 (MO Fc (ksOf Fc E) m).zero) = false := by simpa using hz
    have hz3 : GPoly.isZero (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) (tX Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1.length
        (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1).1 = false := by simpa using hd3.2
    have hdec := T.keDecide_correct hmon hdeg m hn hc hkg A hsqc hdegpos hcop ha0 θ hθA hgen _ _ _
      ps bound rs b hb
    rw [← hv1, ev_stripE T m hTm q1 A _ _ hd3.1 hz3]
    exact hdec
  · -- below a logarithm
    rename_i η hkη
    by_cases hd3 : degG (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1 ≠ 0 ∨
        GPoly.isZero (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1 = true
    · rw [if_pos hd3] at hb; cases hb
    rw [if_neg hd3] at hb
    push Not at hd3
    have hz3 : GPoly.isZero (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1 = false := by simpa using hd3.2
    obtain rfl := (Option.some.inj hb).symm
    have hdec := T.kp_decides_pow hmon hdeg m hn hc hkη A 2 two_pos hsqc hdegpos hcop θ hθA hgen
      1 one_pos one_lt_two (q1.1.map ((MO Fc (ksOf Fc E) m).mul
        ((MO Fc (ksOf Fc E) m).inv ((stripG (MO Fc (ksOf Fc E) m) A q1.2.length
          q1.2).1.getD 0 (MO Fc (ksOf Fc E) m).zero))))
      (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).2
    rw [pow_one] at hdec
    rw [← hv1, ev_stripP T m hTm q1 A _ hd3.1 hz3]
    exact hdec

/-- **Every answer of `frontSqrt` is correct**: for every realization `T` of the compiled tower
and every square root `θ` of `a` generating `L` over it, `∫ e₁ θ` is elementary iff the answer
is `true`. -/
theorem frontSqrt_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (a e1 : EE)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool) (hb : frontSqrt Fc a e1 ps bound rs = some b)
    (T : MTower Fc (ksOf Fc (sqE a e1)) Cc L) (hn : T.n = (sqE a e1).nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE Fc T (sqE a e1).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (sqE a e1).nodesOf.length) {θ}) :
    HasElementaryIntegral (evE Fc T (sqE a e1).nodesOf e1 * θ) ↔ b = true :=
  frontSqrtE_sound hmon hdeg (sqE a e1) a e1 ps bound rs b hb T hn θ hθ hgen

end Sound

end Curves.MT.Front
