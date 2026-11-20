import RischTragerBronstein.Mixed.FrontSqrt
import RischTragerBronstein.Mixed.FrontNK
import RischTragerBronstein.Mixed.KQMain
import RischTragerBronstein.Mixed.KXMain

/-!
# The square-root front end with poles

`frontSqrtPE a e₁ cs`: decides `∫ e₁ √a` when the denominator of `e₁` has, besides `Aˡ` (and `tᵏ`
below an exponential), the simple linear factors `t − c_q` for the poles `c_q` given as
expressions of the level below the top (`cs`), checked by exact divisions (`divLins`): below a
logarithm by `kqDecide`, below an exponential by `kxDecide`. `frontSqrtPE_sound`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- Divide exactly by `t − c` for every `c` in turn. -/
def divLins (m : ℕ) (K : (m : ℕ) → KindC m) : List (LC m) → GPoly (LC m) → Option (GPoly (LC m))
  | [], p => some p
  | c :: cs, p =>
    if GPoly.isZero (MO Fc K m) (GPoly.divMod (MO Fc K m) p (linG Fc K m c)).2 then
      divLins m K cs (GPoly.divMod (MO Fc K m) p (linG Fc K m c)).1
    else none

/-- The combined expression whose nodes make the tower. -/
def spE (a e1 : EE) (cs : List EE) : EE := EE.add (sqE a e1) (sumE cs)

/-- An exponential-level solver for the compiled square-root pole data. -/
abbrev SqrtPoleExpSolver :=
  ((m : ℕ) → KindC m) → ((m : ℕ) → LC m) →
    (m : ℕ) → LC m → GPoly (LC m) → GPoly (LC m) → ℕ → ℕ → List (LC m) → Option Bool

/-- The pole front end with a supplied exponential-level solver. -/
def frontSqrtPEWith (solve : SqrtPoleExpSolver) (E a e1 : EE) (cs : List EE)
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
      if !(GPoly.squarefreeCheck O A) ∨ degG O A % 2 = 0 then none else
      let sA := stripG O A q1.2.length q1.2
      match divLins Fc m K cq sA.1 with
      | none => none
      | some D1 =>
        match K m with
        | .exp g =>
          let st := stripG O (tX Fc K m) D1.length D1
          if degG O st.1 ≠ 0 ∨ GPoly.isZero O st.1 = true then none else
          solve K lv m g A (q1.1.map (O.mul (O.inv (st.1.getD 0 O.zero)))) st.2 sA.2 cq
        | .prim η =>
          if degG O D1 ≠ 0 ∨ GPoly.isZero O D1 = true then none else
          kqDecide Fc K lv m η A (q1.1.map (O.mul (O.inv (D1.getD 0 O.zero)))) sA.2 cq ps bound rs
    | _, _, _ => none

/-- The original pole front end, using the torsion-based exponential solver. -/
def frontSqrtPE (E a e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Option Bool :=
  frontSqrtPEWith Fc
    (fun K lv m g A B kt l cq ↦ kxDecide Fc K lv m g A B kt l cq ps bound rs)
    E a e1 cs ps bound rs

/-- **The front end for `∫ e₁ √a` with poles `cs`**, over the tower of `a`, `e₁` and the poles. -/
def frontSqrtP (a e1 : EE) (cs : List EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option Bool :=
  frontSqrtPE Fc (spE a e1 cs) a e1 cs ps bound rs

universe u

variable {Fc} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

section Values

variable (T : MTower Fc ks Cc L) (m : ℕ) (h : T.Tr m)
include h

lemma divLins_spec : ∀ (cs : List (LC m)) (p D : GPoly (LC m)), divLins Fc m ks cs p = some D →
    T.evP m p = T.evP m (prodLinG Fc ks m cs) * T.evP m D
  | [], p, D, hD => by
    simp only [divLins, Option.some.injEq] at hD
    subst hD
    rw [show prodLinG Fc ks m [] = [(MO Fc ks m).one] from rfl, evP_single Fc T m, T.ev_one_code m h, one_mul]
  | c :: cs, p, D, hD => by
    unfold divLins at hD
    split_ifs at hD with hz
    have hrec := divLins_spec cs _ D hD
    have hs := GPoly.divMod_spec (T.MP m h) p (linG Fc ks m c)
    rw [(GPoly.isZero_iff (T.MP m h) _).mp hz, add_zero] at hs
    have haev : ∀ q, T.evP m q = aeval (T.ts m) (GPoly.toPoly (T.MP m h) q) := fun q ↦
      (T.aeval_toPoly (T.MP m h) (T.sem_MP m h) q).symm
    rw [haev p, hs, map_mul, ← haev, ← haev, hrec, show prodLinG Fc ks m (c :: cs) =
      GPoly.mul (MO Fc ks m) (linG Fc ks m c) (prodLinG Fc ks m cs) from rfl, haev (GPoly.mul _ _ _),
      GPoly.toPoly_mul, map_mul, ← haev, ← haev]
    ring

/-- **Rescaling the numerator by a constant of the denominator.** -/
lemma ev_pair_scale (q : LC (m + 1)) (Den : GPoly (LC m)) (cc : LC m) (hc : T.ev m cc ≠ 0)
    (hD : T.evP m q.2 = T.evP m Den * T.ev m cc) :
    T.ev (m + 1) q =
      T.ev (m + 1) ((q.1.map ((MO Fc ks m).mul ((MO Fc ks m).inv cc)), Den) : LC (m + 1)) := by
  have hinv : T.ev m ((MO Fc ks m).inv cc) = (T.ev m cc)⁻¹ := by
    rw [← T.sem_MP m h, (T.MP m h).sem_inv, IntermediateField.coe_inv, T.sem_MP m h]
  rw [show T.ev (m + 1) q = T.evP m q.1 / T.evP m q.2 from rfl, show T.ev (m + 1)
      ((q.1.map ((MO Fc ks m).mul ((MO Fc ks m).inv cc)), Den) : LC (m + 1)) =
      T.evP m (q.1.map ((MO Fc ks m).mul ((MO Fc ks m).inv cc))) / T.evP m Den from rfl,
    T.evP_mapMul m h, hinv, hD]
  by_cases hDen : T.evP m Den = 0
  · rw [hDen]; simp
  field_simp

end Values

/-- The correctness contract of an exponential solver on a fixed realization. -/
def SqrtPoleExpSound (solve : SqrtPoleExpSolver) (lv : (m : ℕ) → LC m)
    (T : MTower Fc ks Cc L) : Prop :=
  ∀ (m : ℕ), T.n = m + 1 → certC Fc ks lv (m + 1) = true →
    ∀ {g : LC m}, ks m = .exp g →
    ∀ (A : GPoly (LC m)), GPoly.squarefreeCheck (MO Fc ks m) A = true →
      0 < degG (MO Fc ks m) A → Nat.Coprime 2 (degG (MO Fc ks m) A) →
    ∀ (θ : L), θ ^ 2 = T.evP m A →
      (∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ}) →
    ∀ (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (b : Bool),
      solve ks lv m g A B kt l cs = some b →
      (HasElementaryIntegral (T.ev (m + 1)
        ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ) ↔ b = true)

/-- A sound exponential solver gives a sound expression front end: for every realization and
square root `θ` of `a` generating the extension, `∫ e₁ θ` is elementary iff the answer is `true`. -/
theorem frontSqrtPEWith_sound (solve : SqrtPoleExpSolver) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (E a e1 : EE) (cs : List EE)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool)
    (hb : frontSqrtPEWith Fc solve E a e1 cs ps bound rs = some b)
    (T : MTower Fc (ksOf Fc E) Cc L) (hn : T.n = E.nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE Fc T E.nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F E.nodesOf.length) {θ}) :
    SqrtPoleExpSound solve (lvOf Fc E) T →
    (HasElementaryIntegral (evE Fc T E.nodesOf e1 * θ) ↔ b = true) := by
  intro hsolve
  classical
  unfold frontSqrtPEWith at hb
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
    have hdec := hsolve m hn hc hkg A hsqc hdegpos hcop θ hθA hgen _ _ _ cq b hb
    rw [← hv1, ev_pair_scale T m hTm q1 (kxDen Fc (ksOf Fc E) m A
      (stripG (MO Fc (ksOf Fc E) m) (tX Fc (ksOf Fc E) m) D1.length D1).2
      (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).2 cq) _ hcne (by
      rw [hq2, hD1v]
      simp only [kxDen, haev (GPoly.mul _ _ _), GPoly.toPoly_mul, map_mul, ← haev,
        T.evP_monoG m hTm, T.evP_powG m hTm]
      ring)]
    exact hdec
  · -- below a logarithm
    rename_i η hkη
    by_cases hd3 : degG (MO Fc (ksOf Fc E) m) D1 ≠ 0 ∨
        GPoly.isZero (MO Fc (ksOf Fc E) m) D1 = true
    · rw [if_pos hd3] at hb; cases hb
    rw [if_neg hd3] at hb
    push Not at hd3
    obtain ⟨hcv, hcne⟩ := evP_const T m hTm D1 hd3.1 (by simpa using hd3.2)
    have hdec := T.kqDecide_correct hmon hdeg m hn hc hkη A hsqc hdegpos hcop θ hθA hgen _ _ cq
      ps bound rs b hb
    rw [← hv1, ev_pair_scale T m hTm q1 (GPoly.mul (MO Fc (ksOf Fc E) m)
      (prodLinG Fc (ksOf Fc E) m cq) (powG (MO Fc (ksOf Fc E) m) A _)) _ hcne (by
      rw [hq2, hcv, haev (GPoly.mul _ _ _), GPoly.toPoly_mul, map_mul, ← haev, ← haev,
        T.evP_powG m hTm]
      ring)]
    exact hdec

/-- Every answer of the original pole front end is correct. -/
theorem frontSqrtPE_sound (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (E a e1 : EE) (cs : List EE)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool) (hb : frontSqrtPE Fc E a e1 cs ps bound rs = some b)
    (T : MTower Fc (ksOf Fc E) Cc L) (hn : T.n = E.nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE Fc T E.nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F E.nodesOf.length) {θ}) :
    HasElementaryIntegral (evE Fc T E.nodesOf e1 * θ) ↔ b = true := by
  apply frontSqrtPEWith_sound _ hmon hdeg E a e1 cs ps bound rs b hb T hn θ hθ hgen
  intro m hn hc g hk A hsq hp hcop θ hθ hgen B kt l cq b hb
  exact T.kxDecide_correct hmon hdeg m hn hc hk A hsq hp hcop θ hθ hgen B kt l cq
    ps bound rs b hb

/-- **Every answer of `frontSqrtP` is correct.** -/
theorem frontSqrtP_sound (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (a e1 : EE) (cs : List EE)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool) (hb : frontSqrtP Fc a e1 cs ps bound rs = some b)
    (T : MTower Fc (ksOf Fc (spE a e1 cs)) Cc L) (hn : T.n = (spE a e1 cs).nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE Fc T (spE a e1 cs).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (spE a e1 cs).nodesOf.length) {θ}) :
    HasElementaryIntegral (evE Fc T (spE a e1 cs).nodesOf e1 * θ) ↔ b = true :=
  frontSqrtPE_sound hmon hdeg _ a e1 cs ps bound rs b hb T hn θ hθ hgen

end Curves.MT.Front
