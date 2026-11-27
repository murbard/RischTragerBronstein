import RischTragerBronstein.Mixed.MTBaseLine
import RischTragerBronstein.Mixed.MTSound
import RischTragerBronstein.Mixed.KYBack
import RischTragerBronstein.Elementary.ConstExt

/-!
# A fast path for towers over the line

On the line `y = x` every level-`0` integrand is a rational function of `x`, hence elementary
(`MTower.line_hasElementaryIntegral`). `elMF` is `elM` with the level-`0` call of the
general-curve decision `decideTotal` replaced by `some true` on a line; `elMF_sound` proves every
answer correct (an answer of `elMF` is an answer of `elM` at some bound, `elMF_elM`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Every level-`0` integrand on a line has an elementary integral.** -/
theorem line_hasElementaryIntegral (hl : isLine Fc = true) (c : LC 0) :
    HasElementaryIntegral (T.ev 0 c) := by
  classical
  apply hasElementaryIntegral_of_liouvilleIn_constField (K := AlgebraicClosure L)
  rcases hb : baseRat Fc c with _ | ⟨I, R⟩
  · -- zero denominator: the value is `0`
    have hz : toPoly (lineEval Fc c).2 = 0 := by
      simp only [baseRat, hl, if_true] at hb
      split_ifs at hb with hz
      exact (CPoly.isZero_iff _).mp hz
    refine ⟨Fin 0, ∅, fun _ ↦ 0, fun _ ↦ 0, 0, by simp, zero_mem _, ?_⟩
    rw [T.ev0_lineEval hl, hz]
    simp
  · obtain ⟨hval, hsq, hdeg, hs0⟩ := T.baseRat_spec hl c I R hb
    set K := AlgebraicClosure L
    set xK : K := algebraMap L K T.S.x with hxK
    have hx' : xK′ = 1 := by rw [hxK, deriv_algebraMap, T.hx, map_one]
    have hst : aeval xK (toPoly I.s) ≠ 0 := by
      rw [hxK, aeval_algebraMap_apply]
      exact (map_ne_zero_iff _ (algebraMap L K).injective).mpr hs0
    obtain ⟨hc, heq⟩ := ratLog_explicit xK hx' (toPoly I.r) (toPoly I.s) hsq hdeg
      (IsAlgClosed.splits _) hst
    set S := ((toPoly I.s).map (algebraMap ℚ K)).roots.toFinset
    refine ⟨Fin S.card, Finset.univ,
      fun i ↦ aeval (S.equivFin.symm i : K) (toPoly I.r) /
        aeval (S.equivFin.symm i : K) (derivative (toPoly I.s)),
      fun i ↦ xK - (S.equivFin.symm i : K),
      algebraMap L K (aeval T.S.x (toPoly I.gn) / aeval T.S.x (toPoly I.gd) +
        aeval T.S.x (toPoly I.Q)), fun i _ ↦ ?_, IntermediateField.algebraMap_mem _ _, ?_⟩
    · have hi := (S.equivFin.symm i).2
      refine ⟨(hc _ hi).1, sub_mem (IntermediateField.algebraMap_mem _ _) ?_, (hc _ hi).2⟩
      apply mem_constField_of_deriv_eq_zero
      apply deriv_eq_zero_of_isAlgebraic
      have hroot : (S.equivFin.symm i : K) ∈ ((toPoly I.s).map (algebraMap ℚ K)).roots :=
        Multiset.mem_toFinset.mp hi
      refine ⟨toPoly I.s, hsq.ne_zero, ?_⟩
      have := (mem_roots'.mp hroot).2
      rwa [IsRoot.def, eval_map_algebraMap] at this
    · rw [hval, map_add, ← deriv_algebraMap, add_comm]
      congr 1
      rw [map_div₀, ← aeval_algebraMap_apply, ← aeval_algebraMap_apply, ← hxK, heq]
      rw [← Finset.sum_coe_sort S]
      exact (Equiv.sum_comp S.equivFin.symm _).symm

end MTower

open Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc ks) (lv : (m : ℕ) → LC m)

/-- One level of `elM`: a final answer, or the code to decide one level down. -/
def stepM (m : ℕ) (q : LC (m + 1)) : Bool ⊕ LC m :=
  let O := MO Fc ks m
  let q' : GFrac (LC m) := q
  if GPoly.isZero O q'.2 then .inl true
  else match ks m with
  | .prim η =>
    let w := wKC O (.prim η)
    let h := GPoly.hermite O w q'.1 q'.2
    let qr := GPoly.divMod O h.b h.s
    if !(GPoly.residueCheck O w qr.2 h.s) then .inl false
    else match mchain Fc ks lv m η qr.1 qr.1.length O.zero with
      | none => .inl false
      | some Q1 => .inr (mconst Fc ks m η qr.1 Q1)
  | .exp a =>
    let w := wKC O (.exp a)
    let sp := GPoly.expSplit O q'.1 q'.2
    let k := sp.2.2.1
    let h := GPoly.hermite O w sp.1 sp.2.2.2
    let qr := GPoly.divMod O h.b h.s
    let Λ := GPoly.add O (GPoly.mul O qr.1 (GPoly.monomial O k O.one)) sp.2.1
    if !(GPoly.residueCheck O w qr.2 h.s) then .inl false
    else if !((List.range (Λ.length + k + 1)).all fun j ↦
        decide (j = k) || rdeOKM Fc ks lv m (O.mul (mcst Fc ks m ((j : ℚ) - k)) a)
          (Λ.getD j O.zero)) then .inl false
    else .inr (Λ.getD k O.zero)

/-- **`elM` with the level-`0` decision on a line answered at once.** -/
def elMF : (m : ℕ) → LC m → ℕ → Option Bool
  | 0, q, N => if isLine Fc then some true
      else decideTotal Fc ((codeW (cvNorm Fc q)).map trim) (codeQ (cvNorm Fc q)) N
  | m + 1, q, N =>
    match stepM Fc ks lv m q with
    | .inl c => some c
    | .inr q' => elMF m q' N

variable {Fc ks lv}

/-- `elM` in terms of `stepM`. -/
lemma elM_succ (m : ℕ) (q : LC (m + 1)) (N : ℕ) :
    elM Fc ks lv (m + 1) q N = match stepM Fc ks lv m q with
      | .inl c => some c
      | .inr q' => elM Fc ks lv m q' N := by
  rw [elM]
  unfold stepM
  dsimp only
  by_cases hz : GPoly.isZero (MO Fc ks m) (q : GFrac (LC m)).2 = true
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz]
    cases ks m with
    | prim η =>
      dsimp only
      split_ifs with hr
      · rfl
      · split <;> (rename_i heq; simp only [heq])
    | exp a =>
      dsimp only
      split_ifs <;> rfl

/-- **An answer of the fast decider is an answer of `elM` at some bound**, provided `elM`
eventually answers `true` at level `0` on a line. -/
theorem elMF_elM (h0 : isLine Fc = true → ∀ q : LC 0, ∃ N', elM Fc ks lv 0 q N' = some true) :
    ∀ (m : ℕ) (q : LC m) (N : ℕ) (b : Bool), elMF Fc ks lv m q N = some b →
      ∃ N', elM Fc ks lv m q N' = some b := by
  intro m
  induction m with
  | zero =>
    intro q N b h
    unfold elMF at h
    by_cases hl : isLine Fc = true
    · rw [if_pos hl] at h
      obtain rfl := Option.some.inj h
      exact h0 hl q
    · rw [if_neg hl] at h
      exact ⟨N, h⟩
  | succ m ih =>
    intro q N b h
    rw [elMF] at h
    rcases hs : stepM Fc ks lv m q with c | q'
    · rw [hs] at h
      exact ⟨0, by rw [elM_succ, hs]; exact h⟩
    · rw [hs] at h
      obtain ⟨N', hN'⟩ := ih q' N b h
      exact ⟨N', by rw [elM_succ, hs]; exact hN'⟩

/-- **Every answer of the fast decider is correct.** -/
theorem elMF_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hsh : curveShape Fc = true) (T : MTower Fc ks Cc L) (k : ℕ) (hn : T.n = k)
    (hc : certC Fc ks lv k = true) (hgen : ∀ z : L, z ∈ T.F k) (q : LC k) (N : ℕ) (b : Bool)
    (h : elMF Fc ks lv k q N = some b) :
    (HasElementaryIntegral (T.ev k q) ↔ b = true) ∧
      (b = true → HasElementaryIntegralIn (T.ev k q)) := by
  have h0 : isLine Fc = true → ∀ q0 : LC 0, ∃ N', elM Fc ks lv 0 q0 N' = some true := by
    intro hl q0
    obtain ⟨T0, hT0n, hT0ev, hT0gen, -⟩ := T.exists_sub 0 (by omega)
    have hc0 : certC Fc ks lv 0 = true := MTower.certC_le hc 0 (Nat.zero_le k)
    obtain ⟨N₀, hN⟩ := elM_decides_any hmon hdeg hsh T0 0 hT0n hc0 hT0gen q0
    obtain ⟨b', hb', hiff, -⟩ := hN N₀ le_rfl
    have : b' = true := hiff.mp (T0.line_hasElementaryIntegral hl q0)
    exact ⟨N₀, this ▸ hb'⟩
  obtain ⟨N', hN'⟩ := elMF_elM h0 k q N b h
  exact elM_sound hmon hdeg hsh T k hn hc hgen q N' b hN'

end Curves.MT
