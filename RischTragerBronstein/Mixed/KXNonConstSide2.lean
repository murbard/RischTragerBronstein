import RischTragerBronstein.Mixed.KXConstAssemblyS
import RischTragerBronstein.Mixed.KXNonConstSide

/-!
# Side conditions of the level-`m + 1` searches for non-constant curves

`nonconst_sideS`: the side conditions of the level-`m + 1` Mordell–Weil searches (well-formedness,
non-vanishing at the poles, `κ ≠ 0`, `s ≠ 0`, the `z`-equation, the multiplicity gcd) and the
non-vanishing of the short-model discriminant, for arbitrary coefficients (`const_sideS` without the
rationality hypothesis).
-/

open Polynomial Differential IntermediateField Classical

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 4000000 in
/-- **The side conditions of the level-`m + 1` searches for arbitrary (non-constant) curves.** -/
theorem nonconst_sideS (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (m : ℕ) (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdeg3 : degG (MO Fc ks (m + 1)) A = 3)
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (hok : kxOK Fc ks (m + 1) A B kt l cs = true)
    (hcst : kxConst Fc ks (m + 1) g A B kt l cs = true) (hrep : kxRepOK Fc ks (m + 1) g A B kt l cs = true)
    (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]])
    (hAw : ∀ a ∈ A, WFm (MO Fc ks m) a) (hBw : ∀ b ∈ B, WFm (MO Fc ks m) b)
    (hcsw : ∀ c ∈ cs, WFm (MO Fc ks m) c) (hgw : WFm (MO Fc ks m) g)
    (z : LC (m + 1)) (hz : kxZ Fc ks lv (m + 1) A = some z) (h0 : T.Tr (m + 1))
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length) :
    (∀ i < 4, okS (Fc := Fc) m (aCS Fc ks m A i) = true) ∧
    (∀ b ∈ B, okS (Fc := Fc) m b = true) ∧
    (∀ q < cs.length, okS (Fc := Fc) m (kqC Fc ks (m + 1) cs q) = true) ∧
    (∀ q < cs.length, okS (Fc := Fc) m (kxD Fc ks (m + 1) g cs q) = true) ∧
    (∀ q < cs.length, (GPoly.toPoly (T.MP (m + 1) h0) B).eval (T.val (m + 1) (kqC Fc ks (m + 1) cs q)) ≠ 0) ∧
    kxKap Fc ks (m + 1) A z ≠ 0 ∧ sTS Fc ks m g A B kt l cs k ≠ 0 ∧
    T.val (m + 1) z ^ 2 * T.val (m + 1) (aCS Fc ks m A 0) = (kxKap Fc ks (m + 1) A z : T.F (m + 1)) ∧
    mGS Fc ks m g A B kt l cs k ≠ 0 ∧
    (let c := fun i ↦ T.val (m + 1) (aCS Fc ks m A i)
     4 * (c 1 * c 3 - c 2 ^ 2 / 3) ^ 3 +
      27 * (c 0 * c 3 ^ 2 - c 2 * c 1 * c 3 / 3 + 2 * c 2 ^ 3 / 27) ^ 2 ≠ 0) := by
  have MS := T.mspecs hmon hdeg lv (m + 2) (by omega) hc
  have hvL : ∀ q : LC (m + 1), ((T.val (m + 1) q : T.F (m + 1)) : L) = T.ev (m + 1) q := fun q ↦ by
    rw [← T.sem_MP_F (m + 1) h0, T.sem_MP (m + 1) h0]
  have hok0 := T.kxOK_spec (m + 1) h0 A B kt l cs hok
  have ha0 : (MO Fc ks (m + 1)).isZero (A.getD 0 (MO Fc ks (m + 1)).zero) = false := by
    cases h : (MO Fc ks (m + 1)).isZero (A.getD 0 (MO Fc ks (m + 1)).zero)
    · rfl
    · exact absurd (((T.MP (m + 1) h0).isZero_iff _).mp h) hok0.1
  obtain ⟨q1, hq1⟩ := kxZ_some hz
  obtain ⟨-, hzκ, hκ0⟩ := T.ke_z_facts hmon hdeg (m + 1) hn hc A ha0 q1 z hq1
  -- the multiplicity gcd
  have hmG : mGS Fc ks m g A B kt l cs k ≠ 0 := by
    obtain ⟨q0, hq0, hq0T⟩ := kxCls_mem_rep (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs _
      (List.getElem_mem (n := (k : ℕ)) k.2)
    have hm0 : kxMNm Fc ks (m + 1) g A B kt l cs q0 ≠ 0 := by
      intro h0'
      obtain ⟨-, hκ, hc0'⟩ := kxRep_spec (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs hrep q0 hq0
      have hm := kxMNm_eq (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs q0 hq0 hc0'
      rw [h0', Nat.cast_zero, eq_comm, mul_eq_zero] at hm
      rcases hm with h | h
      · exact (kxDenM_pos (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs).ne' (by exact_mod_cast h)
      · rw [h] at hκ; simp at hκ
        exact T.kxK_ne (m + 1) MS.hyp hk A B kt l cs hok hcst q0 hq0 hκ
    intro h0'
    have := foldr_gcd_zero _ h0' (mKcS Fc ks m g A B kt l cs k q0)
      (List.mem_map.mpr ⟨q0, List.mem_range.mpr hq0, rfl⟩)
    unfold mKcS at this
    rw [if_pos (by rw [List.getD_eq_getElem _ _ k.2, hq0T]; exact beq_self_eq_true _)] at this
    exact hm0 (by exact_mod_cast this)
  -- the discriminant
  have hdisc : (let c := fun i ↦ T.val (m + 1) (aCS Fc ks m A i)
      4 * (c 1 * c 3 - c 2 ^ 2 / 3) ^ 3 +
      27 * (c 0 * c 3 ^ 2 - c 2 * c 1 * c 3 / 3 + 2 * c 2 ^ 3 / 27) ^ 2 ≠ 0) := by
    intro c
    set P := GPoly.toPoly (T.MP (m + 1) h0) A with hP
    have hdeg3' : P.natDegree = 3 := by rw [hP, ← degG_eq (T.MP (m + 1) h0) A, hdeg3]
    have hcf : ∀ i, P.coeff i = c i := fun i ↦ by
      rw [hP, Tower.PrimN.coeff_toPoly_getD, T.sem_MP_F (m + 1) h0]; rfl
    have hPc := MTower.cubic_eq P hdeg3'
    rw [hcf 3, hcf 2, hcf 1, hcf 0] at hPc
    have hsq := GPoly.squarefreeCheck_sound (T.MP (m + 1) h0) hsqc
    rw [← hP, hPc] at hsq
    have hP0 : P ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hdeg3'; omega
    have hc3 : c 3 ≠ 0 := by
      rw [← hcf 3]
      have := leadingCoeff_ne_zero.mpr hP0
      rwa [leadingCoeff, hdeg3'] at this
    exact CubicDisc.short_disc_ne_zero _ _ _ _ hc3 hsq
  have hTm : T.Tr m := h0.of_succ
  refine ⟨fun i _ ↦ T.okS_of_WFm m hTm _ (T.WFm_getD m hTm A hAw i),
    fun b hb ↦ T.okS_of_WFm m hTm _ (hBw b hb),
    fun q _ ↦ T.okS_of_WFm m hTm _ (T.WFm_getD m hTm cs hcsw q),
    fun q _ ↦ T.okS_of_WFm m hTm _ (T.WFm_kxD m hTm g cs hgw hcsw q),
    fun q hq ↦ ?_, hκ0, prodSub_ne _ (kxGens_spec (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs).2 _,
    Subtype.ext ?_, hmG, hdisc⟩
  · rw [← T.sem_MP_F (m + 1) h0]; exact (hok0.2 q hq).2.2.2
  · push_cast; rw [hvL, hvL]; exact hzκ

end MTower

end Curves.MT

