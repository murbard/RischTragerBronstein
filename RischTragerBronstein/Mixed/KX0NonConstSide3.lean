import RischTragerBronstein.Mixed.KX0NonConstSide2
import RischTragerBronstein.Mixed.KXConstAssembly

/-!
# Side conditions of the level-`0` searches for non-constant curves

`nonconst_side0`: `const_side` without the rationality hypothesis — well-formed codes, the poles
avoid `B = 0`, `κ ≠ 0`, `s ≠ 0`, the `z`-equation, the multiplicity gcd, and the non-vanishing of the
discriminant of the short model in `F₀`.
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
/-- **The side conditions of the level-`0` searches for arbitrary (non-constant) curves.** -/
theorem nonconst_side0 (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdeg3 : degG (MO Fc ks 0) A = 3)
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (hok : kxOK Fc ks 0 A B kt l cs = true)
    (hcst : kxConst Fc ks 0 g A B kt l cs = true) (hrep : kxRepOK Fc ks 0 g A B kt l cs = true)
    (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]])
    (hAw : ∀ a ∈ A, codeOKb a = true) (hBw : ∀ b ∈ B, codeOKb b = true)
    (hcsw : ∀ c ∈ cs, codeOKb c = true) (hgw : codeOKb g = true)
    (z : LC 0) (hz : kxZ Fc ks lv 0 A = some z) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length) :
    (∀ i < 4, codeOKb (aC Fc ks A i) = true) ∧
    (∀ q < cs.length, codeOKb (kqC Fc ks 0 cs q) = true) ∧
    (∀ q < cs.length, codeOKb (kxD Fc ks 0 g cs q) = true) ∧
    (∀ q < cs.length, (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 (kqC Fc ks 0 cs q)) ≠ 0) ∧
    kxKap Fc ks 0 A z ≠ 0 ∧ sT Fc ks g A B kt l cs k ≠ 0 ∧
    T.val 0 z ^ 2 * T.val 0 (aC Fc ks A 0) = (kxKap Fc ks 0 A z : T.F 0) ∧
    mG Fc ks g A B kt l cs k ≠ 0 ∧
    (let c := fun i ↦ T.val 0 (aC Fc ks A i)
     4 * (c 1 * c 3 - c 2 ^ 2 / 3) ^ 3 +
      27 * (c 0 * c 3 ^ 2 - c 2 * c 1 * c 3 / 3 + 2 * c 2 ^ 3 / 27) ^ 2 ≠ 0) := by
  have MS := T.mspecs hmon hdeg lv 1 (by omega) hc
  have hvL : ∀ q : LC 0, ((T.val 0 q : T.F 0) : L) = T.ev 0 q := fun q ↦ by
    rw [← T.sem_MP_F 0 h0, T.sem_MP 0 h0]
  have hok0 := T.kxOK_spec 0 h0 A B kt l cs hok
  have ha0 : (MO Fc ks 0).isZero (A.getD 0 (MO Fc ks 0).zero) = false := by
    cases h : (MO Fc ks 0).isZero (A.getD 0 (MO Fc ks 0).zero)
    · rfl
    · exact absurd (((T.MP 0 h0).isZero_iff _).mp h) hok0.1
  obtain ⟨q1, hq1⟩ := kxZ_some hz
  obtain ⟨-, hzκ, hκ0⟩ := T.ke_z_facts hmon hdeg 0 hn hc A ha0 q1 z hq1
  have hmG : mG Fc ks g A B kt l cs k ≠ 0 := by
    obtain ⟨q0, hq0, hq0T⟩ := kxCls_mem_rep (Fc := Fc) (ks := ks) 0 g A B kt l cs _
      (List.getElem_mem (n := (k : ℕ)) k.2)
    have hm0 : kxMNm Fc ks 0 g A B kt l cs q0 ≠ 0 := by
      intro h0'
      obtain ⟨-, hκ, hc0'⟩ := kxRep_spec (Fc := Fc) (ks := ks) 0 g A B kt l cs hrep q0 hq0
      have hm := kxMNm_eq (Fc := Fc) (ks := ks) 0 g A B kt l cs q0 hq0 hc0'
      rw [h0', Nat.cast_zero, eq_comm, mul_eq_zero] at hm
      rcases hm with h | h
      · exact (kxDenM_pos (Fc := Fc) (ks := ks) 0 g A B kt l cs).ne' (by exact_mod_cast h)
      · rw [h] at hκ; simp at hκ
        exact T.kxK_ne 0 MS.hyp hk A B kt l cs hok hcst q0 hq0 hκ
    intro h0'
    have := foldr_gcd_zero _ h0' (mKc Fc ks g A B kt l cs k q0)
      (List.mem_map.mpr ⟨q0, List.mem_range.mpr hq0, rfl⟩)
    unfold mKc at this
    rw [if_pos (by rw [List.getD_eq_getElem _ _ k.2, hq0T]; exact beq_self_eq_true _)] at this
    exact hm0 (by exact_mod_cast this)
  have hdisc : (let c := fun i ↦ T.val 0 (aC Fc ks A i)
      4 * (c 1 * c 3 - c 2 ^ 2 / 3) ^ 3 +
      27 * (c 0 * c 3 ^ 2 - c 2 * c 1 * c 3 / 3 + 2 * c 2 ^ 3 / 27) ^ 2 ≠ 0) := by
    intro c
    set P := GPoly.toPoly (T.MP 0 h0) A with hP
    have hdeg3' : P.natDegree = 3 := by rw [hP, ← degG_eq (T.MP 0 h0) A, hdeg3]
    have hcf : ∀ i, P.coeff i = c i := fun i ↦ by
      rw [hP, Tower.PrimN.coeff_toPoly_getD, T.sem_MP_F 0 h0]; rfl
    have hPc := MTower.cubic_eq P hdeg3'
    rw [hcf 3, hcf 2, hcf 1, hcf 0] at hPc
    have hsq := GPoly.squarefreeCheck_sound (T.MP 0 h0) hsqc
    rw [← hP, hPc] at hsq
    have hP0 : P ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hdeg3'; omega
    have hc3 : c 3 ≠ 0 := by
      rw [← hcf 3]
      have := leadingCoeff_ne_zero.mpr hP0
      rwa [leadingCoeff, hdeg3'] at this
    exact CubicDisc.short_disc_ne_zero _ _ _ _ hc3 hsq
  refine ⟨fun i _ ↦ codeOKb_getD A hAw i, fun q _ ↦ codeOKb_getD cs hcsw q, fun q _ ↦ ?_,
    fun q hq ↦ ?_, hκ0, prodSub_ne _ (kxGens_spec (Fc := Fc) (ks := ks) 0 g A B kt l cs).2 _,
    Subtype.ext ?_, hmG, hdisc⟩
  · subst hFc; exact codeOKb_kxD c0f ks g cs hgw hcsw q
  · rw [← T.sem_MP_F 0 h0]; exact (hok0.2 q hq).2.2.2
  · push_cast; rw [hvL, hvL]; exact hzκ

end MTower

end Curves.MT
