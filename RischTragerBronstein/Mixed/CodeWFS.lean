import RischTragerBronstein.Computable.GWF
import RischTragerBronstein.Mixed.KXCertBridgeS
import RischTragerBronstein.Mixed.KRGcdT

/-!
# Well-formed codes at the levels `m + 1`

A fraction code of level `m + 1` is well formed when its denominator is non-zero
(`WFm`). The operations of `COps.monomial` preserve this whenever the base operations have a
model (`pres_monomial`), so every code built from well-formed ones is well formed (e.g. `kxD`,
`okS_kxD`), and well-formed codes pass `okS` (`okS_of_WFm`); normalized codes are well formed
(`okS_normC`).
-/

open Polynomial

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

section Gen

variable {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

/-- A fraction code with a non-zero denominator. -/
def WFm (O : COps α) (q : GFrac α) : Prop := GPoly.isZero O q.2 = false

include M in
lemma isZero_mulG (p q : GPoly α) (hp : GPoly.isZero O p = false) (hq : GPoly.isZero O q = false) :
    GPoly.isZero O (GPoly.mul O p q) = false := by
  rw [Bool.eq_false_iff, Ne, GPoly.isZero_iff M] at hp hq ⊢
  rw [GPoly.toPoly_mul]
  exact mul_ne_zero hp hq

include M in
lemma isZero_oneG : GPoly.isZero O [O.one] = false := by
  rw [Bool.eq_false_iff, Ne, GPoly.isZero_iff M]
  simp [GPoly.toPoly_cons, M.sem_one]

include M in
/-- **The monomial operations preserve well-formedness.** -/
theorem pres_monomial (w : GPoly α) : (O.monomial w).Pres (WFm O) where
  zero := isZero_oneG (M := M)
  one := isZero_oneG (M := M)
  add a b ha hb := by
    show GPoly.isZero O (if GPoly.isZero O a.2 then b else if GPoly.isZero O b.2 then a else _).2 = false
    split_ifs
    · exact hb
    · exact ha
    · exact isZero_mulG (M := M) _ _ ha hb
  neg a ha := ha
  mul a b ha hb := isZero_mulG (M := M) _ _ ha hb
  inv a _ h0 := by
    show GPoly.isZero O a.1 = false
    simp only [COps.monomial, Bool.or_eq_false_iff] at h0
    exact h0.1
  deriv a ha := isZero_mulG (M := M) _ _ ha ha
  natCast _ := isZero_oneG (M := M)

end Gen

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

lemma pres_MO_succ (m : ℕ) (hm : T.Tr m) : (MO Fc ks (m + 1)).Pres (WFm (MO Fc ks m)) :=
  pres_monomial (M := T.MP m hm) _

/-- **Well-formed codes pass `okS`.** -/
lemma okS_of_WFm (m : ℕ) (hm : T.Tr m) (q : LC (m + 1)) (hq : WFm (MO Fc ks m) q) :
    okS (Fc := Fc) m q = true := by
  unfold okS trFr
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]
  intro h0
  apply Bool.eq_false_iff.mp hq
  rw [← CPoly.isZero_iff] at h0
  unfold GPoly.isZero
  unfold CPoly.isZero at h0
  rw [List.all_eq_true] at h0 ⊢
  intro c hc
  have := h0 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  simp only [decide_eq_true_eq] at this
  have hs : (T.MP m hm).sem c = 0 := by rw [← T.psiF_trC m hm, this, map_zero]
  exact ((T.MP m hm).isZero_iff c).mpr hs

/-- Normalized codes pass `okS`. -/
lemma okS_normC (m : ℕ) (hm : T.Tr m) (q : LC (m + 1)) : okS (Fc := Fc) m (normC Fc (m + 1) q) = true := by
  have hc := (RFC.canon_spec (K := KF Fc m) (trC Fc (m + 1) q)).1
  have e : ((RFC.canon (K := KF Fc m) (trC Fc (m + 1) q)).2.map (unTr Fc m)).map (trC Fc m) =
      (RFC.canon (K := KF Fc m) (trC Fc (m + 1) q)).2 := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (RFC.canon (K := KF Fc m) (trC Fc (m + 1) q)).2]
    exact List.map_congr_left fun y _ ↦ T.trC_unTr_T m hm y
  unfold okS trFr
  show (!CPoly.isZero (((RFC.canon (K := KF Fc m) (trC Fc (m + 1) q)).2.map (unTr Fc m)).map
    (trC Fc m))) = true
  rw [e, Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]
  exact hc


lemma WFm_getD (m : ℕ) (hm : T.Tr m) (l : List (LC (m + 1))) (hl : ∀ a ∈ l, WFm (MO Fc ks m) a)
    (i : ℕ) : WFm (MO Fc ks m) (l.getD i (MO Fc ks (m + 1)).zero) := by
  rcases Nat.lt_or_ge i l.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact hl _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ h]; exact (T.pres_MO_succ m hm).zero

/-- **`kxD` is well formed** when `g` and the poles are. -/
lemma WFm_kxD (m : ℕ) (hm : T.Tr m) (g : LC (m + 1)) (cs : List (LC (m + 1)))
    (hg : WFm (MO Fc ks m) g) (hcs : ∀ c ∈ cs, WFm (MO Fc ks m) c) (q : ℕ) :
    WFm (MO Fc ks m) (kxD Fc ks (m + 1) g cs q) := by
  have hP := T.pres_MO_succ m hm
  have hq := T.WFm_getD m hm cs hcs q
  unfold kxD subC
  exact hP.add _ _ (hP.mul _ _ (hP.deriv _ hg) hq) (hP.neg _ (hP.deriv _ hq))

end MTower

end Curves.MT
