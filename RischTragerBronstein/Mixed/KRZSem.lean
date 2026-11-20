import RischTragerBronstein.Mixed.KRBridge

/-!
# Radicals over an exponential level: the search for `z`

* `sem_halfFrN`: the potential `(1/n) a₀′/a₀`;
* `kr_z_facts`: a returned `z` has `zⁿ a₀ = κ ∈ ℚ`, `κ ≠ 0`;
* `kr_hns`: when nothing is returned, `a₀` has no `n`-th root in `Fₘ`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma halfFrN_ok (m n : ℕ) (h : T.Tr m) (a0 : LC m) : FRepOK (T.MP m h) (halfFrN Fc ks m n a0) := by
  intro cw hcw
  simp only [halfFrN, List.mem_singleton] at hcw
  subst hcw
  rw [T.sem_mcst, T.deriv_ratCast]

lemma sem_halfFrN (m n : ℕ) (h : T.Tr m) (a0 : LC m) :
    (((T.MP m h).sem (fCode (MO Fc ks m) (halfFrN Fc ks m n a0)) : T.F m) : L) =
      (1 / n : L) * logDeriv (T.ev m a0) := by
  rw [sem_fCode, logSumV]
  simp only [halfFrN, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    (T.MP m h).sem_zero, Derivation.map_zero, zero_add]
  rw [IntermediateField.coe_mul, T.coe_logDeriv_FX, T.sem_mcst, T.sem_MP m h]
  push_cast
  ring

lemma krZ_some {m n : ℕ} {A : GPoly (LC m)} {z : LC m} (h : krZ Fc ks lv m n A = some z) :
    ∃ q, (prdeC Fc ks lv m (halfFrN Fc ks m n (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) = some (q, z) := by
  unfold krZ at h
  obtain ⟨⟨q, z'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
  subst h2
  exact ⟨q, h1⟩

lemma krZ_none {m n : ℕ} {A : GPoly (LC m)} (h : krZ Fc ks lv m n A = none) :
    (prdeC Fc ks lv m (halfFrN Fc ks m n (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) = none := by
  unfold krZ at h
  exact Option.map_eq_none_iff.mp h

/-- **The kernel element**: `z ≠ 0` and `zⁿ a₀ = κ` (rational, non-zero). -/
theorem kr_z_facts (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m n : ℕ)
    (hn : 0 < n) (hTn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (A : GPoly (LC m))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) (z : LC m)
    (hfind : krZ Fc ks lv m n A = some z) :
    T.ev m z ≠ 0 ∧
      T.ev m z ^ n * T.ev m (A.getD 0 (MO Fc ks m).zero) =
        ((ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
          (A.getD 0 (MO Fc ks m).zero))).getD 0 : ℚ) ∧
      (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
          (A.getD 0 (MO Fc ks m).zero))).getD 0 ≠ 0 := by
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hTm : T.Tr m := MSm.hyp.tr
  obtain ⟨q, hq⟩ := krZ_some hfind
  set a0 := A.getD 0 (MO Fc ks m).zero
  have hmem := List.mem_of_find?_eq_some hq
  have hp := List.find?_some hq
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hp
  have hz0 : (T.MP m hTm).sem z ≠ 0 := fun h0 ↦ by
    rw [← (T.MP m hTm).isZero_iff] at h0; rw [h0] at hp; exact Bool.noConfusion hp
  have hsol := T.halfKer_sound (lv := lv) m hTm (halfFrN Fc ks m n a0)
    (MSm.rde _ (T.halfFrN_ok m n hTm a0)) _ hmem
  have hsolL := congrArg Subtype.val hsol
  rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, T.sem_halfFrN m n hTm,
    T.sem_MP m hTm, IntermediateField.coe_zero] at hsolL
  have hzL : T.ev m z ≠ 0 := by rw [← T.sem_MP m hTm]; exact fun h0 ↦ hz0 (Subtype.ext h0)
  have ha0v : (T.MP m hTm).sem a0 ≠ 0 := fun h0 ↦ by
    rw [← (T.MP m hTm).isZero_iff] at h0; rw [h0] at ha0; exact Bool.noConfusion ha0
  have haL : T.ev m a0 ≠ 0 := by rw [← T.sem_MP m hTm]; exact fun h0 ↦ ha0v (Subtype.ext h0)
  have hnL : (n : L) ≠ 0 := by exact_mod_cast hn.ne'
  have hcst : ((T.MP m hTm).sem ((MO Fc ks m).mul (powC (MO Fc ks m) z n) a0))′ = 0 := by
    apply Subtype.ext
    rw [MTower.coe_deriv, (T.MP m hTm).sem_mul, sem_powC, IntermediateField.coe_mul,
      IntermediateField.coe_pow, T.sem_MP m hTm, T.sem_MP m hTm, IntermediateField.coe_zero]
    rw [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul, nsmul_eq_mul]
    have hz' : (T.ev m z)′ = -(1 / n : L) * logDeriv (T.ev m a0) * T.ev m z := by
      linear_combination hsolL
    have hz'' : (n : L) * (T.ev m z)′ * T.ev m a0 = -(T.ev m a0)′ * T.ev m z := by
      rw [hz']; unfold logDeriv; field_simp
    rcases n with _ | n
    · omega
    rw [pow_succ]
    simp only [Nat.add_sub_cancel]
    push_cast at hz'' ⊢
    linear_combination (T.ev m z) ^ n * hz''
  have hκ := T.ratValC_of_const m hTm _ hcst
  have hκL := congrArg Subtype.val hκ
  rw [(T.MP m hTm).sem_mul, sem_powC, IntermediateField.coe_mul, IntermediateField.coe_pow,
    T.sem_MP m hTm, T.sem_MP m hTm] at hκL
  push_cast at hκL
  refine ⟨hzL, by rw [← hκL], fun h0 ↦ ?_⟩
  rw [h0, Rat.cast_zero] at hκL
  exact mul_ne_zero (pow_ne_zero _ hzL) haL hκL

/-- **No `n`-th root of `A(0)` in `Fₘ`** when `krZ` finds nothing. -/
theorem kr_hns (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m n : ℕ) (hn : 0 < n)
    (hTn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (A : GPoly (LC m))
    (hTm : T.Tr m) (ha0v : (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0)
    (hfind : krZ Fc ks lv m n A = none) (β₀ : AlgebraicClosure (T.F m))
    (hβ₀ : β₀ ^ n = algebraMap (T.F m) _ ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero))) :
    ∀ c : T.F m, algebraMap (T.F m) (AlgebraicClosure (T.F m)) c ≠ β₀ := by
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  set a0 := A.getD 0 (MO Fc ks m).zero with ha0def
  intro cc hcc
  have hc2 : cc ^ n = (T.MP m hTm).sem a0 := by
    apply (algebraMap (T.F m) (AlgebraicClosure (T.F m))).injective
    rw [map_pow, hcc, hβ₀]
  have hcc0 : cc ≠ 0 := fun h0 ↦ ha0v (by rw [← hc2, h0, zero_pow hn.ne'])
  obtain ⟨r, hr, hr0⟩ := T.halfKer_complete (lv := lv) m hTm (halfFrN Fc ks m n a0)
    (MSm.rde _ (T.halfFrN_ok m n hTm a0)) cc⁻¹ (inv_ne_zero hcc0) (by
      apply Subtype.ext
      have hsh := T.sem_halfFrN m n hTm a0
      rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, hsh,
        ← T.sem_MP m hTm a0, ← hc2]
      have hccL : ((cc : T.F m) : L) ≠ 0 := fun h0 ↦ hcc0 (Subtype.ext h0)
      have hnL : (n : L) ≠ 0 := by exact_mod_cast hn.ne'
      rw [IntermediateField.coe_inv, IntermediateField.coe_pow, logDeriv, Derivation.leibniz_inv,
        Derivation.leibniz_pow]
      simp only [smul_eq_mul, nsmul_eq_mul, IntermediateField.coe_zero]
      rcases n with _ | n
      · omega
      have hn1 : ((n : L) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      push_cast
      field_simp
      ring)
  have := List.find?_eq_none.mp (krZ_none hfind) r hr
  simp [hr0] at this

end MTower

end Curves.MT
