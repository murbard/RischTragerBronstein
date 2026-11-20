import RischTragerBronstein.Mixed.KQMain
import RischTragerBronstein.Mixed.KFSpecExist

/-!
# Square roots over a logarithmic level with poles: the decision always answers

`kqDecideL` (local torsion certificates) answers for every large bound at suitable residues
(`kqDecideL_decides`), for accepted data (`cs ≠ []`, `kqOK`, one residue class when the squared
residues are constant); with `kqDecideC_correct` these integrals are **decided** (`kq_decided`).
The points `(c_q, β_q)` lie on `y² = κ₀ A` without adjoining `√κ₀` (`kq_points`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The poles give points of `y² = κ₀ A`.** -/
theorem kq_points [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η) (hTm : T.Tr m)
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hok : kqOK Fc ks m A B l cs = true)
    (hcst : kqConst Fc ks m η A B l cs = true) (hcl : kqClass Fc ks m η A B l cs = true)
    (hr : 0 < cs.length) (q : Fin cs.length) :
    (T.MP m hTm).sem (kqB Fc ks m η A B l cs q) ≠ 0 ∧
      (T.MP m hTm).sem (kqB Fc ks m η A B l cs q) ^ 2 =
        (Polynomial.C ((kqK Fc ks m η A B l cs 0 : ℚ) : T.F m) * GPoly.toPoly (T.MP m hTm) A).eval
          ((T.MP m hTm).sem (kqC Fc ks m cs q)) := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hok' := fun q' (hq' : q' < cs.length) ↦ T.kqOK_spec m hTm A B l cs hok q' hq'
  set κ : ℕ → ℚ := kqK Fc ks m η A B l cs with hκ
  set c : ℕ → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcdef
  set d : ℕ → T.F m := fun q ↦ (T.MP m hTm).sem (kqD Fc ks m η cs q) with hddef
  set Rt : ℕ → T.F m := fun q ↦ (T.MP m hTm).sem (kqR Fc ks m A l cs q) with hRt
  set Bc : ℕ → T.F m := fun q ↦ (GPoly.toPoly (T.MP m hTm) B).eval (c q) with hBc
  set Ac : ℕ → T.F m := fun q ↦ (GPoly.toPoly (T.MP m hTm) A).eval (c q) with hAc
  have hd0 : ∀ q, d q ≠ 0 := fun q h0 ↦ by
    simp only [hddef, T.sem_kqD m hTm, T.sem_eq_val m hTm η] at h0
    exact T.kqS_good m MS.hyp hk (algebraMap (T.F m) _ (c q))
      (by rw [deriv_algebraMap, ← sub_eq_zero.mp h0])
  have hQv : ∀ q < cs.length, (κ q : T.F m) = Bc q ^ 2 * Ac q / (d q * Rt q) ^ 2 := fun q hq ↦ by
    rw [← T.kqConst_spec m hTm η A B l cs hcst q hq, T.sem_kqQ m hTm]
  have hκ0 : ∀ q < cs.length, κ q ≠ 0 := fun q hq ↦ T.kqK_ne m MS.hyp hk A B l cs hok hcst q hq
  have hq := q.2
  obtain ⟨hm2, -⟩ := kqClass_spec m η A B l cs hcl q hq
  rw [T.sem_kqB m hTm, eval_mul, eval_C]
  have hQ := hQv q hq
  have hB0 := (hok' q hq).2.2
  have hR0 := (hok' q hq).1
  have hk0 : (κ 0 : T.F m) ≠ 0 := by exact_mod_cast hκ0 0 hr
  have hmq : (kqM Fc ks m η A B l cs q : T.F m) ^ 2 = (κ q : T.F m) / (κ 0 : T.F m) := by
    rw [← Rat.cast_pow, hm2]; push_cast; rfl
  have hm0 : (kqM Fc ks m η A B l cs q : T.F m) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero, eq_comm, div_eq_zero_iff] at hmq
    rcases hmq with h | h
    · exact hκ0 q hq (by exact_mod_cast h)
    · exact hk0 h
  refine ⟨?_, ?_⟩
  · push_cast
    exact mul_ne_zero (mul_ne_zero hk0 hm0) (div_ne_zero (mul_ne_zero (hd0 q) hR0) hB0)
  · push_cast
    rw [mul_pow, mul_pow, hmq, hQ]
    have hd0q := hd0 q
    simp only [hddef, hRt, hBc, hAc, hcdef, hκ] at hd0q hR0 hB0 ⊢
    field_simp

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`kqDecideL` answers** for every large bound, at suitable residues (accepted data). -/
theorem kqDecideL_decides [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hr0 : cs.length ≠ 0)
    (hok : kqOK Fc ks m A B l cs = true)
    (hcl : kqConst Fc ks m η A B l cs = true → kqClass Fc ks m η A B l cs = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (kqDecideL Fc ks lv m η A B l cs (primesBelow Bd) Bd rs).isSome := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hr : 0 < cs.length := Nat.pos_of_ne_zero hr0
  unfold kqDecideL kqDecideC
  dsimp only
  simp only [if_neg hr0, hok, Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hcst : kqConst Fc ks m η A B l cs = true
  swap
  · refine ⟨fun _ ↦ 0, 0, fun _ _ ↦ ?_⟩
    rw [if_pos (by simpa using hcst)]; rfl
  have hcl' := hcl hcst
  simp only [hcst, hcl', Bool.not_true, Bool.false_eq_true, if_false]
  -- the curve and the points over `Kₘ`
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hκ0 := T.kqK_ne m MS.hyp hk A B l cs hok hcst 0 hr
  set κc : T.F m := ((kqK Fc ks m η A B l cs 0 : ℚ) : T.F m)
  have hκc : κc ≠ 0 := by simp only [κc]; exact_mod_cast hκ0
  set p := Polynomial.C κc * GPoly.toPoly (T.MP m hTm) A
  have hpf : p = (toPoly (kqFK Fc ks m η A B l cs)).map (T.psiF m hTm) := by
    rw [kqFK, CPoly.toPoly_trim, T.toPoly_trC_map m hTm, T.toPoly_kqAhat m hTm]
  have hsqp : Squarefree p :=
    (Associated.squarefree_iff (associated_unit_mul_left _ (Polynomial.C κc)
      (isUnit_C.mpr (Ne.isUnit hκc)))).mpr hsq
  have hcopp : Nat.Coprime 2 p.natDegree := by
    rw [natDegree_C_mul hκc, hdeg1]; exact hcop
  obtain ⟨hd, hsqK, hcop2, hvK, hinjK, -, -⟩ := T.kq_KF_facts m hTm η A B l cs p hpf hsqp hcopp
    (fun q ↦ T.kq_points hmon hdeg m hn hc hk hTm A B l cs hok hcst hcl' hr q)
    (T.kq_cinj m hTm A B l cs hok)
  set fK := kqFK Fc ks m η A B l cs with hfK
  have hne : toPoly fK ≠ 0 := fun h0 ↦ hsqK.ne_zero h0
  have hdpos : 0 < fK.length - 1 := by
    rw [← hd, ← natDegree_map_eq_of_injective (T.psiF m hTm).injective, ← hpf,
      natDegree_C_mul hκc, hdeg1]
    exact hdegpos
  have hlc : fK.getD (fK.length - 1) 0 ≠ 0 := by
    rw [← coeff_toPoly, ← hd]; exact leadingCoeff_ne_zero.mpr hne
  obtain ⟨rs, B0, hB0⟩ := kf_torsLocal_exists_gamma Fc m hdpos hlc hsqK hcop2
    (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs) (kqMq Fc ks m η A B l cs) hvK hinjK
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  have hsome := hB0 Bd hBd
  have hspec := torsOracleC_spec (redAtKF Fc m rs) (localCert fK 2)
    (fun p _ R h ↦ redAtKF_valid Fc m rs p R h) (primesBelow Bd) Bd hsqK hcop2
  rcases htors : torsOracleC (redAtKF Fc m rs) (localCert fK 2) (primesBelow Bd) Bd fK 2
      (Sup.gammaL (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs) (kqMq Fc ks m η A B l cs) 1)
    with _ | _ | N
  · rw [htors] at hsome; exact absurd hsome (by simp)
  · simp only [Option.isSome_some]
  · have hP := ((hspec cs.length (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs)
      (kqMq Fc ks m η A B l cs) hvK hinjK).1 N htors).2
    have hw := witW_ne_none fK 2 two_pos (fK.length - 1) (kqAl Fc ks m cs)
      (kqBe Fc ks m η A B l cs) (kqMq Fc ks m η A B l cs) N
      (fun q ↦ ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) (hvK q).1, (hvK q).2⟩) hP
    rcases hwit : witW fK 2 (fK.length - 1) (kqAl Fc ks m cs) (kqBe Fc ks m η A B l cs)
      (kqMq Fc ks m η A B l cs) N with _ | Wb
    · exact absurd hwit hw
    · dsimp only
      rw [hwit]; rfl

open Classical in
/-- **Square roots over a logarithmic level with poles are decided** (accepted data): at suitable
residues, for every large bound `kqDecideL` answers, and its answer is correct. -/
theorem kq_decided [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hr0 : cs.length ≠ 0)
    (hok : kqOK Fc ks m A B l cs = true)
    (hcl : kqConst Fc ks m η A B l cs = true → kqClass Fc ks m η A B l cs = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd → ∃ b,
      kqDecideL Fc ks lv m η A B l cs (primesBelow Bd) Bd rs = some b ∧
      (HasElementaryIntegral (T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
        (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ) ↔ b = true) := by
  obtain ⟨rs, B0, h⟩ := T.kqDecideL_decides hmon hdeg m hn hc hk A hsqc hdegpos hcop B l cs hr0 hok
    hcl
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h Bd hBd)
  exact ⟨b, hb, T.kqDecideC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B l cs _ _
    rs _ b hb⟩

end MTower

end Curves.MT
