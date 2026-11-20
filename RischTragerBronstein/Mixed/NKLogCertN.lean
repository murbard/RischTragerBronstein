import RischTragerBronstein.Mixed.NKLogCert
import RischTragerBronstein.Mixed.NKInf2N

/-!
# Logarithm certificates with algebraic residues

`nk_iffC` takes logarithms `∑ cⱼ log uⱼ` with `cⱼ ∈ ℚ`, so it covers only rational residues. Here the
coefficients lie in a number field `ℚ(α)`, `α` a root of a monic `μ ∈ ℤ[X]`: `cⱼ = ∑ₖ cⱼₖ αᵏ`
(`cⱼₖ ∈ ℚ`), and the logarithms are `N`-codes `uⱼ = ∑ₖ αᵏ Aⱼₖ(θ)` (as for the units of
`NKUnitN`). `logCertN` checks, for every `j`, `uⱼ vⱼ ≡ 1` (`unitCNL`: `vⱼ` with coefficients in `Fₘ₊₁`, so `uⱼ ≠ 0`) and
`uⱼ′ = (∑ₖ αᵏ gⱼₖ) uⱼ` (`logDerChkN`), and that `f − g − ∑ⱼ cⱼ ∑ₖ αᵏ gⱼₖ ≡ 0` as an `N`-code
modulo `μ(α)` and `P`. With `α` in the constants, `∫ f` is elementary iff `∫ g` is
(`nk_iffCN`), and `g` residue-free is decided by `nk_iffR`.
-/

open Polynomial Differential NCodes

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- One logarithm: the `N`-code `A` of `u`, the `N`-code `B` of `u⁻¹`, the `N`-code `g` of `u′/u`,
and the coefficient `c = ∑ₖ cₖ αᵏ`. -/
abbrev LogN (m : ℕ) :=
  List (List (GPoly (LC m))) × List (GPoly (LC (m + 1))) × List (GPoly (LC (m + 1))) × List ℚ

/-- `u v ≡ 1` for `u = ∑ αᵏ Aₖ` (polynomial codes) and `v = ∑ αᵏ Bₖ` (any coefficients). -/
def unitCNL (m : ℕ) (Pp : List (GPoly (LC m))) (μ : List ℤ) (As : List (List (GPoly (LC m))))
    (Bs : List (GPoly (LC (m + 1)))) : Bool :=
  let R := θOps Fc ks m
  let c := nRed R μ (nConv R (As.map (nkFl Fc ks m)) Bs)
  zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1)) (c.getD 0 []) [(MO Fc ks (m + 1)).one]) &&
  (List.range μ.length).all fun s ↦ s == 0 || zeroModC Fc ks m Pp (c.getD s [])

/-- `∑ⱼ cⱼ gⱼ` as an `N`-code (unreduced). -/
def logTotN (m : ℕ) (logs : List (LogN m)) : List (GPoly (LC (m + 1))) :=
  logs.foldr (fun l acc ↦ nAdd (θOps Fc ks m)
    (nConv (θOps Fc ks m) (l.2.2.2.map fun q ↦ [mcst Fc ks (m + 1) q]) l.2.2.1) acc) []

/-- **The logarithm certificate with algebraic coefficients.** -/
def logCertN (m : ℕ) (Pp : List (GPoly (LC m))) (μ : List ℤ) (fl gl : List (LC (m + 1)))
    (logs : List (LogN m)) (dθ wθ : GPoly (LC (m + 1))) : Bool :=
  let O1 := MO Fc ks (m + 1)
  let c := nRed (θOps Fc ks m) μ (logTotN Fc ks m logs)
  decide (0 < μ.length) &&
  (logs.all fun l ↦ unitCNL Fc ks m Pp μ l.1 l.2.1 && logDerChkN Fc ks m Pp μ l.1 l.2.2.1 dθ wθ) &&
  zeroModC Fc ks m Pp (GPoly.sub O1 (GPoly.sub O1 fl gl) (c.getD 0 [])) &&
  (List.range μ.length).all fun s ↦ s == 0 || zeroModC Fc ks m Pp (c.getD s [])

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Soundness of `unitCNL`**. -/
lemma unitCNL_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (μ : List ℤ) (hd : 0 < μ.length) (α : L)
    (hμ : α ^ μ.length + ∑ i ∈ Finset.range μ.length, (μ.getD i 0 : L) * α ^ i = 0)
    (As : List (List (GPoly (LC m)))) (Bs : List (GPoly (LC (m + 1))))
    (h : unitCNL Fc ks m Pp μ As Bs = true) :
    nVal (T.evθ m h1 θ) α (As.map (nkFl Fc ks m)) * nVal (T.evθ m h1 θ) α Bs = 1 := by
  have hS := T.evθ_RSem m h1 θ
  unfold unitCNL at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨h0, hs⟩ := h
  set c := nRed (θOps Fc ks m) μ (nConv (θOps Fc ks m) (As.map (nkFl Fc ks m)) Bs) with hc
  rw [← nVal_nConv hS, ← nVal_nRed hS α μ hd hμ, ← hc,
    nVal_eq_sum hS α c μ.length (length_nRed _ μ hd _)]
  rw [Finset.sum_eq_single 0 (fun s hsr hs0 ↦ by
      have := T.zeroModC_sound m h1 θ Pp _ hP ((hs s (Finset.mem_range.mp hsr)).resolve_left hs0)
      change α ^ s * T.evθ m h1 θ (c.getD s []) = 0
      rw [this, mul_zero]) (fun h ↦ absurd (Finset.mem_range.mpr hd) h)]
  have := T.zeroModC_sound m h1 θ Pp _ hP h0
  rw [evθ_MP, GPoly.toPoly_sub, map_sub, ← evθ_MP, ← evθ_MP, T.evθ_one_MO m h1 θ, sub_eq_zero]
    at this
  change α ^ 0 * T.evθ m h1 θ (c.getD 0 []) = 1
  rw [pow_zero, one_mul, this]

lemma evθ_mcst (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (q : ℚ) :
    T.evθ m h1 θ [mcst Fc ks (m + 1) q] = (q : L) := by
  rw [evθ_MP]
  simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, aeval_C]
  rw [T.sem_mcst (m + 1) h1 q]
  push_cast; rfl

/-- The value of a rational `N`-code at a constant `α` is a constant. -/
lemma deriv_nVal_rat (m : ℕ) (h1 : T.Tr (m + 1)) (θ α : L) (hα : α′ = 0) :
    ∀ cs : List ℚ, (nVal (T.evθ m h1 θ) α (cs.map fun q ↦ [mcst Fc ks (m + 1) q]))′ = 0
  | [] => by simp [nVal]
  | q :: cs => by
    simp only [List.map_cons, nVal, map_add, Derivation.leibniz, deriv_nVal_rat m h1 θ α hα cs,
      hα, smul_eq_mul, mul_zero, add_zero, T.evθ_mcst m h1 θ q]
    exact deriv_ratCast_any q

lemma nVal_logTotN (m : ℕ) (h1 : T.Tr (m + 1)) (θ α : L) :
    ∀ logs : List (LogN m), nVal (T.evθ m h1 θ) α (logTotN Fc ks m logs) =
      (logs.map fun l ↦ nVal (T.evθ m h1 θ) α (l.2.2.2.map fun q ↦ [mcst Fc ks (m + 1) q]) *
        nVal (T.evθ m h1 θ) α l.2.2.1).sum
  | [] => by simp [logTotN, nVal]
  | l :: logs => by
    have hS := T.evθ_RSem m h1 θ
    have ih := nVal_logTotN m h1 θ α logs
    simp only [logTotN, List.foldr_cons] at ih ⊢
    rw [nVal_nAdd hS, nVal_nConv hS, ih, List.map_cons, List.sum_cons]

/-- **Soundness of `logCertN`**: at every constant root `α` of `μ`, each `uⱼ ≠ 0` and
`f − g = ∑ⱼ cⱼ(α) uⱼ′/uⱼ`. -/
lemma logCertN_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (μ : List ℤ) (α : L) (hα : α′ = 0)
    (hμ : α ^ μ.length + ∑ i ∈ Finset.range μ.length, (μ.getD i 0 : L) * α ^ i = 0)
    (fl gl : List (LC (m + 1))) (logs : List (LogN m)) (dθ wθ : GPoly (LC (m + 1)))
    (h : logCertN Fc ks m Pp μ fl gl logs dθ wθ = true) :
    (∀ l ∈ logs, nVal (T.evθ m h1 θ) α (l.1.map (nkFl Fc ks m)) ≠ 0) ∧
    T.evθ m h1 θ fl - T.evθ m h1 θ gl =
      (logs.map fun l ↦ nVal (T.evθ m h1 θ) α (l.2.2.2.map fun q ↦ [mcst Fc ks (m + 1) q]) *
        logDeriv (nVal (T.evθ m h1 θ) α (l.1.map (nkFl Fc ks m)))).sum := by
  have hS := T.evθ_RSem m h1 θ
  unfold logCertN at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨hd, hl⟩, h0⟩, hs⟩ := h
  have hu : ∀ l ∈ logs, nVal (T.evθ m h1 θ) α (l.1.map (nkFl Fc ks m)) ≠ 0 := fun l hl' ↦
    left_ne_zero_of_mul_eq_one (T.unitCNL_sound m h1 θ Pp hP μ hd α hμ l.1 l.2.1 (hl l hl').1)
  refine ⟨hu, ?_⟩
  set c := nRed (θOps Fc ks m) μ (logTotN Fc ks m logs) with hc
  -- the value of the reduced total
  have hval : nVal (T.evθ m h1 θ) α c = T.evθ m h1 θ (c.getD 0 []) := by
    rw [nVal_eq_sum hS α c μ.length (length_nRed _ μ hd _)]
    rw [Finset.sum_eq_single 0 (fun s hsr hs0 ↦ by
        have := T.zeroModC_sound m h1 θ Pp _ hP ((hs s (Finset.mem_range.mp hsr)).resolve_left hs0)
        change α ^ s * T.evθ m h1 θ (c.getD s []) = 0
        rw [this, mul_zero]) (fun h ↦ absurd (Finset.mem_range.mpr hd) h)]
    change α ^ 0 * T.evθ m h1 θ (c.getD 0 []) = _
    rw [pow_zero, one_mul]
  have hz := T.zeroModC_sound m h1 θ Pp _ hP h0
  rw [evθ_MP, GPoly.toPoly_sub, GPoly.toPoly_sub, map_sub, map_sub, ← evθ_MP, ← evθ_MP,
    ← evθ_MP, ← hval, hc, nVal_nRed hS α μ hd hμ, T.nVal_logTotN m h1 θ α logs, sub_eq_zero] at hz
  rw [hz]
  congr 1
  refine List.map_congr_left fun l hl' ↦ ?_
  congr 1
  have hd' := T.logDerChkN_sound m h1 θ Pp hP μ hd α hα hμ l.1 l.2.2.1 dθ wθ (hl l hl').2
  rw [logDeriv, hd', mul_div_assoc, div_self (hu l hl'), mul_one]

set_option maxHeartbeats 4000000 in
-- the proof unfolds the tower specifications
/-- **The decision with an algebraic log certificate**: with `logCertN` making
`g = f − ∑ⱼ cⱼ uⱼ′/uⱼ` (`cⱼ ∈ ℚ(α)`, `α` a constant root of `μ`) residue-free (`resCert`), `∫ f` is
elementary iff `g − τ(g)/n` is exact and `τ(g)/n` is elementary. -/
theorem nk_iffCN (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fl : List (LC (m + 1))) (hfl : fl.length = Pp.length)
    (gp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp gp D kc U = true) (hgpl : gp.length = Pp.length)
    (μ : List ℤ) (α : Cc)
    (hαμ : α ^ μ.length + ∑ i ∈ Finset.range μ.length, (μ.getD i 0 : Cc) * α ^ i = 0)
    (logs : List (LogN m)) (dθ wθ : GPoly (LC (m + 1)))
    (hlog : logCertN Fc ks m Pp μ fl (nkFlR m gp D) logs dθ wθ = true)
    (res : Bool)
    (hres : exactG Fc ks m (primSysC Fc ks m η (paramLimC Fc ks lv m)) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFlR m gp D) (nkTau Fc ks m Pp.length (nkFlR m gp D) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
      ((T.MPr (m + 1) (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr).sem
        (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m gp D) s)) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  set αL := algebraMap Cc L α with hαL
  have hαc : αL′ = 0 := by rw [hαL, deriv_algebraMap, T.hC, map_zero]
  have hμL : αL ^ μ.length + ∑ i ∈ Finset.range μ.length, (μ.getD i 0 : L) * αL ^ i = 0 := by
    have := congrArg (algebraMap Cc L) hαμ
    simpa [map_add, map_sum, map_mul, map_pow, map_intCast] using this
  obtain ⟨hu0, hfg⟩ := T.logCertN_sound m hTr θ Pp hP μ αL hαc hμL fl _ logs dθ wθ hlog
  have hlen : ∀ (l : List (GPoly (LC m))) (D0 : GPoly (LC m)), (nkFlR m l D0).length = l.length :=
    fun l D0 ↦ List.length_map _
  have hev : ∀ (l : List (GPoly (LC m))) (D0 : GPoly (LC m)), l.length = Pp.length →
      T.evθ m hTr θ (nkFlR m l D0) =
        ∑ j ∈ Finset.range Pp.length, T.evP m (l.getD j []) / T.evP m D0 * θ ^ j := by
    intro l D0 hl
    rw [T.evθ_list, hlen, hl]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [T.sem_nkFlR m hTr l D0 j]
  rw [sub_eq_iff_eq_add, T.evθ_list, hfl, hev gp D hgpl] at hfg
  have hL := hasElementaryIntegralIn_logSum
    (fun l : LogN m ↦ nVal (T.evθ m hTr θ) αL (l.2.2.2.map fun q ↦ [mcst Fc ks (m + 1) q]))
    (fun l ↦ nVal (T.evθ m hTr θ) αL (l.1.map (nkFl Fc ks m))) logs
    (fun l hl ↦ ⟨T.deriv_nVal_rat m hTr θ αL hαc _, hu0 l hl⟩)
  rw [← T.nk_iffR hmon hdeg m hn hc hk Pp hsh θ hθ hgen s hs gp D hsq kc U hcert hgpl res hres, hfg]
  constructor
  · intro h
    have := h.sub_in hL
    simpa using this
  · intro h
    rw [add_comm]; exact h.add_in hL

set_option maxHeartbeats 8000000 in
/-- **`nk_iffCN` without `α` among the constants**: pass to the splitting field `E` of `μ` over
`L` (a finite extension; the tower is realized over the constants of `E`, `exists_lift`), apply
`nk_iffCN` there and come back by `hasElementaryIntegral_finite_iff`. -/
theorem nk_iffCN' (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fl : List (LC (m + 1))) (hfl : fl.length = Pp.length)
    (gp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp gp D kc U = true) (hgpl : gp.length = Pp.length)
    (μ : List ℤ) (logs : List (LogN m)) (dθ wθ : GPoly (LC (m + 1)))
    (hlog : logCertN Fc ks m Pp μ fl (nkFlR m gp D) logs dθ wθ = true)
    (res : Bool)
    (hres : exactG Fc ks m (primSysC Fc ks m η (paramLimC Fc ks lv m)) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFlR m gp D) (nkTau Fc ks m Pp.length (nkFlR m gp D) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
      ((T.MPr (m + 1) (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr).sem
        (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m gp D) s)) := by
  classical
  have hdμ : 0 < μ.length := by
    unfold logCertN at hlog
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlog
    exact hlog.1.1.1
  set μP : ℚ[X] := X ^ μ.length + ∑ i ∈ Finset.range μ.length, Polynomial.C (μ.getD i 0 : ℚ) * X ^ i
    with hμP
  have hμmon : μP.Monic := by
    rw [hμP]
    refine monic_X_pow_add ?_
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro i hi
    refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact_mod_cast Finset.mem_range.mp hi
  have hμdeg : μP.natDegree = μ.length := by
    rw [hμP, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro i hi
    refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact_mod_cast Finset.mem_range.mp hi
  set q : L[X] := μP.map (algebraMap ℚ L) with hq
  let E := SplittingField q
  letI : Differential E := differentialFiniteDimensional L E
  haveI : DifferentialAlgebra L E := differentialAlgebraFiniteDimensional
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap L E).injective
  set ι := algebraMap L E with hι
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E
  have hqdeg : q.degree ≠ 0 := by
    rw [hq, degree_map, degree_eq_natDegree hμmon.ne_zero, hμdeg]; exact_mod_cast hdμ.ne'
  obtain ⟨αE, hαE⟩ := (SplittingField.splits q).exists_eval_eq_zero (by
    rw [degree_map]; exact hqdeg)
  have hmapE : (μP.map (algebraMap ℚ L)).map (algebraMap L E) = μP.map (algebraMap ℚ E) := by
    rw [Polynomial.map_map]; congr 1
  have hαμ : aeval αE μP = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, ← hmapE]; exact hαE
  have hαd : αE′ = 0 := deriv_eq_zero_of_isAlgebraic αE ⟨μP, hμmon.ne_zero, hαμ⟩
  set αC : constants E := ⟨αE, hαd⟩ with hαC
  have hαCμ : αC ^ μ.length + ∑ i ∈ Finset.range μ.length, (μ.getD i 0 : constants E) * αC ^ i =
      0 := by
    apply Subtype.ext
    have := hαμ
    rw [hμP] at this
    simp only [map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C] at this
    simpa using this
  -- the tower data over `E`
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ι (T.evP m P) := fun P ↦ by
    induction P with
    | nil => simp [evP, evPL]
    | cons a P ih =>
      simp only [evP, evPL, List.foldr_cons] at ih ⊢
      rw [ih, map_add, map_mul, hTEts m, ← hTEev m a]
  have hθE : (ι θ) ^ Pp.length + ∑ i ∈ Finset.range Pp.length, TE.evP m (Pp.getD i []) * (ι θ) ^ i
      = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ, map_zero]
  have hT1 : ∀ w ∈ TE.F (m + 1), w ∈ IntermediateField.adjoin (TE.F (m + 1)) {ι θ} :=
    fun w hw ↦ IntermediateField.algebraMap_mem _ (⟨w, hw⟩ : TE.F (m + 1))
  have hLT : ∀ z : L, ι z ∈ IntermediateField.adjoin (TE.F (m + 1)) {ι θ} := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact IntermediateField.mem_adjoin_simple_self _ _
    | algebraMap w => exact hT1 _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hgenE : ∀ z : E, z ∈ IntermediateField.adjoin (TE.F (m + 1)) {ι θ} := by
    intro z
    have hz : z ∈ Algebra.adjoin L (q.rootSet E) := by
      rw [SplittingField.adjoin_rootSet]; trivial
    induction hz using Algebra.adjoin_induction with
    | mem w hw =>
      have hw0 : aeval w μP = 0 := by
        have h2 := (mem_rootSet.mp hw).2
        change aeval w (μP.map (algebraMap ℚ L)) = 0 at h2
        rwa [aeval_map_algebraMap] at h2
      have hwd : w′ = 0 := deriv_eq_zero_of_isAlgebraic w ⟨μP, hμmon.ne_zero, hw0⟩
      obtain ⟨c0, hc0⟩ := TE.hconst w hwd
      rw [← hc0]
      exact hT1 _ (TE.const_mem (m + 1) c0)
    | algebraMap w => exact hLT w
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
  have hn' : TE.n = m + 1 := by rw [hTEn, hn]
  have key := TE.nk_iffCN hmon hdeg m hn' hc hk Pp hsh (ι θ) hθE hgenE s hs fl hfl gp D hsq kc U
    hcert hgpl μ αC hαCμ logs dθ wθ hlog res hres
  have hMS := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  have hMSE := (TE.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  have hint : ∑ j ∈ Finset.range Pp.length,
      ((TE.MPr (m + 1) hMSE).sem (fl.getD j (MOr Fc ks (m + 1)).zero) : E) * (ι θ) ^ j =
      ι (∑ j ∈ Finset.range Pp.length,
        ((T.MPr (m + 1) hMS).sem (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_pow, MPr_sem, MPr_sem, TE.sem_MP, T.sem_MP, hTEev]
  rw [hint, hTEev, hasElementaryIntegral_finite_iff, hasElementaryIntegral_finite_iff] at key
  exact key

end MTower

end Curves.MT
