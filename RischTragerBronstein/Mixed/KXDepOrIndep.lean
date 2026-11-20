import RischTragerBronstein.Mixed.KXDepFind
import RischTragerBronstein.Mixed.KXAbelRev
import RischTragerBronstein.Mixed.KXGroupFacts

/-!
# A non-torsion class is dependent on `P₊` (search succeeds) or independent of it

`kx_dep_or_indep` (linear base, cubic `A`): in a realization with the square roots of the class
constants and of `κ`, for a class `k` certified non-torsion and `P₊ − ∞` certified non-torsion,
either a relation `2N Σ_k + 2μ P₊ = 0` (`N > 0`) holds on the curve over `Kₘ` — then the dependent
search finds it (`kx_rel_found_of_pm`, via `pm_of_groupC`) — or there is none: then the class point
has infinite order, `P₊` has infinite order (the oracles' certificates, via
`isPrincipalS_class_of_pm` / `isPrincipalS_P0_of_pm`), and they are independent — the hypotheses of
the certificate-existence lemmas `kxMWSearchCK_of` / `kxMWSearchTK_of`.
-/

open Polynomial Differential IntermediateField Classical

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable [Fact (Irreducible (toPoly (fKc Fc)))]

/-- A cubic as the sum of its coefficients. -/
lemma cubic_eq {F : Type*} [Field F] (P : F[X]) (h : P.natDegree = 3) :
    P = Polynomial.C (P.coeff 3) * X ^ 3 + Polynomial.C (P.coeff 2) * X ^ 2 +
      Polynomial.C (P.coeff 1) * X + Polynomial.C (P.coeff 0) := by
  conv_lhs => rw [P.as_sum_range' 4 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← C_mul_X_pow_eq_monomial, pow_one,
    pow_zero, mul_one]
  ring

set_option maxHeartbeats 16000000 in
/-- **Dependent (the search succeeds) or independent (the certificate hypotheses hold).** -/
theorem kx_dep_or_indep (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (hdeg3 : degG (MO Fc ks m) A = 3)
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (hcst : kxConst Fc ks m g A B kt l cs = true) (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (k : Fin (kxCls Fc ks m g A B kt l cs).length)
    (htk : kxTorsC Fc ks m g A B kt l cs cpf ps bound rs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] =
      some none)
    (z : LC m) (s : L) (hz : kxZ Fc ks lv m A = some z)
    (ht0 : kxTors0C Fc ks m A cpf ps bound rs z = some none)
    (hs2 : s ^ 2 = (kxKap Fc ks m A z : L)) (hs' : s′ = 0)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) (hTr : T.Tr (m + 1))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (rtsF : List (T.F m)) (hrlF : rtsF.length = (kxGens Fc ks m g A B kt l cs).length)
    (hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : T.F m))
    (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) :
    (∃ (N M : ℕ) (b bt : KF Fc m), 1 ≤ N ∧ 1 ≤ M ∧
      kxBt0 Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] z = some b ∧
      (bt = b ∨ bt = -b) ∧
      kxWitD Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] bt N M ≠ none ∧
      bt * bt = (kxFKm Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]).getD 0 0 ∧
      bt ≠ 0) ∨
    ∃ (b₀ : T.F m) (_ : b₀ ^ 2 = (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero))
      (hns : ∀ q : Fin cs.length, (Differential.SuperData.WG
        ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 3) ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 2)
        ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 1)
        ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 3 * (T.MP m hTr.of_succ).sem (kqC Fc ks m cs q))
        ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 3 * (((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
          SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
          ((T.MP m hTr.of_succ).sem (kxD Fc ks m g cs q) * (T.MP m hTr.of_succ).sem (kxR Fc ks m A kt l cs q) /
            (GPoly.toPoly (T.MP m hTr.of_succ) B).eval ((T.MP m hTr.of_succ).sem (kqC Fc ks m cs q))))))
      (hns0 : (Differential.SuperData.WG ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 3)
        ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 2) ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 1)
        ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 3 * 0)
        ((GPoly.toPoly (T.MP m hTr.of_succ) A).coeff 3 * b₀)),
      (∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks m g A B kt l cs q)
          (kxCl m g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0) ∧
      (∀ n : ℤ, n • WeierstrassCurve.Affine.Point.some _ _ hns0 = 0 → n = 0) ∧
      (∀ n : ℤ, n • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks m g A B kt l cs q)
        (kxCl m g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) = 0 →
        n = 0) := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTm : T.Tr m := hTr.of_succ
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  set S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero with hS
  have hok0 := T.kxOK_spec m hTm A B kt l cs hok
  have hc0K : ∀ q : Fin cs.length, (T.MP m hTm).sem (kqC Fc ks m cs q) ≠ 0 := fun q ↦
    (hok0.2 q q.2).1
  have hcinj := T.kx_cinj m hTm A B kt l cs hok
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ 1 one_ne_zero hcopA
  obtain ⟨hβ, hres, hρ⟩ := T.kxm_abs m MS.hyp hk A B kt l cs hok hcst hrep rtsF hrlF hrsF
  set Tk := (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] with hTk
  have ha0v : (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 := hok0.1
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) ha0v
  obtain ⟨b₀, μ₀, hb₀, hb₀2, hμ₀, hμb, hμv, hpf0, hd0, hf0, hsq0, hcop0⟩ :=
    T.kx_zero_twist hmon hdeg m hn hc hTr A hsq hdegA hcopA ha0 z hz θ hθ s hs2 hs'
  have hnp := T.kx_P0_nt m hTr A hsq hdegA hcopA θ hθ z b₀ μ₀ hb₀ hb₀2 hμ₀ hμb hpf0 hd0 hf0 hsq0
    hcop0 ps bound rs cpf ht0
  have hb₀n : b₀ ^ S.n = S.p.eval 0 := by
    show b₀ ^ 2 = (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm, hb₀2]
  -- the class data over `Kₘ`
  obtain ⟨hμ0, hpf, hd, hsqK, hcop2, hvK, hinjK, hA, hB⟩ :=
    T.kxm_class_KF m MS.hyp hk A B hsq hcopA kt l cs hok hcst hrep rtsF hrlF hrsF k
  have hspec := torsOracleC_specF (redAtKF Fc m rs) cpf (fun p _ R h ↦ redAtKF_valid Fc m rs p R h)
    ps bound hsqK hcop2
  have hnot := (hspec _ _ _ (kxMqm Fc ks m g A B kt l cs Tk) hvK hinjK).2 htk
  have hΓK : ∀ i : Fin (kxQs Fc ks m g A B kt l cs Tk).length,
      ((2 : ℕ) : KF Fc m) * kxBem Fc ks m g A B kt l cs Tk i ^ (2 - 1) ≠ 0 ∧
        kxBem Fc ks m g A B kt l cs Tk i ^ 2 =
          (toPoly (kxFKm Fc ks m g A B kt l cs Tk)).eval (kxAlm Fc ks m g A B kt l cs Tk i) := fun i ↦
    ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) (hvK i).1, (hvK i).2⟩
  have hnt := S.class_not_principal (K := AlgebraicClosure (T.F m)) rfl hcopS
    (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj
    (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) k
    (kxIota m g A B kt l cs k) (kxIota_cl m g A B kt l cs k) (kxIota_surj m g A B kt l cs k)
    (kxIota_inj m g A B kt l cs k) (T.psiF m hTm) _ _ hμ0 hpf hd _ _ hA hB _ (fun i ↦ rfl) hΓK hnot
  -- the cubic model
  set P := GPoly.toPoly (T.MP m hTm) A with hP
  have hdeg3' : P.natDegree = 3 := by rw [hdeg1, hdeg3]
  set c3 := P.coeff 3
  set c2 := P.coeff 2
  set c1 := P.coeff 1
  set c0' := P.coeff 0
  have hPc := cubic_eq P hdeg3'
  have hpE : S.p = Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X +
      Polynomial.C c0' := by
    show Polynomial.C ((1 : T.F m) ^ 2) * P = _
    rw [one_pow, map_one, one_mul]; exact hPc
  have hP0 : P ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hdeg3'; omega
  have hc3 : c3 ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr hP0
    rwa [leadingCoeff, hdeg3'] at this
  have hsep : (Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X +
      Polynomial.C c0').Separable := by
    rw [← hPc]; exact PerfectField.separable_iff_squarefree.mpr hsq
  set f := algebraMap (T.F m) (AlgebraicClosure (T.F m)) with hf
  have hc3K : f c3 ≠ 0 := (map_ne_zero_iff _ f.injective).mpr hc3
  have hsepK : (Polynomial.C (f c3) * X ^ 3 + Polynomial.C (f c2) * X ^ 2 + Polynomial.C (f c1) * X +
      Polynomial.C (f c0')).Separable := by
    have := hsep.map (f := f)
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X] using this
  set cf : Fin cs.length → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcf
  set βf : Fin cs.length → T.F m := fun q ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
    SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
    ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
      (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))) with hβf
  set mf : Fin cs.length → ℕ := fun q ↦ kxMNm Fc ks m g A B kt l cs q with hmf
  have hβS : ∀ q, βf q ≠ 0 ∧ βf q ^ S.n = S.p.eval (cf q) := fun q ↦ ⟨(hβ q).1, (hβ q).2⟩
  have hptq : ∀ q, (c3 * βf q) ^ 2 = (c3 * cf q) ^ 3 + c2 * (c3 * cf q) ^ 2 + c1 * c3 * (c3 * cf q) +
      c0' * c3 ^ 2 := fun q ↦ by
    have h : βf q ^ 2 = S.p.eval (cf q) := (hβS q).2
    rw [hpE] at h
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at h
    linear_combination c3 ^ 2 * h
  have hpt0 : (c3 * b₀) ^ 2 = (c3 * 0) ^ 3 + c2 * (c3 * 0) ^ 2 + c1 * c3 * (c3 * 0) +
      c0' * c3 ^ 2 := by
    have h : b₀ ^ 2 = S.p.eval 0 := hb₀n
    rw [hpE] at h
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at h
    linear_combination c3 ^ 2 * h
  have hnsC : ∀ q, (Differential.SuperData.WG c3 c2 c1 c0').Nonsingular (c3 * cf q) (c3 * βf q) :=
    fun q ↦ Differential.SuperData.ns_of_eq hc3 hsep _ _ (hptq q)
  have hns0C : (Differential.SuperData.WG c3 c2 c1 c0').Nonsingular (c3 * 0) (c3 * b₀) :=
    Differential.SuperData.ns_of_eq hc3 hsep _ _ hpt0
  have hnsK : ∀ q, (Differential.SuperData.WG (f c3) (f c2) (f c1) (f c0')).Nonsingular
      (f c3 * f (cf q)) (f c3 * f (βf q)) := fun q ↦ by
    refine Differential.SuperData.ns_of_eq hc3K hsepK _ _ ?_
    have := congrArg f (hptq q)
    simpa only [map_add, map_mul, map_pow] using this
  have hns0K : (Differential.SuperData.WG (f c3) (f c2) (f c1) (f c0')).Nonsingular
      (f c3 * 0) (f c3 * f b₀) := by
    refine Differential.SuperData.ns_of_eq hc3K hsepK _ _ ?_
    have := congrArg f hpt0
    simpa only [map_add, map_mul, map_pow, map_zero] using this
  set Sk := ∑ q, (Differential.SuperData.mK mf (kxCl m g A B kt l cs) k q : ℤ) •
    WeierstrassCurve.Affine.Point.some _ _ (hnsC q) with hSk
  set P₀ := WeierstrassCurve.Affine.Point.some _ _ hns0C with hP₀
  have hpm := fun (N : ℕ) (μ : ℤ) (hrel : (2 * (N : ℤ)) • Sk + (2 * μ) • P₀ = 0) ↦
    S.pm_of_groupC (K := AlgebraicClosure (T.F m)) cf βf mf (kxCl m g A B kt l cs) k c3 c2 c1 c0'
      rfl hc3 hpE hcopS hcinj hc0K hβS b₀ hb₀ hb₀n hnsC hns0C hnsK hns0K N μ (by convert hrel)
  -- `P₊` has infinite order
  have hP0nt : ∀ n : ℤ, n • P₀ = 0 → n = 0 := by
    intro n hn0
    by_contra hne
    have h2 : (2 * ((0 : ℕ) : ℤ)) • Sk + (2 * (n.natAbs : ℤ)) • P₀ = 0 := by
      simp only [Nat.cast_zero, mul_zero, zero_zsmul, zero_add]
      rw [← smul_smul]
      rcases Int.natAbs_eq n with h | h
      · rw [← h, hn0, zsmul_zero]
      · rw [show ((n.natAbs : ℕ) : ℤ) = -n by omega, neg_zsmul, hn0, neg_zero, zsmul_zero]
    have h3 := hpm 0 n.natAbs h2
    simp only [Nat.cast_nonneg, ite_true, Int.natAbs_natCast, mul_zero, zero_mul] at h3
    have h4 := S.isPrincipalS_P0_of_pm (K := AlgebraicClosure (T.F m)) rfl hcopS cf βf hcinj hc0K
      hβS b₀ hb₀ hb₀n _ h3
    exact hnp (2 * n.natAbs) (by have := Int.natAbs_pos.mpr hne; omega) h4
  by_cases hR : ∃ N : ℕ, 0 < N ∧ ∃ μ : ℤ, (2 * (N : ℤ)) • Sk + (2 * μ) • P₀ = 0
  · left
    obtain ⟨N, hN, μ, hrel⟩ := hR
    have hPM := hpm N μ hrel
    by_cases hμ : μ = 0
    · exfalso
      subst hμ
      simp only [le_refl, ite_true, Int.natAbs_zero, mul_zero] at hPM
      exact hnt (2 * N) (by omega)
        (S.isPrincipalS_class_of_pm (K := AlgebraicClosure (T.F m)) rfl hcopS cf βf hcinj hc0K
          hβS _ b₀ hb₀ hb₀n (2 * N) hPM)
    set σC : T.F m := if 0 ≤ μ then b₀ else -b₀ with hσC
    have hσ0 : σC ≠ 0 := by simp only [hσC]; split_ifs <;> simp [hb₀]
    have hσ2 : σC ^ 2 = (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) := by
      rw [← hb₀2]; simp only [hσC]; split_ifs <;> ring
    set ιk := kxIota m g A B kt l cs k with hιk
    let ρ : Fin ((kxQs Fc ks m g A B kt l cs Tk).length + 1) → Fin (cs.length + 1) :=
      Fin.cons 0 fun i ↦ (ιk i).succ
    have hρinj : Function.Injective ρ := by
      intro i j h
      induction i using Fin.cases <;> induction j using Fin.cases
      · rfl
      · exact absurd h (by simp only [ρ, Fin.cons_zero, Fin.cons_succ]; exact (Fin.succ_ne_zero _).symm)
      · exact absurd h (by simp [ρ])
      · simp only [ρ, Fin.cons_succ, Fin.succ_inj] at h
        rw [kxIota_inj m g A B kt l cs k h]
    have hsupp : ∀ q, (Fin.cons (2 * μ.natAbs) fun q ↦ (2 * N) *
        Differential.SuperData.mK mf (kxCl m g A B kt l cs) k q : Fin (cs.length + 1) → ℕ) q ≠ 0 →
        ∃ i, ρ i = q := by
      intro q hq
      induction q using Fin.cases
      · exact ⟨0, rfl⟩
      · rename_i q
        simp only [Fin.cons_succ] at hq
        have hcl : kxCl m g A B kt l cs q = k := by
          by_contra h; simp [Differential.SuperData.mK, h] at hq
        obtain ⟨i, hi⟩ := kxIota_surj m g A B kt l cs k q hcl
        exact ⟨i.succ, by simp only [ρ, Fin.cons_succ, Fin.succ_inj]; exact hi⟩
    have hR := principalMulN_restrict ρ hρinj hsupp hPM
    have e1 : (fun i ↦ (Fin.cons 0 cf : Fin (cs.length + 1) → T.F m) (ρ i)) =
        Fin.cons 0 fun i ↦ cf (ιk i) := by
      funext i; induction i using Fin.cases <;> simp [ρ]
    have e2 : (fun i ↦ (Fin.cons σC βf : Fin (cs.length + 1) → T.F m) (ρ i)) =
        Fin.cons σC fun i ↦ βf (ιk i) := by
      funext i; induction i using Fin.cases <;> simp [ρ, hσC]
    have e3 : (fun i ↦ (Fin.cons (2 * μ.natAbs) fun q ↦ (2 * N) *
        Differential.SuperData.mK mf (kxCl m g A B kt l cs) k q : Fin (cs.length + 1) → ℕ) (ρ i)) =
        Fin.cons (2 * μ.natAbs) fun i ↦ (2 * N) * mf (ιk i) := by
      funext i; induction i using Fin.cases
      · simp [ρ]
      · simp [ρ, Differential.SuperData.mK, kxIota_cl m g A B kt l cs k, hιk]
    rw [e1, e2, e3] at hR
    exact T.kx_rel_found_of_pm hmon hdeg m hn hc hk A hsqc hdegpos hcop B kt l cs hok hcst hrep ps
      bound rs cpf k htk z s hz ht0 hs2 hs' θ hθ hTr hsq hdegA rtsF hrlF hrsF
      ⟨σC, 2 * N, 2 * μ.natAbs, hσ0, hσ2, by omega,
        by have := Int.natAbs_pos.mpr hμ; omega, hR⟩ c0 hFc
  · right
    push Not at hR
    refine ⟨b₀, hb₀2, hnsC, hns0C, fun N hN μ ↦ hR N hN μ, hP0nt, fun n hn0 ↦ ?_⟩
    by_contra hne
    apply hR n.natAbs (Int.natAbs_pos.mpr hne) 0
    rw [mul_zero, zero_zsmul, add_zero, mul_zsmul]
    rcases Int.natAbs_eq n with h | h
    · rw [← h]; exact (congrArg _ hn0).trans (zsmul_zero _)
    · rw [show ((n.natAbs : ℕ) : ℤ) = -n by omega, neg_zsmul, hn0, neg_zero, zsmul_zero]

end MTower

end Curves.MT
