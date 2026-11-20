import RischTragerBronstein.Mixed.KXDepConj
import RischTragerBronstein.Mixed.KXForwardDep
import RischTragerBronstein.Mixed.KFSquare
import RischTragerBronstein.Mixed.KXNoRel

/-!
# A Liouville form makes the relation search succeed (linear base)

In the exception (`P₊ − ∞` not torsion) a Liouville form forces, for every non-torsion class `k`, a
relation `N Δ_k + μ δ₀ ∼ 0` (`kxe_norel`), `μ ≠ 0` (`Δ_k` is not torsion). Then
`f ∏(x − c_q)^{N m_q} x^{|μ|}` has divisor `2N Γ_k + 2|μ| P_±` (`ordAt_unzD`), so `P_±` is defined
over the code field `Kₘ` on the twist (`rel_point_defined`), hence (linear base: rational
non-squares stay non-squares, `not_isSquare_KF'`) `s_T κ` is a rational square and `kxBt0` gives
`±` its ordinate; and the relation descends to `Kₘ`, so `witW` finds the witness
(`kx_rel_found`).
-/

open Polynomial Differential IntermediateField Classical

set_option linter.unusedSectionVars false

namespace Differential.SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

lemma dZ_neg (β₀ : K) (hβ₀ : β₀ ≠ 0) (Q : K × K) : dZ (-β₀) Q = -dZ β₀ Q := by
  have hne : β₀ ≠ -β₀ := fun h ↦ hβ₀ (by
    have h2 : (2 : K) * β₀ = 0 := by linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero)
  unfold dZ
  by_cases h1 : Q = (0, β₀)
  · subst h1; simp [Prod.ext_iff, hne]
  · by_cases h2 : Q = (0, -β₀)
    · subst h2; simp [Prod.ext_iff, hne.symm]
    · simp [h1, h2]

end Differential.SuperData

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 8000000 in
/-- **The relation search succeeds** (linear base): in a realization with a Liouville form, in the
exception, every non-torsion class has a candidate `(N, M, ±b)` of `kxDepSearch` that passes. -/
theorem kx_rel_found (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (hcst : kxConst Fc ks m g A B kt l cs = true) (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (k : Fin (kxCls Fc ks m g A B kt l cs).length)
    (htk : kxTorsC Fc ks m g A B kt l cs cpf ps bound rs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] =
      some none)
    (z : LC m) (s : L) (hz : kxZ Fc ks lv m A = some z)
    (ht0 : kxTors0C Fc ks m A cpf ps bound rs z = some none)
    (hs2 : s ^ 2 = (kxKap Fc ks m A z : L)) (hs' : s′ = 0)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (rts : List L) (hrl : rts.length = (kxGens Fc ks m g A B kt l cs).length)
    (hrts : ∀ i (hi : i < rts.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rts[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : L) ∧ rts[i]′ = 0)
    (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) :
    ∃ (N M : ℕ) (b bt : KF Fc m), 1 ≤ N ∧ 1 ≤ M ∧
      kxBt0 Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] z = some b ∧
      (bt = b ∨ bt = -b) ∧
      kxWitD Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] bt N M ≠ none ∧
      bt * bt = (kxFKm Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]).getD 0 0 ∧
      bt ≠ 0 := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  obtain ⟨rtsF, hFl, hFv⟩ := T.roots_F m rts (fun i hi ↦ (hrts i hi (by omega)).2)
  have hrlF : rtsF.length = (kxGens Fc ks m g A B kt l cs).length := by rw [hFl, hrl]
  have hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : T.F m) := fun i hi hi' ↦ Subtype.ext (by
    rw [IntermediateField.coe_pow, hFv i hi (by omega), (hrts i (by omega) hi').1]; simp)
  obtain ⟨hb, hby, hbm, hDR, hDoff, hbP⟩ :=
    T.kx_data m hTr A hsq hdegA θ hθ (by omega) B kt l cs hA0
  set S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero with hS
  have hok0 := T.kxOK_spec m hTm A B kt l cs hok
  have hc0K : ∀ q : Fin cs.length, (T.MP m hTm).sem (kqC Fc ks m cs q) ≠ 0 := fun q ↦
    (hok0.2 q q.2).1
  have hRne := T.kx_Rne m hTm A B kt l cs hok
  have hcinj := T.kx_cinj m hTm A B kt l cs hok
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ 1 one_ne_zero hcopA
  obtain ⟨hβ, hres, hρ⟩ := T.kxm_abs m MS.hyp hk A B kt l cs hok hcst hrep rtsF hrlF hrsF
  set Tk := (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] with hTk
  obtain ⟨q0, hq0, hq0T⟩ := kxCls_mem_rep (Fc := Fc) (ks := ks) m g A B kt l cs _
    (List.getElem_mem (n := (k : ℕ)) k.2)
  have hk0 : ∃ q, kxCl m g A B kt l cs q = k ∧ kxMNm Fc ks m g A B kt l cs q ≠ 0 := by
    refine ⟨⟨q0, hq0⟩, (kxCl_eq_iff m g A B kt l cs _ k).mpr hq0T, fun h0 ↦ ?_⟩
    obtain ⟨-, hκ, hc0'⟩ := kxRep_spec (Fc := Fc) (ks := ks) m g A B kt l cs hrep q0 hq0
    have hm := kxMNm_eq (Fc := Fc) (ks := ks) m g A B kt l cs q0 hq0 hc0'
    rw [h0, Nat.cast_zero, eq_comm, mul_eq_zero] at hm
    rcases hm with h | h
    · exact (kxDenM_pos (Fc := Fc) (ks := ks) m g A B kt l cs).ne' (by exact_mod_cast h)
    · rw [h] at hκ; simp at hκ
      exact T.kxK_ne m MS.hyp hk A B kt l cs hok hcst q0 hq0 hκ
  have hp0v : (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 =
      algebraMap (T.F m) _ ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)) := by
    rw [eval_map, ← map_zero (algebraMap (T.F m) (AlgebraicClosure (T.F m))), eval₂_at_apply]
    congr 1
    change (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0 = _
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm]
  have ha0v : (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 := hok0.1
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) ha0v
  obtain ⟨b₀, μ₀, hb₀, hb₀2, hμ₀, hμb, hμv, hpf0, hd0, hf0, hsq0, hcop0⟩ :=
    T.kx_zero_twist hmon hdeg m hn hc hTr A hsq hdegA hcopA ha0 z hz θ hθ s hs2 hs'
  have hnp := T.kx_P0_nt m hTr A hsq hdegA hcopA θ hθ z b₀ μ₀ hb₀ hb₀2 hμ₀ hμb hpf0 hd0 hf0 hsq0
    hcop0 ps bound rs cpf ht0
  set β₀ := algebraMap (T.F m) (AlgebraicClosure (T.F m)) b₀
  have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) _).injective).mpr hb₀
  have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 := by
    rw [hp0v]; show β₀ ^ 2 = _; rw [← map_pow, hb₀2]
  have hb₀n : b₀ ^ S.n = S.p.eval 0 := by
    show b₀ ^ 2 = (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm, hb₀2]
  have hntZ : ∀ f : (T.F m)⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ M : ℤ, (∀ α β' : AlgebraicClosure (T.F m),
      β' ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
        (S.ordAt (AlgebraicClosure (T.F m)) f α β' : ℚ) =
          M * Differential.SuperData.dZ β₀ (α, β')) → M = 0 := fun f hf M hM ↦
    S.kxe_mu0_nt rfl β₀ hβ0 hv0 (r := 0) (nk := 0) (fun q ↦ q.elim0) (fun q ↦ q.elim0)
      (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0)
      hcopS b₀ ⟨hb₀, hb₀n⟩ rfl hnp (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0)
      (fun q ↦ q.elim0) (fun q ↦ q.elim0) f hf (fun q ↦ q.elim0) M
      (fun α β' hv ↦ by rw [hM α β' hv]; simp)
  -- the class data over `Kₘ`
  obtain ⟨hμ0, hpf, hd, hsqK, hcop2, hvK, hinjK, hA, hB⟩ :=
    T.kxm_class_KF m MS.hyp hk A B hsq hcopA kt l cs hok hcst hrep rtsF hrlF hrsF k
  set μk : T.F m := SqrtIndep.prodRoots rtsF Tk with hμk
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
  -- the relation
  obtain ⟨f, hf, N, hN, μ, hfo⟩ : ∃ f : (T.F m)⟮S.x⟯⟮S.y⟯, f ≠ 0 ∧ ∃ N : ℕ, 0 < N ∧ ∃ μ : ℤ,
      ∀ α β' : AlgebraicClosure (T.F m), β' ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
        (S.ordAt (AlgebraicClosure (T.F m)) f α β' : ℚ) =
          N * Differential.SuperData.dK (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q))
            (fun q : Fin cs.length ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
              SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
              ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
                (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))))
            (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) k (α, β') +
          μ * Differential.SuperData.dZ β₀ (α, β') := by
    by_contra hne
    exact S.kxe_norel (K := AlgebraicClosure (T.F m)) (T.val m g)′
      (T.keS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) hk) (fun c ↦ deriv_algebraMap c)
      (T.kxS_good m MS.hyp hk) (T.keS_constC m)
      (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj hc0K
      (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) _
      (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hTm) B) l _ hb
      _ (fun q' ↦ X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR hRne
      hDoff hbP hres rfl β₀ hβ0 hv0 k hk0 hρ
      (fun f hf N hN μ hall ↦ hne ⟨f, hf, N, hN, μ, hall⟩) hbm sI c u hcd
      (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ (hu i hi).2⟩) v
      (T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ hv) (by rw [hby]; exact heq)
  set cf : Fin cs.length → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcf
  set βf : Fin cs.length → T.F m := fun q ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
    SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
    ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
      (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))) with hβf
  set mf : Fin cs.length → ℕ := fun q ↦ kxMNm Fc ks m g A B kt l cs q with hmf
  -- the function `w` of divisor `2N Γ_k + 2|μ| P_±`
  obtain ⟨w, hw0, hwo⟩ : ∃ w : (T.F m)⟮S.x⟯⟮S.y⟯, w ≠ 0 ∧
      ∀ α β' : AlgebraicClosure (T.F m), β' ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
        S.ordAt (AlgebraicClosure (T.F m)) w α β' =
          (2 * N : ℕ) * Differential.SuperData.gammaQ cf βf
            (Differential.SuperData.mK mf (kxCl m g A B kt l cs) k) (α, β') +
          (2 * μ.natAbs : ℕ) * Differential.SuperData.gammaP (if 0 ≤ μ then β₀ else -β₀) (α, β') :=
    ⟨_, (S.ordAt_unzD (K := AlgebraicClosure (T.F m)) rfl β₀ hβ0 hv0 cf βf hcinj hc0K
      (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) mf _ k f hf N μ hfo).1,
      (S.ordAt_unzD (K := AlgebraicClosure (T.F m)) rfl β₀ hβ0 hv0 cf βf hcinj hc0K
      (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) mf _ k f hf N μ hfo).2⟩
  have hwI : S.IsIntegralS (AlgebraicClosure (T.F m)) w := fun α β' hv ↦ by
    rw [hwo α β' hv]; positivity
  have hμne : μ ≠ 0 := by
    intro hμ0'
    refine hnt (2 * N) (by omega) ⟨w, hw0, hwI, fun Q hv ↦ ?_⟩
    rw [hwo Q.1 Q.2 hv, hμ0']; simp
  set σC : T.F m := if 0 ≤ μ then b₀ else -b₀ with hσC
  have hσK : algebraMap (T.F m) (AlgebraicClosure (T.F m)) σC = if 0 ≤ μ then β₀ else -β₀ := by
    simp only [hσC]; split_ifs <;> simp [β₀]
  have hσ0 : σC ≠ 0 := by simp only [hσC]; split_ifs <;> simp [hb₀]
  have hσ2 : σC ^ S.n = S.p.eval 0 := by
    rw [← hb₀n]; simp only [hσC]; split_ifs
    · rfl
    · show (-b₀) ^ 2 = b₀ ^ 2; ring
  set M : ℕ := 2 * μ.natAbs with hM
  have hMpos : 0 < M := by have := Int.natAbs_pos.mpr hμne; omega
  set ιk := kxIota m g A B kt l cs k with hιk
  set a : Fin (kxQs Fc ks m g A B kt l cs Tk).length → T.F m := fun i ↦ cf (ιk i) with ha
  set bb : Fin (kxQs Fc ks m g A B kt l cs Tk).length → T.F m := fun i ↦ βf (ιk i) with hbb
  set mq : Fin (kxQs Fc ks m g A B kt l cs Tk).length → ℕ := fun i ↦ (2 * N) * mf (ιk i) with hmq
  have hgam : ∀ Q : AlgebraicClosure (T.F m) × AlgebraicClosure (T.F m),
      Differential.SuperData.gammaQ (Fin.cons 0 a) (Fin.cons σC bb) (Fin.cons M mq) Q =
        (2 * N : ℕ) * Differential.SuperData.gammaQ cf βf
          (Differential.SuperData.mK mf (kxCl m g A B kt l cs) k) Q +
        M * Differential.SuperData.gammaP (algebraMap (T.F m) _ σC) Q := by
    intro Q
    rw [Differential.SuperData.gammaQ_cons]
    congr 1
    rw [Differential.SuperData.gammaQ_class cf βf hcinj mf (kxCl m g A B kt l cs) k ιk
      (kxIota_cl m g A B kt l cs k) (kxIota_surj m g A B kt l cs k) (kxIota_inj m g A B kt l cs k) Q]
    simp only [Differential.SuperData.gammaQ, Finset.mul_sum, ha, hbb, hmq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  have hrel : S.IsPrincipalS (AlgebraicClosure (T.F m))
      (Differential.SuperData.gammaQ (Fin.cons 0 a) (Fin.cons σC bb) (Fin.cons M mq)) 1 :=
    ⟨w, hw0, hwI, fun Q hv ↦ by rw [hwo Q.1 Q.2 hv, hgam, hσK]; push_cast; ring⟩
  have hainj : Function.Injective a := fun i j h ↦ kxIota_inj m g A B kt l cs k (hcinj h)
  have hntZσ : ∀ f : (T.F m)⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ M' : ℤ, (∀ α β' : AlgebraicClosure (T.F m),
      β' ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
        (S.ordAt (AlgebraicClosure (T.F m)) f α β' : ℚ) =
          M' * Differential.SuperData.dZ (algebraMap (T.F m) _ σC) (α, β')) → M' = 0 := by
    intro f hf M' hM'
    rw [hσK] at hM'
    split_ifs at hM'
    · exact hntZ f hf M' hM'
    · have := hntZ f hf (-M') fun α β' hv ↦ by
        rw [hM' α β' hv, Differential.SuperData.dZ_neg β₀ hβ0]; push_cast; ring
      omega
  obtain ⟨bt, hbt⟩ := S.rel_point_defined (K := AlgebraicClosure (T.F m)) rfl hcopS a bb hainj
    (fun i ↦ hc0K _) (fun i ↦ ⟨(hβ _).1, (hβ _).2⟩) mq (T.psiF m hTm)
    (kxFKm Fc ks m g A B kt l cs Tk) μk hμ0 hpf (kxAlm Fc ks m g A B kt l cs Tk)
    (kxBem Fc ks m g A B kt l cs Tk) hA hB hvK σC hσ0 hσ2 M hMpos hrel hntZσ
  -- the computations over `Kₘ`
  set ψ := T.psiF m hTm with hψdef
  set κ : ℚ := kxKap Fc ks m A z with hκdef
  set sT : ℚ := kxS Fc ks m g A B kt l cs Tk with hsTdef
  set fK := kxFKm Fc ks m g A B kt l cs Tk with hfKdef
  obtain ⟨q1, hq1⟩ := kxZ_some hz
  have hz0 : T.ev m z ≠ 0 := (T.ke_z_facts hmon hdeg m hn hc A ha0 q1 z hq1).1
  have hzF : (T.MP m hTm).sem z ≠ 0 := fun h ↦ hz0 (by rw [← T.sem_MP m hTm, h]; rfl)
  have hs0 : s ≠ 0 := fun h0 ↦ hμ₀ (Subtype.ext (by rw [hμv, h0, div_zero]; rfl))
  have hbzL : ((b₀ : T.F m) : L) * T.ev m z = s := by
    have h1 : ((μ₀ : T.F m) : L) * ((b₀ : T.F m) : L) = 1 := by
      rw [← IntermediateField.coe_mul, hμb]; rfl
    rw [hμv] at h1
    field_simp at h1
    linear_combination h1
  have hκF : (b₀ * (T.MP m hTm).sem z) ^ 2 = ((κ : ℚ) : T.F m) := Subtype.ext (by
    rw [IntermediateField.coe_pow, IntermediateField.coe_mul, T.sem_MP m hTm, hbzL, hs2]
    simp)
  have hμk2 : μk ^ 2 = ((sT : ℚ) : T.F m) := SqrtIndep.prodRoots_sq _ rtsF hrlF hrsF _
  have hfK0 : ψ (fK.getD 0 0) = μk ^ 2 * b₀ ^ 2 := by
    have h0 := congrArg (fun P ↦ P.eval 0) hpf
    rw [eval_mul, eval_C, eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm,
      Polynomial.eval_zero_map, ← coeff_zero_eq_eval_zero (p := toPoly fK), CPoly.coeff_toPoly,
      ← hb₀2] at h0
    exact h0.symm
  have hσ2' : σC ^ 2 = b₀ ^ 2 := by simp only [hσC]; split_ifs <;> ring
  have hbt2 : bt * bt = fK.getD 0 0 := ψ.injective (by
    rw [map_mul, hbt, hfK0, ← hσ2']; ring)
  have hbt0 : bt ≠ 0 := fun h ↦ by
    have := hbt; rw [h, map_zero] at this
    exact mul_ne_zero hμ0 hσ0 this.symm
  have htz : ψ (trC Fc m z) = (T.MP m hTm).sem z := T.psiF_trC m hTm z
  have hsqKF : IsSquare (((sT * κ : ℚ) : ℚ) : KF Fc m) := ⟨bt * trC Fc m z, ψ.injective (by
    rw [map_ratCast, map_mul, map_mul, hbt, htz]
    push_cast
    rw [← hμk2, ← hκF]
    simp only [hσC]; split_ifs <;> ring)⟩
  have hsqQ : IsSquare (sT * κ) := by
    by_contra hns
    exact not_isSquare_KF' Fc c0 hFc _ hns m hsqKF
  have hr : Rat.sqrt (sT * κ) * Rat.sqrt (sT * κ) = sT * κ := by
    obtain ⟨r, hr⟩ := hsqQ
    exact (Rat.exists_mul_self _).mp ⟨r, hr.symm⟩
  set b : KF Fc m := ((Rat.sqrt (sT * κ) : ℚ) : KF Fc m) / trC Fc m z with hbdef
  have hBt0 : kxBt0 Fc ks m g A B kt l cs Tk z = some b := by
    unfold kxBt0
    simp only [← hsTdef, ← hκdef, hr, beq_self_eq_true, if_true]
    rfl
  have hpm : bt = b ∨ bt = -b := by
    refine sq_eq_sq_iff_eq_or_eq_neg.mp (ψ.injective ?_)
    rw [map_pow, map_pow, hbt, hbdef, map_div₀, map_ratCast, htz, div_pow, ← Rat.cast_pow,
      show Rat.sqrt (sT * κ) ^ 2 = sT * κ by rw [sq, hr]]
    rw [eq_div_iff (pow_ne_zero 2 hzF)]
    push_cast
    rw [← hμk2, ← hκF]
    simp only [hσC]; split_ifs <;> ring
  -- the witness
  have hinjpt : Function.Injective fun q : Fin ((kxQs Fc ks m g A B kt l cs Tk).length + 1) ↦
      ((Fin.cons 0 a : Fin _ → T.F m) q, (Fin.cons σC bb : Fin _ → T.F m) q) := fun i j h ↦
    Differential.SuperData.cons_inj a hainj (fun i ↦ hc0K _) (Prod.ext_iff.mp h).1
  have hP0 := S.principalMulN_of_isPrincipalS (K := AlgebraicClosure (T.F m)) hcopS (Fin.cons 0 a)
    (Fin.cons σC bb) (Fin.cons M mq) hinjpt
    (fun q ↦ by induction q using Fin.cases
                · exact hσ0
                · exact (hβ _).1)
    (fun q ↦ by induction q using Fin.cases
                · exact hσ2
                · exact (hβ _).2) _ (fun Q _ ↦ rfl) 1 hrel
  have hP1 := principalMulN_scale μk hμ0 hP0
  rw [show S.n = 2 from rfl,
    show Polynomial.C (μk ^ 2) * S.p = (toPoly fK).map ψ from hpf] at hP1
  have e1 : (Fin.cons 0 a : Fin _ → T.F m) =
      fun q ↦ ψ ((Fin.cons 0 (kxAlm Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q) := by
    funext q; induction q using Fin.cases
    · simp
    · simp only [Fin.cons_succ]; exact (hA _).symm
  have e2 : (fun q ↦ μk * (Fin.cons σC bb : Fin _ → T.F m) q) =
      fun q ↦ ψ ((Fin.cons bt (kxBem Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q) := by
    funext q; induction q using Fin.cases
    · simp only [Fin.cons_zero]; exact hbt.symm
    · simp only [Fin.cons_succ]; exact (hB _).symm
  rw [e1, e2, Differential.SuperData.natDegree_eq_of_scale S ψ fK μk hμ0 hpf hd] at hP1
  have hΓ' : ∀ q : Fin ((kxQs Fc ks m g A B kt l cs Tk).length + 1),
      ((2 : ℕ) : KF Fc m) * (Fin.cons bt (kxBem Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q ^
        (2 - 1) ≠ 0 ∧
      (Fin.cons bt (kxBem Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q ^ 2 =
        (toPoly fK).eval ((Fin.cons 0 (kxAlm Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q) :=
    fun q ↦ by
      induction q using Fin.cases
      · simp only [Fin.cons_zero]
        refine ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) hbt0, ?_⟩
        rw [sq, hbt2, ← coeff_zero_eq_eval_zero, CPoly.coeff_toPoly]
      · simp only [Fin.cons_succ]; exact hΓK _
  have hP2 := principalMulN_descend ψ (toPoly fK) two_pos _ _ _ _ hΓ' 1 hP1
  have hw := witW_ne_none fK 2 two_pos _ _ _ _ 1 hΓ' hP2
  exact ⟨2 * N, M, b, bt, by omega, hMpos, hBt0, hpm, hw, hbt2, hbt0⟩

set_option maxHeartbeats 8000000 in
/-- **The relation search succeeds on a relation** (linear base): in a realization with the square
roots, if a non-torsion class satisfies a relation `N Δ_k + μ δ₀ ∼ 0` (for every choice of
`b₀ = √A(0)`), a candidate `(N, M, ±b)` of `kxDepSearch` passes. -/
theorem kx_rel_found_of_rel (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
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
    (hrel : let S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero
      ∀ b₀ : T.F m, b₀ ≠ 0 → b₀ ^ 2 = (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) →
      ∃ f : (T.F m)⟮S.x⟯⟮S.y⟯, f ≠ 0 ∧ ∃ N : ℕ, 0 < N ∧ ∃ μ : ℤ,
        ∀ α β' : AlgebraicClosure (T.F m), β' ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
          (S.ordAt (AlgebraicClosure (T.F m)) f α β' : ℚ) =
            N * Differential.SuperData.dK
              (fun q : Fin cs.length ↦ (T.MP m hTr.of_succ).sem (kqC Fc ks m cs q))
              (fun q : Fin cs.length ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
                SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
                ((T.MP m hTr.of_succ).sem (kxD Fc ks m g cs q) *
                  (T.MP m hTr.of_succ).sem (kxR Fc ks m A kt l cs q) /
                  (GPoly.toPoly (T.MP m hTr.of_succ) B).eval
                    ((T.MP m hTr.of_succ).sem (kqC Fc ks m cs q))))
              (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) k (α, β') +
            μ * Differential.SuperData.dZ (algebraMap (T.F m) (AlgebraicClosure (T.F m)) b₀) (α, β'))
    (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) :
    ∃ (N M : ℕ) (b bt : KF Fc m), 1 ≤ N ∧ 1 ≤ M ∧
      kxBt0 Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] z = some b ∧
      (bt = b ∨ bt = -b) ∧
      kxWitD Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] bt N M ≠ none ∧
      bt * bt = (kxFKm Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]).getD 0 0 ∧
      bt ≠ 0 := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTm : T.Tr m := hTr.of_succ
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  set S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero with hS
  have hok0 := T.kxOK_spec m hTm A B kt l cs hok
  have hc0K : ∀ q : Fin cs.length, (T.MP m hTm).sem (kqC Fc ks m cs q) ≠ 0 := fun q ↦
    (hok0.2 q q.2).1
  have hRne := T.kx_Rne m hTm A B kt l cs hok
  have hcinj := T.kx_cinj m hTm A B kt l cs hok
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ 1 one_ne_zero hcopA
  obtain ⟨hβ, hres, hρ⟩ := T.kxm_abs m MS.hyp hk A B kt l cs hok hcst hrep rtsF hrlF hrsF
  set Tk := (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] with hTk
  obtain ⟨q0, hq0, hq0T⟩ := kxCls_mem_rep (Fc := Fc) (ks := ks) m g A B kt l cs _
    (List.getElem_mem (n := (k : ℕ)) k.2)
  have hk0 : ∃ q, kxCl m g A B kt l cs q = k ∧ kxMNm Fc ks m g A B kt l cs q ≠ 0 := by
    refine ⟨⟨q0, hq0⟩, (kxCl_eq_iff m g A B kt l cs _ k).mpr hq0T, fun h0 ↦ ?_⟩
    obtain ⟨-, hκ, hc0'⟩ := kxRep_spec (Fc := Fc) (ks := ks) m g A B kt l cs hrep q0 hq0
    have hm := kxMNm_eq (Fc := Fc) (ks := ks) m g A B kt l cs q0 hq0 hc0'
    rw [h0, Nat.cast_zero, eq_comm, mul_eq_zero] at hm
    rcases hm with h | h
    · exact (kxDenM_pos (Fc := Fc) (ks := ks) m g A B kt l cs).ne' (by exact_mod_cast h)
    · rw [h] at hκ; simp at hκ
      exact T.kxK_ne m MS.hyp hk A B kt l cs hok hcst q0 hq0 hκ
  have hp0v : (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 =
      algebraMap (T.F m) _ ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)) := by
    rw [eval_map, ← map_zero (algebraMap (T.F m) (AlgebraicClosure (T.F m))), eval₂_at_apply]
    congr 1
    change (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0 = _
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm]
  have ha0v : (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 := hok0.1
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) ha0v
  obtain ⟨b₀, μ₀, hb₀, hb₀2, hμ₀, hμb, hμv, hpf0, hd0, hf0, hsq0, hcop0⟩ :=
    T.kx_zero_twist hmon hdeg m hn hc hTr A hsq hdegA hcopA ha0 z hz θ hθ s hs2 hs'
  have hnp := T.kx_P0_nt m hTr A hsq hdegA hcopA θ hθ z b₀ μ₀ hb₀ hb₀2 hμ₀ hμb hpf0 hd0 hf0 hsq0
    hcop0 ps bound rs cpf ht0
  set β₀ := algebraMap (T.F m) (AlgebraicClosure (T.F m)) b₀
  have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) _).injective).mpr hb₀
  have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 := by
    rw [hp0v]; show β₀ ^ 2 = _; rw [← map_pow, hb₀2]
  have hb₀n : b₀ ^ S.n = S.p.eval 0 := by
    show b₀ ^ 2 = (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm, hb₀2]
  have hntZ : ∀ f : (T.F m)⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ M : ℤ, (∀ α β' : AlgebraicClosure (T.F m),
      β' ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
        (S.ordAt (AlgebraicClosure (T.F m)) f α β' : ℚ) =
          M * Differential.SuperData.dZ β₀ (α, β')) → M = 0 := fun f hf M hM ↦
    S.kxe_mu0_nt rfl β₀ hβ0 hv0 (r := 0) (nk := 0) (fun q ↦ q.elim0) (fun q ↦ q.elim0)
      (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0)
      hcopS b₀ ⟨hb₀, hb₀n⟩ rfl hnp (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0)
      (fun q ↦ q.elim0) (fun q ↦ q.elim0) f hf (fun q ↦ q.elim0) M
      (fun α β' hv ↦ by rw [hM α β' hv]; simp)
  -- the class data over `Kₘ`
  obtain ⟨hμ0, hpf, hd, hsqK, hcop2, hvK, hinjK, hA, hB⟩ :=
    T.kxm_class_KF m MS.hyp hk A B hsq hcopA kt l cs hok hcst hrep rtsF hrlF hrsF k
  set μk : T.F m := SqrtIndep.prodRoots rtsF Tk with hμk
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
  -- the relation
  obtain ⟨f, hf, N, hN, μ, hfo⟩ := hrel b₀ hb₀ hb₀2
  set cf : Fin cs.length → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcf
  set βf : Fin cs.length → T.F m := fun q ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
    SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
    ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
      (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))) with hβf
  set mf : Fin cs.length → ℕ := fun q ↦ kxMNm Fc ks m g A B kt l cs q with hmf
  -- the function `w` of divisor `2N Γ_k + 2|μ| P_±`
  obtain ⟨w, hw0, hwo⟩ : ∃ w : (T.F m)⟮S.x⟯⟮S.y⟯, w ≠ 0 ∧
      ∀ α β' : AlgebraicClosure (T.F m), β' ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
        S.ordAt (AlgebraicClosure (T.F m)) w α β' =
          (2 * N : ℕ) * Differential.SuperData.gammaQ cf βf
            (Differential.SuperData.mK mf (kxCl m g A B kt l cs) k) (α, β') +
          (2 * μ.natAbs : ℕ) * Differential.SuperData.gammaP (if 0 ≤ μ then β₀ else -β₀) (α, β') :=
    ⟨_, (S.ordAt_unzD (K := AlgebraicClosure (T.F m)) rfl β₀ hβ0 hv0 cf βf hcinj hc0K
      (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) mf _ k f hf N μ hfo).1,
      (S.ordAt_unzD (K := AlgebraicClosure (T.F m)) rfl β₀ hβ0 hv0 cf βf hcinj hc0K
      (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) mf _ k f hf N μ hfo).2⟩
  have hwI : S.IsIntegralS (AlgebraicClosure (T.F m)) w := fun α β' hv ↦ by
    rw [hwo α β' hv]; positivity
  have hμne : μ ≠ 0 := by
    intro hμ0'
    refine hnt (2 * N) (by omega) ⟨w, hw0, hwI, fun Q hv ↦ ?_⟩
    rw [hwo Q.1 Q.2 hv, hμ0']; simp
  set σC : T.F m := if 0 ≤ μ then b₀ else -b₀ with hσC
  have hσK : algebraMap (T.F m) (AlgebraicClosure (T.F m)) σC = if 0 ≤ μ then β₀ else -β₀ := by
    simp only [hσC]; split_ifs <;> simp [β₀]
  have hσ0 : σC ≠ 0 := by simp only [hσC]; split_ifs <;> simp [hb₀]
  have hσ2 : σC ^ S.n = S.p.eval 0 := by
    rw [← hb₀n]; simp only [hσC]; split_ifs
    · rfl
    · show (-b₀) ^ 2 = b₀ ^ 2; ring
  set M : ℕ := 2 * μ.natAbs with hM
  have hMpos : 0 < M := by have := Int.natAbs_pos.mpr hμne; omega
  set ιk := kxIota m g A B kt l cs k with hιk
  set a : Fin (kxQs Fc ks m g A B kt l cs Tk).length → T.F m := fun i ↦ cf (ιk i) with ha
  set bb : Fin (kxQs Fc ks m g A B kt l cs Tk).length → T.F m := fun i ↦ βf (ιk i) with hbb
  set mq : Fin (kxQs Fc ks m g A B kt l cs Tk).length → ℕ := fun i ↦ (2 * N) * mf (ιk i) with hmq
  have hgam : ∀ Q : AlgebraicClosure (T.F m) × AlgebraicClosure (T.F m),
      Differential.SuperData.gammaQ (Fin.cons 0 a) (Fin.cons σC bb) (Fin.cons M mq) Q =
        (2 * N : ℕ) * Differential.SuperData.gammaQ cf βf
          (Differential.SuperData.mK mf (kxCl m g A B kt l cs) k) Q +
        M * Differential.SuperData.gammaP (algebraMap (T.F m) _ σC) Q := by
    intro Q
    rw [Differential.SuperData.gammaQ_cons]
    congr 1
    rw [Differential.SuperData.gammaQ_class cf βf hcinj mf (kxCl m g A B kt l cs) k ιk
      (kxIota_cl m g A B kt l cs k) (kxIota_surj m g A B kt l cs k) (kxIota_inj m g A B kt l cs k) Q]
    simp only [Differential.SuperData.gammaQ, Finset.mul_sum, ha, hbb, hmq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  have hrel : S.IsPrincipalS (AlgebraicClosure (T.F m))
      (Differential.SuperData.gammaQ (Fin.cons 0 a) (Fin.cons σC bb) (Fin.cons M mq)) 1 :=
    ⟨w, hw0, hwI, fun Q hv ↦ by rw [hwo Q.1 Q.2 hv, hgam, hσK]; push_cast; ring⟩
  have hainj : Function.Injective a := fun i j h ↦ kxIota_inj m g A B kt l cs k (hcinj h)
  have hntZσ : ∀ f : (T.F m)⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ M' : ℤ, (∀ α β' : AlgebraicClosure (T.F m),
      β' ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
        (S.ordAt (AlgebraicClosure (T.F m)) f α β' : ℚ) =
          M' * Differential.SuperData.dZ (algebraMap (T.F m) _ σC) (α, β')) → M' = 0 := by
    intro f hf M' hM'
    rw [hσK] at hM'
    split_ifs at hM'
    · exact hntZ f hf M' hM'
    · have := hntZ f hf (-M') fun α β' hv ↦ by
        rw [hM' α β' hv, Differential.SuperData.dZ_neg β₀ hβ0]; push_cast; ring
      omega
  obtain ⟨bt, hbt⟩ := S.rel_point_defined (K := AlgebraicClosure (T.F m)) rfl hcopS a bb hainj
    (fun i ↦ hc0K _) (fun i ↦ ⟨(hβ _).1, (hβ _).2⟩) mq (T.psiF m hTm)
    (kxFKm Fc ks m g A B kt l cs Tk) μk hμ0 hpf (kxAlm Fc ks m g A B kt l cs Tk)
    (kxBem Fc ks m g A B kt l cs Tk) hA hB hvK σC hσ0 hσ2 M hMpos hrel hntZσ
  -- the computations over `Kₘ`
  set ψ := T.psiF m hTm with hψdef
  set κ : ℚ := kxKap Fc ks m A z with hκdef
  set sT : ℚ := kxS Fc ks m g A B kt l cs Tk with hsTdef
  set fK := kxFKm Fc ks m g A B kt l cs Tk with hfKdef
  obtain ⟨q1, hq1⟩ := kxZ_some hz
  have hz0 : T.ev m z ≠ 0 := (T.ke_z_facts hmon hdeg m hn hc A ha0 q1 z hq1).1
  have hzF : (T.MP m hTm).sem z ≠ 0 := fun h ↦ hz0 (by rw [← T.sem_MP m hTm, h]; rfl)
  have hs0 : s ≠ 0 := fun h0 ↦ hμ₀ (Subtype.ext (by rw [hμv, h0, div_zero]; rfl))
  have hbzL : ((b₀ : T.F m) : L) * T.ev m z = s := by
    have h1 : ((μ₀ : T.F m) : L) * ((b₀ : T.F m) : L) = 1 := by
      rw [← IntermediateField.coe_mul, hμb]; rfl
    rw [hμv] at h1
    field_simp at h1
    linear_combination h1
  have hκF : (b₀ * (T.MP m hTm).sem z) ^ 2 = ((κ : ℚ) : T.F m) := Subtype.ext (by
    rw [IntermediateField.coe_pow, IntermediateField.coe_mul, T.sem_MP m hTm, hbzL, hs2]
    simp)
  have hμk2 : μk ^ 2 = ((sT : ℚ) : T.F m) := SqrtIndep.prodRoots_sq _ rtsF hrlF hrsF _
  have hfK0 : ψ (fK.getD 0 0) = μk ^ 2 * b₀ ^ 2 := by
    have h0 := congrArg (fun P ↦ P.eval 0) hpf
    rw [eval_mul, eval_C, eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm,
      Polynomial.eval_zero_map, ← coeff_zero_eq_eval_zero (p := toPoly fK), CPoly.coeff_toPoly,
      ← hb₀2] at h0
    exact h0.symm
  have hσ2' : σC ^ 2 = b₀ ^ 2 := by simp only [hσC]; split_ifs <;> ring
  have hbt2 : bt * bt = fK.getD 0 0 := ψ.injective (by
    rw [map_mul, hbt, hfK0, ← hσ2']; ring)
  have hbt0 : bt ≠ 0 := fun h ↦ by
    have := hbt; rw [h, map_zero] at this
    exact mul_ne_zero hμ0 hσ0 this.symm
  have htz : ψ (trC Fc m z) = (T.MP m hTm).sem z := T.psiF_trC m hTm z
  have hsqKF : IsSquare (((sT * κ : ℚ) : ℚ) : KF Fc m) := ⟨bt * trC Fc m z, ψ.injective (by
    rw [map_ratCast, map_mul, map_mul, hbt, htz]
    push_cast
    rw [← hμk2, ← hκF]
    simp only [hσC]; split_ifs <;> ring)⟩
  have hsqQ : IsSquare (sT * κ) := by
    by_contra hns
    exact not_isSquare_KF' Fc c0 hFc _ hns m hsqKF
  have hr : Rat.sqrt (sT * κ) * Rat.sqrt (sT * κ) = sT * κ := by
    obtain ⟨r, hr⟩ := hsqQ
    exact (Rat.exists_mul_self _).mp ⟨r, hr.symm⟩
  set b : KF Fc m := ((Rat.sqrt (sT * κ) : ℚ) : KF Fc m) / trC Fc m z with hbdef
  have hBt0 : kxBt0 Fc ks m g A B kt l cs Tk z = some b := by
    unfold kxBt0
    simp only [← hsTdef, ← hκdef, hr, beq_self_eq_true, if_true]
    rfl
  have hpm : bt = b ∨ bt = -b := by
    refine sq_eq_sq_iff_eq_or_eq_neg.mp (ψ.injective ?_)
    rw [map_pow, map_pow, hbt, hbdef, map_div₀, map_ratCast, htz, div_pow, ← Rat.cast_pow,
      show Rat.sqrt (sT * κ) ^ 2 = sT * κ by rw [sq, hr]]
    rw [eq_div_iff (pow_ne_zero 2 hzF)]
    push_cast
    rw [← hμk2, ← hκF]
    simp only [hσC]; split_ifs <;> ring
  -- the witness
  have hinjpt : Function.Injective fun q : Fin ((kxQs Fc ks m g A B kt l cs Tk).length + 1) ↦
      ((Fin.cons 0 a : Fin _ → T.F m) q, (Fin.cons σC bb : Fin _ → T.F m) q) := fun i j h ↦
    Differential.SuperData.cons_inj a hainj (fun i ↦ hc0K _) (Prod.ext_iff.mp h).1
  have hP0 := S.principalMulN_of_isPrincipalS (K := AlgebraicClosure (T.F m)) hcopS (Fin.cons 0 a)
    (Fin.cons σC bb) (Fin.cons M mq) hinjpt
    (fun q ↦ by induction q using Fin.cases
                · exact hσ0
                · exact (hβ _).1)
    (fun q ↦ by induction q using Fin.cases
                · exact hσ2
                · exact (hβ _).2) _ (fun Q _ ↦ rfl) 1 hrel
  have hP1 := principalMulN_scale μk hμ0 hP0
  rw [show S.n = 2 from rfl,
    show Polynomial.C (μk ^ 2) * S.p = (toPoly fK).map ψ from hpf] at hP1
  have e1 : (Fin.cons 0 a : Fin _ → T.F m) =
      fun q ↦ ψ ((Fin.cons 0 (kxAlm Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q) := by
    funext q; induction q using Fin.cases
    · simp
    · simp only [Fin.cons_succ]; exact (hA _).symm
  have e2 : (fun q ↦ μk * (Fin.cons σC bb : Fin _ → T.F m) q) =
      fun q ↦ ψ ((Fin.cons bt (kxBem Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q) := by
    funext q; induction q using Fin.cases
    · simp only [Fin.cons_zero]; exact hbt.symm
    · simp only [Fin.cons_succ]; exact (hB _).symm
  rw [e1, e2, Differential.SuperData.natDegree_eq_of_scale S ψ fK μk hμ0 hpf hd] at hP1
  have hΓ' : ∀ q : Fin ((kxQs Fc ks m g A B kt l cs Tk).length + 1),
      ((2 : ℕ) : KF Fc m) * (Fin.cons bt (kxBem Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q ^
        (2 - 1) ≠ 0 ∧
      (Fin.cons bt (kxBem Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q ^ 2 =
        (toPoly fK).eval ((Fin.cons 0 (kxAlm Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q) :=
    fun q ↦ by
      induction q using Fin.cases
      · simp only [Fin.cons_zero]
        refine ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) hbt0, ?_⟩
        rw [sq, hbt2, ← coeff_zero_eq_eval_zero, CPoly.coeff_toPoly]
      · simp only [Fin.cons_succ]; exact hΓK _
  have hP2 := principalMulN_descend ψ (toPoly fK) two_pos _ _ _ _ hΓ' 1 hP1
  have hw := witW_ne_none fK 2 two_pos _ _ _ _ 1 hΓ' hP2
  exact ⟨2 * N, M, b, bt, by omega, hMpos, hBt0, hpm, hw, hbt2, hbt0⟩

set_option maxHeartbeats 8000000 in
/-- **The relation search succeeds on a `PrincipalMulN` relation** (linear base): if the class points
with multiplicities `N m_q` and `(0, σ)` (`σ² = A(0)`) with multiplicity `M ≥ 1` satisfy
`PrincipalMulN` over `Fₘ`, a candidate `(N, M, ±b)` of `kxDepSearch` passes. -/
theorem kx_rel_found_of_pm (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
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
    (hpm : let S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero
      ∃ (σ : T.F m) (N M : ℕ), σ ≠ 0 ∧
        σ ^ 2 = (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) ∧ 1 ≤ N ∧ 1 ≤ M ∧
        PrincipalMulN S.p S.n S.p.natDegree
          (Fin.cons 0 fun i ↦ (T.MP m hTr.of_succ).sem (kqC Fc ks m cs (kxIota m g A B kt l cs k i)))
          (Fin.cons σ fun i ↦
            ((kxRep Fc ks m g A B kt l cs (kxIota m g A B kt l cs k i)).2 : T.F m) *
              SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs (kxIota m g A B kt l cs k i)).1 *
              ((T.MP m hTr.of_succ).sem (kxD Fc ks m g cs (kxIota m g A B kt l cs k i)) *
                (T.MP m hTr.of_succ).sem (kxR Fc ks m A kt l cs (kxIota m g A B kt l cs k i)) /
                (GPoly.toPoly (T.MP m hTr.of_succ) B).eval
                  ((T.MP m hTr.of_succ).sem (kqC Fc ks m cs (kxIota m g A B kt l cs k i)))))
          (Fin.cons M fun i ↦ N * kxMNm Fc ks m g A B kt l cs (kxIota m g A B kt l cs k i)) 1)
    (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) :
    ∃ (N M : ℕ) (b bt : KF Fc m), 1 ≤ N ∧ 1 ≤ M ∧
      kxBt0 Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] z = some b ∧
      (bt = b ∨ bt = -b) ∧
      kxWitD Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] bt N M ≠ none ∧
      bt * bt = (kxFKm Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]).getD 0 0 ∧
      bt ≠ 0 := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTm : T.Tr m := hTr.of_succ
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  set S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero with hS
  have hok0 := T.kxOK_spec m hTm A B kt l cs hok
  have hc0K : ∀ q : Fin cs.length, (T.MP m hTm).sem (kqC Fc ks m cs q) ≠ 0 := fun q ↦
    (hok0.2 q q.2).1
  have hRne := T.kx_Rne m hTm A B kt l cs hok
  have hcinj := T.kx_cinj m hTm A B kt l cs hok
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ 1 one_ne_zero hcopA
  obtain ⟨hβ, hres, hρ⟩ := T.kxm_abs m MS.hyp hk A B kt l cs hok hcst hrep rtsF hrlF hrsF
  set Tk := (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] with hTk
  obtain ⟨q0, hq0, hq0T⟩ := kxCls_mem_rep (Fc := Fc) (ks := ks) m g A B kt l cs _
    (List.getElem_mem (n := (k : ℕ)) k.2)
  have hk0 : ∃ q, kxCl m g A B kt l cs q = k ∧ kxMNm Fc ks m g A B kt l cs q ≠ 0 := by
    refine ⟨⟨q0, hq0⟩, (kxCl_eq_iff m g A B kt l cs _ k).mpr hq0T, fun h0 ↦ ?_⟩
    obtain ⟨-, hκ, hc0'⟩ := kxRep_spec (Fc := Fc) (ks := ks) m g A B kt l cs hrep q0 hq0
    have hm := kxMNm_eq (Fc := Fc) (ks := ks) m g A B kt l cs q0 hq0 hc0'
    rw [h0, Nat.cast_zero, eq_comm, mul_eq_zero] at hm
    rcases hm with h | h
    · exact (kxDenM_pos (Fc := Fc) (ks := ks) m g A B kt l cs).ne' (by exact_mod_cast h)
    · rw [h] at hκ; simp at hκ
      exact T.kxK_ne m MS.hyp hk A B kt l cs hok hcst q0 hq0 hκ
  have hp0v : (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 =
      algebraMap (T.F m) _ ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)) := by
    rw [eval_map, ← map_zero (algebraMap (T.F m) (AlgebraicClosure (T.F m))), eval₂_at_apply]
    congr 1
    change (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0 = _
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm]
  have ha0v : (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 := hok0.1
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) ha0v
  obtain ⟨b₀, μ₀, hb₀, hb₀2, hμ₀, hμb, hμv, hpf0, hd0, hf0, hsq0, hcop0⟩ :=
    T.kx_zero_twist hmon hdeg m hn hc hTr A hsq hdegA hcopA ha0 z hz θ hθ s hs2 hs'
  have hnp := T.kx_P0_nt m hTr A hsq hdegA hcopA θ hθ z b₀ μ₀ hb₀ hb₀2 hμ₀ hμb hpf0 hd0 hf0 hsq0
    hcop0 ps bound rs cpf ht0
  set β₀ := algebraMap (T.F m) (AlgebraicClosure (T.F m)) b₀
  have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) _).injective).mpr hb₀
  have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 := by
    rw [hp0v]; show β₀ ^ 2 = _; rw [← map_pow, hb₀2]
  have hb₀n : b₀ ^ S.n = S.p.eval 0 := by
    show b₀ ^ 2 = (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm, hb₀2]
  have hntZ : ∀ f : (T.F m)⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ M : ℤ, (∀ α β' : AlgebraicClosure (T.F m),
      β' ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
        (S.ordAt (AlgebraicClosure (T.F m)) f α β' : ℚ) =
          M * Differential.SuperData.dZ β₀ (α, β')) → M = 0 := fun f hf M hM ↦
    S.kxe_mu0_nt rfl β₀ hβ0 hv0 (r := 0) (nk := 0) (fun q ↦ q.elim0) (fun q ↦ q.elim0)
      (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0)
      hcopS b₀ ⟨hb₀, hb₀n⟩ rfl hnp (fun q ↦ q.elim0) (fun q ↦ q.elim0) (fun q ↦ q.elim0)
      (fun q ↦ q.elim0) (fun q ↦ q.elim0) f hf (fun q ↦ q.elim0) M
      (fun α β' hv ↦ by rw [hM α β' hv]; simp)
  -- the class data over `Kₘ`
  obtain ⟨hμ0, hpf, hd, hsqK, hcop2, hvK, hinjK, hA, hB⟩ :=
    T.kxm_class_KF m MS.hyp hk A B hsq hcopA kt l cs hok hcst hrep rtsF hrlF hrsF k
  set μk : T.F m := SqrtIndep.prodRoots rtsF Tk with hμk
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
  -- the relation
  obtain ⟨σC, N, M, hσ0, hσsq, hN1, hMpos, hP0⟩ := hpm
  set cf : Fin cs.length → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcf
  set βf : Fin cs.length → T.F m := fun q ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
    SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
    ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
      (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))) with hβf
  set mf : Fin cs.length → ℕ := fun q ↦ kxMNm Fc ks m g A B kt l cs q with hmf
  have hσ2 : σC ^ S.n = S.p.eval 0 := by
    show σC ^ 2 = (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm, hσsq]
  have hσb : σC ^ 2 = b₀ ^ 2 := by rw [hσsq, hb₀2]
  have hσpm : σC = b₀ ∨ σC = -b₀ := sq_eq_sq_iff_eq_or_eq_neg.mp hσb
  set ιk := kxIota m g A B kt l cs k with hιk
  set a : Fin (kxQs Fc ks m g A B kt l cs Tk).length → T.F m := fun i ↦ cf (ιk i) with ha
  set bb : Fin (kxQs Fc ks m g A B kt l cs Tk).length → T.F m := fun i ↦ βf (ιk i) with hbb
  set mq : Fin (kxQs Fc ks m g A B kt l cs Tk).length → ℕ := fun i ↦ N * mf (ιk i) with hmq
  have hainj : Function.Injective a := fun i j h ↦ kxIota_inj m g A B kt l cs k (hcinj h)
  have hntZσ : ∀ f : (T.F m)⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ M' : ℤ, (∀ α β' : AlgebraicClosure (T.F m),
      β' ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
        (S.ordAt (AlgebraicClosure (T.F m)) f α β' : ℚ) =
          M' * Differential.SuperData.dZ (algebraMap (T.F m) _ σC) (α, β')) → M' = 0 := by
    intro f hf M' hM'
    rcases hσpm with h | h <;> rw [h] at hM'
    · exact hntZ f hf M' hM'
    · have := hntZ f hf (-M') fun α β' hv ↦ by
        rw [hM' α β' hv, map_neg, Differential.SuperData.dZ_neg β₀ hβ0]; push_cast; ring
      omega
  obtain ⟨bt, hbt⟩ := S.rel_point_defined_pm (K := AlgebraicClosure (T.F m)) rfl hcopS a bb hainj
    (fun i ↦ hc0K _) (fun i ↦ ⟨(hβ _).1, (hβ _).2⟩) mq (T.psiF m hTm)
    (kxFKm Fc ks m g A B kt l cs Tk) μk hμ0 hpf (kxAlm Fc ks m g A B kt l cs Tk)
    (kxBem Fc ks m g A B kt l cs Tk) hA hB hvK σC hσ0 hσ2 M hMpos hP0 hntZσ
  -- the computations over `Kₘ`
  set ψ := T.psiF m hTm with hψdef
  set κ : ℚ := kxKap Fc ks m A z with hκdef
  set sT : ℚ := kxS Fc ks m g A B kt l cs Tk with hsTdef
  set fK := kxFKm Fc ks m g A B kt l cs Tk with hfKdef
  obtain ⟨q1, hq1⟩ := kxZ_some hz
  have hz0 : T.ev m z ≠ 0 := (T.ke_z_facts hmon hdeg m hn hc A ha0 q1 z hq1).1
  have hzF : (T.MP m hTm).sem z ≠ 0 := fun h ↦ hz0 (by rw [← T.sem_MP m hTm, h]; rfl)
  have hs0 : s ≠ 0 := fun h0 ↦ hμ₀ (Subtype.ext (by rw [hμv, h0, div_zero]; rfl))
  have hbzL : ((b₀ : T.F m) : L) * T.ev m z = s := by
    have h1 : ((μ₀ : T.F m) : L) * ((b₀ : T.F m) : L) = 1 := by
      rw [← IntermediateField.coe_mul, hμb]; rfl
    rw [hμv] at h1
    field_simp at h1
    linear_combination h1
  have hκF : (b₀ * (T.MP m hTm).sem z) ^ 2 = ((κ : ℚ) : T.F m) := Subtype.ext (by
    rw [IntermediateField.coe_pow, IntermediateField.coe_mul, T.sem_MP m hTm, hbzL, hs2]
    simp)
  have hμk2 : μk ^ 2 = ((sT : ℚ) : T.F m) := SqrtIndep.prodRoots_sq _ rtsF hrlF hrsF _
  have hfK0 : ψ (fK.getD 0 0) = μk ^ 2 * b₀ ^ 2 := by
    have h0 := congrArg (fun P ↦ P.eval 0) hpf
    rw [eval_mul, eval_C, eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm,
      Polynomial.eval_zero_map, ← coeff_zero_eq_eval_zero (p := toPoly fK), CPoly.coeff_toPoly,
      ← hb₀2] at h0
    exact h0.symm
  have hσ2' : σC ^ 2 = b₀ ^ 2 := hσb
  have hbt2 : bt * bt = fK.getD 0 0 := ψ.injective (by
    rw [map_mul, hbt, hfK0, ← hσ2']; ring)
  have hbt0 : bt ≠ 0 := fun h ↦ by
    have := hbt; rw [h, map_zero] at this
    exact mul_ne_zero hμ0 hσ0 this.symm
  have htz : ψ (trC Fc m z) = (T.MP m hTm).sem z := T.psiF_trC m hTm z
  have hsqKF : IsSquare (((sT * κ : ℚ) : ℚ) : KF Fc m) := ⟨bt * trC Fc m z, ψ.injective (by
    rw [map_ratCast, map_mul, map_mul, hbt, htz]
    push_cast
    rw [← hμk2, ← hκF]
    rcases hσpm with h | h <;> rw [h] <;> ring)⟩
  have hsqQ : IsSquare (sT * κ) := by
    by_contra hns
    exact not_isSquare_KF' Fc c0 hFc _ hns m hsqKF
  have hr : Rat.sqrt (sT * κ) * Rat.sqrt (sT * κ) = sT * κ := by
    obtain ⟨r, hr⟩ := hsqQ
    exact (Rat.exists_mul_self _).mp ⟨r, hr.symm⟩
  set b : KF Fc m := ((Rat.sqrt (sT * κ) : ℚ) : KF Fc m) / trC Fc m z with hbdef
  have hBt0 : kxBt0 Fc ks m g A B kt l cs Tk z = some b := by
    unfold kxBt0
    simp only [← hsTdef, ← hκdef, hr, beq_self_eq_true, if_true]
    rfl
  have hpm : bt = b ∨ bt = -b := by
    refine sq_eq_sq_iff_eq_or_eq_neg.mp (ψ.injective ?_)
    rw [map_pow, map_pow, hbt, hbdef, map_div₀, map_ratCast, htz, div_pow, ← Rat.cast_pow,
      show Rat.sqrt (sT * κ) ^ 2 = sT * κ by rw [sq, hr]]
    rw [eq_div_iff (pow_ne_zero 2 hzF)]
    push_cast
    rw [← hμk2, ← hκF]
    rcases hσpm with h | h <;> rw [h] <;> ring
  -- the witness
  have hP1 := principalMulN_scale μk hμ0 hP0
  rw [show S.n = 2 from rfl,
    show Polynomial.C (μk ^ 2) * S.p = (toPoly fK).map ψ from hpf] at hP1
  have e1 : (Fin.cons 0 a : Fin _ → T.F m) =
      fun q ↦ ψ ((Fin.cons 0 (kxAlm Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q) := by
    funext q; induction q using Fin.cases
    · simp
    · simp only [Fin.cons_succ]; exact (hA _).symm
  have e2 : (fun q ↦ μk * (Fin.cons σC bb : Fin _ → T.F m) q) =
      fun q ↦ ψ ((Fin.cons bt (kxBem Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q) := by
    funext q; induction q using Fin.cases
    · simp only [Fin.cons_zero]; exact hbt.symm
    · simp only [Fin.cons_succ]; exact (hB _).symm
  rw [e1, e2, Differential.SuperData.natDegree_eq_of_scale S ψ fK μk hμ0 hpf hd] at hP1
  have hΓ' : ∀ q : Fin ((kxQs Fc ks m g A B kt l cs Tk).length + 1),
      ((2 : ℕ) : KF Fc m) * (Fin.cons bt (kxBem Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q ^
        (2 - 1) ≠ 0 ∧
      (Fin.cons bt (kxBem Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q ^ 2 =
        (toPoly fK).eval ((Fin.cons 0 (kxAlm Fc ks m g A B kt l cs Tk) : Fin _ → KF Fc m) q) :=
    fun q ↦ by
      induction q using Fin.cases
      · simp only [Fin.cons_zero]
        refine ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) hbt0, ?_⟩
        rw [sq, hbt2, ← coeff_zero_eq_eval_zero, CPoly.coeff_toPoly]
      · simp only [Fin.cons_succ]; exact hΓK _
  have hP2 := principalMulN_descend ψ (toPoly fK) two_pos _ _ _ _ hΓ' 1 hP1
  have hw := witW_ne_none fK 2 two_pos _ _ _ _ 1 hΓ' hP2
  exact ⟨N, M, b, bt, hN1, hMpos, hBt0, hpm, hw, hbt2, hbt0⟩

end MTower

end Curves.MT
