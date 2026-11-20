import RischTragerBronstein.Mixed.KXForward
import RischTragerBronstein.Mixed.KXDep
import RischTragerBronstein.Mixed.KXDepCodes

/-!
# The Mordell–Weil exception with dependent classes: the forward direction

* `kx_class_witsD`: the class witnesses (torsion, or of a relation `N Δ_k ± M δ₀ ∼ 0`), read on
  `y² = A`, with the values of their columns;
* `kx_forward_dep`: with `P₊ − ∞` not torsion and such witnesses, a Liouville form gives a solution
  of the parametric equation (`kxe_dep`).
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

section ForwardDep

variable [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The witnesses of the classes, torsion or dependent on `δ₀`**, read on `y² = A`, with the values
of their columns: a dependent witness has divisor `N Γ_k + M (0, σ_k)`, `σ_k = ±b₀`. -/
theorem kx_class_witsD (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hTr : T.Tr (m + 1)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (hA0 : T.evP m A ≠ 0)
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (hcst : kxConst Fc ks m g A B kt l cs = true) (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (Ns : Fin (kxCls Fc ks m g A B kt l cs).length → ℕ)
    (Ms : Fin (kxCls Fc ks m g A B kt l cs).length → ℕ)
    (bts : Fin (kxCls Fc ks m g A B kt l cs).length → KF Fc m)
    (Wbs : Fin (kxCls Fc ks m g A B kt l cs).length → BPoly (KF Fc m))
    (hwit : ∀ k : Fin (kxCls Fc ks m g A B kt l cs).length,
      (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] =
        some (some (Ns k)) ∧
        kxWit Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (Ns k) = some (Wbs k) ∧
        Ms k = 0) ∨
      (1 ≤ Ns k ∧ kxWitD Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (bts k) (Ns k)
          (Ms k) = some (Wbs k) ∧
        bts k * bts k = (kxFKm Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]).getD 0 0 ∧
        bts k ≠ 0))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (rtsF : List (T.F m)) (hrlF : rtsF.length = (kxGens Fc ks m g A B kt l cs).length)
    (hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : T.F m))
    (hrd : ∀ z ∈ rtsF, ((z : T.F m) : L)′ = 0) (b₀ : T.F m) (hb₀ : b₀ ≠ 0)
    (hb₀2 : b₀ ^ 2 = (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero)) :
    let S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero
    let hTm : T.Tr m := hTr.of_succ
    ∃ (W : Fin (kxCls Fc ks m g A B kt l cs).length → (T.F m)⟮S.x⟯⟮S.y⟯)
      (W0 W1 μ : Fin (kxCls Fc ks m g A B kt l cs).length → L)
      (σ : Fin (kxCls Fc ks m g A B kt l cs).length → T.F m),
      (∀ k, 1 ≤ Ns k) ∧ (∀ k, W k ≠ 0) ∧ (∀ k, σ k = b₀ ∨ σ k = -b₀) ∧
      (∀ k, ∀ a b : AlgebraicClosure (T.F m), b ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval a →
        S.ordAt (AlgebraicClosure (T.F m)) (W k) a b =
          Ns k * Differential.SuperData.gammaQ
            (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q))
            (fun q : Fin cs.length ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
              SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
              ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
                (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))))
            (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks m g A B kt l cs q)
              (kxCl m g A B kt l cs) k) (a, b) +
          Ms k * Differential.SuperData.gammaP (algebraMap (T.F m) _ (σ k)) (a, b)) ∧
      (∀ k, W0 k ∈ (T.F m)⟮S.x⟯) ∧ (∀ k, W1 k ∈ (T.F m)⟮S.x⟯) ∧
      (∀ k, ((W k : (T.F m)⟮S.x⟯⟮S.y⟯) : L) = W0 k + W1 k * S.y) ∧
      (∀ k, W0 k ^ 2 - W1 k ^ 2 * aeval S.x S.p ≠ 0) ∧ (∀ k, (μ k)′ = 0) ∧
      (∀ k, μ k * T.ev (m + 1) (kxCol Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]
        (Wbs k)) =
        (W0 k * ((W1 k)′ + W1 k * (aeval S.x (mapCoeffs S.p + Polynomial.C (T.val m g)′ * X *
          derivative S.p) / ((S.n : L) * aeval S.x S.p))) - (W0 k)′ * W1 k) /
          (W0 k ^ 2 - W1 k ^ 2 * aeval S.x S.p)) := by
  intro S hTm
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hok0 := T.kxOK_spec m hTm A B kt l cs hok
  have hcinj := T.kx_cinj m hTm A B kt l cs hok
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ 1 one_ne_zero hcopA
  obtain ⟨hβ, -, -⟩ := T.kxm_abs m MS.hyp hk A B kt l cs hok hcst hrep rtsF hrlF hrsF
  have hKF := fun k ↦ T.kxm_class_KF m MS.hyp hk A B hsq hcopA kt l cs hok hcst hrep rtsF hrlF hrsF k
  set Tk : Fin (kxCls Fc ks m g A B kt l cs).length → List Bool :=
    fun k ↦ (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] with hTk
  set μ : Fin (kxCls Fc ks m g A B kt l cs).length → T.F m :=
    fun k ↦ SqrtIndep.prodRoots rtsF (Tk k) with hμ
  have hN : ∀ k, 1 ≤ Ns k := fun k ↦ by
    rcases hwit k with ⟨htk, -, -⟩ | ⟨h1, -⟩
    · obtain ⟨-, -, -, hsqK, hcop2, hvK, hinjK, -, -⟩ := hKF k
      have hspec := torsOracleC_specF (redAtKF Fc m rs) cpf
        (fun p _ R h ↦ redAtKF_valid Fc m rs p R h) ps bound hsqK hcop2
      exact ((hspec _ _ _ (kxMqm Fc ks m g A B kt l cs (Tk k)) hvK hinjK).1 (Ns k) htk).1
    · exact h1
  have hc0K : ∀ q : Fin cs.length, (T.MP m hTm).sem (kqC Fc ks m cs q) ≠ 0 := fun q ↦
    (hok0.2 q q.2).1
  have hS0 : S.p.eval 0 = b₀ ^ 2 := by
    rw [hb₀2]
    change (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0 = _
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm]
  set caseB : Fin (kxCls Fc ks m g A B kt l cs).length → Prop := fun k ↦
    1 ≤ Ns k ∧ kxWitD Fc ks m g A B kt l cs (Tk k) (bts k) (Ns k) (Ms k) = some (Wbs k) ∧
      bts k * bts k = (kxFKm Fc ks m g A B kt l cs (Tk k)).getD 0 0 ∧ bts k ≠ 0 with hcaseB
  set σ : Fin (kxCls Fc ks m g A B kt l cs).length → T.F m := fun k ↦
    if caseB k then T.psiF m hTm (bts k) / μ k else b₀ with hσdef
  have hσpm : ∀ k, caseB k → σ k ≠ 0 ∧ σ k ^ 2 = b₀ ^ 2 ∧ T.psiF m hTm (bts k) = μ k * σ k := by
    intro k hB
    obtain ⟨hμ0, hpf, -⟩ := hKF k
    have hσk : σ k = T.psiF m hTm (bts k) / μ k := by simp only [hσdef, if_pos hB]
    have h0 := congrArg (fun P ↦ P.eval 0) hpf
    simp only [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm, ← hb₀2,
      Polynomial.eval_zero_map, ← coeff_zero_eq_eval_zero, Polynomial.coeff_map,
      CPoly.coeff_toPoly] at h0
    have hμk : μ k ≠ 0 := hμ0
    have hψ2 : T.psiF m hTm (bts k) ^ 2 = μ k ^ 2 * b₀ ^ 2 := by
      rw [sq, ← map_mul, hB.2.2.1]; exact h0.symm
    have hψ0 : T.psiF m hTm (bts k) ≠ 0 :=
      (map_ne_zero_iff _ (T.psiF m hTm).injective).mpr hB.2.2.2
    refine ⟨by rw [hσk]; exact div_ne_zero hψ0 hμk, ?_, ?_⟩
    · rw [hσk, div_pow, hψ2, mul_div_right_comm, div_self (pow_ne_zero 2 hμk), one_mul]
    · rw [hσk, mul_div_cancel₀ _ hμk]
  have hσ1 : ∀ k, σ k = b₀ ∨ σ k = -b₀ := fun k ↦ by
    by_cases hB : caseB k
    · exact sq_eq_sq_iff_eq_or_eq_neg.mp (hσpm k hB).2.1
    · left; simp only [hσdef, if_neg hB]
  set Wp : Fin (kxCls Fc ks m g A B kt l cs).length → (T.F m)[X][X] :=
    fun k ↦ (toB (Wbs k)).map (mapRingHom (T.psiF m hTm)) with hWp
  set Wk : Fin (kxCls Fc ks m g A B kt l cs).length → (T.F m)[X][X] := fun k ↦
    (Wp k).comp (Polynomial.C (Polynomial.C (μ k)) * X) with hWk
  have hWit : ∀ k, S.elemW (Wk k) ≠ 0 ∧ ∀ a b : AlgebraicClosure (T.F m),
      b ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval a →
        S.ordAt (AlgebraicClosure (T.F m)) (S.elemW (Wk k)) a b =
          Ns k * Differential.SuperData.gammaQ
            (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q))
            (fun q : Fin cs.length ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
              SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
              ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
                (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))))
            (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks m g A B kt l cs q)
              (kxCl m g A B kt l cs) k) (a, b) +
          Ms k * Differential.SuperData.gammaP (algebraMap (T.F m) _ (σ k)) (a, b) := fun k ↦ by
    obtain ⟨hμ0, hpf, hd, hsqK, hcop2, hvK, hinjK, hA, hB⟩ := hKF k
    have hΓK : ∀ i : Fin (kxQs Fc ks m g A B kt l cs (Tk k)).length,
        ((2 : ℕ) : KF Fc m) * kxBem Fc ks m g A B kt l cs (Tk k) i ^ (2 - 1) ≠ 0 ∧
          kxBem Fc ks m g A B kt l cs (Tk k) i ^ 2 =
            (toPoly (kxFKm Fc ks m g A B kt l cs (Tk k))).eval (kxAlm Fc ks m g A B kt l cs (Tk k) i) :=
      fun i ↦ ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) (hvK i).1, (hvK i).2⟩
    rcases hwit k with ⟨-, hw, hM0⟩ | hBk
    · have h := S.class_witness (K := AlgebraicClosure (T.F m)) rfl hcopS
        (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj
        (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) k
        (kxIota m g A B kt l cs k) (kxIota_cl m g A B kt l cs k) (kxIota_surj m g A B kt l cs k)
        (kxIota_inj m g A B kt l cs k) (T.psiF m hTm) _ _ hμ0 hpf hd _ _ hA hB _ (fun i ↦ rfl) hΓK
        (Ns k) (Wbs k) hw
      refine ⟨h.1, fun a b hv ↦ ?_⟩
      rw [h.2 a b hv, hM0]; simp
    · obtain ⟨hσ0, hσ2, hψσ⟩ := hσpm k hBk
      obtain ⟨-, hw, hbb, hb0⟩ := hBk
      set βf : Fin cs.length → T.F m := fun q ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
        ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
          (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))) with hβf
      set cf : Fin cs.length → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcf
      have hcinj' : Function.Injective (Fin.cons (0 : T.F m) cf : Fin (cs.length + 1) → T.F m) := by
        intro i j h
        induction i using Fin.cases <;> induction j using Fin.cases
        · rfl
        · exact absurd h.symm (by simpa using hc0K _)
        · exact absurd h (by simpa using hc0K _)
        · simp only [Fin.cons_succ] at h
          rw [hcinj h]
      have hβ' : ∀ q, (Fin.cons (σ k) βf : Fin (cs.length + 1) → T.F m) q ≠ 0 ∧
          (Fin.cons (σ k) βf : Fin (cs.length + 1) → T.F m) q ^ S.n =
            S.p.eval ((Fin.cons (0 : T.F m) cf : Fin (cs.length + 1) → T.F m) q) := fun q ↦ by
        induction q using Fin.cases
        · simp only [Fin.cons_zero]
          exact ⟨hσ0, by rw [hS0]; exact hσ2⟩
        · simp only [Fin.cons_succ]; exact ⟨(hβ _).1, (hβ _).2⟩
      have hΓK' : ∀ i : Fin ((kxQs Fc ks m g A B kt l cs (Tk k)).length + 1),
          ((2 : ℕ) : KF Fc m) * (Fin.cons (bts k) (kxBem Fc ks m g A B kt l cs (Tk k)) :
            Fin _ → KF Fc m) i ^ (2 - 1) ≠ 0 ∧
          (Fin.cons (bts k) (kxBem Fc ks m g A B kt l cs (Tk k)) : Fin _ → KF Fc m) i ^ 2 =
            (toPoly (kxFKm Fc ks m g A B kt l cs (Tk k))).eval
              ((Fin.cons 0 (kxAlm Fc ks m g A B kt l cs (Tk k)) : Fin _ → KF Fc m) i) := fun i ↦ by
        induction i using Fin.cases
        · simp only [Fin.cons_zero]
          refine ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) hb0, ?_⟩
          rw [sq, hbb, ← coeff_zero_eq_eval_zero, CPoly.coeff_toPoly]
        · simp only [Fin.cons_succ]; exact hΓK _
      have h := S.class_witness (K := AlgebraicClosure (T.F m)) rfl hcopS
        (Fin.cons (0 : T.F m) cf) (Fin.cons (σ k) βf) hcinj' hβ'
        (Fin.cons (Ms k) fun q ↦ Ns k * kxMNm Fc ks m g A B kt l cs q)
        (Fin.cons k (kxCl m g A B kt l cs)) k
        (Fin.cons 0 fun i ↦ (kxIota m g A B kt l cs k i).succ)
        (fun i ↦ by
          induction i using Fin.cases
          · rfl
          · simp only [Fin.cons_succ]; exact kxIota_cl m g A B kt l cs k _)
        (fun q hq ↦ by
          induction q using Fin.cases
          · exact ⟨0, rfl⟩
          · simp only [Fin.cons_succ] at hq
            obtain ⟨i, hi⟩ := kxIota_surj m g A B kt l cs k _ hq
            exact ⟨i.succ, by simp [hi]⟩)
        (fun i j h ↦ by
          induction i using Fin.cases <;> induction j using Fin.cases
          · rfl
          · simp only [Fin.cons_zero, Fin.cons_succ] at h; exact absurd h.symm (Fin.succ_ne_zero _)
          · simp only [Fin.cons_zero, Fin.cons_succ] at h; exact absurd h (Fin.succ_ne_zero _)
          · simp only [Fin.cons_succ, Fin.succ_inj] at h
            rw [kxIota_inj m g A B kt l cs k h])
        (T.psiF m hTm) _ _ hμ0 hpf hd
        (Fin.cons 0 (kxAlm Fc ks m g A B kt l cs (Tk k)))
        (Fin.cons (bts k) (kxBem Fc ks m g A B kt l cs (Tk k)))
        (fun i ↦ by
          induction i using Fin.cases
          · simp
          · simp only [Fin.cons_succ]; exact hA _)
        (fun i ↦ by
          induction i using Fin.cases
          · simp only [Fin.cons_zero]; exact hψσ
          · simp only [Fin.cons_succ]; exact hB _)
        (Fin.cons (Ms k) fun i ↦ Ns k * kxMqm Fc ks m g A B kt l cs (Tk k) i)
        (fun i ↦ by
          induction i using Fin.cases
          · rfl
          · rfl)
        hΓK' 1 (Wbs k) hw
      refine ⟨h.1, fun a b hv ↦ ?_⟩
      rw [h.2 a b hv, Differential.SuperData.gammaQ_aug]
      push_cast; ring
  have hmemx : ∀ P : (T.F m)[X], aeval (T.ts m) P ∈ (T.F m)⟮S.x⟯ := fun P ↦ by
    letI := algebraAdjoinSimple (F := T.F m) S.x
    rw [show aeval (T.ts m) P = aeval S.x P from rfl, ← algebraMap_adjoinSimple (F := T.F m) S.x P]
    exact SetLike.coe_mem _
  set W0 : Fin (kxCls Fc ks m g A B kt l cs).length → L :=
    fun k ↦ aeval (T.ts m) ((Wp k).coeff 0) with hW0
  set W1c : Fin (kxCls Fc ks m g A B kt l cs).length → L :=
    fun k ↦ aeval (T.ts m) ((Wp k).coeff 1) with hW1c
  set W1 : Fin (kxCls Fc ks m g A B kt l cs).length → L :=
    fun k ↦ ((μ k : T.F m) : L) * W1c k with hW1
  have hWe : ∀ k, ((S.elemW (Wk k) : (T.F m)⟮S.x⟯⟮S.y⟯) : L) = W0 k + W1 k * S.y := fun k ↦ by
    rw [T.elemW_two S rfl (Wk k)]
    simp only [hWk, comp_C_mul_X_coeff, pow_zero, mul_one, pow_one, hW0, hW1, hW1c]
    rw [map_mul, aeval_C]
    simp only [IntermediateField.algebraMap_apply]
    have hSx : S.x = T.ts m := rfl
    rw [hSx]
    ring
  have hW1m : ∀ k, W1 k ∈ (T.F m)⟮S.x⟯ := fun k ↦
    mul_mem (IntermediateField.algebraMap_mem _ (μ k)) (hmemx _)
  have hNm : ∀ k, W0 k ^ 2 - W1 k ^ 2 * aeval S.x S.p ≠ 0 := fun k h0 ↦ by
    have hWne := (hWit k).1
    have hy2 : S.y ^ 2 = aeval S.x S.p := S.hy
    have hodd : Odd S.p.natDegree := by
      rw [← Nat.coprime_two_left]; exact hcopS
    have hny := not_mem_of_sq_odd (C := T.F m) S.x S.y S.htr S.p hodd hy2
    have hfac : (W0 k + W1 k * S.y) * (W0 k - W1 k * S.y) = 0 := by rw [← h0, ← hy2]; ring
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact hWne (Subtype.ext (by rw [hWe k, h1]; rfl))
    · by_cases hw1 : W1 k = 0
      · apply hWne; apply Subtype.ext
        rw [hWe k, hw1, zero_mul, add_zero]
        rw [hw1, zero_mul, sub_zero] at h1
        rw [h1]; rfl
      · apply hny
        rw [show S.y = W0 k / W1 k by field_simp; linear_combination -h1]
        exact div_mem (hmemx _) (hW1m k)
  have hx := T.keS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) hk
  have hμ2 : ∀ k, (μ k) ^ 2 = ((kxS Fc ks m g A B kt l cs (Tk k) : ℚ) : T.F m) := fun k ↦
    SqrtIndep.prodRoots_sq _ rtsF hrlF hrsF _
  have hμd : ∀ k, ((μ k : T.F m) : L)′ = 0 := fun k ↦ by
    have : ∀ (r' : List (T.F m)) (T' : List Bool), (∀ z ∈ r', ((z : T.F m) : L)′ = 0) →
        ((SqrtIndep.prodRoots r' T' : T.F m) : L)′ = 0 := by
      intro r' T' hr'
      induction r' generalizing T' with
      | nil => cases T' <;> simp [SqrtIndep.prodRoots]
      | cons y r' ih =>
        cases T' with
        | nil => simp [SqrtIndep.prodRoots]
        | cons b T' =>
          simp only [SqrtIndep.prodRoots, IntermediateField.coe_mul]
          rw [Derivation.leibniz, ih T' (fun z hz ↦ hr' z (List.mem_cons_of_mem _ hz))]
          split_ifs
          · rw [hr' y (List.mem_cons_self)]; simp
          · simp
    exact this rtsF _ hrd
  have hPd : (aeval (T.ts m) S.p)′ = aeval (T.ts m) (mapCoeffs S.p +
      Polynomial.C (T.val m g)′ * X * derivative S.p) := S.deriv_aeval_xW _ hx S.p
  have hPA : aeval (T.ts m) S.p = T.evP m A := by
    change aeval (T.ts m) (Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hTm) A) = _
    rw [map_mul, aeval_C, T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
    simp
  refine ⟨fun k ↦ S.elemW (Wk k), W0, W1, fun k ↦ ((μ k : T.F m) : L), σ, hN, fun k ↦ (hWit k).1,
    hσ1, fun k ↦ (hWit k).2, fun k ↦ hmemx _, hW1m, hWe, hNm, hμd, fun k ↦ ?_⟩
  have hW0c : T.evP m ((Wbs k).getD 0 [] |>.map (unTr Fc m)) = W0 k := by
    rw [T.evP_unTr_map m hTm, hW0, hWp]
    simp only [Polynomial.coeff_map, coe_mapRingHom, coeff_toB]
  have hW1c' : T.evP m ((Wbs k).getD 1 [] |>.map (unTr Fc m)) = W1c k := by
    rw [T.evP_unTr_map m hTm, hW1c, hWp]
    simp only [Polynomial.coeff_map, coe_mapRingHom, coeff_toB]
  have hAh : T.evP m (A.map ((MO Fc ks m).mul (mcst Fc ks m (kxS Fc ks m g A B kt l cs (Tk k))))) =
      ((kxS Fc ks m g A B kt l cs (Tk k) : ℚ) : L) * aeval (T.ts m) S.p := by
    rw [T.evP_mapMul m hTm, ← T.sem_MP m hTm, T.sem_mcst, hPA]; push_cast; rfl
  have hμL2 : ((μ k : T.F m) : L) ^ 2 = ((kxS Fc ks m g A B kt l cs (Tk k) : ℚ) : L) := by
    rw [← IntermediateField.coe_pow, hμ2 k]; push_cast; rfl
  rw [kxCol, T.ev_normC (m + 1) hTr, T.ev_logCol m hTr, hW0c, hW1c', hAh, T.ev_one_code m hTm,
    mul_one]
  have hSx : S.x = T.ts m := rfl
  have hn2' : ((S.n : ℕ) : L) = 2 := by show ((2 : ℕ) : L) = 2; norm_num
  have hsPd : (((kxS Fc ks m g A B kt l cs (Tk k) : ℚ) : L) * aeval (T.ts m) S.p)′ =
      ((kxS Fc ks m g A B kt l cs (Tk k) : ℚ) : L) * (aeval (T.ts m) S.p)′ := by
    rw [Derivation.leibniz, T.deriv_ratCast_E]; simp
  have hW1d : (W1 k)′ = ((μ k : T.F m) : L) * (W1c k)′ := by
    simp only [hW1]; rw [Derivation.leibniz, hμd k]; simp
  rw [hsPd, hSx, hn2', ← hPd, hW1d]
  simp only [hW1]
  rw [← hμL2]
  have hμ0 : ((μ k : T.F m) : L) ≠ 0 := fun h ↦ (hKF k).1 (Subtype.ext h)
  field_simp


set_option maxHeartbeats 4000000 in
open Classical in
/-- **Forward, dependent classes**: with `P₊ − ∞` not torsion and, for every class, a torsion
witness or the witness of a relation `N Δ_k ± M δ₀ ∼ 0`, a Liouville form gives a solution of the
parametric equation. -/
theorem kx_forward_dep (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (hcst : kxConst Fc ks m g A B kt l cs = true) (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (Ns : Fin (kxCls Fc ks m g A B kt l cs).length → ℕ)
    (Ms : Fin (kxCls Fc ks m g A B kt l cs).length → ℕ)
    (bts : Fin (kxCls Fc ks m g A B kt l cs).length → KF Fc m)
    (Wbs : Fin (kxCls Fc ks m g A B kt l cs).length → BPoly (KF Fc m))
    (hwit : ∀ k : Fin (kxCls Fc ks m g A B kt l cs).length,
      (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] =
        some (some (Ns k)) ∧
        kxWit Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (Ns k) = some (Wbs k) ∧
        Ms k = 0) ∨
      (1 ≤ Ns k ∧ kxWitD Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (bts k) (Ns k)
          (Ms k) = some (Wbs k) ∧
        bts k * bts k = (kxFKm Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]).getD 0 0 ∧
        bts k ≠ 0))
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
      rts[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : L) ∧ rts[i]′ = 0) :
    (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
      (((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) ::
        List.ofFn fun k ↦ kxCol Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (Wbs k))).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true := by
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
  have hrd : ∀ z ∈ rtsF, ((z : T.F m) : L)′ = 0 := fun z hz ↦ by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    rw [hFv i hi (by omega)]
    exact (hrts i (by omega) (by omega)).2
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
  have hp0v : (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 =
      algebraMap (T.F m) _ ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)) := by
    rw [eval_map, ← map_zero (algebraMap (T.F m) (AlgebraicClosure (T.F m))), eval₂_at_apply]
    congr 1
    change (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0 = _
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm]
  have ha0v : (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 := hok0.1
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  obtain ⟨b₀, μ₀, hb₀, hb₀2, hμ₀, hμb, -, hpf0, hd0, hf0, hsq0, hcop0⟩ :=
    T.kx_zero_twist hmon hdeg m hn hc hTr A hsq hdegA hcopA (by
      cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
      · rfl
      · exact absurd (((T.MP m hTm).isZero_iff _).mp h) ha0v) z hz θ hθ s hs2 hs'
  have hnp := T.kx_P0_nt m hTr A hsq hdegA hcopA θ hθ z b₀ μ₀ hb₀ hb₀2 hμ₀ hμb hpf0 hd0 hf0 hsq0
    hcop0 ps bound rs cpf ht0
  obtain ⟨W, W0, W1, μ, σ, hN, hW, hσ, hWord, hW0, hW1, hWe, hNm, hμd, hcolv⟩ :=
    T.kx_class_witsD hmon hdeg m hn hc hk A hTr hsq hdegA hcopA hA0 B kt l cs hok hcst hrep ps bound
      rs cpf Ns Ms bts Wbs hwit θ hθ rtsF hrlF hrsF hrd b₀ hb₀ hb₀2
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
  obtain ⟨aa, haa, e, he, hae⟩ := S.kxe_dep (K := AlgebraicClosure (T.F m)) (T.val m g)′
    (T.keS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) hk) (fun c ↦ deriv_algebraMap c)
    (T.kxS_good m MS.hyp hk) (T.keS_constC m)
    (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj hc0K
    (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs)
    (fun k ↦ SqrtIndep.prodRoots rtsF (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] /
      (kxDenM Fc ks m g A B kt l cs : T.F m))
    (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hTm) B) l _ hb
    _ (fun q' ↦ X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR hRne
    hDoff hbP hres rfl hcopS β₀ hβ0 hv0 hntZ Ns Ms (fun k ↦ hN k)
    (fun k ↦ algebraMap (T.F m) _ (σ k))
    (fun k ↦ by rcases hσ k with h | h <;> rw [h] <;> simp [β₀]) W hW hWord W0 W1 hW0 hW1 hWe hNm
    hbm sI c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ (hu i hi).2⟩) v
    (T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ hv) (by rw [hby]; exact heq)
  rw [hby] at hae
  have hSy : S.y = θ * ((1 : T.F m) : L) := rfl
  refine T.prde_forward_ofFn m hTr A hA0 θ hθ hspecA _ _ aa ((T.mem_F_succ).mpr haa)
    (fun k ↦ algebraMap (T.F m) L (e k) * μ k) (fun k ↦ by
      rw [Derivation.leibniz, he k, hμd k]; simp) ?_
  rw [hae, hSy]
  simp only [IntermediateField.coe_one, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← hcolv k]
  ring

end ForwardDep

end MTower

end Curves.MT
