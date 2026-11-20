import RischTragerBronstein.Mixed.KXZero

/-!
# Square roots over an exponential level with poles: the forward direction

* `kx_forward_nontors`: a class without torsion leaves no Liouville form when `√A(0) ∉ Fₘ` or
  `P₊ − ∞` is torsion;
* `kx_forward_tors_mu0`, `kx_forward_tors_W0`: with all classes torsion, a Liouville form gives a
  solution of the parametric Risch equation.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- `torsOracleC_spec` for a provider depending on the curve. -/
lemma torsOracleC_specF {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (redAt : (p : ℕ) → Option (RedFns p K)) (cpf : CPoly K → CertProv K)
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p K), redAt p = some R →
      ∃ φ : K →+* ℚ_[p], RedValid p R φ)
    (ps : List ℕ) (bound : ℕ) {fK : CPoly K} {n : ℕ} (hsq : Squarefree (CPoly.toPoly fK))
    (hcop : Nat.Coprime n (fK.length - 1)) :
    TorsSpecN fK n (torsOracleC redAt (cpf fK) ps bound fK n) :=
  torsOracleC_spec redAt (cpf fK) hred ps bound hsq hcop

namespace MTower

variable (T : MTower Fc ks Cc L)

section Forward

variable [Fact (Irreducible (toPoly (fKc Fc)))]

open Classical in
/-- **The point `P₊` as a one-point class**: the witness of `N (P₊ − ∞)` over `Kₘ`, read on
`y² = A`, has divisor `N (P₊ − ∞)`. -/
theorem kx_W0 (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) (z : LC m) (b₀ μ₀ : T.F m) (hb₀ : b₀ ≠ 0)
    (hb₀2 : b₀ ^ 2 = (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero)) (hμ₀ : μ₀ ≠ 0)
    (hμb : μ₀ * b₀ = 1)
    (hpf0 : Polynomial.C (μ₀ ^ 2) * (Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hTr.of_succ) A) =
        (toPoly (kxFK0 Fc ks m A z)).map (T.psiF m hTr.of_succ))
    (hd0 : (toPoly (kxFK0 Fc ks m A z)).natDegree = (kxFK0 Fc ks m A z).length - 1)
    (hf0 : (toPoly (kxFK0 Fc ks m A z)).eval 0 = 1)
    (N : ℕ) (W0b : BPoly (KF Fc m)) (hw0 : kxWit0 Fc ks m A z N = some W0b) :
    let S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero
    let W := ((toB W0b).map (mapRingHom (T.psiF m hTr.of_succ))).comp
      (Polynomial.C (Polynomial.C μ₀) * X)
    S.elemW W ≠ 0 ∧ ∀ a b : AlgebraicClosure (T.F m),
      b ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval a →
        S.ordAt (AlgebraicClosure (T.F m)) (S.elemW W) a b =
          N * Differential.SuperData.gammaP (algebraMap (T.F m) (AlgebraicClosure (T.F m)) b₀) (a, b) := by
  intro S W
  have hTm : T.Tr m := hTr.of_succ
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ 1 one_ne_zero hcopA
  have hp : S.p = Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hTm) A := rfl
  have hβ1 : ∀ q : Fin 1, b₀ ≠ 0 ∧ b₀ ^ S.n = S.p.eval 0 := fun _ ↦ ⟨hb₀, by
    show b₀ ^ 2 = _
    rw [hp, eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm, hb₀2]⟩
  have hΓK : ∀ i : Fin 1, ((2 : ℕ) : KF Fc m) * (![(1 : KF Fc m)] i) ^ (2 - 1) ≠ 0 ∧
      (![(1 : KF Fc m)] i) ^ 2 = (toPoly (kxFK0 Fc ks m A z)).eval (![(0 : KF Fc m)] i) := fun i ↦ by
    fin_cases i; simp [hf0]
  obtain ⟨h1, h2⟩ := S.class_witness (K := AlgebraicClosure (T.F m)) rfl hcopS
    (fun _ : Fin 1 ↦ (0 : T.F m)) (fun _ ↦ b₀) (fun i j _ ↦ Subsingleton.elim i j) hβ1
    (fun _ ↦ 1) (fun _ ↦ (0 : Fin 1)) 0 id (fun _ ↦ rfl) (fun q _ ↦ ⟨q, rfl⟩) (fun _ _ h ↦ h)
    (T.psiF m hTm) (kxFK0 Fc ks m A z) μ₀ hμ₀ hpf0 hd0 ![(0 : KF Fc m)] ![(1 : KF Fc m)]
    (fun i ↦ by fin_cases i; simp) (fun i ↦ by fin_cases i; simp [hμb]) ![1]
    (fun i ↦ by fin_cases i; simp) hΓK N W0b hw0
  refine ⟨h1, fun a b hv ↦ ?_⟩
  rw [h2 a b hv, Differential.SuperData.mK_single, Differential.SuperData.gammaQ_single]

open Classical in
/-- **`P₊ − ∞` not torsion over `Kₘ` ⇒ no multiple of `P₊ − ∞` is principal on `y² = A`.** -/
theorem kx_P0_nt (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) (z : LC m) (b₀ μ₀ : T.F m) (hb₀ : b₀ ≠ 0)
    (hb₀2 : b₀ ^ 2 = (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero)) (hμ₀ : μ₀ ≠ 0)
    (hμb : μ₀ * b₀ = 1)
    (hpf0 : Polynomial.C (μ₀ ^ 2) * (Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hTr.of_succ) A) =
        (toPoly (kxFK0 Fc ks m A z)).map (T.psiF m hTr.of_succ))
    (hd0 : (toPoly (kxFK0 Fc ks m A z)).natDegree = (kxFK0 Fc ks m A z).length - 1)
    (hf0 : (toPoly (kxFK0 Fc ks m A z)).eval 0 = 1)
    (hsq0 : Squarefree (toPoly (kxFK0 Fc ks m A z)))
    (hcop0 : Nat.Coprime 2 ((kxFK0 Fc ks m A z).length - 1))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ht0 : kxTors0C Fc ks m A cpf ps bound rs z = some none) :
    let S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero
    ∀ N : ℕ, 0 < N → ¬ S.IsPrincipalS (AlgebraicClosure (T.F m))
      (Differential.SuperData.gammaQ (fun _ : Fin 1 ↦ (0 : T.F m)) (fun _ ↦ b₀) (fun _ ↦ 1)) N := by
  intro S
  have hTm : T.Tr m := hTr.of_succ
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ 1 one_ne_zero hcopA
  have hp : S.p = Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hTm) A := rfl
  have hβ1 : ∀ q : Fin 1, b₀ ≠ 0 ∧ b₀ ^ S.n = S.p.eval 0 := fun _ ↦ ⟨hb₀, by
    show b₀ ^ 2 = _
    rw [hp, eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm, hb₀2]⟩
  have hΓK : ∀ i : Fin 1, ((2 : ℕ) : KF Fc m) * (![(1 : KF Fc m)] i) ^ (2 - 1) ≠ 0 ∧
      (![(1 : KF Fc m)] i) ^ 2 = (toPoly (kxFK0 Fc ks m A z)).eval (![(0 : KF Fc m)] i) := fun i ↦ by
    fin_cases i; simp [hf0]
  have hspec := torsOracleC_specF (redAtKF Fc m rs) cpf (fun p _ R h ↦ redAtKF_valid Fc m rs p R h)
    ps bound hsq0 hcop0
  have hnot := (hspec 1 ![(0 : KF Fc m)] ![1] ![1] (fun q ↦ by fin_cases q; simp [hf0])
    (fun a b _ ↦ Subsingleton.elim a b)).2 ht0
  have h := S.class_not_principal (K := AlgebraicClosure (T.F m)) rfl hcopS
    (fun _ : Fin 1 ↦ (0 : T.F m)) (fun _ ↦ b₀) (fun i j _ ↦ Subsingleton.elim i j) hβ1
    (fun _ ↦ 1) (fun _ ↦ (0 : Fin 1)) 0 id (fun _ ↦ rfl) (fun q _ ↦ ⟨q, rfl⟩) (fun _ _ h ↦ h)
    (T.psiF m hTm) (kxFK0 Fc ks m A z) μ₀ hμ₀ hpf0 hd0 ![(0 : KF Fc m)] ![(1 : KF Fc m)]
    (fun i ↦ by fin_cases i; simp) (fun i ↦ by fin_cases i; simp [hμb]) ![1]
    (fun i ↦ by fin_cases i; simp) hΓK hnot
  rw [Differential.SuperData.mK_single] at h
  exact h

set_option maxHeartbeats 2000000 in
open Classical in
/-- **Forward, a class without torsion**: no Liouville form, when `√A(0) ∉ Fₘ` or `P₊ − ∞` is
torsion. -/
theorem kx_forward_nontors (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (hcst : kxConst Fc ks m g A B kt l cs = true) (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (k : Fin (kxCls Fc ks m g A B kt l cs).length)
    (htors : kxTorsC Fc ks m g A B kt l cs cpf ps bound rs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] =
      some none)
    (hzero : kxZ Fc ks lv m A = none ∨ ∃ (z : LC m) (N : ℕ) (W0b : BPoly (KF Fc m)) (s : L),
      kxZ Fc ks lv m A = some z ∧ kxTors0C Fc ks m A cpf ps bound rs z = some (some N) ∧
      kxWit0 Fc ks m A z N = some W0b ∧ s ^ 2 = (kxKap Fc ks m A z : L) ∧ s′ = 0)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (rts : List L) (hrl : rts.length = (kxGens Fc ks m g A B kt l cs).length)
    (hrts : ∀ i (hi : i < rts.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rts[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : L) ∧ rts[i]′ = 0) : False := by
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
  have hc0 : ∀ q : Fin cs.length, (T.MP m hTm).sem (kqC Fc ks m cs q) ≠ 0 := fun q ↦
    (hok0.2 q q.2).1
  have hRne := T.kx_Rne m hTm A B kt l cs hok
  have hcinj := T.kx_cinj m hTm A B kt l cs hok
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ 1 one_ne_zero hcopA
  obtain ⟨hβ, hres, hρ⟩ := T.kxm_abs m MS.hyp hk A B kt l cs hok hcst hrep rtsF hrlF hrsF
  obtain ⟨hμ0, hpf, hd, hsqK, hcop2, hvK, hinjK, hA, hB⟩ :=
    T.kxm_class_KF m MS.hyp hk A B hsq hcopA kt l cs hok hcst hrep rtsF hrlF hrsF k
  have hspec := torsOracleC_specF (redAtKF Fc m rs) cpf (fun p _ R h ↦ redAtKF_valid Fc m rs p R h)
    ps bound hsqK hcop2
  have hnot := (hspec _ _ _ (kxMqm Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]) hvK
    hinjK).2 htors
  set Tk := (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] with hTk
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
  obtain ⟨q0, hq0, hq0T⟩ := kxCls_mem_rep (Fc := Fc) (ks := ks) m g A B kt l cs _ (List.getElem_mem _)
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
  have hc0K : ∀ q : Fin cs.length, (T.MP m hTm).sem (kqC Fc ks m cs q) ≠ 0 := hc0
  have finish : ∀ β₀ : AlgebraicClosure (T.F m), β₀ ≠ 0 →
      β₀ ^ S.n = (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 →
      (∀ f : (T.F m)⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ (L' : Fin (kxCls Fc ks m g A B kt l cs).length → ℚ)
        (μ : ℤ), S.DivKZ β₀ (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _
          (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) f L' μ →
        ∃ M : ℕ, 0 < M ∧ ∃ g' : (T.F m)⟮S.x⟯⟮S.y⟯, g' ≠ 0 ∧
          S.DivKZ β₀ (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _
            (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) g'
            (fun kk ↦ M * L' kk) 0) → False :=
    fun β₀ hβ₀ hv0 hkill ↦ S.kxe_nontors (K := AlgebraicClosure (T.F m)) (T.val m g)′
      (T.keS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) hk) (fun c ↦ deriv_algebraMap c)
      (T.kxS_good m MS.hyp hk) (T.keS_constC m)
      (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj hc0K
      (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) _
      (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hTm) B) l _ hb
      _ (fun q' ↦ X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR hRne
      hDoff hbP hres rfl β₀ hβ₀ hv0 k hk0 hρ hnt hkill hbm sI c u hcd
      (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ (hu i hi).2⟩) v
      (T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ hv) (by rw [hby]; exact heq)
  have ha0v : (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 := hok0.1
  rcases hzero with hz | ⟨z, N, W0b, s, hz, ht0, hw0, hs2, hs'⟩
  · -- `A(0)` is not a square: `μ = 0` by symmetry
    obtain ⟨β₀, hβ₀⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap (T.F m) (AlgebraicClosure (T.F m)) ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)))
      two_pos
    have hβ0 : β₀ ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow two_ne_zero] at hβ₀
      exact ha0v ((map_eq_zero_iff _ (algebraMap (T.F m) _).injective).mp hβ₀.symm)
    have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 := by
      rw [hp0v]; exact hβ₀
    have hns := T.kx_hns hmon hdeg m hn hc A hTm ha0v hz β₀ hβ₀
    exact finish β₀ hβ0 hv0 (S.kill_of_mu0 _ _ _ _ β₀ fun f hf L' μ hfo ↦
      S.kxe_mu0_sym rfl β₀ hβ0 hv0 _ _ hc0K _ _ hns f hf L' μ hfo)
  · -- `P₊ − ∞` torsion: its witness kills `δ₀`
    obtain ⟨b₀, μ₀, hb₀, hb₀2, hμ₀, hμb, -, hpf0, hd0, hf0, hsq0, hcop0⟩ :=
      T.kx_zero_twist hmon hdeg m hn hc hTr A hsq hdegA hcopA (by
        cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
        · rfl
        · exact absurd (((T.MP m hTm).isZero_iff _).mp h) ha0v) z hz θ hθ s hs2 hs'
    have hN1 : 1 ≤ N := by
      have hspec0 := torsOracleC_specF (redAtKF Fc m rs) cpf (fun p _ R h ↦ redAtKF_valid Fc m rs p R h)
        ps bound hsq0 hcop0
      exact ((hspec0 1 ![(0 : KF Fc m)] ![1] ![1] (fun q ↦ by fin_cases q; simp [hf0])
        (fun a b _ ↦ Subsingleton.elim a b)).1 N ht0).1
    obtain ⟨hW0, hW0o⟩ := T.kx_W0 m hTr A hsq hdegA hcopA θ hθ z b₀ μ₀ hb₀ hb₀2 hμ₀ hμb hpf0 hd0 hf0
      N W0b hw0
    set β₀ := algebraMap (T.F m) (AlgebraicClosure (T.F m)) b₀
    have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) _).injective).mpr hb₀
    have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 := by
      rw [hp0v]; show β₀ ^ 2 = _; rw [← map_pow, hb₀2]
    exact finish β₀ hβ0 hv0 (S.kxe_kill_W0 rfl β₀ hβ0 hv0 _ _ _ _ N (by omega) _ hW0 hW0o)

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The witnesses of the classes**, read on `y² = A`, with the values of their columns. -/
theorem kx_class_wits (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hTr : T.Tr (m + 1)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (hA0 : T.evP m A ≠ 0)
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (hcst : kxConst Fc ks m g A B kt l cs = true) (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (Ns : Fin (kxCls Fc ks m g A B kt l cs).length → ℕ)
    (htors : ∀ k : Fin (kxCls Fc ks m g A B kt l cs).length,
      kxTorsC Fc ks m g A B kt l cs cpf ps bound rs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] =
        some (some (Ns k)))
    (Wbs : Fin (kxCls Fc ks m g A B kt l cs).length → BPoly (KF Fc m))
    (hwit : ∀ k : Fin (kxCls Fc ks m g A B kt l cs).length,
      kxWit Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (Ns k) = some (Wbs k))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (rtsF : List (T.F m)) (hrlF : rtsF.length = (kxGens Fc ks m g A B kt l cs).length)
    (hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : T.F m))
    (hrd : ∀ z ∈ rtsF, ((z : T.F m) : L)′ = 0) :
    let S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero
    let hTm : T.Tr m := hTr.of_succ
    ∃ (W : Fin (kxCls Fc ks m g A B kt l cs).length → (T.F m)⟮S.x⟯⟮S.y⟯)
      (W0 W1 μ : Fin (kxCls Fc ks m g A B kt l cs).length → L),
      (∀ k, 1 ≤ Ns k) ∧ (∀ k, W k ≠ 0) ∧
      (∀ k, ∀ a b : AlgebraicClosure (T.F m), b ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval a →
        S.ordAt (AlgebraicClosure (T.F m)) (W k) a b =
          Ns k * Differential.SuperData.gammaQ
            (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q))
            (fun q : Fin cs.length ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
              SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
              ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
                (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))))
            (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks m g A B kt l cs q)
              (kxCl m g A B kt l cs) k) (a, b)) ∧
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
    obtain ⟨-, -, -, hsqK, hcop2, hvK, hinjK, -, -⟩ := hKF k
    have hspec := torsOracleC_specF (redAtKF Fc m rs) cpf (fun p _ R h ↦ redAtKF_valid Fc m rs p R h)
      ps bound hsqK hcop2
    exact ((hspec _ _ _ (kxMqm Fc ks m g A B kt l cs (Tk k)) hvK hinjK).1 (Ns k) (htors k)).1
  set Wp : Fin (kxCls Fc ks m g A B kt l cs).length → (T.F m)[X][X] :=
    fun k ↦ (toB (Wbs k)).map (mapRingHom (T.psiF m hTm)) with hWp
  set Wk : Fin (kxCls Fc ks m g A B kt l cs).length → (T.F m)[X][X] := fun k ↦
    (Wp k).comp (Polynomial.C (Polynomial.C (μ k)) * X) with hWk
  have hWit : ∀ k, S.elemW (Wk k) ≠ 0 ∧ ∀ a b : AlgebraicClosure (T.F m),
      b ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval a →
        S.ordAt (AlgebraicClosure (T.F m)) (S.elemW (Wk k)) a b =
          Ns k * Differential.SuperData.gammaQ
            (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _
            (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks m g A B kt l cs q)
              (kxCl m g A B kt l cs) k) (a, b) := fun k ↦ by
    obtain ⟨hμ0, hpf, hd, hsqK, hcop2, hvK, hinjK, hA, hB⟩ := hKF k
    have hΓK : ∀ i : Fin (kxQs Fc ks m g A B kt l cs (Tk k)).length,
        ((2 : ℕ) : KF Fc m) * kxBem Fc ks m g A B kt l cs (Tk k) i ^ (2 - 1) ≠ 0 ∧
          kxBem Fc ks m g A B kt l cs (Tk k) i ^ 2 =
            (toPoly (kxFKm Fc ks m g A B kt l cs (Tk k))).eval (kxAlm Fc ks m g A B kt l cs (Tk k) i) :=
      fun i ↦ ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) (hvK i).1, (hvK i).2⟩
    exact S.class_witness (K := AlgebraicClosure (T.F m)) rfl hcopS
      (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj
      (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) k
      (kxIota m g A B kt l cs k) (kxIota_cl m g A B kt l cs k) (kxIota_surj m g A B kt l cs k)
      (kxIota_inj m g A B kt l cs k) (T.psiF m hTm) _ _ hμ0 hpf hd _ _ hA hB _ (fun i ↦ rfl) hΓK
      (Ns k) (Wbs k) (hwit k)
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
  refine ⟨fun k ↦ S.elemW (Wk k), W0, W1, fun k ↦ ((μ k : T.F m) : L), hN, fun k ↦ (hWit k).1,
    fun k ↦ (hWit k).2, fun k ↦ hmemx _, hW1m, hWe, hNm, hμd, fun k ↦ ?_⟩
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
/-- **Forward, all classes torsion, no `δ₀` part** (`√A(0) ∉ Fₘ`, or `P₊ − ∞` not torsion):
a Liouville form gives a solution of the parametric equation. -/
theorem kx_forward_tors_mu0 (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (hcst : kxConst Fc ks m g A B kt l cs = true) (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (Ns : Fin (kxCls Fc ks m g A B kt l cs).length → ℕ)
    (htors : ∀ k : Fin (kxCls Fc ks m g A B kt l cs).length,
      kxTorsC Fc ks m g A B kt l cs cpf ps bound rs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] =
        some (some (Ns k)))
    (Wbs : Fin (kxCls Fc ks m g A B kt l cs).length → BPoly (KF Fc m))
    (hwit : ∀ k : Fin (kxCls Fc ks m g A B kt l cs).length,
      kxWit Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (Ns k) = some (Wbs k))
    (hzero : kxZ Fc ks lv m A = none ∨ ∃ (z : LC m) (s : L),
      kxZ Fc ks lv m A = some z ∧ kxTors0C Fc ks m A cpf ps bound rs z = some none ∧
      s ^ 2 = (kxKap Fc ks m A z : L) ∧ s′ = 0)
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
  obtain ⟨W, W0, W1, μ, hN, hW, hWord, hW0, hW1, hWe, hNm, hμd, hcolv⟩ :=
    T.kx_class_wits hmon hdeg m hn hc hk A hTr hsq hdegA hcopA hA0 B kt l cs hok hcst hrep ps bound
      rs cpf Ns htors Wbs hwit θ hθ rtsF hrlF hrsF hrd
  have hp0v : (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 =
      algebraMap (T.F m) _ ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)) := by
    rw [eval_map, ← map_zero (algebraMap (T.F m) (AlgebraicClosure (T.F m))), eval₂_at_apply]
    congr 1
    change (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0 = _
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm]
  have ha0v : (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 := hok0.1
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  set βf : Fin cs.length → T.F m := fun q ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
    SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
    ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
      (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))) with hβf
  have finish : ∀ β₀ : AlgebraicClosure (T.F m), β₀ ≠ 0 →
      β₀ ^ S.n = (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 →
      (∀ f : (T.F m)⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ (L' : Fin (kxCls Fc ks m g A B kt l cs).length → ℚ)
        (μ : ℤ), S.DivKZ β₀ (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) βf
          (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs) f L' μ → μ = 0) →
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
        (((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) ::
          List.ofFn fun k ↦ kxCol Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]
            (Wbs k))).any (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true := by
    intro β₀ hβ0 hv0 hmu0
    obtain ⟨aa, haa, e, he, hae⟩ := S.kxe_tors_mu0 (K := AlgebraicClosure (T.F m)) (T.val m g)′
      (T.keS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) hk) (fun c ↦ deriv_algebraMap c)
      (T.kxS_good m MS.hyp hk) (T.keS_constC m)
      (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj hc0K
      (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs)
      (fun k ↦ SqrtIndep.prodRoots rtsF (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] /
        (kxDenM Fc ks m g A B kt l cs : T.F m))
      (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hTm) B) l _ hb
      _ (fun q' ↦ X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR hRne
      hDoff hbP hres rfl hcopS β₀ hβ0 hv0 hmu0 Ns (fun k ↦ hN k) W hW hWord W0 W1 hW0 hW1 hWe hNm
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
  rcases hzero with hz | ⟨z, s, hz, ht0, hs2, hs'⟩
  · obtain ⟨β₀, hβ₀⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap (T.F m) (AlgebraicClosure (T.F m)) ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)))
      two_pos
    have hβ0 : β₀ ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow two_ne_zero] at hβ₀
      exact ha0v ((map_eq_zero_iff _ (algebraMap (T.F m) _).injective).mp hβ₀.symm)
    have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 := by
      rw [hp0v]; exact hβ₀
    have hns := T.kx_hns hmon hdeg m hn hc A hTm ha0v hz β₀ hβ₀
    exact finish β₀ hβ0 hv0 fun f hf L' μ' hfo ↦
      S.kxe_mu0_sym rfl β₀ hβ0 hv0 _ _ hc0K _ _ hns f hf L' μ' hfo
  · obtain ⟨b₀, μ₀, hb₀, hb₀2, hμ₀, hμb, -, hpf0, hd0, hf0, hsq0, hcop0⟩ :=
      T.kx_zero_twist hmon hdeg m hn hc hTr A hsq hdegA hcopA (by
        cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
        · rfl
        · exact absurd (((T.MP m hTm).isZero_iff _).mp h) ha0v) z hz θ hθ s hs2 hs'
    have hnp := T.kx_P0_nt m hTr A hsq hdegA hcopA θ hθ z b₀ μ₀ hb₀ hb₀2 hμ₀ hμb hpf0 hd0 hf0 hsq0
      hcop0 ps bound rs cpf ht0
    set β₀ := algebraMap (T.F m) (AlgebraicClosure (T.F m)) b₀
    have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) _).injective).mpr hb₀
    have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 := by
      rw [hp0v]; show β₀ ^ 2 = _; rw [← map_pow, hb₀2]
    have hb₀n : b₀ ^ S.n = S.p.eval 0 := by
      show b₀ ^ 2 = (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0
      rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm, hb₀2]
    exact finish β₀ hβ0 hv0 fun f hf L' μ' hfo ↦
      S.kxe_mu0_nt rfl β₀ hβ0 hv0 _ _ hcinj hc0K (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) _ _ hcopS b₀
        ⟨hb₀, hb₀n⟩ rfl hnp Ns (fun k ↦ hN k) W hW hWord f hf L' μ' hfo

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The column of `P₊ − ∞`**: `ev col₀ = s B₀` where `W = W₀ + W₁ y` (`y = θ`) is the witness
and `B₀` its logarithmic coefficient. -/
theorem kx_col0 (m : ℕ) (hTr : T.Tr (m + 1)) {g : LC m} (hk : ks m = .exp g) (hmn : m < T.n)
    (A : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) (z : LC m) (hz0 : T.ev m z ≠ 0) (s : L) (hs0 : s ≠ 0)
    (hs2 : s ^ 2 = (kxKap Fc ks m A z : L)) (hs' : s′ = 0) (μ₀ : T.F m)
    (hμv : ((μ₀ : T.F m) : L) = T.ev m z / s) (W0b : BPoly (KF Fc m)) :
    let S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero
    let Wp := (toB W0b).map (mapRingHom (T.psiF m hTr.of_succ))
    let W0 := aeval (T.ts m) (Wp.coeff 0)
    let W1 := ((μ₀ : T.F m) : L) * aeval (T.ts m) (Wp.coeff 1)
    W0 ^ 2 - W1 ^ 2 * aeval S.x S.p ≠ 0 →
    T.ev (m + 1) (kxCol0 Fc ks m A z W0b) = s *
      ((W0 * (W1′ + W1 * (aeval S.x (mapCoeffs S.p + Polynomial.C (T.val m g)′ * X *
          derivative S.p) / ((S.n : L) * aeval S.x S.p))) - W0′ * W1) /
        (W0 ^ 2 - W1 ^ 2 * aeval S.x S.p)) := by
  intro S Wp W0 W1 hNm
  have hTm : T.Tr m := hTr.of_succ
  set W1c := aeval (T.ts m) (Wp.coeff 1) with hW1c
  have hx := T.keS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero hmn hk
  have hPd : (aeval (T.ts m) S.p)′ = aeval (T.ts m) (mapCoeffs S.p +
      Polynomial.C (T.val m g)′ * X * derivative S.p) := S.deriv_aeval_xW _ hx S.p
  have hPA : aeval (T.ts m) S.p = T.evP m A := by
    change aeval (T.ts m) (Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hTm) A) = _
    rw [map_mul, aeval_C, T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
    simp
  have hA0 : T.evP m A ≠ 0 := by
    rw [← hPA]; exact fun h0 ↦ S.htr ⟨S.p, S.hsq.ne_zero, h0⟩
  have hW0c : T.evP m ((W0b.getD 0 []).map (unTr Fc m)) = W0 := by
    rw [T.evP_unTr_map m hTm]
    simp only [W0, Wp, Polynomial.coeff_map, coe_mapRingHom, coeff_toB]
  have hW1c' : T.evP m ((W0b.getD 1 []).map (unTr Fc m)) = W1c := by
    rw [T.evP_unTr_map m hTm, hW1c]
    simp only [Wp, Polynomial.coeff_map, coe_mapRingHom, coeff_toB]
  set κ : ℚ := kxKap Fc ks m A z with hκ
  have hκL : (κ : L) = s ^ 2 := hs2.symm
  have hAh : T.evP m (kxAh Fc ks m A z) = T.ev m z * T.ev m z * ((κ⁻¹ : ℚ) : L) * T.evP m A := by
    rw [kxAh, T.evP_mapMul m hTm, ← T.sem_MP m hTm, (T.MP m hTm).sem_mul, (T.MP m hTm).sem_mul,
      T.sem_mcst, IntermediateField.coe_mul, IntermediateField.coe_mul, T.sem_MP m hTm]
    rfl
  have hκd : (((κ⁻¹ : ℚ) : L))′ = 0 := T.deriv_ratCast_E _
  rw [kxCol0, T.ev_normC (m + 1) hTr, T.ev_logCol m hTr, hW0c, hW1c', hAh]
  have hSx : S.x = T.ts m := rfl
  have hn2' : ((S.n : ℕ) : L) = 2 := by show ((2 : ℕ) : L) = 2; norm_num
  rw [hSx, hn2', ← hPd, hPA]
  have hμd : ((μ₀ : T.F m) : L)′ = (T.ev m z)′ / s := by
    rw [hμv, div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, hs']
    simp [div_eq_mul_inv, mul_comm]
  have hW1d : W1′ = (T.ev m z)′ / s * W1c + ((μ₀ : T.F m) : L) * W1c′ := by
    show (((μ₀ : T.F m) : L) * W1c)′ = _
    rw [Derivation.leibniz, hμd]; simp only [smul_eq_mul]; ring
  have hκi : ((κ⁻¹ : ℚ) : L) = (s ^ 2)⁻¹ := by push_cast; rw [hκL]
  rw [hW1d]
  simp only [W1] at hNm ⊢
  rw [hμv] at hNm ⊢
  rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz, hκd, hκi]
  rw [← hPA]
  rw [hSx] at hNm
  have hP0 : aeval (T.ts m) S.p ≠ 0 := by rw [hPA]; exact hA0
  have hD : W0 * W0 - W1c * W1c * (T.ev m z * T.ev m z * (s ^ 2)⁻¹ * aeval (T.ts m) S.p) =
      W0 ^ 2 - (T.ev m z / s * W1c) ^ 2 * aeval (T.ts m) S.p := by
    field_simp
  rw [hD]
  simp only [smul_eq_mul]
  field_simp
  ring

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Forward, all classes torsion, `P₊ − ∞` torsion**: a Liouville form gives a solution of the
parametric equation with the column of `P₊ − ∞`. -/
theorem kx_forward_tors_W0 (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (hcst : kxConst Fc ks m g A B kt l cs = true) (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (Ns : Fin (kxCls Fc ks m g A B kt l cs).length → ℕ)
    (htors : ∀ k : Fin (kxCls Fc ks m g A B kt l cs).length,
      kxTorsC Fc ks m g A B kt l cs cpf ps bound rs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] =
        some (some (Ns k)))
    (Wbs : Fin (kxCls Fc ks m g A B kt l cs).length → BPoly (KF Fc m))
    (hwit : ∀ k : Fin (kxCls Fc ks m g A B kt l cs).length,
      kxWit Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (Ns k) = some (Wbs k))
    (z : LC m) (N₀ : ℕ) (W0b : BPoly (KF Fc m)) (s : L) (hz : kxZ Fc ks lv m A = some z)
    (ht0 : kxTors0C Fc ks m A cpf ps bound rs z = some (some N₀)) (hw0 : kxWit0 Fc ks m A z N₀ = some W0b)
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
      (((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) :: ([kxCol0 Fc ks m A z W0b] ++
        List.ofFn fun k ↦ kxCol Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (Wbs k)))).any
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
  obtain ⟨W, W0, W1, μ, hN, hW, hWord, hW0, hW1, hWe, hNm, hμd, hcolv⟩ :=
    T.kx_class_wits hmon hdeg m hn hc hk A hTr hsq hdegA hcopA hA0 B kt l cs hok hcst hrep ps bound
      rs cpf Ns htors Wbs hwit θ hθ rtsF hrlF hrsF hrd
  have hp0v : (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 =
      algebraMap (T.F m) _ ((T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero)) := by
    rw [eval_map, ← map_zero (algebraMap (T.F m) (AlgebraicClosure (T.F m))), eval₂_at_apply]
    congr 1
    change (Polynomial.C ((1 : T.F m) ^ 2) * _).eval 0 = _
    rw [eval_mul, eval_C, one_pow, one_mul, T.toPoly_eval_zero m hTm]
  have ha0v : (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 := hok0.1
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  set βf : Fin cs.length → T.F m := fun q ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
    SqrtIndep.prodRoots rtsF (kxRep Fc ks m g A B kt l cs q).1 *
    ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) /
      (GPoly.toPoly (T.MP m hTm) B).eval ((T.MP m hTm).sem (kqC Fc ks m cs q))) with hβf
  obtain ⟨b₀, μ₀, hb₀, hb₀2, hμ₀, hμb, hμv, hpf0, hd0, hf0, hsq0, hcop0⟩ :=
    T.kx_zero_twist hmon hdeg m hn hc hTr A hsq hdegA hcopA (by
      cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
      · rfl
      · exact absurd (((T.MP m hTm).isZero_iff _).mp h) ha0v) z hz θ hθ s hs2 hs'
  have hN₀ : 1 ≤ N₀ := by
    have hspec0 := torsOracleC_specF (redAtKF Fc m rs) cpf (fun p _ R h ↦ redAtKF_valid Fc m rs p R h)
      ps bound hsq0 hcop0
    exact ((hspec0 1 ![(0 : KF Fc m)] ![1] ![1] (fun q ↦ by fin_cases q; simp [hf0])
      (fun a b _ ↦ Subsingleton.elim a b)).1 N₀ ht0).1
  obtain ⟨hWz, hWzo⟩ := T.kx_W0 m hTr A hsq hdegA hcopA θ hθ z b₀ μ₀ hb₀ hb₀2 hμ₀ hμb hpf0 hd0 hf0
    N₀ W0b hw0
  set β₀ := algebraMap (T.F m) (AlgebraicClosure (T.F m)) b₀
  have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) _).injective).mpr hb₀
  have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 := by
    rw [hp0v]; show β₀ ^ 2 = _; rw [← map_pow, hb₀2]
  obtain ⟨q0, hq0⟩ := kxZ_some hz
  have hz0 : T.ev m z ≠ 0 := (T.ke_z_facts hmon hdeg m hn hc A (by
      cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
      · rfl
      · exact absurd (((T.MP m hTm).isZero_iff _).mp h) ha0v) q0 z hq0).1
  have hκ0 : kxKap Fc ks m A z ≠ 0 := (T.ke_z_facts hmon hdeg m hn hc A (by
      cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
      · rfl
      · exact absurd (((T.MP m hTm).isZero_iff _).mp h) ha0v) q0 z hq0).2.2
  have hs0 : s ≠ 0 := fun h0 ↦ hκ0 (by
    rw [h0, zero_pow two_ne_zero] at hs2; exact_mod_cast hs2.symm)
  set Wz := ((toB W0b).map (mapRingHom (T.psiF m hTm))).comp (Polynomial.C (Polynomial.C μ₀) * X)
    with hWzdef
  set W0z := aeval (T.ts m) (((toB W0b).map (mapRingHom (T.psiF m hTm))).coeff 0) with hW0z
  set W1z := ((μ₀ : T.F m) : L) * aeval (T.ts m) (((toB W0b).map (mapRingHom (T.psiF m hTm))).coeff 1)
    with hW1z
  have hmemx : ∀ P : (T.F m)[X], aeval (T.ts m) P ∈ (T.F m)⟮S.x⟯ := fun P ↦ by
    letI := algebraAdjoinSimple (F := T.F m) S.x
    rw [show aeval (T.ts m) P = aeval S.x P from rfl, ← algebraMap_adjoinSimple (F := T.F m) S.x P]
    exact SetLike.coe_mem _
  have hWez : ((S.elemW Wz : (T.F m)⟮S.x⟯⟮S.y⟯) : L) = W0z + W1z * S.y := by
    rw [T.elemW_two S rfl Wz]
    simp only [hWzdef, comp_C_mul_X_coeff, pow_zero, mul_one, pow_one, hW0z, hW1z]
    rw [map_mul, aeval_C]
    simp only [IntermediateField.algebraMap_apply]
    have hSx : S.x = T.ts m := rfl
    rw [hSx]
    ring
  have hW1zm : W1z ∈ (T.F m)⟮S.x⟯ := mul_mem (IntermediateField.algebraMap_mem _ μ₀) (hmemx _)
  have hNmz : W0z ^ 2 - W1z ^ 2 * aeval S.x S.p ≠ 0 := fun h0 ↦ by
    have hy2 : S.y ^ 2 = aeval S.x S.p := S.hy
    have hodd : Odd S.p.natDegree := by
      rw [← Nat.coprime_two_left]; exact hcopS
    have hny := not_mem_of_sq_odd (C := T.F m) S.x S.y S.htr S.p hodd hy2
    have hfac : (W0z + W1z * S.y) * (W0z - W1z * S.y) = 0 := by rw [← h0, ← hy2]; ring
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact hWz (Subtype.ext (by rw [hWez, h1]; rfl))
    · by_cases hw1 : W1z = 0
      · apply hWz; apply Subtype.ext
        rw [hWez, hw1, zero_mul, add_zero]
        rw [hw1, zero_mul, sub_zero] at h1
        rw [h1]; rfl
      · apply hny
        rw [show S.y = W0z / W1z by field_simp; linear_combination -h1]
        exact div_mem (hmemx _) hW1zm
  have hcol0 : T.ev (m + 1) (kxCol0 Fc ks m A z W0b) = s *
      ((W0z * (W1z′ + W1z * (aeval S.x (mapCoeffs S.p + Polynomial.C (T.val m g)′ * X *
          derivative S.p) / ((S.n : L) * aeval S.x S.p))) - W0z′ * W1z) /
        (W0z ^ 2 - W1z ^ 2 * aeval S.x S.p)) :=
    T.kx_col0 m hTr hk (by omega) A hsq hdegA hcopA θ hθ z hz0 s hs0 hs2 hs' μ₀ hμv W0b hNmz
  obtain ⟨aa, haa, e, he, hae⟩ := S.kxe_tors_W0 (K := AlgebraicClosure (T.F m)) (T.val m g)′
    (T.keS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) hk) (fun c ↦ deriv_algebraMap c)
    (T.kxS_good m MS.hyp hk) (T.keS_constC m)
    (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj hc0K
    (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kxMNm Fc ks m g A B kt l cs q) (kxCl m g A B kt l cs)
    (fun k ↦ SqrtIndep.prodRoots rtsF (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] /
      (kxDenM Fc ks m g A B kt l cs : T.F m))
    (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hTm) B) l _ hb
    _ (fun q' ↦ X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR hRne
    hDoff hbP hres rfl hcopS β₀ hβ0 hv0 N₀ (by omega) (S.elemW Wz) hWz hWzo Ns (fun k ↦ hN k) W hW
    hWord (Fin.cons W0z W0) (Fin.cons W1z W1)
    (fun i ↦ Fin.cases (hmemx _) (fun k ↦ hW0 k) i) (fun i ↦ Fin.cases hW1zm (fun k ↦ hW1 k) i)
    (fun i ↦ Fin.cases hWez (fun k ↦ hWe k) i) (fun i ↦ Fin.cases hNmz (fun k ↦ hNm k) i)
    hbm sI c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ (hu i hi).2⟩) v
    (T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ hv) (by rw [hby]; exact heq)
  rw [hby] at hae
  have hSy : S.y = θ * ((1 : T.F m) : L) := rfl
  have hlist : [kxCol0 Fc ks m A z W0b] ++ List.ofFn (fun k ↦ kxCol Fc ks m g A B kt l cs
      (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (Wbs k)) =
      List.ofFn (Fin.cons (kxCol0 Fc ks m A z W0b) (fun k ↦ kxCol Fc ks m g A B kt l cs
        (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] (Wbs k))) := by
    rw [List.ofFn_succ]; simp
  rw [hlist]
  refine T.prde_forward_ofFn m hTr A hA0 θ hθ hspecA _ _ aa ((T.mem_F_succ).mpr haa)
    (Fin.cons (algebraMap (T.F m) L (e 0) / s) (fun k ↦ algebraMap (T.F m) L (e k.succ) * μ k))
    (fun i ↦ Fin.cases (by
      show (algebraMap (T.F m) L (e 0) / s)′ = 0
      rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, he 0, hs']; simp)
      (fun k ↦ by
        show (algebraMap (T.F m) L (e k.succ) * μ k)′ = 0
        rw [Derivation.leibniz, he k.succ, hμd k]; simp) i) ?_
  rw [hae, hSy]
  simp only [IntermediateField.coe_one, mul_one]
  congr 1
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  · rw [hcol0]; field_simp
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← hcolv k]
    ring

end Forward

end MTower

end Curves.MT
