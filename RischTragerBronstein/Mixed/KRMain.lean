import RischTragerBronstein.Mixed.KRForward

/-!
# Radicals `θⁿ = A(t)` over an exponential level: correctness of `krDecide`

`krDecide_correct`: whenever `krDecide` answers `some b`, the integral of `B(t) θʲ / (tᵏ A(t)ˡ)`
(`t` an exponential level of a certified tower, `θⁿ = A(t)`, `A` squarefree of degree prime to `n`)
is elementary exactly when `b = true`.
-/

open Polynomial Differential IntermediateField CPoly Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The setup** for a realization: the curve data and the specification of the Risch solver. -/
lemma kr_setup (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (n j : ℕ) (A : GPoly (LC m))
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true) (hdegpos : 0 < degG (MO Fc ks m) A)
    (hcop : Nat.Coprime n (degG (MO Fc ks m) A)) :
    ∃ hTr : T.Tr (m + 1), Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A) ∧
      0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree ∧
      Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree ∧ T.MixHyp (m + 1) ∧
      RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
        ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
        (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)) ∧ T.evP m A ≠ 0 := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  exact ⟨hTr, GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc, by rw [hdeg1]; exact hdegpos,
    by rw [hdeg1]; exact hcop, MS.hyp, MS.rde _ (T.kpFr_ok m hTr j n A),
    MTower.evP_ne_zero T m hTr (by omega) A hdegpos⟩

lemma kr_a0 (m : ℕ) (hTm : T.Tr m) (A : GPoly (LC m))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) :
    (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 := fun h0 ↦ by
  rw [← (T.MP m hTm).isZero_iff] at h0; rw [h0] at ha0; exact Bool.noConfusion ha0

lemma kr_zsem (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m n : ℕ) (hn0 : 0 < n)
    (hTn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (hTm : T.Tr m) (A : GPoly (LC m))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) (z : LC m)
    (hz : krZ Fc ks lv m n A = some z) :
    (T.MP m hTm).sem z ≠ 0 ∧ (T.MP m hTm).sem z ^ n * (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) =
      (((ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
        (A.getD 0 (MO Fc ks m).zero))).getD 0 : ℚ) : T.F m) := by
  obtain ⟨hz0, hzκ, -⟩ := T.kr_z_facts hmon hdeg m n hn0 hTn hc A ha0 z hz
  refine ⟨fun h ↦ hz0 (by rw [← T.sem_MP m hTm, h]; rfl), Subtype.ext ?_⟩
  rw [IntermediateField.coe_mul, IntermediateField.coe_pow, T.sem_MP m hTm, T.sem_MP m hTm, hzκ]
  simp

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`krDecide` is correct**: whenever it answers `some b`, the integral of
`B(t) θʲ / (tᵏ A(t)ˡ)` (`θⁿ = A(t)`, `t` an exponential level of a certified tower) is elementary
exactly when `b = true`. -/
theorem krDecideC_correct [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g) (n j : ℕ)
    [Fact (Irreducible (toPoly (cycK Fc m n)))] (A : GPoly (LC m))
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true) (hdegpos : 0 < degG (MO Fc ks m) A)
    (hcop : Nat.Coprime n (degG (MO Fc ks m) A)) (θ : L) (hθ : θ ^ n = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (NFz Fc m n) → CertProv (NFz Fc m n)) (b : Bool)
    (hdec : krDecideC Fc ks lv m n j A B kt l cpf ps bound rs = some b) :
    HasElementaryIntegral (T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) * θ ^ j) ↔ b = true := by
  obtain ⟨hTr, hsq, hdegA, hcopA, hM, hspecA, hA0⟩ :=
    T.kr_setup (lv := lv) hmon hdeg m hn hc n j A hsqc hdegpos hcop
  have hTm : T.Tr m := hTr.of_succ
  unfold krDecideC at hdec
  dsimp only at hdec
  by_cases hchk : (decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) = true
  swap
  · simp only [Bool.not_eq_true] at hchk
    simp [hchk] at hdec
  rw [if_neg (by simp only [hchk, Bool.not_true]; decide)] at hdec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hn1, hj0⟩, hjn⟩, hjc⟩ := hchk
  have hn0 : 0 < n := by omega
  by_cases ha0t : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = true
  · rw [if_pos ha0t] at hdec; exact absurd hdec (by simp)
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by simpa using ha0t
  rw [if_neg (by rw [ha0]; decide)] at hdec
  have hrhs : T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) * θ ^ j =
      T.ev (m + 1) ((B, denC Fc ks m kt l A) : LC (m + 1)) * θ ^ j := by
    rw [T.ev_rhs m hTr A B]
  rcases hz : krZ Fc ks lv m n A with _ | z
  · -- no `n`-th root of `A(0)`
    simp only [hz] at hdec
    obtain rfl := Option.some.inj hdec
    constructor
    · intro hf
      obtain ⟨E, _, _, _, TE, θE, -, ζ, ι, sI, c, u, v, hTEn, hθE, -, -, hζ, hζ', hcd, hu, hv, heq⟩ :=
        T.kr_lift m hn n hn0 A θ hθ hgen B kt l j hf 1 one_ne_zero
      obtain ⟨ω, hω, -⟩ := TE.root_in_F m n ζ hζ hζ'
      obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
        TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
      exact TE.kr_forward_noz hmon hdeg m hTEn hc hTrE A hsqE hdegAE n hn0 hn1 hcopAE θE hθE hME
        (by omega) hk (TE.kr_a0 m hTrE.of_succ A ha0) hz ω hω j hj0 hjn hjc hspecE B kt l sI c u
        hcd hu v hv heq
    · intro h
      rw [hrhs]
      exact (T.rde_backward_N m n j hn0 hTr A θ hθ hA0 hspecA _ h).hasElementaryIntegral
  · simp only [hz] at hdec
    obtain ⟨-, -, hκ0⟩ := T.kr_z_facts hmon hdeg m n hn0 hn hc A ha0 z hz
    obtain ⟨hz0, -⟩ := T.kr_zsem hmon hdeg m n hn0 hn hc hTm A ha0 z hz
    have hz0L : T.ev m z ≠ 0 := fun h ↦ hz0 (Subtype.ext (by rw [T.sem_MP m hTm]; exact h))
    set κ : ℚ := (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
      (A.getD 0 (MO Fc ks m).zero))).getD 0 with hκdef
    rw [if_neg hκ0] at hdec
    rcases htors : krTorsC Fc ks m n A z κ cpf ps bound rs with _ | _ | N
    · simp only [htors] at hdec; exact absurd hdec (by simp)
    · -- `Ψ` not torsion
      simp only [htors] at hdec
      obtain rfl := Option.some.inj hdec
      constructor
      · intro hf
        obtain ⟨E, _, _, _, TE, θE, s, ζ, ι, sI, c, u, v, hTEn, hθE, hsn, hs', hζ, hζ', hcd, hu, hv,
          heq⟩ := T.kr_lift m hn n hn0 A θ hθ hgen B kt l j hf κ hκ0
        obtain ⟨ω, hω, -⟩ := TE.root_in_F m n ζ hζ hζ'
        obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
          TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
        obtain ⟨hZ0E, hzκE⟩ := TE.kr_zsem hmon hdeg m n hn0 hTEn hc hTrE.of_succ A ha0 z hz
        obtain ⟨sF, hsF, -⟩ : ∃ sF : TE.F m, sF ^ n = (κ : TE.F m) ∧ (sF : E) = s := by
          obtain ⟨c0, hc0⟩ := TE.hconst s hs'
          exact ⟨⟨s, hc0 ▸ TE.const_mem m c0⟩, Subtype.ext (by simpa using hsn), rfl⟩
        exact TE.kr_forward_nontors m hTrE A hsqE hdegAE n hn0 hn1 hcopAE θE hθE hME (by omega) hk
          ω hω z κ hZ0E hzκE hκ0 sF hsF ps bound rs cpf htors j hj0 hjn hjc hspecE B kt l sI c u hcd hu
          v hv heq
      · intro h
        rw [hrhs]
        exact (T.rde_backward_N m n j hn0 hTr A θ hθ hA0 hspecA _ h).hasElementaryIntegral
    · -- torsion
      simp only [htors] at hdec
      rcases hwit : krWit Fc ks m n A z κ N with _ | Wb
      · simp only [hwit] at hdec; exact absurd hdec (by simp)
      simp only [hwit] at hdec
      rcases hdsc : descendNF Fc m n (normNF Fc m n Wb) with _ | W0b
      · simp only [hdsc] at hdec; exact absurd hdec (by simp)
      simp only [hdsc] at hdec
      rcases hcolc : krCol Fc ks m n (krAh Fc ks m n A z κ) z j W0b with _ | col
      · simp only [hcolc] at hdec; exact absurd hdec (by simp)
      simp only [hcolc] at hdec
      obtain rfl := Option.some.inj hdec
      constructor
      · intro hf
        obtain ⟨E, _, _, _, TE, θE, s, ζ, ι, sI, c, u, v, hTEn, hθE, hsn, hs', hζ, hζ', hcd, hu, hv,
          heq⟩ := T.kr_lift m hn n hn0 A θ hθ hgen B kt l j hf κ hκ0
        obtain ⟨ω, hω, -⟩ := TE.root_in_F m n ζ hζ hζ'
        obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
          TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
        obtain ⟨hZ0E, hzκE⟩ := TE.kr_zsem hmon hdeg m n hn0 hTEn hc hTrE.of_succ A ha0 z hz
        obtain ⟨sF, hsF, -⟩ : ∃ sF : TE.F m, sF ^ n = (κ : TE.F m) ∧ (sF : E) = s := by
          obtain ⟨c0, hc0⟩ := TE.hconst s hs'
          exact ⟨⟨s, hc0 ▸ TE.const_mem m c0⟩, Subtype.ext (by simpa using hsn), rfl⟩
        exact TE.kr_forward_tors m hTrE A hsqE hdegAE n hn0 hn1 hcopAE θE hθE hME (by omega) hk
          ω hω z κ hZ0E hzκE hκ0 sF hsF ps bound rs cpf N htors Wb hwit W0b hdsc j hj0 hjn hjc col hcolc
          hspecE B kt l sI c u hcd hu v hv heq
      · intro h
        rw [hrhs]
        refine (T.prde_backward_genN m n j hn0 hTr A θ hθ hA0 hspecA _ [col] (fun c hc q ↦ ?_)
          h).hasElementaryIntegral
        rw [List.mem_singleton] at hc
        subst hc
        exact T.kr_col_hei m n j hn0 hjn hTr A θ hθ hA0 z hz0L κ hκ0 W0b _ hcolc q

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`krDecide` is correct**: whenever it answers `some b`, the integral of
`B(t) θʲ / (tᵏ A(t)ˡ)` (`θⁿ = A(t)`, `t` an exponential level of a certified tower) is elementary
exactly when `b = true`. -/
theorem krDecide_correct [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g) (n j : ℕ)
    [Fact (Irreducible (toPoly (cycK Fc m n)))] (A : GPoly (LC m))
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true) (hdegpos : 0 < degG (MO Fc ks m) A)
    (hcop : Nat.Coprime n (degG (MO Fc ks m) A)) (θ : L) (hθ : θ ^ n = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool)
    (hdec : krDecide Fc ks lv m n j A B kt l ps bound rs = some b) :
    HasElementaryIntegral (T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) * θ ^ j) ↔ b = true :=
  T.krDecideC_correct hmon hdeg m hn hc hk n j A hsqc hdegpos hcop θ hθ hgen B kt l ps bound rs _ b hdec

end MTower

end Curves.MT
