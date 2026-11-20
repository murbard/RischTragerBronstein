import RischTragerBronstein.Mixed.KVForward
import RischTragerBronstein.Mixed.KYMain

/-!
# Radicals with poles over a logarithm: the decision is correct

**`kvDecide_correct`**: whenever `kvDecideC` answers `some b`, the integral of
`B(t) θʲ / (∏_q (t − c_q) A(t)ˡ)` (`θⁿ = A(t)`, `t` a logarithmic level of a certified tower,
residues in the number field `ℚ[X]/(M)`) is elementary exactly when `b = true`. Over a
logarithm there is no Mordell–Weil exception: a component that is not torsion is impossible
(`kv_forward_neg`).
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

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

lemma kv_rootF (m : ℕ) (hTm : T.Tr m) (n j : ℕ) (hn : 0 < n) (η : LC m) (A B : GPoly (LC m))
    (l : ℕ) (cs : List (LC m)) (M zN : CPoly ℚ) (gs : List (CPoly ℚ))
    [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    (hF : kvFieldOK Fc ks m n j η A B l cs M zN gs = true)
    (ρE : L) (hρE : aeval ρE (toPoly M) = 0) (hρd : ρE′ = 0) :
    ∃ ρ : T.F m, aeval ρ (toPoly M) = 0 ∧ IsPrimitiveRoot (aeval ρ (toPoly zN)) n := by
  obtain ⟨htrim, hlen, h1, h2, -, -⟩ := kvFieldOK_spec hF
  obtain ⟨c0, hc0⟩ := T.hconst ρE hρd
  set ρ : T.F m := ⟨ρE, hc0 ▸ T.const_mem m c0⟩ with hρdef
  have hρ : aeval ρ (toPoly M) = 0 := by
    apply (algebraMap (T.F m) L).injective
    rw [← aeval_algebraMap_apply, map_zero]
    exact hρE
  have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
  have hM0 : toPoly M ≠ 0 := fun h ↦ hMne (by
    have := (CPoly.trim_eq_nil_iff M).mpr h; rwa [htrim] at this)
  have hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0 :=
    hmin_of_irr M ρ hρ (K := KF Fc m) (by rw [← toPoly_liftQ]; exact Fact.out)
  exact ⟨ρ, hρ, zeta_prim M ρ hρ hmin hM0 n hn zN h1 h2⟩

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`kvDecide` is correct**: whenever it answers `some b`, the integral of
`B(t) θʲ / (∏_q (t − c_q) A(t)ˡ)` (`θⁿ = A(t)`, `t` a logarithmic level of a certified tower,
residues in the number field `ℚ[X]/(M)`) is elementary exactly when `b = true`. -/
theorem kvDecide_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime n (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ n = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (b : Bool) (hdec : kvDecideC Fc ks lv m n j η M zN gs A B l cs cpf ps bound rs = some b) :
    HasElementaryIntegral (T.ev (m + 1) ((B, kvDen Fc ks m A l cs) : LC (m + 1)) * θ ^ j) ↔
      b = true := by
  obtain ⟨hTr, hsq, hdegA, hcopA, hM, hspecA, hA0⟩ :=
    T.kr_setup (lv := lv) hmon hdeg m hn hc n j A hsqc hdegpos hcop
  unfold kvDecideC at hdec
  dsimp only at hdec
  by_cases hchk : (decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) = true
  swap
  · simp only [Bool.not_eq_true] at hchk
    simp [hchk] at hdec
  rw [if_neg (by simp only [hchk, Bool.not_true]; decide)] at hdec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hn1, hj0⟩, hjn⟩, hjc⟩ := hchk
  have hn0 : 0 < n := by omega
  by_cases hr0 : cs.length = 0
  · rw [if_pos hr0] at hdec; exact absurd hdec (by simp)
  rw [if_neg hr0] at hdec
  by_cases hok : kqOK Fc ks m A B l cs = true
  swap
  · rw [if_pos (by simpa using hok)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hok])] at hdec
  by_cases hcst : kvConst Fc ks m n j η A B l cs = true
  swap
  · rw [if_pos (by simpa using hcst)] at hdec
    obtain rfl := Option.some.inj hdec
    simp only [Bool.false_eq_true, iff_false]
    intro hf
    obtain ⟨E, _, _, _, TE, θE, -, -, ι, sI, c, u, v, hTEn, hθE, -, -, -, -, hcd, hu, hv, heq⟩ :=
      T.ky_lift m hn n hn0 A θ hθ hgen _ j hf 1 one_ne_zero X (by simp)
    obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
      TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
    exact hcst (TE.kv_forward_const m hTrE A hsqE hdegAE n hn0 θE hθE hME (by omega) hk j hj0 hjn B
      l cs hok sI c u hcd hu v hv heq)
  rw [if_neg (by simp [hcst])] at hdec
  by_cases hF : kvFieldOK Fc ks m n j η A B l cs M zN gs = true
  swap
  · rw [if_pos (by simpa using hF)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hF])] at hdec
  obtain ⟨htrim, hlen, -, -, -, -⟩ := kvFieldOK_spec hF
  have hMdegpos : 0 < (toPoly M).natDegree := by
    have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
    have := CPoly.length_trim (p := M) (by rw [htrim]; exact hMne)
    rw [htrim] at this; omega
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length) with hcomps
  set tors := comps.map (kvTorsC Fc ks m n j M η A B l cs zN gs cpf ps bound rs) with htorsdef
  by_cases hnone : tors.any (· == none) = true
  · rw [if_pos hnone] at hdec; exact absurd hdec (by simp)
  rw [if_neg hnone] at hdec
  by_cases hsn : tors.any (· == some none) = true
  · -- a component is not torsion
    rw [if_pos hsn] at hdec
    obtain rfl := Option.some.inj hdec
    simp only [Bool.false_eq_true, iff_false]
    intro hf
    obtain ⟨x, hx, hx0⟩ := List.any_eq_true.mp hsn
    obtain ⟨f0, hf0, rfl⟩ := List.mem_map.mp hx
    have htk : kvTorsC Fc ks m n j M η A B l cs zN gs cpf ps bound rs f0 = some none := by
      simpa using hx0
    obtain ⟨E, _, _, _, TE, θE, -, ρE, ι, sI, c, u, v, hTEn, hθE, -, -, hρE, hρd, hcd, hu, hv,
      heq⟩ := T.ky_lift m hn n hn0 A θ hθ hgen _ j hf 1 one_ne_zero (toPoly M) hMdegpos
    obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
      TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
    obtain ⟨ρ, hρ, hζ⟩ := TE.kv_rootF m hTrE.of_succ n j hn0 η A B l cs M zN gs hF ρE hρE hρd
    exact TE.kv_forward_neg m hTrE A hsqE hdegAE n hn0 hcopAE θE hθE hME (by omega) hk j hj0 hjn
      hjc B l cs M ρ hρ zN gs hζ hok hcst hF ps bound rs f0 hf0 htk sI c u hcd hu v hv heq
  rw [if_neg hsn] at hdec
  have hall : ∀ f ∈ comps,
      ∃ N, kvTorsC Fc ks m n j M η A B l cs zN gs cpf ps bound rs f = some (some N) := by
    intro f hf
    rcases h : kvTorsC Fc ks m n j M η A B l cs zN gs cpf ps bound rs f with _ | _ | N
    · exact absurd (List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨f, hf, h⟩, by simp⟩) hnone
    · exact absurd (List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨f, hf, h⟩, by simp⟩) hsn
    · exact ⟨N, rfl⟩
  constructor
  · intro hf
    obtain ⟨E, _, _, _, TE, θE, -, ρE, ι, sI, c, u, v, hTEn, hθE, -, -, hρE, hρd, hcd, hu, hv,
      heq⟩ := T.ky_lift m hn n hn0 A θ hθ hgen _ j hf 1 one_ne_zero (toPoly M) hMdegpos
    obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
      TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
    obtain ⟨ρ, hρ, hζ⟩ := TE.kv_rootF m hTrE.of_succ n j hn0 η A B l cs M zN gs hF ρE hρE hρd
    exact TE.kv_forward_pos m hTrE A hsqE hdegAE n hn0 hcopAE θE hθE hME (by omega) hk j hj0 hjn
      hjc B l cs M ρ hρ zN gs hζ hok hcst hF hspecE sI c u hcd hu v hv heq ps bound rs hall b hdec
  · intro hb
    subst hb
    obtain ⟨Ns, Wbs, colss, -, -, hcol, hbeq⟩ :=
      kvSolve_spec (lv := lv) m n j η M zN gs A B l cs ps bound rs true hall hdec
    exact (T.ky_backward m n j hn0 hjn hTr A θ hθ hA0 M htrim hlen hspecA _ [] (by simp) Wbs
      colss hcol (by simpa using hbeq.symm)).hasElementaryIntegral

end MTower

end Curves.MT
