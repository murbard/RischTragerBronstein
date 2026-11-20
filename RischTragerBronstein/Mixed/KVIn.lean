import RischTragerBronstein.Mixed.KVMain

/-!
# Radicals with poles over a logarithm: positive answers are stable under extension

**`kvDecide_in`**: when `kvDecideC` answers `some true`, the integrand
`B(t) θʲ / (∏_q (t − c_q) A(t)ˡ)` has an elementary integral over *every* elementary extension
of `L` (`HasElementaryIntegralIn`), so it can be added to other integrable terms
(`HasElementaryIntegral.add_in`).
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

set_option maxHeartbeats 4000000 in
open Classical in
/-- **A positive answer of `kvDecide` holds over every elementary extension.** -/
theorem kvDecide_in (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime n (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ n = T.evP m A)
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (hdec : kvDecideC Fc ks lv m n j η M zN gs A B l cs cpf ps bound rs = some true) :
    HasElementaryIntegralIn (T.ev (m + 1) ((B, kvDen Fc ks m A l cs) : LC (m + 1)) * θ ^ j) := by
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
  · rw [if_pos (by simpa using hcst)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hcst])] at hdec
  by_cases hF : kvFieldOK Fc ks m n j η A B l cs M zN gs = true
  swap
  · rw [if_pos (by simpa using hF)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hF])] at hdec
  obtain ⟨htrim, hlen, -, -, -, -⟩ := kvFieldOK_spec hF
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length) with hcomps
  set tors := comps.map (kvTorsC Fc ks m n j M η A B l cs zN gs cpf ps bound rs) with htorsdef
  by_cases hnone : tors.any (· == none) = true
  · rw [if_pos hnone] at hdec; exact absurd hdec (by simp)
  rw [if_neg hnone] at hdec
  by_cases hsn : tors.any (· == some none) = true
  · rw [if_pos hsn] at hdec; exact absurd hdec (by simp)
  rw [if_neg hsn] at hdec
  have hall : ∀ f ∈ comps,
      ∃ N, kvTorsC Fc ks m n j M η A B l cs zN gs cpf ps bound rs f = some (some N) := by
    intro f hf
    rcases h : kvTorsC Fc ks m n j M η A B l cs zN gs cpf ps bound rs f with _ | _ | N
    · exact absurd (List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨f, hf, h⟩, by simp⟩) hnone
    · exact absurd (List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨f, hf, h⟩, by simp⟩) hsn
    · exact ⟨N, rfl⟩
  obtain ⟨Ns, Wbs, colss, -, -, hcol, hbeq⟩ :=
    kvSolve_spec (lv := lv) m n j η M zN gs A B l cs ps bound rs true hall hdec
  exact T.ky_backward m n j hn0 hjn hTr A θ hθ hA0 M htrim hlen hspecA _ [] (by simp) Wbs
    colss hcol (by simpa using hbeq.symm)

end MTower

end Curves.MT
