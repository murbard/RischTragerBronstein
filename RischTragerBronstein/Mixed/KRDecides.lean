import RischTragerBronstein.Mixed.KRMain
import RischTragerBronstein.Mixed.KRGcdT
import RischTragerBronstein.Mixed.KRSpec

/-!
# Radicals over an exponential level: the decision always answers

`krDecideL` (local torsion certificates over `Kₘ(ζₙ)`) answers for every large bound at suitable
residues (`krDecideL_decides`): the oracle answers (`kfz_query_els`), a torsion answer yields a
witness (`witW_ne_none`), its norm descends (`descendNF_normNF_isSome`) and the column
computation succeeds (`kr_gcd_coprime`). With `krDecideC_correct`: `kr_decided`.
-/

open Polynomial Differential IntermediateField CPoly CPoly.Kron Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **The twisted curve over the code fields.** -/
theorem krFK_facts (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (n : ℕ) (hn0 : 0 < n)
    [Fact (Irreducible (toPoly (cycK Fc m n)))] (A : GPoly (LC m))
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true) (hdegpos : 0 < degG (MO Fc ks m) A)
    (hcop : Nat.Coprime n (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) (z : LC m)
    (hz : krZ Fc ks lv m n A = some z) :
    let κ := (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
      (A.getD 0 (MO Fc ks m).zero))).getD 0
    let fK := krFK Fc ks m n A z κ
    let P0 := toPoly ((krAh Fc ks m n A z κ).map (trC Fc m))
    0 < fK.length - 1 ∧ fK.getD (fK.length - 1) 0 ≠ 0 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime n (fK.length - 1) ∧ (toPoly fK).eval 0 = 1 ∧ Squarefree P0 ∧
      0 < P0.natDegree := by
  intro κ fK P0
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  obtain ⟨hz0, hzκ⟩ := T.kr_zsem hmon hdeg m n hn0 hn hc hTm A ha0 z hz
  obtain ⟨-, -, hκ0⟩ := T.kr_z_facts hmon hdeg m n hn0 hn hc A ha0 z hz
  set cF : T.F m := (T.MP m hTm).sem ((MO Fc ks m).mul (powC (MO Fc ks m) z n) (mcst Fc ks m κ⁻¹))
  have hcF : cF = (T.MP m hTm).sem z ^ n * ((κ⁻¹ : ℚ) : T.F m) := by
    simp only [cF]; rw [(T.MP m hTm).sem_mul, sem_powC, T.sem_mcst]
  have hκF : ((κ : ℚ) : T.F m) ≠ 0 := by exact_mod_cast hκ0
  have hc0 : cF ≠ 0 := by
    rw [hcF]; exact mul_ne_zero (pow_ne_zero _ hz0) (by push_cast; exact inv_ne_zero hκF)
  have hpf : P0.map (T.psiF m hTm) = C cF * GPoly.toPoly (T.MP m hTm) A := by
    simp only [P0]
    rw [T.toPoly_trC_map m hTm]
    have e : krAh Fc ks m n A z κ = GPoly.smul (MO Fc ks m) ((MO Fc ks m).mul
        (powC (MO Fc ks m) z n) (mcst Fc ks m κ⁻¹)) A := rfl
    rw [e, GPoly.toPoly_smul]
  have hsqI : Squarefree (C cF * GPoly.toPoly (T.MP m hTm) A) :=
    (Associated.squarefree_iff (associated_unit_mul_left _ (C cF)
      (isUnit_C.mpr (Ne.isUnit hc0)))).mpr hsq
  have hP0sq : Squarefree P0 := squarefree_of_map (T.psiF m hTm) P0 (by rw [hpf]; exact hsqI)
  have hP0deg : P0.natDegree = degG (MO Fc ks m) A := by
    rw [← natDegree_map_eq_of_injective (T.psiF m hTm).injective, hpf, natDegree_C_mul hc0, hdeg1]
  have hP0e : P0.eval 0 = 1 := by
    apply (T.psiF m hTm).injective
    rw [map_one, ← eval₂_at_apply, map_zero, ← eval_map, hpf, eval_mul, eval_C,
      T.toPoly_eval_zero m hTm, hcF, mul_assoc, mul_comm (((κ⁻¹ : ℚ) : T.F m)), ← mul_assoc, hzκ]
    push_cast; exact mul_inv_cancel₀ hκF
  -- over `Kₘ(ζ)`
  have hfK : toPoly fK = P0.map (eNF Fc m n) := by
    simp only [fK, krFK]
    rw [CPoly.toPoly_trim, ← toPoly_map']; rfl
  have hsep : (toPoly fK).Separable := by
    rw [hfK]; exact (PerfectField.separable_iff_squarefree.mpr hP0sq).map
  have hne : toPoly fK ≠ 0 := hsep.squarefree.ne_zero
  have hnd : (toPoly fK).natDegree = degG (MO Fc ks m) A := by
    rw [hfK, natDegree_map_eq_of_injective (eNF Fc m n).injective, hP0deg]
  have htrim : CPoly.trim fK = fK := by simp only [fK, krFK, CPoly.trim_trim]
  have htne : CPoly.trim fK ≠ [] := fun h0 ↦ hne ((CPoly.trim_eq_nil_iff fK).mp h0)
  have hlen := CPoly.length_trim htne
  rw [htrim] at hlen
  have hl1 : fK.length - 1 = degG (MO Fc ks m) A := by omega
  refine ⟨by omega, ?_, hsep.squarefree, hl1 ▸ hcop, ?_, hP0sq, by omega⟩
  · rw [← coeff_toPoly, show fK.length - 1 = (toPoly fK).natDegree by omega]
    exact leadingCoeff_ne_zero.mpr hne
  · rw [hfK, eval_map, ← map_zero (eNF Fc m n), eval₂_at_apply, hP0e, map_one]

/-- `kfz_query_els` for a divisor given by its points. -/
theorem kfz_query_els_gamma (m n : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))] (hn : 2 ≤ n)
    {fK : CPoly (NFz Fc m n)} (hd : 0 < fK.length - 1) (hlc : fK.getD (fK.length - 1) 0 ≠ 0)
    (hsq : Squarefree (toPoly fK)) (hcop : Nat.Coprime n (fK.length - 1)) {r : ℕ}
    (α β : Fin r → NFz Fc m n) (mq : Fin r → ℕ)
    (hv : ∀ q, β q ≠ 0 ∧ β q ^ n = (toPoly fK).eval (α q))
    (hinj : Function.Injective fun q ↦ (α q, β q)) :
    ∃ Els : List (KF Fc m), ∀ rs : ℕ → ℕ, rs 0 ∉ kfBad Fc → (∀ x ∈ Els, specB Fc rs m x = true) →
      ∃ B0, ∀ B, B0 ≤ B →
        (torsOracleC (redAtNF Fc m n rs) (localCert fK n) (primesBelow B) B fK n
          (Sup.gammaL α β mq 1)).isSome := by
  set l := Sup.gammaL α β mq 1 with hl
  have hlen : l.length = r := by simp [hl, Sup.gammaL]
  set e : Fin l.length ≃ Fin r := finCongr hlen with he
  have hget : ∀ q : Fin l.length, l.get q = (α (e q), β (e q), 1 * mq (e q)) := by
    intro q
    simp [hl, Sup.gammaL, he]
    exact ⟨rfl, rfl, rfl⟩
  refine kfz_query_els Fc m n hn hd hlc hsq hcop l (fun q ↦ ?_) (fun q q' h ↦ ?_)
  · rw [hget q, evalC_eq]; exact hv (e q)
  · simp only [hget] at h
    exact e.injective (hinj h)

lemma natDegree_lt_of_witW {F : Type*} [Field F] [DecidableEq F] {Wb : BPoly F} {n : ℕ}
    (h0 : toB Wb ≠ 0) (h : ∀ i a, ((toB Wb).coeff i).coeff a ≠ 0 → i < n) :
    (toB Wb).natDegree < n := by
  have hl : (toB Wb).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr h0
  obtain ⟨a, ha⟩ : ∃ a, ((toB Wb).leadingCoeff).coeff a ≠ 0 := by
    by_contra hc; push Not at hc; exact hl (Polynomial.ext hc)
  exact h _ a ha

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`krDecideL` answers** for every large bound, at suitable residues. -/
theorem krDecideL_decides (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (n j : ℕ)
    [Fact (Irreducible (toPoly (cycK Fc m n)))] (A : GPoly (LC m))
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true) (hdegpos : 0 < degG (MO Fc ks m) A)
    (hcop : Nat.Coprime n (degG (MO Fc ks m) A)) (B : GPoly (LC m)) (kt l : ℕ)
    (hn1 : 1 < n) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (krDecideL Fc ks lv m n j A B kt l (primesBelow Bd) Bd rs).isSome := by
  have hn0 : 0 < n := by omega
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hpre : ∀ rs Bd, krDecideL Fc ks lv m n j A B kt l (primesBelow Bd) Bd rs =
      match krZ Fc ks lv m n A with
      | none => some (rdeOKFr Fc ks lv (m + 1) (kpFr Fc ks m j n A) (B, denC Fc ks m kt l A))
      | some z =>
        let κ := (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
          (A.getD 0 (MO Fc ks m).zero))).getD 0
        if κ = 0 then none
        else
          match krTorsC Fc ks m n A z κ (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs with
          | none => none
          | some none => some (rdeOKFr Fc ks lv (m + 1) (kpFr Fc ks m j n A) (B, denC Fc ks m kt l A))
          | some (some N) =>
            match krWit Fc ks m n A z κ N with
            | none => none
            | some Wb =>
              match descendNF Fc m n (normNF Fc m n Wb) with
              | none => none
              | some W0 =>
                match krCol Fc ks m n (krAh Fc ks m n A z κ) z j W0 with
                | none => none
                | some col => some ((prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)
                    [(B, denC Fc ks m kt l A), col]).any fun r ↦ decide (r.1.getD 0 0 ≠ 0)) := by
    intro rs Bd
    unfold krDecideL krDecideC
    dsimp only
    rw [if_neg (by simp [hn1, hj0, hjn, hjc]), if_neg (by rw [ha0]; decide)]
    rfl
  rcases hz : krZ Fc ks lv m n A with _ | z
  · exact ⟨fun _ ↦ 0, 0, fun Bd _ ↦ by rw [hpre, hz]; rfl⟩
  obtain ⟨-, -, hκ0⟩ := T.kr_z_facts hmon hdeg m n hn0 hn hc A ha0 z hz
  set κ := (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
      (A.getD 0 (MO Fc ks m).zero))).getD 0 with hκ
  obtain ⟨hd, hlc, hsqK, hcop2, hf0, hP0sq, hP0deg⟩ :=
    T.krFK_facts hmon hdeg m hn hc n hn0 A hsqc hdegpos hcop ha0 z hz
  set fK := krFK Fc ks m n A z κ with hfK
  have hprim := zetaN_prim Fc m n hn0
  have hv : ∀ k : Fin n, zetaN Fc m n ^ (k : ℕ) ≠ 0 ∧
      (zetaN Fc m n ^ (k : ℕ)) ^ n = (toPoly fK).eval ((fun _ : Fin n ↦ (0 : NFz Fc m n)) k) := by
    intro k
    refine ⟨pow_ne_zero _ (hprim.ne_zero hn0.ne'), ?_⟩
    rw [hf0, ← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  have hinj : Function.Injective fun k : Fin n ↦
      ((fun _ : Fin n ↦ (0 : NFz Fc m n)) k, zetaN Fc m n ^ (k : ℕ)) := by
    intro k k' h
    exact Fin.ext (hprim.pow_inj k.2 k'.2 (congrArg Prod.snd h))
  obtain ⟨Els, hEls⟩ := kfz_query_els_gamma (Fc := Fc) m n (by omega) hd hlc hsqK hcop2
    (fun _ : Fin n ↦ (0 : NFz Fc m n)) (fun k ↦ zetaN Fc m n ^ (k : ℕ)) (ramMult n) hv hinj
  obtain ⟨rs, h0, hE⟩ := exists_rs Fc m Els (kfBad Fc) (kfBad_finite Fc)
  obtain ⟨B0, hB0⟩ := hEls rs h0 hE
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  rw [hpre, hz]
  dsimp only
  rw [if_neg hκ0]
  have hsome := hB0 Bd hBd
  have hspec := torsOracleC_spec (redAtNF Fc m n rs) (localCert fK n)
    (fun p _ R h ↦ MTower.redAtNF_valid (Fc := Fc) m n rs p R h) (primesBelow Bd) Bd hsqK hcop2
  rcases ht : krTorsC Fc ks m n A z κ (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs
    with _ | _ | N
  · exfalso
    have ht' : torsOracleC (redAtNF Fc m n rs) (localCert fK n) (primesBelow Bd) Bd fK n
        (Sup.gammaL (fun _ : Fin n ↦ (0 : NFz Fc m n)) (fun k ↦ zetaN Fc m n ^ (k : ℕ)) (ramMult n) 1)
        = none := ht
    rw [ht'] at hsome; exact absurd hsome (by simp)
  · rfl
  · dsimp only
    have hP := ((hspec n _ _ (ramMult n) hv hinj).1 N ht).2
    have hΓ : ∀ k : Fin n, ((n : ℕ) : NFz Fc m n) * (zetaN Fc m n ^ (k : ℕ)) ^ (n - 1) ≠ 0 ∧
        (zetaN Fc m n ^ (k : ℕ)) ^ n = (toPoly fK).eval ((fun _ : Fin n ↦ (0 : NFz Fc m n)) k) :=
      fun k ↦ ⟨mul_ne_zero (by exact_mod_cast hn0.ne') (pow_ne_zero _ (hv k).1), (hv k).2⟩
    have hw := witW_ne_none fK n hn0 (fK.length - 1) _ _ (ramMult n) N hΓ hP
    rcases hwit : krWit Fc ks m n A z κ N with _ | Wb
    · exact absurd hwit hw
    dsimp only
    obtain ⟨hWb0, hWbd, -⟩ := witW_spec fK n hn0 (fK.length - 1) _ _ (ramMult n) N hΓ hwit
    obtain ⟨W0b, hW0⟩ := Option.isSome_iff_exists.mp (descendNF_normNF_isSome Fc m n hn1 Wb)
    rw [hW0]
    dsimp only
    have hcopW := T.kr_gcd_coprime m n hn1 hTm Wb hWb0
      (natDegree_lt_of_witW hWb0 fun i a h ↦ (hWbd i a h).1) W0b hW0 (krAh Fc ks m n A z κ)
      hP0sq hP0deg
    rcases hcol : krCol Fc ks m n (krAh Fc ks m n A z κ) z j W0b with _ | col
    · exfalso
      unfold krCol at hcol
      simp only at hcol
      rw [if_pos (trim_egcd_length _ _ hcopW)] at hcol
      exact absurd hcol (by simp)
    · rfl

open Classical in
/-- **Radicals over an exponential level are decided**: at suitable residues, for every large
bound, `krDecideL` answers, and correctly. -/
theorem kr_decided (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (n j : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))] (A : GPoly (LC m))
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true) (hdegpos : 0 < degG (MO Fc ks m) A)
    (hcop : Nat.Coprime n (degG (MO Fc ks m) A)) (θ : L) (hθ : θ ^ n = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (hn1 : 1 < n) (hj0 : 0 < j) (hjn : j < n)
    (hjc : Nat.Coprime j n) (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd → ∃ b,
      krDecideL Fc ks lv m n j A B kt l (primesBelow Bd) Bd rs = some b ∧
      (HasElementaryIntegral (T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) * θ ^ j) ↔ b = true) := by
  obtain ⟨rs, B0, h⟩ := T.krDecideL_decides hmon hdeg m hn hc n j A hsqc hdegpos hcop B kt l hn1
    hj0 hjn hjc ha0
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h Bd hBd)
  exact ⟨b, hb, T.krDecideC_correct hmon hdeg m hn hc hk n j A hsqc hdegpos hcop θ hθ hgen B kt l
    _ _ rs _ b hb⟩

end MTower

end Curves.MT
