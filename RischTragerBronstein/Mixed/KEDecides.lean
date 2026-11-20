import RischTragerBronstein.Mixed.KEFull
import RischTragerBronstein.Mixed.KFSpecExist

/-!
# Square roots over an exponential level: the decision always answers

`keDecideL` (the decision with local torsion certificates, `localCert`) answers for every large
bound at suitable integer residues `rs` (`keDecideL_decides`); with `keDecideC_correct` the
integrals `∫ B(t) θ / tᵏ` (`θ² = A(t)`, `t` an exponential level) are **decided**
(`ke_decided`). The normalized curve `Â = c A` (`c = z²/κ`) is squarefree of odd degree with
`Â(0) = 1` (`ke_fK_facts`); the torsion oracle answers by `kf_torsLocal_exists`, and in the torsion
case the witness is found (`witW_ne_none`).
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

/-- **The normalized curve over the code field.** -/
theorem ke_fK_facts [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false) (q : List ℚ) (z : LC m)
    (hfind : (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) = some (q, z)) :
    let fK : CPoly (KF Fc m) := CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul
      ((MO Fc ks m).mul z z) (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul
        ((MO Fc ks m).mul z z) (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m))
    0 < fK.length - 1 ∧ fK.getD (fK.length - 1) 0 ≠ 0 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime 2 (fK.length - 1) ∧ (toPoly fK).eval 0 = 1 := by
  intro fK
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  obtain ⟨hz0, hκrel, hκ0⟩ := T.ke_z_facts hmon hdeg m hn hc A ha0 q z hfind
  set κ : ℚ := (ratValC Fc ks m ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
    (A.getD 0 (MO Fc ks m).zero))).getD 0 with hκdef
  have hκL : (κ : L) ≠ 0 := by exact_mod_cast hκ0
  set cF : T.F m := (T.MP m hTm).sem ((MO Fc ks m).mul ((MO Fc ks m).mul z z) (mcst Fc ks m κ⁻¹))
  have hcL : (cF : L) = T.ev m z * T.ev m z * (κ : L)⁻¹ := by
    simp only [cF]
    rw [(T.MP m hTm).sem_mul, (T.MP m hTm).sem_mul, T.sem_mcst, IntermediateField.coe_mul,
      IntermediateField.coe_mul, T.sem_MP m hTm]
    push_cast; rfl
  have hc0 : cF ≠ 0 := fun h0 ↦ by
    have := congrArg Subtype.val h0
    rw [hcL, IntermediateField.coe_zero] at this
    exact mul_ne_zero (mul_ne_zero hz0 hz0) (inv_ne_zero hκL) this
  have hpf : (toPoly fK).map (T.psiF m hTm) = C cF * GPoly.toPoly (T.MP m hTm) A := by
    simp only [fK]
    rw [CPoly.toPoly_trim, T.toPoly_trC_map m hTm]
    have e : A.map ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
        (mcst Fc ks m κ⁻¹))) = GPoly.smul (MO Fc ks m) ((MO Fc ks m).mul ((MO Fc ks m).mul z z)
        (mcst Fc ks m κ⁻¹)) A := rfl
    rw [e, GPoly.toPoly_smul]
  have hp0 : (C cF * GPoly.toPoly (T.MP m hTm) A).eval 0 = 1 := by
    rw [eval_mul, eval_C, T.toPoly_eval_zero m hTm]
    apply Subtype.ext
    rw [IntermediateField.coe_mul, hcL, T.sem_MP m hTm, IntermediateField.coe_one]
    rw [show T.ev m z * T.ev m z * (κ : L)⁻¹ * T.ev m (A.getD 0 (MO Fc ks m).zero) =
      (T.ev m z ^ 2 * T.ev m (A.getD 0 (MO Fc ks m).zero)) * (κ : L)⁻¹ by ring, hκrel,
      mul_inv_cancel₀ hκL]
  have hsqp : Squarefree (C cF * GPoly.toPoly (T.MP m hTm) A) :=
    (Associated.squarefree_iff (associated_unit_mul_left _ (C cF)
      (isUnit_C.mpr (Ne.isUnit hc0)))).mpr hsq
  have hcopp : Nat.Coprime 2 (C cF * GPoly.toPoly (T.MP m hTm) A).natDegree := by
    rw [natDegree_C_mul hc0, hdeg1]; exact hcop
  obtain ⟨hd, hf0, hsqK, hcop2⟩ := fK_facts (T.psiF m hTm) fK (CPoly.trim_trim _) _ hpf.symm hp0
    hsqp hcopp
  have hdpos : 0 < fK.length - 1 := by
    rw [← hd, ← natDegree_map_eq_of_injective (T.psiF m hTm).injective, hpf, natDegree_C_mul hc0,
      hdeg1]
    exact hdegpos
  have hne : toPoly fK ≠ 0 := fun h0 ↦ by rw [h0, eval_zero] at hf0; exact zero_ne_one hf0
  refine ⟨hdpos, ?_, hsqK, hcop2, hf0⟩
  rw [← coeff_toPoly, ← hd]
  exact leadingCoeff_ne_zero.mpr hne

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`keDecideL` answers** for every large bound, at suitable residues. -/
theorem keDecideL_decides [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false)
    (B : GPoly (LC m)) (k l : ℕ) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (keDecideL Fc ks lv m A B k l (primesBelow Bd) Bd rs).isSome := by
  unfold keDecideL keDecideC
  dsimp only
  rcases hfind : (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) with _ | ⟨q, z⟩
  · exact ⟨fun _ ↦ 0, 0, fun _ _ ↦ by rw [hfind]; rfl⟩
  obtain ⟨hd, hlc, hsqK, hcop2, hf0⟩ := T.ke_fK_facts hmon hdeg m hn hc A hsqc hdegpos hcop ha0 q z
    hfind
  set fK : CPoly (KF Fc m) := CPoly.trim ((A.map ((MO Fc ks m).mul ((MO Fc ks m).mul
      ((MO Fc ks m).mul z z) (mcst Fc ks m ((ratValC Fc ks m ((MO Fc ks m).mul
        ((MO Fc ks m).mul z z) (A.getD 0 (MO Fc ks m).zero))).getD 0)⁻¹)))).map (trC Fc m))
    with hfK
  have hv : ∀ q : Fin 1, (![(1 : KF Fc m)] q) ≠ 0 ∧
      (![(1 : KF Fc m)] q) ^ 2 = (toPoly fK).eval (![(0 : KF Fc m)] q) := fun q ↦ by
    fin_cases q; simp [hf0]
  have hinj : Function.Injective fun q : Fin 1 ↦ (![(0 : KF Fc m)] q, ![(1 : KF Fc m)] q) :=
    fun a b _ ↦ Subsingleton.elim a b
  set lq := Sup.gammaL ![(0 : KF Fc m)] ![1] ![1] 1 with hl
  have hlen : lq.length = 1 := by simp [hl, Sup.gammaL]
  have hget : ∀ q : Fin lq.length, lq.get q = (0, 1, 1) := by
    intro q; simp [hl, Sup.gammaL]
  obtain ⟨rs, B0, hB0⟩ := kf_torsLocal_exists Fc m hd hlc hsqK hcop2 lq
    (fun q ↦ by rw [hget q]; simp [CPoly.Kron.evalC_eq, hf0])
    (fun a b _ ↦ Fin.ext (by have := a.isLt; have := b.isLt; omega))
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  rw [hfind]
  dsimp only
  have hsome := hB0 Bd hBd
  have hspec := torsOracleC_spec (redAtKF Fc m rs) (localCert fK 2)
    (fun p _ R h ↦ redAtKF_valid Fc m rs p R h) (primesBelow Bd) Bd hsqK hcop2
  rcases htors : torsOracleC (redAtKF Fc m rs) (localCert fK 2) (primesBelow Bd) Bd fK 2 lq
    with _ | _ | N
  · rw [htors] at hsome; exact absurd hsome (by simp)
  · simp only [Option.isSome_some]
  · have hP := ((hspec 1 ![(0 : KF Fc m)] ![1] ![1] hv hinj).1 N htors).2
    have hw := witW_ne_none fK 2 two_pos (fK.length - 1) ![(0 : KF Fc m)] ![1] ![1] N
      (fun q ↦ by fin_cases q; simp [hf0]) hP
    rcases hwit : witW fK 2 (fK.length - 1) ![(0 : KF Fc m)] ![1] ![1] N with _ | Wb
    · exact absurd hwit hw
    · dsimp only
      rw [← hfK, hwit]; rfl

open Classical in
/-- **Square roots over an exponential level are decided**: at suitable residues, for every large
bound `keDecideL` answers, and its answer is correct. -/
theorem ke_decided [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (k l : ℕ) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd → ∃ b, keDecideL Fc ks lv m A B k l (primesBelow Bd) Bd rs = some b ∧
      (HasElementaryIntegral (T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ) ↔ b = true) := by
  obtain ⟨rs, B0, h⟩ := T.keDecideL_decides hmon hdeg m hn hc A hsqc hdegpos hcop ha0 B k l
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h Bd hBd)
  exact ⟨b, hb, T.keDecideC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop ha0 θ hθ hgen B k l _ _
    rs _ b hb⟩

end MTower

end Curves.MT
