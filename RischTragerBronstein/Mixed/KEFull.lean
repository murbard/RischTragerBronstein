import RischTragerBronstein.Mixed.KEMain
import RischTragerBronstein.Mixed.KLDecideW

/-!
# General integrands over a square root of an exponential level

`ke_full_decides`: for `θ² = A(t)` over an exponential level, an integrand `g₀ + B(t) θ / tᵏ`
(`g₀` any element of the tower field, by a code) is elementary iff `∫ g₀` is (decided by `elM`, at
every large search bound) and `keDecide` answers `true`, whenever `keDecide` answers. The `θ`-component
is split off by the Galois projection (`kl_componentsW`).
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

open Classical in
/-- **A positive answer of `keDecide` gives an integral over every elementary extension.** -/
theorem keDecideC_true_in [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) (A : GPoly (LC m)) (hdegpos : 0 < degG (MO Fc ks m) A)
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) (B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (hdec : keDecideC Fc ks lv m A B k l ps bound rs cpf = some true) :
    HasElementaryIntegralIn (T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ) := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  unfold keDecideC at hdec
  dsimp only at hdec
  rcases hfind : (prdeC Fc ks lv m (halfFr Fc ks m (A.getD 0 (MO Fc ks m).zero)) []).find?
      (fun r ↦ !(MO Fc ks m).isZero r.2) with _ | ⟨q, z⟩
  · rw [hfind] at hdec
    exact T.ke_backward_plain m hTr A B k l θ hθ hA0 hspecA (Option.some.inj hdec)
  · rw [hfind] at hdec
    dsimp only at hdec
    obtain ⟨hz0, -, hκ0⟩ := T.ke_z_facts hmon hdeg m hn hc A ha0 q z hfind
    split at hdec
    · exact absurd hdec (by simp)
    · exact T.ke_backward_plain m hTr A B k l θ hθ hA0 hspecA (Option.some.inj hdec)
    · split at hdec
      · exact absurd hdec (by simp)
      · exact T.ke_backward_param m hTr A B k l θ hθ hA0 z hz0 _ hκ0 _ _ hspecA
          (Option.some.inj hdec)

set_option maxHeartbeats 8000000 in
open Classical in
/-- **The `θ`-component splits off.** -/
theorem ke_iffC [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (f0 : LC (m + 1)) (B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (b : Bool)
    (hdec : keDecideC Fc ks lv m A B k l ps bound rs cpf = some b) :
    HasElementaryIntegral (T.ev (m + 1) f0 + T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ) ↔
      HasElementaryIntegral (T.ev (m + 1) f0) ∧ b = true := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcorr := T.keDecideC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop ha0 θ hθ hgen B k l ps
    bound rs cpf b hdec
  constructor
  · intro hf
    set cs : ℕ → LC (m + 1) := fun j ↦ if j = 0 then f0 else ((B, denC Fc ks m k l A) : LC (m + 1))
      with hcs
    have hsum : ∑ j ∈ Finset.range 2, T.ev (m + 1) (cs j) * θ ^ j =
        T.ev (m + 1) f0 + T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have e1 : cs 1 = ((B, denC Fc ks m k l A) : LC (m + 1)) := if_neg one_ne_zero
      rw [e1, T.ev_rhs m hTr]
      simp [hcs]
    have hcomp := T.kl_componentsW hmon hdeg m hn hc A 2 two_pos hsqc hdegpos θ hθ hgen cs
      (hsum ▸ hf)
    refine ⟨by simpa [hcs] using hcomp 0 two_pos, hcorr.mp ?_⟩
    have h1 := hcomp 1 (by norm_num)
    have e1 : cs 1 = ((B, denC Fc ks m k l A) : LC (m + 1)) := if_neg one_ne_zero
    rw [e1, T.ev_rhs m hTr, pow_one] at h1
    exact h1
  · rintro ⟨h0, rfl⟩
    exact h0.add_in (T.keDecideC_true_in hmon hdeg m hn hc A hdegpos ha0 θ hθ B k l ps bound rs cpf hdec)

set_option maxHeartbeats 8000000 in
open Classical in
/-- **General integrands `g₀ + B(t) θ / tᵏ` over a square root of an exponential level are
decided**, whenever `keDecide` answers: `elM` decides `g₀` at every large search bound. -/
theorem ke_full_decidesC [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (hsh : curveShape Fc = true) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (f0 : LC (m + 1)) (B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (b : Bool)
    (hdec : keDecideC Fc ks lv m A B k l ps bound rs cpf = some b) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b0, elM Fc ks lv (m + 1) f0 N = some b0 ∧
      (HasElementaryIntegral (T.ev (m + 1) f0 + T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ) ↔
        b0 = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m + 1) (by omega)
  obtain ⟨N₀, hN₀⟩ := elM_decides_any hmon hdeg hsh T' (m + 1) hT'n hc hT'gen f0
  have hθmem : θ ^ 2 ∈ T.F (m + 1) := by
    rw [hθ, ← T.sem_poly_code m hTr]
    exact SetLike.coe_mem _
  have hθi : IsIntegral (T.F (m + 1)) θ := by
    refine ⟨X ^ 2 - C ⟨θ ^ 2, hθmem⟩, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [eval₂_sub, eval₂_X_pow, eval₂_C]
  have halg : Algebra.IsAlgebraic (T.F (m + 1)) L := ⟨fun z ↦ by
    have := IntermediateField.isAlgebraic_adjoin_simple hθi
    exact (IntermediateField.isAlgebraic_iff (x := (⟨z, hgen z⟩ :
      IntermediateField.adjoin (T.F (m + 1)) {θ}))).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have h0 : HasElementaryIntegral (T.ev (m + 1) f0) ↔ HasElementaryIntegral (T'.ev (m + 1) f0) := by
    rw [← hasElementaryIntegral_isAlgebraic_iff halg]
    rw [show algebraMap (T.F (m + 1)) L (T'.ev (m + 1) f0) = T.ev (m + 1) f0 from
      hT'ev (m + 1) le_rfl f0]
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b0, hb0, hiff, -⟩ := hN₀ N hN
  refine ⟨b0, hb0, ?_⟩
  rw [T.ke_iffC hmon hdeg m hn hc hk A hsqc hdegpos hcop ha0 θ hθ hgen f0 B k l ps bound rs cpf b hdec, h0,
    hiff]

set_option maxHeartbeats 8000000 in
open Classical in
/-- **General integrands `g₀ + B(t) θ / tᵏ` over a square root of an exponential level are
decided**, whenever `keDecide` answers: `elM` decides `g₀` at every large search bound. -/
theorem ke_full_decides [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (hsh : curveShape Fc = true) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (f0 : LC (m + 1)) (B : GPoly (LC m)) (k l : ℕ) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool)
    (hdec : keDecide Fc ks lv m A B k l ps bound rs = some b) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b0, elM Fc ks lv (m + 1) f0 N = some b0 ∧
      (HasElementaryIntegral (T.ev (m + 1) f0 + T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ) ↔
        b0 = true ∧ b = true) :=
  T.ke_full_decidesC hmon hdeg hsh m hn hc hk A hsqc hdegpos hcop ha0 θ hθ hgen f0 B k l ps bound rs
    _ b hdec

end MTower

end Curves.MT
