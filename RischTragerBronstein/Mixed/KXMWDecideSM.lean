import RischTragerBronstein.Mixed.KXMWDecideS
import RischTragerBronstein.Mixed.KXManin
import RischTragerBronstein.Mixed.KFRatGuess

/-!
# `kxDecide` at levels `m + 1` with the Manin-map certificate

`kxChkTSM` is `kxChkTS` with the height certificate replaced by the Manin certificate
(`manCertP` over `Kₘ(t)`, `Kₘ` the code field `KF Fc m`); `grp_of_chkTSM` its group condition
(through `grp_of_chkT0S` and `indep_of_manCertP`). `kxDecideMWSM` tries it first, then
`kxDecideMWS`; `kxDecideMWSM_correct`.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

section ChkM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (c : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m)) (kc : ℕ)

/-- **The Manin check on the twist at level `m + 1`.** -/
def kxChkTSM : Bool :=
  kxChkT0S Fc ks m g A B kt l cs z c uF Ac Bc kc &&
  (Differential.SuperData.manCertP Ac Bc (ptDTS Fc ks m g A B kt l cs uF Ac kc)
    (ptZTS Fc ks m g A B kt l cs z c uF kc) ||
   Differential.SuperData.manCertRP Ac Bc (fun x ↦ (ratOfK Fc m x).isSome)
    (ptDTS Fc ks m g A B kt l cs uF Ac kc) (ptZTS Fc ks m g A B kt l cs z c uF kc))

end ChkM

namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L) (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (c : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m))

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The group condition at level `m + 1` from the Manin check.** -/
theorem grp_of_chkTSM (h0 : T.Tr (m + 1)) (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    (hchk : kxChkTSM Fc ks m g A B kt l cs z c uF Ac Bc k = true)
    (rtsF : List (T.F (m + 1))) (hrl : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : T.F (m + 1)))
    (b₀ : T.F (m + 1)) (hb₀ : b₀ ^ 2 = (T.MP (m + 1) h0).sem (A.getD 0 (MO Fc ks (m + 1)).zero)) :
    let cC : ℕ → T.F (m + 1) := (fun i ↦ (GPoly.toPoly (T.MP (m + 1) h0) A).coeff i)
    let xC : Fin cs.length → T.F (m + 1) := (fun q ↦ (T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))
    let βC : Fin cs.length → T.F (m + 1) := (fun q ↦
      ((kxRep Fc ks (m + 1) g A B kt l cs q).2 : T.F (m + 1)) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks (m + 1) g A B kt l cs q).1 *
        ((T.MP (m + 1) h0).sem (kxD Fc ks (m + 1) g cs q) *
          (T.MP (m + 1) h0).sem (kxR Fc ks (m + 1) A kt l cs q) /
          (GPoly.toPoly (T.MP (m + 1) h0) B).eval ((T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK
          (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
          (kxCl (m + 1) g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
  simp only [kxChkTSM, Bool.and_eq_true, Bool.or_eq_true] at hchk
  obtain ⟨hchk0, hcert⟩ := hchk
  exact T.grp_of_chkT0S m g A B kt l cs z c uF Ac Bc h0 k hchk0
    (fun PD PZ hRD hRZ ↦ hcert.elim
      (fun h ↦ Differential.SuperData.indep_of_manCertP Ac Bc _ _ PD PZ hRD hRZ h)
      (fun h ↦ Differential.SuperData.indep_of_manCertRP Ac Bc
        (fun q ↦ by simp [ratOfK_ratCast]) _ _ PD PZ hRD hRZ h))
    rtsF hrl hrs b₀ hb₀

end MTower

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Search

variable (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))

/-- **The Manin search at level `m + 1`** (data as in `kxMWSearchS`). -/
def kxMWSearchSM : Bool :=
  match kxZ Fc ks lv (m + 1) A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks (m + 1) A z
    let uF := mwUS Fc ks m A
    (List.range (kxCls Fc ks (m + 1) g A B kt l cs).length).any fun kc ↦
      let s := sTS Fc ks m g A B kt l cs kc
      let c := Rat.sqrt (κ / s)
      let Ac := polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2)) (AFrS Fc ks m A uF))
      let Bc := polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3)) (BFrS Fc ks m A uF))
      kxChkTSM Fc ks m g A B kt l cs z c uF Ac Bc kc

/-- The side conditions and the Manin search. -/
def kxMWOKSM : Bool :=
  degG (MO Fc ks (m + 1)) A == 3 && kxOK Fc ks (m + 1) A B kt l cs &&
  kxConst Fc ks (m + 1) g A B kt l cs && kxRepOK Fc ks (m + 1) g A B kt l cs &&
  kxMWSearchSM Fc ks lv m g A B kt l cs

end Search

/-- **`kxDecide` at level `m + 1` with the Manin, then the height, certificate searches.** -/
def kxDecideMWSM (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (kmax : ℕ) : Option Bool :=
  match kxDecide Fc ks lv (m + 1) g A B kt l cs ps bound rs with
  | some b => some b
  | none =>
    if kxMWOKSM Fc ks lv m g A B kt l cs then some false
    else kxDecideMWS Fc ks lv m g A B kt l cs ps bound rs kmax

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Non-elementarity from the Manin search at level `m + 1`.** -/
theorem not_elementary_of_MWOKSM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (m : ℕ) (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
    (hok : kxMWOKSM Fc ks lv m g A B kt l cs = true) :
    ¬ HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) := by
  simp only [kxMWOKSM, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨hdeg3, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hok
  unfold kxMWSearchSM at hq
  split at hq
  · exact absurd hq (by decide)
  rename_i z hz
  simp only [List.any_eq_true, List.mem_range] at hq
  obtain ⟨kc, hkc, hchk⟩ := hq
  exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
    B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkTSM m g A B kt l cs z _ _ _ _ hTm ⟨kc, hkc⟩ hchk rtsF hrl
        hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`kxDecideMWSM` is correct**: whenever it answers `some b`, the integral is elementary exactly
when `b = true`. -/
theorem kxDecideMWSM_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (kmax : ℕ) (b : Bool)
    (hdec : kxDecideMWSM Fc ks lv m g A B kt l cs ps bound rs kmax = some b) :
    HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) ↔
      b = true := by
  unfold kxDecideMWSM at hdec
  cases hkx : kxDecide Fc ks lv (m + 1) g A B kt l cs ps bound rs with
  | some b' =>
    rw [hkx] at hdec
    cases hdec
    exact T.kxDecide_correct hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps
      bound rs _ hkx
  | none =>
    rw [hkx] at hdec
    simp only at hdec
    split_ifs at hdec with hok
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKSM, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨hdeg3, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hok
      unfold kxMWSearchSM at hq
      split at hq
      · exact absurd hq (by decide)
      rename_i z hz
      simp only [List.any_eq_true, List.mem_range] at hq
      obtain ⟨kc, hkc, hchk⟩ := hq
      exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
        B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkTSM m g A B kt l cs z _ _ _ _ hTm ⟨kc, hkc⟩ hchk rtsF hrl
            hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)
    · exact T.kxDecideMWS_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps
        bound rs kmax b hdec

end MTower

end Curves.MT

