import RischTragerBronstein.Mixed.KXNonConstDecide
import RischTragerBronstein.Mixed.ManinOne
import RischTragerBronstein.Mixed.KXNonConstSide4

/-!
# The conjugation branch for non-constant curves at levels `m + 1`

When `κ / s` is not a rational square the two exception points lie in different classes and the
relation question reduces to the infinite order of one point on a twist (`grp_of_chkC0S`). Here:
`kxChkCSM` (structural check + one-point **Manin** certificate `manCert1P`), its soundness
`grp_of_chkCSM`, the normalized searches `kxMWSearchCSMN` (Manin) and `kxMWSearchCSN` (one-point
heights `certQ1`), and the decider `kxDecideNCS2` = `kxDecideNCS` + both conjugation searches, correct
by `kxDecideNCS2_correct`.
-/

open Polynomial Differential IntermediateField Classical

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

section ChkCSM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (κ : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m)) (kc : ℕ)

/-- **The conjugation check with the one-point Manin certificate.** -/
def kxChkCSM : Bool :=
  kxChkC0S Fc ks m g A B kt l cs z κ uF Ac Bc kc &&
  Manin.manCert1P Ac Bc (ptDTS Fc ks m g A B kt l cs uF Ac kc)

end ChkCSM

namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L) (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (κ : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m))

set_option maxHeartbeats 4000000 in
/-- **The group condition from the conjugation Manin check.** -/
theorem grp_of_chkCSM (h0 : T.Tr (m + 1)) (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    [Fact (¬ IsSquare (Rat.cast (sTS Fc ks m g A B kt l cs k * κ) : KF Fc m))]
    (hchk : kxChkCSM Fc ks m g A B kt l cs z κ uF Ac Bc k = true)
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
  simp only [kxChkCSM, Bool.and_eq_true] at hchk
  obtain ⟨hchk0, hcert⟩ := hchk
  exact T.grp_of_chkC0S m g A B kt l cs z κ uF Ac Bc h0 k hchk0
    (fun PD hRD n hn ↦ Manin.nontors_of_manCert1P Ac Bc _ PD hRD hcert n hn) rtsF hrl hrs b₀ hb₀

end MTower

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Search

variable (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (kmax : ℕ)

/-- **The conjugation Manin search** (normalized `z`). -/
def kxMWSearchCSMN : Bool :=
  match kxZ Fc ks lv (m + 1) A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks (m + 1) A z
    (List.range (kxCls Fc ks (m + 1) g A B kt l cs).length).any fun kc ↦
      let s := sTS Fc ks m g A B kt l cs kc
      !(Rat.sqrt (s * κ) * Rat.sqrt (s * κ) == s * κ) &&
      kxChkCSM Fc ks m g A B kt l cs (normC Fc (m + 1) z) κ (mwUS Fc ks m A) (ncAc Fc ks m A s)
        (ncBc Fc ks m A s) kc

/-- **The conjugation height search** (normalized `z`, one-point heights). -/
def kxMWSearchCSN : Bool :=
  match kxZ Fc ks lv (m + 1) A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks (m + 1) A z
    (List.range (kxCls Fc ks (m + 1) g A B kt l cs).length).any fun kc ↦
      let s := sTS Fc ks m g A B kt l cs kc
      !(Rat.sqrt (s * κ) * Rat.sqrt (s * κ) == s * κ) &&
      (List.range kmax).any fun kk ↦
        kxChkCS Fc ks m g A B kt l cs (normC Fc (m + 1) z) κ (mwUS Fc ks m A) (ncAc Fc ks m A s)
          (ncBc Fc ks m A s) kk kc

/-- Side conditions and the conjugation Manin search. -/
def kxMWOKCSMN : Bool :=
  sqOK Fc && degG (MO Fc ks (m + 1)) A == 3 && kxOK Fc ks (m + 1) A B kt l cs &&
  kxConst Fc ks (m + 1) g A B kt l cs && kxRepOK Fc ks (m + 1) g A B kt l cs &&
  kxMWSearchCSMN Fc ks lv m g A B kt l cs

/-- Side conditions and the conjugation height search. -/
def kxMWOKCSN : Bool :=
  sqOK Fc && degG (MO Fc ks (m + 1)) A == 3 && kxOK Fc ks (m + 1) A B kt l cs &&
  kxConst Fc ks (m + 1) g A B kt l cs && kxRepOK Fc ks (m + 1) g A B kt l cs &&
  kxMWSearchCSN Fc ks lv m g A B kt l cs kmax

end Search

/-- **The non-constant decider with both branches.** -/
def kxDecideNCS2 (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) : Option Bool :=
  match kxDecideNCS Fc ks lv m g A B kt l cs ps bound rs nmax kmax with
  | some b => some b
  | none =>
    if kxMWOKCSMN Fc ks lv m g A B kt l cs then some false
    else if kxMWOKCSN Fc ks lv m g A B kt l cs kmax then some false else none

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **`kxDecideNCS2` is correct.** -/
theorem kxDecideNCS2_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (nmax kmax : ℕ) (b : Bool)
    (hdec : kxDecideNCS2 Fc ks lv m g A B kt l cs ps bound rs nmax kmax = some b) :
    HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) ↔
      b = true := by
  unfold kxDecideNCS2 at hdec
  cases hD : kxDecideNCS Fc ks lv m g A B kt l cs ps bound rs nmax kmax with
  | some b' =>
    rw [hD] at hdec
    cases hdec
    exact T.kxDecideNCS_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps
      bound rs nmax kmax _ hD
  | none =>
    rw [hD] at hdec
    simp only at hdec
    split_ifs at hdec with hM hH
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKCSMN, Bool.and_eq_true, beq_iff_eq] at hM
      obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hM
      unfold kxMWSearchCSMN at hq
      split at hq
      · exact absurd hq (by decide)
      rename_i z hz
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne] at hq
      obtain ⟨kc, hkc, hδ, hchk⟩ := hq
      have : Fact (¬ IsSquare (Rat.cast (sTS Fc ks m g A B kt l cs kc * kxKap Fc ks (m + 1) A z) :
          KF Fc m)) :=
        ⟨not_isSquare_KF_sqOK Fc hFc _ (not_isSquare_of_sqrt hδ) m⟩
      exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
        B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkCSM m g A B kt l cs _ _ _ _ _ hTm ⟨kc, hkc⟩ hchk rtsF hrl
            hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKCSN, Bool.and_eq_true, beq_iff_eq] at hH
      obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hH
      unfold kxMWSearchCSN at hq
      split at hq
      · exact absurd hq (by decide)
      rename_i z hz
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne] at hq
      obtain ⟨kc, hkc, hδ, kk, -, hchk⟩ := hq
      have : Fact (¬ IsSquare (Rat.cast (sTS Fc ks m g A B kt l cs kc * kxKap Fc ks (m + 1) A z) :
          KF Fc m)) :=
        ⟨not_isSquare_KF_sqOK Fc hFc _ (not_isSquare_of_sqrt hδ) m⟩
      exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
        B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkCS m g A B kt l cs _ _ _ _ _ kk hTm ⟨kc, hkc⟩ hchk rtsF hrl
            hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)

/-- Once a search succeeds, `kxDecideNCS2` answers. -/
lemma kxDecideNCS2_isSome_of (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ)
    (h : (kxDecideNCS Fc ks lv m g A B kt l cs ps bound rs nmax kmax).isSome ∨
      kxMWOKCSMN Fc ks lv m g A B kt l cs = true ∨ kxMWOKCSN Fc ks lv m g A B kt l cs kmax = true) :
    (kxDecideNCS2 Fc ks lv m g A B kt l cs ps bound rs nmax kmax).isSome := by
  unfold kxDecideNCS2
  rcases hN : kxDecideNCS Fc ks lv m g A B kt l cs ps bound rs nmax kmax with _ | b
  · dsimp only
    rcases h with h | h | h
    · rw [hN] at h; exact absurd h (by decide)
    · rw [if_pos h]; rfl
    · split_ifs <;> rfl
  · rfl

end MTower

end Curves.MT
