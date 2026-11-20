import RischTragerBronstein.Mixed.KXNonConstDecide3
import RischTragerBronstein.Mixed.IndepTower

/-!
# Non-constant curves at levels `m + 1` with the recursive certificate

The checks `kxChkTSR` / `kxChkCSR` run the recursive step `stepI` / `stepI1` (Manin, heights, and the
descent for curves constant up to scaling, recursing over `Kₘ` with a check `rec` / `rec1`) on the
short model of a class. `kxDecideNCS3` = `kxDecideNCS2` followed by the two recursive searches; it is
correct (`kxDecideNCS3_correct`) for any sound recursive checks (`RecS`, `RecS1`).
-/

open Polynomial Differential IntermediateField Classical

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

section Chk

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (c κ : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m)) (kc : ℕ)
  (rec : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Option (KF Fc m × KF Fc m) → Bool)
  (rec1 : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Bool) (kmax : ℕ)

/-- **The two-point check with the recursive certificate.** -/
def kxChkTSR : Bool :=
  kxChkT0S Fc ks m g A B kt l cs z c uF Ac Bc kc &&
  stepI (fun x ↦ (ratOfK Fc m x).isSome) rec kmax Ac Bc (ptDTS Fc ks m g A B kt l cs uF Ac kc)
    (ptZTS Fc ks m g A B kt l cs z c uF kc)

/-- **The conjugation check with the recursive one-point certificate.** -/
def kxChkCSR : Bool :=
  kxChkC0S Fc ks m g A B kt l cs z κ uF Ac Bc kc &&
  stepI1 rec1 kmax Ac Bc (ptDTS Fc ks m g A B kt l cs uF Ac kc)

end Chk

lemma disc_of_chkT0S {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} [Fact (Irreducible (toPoly (fKc Fc)))]
    {m : ℕ} {g : LC (m + 1)} {A B : GPoly (LC (m + 1))} {kt l : ℕ} {cs : List (LC (m + 1))}
    {z : LC (m + 1)} {c : ℚ} {uF : Fr (KF Fc m)} {Ac Bc : CPoly (KF Fc m)} {kc : ℕ}
    (hchk : kxChkT0S Fc ks m g A B kt l cs z c uF Ac Bc kc = true) :
    4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 ≠ 0 := by
  have hc := hchk
  simp only [kxChkT0S, Bool.and_eq_true, Bool.not_eq_true'] at hc
  have hdisc := hc.1.1.1.1.2
  intro h0'
  rw [show 4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 =
    CPoly.toPoly (discCS Fc m Ac Bc) by
    simp only [discCS, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, map_ofNat,
      Polynomial.C_ofNat]; ring, ← CPoly.isZero_iff] at h0'
  rw [h0'] at hdisc; exact absurd hdisc (by decide)

lemma disc_of_chkC0S {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} [Fact (Irreducible (toPoly (fKc Fc)))]
    {m : ℕ} {g : LC (m + 1)} {A B : GPoly (LC (m + 1))} {kt l : ℕ} {cs : List (LC (m + 1))}
    {z : LC (m + 1)} {κ : ℚ} {uF : Fr (KF Fc m)} {Ac Bc : CPoly (KF Fc m)} {kc : ℕ}
    (hchk : kxChkC0S Fc ks m g A B kt l cs z κ uF Ac Bc kc = true) :
    4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 ≠ 0 := by
  have hc := hchk
  simp only [kxChkC0S, Bool.and_eq_true, Bool.not_eq_true'] at hc
  have hdisc := hc.1.1.1.1.2
  intro h0'
  rw [show 4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 =
    CPoly.toPoly (discCS Fc m Ac Bc) by
    simp only [discCS, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, map_ofNat,
      Polynomial.C_ofNat]; ring, ← CPoly.isZero_iff] at h0'
  rw [h0'] at hdisc; exact absurd hdisc (by decide)

namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L) (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (c κ : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m))
  {rec : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Option (KF Fc m × KF Fc m) → Bool}
  {rec1 : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Bool} (kmax : ℕ)

set_option maxHeartbeats 4000000 in
/-- **The group condition from the recursive check.** -/
theorem grp_of_chkTSR (hrec : RecS rec) (h0 : T.Tr (m + 1))
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    (hchk : kxChkTSR Fc ks m g A B kt l cs z c uF Ac Bc k rec kmax = true)
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
  simp only [kxChkTSR, Bool.and_eq_true] at hchk
  obtain ⟨hchk0, hcert⟩ := hchk
  have hΔq := disc_of_chkT0S hchk0
  exact T.grp_of_chkT0S m g A B kt l cs z c uF Ac Bc h0 k hchk0
    (fun PD PZ hRD hRZ ↦ stepI_sound (fun q ↦ by simp [ratOfK_ratCast]) hrec kmax Ac Bc _ _ hΔq
      PD PZ hRD hRZ hcert)
    rtsF hrl hrs b₀ hb₀

set_option maxHeartbeats 4000000 in
/-- **The group condition from the recursive conjugation check.** -/
theorem grp_of_chkCSR (hrec1 : RecS1 rec1) (h0 : T.Tr (m + 1))
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    [Fact (¬ IsSquare (Rat.cast (sTS Fc ks m g A B kt l cs k * κ) : KF Fc m))]
    (hchk : kxChkCSR Fc ks m g A B kt l cs z κ uF Ac Bc k rec1 kmax = true)
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
  simp only [kxChkCSR, Bool.and_eq_true] at hchk
  obtain ⟨hchk0, hcert⟩ := hchk
  have hΔq := disc_of_chkC0S hchk0
  exact T.grp_of_chkC0S m g A B kt l cs z κ uF Ac Bc h0 k hchk0
    (fun PD hRD n hn ↦ stepI1_sound hrec1 kmax Ac Bc _ hΔq PD hRD hcert n hn) rtsF hrl hrs b₀ hb₀

end MTower

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Search

variable (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (rec : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Option (KF Fc m × KF Fc m) → Bool)
  (rec1 : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Bool) (kmax : ℕ)

/-- **The recursive search** (normalized `z`). -/
def kxMWSearchSR : Bool :=
  match kxZ Fc ks lv (m + 1) A with
  | none => false
  | some z =>
    (List.range (kxCls Fc ks (m + 1) g A B kt l cs).length).any fun kc ↦
      let s := sTS Fc ks m g A B kt l cs kc
      kxChkTSR Fc ks m g A B kt l cs (normC Fc (m + 1) z)
        (Rat.sqrt (kxKap Fc ks (m + 1) A z / s)) (mwUS Fc ks m A) (ncAc Fc ks m A s) (ncBc Fc ks m A s)
        kc rec kmax

/-- **The recursive conjugation search** (normalized `z`). -/
def kxMWSearchCSR : Bool :=
  match kxZ Fc ks lv (m + 1) A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks (m + 1) A z
    (List.range (kxCls Fc ks (m + 1) g A B kt l cs).length).any fun kc ↦
      let s := sTS Fc ks m g A B kt l cs kc
      !(Rat.sqrt (s * κ) * Rat.sqrt (s * κ) == s * κ) &&
      kxChkCSR Fc ks m g A B kt l cs (normC Fc (m + 1) z) κ (mwUS Fc ks m A) (ncAc Fc ks m A s)
        (ncBc Fc ks m A s) kc rec1 kmax

/-- Side conditions and the recursive search. -/
def kxMWOKSR : Bool :=
  degG (MO Fc ks (m + 1)) A == 3 && kxOK Fc ks (m + 1) A B kt l cs &&
  kxConst Fc ks (m + 1) g A B kt l cs && kxRepOK Fc ks (m + 1) g A B kt l cs &&
  kxMWSearchSR Fc ks lv m g A B kt l cs rec kmax

/-- Side conditions and the recursive conjugation search. -/
def kxMWOKCSR : Bool :=
  sqOK Fc && degG (MO Fc ks (m + 1)) A == 3 && kxOK Fc ks (m + 1) A B kt l cs &&
  kxConst Fc ks (m + 1) g A B kt l cs && kxRepOK Fc ks (m + 1) g A B kt l cs &&
  kxMWSearchCSR Fc ks lv m g A B kt l cs rec1 kmax

end Search

/-- **The non-constant decider with the recursive certificates.** -/
def kxDecideNCS3 (m : ℕ)
    (rec : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Option (KF Fc m × KF Fc m) → Bool)
    (rec1 : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Bool)
    (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) : Option Bool :=
  match kxDecideNCS2 Fc ks lv m g A B kt l cs ps bound rs nmax kmax with
  | some b => some b
  | none =>
    if kxMWOKSR Fc ks lv m g A B kt l cs rec kmax then some false
    else if kxMWOKCSR Fc ks lv m g A B kt l cs rec1 kmax then some false else none

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **`kxDecideNCS3` is correct** (for sound recursive checks). -/
theorem kxDecideNCS3_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    {rec : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Option (KF Fc m × KF Fc m) → Bool}
    {rec1 : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Bool}
    (hrec : RecS rec) (hrec1 : RecS1 rec1)
    (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (nmax kmax : ℕ) (b : Bool)
    (hdec : kxDecideNCS3 Fc ks lv m rec rec1 g A B kt l cs ps bound rs nmax kmax = some b) :
    HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) ↔
      b = true := by
  unfold kxDecideNCS3 at hdec
  cases hD : kxDecideNCS2 Fc ks lv m g A B kt l cs ps bound rs nmax kmax with
  | some b' =>
    rw [hD] at hdec
    cases hdec
    exact T.kxDecideNCS2_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps
      bound rs nmax kmax _ hD
  | none =>
    rw [hD] at hdec
    simp only at hdec
    split_ifs at hdec with hM hH
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKSR, Bool.and_eq_true, beq_iff_eq] at hM
      obtain ⟨⟨⟨⟨hdeg3, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hM
      unfold kxMWSearchSR at hq
      split at hq
      · exact absurd hq (by decide)
      rename_i z hz
      simp only [List.any_eq_true, List.mem_range] at hq
      obtain ⟨kc, hkc, hchk⟩ := hq
      exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
        B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkTSR m g A B kt l cs _ _ _ _ _ kmax hrec hTm ⟨kc, hkc⟩ hchk rtsF hrl
            hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKCSR, Bool.and_eq_true, beq_iff_eq] at hH
      obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hH
      unfold kxMWSearchCSR at hq
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
          have h := TE.grp_of_chkCSR m g A B kt l cs _ _ _ _ _ kmax hrec1 hTm ⟨kc, hkc⟩ hchk rtsF hrl
            hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)

/-- Once a search succeeds, `kxDecideNCS3` answers. -/
lemma kxDecideNCS3_isSome_of (m : ℕ)
    (rec : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Option (KF Fc m × KF Fc m) → Bool)
    (rec1 : ℕ → KF Fc m → KF Fc m → Option (KF Fc m × KF Fc m) → Bool)
    (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ)
    (h : (kxDecideNCS2 Fc ks lv m g A B kt l cs ps bound rs nmax kmax).isSome ∨
      kxMWOKSR Fc ks lv m g A B kt l cs rec kmax = true ∨
      kxMWOKCSR Fc ks lv m g A B kt l cs rec1 kmax = true) :
    (kxDecideNCS3 Fc ks lv m rec rec1 g A B kt l cs ps bound rs nmax kmax).isSome := by
  unfold kxDecideNCS3
  rcases hN : kxDecideNCS2 Fc ks lv m g A B kt l cs ps bound rs nmax kmax with _ | b
  · dsimp only
    rcases h with h | h | h
    · rw [hN] at h; exact absurd h (by decide)
    · rw [if_pos h]; rfl
    · split_ifs <;> rfl
  · rfl

end MTower

end Curves.MT
