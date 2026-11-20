import RischTragerBronstein.Mixed.KX0NonConstSide3
import RischTragerBronstein.Mixed.IndepQ

/-!
# Level `0` with the recursive certificate (curves over `ℚ(x)`)

At level `0` (linear base) the short model of a class lives over `ℚ[X]`. The checks `kxChkT0R` /
`kxChkC0R` run the step `stepI` / `stepI1` with the recursion `recQ` / `recQ1` over `ℚ` (Manin,
heights `certQ`, and the descent of curves constant up to scaling to `E(ℚ)` with Néron–Tate heights).
`kxDecideNC0` = `kxDecideDK0` followed by the two recursive searches; correct by
`kxDecideNC0_correct`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

section Chk

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) [Fact (Irreducible (toPoly (fKc Fc)))]
variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
  (z : LC 0) (c κ : ℚ) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (kc kmax : ℕ)

/-- **The level-`0` two-point check with the recursive certificate.** -/
def kxChkT0R : Bool :=
  kxChkT0 Fc ks c0f g A B kt l cs z c uF Ac Bc kc &&
  stepI (fun _ ↦ true) recQ kmax Ac Bc (ptDT Fc ks c0f g A B kt l cs uF Ac kc)
    (ptZT Fc ks c0f g A B kt l cs z c uF kc)

/-- **The level-`0` conjugation check with the recursive one-point certificate.** -/
def kxChkC0R : Bool :=
  kxChkC0 Fc ks c0f g A B kt l cs z κ uF Ac Bc kc &&
  stepI1 recQ1 kmax Ac Bc (ptDT Fc ks c0f g A B kt l cs uF Ac kc)

end Chk

lemma disc_of_discC {Ac Bc : CPoly ℚ} (h : (!CPoly.isZero (discC Ac Bc)) = true) :
    4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 ≠ 0 := by
  intro h0
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff] at h
  apply h
  simp only [discC, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul]
  rw [← h0]; simp only [map_ofNat, Polynomial.C_ofNat]; ring

lemma disc_of_chkT0 {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} [Fact (Irreducible (toPoly (fKc Fc)))]
    {c0f : CPoly ℚ} {g : LC 0} {A B : GPoly (LC 0)} {kt l : ℕ} {cs : List (LC 0)} {z : LC 0} {c : ℚ}
    {uF : Fr ℚ} {Ac Bc : CPoly ℚ} {kc : ℕ}
    (hchk : kxChkT0 Fc ks c0f g A B kt l cs z c uF Ac Bc kc = true) :
    4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 ≠ 0 := by
  simp only [kxChkT0, Bool.and_eq_true] at hchk
  exact disc_of_discC hchk.1.1.1.1.2

lemma disc_of_chkC0 {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} [Fact (Irreducible (toPoly (fKc Fc)))]
    {c0f : CPoly ℚ} {g : LC 0} {A B : GPoly (LC 0)} {kt l : ℕ} {cs : List (LC 0)} {z : LC 0} {κ : ℚ}
    {uF : Fr ℚ} {Ac Bc : CPoly ℚ} {kc : ℕ}
    (hchk : kxChkC0 Fc ks c0f g A B kt l cs z κ uF Ac Bc kc = true) :
    4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 ≠ 0 := by
  simp only [kxChkC0, Bool.and_eq_true] at hchk
  exact disc_of_discC hchk.1.1.1.1.2

namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
  (z : LC 0) (c κ : ℚ) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (kmax : ℕ)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The group condition from the recursive level-`0` check.** -/
theorem grp_of_chkT0R (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    (hchk : kxChkT0R Fc ks c0f g A B kt l cs z c uF Ac Bc k kmax = true)
    (rtsF : List (T.F 0)) (hrl : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : T.F 0))
    (b₀ : T.F 0) (hb₀ : b₀ ^ 2 = (T.MP 0 h0).sem (A.getD 0 (MO Fc ks 0).zero)) :
    let cC : ℕ → T.F 0 := (fun i ↦ (GPoly.toPoly (T.MP 0 h0) A).coeff i)
    let xC : Fin cs.length → T.F 0 := (fun q ↦ (T.MP 0 h0).sem (kqC Fc ks 0 cs q))
    let βC : Fin cs.length → T.F 0 := (fun q ↦
      ((kxRep Fc ks 0 g A B kt l cs q).2 : T.F 0) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks 0 g A B kt l cs q).1 *
        ((T.MP 0 h0).sem (kxD Fc ks 0 g cs q) * (T.MP 0 h0).sem (kxR Fc ks 0 A kt l cs q) /
          (GPoly.toPoly (T.MP 0 h0) B).eval ((T.MP 0 h0).sem (kqC Fc ks 0 cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
          (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
  simp only [kxChkT0R, Bool.and_eq_true] at hchk
  obtain ⟨hchk0, hcert⟩ := hchk
  exact T.grp_of_chkT0 c0f g A B kt l cs z c uF Ac Bc hFc h0 k hchk0
    (fun PD PZ hRD hRZ ↦ stepI_sound (fun _ ↦ rfl) recQ_sound kmax Ac Bc _ _ (disc_of_chkT0 hchk0)
      PD PZ hRD hRZ hcert) rtsF hrl hrs b₀ hb₀

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The group condition from the recursive level-`0` conjugation check.** -/
theorem grp_of_chkC0R (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    [Fact (¬ IsSquare (sT Fc ks g A B kt l cs k * κ))]
    (hchk : kxChkC0R Fc ks c0f g A B kt l cs z κ uF Ac Bc k kmax = true)
    (rtsF : List (T.F 0)) (hrl : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : T.F 0))
    (b₀ : T.F 0) (hb₀ : b₀ ^ 2 = (T.MP 0 h0).sem (A.getD 0 (MO Fc ks 0).zero)) :
    let cC : ℕ → T.F 0 := (fun i ↦ (GPoly.toPoly (T.MP 0 h0) A).coeff i)
    let xC : Fin cs.length → T.F 0 := (fun q ↦ (T.MP 0 h0).sem (kqC Fc ks 0 cs q))
    let βC : Fin cs.length → T.F 0 := (fun q ↦
      ((kxRep Fc ks 0 g A B kt l cs q).2 : T.F 0) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks 0 g A B kt l cs q).1 *
        ((T.MP 0 h0).sem (kxD Fc ks 0 g cs q) * (T.MP 0 h0).sem (kxR Fc ks 0 A kt l cs q) /
          (GPoly.toPoly (T.MP 0 h0) B).eval ((T.MP 0 h0).sem (kqC Fc ks 0 cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
          (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
  simp only [kxChkC0R, Bool.and_eq_true] at hchk
  obtain ⟨hchk0, hcert⟩ := hchk
  exact T.grp_of_chkC0 c0f g A B kt l cs z κ uF Ac Bc hFc h0 k hchk0
    (fun PD hRD n hn ↦ stepI1_sound recQ1_sound kmax Ac Bc _ (disc_of_chkC0 hchk0) PD hRD hcert n hn)
    rtsF hrl hrs b₀ hb₀

end MTower

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Search

variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (kmax : ℕ)

/-- **The recursive level-`0` search** (normalized `z`, scaling `mwU`). -/
def kxMWSearchT0R : Bool :=
  match kxZ Fc ks lv 0 A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks 0 A z
    let uF := mwU Fc ks c0f A
    (List.range (kxCls Fc ks 0 g A B kt l cs).length).any fun kc ↦
      let s := sT Fc ks g A B kt l cs kc
      kxChkT0R Fc ks c0f g A B kt l cs (normC Fc 0 z) (Rat.sqrt (κ / s)) uF
        (polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A uF))) (polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A uF)))
        kc kmax

/-- **The recursive level-`0` conjugation search.** -/
def kxMWSearchC0R : Bool :=
  match kxZ Fc ks lv 0 A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks 0 A z
    let uF := mwU Fc ks c0f A
    (List.range (kxCls Fc ks 0 g A B kt l cs).length).any fun kc ↦
      let s := sT Fc ks g A B kt l cs kc
      !(Rat.sqrt (s * κ) * Rat.sqrt (s * κ) == s * κ) &&
      kxChkC0R Fc ks c0f g A B kt l cs (normC Fc 0 z) κ uF
        (polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A uF))) (polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A uF)))
        kc kmax

/-- Side conditions and the recursive search. -/
def kxMWOKT0R : Bool :=
  Fc == [c0f, [1]] && degG (MO Fc ks 0) A == 3 && kxOK Fc ks 0 A B kt l cs &&
  kxConst Fc ks 0 g A B kt l cs && kxRepOK Fc ks 0 g A B kt l cs &&
  kxMWSearchT0R Fc ks lv c0f g A B kt l cs kmax

/-- Side conditions and the recursive conjugation search. -/
def kxMWOKC0R : Bool :=
  Fc == [c0f, [1]] && degG (MO Fc ks 0) A == 3 && kxOK Fc ks 0 A B kt l cs &&
  kxConst Fc ks 0 g A B kt l cs && kxRepOK Fc ks 0 g A B kt l cs &&
  kxMWSearchC0R Fc ks lv c0f g A B kt l cs kmax

end Search

/-- **The level-`0` decider with the recursive certificates** (curves over `ℚ(x)`, any `j`). -/
def kxDecideNC0 (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) : Option Bool :=
  match kxDecideDK0 Fc ks lv g A B kt l cs ps bound rs nmax kmax with
  | some b => some b
  | none =>
    if kxMWOKT0R Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false
    else if kxMWOKC0R Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false else none

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`kxDecideNC0` is correct.** -/
theorem kxDecideNC0_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (nmax kmax : ℕ) (b : Bool)
    (hdec : kxDecideNC0 Fc ks lv g A B kt l cs ps bound rs nmax kmax = some b) :
    HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) ↔ b = true := by
  unfold kxDecideNC0 at hdec
  cases hD : kxDecideDK0 Fc ks lv g A B kt l cs ps bound rs nmax kmax with
  | some b' =>
    rw [hD] at hdec
    cases hdec
    exact T.kxDecideDK0_correct hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound
      rs nmax kmax _ hD
  | none =>
    rw [hD] at hdec
    simp only at hdec
    split_ifs at hdec with hM hH
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKT0R, Bool.and_eq_true, beq_iff_eq] at hM
      obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hM
      unfold kxMWSearchT0R at hq
      split at hq
      · exact absurd hq (by decide)
      rename_i z hz
      simp only [List.any_eq_true, List.mem_range] at hq
      obtain ⟨kc, hkc, hchk⟩ := hq
      exact T.kx_not_elementary_mwC hmon hdeg 0 hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen B kt l
        cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkT0R (Fc.headD []) g A B kt l cs _ _ _ _ _ kmax hFc hTm ⟨kc, hkc⟩
            hchk rtsF hrl hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKC0R, Bool.and_eq_true, beq_iff_eq] at hH
      obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hH
      unfold kxMWSearchC0R at hq
      split at hq
      · exact absurd hq (by decide)
      rename_i z hz
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne] at hq
      obtain ⟨kc, hkc, hδ, hchk⟩ := hq
      have : Fact (¬ IsSquare (sT Fc ks g A B kt l cs kc * kxKap Fc ks 0 A z)) :=
        ⟨not_isSquare_of_sqrt hδ⟩
      exact T.kx_not_elementary_mwC hmon hdeg 0 hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen B kt l
        cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkC0R (Fc.headD []) g A B kt l cs _ _ _ _ _ kmax hFc hTm ⟨kc, hkc⟩
            hchk rtsF hrl hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)

/-- Once a search succeeds, `kxDecideNC0` answers. -/
lemma kxDecideNC0_isSome_of (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ)
    (h : (kxDecideDK0 Fc ks lv g A B kt l cs ps bound rs nmax kmax).isSome ∨
      kxMWOKT0R Fc ks lv (Fc.headD []) g A B kt l cs kmax = true ∨
      kxMWOKC0R Fc ks lv (Fc.headD []) g A B kt l cs kmax = true) :
    (kxDecideNC0 Fc ks lv g A B kt l cs ps bound rs nmax kmax).isSome := by
  unfold kxDecideNC0
  rcases hN : kxDecideDK0 Fc ks lv g A B kt l cs ps bound rs nmax kmax with _ | b
  · dsimp only
    rcases h with h | h | h
    · rw [hN] at h; exact absurd h (by decide)
    · rw [if_pos h]; rfl
    · split_ifs <;> rfl
  · rfl

end MTower

end Curves.MT
