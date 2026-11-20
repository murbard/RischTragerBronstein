import RischTragerBronstein.Mixed.KXMWDecideQ
import RischTragerBronstein.Mixed.KXCertBridgeT
import RischTragerBronstein.Mixed.KXCertBridgeC

/-!
# The Mordell–Weil certificate search on the twist

`kxDecideMWT0`: `kxDecide`, then the rational search, then the search on the twist by the class
value `s = ∏_T gᵢ` of each class (`kxChkT`, certificate over `ℚ`, any number of generators, when
`κ = s c²`), then the search over `ℚ(√d)`. Correct by `kxDecideMWT0_correct`.
-/

open Polynomial Differential IntermediateField NFEmbed

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Search

variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (kmax : ℕ)

/-- **The search on the twists.** -/
def kxMWSearchT : Bool :=
  match kxZ Fc ks lv 0 A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks 0 A z
    let uF := mwU Fc ks c0f A
    (List.range (kxCls Fc ks 0 g A B kt l cs).length).any fun kc ↦
      let s := sT Fc ks g A B kt l cs kc
      let c := Rat.sqrt (κ / s)
      let Ac := polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A uF))
      let Bc := polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A uF))
      (List.range kmax).any fun kk ↦ kxChkT Fc ks c0f g A B kt l cs z c uF Ac Bc (kk + 1) kc

/-- The side conditions and the twisted search. -/
def kxMWOKT : Bool :=
  Fc == [c0f, [1]] && degG (MO Fc ks 0) A == 3 && kxOK Fc ks 0 A B kt l cs &&
  kxConst Fc ks 0 g A B kt l cs && kxRepOK Fc ks 0 g A B kt l cs &&
  kxMWSearchT Fc ks lv c0f g A B kt l cs kmax

/-- **The search by conjugation** (classes of `D` and `P₊` different: `s κ` not a square). -/
def kxMWSearchC : Bool :=
  match kxZ Fc ks lv 0 A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks 0 A z
    let uF := mwU Fc ks c0f A
    (List.range (kxCls Fc ks 0 g A B kt l cs).length).any fun kc ↦
      let s := sT Fc ks g A B kt l cs kc
      !(Rat.sqrt (s * κ) * Rat.sqrt (s * κ) == s * κ) &&
      (let Ac := polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A uF))
       let Bc := polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A uF))
       (List.range kmax).any fun kk ↦ kxChkC Fc ks c0f g A B kt l cs z κ uF Ac Bc (kk + 1) kc)

/-- The side conditions and the conjugation search. -/
def kxMWOKC : Bool :=
  Fc == [c0f, [1]] && degG (MO Fc ks 0) A == 3 && kxOK Fc ks 0 A B kt l cs &&
  kxConst Fc ks 0 g A B kt l cs && kxRepOK Fc ks 0 g A B kt l cs &&
  kxMWSearchC Fc ks lv c0f g A B kt l cs kmax

end Search

/-- **`kxDecide` at level `0` with the rational, twisted and quadratic certificate searches.** -/
def kxDecideMWT0 (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (kmax : ℕ) : Option Bool :=
  match kxDecideMW0 Fc ks lv g A B kt l cs ps bound rs kmax with
  | some b => some b
  | none =>
    if kxMWOKT Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false
    else if kxMWOKQ Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false else none

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The twisted branch proves non-elementarity.** -/
theorem not_elementary_of_MWOKT (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (kmax : ℕ)
    (hok : kxMWOKT Fc ks lv (Fc.headD []) g A B kt l cs kmax = true) :
    ¬ HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) := by
  simp only [kxMWOKT, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hok
  unfold kxMWSearchT at hq
  split at hq
  · exact absurd hq (by decide)
  rename_i z hz
  simp only [List.any_eq_true, List.mem_range] at hq
  obtain ⟨kc, hkc, kk, -, hchk⟩ := hq
  exact T.kx_not_elementary_mwC hmon hdeg 0 hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen B kt l cs
    hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkT (Fc.headD []) g A B kt l cs z _ _ _ _ (kk + 1) hFc hTm ⟨kc, hkc⟩
        hchk rtsF hrl hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

set_option maxHeartbeats 2000000 in
/-- **`kxDecideMWT0` is correct**: whenever it answers `some b`, the integral is elementary exactly
when `b = true`. -/
theorem kxDecideMWT0_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (kmax : ℕ) (b : Bool) (hdec : kxDecideMWT0 Fc ks lv g A B kt l cs ps bound rs kmax = some b) :
    HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) ↔ b = true := by
  unfold kxDecideMWT0 at hdec
  cases hkx : kxDecideMW0 Fc ks lv g A B kt l cs ps bound rs kmax with
  | some b' =>
    rw [hkx] at hdec
    cases hdec
    exact T.kxDecideMW0_correct hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound
      rs kmax _ hkx
  | none =>
    rw [hkx] at hdec
    simp only at hdec
    split_ifs at hdec with hT hQ
    · cases hdec
      exact iff_of_false (T.not_elementary_of_MWOKT hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ
        hgen B kt l cs kmax hT) (by decide)
    · cases hdec
      exact iff_of_false (T.not_elementary_of_MWOKQ hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ
        hgen B kt l cs kmax hQ) (by decide)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The conjugation branch proves non-elementarity.** -/
theorem not_elementary_of_MWOKC (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (kmax : ℕ)
    (hok : kxMWOKC Fc ks lv (Fc.headD []) g A B kt l cs kmax = true) :
    ¬ HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) := by
  simp only [kxMWOKC, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hok
  unfold kxMWSearchC at hq
  split at hq
  · exact absurd hq (by decide)
  rename_i z hz
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at hq
  obtain ⟨kc, hkc, hδ, kk, -, hchk⟩ := hq
  have : Fact (¬ IsSquare (sT Fc ks g A B kt l cs kc * kxKap Fc ks 0 A z)) :=
    ⟨not_isSquare_of_sqrt hδ⟩
  exact T.kx_not_elementary_mwC hmon hdeg 0 hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen B kt l cs
    hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkC (Fc.headD []) g A B kt l cs z (kxKap Fc ks 0 A z) _ _ _ (kk + 1) hFc
        hTm ⟨kc, hkc⟩ hchk rtsF hrl hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

end MTower

/-- **`kxDecide` at level `0` with all certificate searches** (rational, twist, conjugation,
`ℚ(√d)`). -/
def kxDecideMWC0 (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (kmax : ℕ) : Option Bool :=
  match kxDecideMW0 Fc ks lv g A B kt l cs ps bound rs kmax with
  | some b => some b
  | none =>
    if kxMWOKT Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false
    else if kxMWOKC Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false
    else if kxMWOKQ Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false else none

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 2000000 in
/-- **`kxDecideMWC0` is correct.** -/
theorem kxDecideMWC0_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (kmax : ℕ) (b : Bool) (hdec : kxDecideMWC0 Fc ks lv g A B kt l cs ps bound rs kmax = some b) :
    HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) ↔ b = true := by
  unfold kxDecideMWC0 at hdec
  cases hkx : kxDecideMW0 Fc ks lv g A B kt l cs ps bound rs kmax with
  | some b' =>
    rw [hkx] at hdec
    cases hdec
    exact T.kxDecideMW0_correct hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound
      rs kmax _ hkx
  | none =>
    rw [hkx] at hdec
    simp only at hdec
    split_ifs at hdec with hT hC hQ
    · cases hdec
      exact iff_of_false (T.not_elementary_of_MWOKT hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ
        hgen B kt l cs kmax hT) (by decide)
    · cases hdec
      exact iff_of_false (T.not_elementary_of_MWOKC hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ
        hgen B kt l cs kmax hC) (by decide)
    · cases hdec
      exact iff_of_false (T.not_elementary_of_MWOKQ hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ
        hgen B kt l cs kmax hQ) (by decide)

end MTower

end Curves.MT
