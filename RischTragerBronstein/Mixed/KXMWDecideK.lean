import RischTragerBronstein.Mixed.KXMWDecideT
import RischTragerBronstein.Mixed.KXCertBridgeCK

/-!
# The Mordell–Weil certificate search for constant curves

`kxDecideMWK0`: `kxDecideMWC0`, then — for curves with constant coefficients, where function-field
heights vanish — the conjugation argument with a height certificate over `ℚ` (`kxChkCK`) for each
class whose square class differs from that of `P₊`. Correct by `kxDecideMWK0_correct`.
-/

open Polynomial Differential IntermediateField NFEmbed

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Search

variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (kmax : ℕ)

/-- The scaling candidates: `1, 2, 3, 6` and the common denominator `d` of the model at `m = 1`
(scaling `u` by `d` multiplies `a, b` by `d⁴, d⁶`, which makes them integers). -/
def mwScales (c0f : CPoly ℚ) (A : GPoly (LC 0)) (s : ℚ) : List ℚ :=
  let a1 := (polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A (mwU Fc ks c0f A)))).headD 0
  let b1 := (polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A (mwU Fc ks c0f A)))).headD 0
  [1, 2, 3, 6, (Nat.lcm a1.den b1.den : ℚ)]

/-- **The search for constant curves** (different classes, heights over `ℚ`). -/
def kxMWSearchCK : Bool :=
  match kxZ Fc ks lv 0 A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks 0 A z
    (List.range (kxCls Fc ks 0 g A B kt l cs).length).any fun kc ↦
      let s := sT Fc ks g A B kt l cs kc
      !(Rat.sqrt (s * κ) * Rat.sqrt (s * κ) == s * κ) &&
      (mwScales Fc ks c0f A s).any fun m ↦
        let uF := Fr.mul (mwU Fc ks c0f A) (Fr.ofPoly [m])
        let Ac : CPoly ℚ := [(polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A uF))).headD 0]
        let Bc : CPoly ℚ := [(polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A uF))).headD 0]
        (List.range kmax).any fun kk ↦
          kxChkCK Fc ks c0f g A B kt l cs (normC Fc 0 z) κ uF Ac Bc kk kc (Ac.headD 0).num (Bc.headD 0).num

/-- The side conditions and the constant-curve search. -/
def kxMWOKCK : Bool :=
  Fc == [c0f, [1]] && degG (MO Fc ks 0) A == 3 && kxOK Fc ks 0 A B kt l cs &&
  kxConst Fc ks 0 g A B kt l cs && kxRepOK Fc ks 0 g A B kt l cs &&
  kxMWSearchCK Fc ks lv c0f g A B kt l cs kmax

/-- **The search for constant curves, same class** (two-point heights over `ℚ` on the twist). -/
def kxMWSearchTK : Bool :=
  match kxZ Fc ks lv 0 A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks 0 A z
    (List.range (kxCls Fc ks 0 g A B kt l cs).length).any fun kc ↦
      let s := sT Fc ks g A B kt l cs kc
      let c := Rat.sqrt (κ / s)
      (mwScales Fc ks c0f A s).any fun m ↦
        let uF := Fr.mul (mwU Fc ks c0f A) (Fr.ofPoly [m])
        let Ac : CPoly ℚ := [(polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A uF))).headD 0]
        let Bc : CPoly ℚ := [(polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A uF))).headD 0]
        (List.range kmax).any fun kk ↦
          kxChkTK Fc ks c0f g A B kt l cs (normC Fc 0 z) uF Ac Bc kk kc (Ac.headD 0).num (Bc.headD 0).num c

/-- The side conditions and the same-class constant-curve search. -/
def kxMWOKTK : Bool :=
  Fc == [c0f, [1]] && degG (MO Fc ks 0) A == 3 && kxOK Fc ks 0 A B kt l cs &&
  kxConst Fc ks 0 g A B kt l cs && kxRepOK Fc ks 0 g A B kt l cs &&
  kxMWSearchTK Fc ks lv c0f g A B kt l cs kmax

end Search

/-- **`kxDecide` at level `0` with all certificate searches, including constant curves.** -/
def kxDecideMWK0 (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (kmax : ℕ) : Option Bool :=
  match kxDecideMWC0 Fc ks lv g A B kt l cs ps bound rs kmax with
  | some b => some b
  | none =>
    if kxMWOKCK Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false
    else if kxMWOKTK Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false else none

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The constant-curve branch proves non-elementarity.** -/
theorem not_elementary_of_MWOKCK (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (kmax : ℕ)
    (hok : kxMWOKCK Fc ks lv (Fc.headD []) g A B kt l cs kmax = true) :
    ¬ HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) := by
  simp only [kxMWOKCK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hok
  unfold kxMWSearchCK at hq
  split at hq
  · exact absurd hq (by decide)
  rename_i z hz
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at hq
  obtain ⟨kc, hkc, hδ, m, -, kk, -, hchk⟩ := hq
  have : Fact (¬ IsSquare (sT Fc ks g A B kt l cs kc * kxKap Fc ks 0 A z)) :=
    ⟨not_isSquare_of_sqrt hδ⟩
  exact T.kx_not_elementary_mwC hmon hdeg 0 hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen B kt l cs
    hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkCK (Fc.headD []) g A B kt l cs (normC Fc 0 z) (kxKap Fc ks 0 A z) _ _ _ kk
        _ _ hFc hTm ⟨kc, hkc⟩ hchk rtsF hrl hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The same-class constant-curve branch proves non-elementarity.** -/
theorem not_elementary_of_MWOKTK (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (kmax : ℕ)
    (hok : kxMWOKTK Fc ks lv (Fc.headD []) g A B kt l cs kmax = true) :
    ¬ HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) := by
  simp only [kxMWOKTK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hok
  unfold kxMWSearchTK at hq
  split at hq
  · exact absurd hq (by decide)
  rename_i z hz
  simp only [List.any_eq_true, List.mem_range] at hq
  obtain ⟨kc, hkc, m, -, kk, -, hchk⟩ := hq
  exact T.kx_not_elementary_mwC hmon hdeg 0 hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen B kt l cs
    hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkTK (Fc.headD []) g A B kt l cs (normC Fc 0 z) _ _ _ kk _ _ _ hFc hTm
        ⟨kc, hkc⟩ hchk rtsF hrl hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

set_option maxHeartbeats 2000000 in
/-- **`kxDecideMWK0` is correct.** -/
theorem kxDecideMWK0_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (kmax : ℕ) (b : Bool) (hdec : kxDecideMWK0 Fc ks lv g A B kt l cs ps bound rs kmax = some b) :
    HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) ↔ b = true := by
  unfold kxDecideMWK0 at hdec
  cases hkx : kxDecideMWC0 Fc ks lv g A B kt l cs ps bound rs kmax with
  | some b' =>
    rw [hkx] at hdec
    cases hdec
    exact T.kxDecideMWC0_correct hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound
      rs kmax _ hkx
  | none =>
    rw [hkx] at hdec
    simp only at hdec
    split_ifs at hdec with hK hTK
    · cases hdec
      exact iff_of_false (T.not_elementary_of_MWOKCK hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ
        hgen B kt l cs kmax hK) (by decide)
    · cases hdec
      exact iff_of_false (T.not_elementary_of_MWOKTK hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ
        hgen B kt l cs kmax hTK) (by decide)

end MTower

end Curves.MT
