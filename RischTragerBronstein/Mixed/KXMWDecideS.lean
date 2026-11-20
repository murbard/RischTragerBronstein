import RischTragerBronstein.Mixed.KXMWDecide
import RischTragerBronstein.Mixed.KXCertBridgeS
import RischTragerBronstein.Mixed.KXCertBridgeCS
import RischTragerBronstein.Mixed.KFSquarePoint
import RischTragerBronstein.Mixed.KXMWDecideQ

/-!
# The Mordell–Weil certificate search at levels `m + 1`

`kxDecideMWS m`: `kxDecide` at level `m + 1` (any base curve), and when it does not answer the
search over the classes and levels of the twisted check `kxChkTS` (certificate over `Kₘ`).
Correct by `kxDecideMWS_correct` (`kx_not_elementary_mwC` + `grp_of_chkTS`).
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Search

variable (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (kmax : ℕ)

/-- A polynomial candidate for a fraction over `Kₘ`. -/
def polyOfS (f : Fr (KF Fc m)) : CPoly (KF Fc m) :=
  (CPoly.trim (Fr.norm f).1).map (· / (CPoly.trim (Fr.norm f).2).headD 1)

/-- The scaling: the product of the reduced denominators of `c₀, …, c₃`. -/
def mwUS : Fr (KF Fc m) :=
  ((List.range 4).map fun i ↦ Fr.ofPoly (Fr.norm (cFS Fc ks m A i)).2).foldr Fr.mul (Fr.ofPoly [1])

/-- **The search at level `m + 1`.** -/
def kxMWSearchS : Bool :=
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
      (List.range kmax).any fun kk ↦ kxChkTS Fc ks m g A B kt l cs z c uF Ac Bc (kk + 1) kc

/-- The side conditions and the search. -/
def kxMWOKS : Bool :=
  degG (MO Fc ks (m + 1)) A == 3 && kxOK Fc ks (m + 1) A B kt l cs &&
  kxConst Fc ks (m + 1) g A B kt l cs && kxRepOK Fc ks (m + 1) g A B kt l cs &&
  kxMWSearchS Fc ks lv m g A B kt l cs kmax

/-- **The conjugation search at level `m + 1`** (linear base, different classes). -/
def kxMWSearchCS : Bool :=
  match kxZ Fc ks lv (m + 1) A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks (m + 1) A z
    let uF := mwUS Fc ks m A
    (List.range (kxCls Fc ks (m + 1) g A B kt l cs).length).any fun kc ↦
      let s := sTS Fc ks m g A B kt l cs kc
      !(Rat.sqrt (s * κ) * Rat.sqrt (s * κ) == s * κ) &&
      (let Ac := polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2)) (AFrS Fc ks m A uF))
       let Bc := polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3)) (BFrS Fc ks m A uF))
       (List.range kmax).any fun kk ↦ kxChkCS Fc ks m g A B kt l cs z κ uF Ac Bc (kk + 1) kc)

def kxMWOKCS : Bool :=
  sqOK Fc && degG (MO Fc ks (m + 1)) A == 3 && kxOK Fc ks (m + 1) A B kt l cs &&
  kxConst Fc ks (m + 1) g A B kt l cs && kxRepOK Fc ks (m + 1) g A B kt l cs &&
  kxMWSearchCS Fc ks lv m g A B kt l cs kmax

end Search

/-- **`kxDecide` at level `m + 1` with the Mordell–Weil certificate search.** -/
def kxDecideMWS (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (kmax : ℕ) : Option Bool :=
  match kxDecide Fc ks lv (m + 1) g A B kt l cs ps bound rs with
  | some b => some b
  | none =>
    if kxMWOKS Fc ks lv m g A B kt l cs kmax then some false
    else if kxMWOKCS Fc ks lv m g A B kt l cs kmax then some false else none

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`kxDecideMWS` is correct**: whenever it answers `some b`, the integral is elementary exactly
when `b = true`. -/
theorem kxDecideMWS_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (kmax : ℕ) (b : Bool)
    (hdec : kxDecideMWS Fc ks lv m g A B kt l cs ps bound rs kmax = some b) :
    HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) ↔
      b = true := by
  unfold kxDecideMWS at hdec
  cases hkx : kxDecide Fc ks lv (m + 1) g A B kt l cs ps bound rs with
  | some b' =>
    rw [hkx] at hdec
    cases hdec
    exact T.kxDecide_correct hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps
      bound rs _ hkx
  | none =>
    rw [hkx] at hdec
    simp only at hdec
    split_ifs at hdec with hok hokC
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKS, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨hdeg3, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hok
      unfold kxMWSearchS at hq
      split at hq
      · exact absurd hq (by decide)
      rename_i z hz
      simp only [List.any_eq_true, List.mem_range] at hq
      obtain ⟨kc, hkc, kk, -, hchk⟩ := hq
      exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
        B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkTS m g A B kt l cs z _ _ _ _ (kk + 1) hTm ⟨kc, hkc⟩ hchk rtsF hrl
            hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKCS, Bool.and_eq_true, beq_iff_eq] at hokC
      obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hokC
      unfold kxMWSearchCS at hq
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
          have h := TE.grp_of_chkCS m g A B kt l cs z _ _ _ _ (kk + 1) hTm ⟨kc, hkc⟩ hchk rtsF hrl
            hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)

end MTower

end Curves.MT
