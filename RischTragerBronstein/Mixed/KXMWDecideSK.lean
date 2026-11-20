import RischTragerBronstein.Mixed.KXMWDecideS
import RischTragerBronstein.Mixed.KXCertBridgeCKS

/-!
# Constant curves at the levels `m + 1`: the searches and the decider

`kxDecideMWSK m`: `kxDecideMWS m` and, when it does not answer, the searches with heights over `ℚ`
for curves with rational coefficients (`kxChkCKS` for a class in another square class than `P₊`,
linear base; `kxChkTKS` for the same class). Correct by `kxDecideMWSK_correct`.
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

/-- The rational value of a head coefficient (`0` if not rational). -/
def headRat (p : CPoly (KF Fc m)) : ℚ := (ratOfK Fc m (p.headD 0)).getD 0

/-- The scaling candidates at level `m + 1` (`1, 2, 3, 6` and the common denominator of the model
at scale `1`; for rational coefficients a rational scaling suffices). -/
def mwScalesS (s : ℚ) : List ℚ :=
  let a1 := headRat Fc m (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2)) (AFrS Fc ks m A (Fr.ofPoly [(1 : KF Fc m)]))))
  let b1 := headRat Fc m (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3)) (BFrS Fc ks m A (Fr.ofPoly [(1 : KF Fc m)]))))
  [1, 2, 3, 6, (Nat.lcm a1.den b1.den : ℚ)]

/-- **The constant-curve search at level `m + 1`, different classes.** -/
def kxMWSearchCKS : Bool :=
  match kxZ Fc ks lv (m + 1) A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks (m + 1) A z
    (List.range (kxCls Fc ks (m + 1) g A B kt l cs).length).any fun kc ↦
      let s := sTS Fc ks m g A B kt l cs kc
      !(Rat.sqrt (s * κ) * Rat.sqrt (s * κ) == s * κ) &&
      (mwScalesS Fc ks m A s).any fun mm ↦
        let uF : Fr (KF Fc m) := Fr.ofPoly [((mm : ℚ) : KF Fc m)]
        let Ac : CPoly (KF Fc m) :=
          [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2)) (AFrS Fc ks m A uF))).headD 0]
        let Bc : CPoly (KF Fc m) :=
          [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3)) (BFrS Fc ks m A uF))).headD 0]
        (List.range kmax).any fun kk ↦
          kxChkCKS Fc ks m g A B kt l cs (normC Fc (m + 1) z) κ uF Ac Bc kk kc
            (headRat Fc m Ac).num (headRat Fc m Bc).num

def kxMWOKCKS : Bool :=
  sqOK Fc && degG (MO Fc ks (m + 1)) A == 3 && kxOK Fc ks (m + 1) A B kt l cs &&
  kxConst Fc ks (m + 1) g A B kt l cs && kxRepOK Fc ks (m + 1) g A B kt l cs &&
  kxMWSearchCKS Fc ks lv m g A B kt l cs kmax

/-- **The constant-curve search at level `m + 1`, same class.** -/
def kxMWSearchTKS : Bool :=
  match kxZ Fc ks lv (m + 1) A with
  | none => false
  | some z =>
    let κ := kxKap Fc ks (m + 1) A z
    (List.range (kxCls Fc ks (m + 1) g A B kt l cs).length).any fun kc ↦
      let s := sTS Fc ks m g A B kt l cs kc
      let c := Rat.sqrt (κ / s)
      (mwScalesS Fc ks m A s).any fun mm ↦
        let uF : Fr (KF Fc m) := Fr.ofPoly [((mm : ℚ) : KF Fc m)]
        let Ac : CPoly (KF Fc m) :=
          [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2)) (AFrS Fc ks m A uF))).headD 0]
        let Bc : CPoly (KF Fc m) :=
          [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3)) (BFrS Fc ks m A uF))).headD 0]
        (List.range kmax).any fun kk ↦
          kxChkTKS Fc ks m g A B kt l cs (normC Fc (m + 1) z) uF Ac Bc kk kc
            (headRat Fc m Ac).num (headRat Fc m Bc).num c

def kxMWOKTKS : Bool :=
  degG (MO Fc ks (m + 1)) A == 3 && kxOK Fc ks (m + 1) A B kt l cs &&
  kxConst Fc ks (m + 1) g A B kt l cs && kxRepOK Fc ks (m + 1) g A B kt l cs &&
  kxMWSearchTKS Fc ks lv m g A B kt l cs kmax

end Search

/-- **`kxDecideMWS` with the constant-curve searches at level `m + 1`.** -/
def kxDecideMWSK (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (kmax : ℕ) : Option Bool :=
  match kxDecideMWS Fc ks lv m g A B kt l cs ps bound rs kmax with
  | some b => some b
  | none =>
    if kxMWOKCKS Fc ks lv m g A B kt l cs kmax then some false
    else if kxMWOKTKS Fc ks lv m g A B kt l cs kmax then some false else none

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`kxDecideMWSK` is correct.** -/
theorem kxDecideMWSK_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (kmax : ℕ) (b : Bool)
    (hdec : kxDecideMWSK Fc ks lv m g A B kt l cs ps bound rs kmax = some b) :
    HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) ↔
      b = true := by
  unfold kxDecideMWSK at hdec
  cases hkx : kxDecideMWS Fc ks lv m g A B kt l cs ps bound rs kmax with
  | some b' =>
    rw [hkx] at hdec
    cases hdec
    exact T.kxDecideMWS_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps
      bound rs kmax _ hkx
  | none =>
    rw [hkx] at hdec
    simp only at hdec
    split_ifs at hdec with hok hokT
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKCKS, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hok
      unfold kxMWSearchCKS at hq
      split at hq
      · exact absurd hq (by decide)
      rename_i z hz
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne] at hq
      obtain ⟨kc, hkc, hδ, mm, -, kk, -, hchk⟩ := hq
      have : Fact (¬ IsSquare (Rat.cast (sTS Fc ks m g A B kt l cs kc * kxKap Fc ks (m + 1) A z) :
          KF Fc m)) :=
        ⟨not_isSquare_KF_sqOK Fc hFc _ (not_isSquare_of_sqrt hδ) m⟩
      exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
        B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkCKS m g A B kt l cs _ _ _ _ _ kk _ _ hTm ⟨kc, hkc⟩ hchk rtsF hrl
            hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKTKS, Bool.and_eq_true, beq_iff_eq] at hokT
      obtain ⟨⟨⟨⟨hdeg3, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hokT
      unfold kxMWSearchTKS at hq
      split at hq
      · exact absurd hq (by decide)
      rename_i z hz
      simp only [List.any_eq_true, List.mem_range] at hq
      obtain ⟨kc, hkc, mm, -, kk, -, hchk⟩ := hq
      exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
        B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkTKS m g A B kt l cs _ _ _ _ kk _ _ _ hTm ⟨kc, hkc⟩ hchk rtsF hrl
            hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)

end MTower

end Curves.MT
