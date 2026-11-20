import RischTragerBronstein.Mixed.KXMWDecide
import RischTragerBronstein.Mixed.KXCertBridgeM

/-!
# `kxDecide` with the Manin-map certificate (level `0`, linear base)

`kxDecideMW0M`: run `kxDecide`; in the Mordell–Weil case try first the **Manin certificate**
`kxChkM` (one Wronskian, no doublings) for every class, then the height search of `kxDecideMW0`.
Correct by `kxDecideMW0M_correct`.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Search

variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))

/-- **The Manin certificate search** (data as in `kxMWSearch`). -/
def kxMWSearchM : Bool :=
  match kxZ Fc ks lv 0 A with
  | none => false
  | some z =>
    let r := Rat.sqrt (kxKap Fc ks 0 A z)
    let uF := mwU Fc ks c0f A
    let Ac := polyOf (AFr Fc ks c0f A uF)
    let Bc := polyOf (BFr Fc ks c0f A uF)
    (List.range (kxCls Fc ks 0 g A B kt l cs).length).any fun kc ↦
      kxChkM Fc ks c0f g A B kt l cs z r uF Ac Bc kc

/-- The side conditions and the Manin search. -/
def kxMWOKM : Bool :=
  Fc == [c0f, [1]] && degG (MO Fc ks 0) A == 3 && kxOK Fc ks 0 A B kt l cs &&
  kxConst Fc ks 0 g A B kt l cs && kxRepOK Fc ks 0 g A B kt l cs &&
  (kxGens Fc ks 0 g A B kt l cs).isEmpty && kxMWSearchM Fc ks lv c0f g A B kt l cs

lemma kxMWSearchM_spec (h : kxMWSearchM Fc ks lv c0f g A B kt l cs = true) :
    ∃ z r uF Ac Bc kc, kxZ Fc ks lv 0 A = some z ∧ kc < (kxCls Fc ks 0 g A B kt l cs).length ∧
      kxChkM Fc ks c0f g A B kt l cs z r uF Ac Bc kc = true := by
  unfold kxMWSearchM at h
  split at h
  · exact absurd h (by decide)
  · rename_i z hz
    simp only [List.any_eq_true, List.mem_range] at h
    obtain ⟨kc, hkc, hchk⟩ := h
    exact ⟨z, _, _, _, _, kc, hz, hkc, hchk⟩

end Search

/-- **`kxDecide` at level `0` with the Manin and height certificate searches.** -/
def kxDecideMW0M (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (kmax : ℕ) : Option Bool :=
  match kxDecide Fc ks lv 0 g A B kt l cs ps bound rs with
  | some b => some b
  | none => if kxMWOKM Fc ks lv (Fc.headD []) g A B kt l cs then some false else
      kxDecideMW0 Fc ks lv g A B kt l cs ps bound rs kmax

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 2000000 in
open Classical in
/-- **`kxDecideMW0M` is correct**: whenever it answers `some b`, the integral is elementary exactly
when `b = true`. -/
theorem kxDecideMW0M_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (kmax : ℕ) (b : Bool) (hdec : kxDecideMW0M Fc ks lv g A B kt l cs ps bound rs kmax = some b) :
    HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) ↔ b = true := by
  unfold kxDecideMW0M at hdec
  cases hkx : kxDecide Fc ks lv 0 g A B kt l cs ps bound rs with
  | some b' =>
    rw [hkx] at hdec
    cases hdec
    exact T.kxDecide_correct hmon hdeg 0 hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound rs
      _ hkx
  | none =>
    rw [hkx] at hdec
    simp only at hdec
    split_ifs at hdec with hok
    · cases hdec
      simp only [kxMWOKM, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hok
      obtain ⟨⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hgens⟩, hsearch⟩ := hok
      obtain ⟨z, r, uF, Ac, Bc, kc, hz, hkc, hchk⟩ :=
        kxMWSearchM_spec Fc ks lv _ g A B kt l cs hsearch
      have : Fact (Irreducible (toPoly (fKc Fc))) := inferInstance
      refine iff_of_false ?_ (by decide)
      exact T.kx_not_elementary_mwC hmon hdeg 0 hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen B kt l cs
        hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl _ b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkM (Fc.headD []) g A B kt l cs z r uF Ac Bc hFc hTm ⟨kc, hkc⟩ hchk
            hgens rtsF hrl b₀ hb₀ hns hns0 N hN μ
          convert h using 3)
    · exact T.kxDecideMW0_correct hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound
        rs kmax b hdec

end MTower

end Curves.MT

