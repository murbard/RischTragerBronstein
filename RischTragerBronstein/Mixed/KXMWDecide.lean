import RischTragerBronstein.Mixed.KXNotElemMW
import RischTragerBronstein.Mixed.KXCertBridge

/-!
# `kxDecide` with the Mordell–Weil certificate search (level `0`, linear base)

`kxDecideMW0`: run `kxDecide`; when it does not answer (the Mordell–Weil case), search for the
data of the bridge check `kxChk` automatically — `z` from `kxZ`, `r = √κ` (`Rat.sqrt`), the scaling
`u` (product of the denominators of the coefficients of `A`), the short model `Ac`, `Bc` read off
the normalized fractions, every class and certificate level `1, …, kmax` — and answer
`some false` if a check passes. Correct by `kxDecideMW0_correct` (`kxDecide_correct` +
`kx_not_elementary_mwC` + `grp_of_chk`).
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Search

variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (kmax : ℕ)

/-- The scaling `u`: the product of the (reduced) denominators of `c₀, …, c₃`. -/
def mwU : Fr ℚ :=
  ((List.range 4).map fun i ↦ Fr.ofPoly (Fr.norm (cF Fc ks c0f A i)).2).foldr Fr.mul (Fr.ofPoly [1])

/-- A polynomial candidate for a fraction (exact when the reduced denominator is constant). -/
def polyOf (f : Fr ℚ) : CPoly ℚ :=
  (CPoly.trim (Fr.norm f).1).map (· / (CPoly.trim (Fr.norm f).2).headD 1)

/-- **The certificate search.** -/
def kxMWSearch : Bool :=
  match kxZ Fc ks lv 0 A with
  | none => false
  | some z =>
    let r := Rat.sqrt (kxKap Fc ks 0 A z)
    let uF := mwU Fc ks c0f A
    let Ac := polyOf (AFr Fc ks c0f A uF)
    let Bc := polyOf (BFr Fc ks c0f A uF)
    (List.range (kxCls Fc ks 0 g A B kt l cs).length).any fun kc ↦
      (List.range kmax).any fun kk ↦ kxChk Fc ks c0f g A B kt l cs z r uF Ac Bc (kk + 1) kc

/-- The side conditions and the search. -/
def kxMWOK : Bool :=
  Fc == [c0f, [1]] && degG (MO Fc ks 0) A == 3 && kxOK Fc ks 0 A B kt l cs &&
  kxConst Fc ks 0 g A B kt l cs && kxRepOK Fc ks 0 g A B kt l cs &&
  (kxGens Fc ks 0 g A B kt l cs).isEmpty && kxMWSearch Fc ks lv c0f g A B kt l cs kmax

lemma kxMWSearch_spec (h : kxMWSearch Fc ks lv c0f g A B kt l cs kmax = true) :
    ∃ z r uF Ac Bc kk kc, kxZ Fc ks lv 0 A = some z ∧ kc < (kxCls Fc ks 0 g A B kt l cs).length ∧
      kxChk Fc ks c0f g A B kt l cs z r uF Ac Bc kk kc = true := by
  unfold kxMWSearch at h
  split at h
  · exact absurd h (by decide)
  · rename_i z hz
    simp only [List.any_eq_true, List.mem_range] at h
    obtain ⟨kc, hkc, kk, -, hchk⟩ := h
    exact ⟨z, _, _, _, _, _, kc, hz, hkc, hchk⟩

end Search

/-- **`kxDecide` at level `0` with the Mordell–Weil certificate search.** -/
def kxDecideMW0 (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (kmax : ℕ) : Option Bool :=
  match kxDecide Fc ks lv 0 g A B kt l cs ps bound rs with
  | some b => some b
  | none => if kxMWOK Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false else none

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 2000000 in
open Classical in
/-- **`kxDecideMW0` is correct**: whenever it answers `some b`, the integral is elementary exactly
when `b = true`. -/
theorem kxDecideMW0_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (kmax : ℕ) (b : Bool) (hdec : kxDecideMW0 Fc ks lv g A B kt l cs ps bound rs kmax = some b) :
    HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) ↔ b = true := by
  unfold kxDecideMW0 at hdec
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
    cases hdec
    simp only [kxMWOK, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hok
    obtain ⟨⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hgens⟩, hsearch⟩ := hok
    obtain ⟨z, r, uF, Ac, Bc, kk, kc, hz, hkc, hchk⟩ := kxMWSearch_spec Fc ks lv _ g A B kt l cs kmax hsearch
    have : Fact (Irreducible (toPoly (fKc Fc))) := inferInstance
    refine iff_of_false ?_ (by decide)
    exact T.kx_not_elementary_mwC hmon hdeg 0 hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen B kt l cs
      hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl _ b₀ hb₀ ↦ by
        intro cC xC βC hns hns0 N hN μ
        have h := TE.grp_of_chk (Fc.headD []) g A B kt l cs z r uF Ac Bc kk hFc hTm ⟨kc, hkc⟩ hchk
          hgens rtsF hrl b₀ hb₀ hns hns0 N hN μ
        convert h using 3)

end MTower

end Curves.MT
