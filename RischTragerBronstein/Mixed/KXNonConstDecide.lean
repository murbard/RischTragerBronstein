import RischTragerBronstein.Mixed.KXManinExist
import RischTragerBronstein.Mixed.KXConstAssemblyS

/-!
# Deciding the Mordell–Weil exception for non-constant curves at levels `m + 1`

`kxDecideNCS`: relation search (`kxDecideDL`), then the Manin search, then the height search, with
the checks run on the normalized zero code `normC z` (so the side conditions are provable). Correct
by `kxDecideNCS_correct`. `kxDecideNCS_decides` (in `KXNonConstDecide2`) proves that it answers.
-/

open Polynomial Differential IntermediateField Classical

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Search

variable (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (kmax : ℕ)

/-- The data of the class `kc`: scaling, short model. -/
def ncAc (s : ℚ) : CPoly (KF Fc m) :=
  polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2)) (AFrS Fc ks m A (mwUS Fc ks m A)))
/-- The `B` coefficient of the short model. -/
def ncBc (s : ℚ) : CPoly (KF Fc m) :=
  polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3)) (BFrS Fc ks m A (mwUS Fc ks m A)))

/-- **The Manin search** (normalized `z`). -/
def kxMWSearchSMN : Bool :=
  match kxZ Fc ks lv (m + 1) A with
  | none => false
  | some z =>
    (List.range (kxCls Fc ks (m + 1) g A B kt l cs).length).any fun kc ↦
      let s := sTS Fc ks m g A B kt l cs kc
      kxChkTSM Fc ks m g A B kt l cs (normC Fc (m + 1) z)
        (Rat.sqrt (kxKap Fc ks (m + 1) A z / s)) (mwUS Fc ks m A) (ncAc Fc ks m A s) (ncBc Fc ks m A s) kc

/-- **The height search** (normalized `z`). -/
def kxMWSearchSN : Bool :=
  match kxZ Fc ks lv (m + 1) A with
  | none => false
  | some z =>
    (List.range (kxCls Fc ks (m + 1) g A B kt l cs).length).any fun kc ↦
      let s := sTS Fc ks m g A B kt l cs kc
      (List.range kmax).any fun kk ↦
        kxChkTS Fc ks m g A B kt l cs (normC Fc (m + 1) z)
          (Rat.sqrt (kxKap Fc ks (m + 1) A z / s)) (mwUS Fc ks m A) (ncAc Fc ks m A s) (ncBc Fc ks m A s)
          kk kc

/-- Side conditions and the Manin search. -/
def kxMWOKSMN : Bool :=
  degG (MO Fc ks (m + 1)) A == 3 && kxOK Fc ks (m + 1) A B kt l cs &&
  kxConst Fc ks (m + 1) g A B kt l cs && kxRepOK Fc ks (m + 1) g A B kt l cs &&
  kxMWSearchSMN Fc ks lv m g A B kt l cs

/-- Side conditions and the height search. -/
def kxMWOKSN : Bool :=
  degG (MO Fc ks (m + 1)) A == 3 && kxOK Fc ks (m + 1) A B kt l cs &&
  kxConst Fc ks (m + 1) g A B kt l cs && kxRepOK Fc ks (m + 1) g A B kt l cs &&
  kxMWSearchSN Fc ks lv m g A B kt l cs kmax

end Search

/-- **The non-constant decider at level `m + 1`.** -/
def kxDecideNCS (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) : Option Bool :=
  match kxDecideDL Fc ks lv (m + 1) g A B kt l cs ps bound rs nmax with
  | some b => some b
  | none =>
    if kxMWOKSMN Fc ks lv m g A B kt l cs then some false
    else if kxMWOKSN Fc ks lv m g A B kt l cs kmax then some false else none

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **`kxDecideNCS` is correct.** -/
theorem kxDecideNCS_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (nmax kmax : ℕ) (b : Bool)
    (hdec : kxDecideNCS Fc ks lv m g A B kt l cs ps bound rs nmax kmax = some b) :
    HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) ↔
      b = true := by
  unfold kxDecideNCS at hdec
  cases hD : kxDecideDL Fc ks lv (m + 1) g A B kt l cs ps bound rs nmax with
  | some b' =>
    rw [hD] at hdec
    cases hdec
    exact T.kxDecideDL_correct hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps
      bound rs nmax _ hD
  | none =>
    rw [hD] at hdec
    simp only at hdec
    split_ifs at hdec with hM hH
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKSMN, Bool.and_eq_true, beq_iff_eq] at hM
      obtain ⟨⟨⟨⟨hdeg3, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hM
      unfold kxMWSearchSMN at hq
      split at hq
      · exact absurd hq (by decide)
      rename_i z hz
      simp only [List.any_eq_true, List.mem_range] at hq
      obtain ⟨kc, hkc, hchk⟩ := hq
      exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
        B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkTSM m g A B kt l cs _ _ _ _ _ hTm ⟨kc, hkc⟩ hchk rtsF hrl
            hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)
    · cases hdec
      refine iff_of_false ?_ (by decide)
      simp only [kxMWOKSN, Bool.and_eq_true, beq_iff_eq] at hH
      obtain ⟨⟨⟨⟨hdeg3, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hH
      unfold kxMWSearchSN at hq
      split at hq
      · exact absurd hq (by decide)
      rename_i z hz
      simp only [List.any_eq_true, List.mem_range] at hq
      obtain ⟨kc, hkc, kk, -, hchk⟩ := hq
      exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
        B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
          intro cC xC βC hns hns0 N hN μ
          have h := TE.grp_of_chkTS m g A B kt l cs _ _ _ _ _ kk hTm ⟨kc, hkc⟩ hchk rtsF hrl
            hrs b₀ hb₀ hns hns0 N hN μ
          convert h using 3)

/-- Once a search succeeds, `kxDecideNCS` answers. -/
lemma kxDecideNCS_isSome_of (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ)
    (h : kxMWOKSMN Fc ks lv m g A B kt l cs = true ∨ kxMWOKSN Fc ks lv m g A B kt l cs kmax = true) :
    (kxDecideNCS Fc ks lv m g A B kt l cs ps bound rs nmax kmax).isSome := by
  unfold kxDecideNCS
  rcases kxDecideDL Fc ks lv (m + 1) g A B kt l cs ps bound rs nmax with _ | b
  · dsimp only
    rcases h with h | h
    · rw [if_pos h]; rfl
    · split_ifs <;> rfl
  · rfl

end MTower

end Curves.MT
