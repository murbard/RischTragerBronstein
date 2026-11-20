import RischTragerBronstein.Mixed.KXWit
import RischTragerBronstein.Mixed.KXDepDecides
import RischTragerBronstein.Mixed.KXConstAssemblyS

/-!
# The dependent case with the antiderivative

`kxSolveDepCW` mirrors `kxSolveDepC`: the columns of the classes (with a torsion witness or a
witness of a relation with `δ₀`) are the same square-root columns `kxSq` as in `kxSolveCW`, so the
returned data is a valid antiderivative (`KXW.Valid`, read by `sqcols_antiderivative`). With
`kxDecideCW`: `kxDecideDLW` (agreeing with `kxDecideDL`, `kxDecideDLW_isSome`, valid
`kxDecideDLW_valid`), and the constant-curve deciders `kxDecideDK0W`, `kxDecideDKSW` (their
`false` answers come from the certificate searches).
-/

open Polynomial CPoly SqrtIndep

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Dep

variable (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))

/-- `kxSolveDepC` with the antiderivative. -/
def kxSolveDepCW (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (z : LC m) (nmax : ℕ) : Option (Option (KXW m)) :=
  let cls := kxCls Fc ks m g A B kt l cs
  let tors := cls.map (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs)
  let wits := (List.zip cls tors).map fun p ↦ kxWitAny Fc ks m g A B kt l cs z nmax p.1 p.2
  match wits.allSome with
  | none => none
  | some Wbs =>
    let cols := (List.zip cls Wbs).map fun p ↦ kxSq Fc ks m g A B kt l cs p.1 p.2
    some ((prdeSolN Fc ks lv m (kpFr Fc ks m 1 2 A) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1))
      (cols.map (SqCol.code Fc ks))).map fun r ↦ (r, cols))

lemma kxSolveDepCW_isSome (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (z : LC m) (nmax : ℕ) :
    (kxSolveDepCW Fc ks lv m g A B kt l cs cpf ps bound rs z nmax).map Option.isSome =
      kxSolveDepC Fc ks lv m g A B kt l cs cpf ps bound rs z nmax := by
  unfold kxSolveDepCW kxSolveDepC
  dsimp only
  split
  · rename_i heq; rw [heq]; rfl
  · rename_i Wbs heq
    rw [heq]
    simp only [Option.map_some, Option.isSome_map]
    exact congrArg some ((prdeSolN_isSome _ _ _ _ _ _ _).trans (by rw [List.map_map]; rfl))

/-- `kxDecideDepC` with the antiderivative. -/
def kxDecideDepCW (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (nmax : ℕ) : Option (Option (KXW m)) :=
  let tors := (kxCls Fc ks m g A B kt l cs).map (kxTorsC Fc ks m g A B kt l cs cpf ps bound rs)
  if cs.length = 0 then none
  else if !kxOK Fc ks m A B kt l cs then none
  else if !kxConst Fc ks m g A B kt l cs then none
  else if !kxRepOK Fc ks m g A B kt l cs then none
  else if tors.any (· == none) then none
  else
    match kxZ Fc ks lv m A with
    | none => none
    | some z =>
      match kxTors0C Fc ks m A cpf ps bound rs z with
      | some none => kxSolveDepCW Fc ks lv m g A B kt l cs cpf ps bound rs z nmax
      | _ => none

lemma kxDecideDepCW_isSome (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (nmax : ℕ) :
    (kxDecideDepCW Fc ks lv m g A B kt l cs cpf ps bound rs nmax).map Option.isSome =
      kxDecideDepC Fc ks lv m g A B kt l cs cpf ps bound rs nmax := by
  unfold kxDecideDepCW kxDecideDepC
  dsimp only
  split_ifs <;> try rfl
  rcases kxZ Fc ks lv m A with _ | z
  · rfl
  · dsimp only
    rcases kxTors0C Fc ks m A cpf ps bound rs z with _ | _ | N
    · rfl
    · exact kxSolveDepCW_isSome Fc ks lv m g A B kt l cs cpf ps bound rs z nmax
    · rfl

/-- **`kxDecideDL` with the antiderivative.** -/
def kxDecideDLW (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax : ℕ) : Option (Option (KXW m)) :=
  match kxDecideCW Fc ks lv m g A B kt l cs (fun fK ↦ localCert fK 2) ps bound rs with
  | some r => some r
  | none => kxDecideDepCW Fc ks lv m g A B kt l cs (fun fK ↦ localCert fK 2) ps bound rs nmax

theorem kxDecideDLW_isSome (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax : ℕ) :
    (kxDecideDLW Fc ks lv m g A B kt l cs ps bound rs nmax).map Option.isSome =
      kxDecideDL Fc ks lv m g A B kt l cs ps bound rs nmax := by
  have h1 := kxDecideCW_isSome Fc ks lv m g A B kt l cs (fun fK ↦ localCert fK 2) ps bound rs
  unfold kxDecideDLW kxDecideDL kxDecideL
  rcases hW : kxDecideCW Fc ks lv m g A B kt l cs (fun fK ↦ localCert fK 2) ps bound rs with _ | r
  · rw [hW] at h1
    rw [← h1]
    exact kxDecideDepCW_isSome Fc ks lv m g A B kt l cs _ ps bound rs nmax
  · rw [hW] at h1
    rw [← h1]; rfl

end Dep

/-- **`kxDecideDK0` with the antiderivative.** -/
def kxDecideDK0W (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) : Option (Option (KXW 0)) :=
  match kxDecideDLW Fc ks lv 0 g A B kt l cs ps bound rs nmax with
  | some r => some r
  | none =>
    if kxMWOKCK Fc ks lv (Fc.headD []) g A B kt l cs kmax then some none
    else if kxMWOKTK Fc ks lv (Fc.headD []) g A B kt l cs kmax then some none else none

theorem kxDecideDK0W_isSome (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) :
    (kxDecideDK0W Fc ks lv g A B kt l cs ps bound rs nmax kmax).map Option.isSome =
      kxDecideDK0 Fc ks lv g A B kt l cs ps bound rs nmax kmax := by
  have h1 := kxDecideDLW_isSome Fc ks lv 0 g A B kt l cs ps bound rs nmax
  unfold kxDecideDK0W kxDecideDK0
  rcases hW : kxDecideDLW Fc ks lv 0 g A B kt l cs ps bound rs nmax with _ | r
  · rw [hW] at h1; rw [← h1]; dsimp only; split_ifs <;> rfl
  · rw [hW] at h1; rw [← h1]; rfl

/-- **`kxDecideDKS` with the antiderivative.** -/
def kxDecideDKSW (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) :
    Option (Option (KXW (m + 1))) :=
  match kxDecideDLW Fc ks lv (m + 1) g A B kt l cs ps bound rs nmax with
  | some r => some r
  | none =>
    if kxMWOKCKS Fc ks lv m g A B kt l cs kmax then some none
    else if kxMWOKTKS Fc ks lv m g A B kt l cs kmax then some none else none

theorem kxDecideDKSW_isSome (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) :
    (kxDecideDKSW Fc ks lv m g A B kt l cs ps bound rs nmax kmax).map Option.isSome =
      kxDecideDKS Fc ks lv m g A B kt l cs ps bound rs nmax kmax := by
  have h1 := kxDecideDLW_isSome Fc ks lv (m + 1) g A B kt l cs ps bound rs nmax
  unfold kxDecideDKSW kxDecideDKS
  rcases hW : kxDecideDLW Fc ks lv (m + 1) g A B kt l cs ps bound rs nmax with _ | r
  · rw [hW] at h1; rw [← h1]; dsimp only; split_ifs <;> rfl
  · rw [hW] at h1; rw [← h1]; rfl

universe u

variable {Fc ks lv} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma kxSolveDepCW_valid (m : ℕ) (h : T.Tr m) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (z : LC m) (nmax : ℕ) (w : KXW m)
    (hw : kxSolveDepCW Fc ks lv m g A B kt l cs cpf ps bound rs z nmax = some (some w)) :
    KXW.Valid T lv m A B kt l cs w := by
  unfold kxSolveDepCW at hw
  dsimp only at hw
  split at hw
  · exact absurd hw (by simp)
  · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hw)
    have hr0 := List.find?_some hr
    simp only [decide_eq_true_eq] at hr0
    refine ⟨List.mem_of_find?_eq_some hr, hr0, fun c hc ↦ ?_⟩
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hc
    exact T.kxSq_good m h g A B kt l cs p.1 p.2

lemma kxDecideDepCW_valid (m : ℕ) (h : T.Tr m) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (nmax : ℕ) (w : KXW m)
    (hw : kxDecideDepCW Fc ks lv m g A B kt l cs cpf ps bound rs nmax = some (some w)) :
    KXW.Valid T lv m A B kt l cs w := by
  unfold kxDecideDepCW at hw
  dsimp only at hw
  split_ifs at hw
  rcases hz : kxZ Fc ks lv m A with _ | z
  · rw [hz] at hw; cases hw
  · rw [hz] at hw
    dsimp only at hw
    rcases ht : kxTors0C Fc ks m A cpf ps bound rs z with _ | _ | N
    · rw [ht] at hw; cases hw
    · rw [ht] at hw
      exact T.kxSolveDepCW_valid m h g A B kt l cs cpf ps bound rs z nmax w hw
    · rw [ht] at hw; cases hw

/-- **Every antiderivative returned by `kxDecideDLW` is valid.** -/
theorem kxDecideDLW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (g : LC m) (A B : GPoly (LC m))
    (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax : ℕ) (w : KXW m)
    (hdec : kxDecideDLW Fc ks lv m g A B kt l cs ps bound rs nmax = some (some w)) :
    KXW.Valid T lv m A B kt l cs w := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTm : T.Tr m := MS.hyp.tr.of_succ
  unfold kxDecideDLW at hdec
  rcases hW : kxDecideCW Fc ks lv m g A B kt l cs (fun fK ↦ localCert fK 2) ps bound rs with _ | r
  · rw [hW] at hdec
    exact T.kxDecideDepCW_valid m hTm g A B kt l cs _ ps bound rs nmax w hdec
  · rw [hW] at hdec
    cases hdec
    exact T.kxDecideCW_valid hmon hdeg m hn hc g A B kt l cs _ ps bound rs w hW

theorem kxDecideDK0W_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) (g : LC 0) (A B : GPoly (LC 0))
    (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ)
    (w : KXW 0) (hdec : kxDecideDK0W Fc ks lv g A B kt l cs ps bound rs nmax kmax = some (some w)) :
    KXW.Valid T lv 0 A B kt l cs w := by
  unfold kxDecideDK0W at hdec
  rcases hW : kxDecideDLW Fc ks lv 0 g A B kt l cs ps bound rs nmax with _ | r
  · rw [hW] at hdec; dsimp only at hdec; split_ifs at hdec <;> simp at hdec
  · rw [hW] at hdec; cases hdec
    exact T.kxDecideDLW_valid hmon hdeg 0 hn hc g A B kt l cs ps bound rs nmax w hW

theorem kxDecideDKSW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) (g : LC (m + 1))
    (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (nmax kmax : ℕ) (w : KXW (m + 1))
    (hdec : kxDecideDKSW Fc ks lv m g A B kt l cs ps bound rs nmax kmax = some (some w)) :
    KXW.Valid T lv (m + 1) A B kt l cs w := by
  unfold kxDecideDKSW at hdec
  rcases hW : kxDecideDLW Fc ks lv (m + 1) g A B kt l cs ps bound rs nmax with _ | r
  · rw [hW] at hdec; dsimp only at hdec; split_ifs at hdec <;> simp at hdec
  · rw [hW] at hdec; cases hdec
    exact T.kxDecideDLW_valid hmon hdeg (m + 1) hn hc g A B kt l cs ps bound rs nmax w hW

end MTower

end Curves.MT
