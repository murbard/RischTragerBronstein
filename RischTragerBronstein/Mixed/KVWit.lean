import RischTragerBronstein.Mixed.KVMain
import RischTragerBronstein.Mixed.KYWit

/-!
# Radicals with poles over a logarithm: the antiderivative

`kvDecideCW` mirrors `kvDecideC` (`kvDecideCW_isSome`) and returns, with a `true` answer, the
solution of the parametric Risch equation and one column group (`KYGrp`: the witness `W` of a
component and its columns `kyColM`) per component; `kvDecideCW_valid`: the solution is a solution
and every group is a `kyColM` group of `A` itself, so the columns times `θʲ` are explicit sums of
logarithmic derivatives by `ky_root_logs`.
-/

open Polynomial Differential IntermediateField CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

section Codes

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

/-- `kvSolveC` with the antiderivative. -/
def kvSolveCW (m n j : ℕ) (η : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Option (Option (KYW Fc M m)) :=
  let comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)
  let tors := comps.map (kvTorsC Fc ks m n j M η A B l cs zN gs cpf ps bound rs)
  let wits := (List.zip comps tors).map fun p ↦
    kvWit Fc ks m n j M η A B l cs zN gs p.1 ((p.2.getD none).getD 0)
  match wits.allSome with
  | none => none
  | some Wbs =>
    match (Wbs.map (kyColM Fc ks m n M A (MO Fc ks m).one j)).allSome with
    | none => none
    | some colss =>
      let grps := (List.zip Wbs colss).map fun p ↦
        (⟨A, (MO Fc ks m).one, 1, p.1, p.2⟩ : KYGrp Fc M m)
      some ((prdeSolN Fc ks lv m (kpFr Fc ks m j n A) ((B, kvDen Fc ks m A l cs) : LC (m + 1))
        (grps.flatMap (·.cols))).map fun r ↦ (r, grps))

lemma kvSolveCW_isSome (m n j : ℕ) (η : LC m) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    (kvSolveCW Fc ks lv m n j η M zN gs A B l cs cpf ps bound rs).map Option.isSome =
      kvSolveC Fc ks lv m n j η M zN gs A B l cs cpf ps bound rs := by
  unfold kvSolveCW kvSolveC
  dsimp only
  split
  · rename_i heq; rw [heq]; rfl
  · rename_i Wbs heq
    rw [heq]
    dsimp only
    split
    · rename_i heq2; rw [heq2]; rfl
    · rename_i colss heq2
      rw [heq2]
      simp only [Option.map_some, Option.isSome_map]
      refine congrArg some ((prdeSolN_isSome _ _ _ _ _ _ _).trans ?_)
      have hlen := (MTower.allSome_spec _ colss heq2).1
      rw [List.flatMap_map]
      simp only
      rw [flatMap_zip_snd Wbs colss (by rw [hlen, List.length_map])]

/-- **`kvDecideC` with the antiderivative.** -/
def kvDecideCW (m n j : ℕ) (η : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Option (Option (KYW Fc M m)) :=
  let comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)
  let tors := comps.map (kvTorsC Fc ks m n j M η A B l cs zN gs cpf ps bound rs)
  if !(decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) then none
  else if cs.length = 0 then none
  else if !kqOK Fc ks m A B l cs then none
  else if !kvConst Fc ks m n j η A B l cs then some none
  else if !kvFieldOK Fc ks m n j η A B l cs M zN gs then none
  else if tors.any (· == none) then none
  else if tors.any (· == some none) then some none
  else kvSolveCW Fc ks lv m n j η M zN gs A B l cs cpf ps bound rs

/-- **`kvDecideCW` answers exactly as `kvDecideC`.** -/
theorem kvDecideCW_isSome (m n j : ℕ) (η : LC m) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    (kvDecideCW Fc ks lv m n j η M zN gs A B l cs cpf ps bound rs).map Option.isSome =
      kvDecideC Fc ks lv m n j η M zN gs A B l cs cpf ps bound rs := by
  unfold kvDecideCW kvDecideC
  dsimp only
  split_ifs
  all_goals first | rfl | exact kvSolveCW_isSome Fc ks lv m n j η M zN gs A B l cs cpf ps bound rs

/-- **The KV antiderivative display**: the components of the integral as strings. -/
def kvShow (m n j : ℕ) (η : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    String :=
  match kvDecideCW Fc ks lv m n j η M zN gs A B l cs (fun fK ↦ searchCert fK n) ps bound rs with
  | none => "no answer"
  | some none => "not elementary"
  | some (some w) => "elementary: q = " ++ toString w.1.1 ++ ", " ++ toString w.2.length ++
      " column groups"

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **A valid KV antiderivative**: a solution with `q₀ ≠ 0` for the integrand
`B/(∏ (t − c_q) Aˡ) θʲ`; every group's columns are those of `kyColM` for a twist
`Â = (zⁿ/κ) θⁿ` (so `ky_root_logs` applies to each). -/
def KVW.Valid (lv : (m : ℕ) → LC m) (m n j : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (θ : L) (w : KYW Fc M m) : Prop :=
  w.1 ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)
    (((B, kvDen Fc ks m A l cs) : LC (m + 1)) :: w.2.flatMap (·.cols)) ∧
  w.1.1.getD 0 0 ≠ 0 ∧
  ∀ g ∈ w.2, kyColM Fc ks m n M g.Ah g.z j g.W = some g.cols ∧ g.κ ≠ 0 ∧ T.ev m g.z ≠ 0 ∧
    T.ev (m + 1) (pcP Fc ks m g.Ah) = T.ev m g.z ^ n * ((g.κ⁻¹ : ℚ) : L) * θ ^ n

lemma kvSolveCW_valid (m n j : ℕ) (hTr : T.Tr (m + 1)) (η : LC m) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (θ : L) (hθ : θ ^ n = T.evP m A) (w : KYW Fc M m)
    (hw : kvSolveCW Fc ks lv m n j η M zN gs A B l cs cpf ps bound rs = some (some w)) :
    KVW.Valid T lv m n j M A B l cs θ w := by
  have hTm : T.Tr m := hTr.of_succ
  unfold kvSolveCW at hw
  dsimp only at hw
  split at hw
  · simp at hw
  rename_i Wbs hWbs
  split at hw
  · simp at hw
  rename_i colss hcolss
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hw)
  have hr0 := List.find?_some hr
  simp only [decide_eq_true_eq] at hr0
  refine ⟨List.mem_of_find?_eq_some hr, hr0, fun gr hg ↦ ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  obtain ⟨hl, hv⟩ := MTower.allSome_spec _ colss hcolss
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
  have hi1 : i < Wbs.length := by simp at hi; omega
  have hi2 : i < colss.length := by simp at hi; omega
  have hpe : p = (Wbs[i], colss[i]) := by rw [← hpi, List.getElem_zip]
  subst hpe
  refine ⟨?_, one_ne_zero, by rw [T.ev_one_code m hTm]; exact one_ne_zero, ?_⟩
  · have := hv i (by simpa using hi1) hi2
    simpa using this
  · show T.ev (m + 1) (pcP Fc ks m A) = T.ev m (MO Fc ks m).one ^ n * (((1 : ℚ)⁻¹ : ℚ) : L) * θ ^ n
    rw [T.ev_one_code m hTm]
    change T.evP m A / T.evP m [(MO Fc ks m).one] = _
    rw [T.evP_single, T.ev_one_code m hTm, hθ]
    simp

/-- **Every antiderivative returned by `kvDecideCW` is valid** (the columns then by
`ky_root_logs`). -/
theorem kvDecideCW_valid (m n j : ℕ) (hTr : T.Tr (m + 1)) (η : LC m) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A : GPoly (LC m)) (θ : L) (hθ : θ ^ n = T.evP m A)
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (w : KYW Fc M m)
    (hdec : kvDecideCW Fc ks lv m n j η M zN gs A B l cs cpf ps bound rs = some (some w)) :
    KVW.Valid T lv m n j M A B l cs θ w := by
  unfold kvDecideCW at hdec
  dsimp only at hdec
  split_ifs at hdec
  all_goals first
    | (simp at hdec; done)
    | exact T.kvSolveCW_valid m n j hTr η M zN gs A B l cs cpf ps bound rs θ hθ w hdec

end MTower

end Curves.MT
