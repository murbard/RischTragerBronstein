import RischTragerBronstein.Mixed.KZDecides
import RischTragerBronstein.Mixed.KYWit

/-!
# Radicals with poles in `Fₘ ⊗ N` over an exponential: the antiderivative

`kzDecideCW` mirrors `kzDecideC` (`kzDecideCW_isSome`) like `kyDecideCW`: the parametric solution
and the column groups of `kyColM` (`KYGrp`); `kzDecideCW_valid`, the columns explicit by
`ky_root_logs`.
-/

open Polynomial Differential IntermediateField CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

section Codes

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

/-- `kzSolveC` with the antiderivative. -/
def kzSolveCW (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) (extra : List (KYGrp Fc M m)) : Option (Option (KYW Fc M m)) :=
  let comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)
  let tors := comps.map (kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs)
  let wits := (List.zip comps tors).map fun p ↦
    kzWit Fc ks m n j M g A B kt l cs zN gs p.1 ((p.2.getD none).getD 0)
  match wits.allSome with
  | none => none
  | some Wbs =>
    match (Wbs.map (kyColM Fc ks m n M A (MO Fc ks m).one j)).allSome with
    | none => none
    | some colss =>
      let grps := extra ++ (List.zip Wbs colss).map fun p ↦
        (⟨A, (MO Fc ks m).one, 1, p.1, p.2⟩ : KYGrp Fc M m)
      some ((prdeSolN Fc ks lv m (kpFr Fc ks m j n A) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1))
        (grps.flatMap (·.cols))).map fun r ↦ (r, grps))

lemma kzSolveCW_isSome (m n j : ℕ) (g : LC m) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (extra : List (KYGrp Fc M m)) :
    (kzSolveCW Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs extra).map Option.isSome =
      kzSolveC Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs (extra.flatMap (·.cols)) := by
  unfold kzSolveCW kzSolveC
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
      rw [List.flatMap_append, List.flatMap_map]
      simp only
      rw [flatMap_zip_snd Wbs colss (by rw [hlen, List.length_map])]

/-- **`kzDecideC` with the antiderivative.** -/
def kzDecideCW (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Option (Option (KYW Fc M m)) :=
  let O := MO Fc ks m
  let d := M.length - 1
  let comps := (List.range d).filter (kyNZ n j M zN gs cs.length)
  let tors := comps.map (kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs)
  let solve : List (KYGrp Fc M m) → Option (Option (KYW Fc M m)) :=
    kzSolveCW Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs
  if !(decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) then none
  else if cs.length = 0 then none
  else if !kzOK Fc ks m M A B kt l cs dC then none
  else if !kzConst Fc ks m n j M g A B kt l cs then some none
  else if !kzFieldOK Fc ks m n j M g A B kt l cs zN gs then none
  else if tors.any (· == none) then none
  else
    let allT := !(tors.any (· == some none))
    match krZ Fc ks lv m n A with
    | none =>
      if allT then solve []
      else if (List.range (n + 1)).all (fun ℓ ↦ !(decide (Nat.Prime ℓ ∧ ℓ ∣ n)) ||
          (krZ Fc ks lv m ℓ A).isNone) then some none
      else none
    | some z =>
      let κ := (ratValC Fc ks m (O.mul (powC O z n) (A.getD 0 O.zero))).getD 0
      if κ = 0 then none
      else
        match kyTorsPsiC Fc ks m n M A zN z κ cpf ps bound rs with
        | none => none
        | some none =>
          if allT then solve []
          else if kyZeroTorsC Fc ks m n M A zN z κ cpf ps bound rs then some none else none
        | some (some N0) =>
          if allT then
            match kyWitPsi Fc ks m n M A zN z κ N0 with
            | none => none
            | some W0 =>
              match kyColM Fc ks m n M (krAh Fc ks m n A z κ) z j W0 with
              | none => none
              | some cols0 => solve [⟨krAh Fc ks m n A z κ, z, κ, W0, cols0⟩]
          else if kyZeroTorsC Fc ks m n M A zN z κ cpf ps bound rs then some none else none

/-- **`kzDecideCW` answers exactly as `kzDecideC`.** -/
theorem kzDecideCW_isSome (m n j : ℕ) (g : LC m) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    (kzDecideCW Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs).map Option.isSome =
      kzDecideC Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs := by
  unfold kzDecideCW kzDecideC
  dsimp only
  have hs : ∀ e : List (KYGrp Fc M m),
      (kzSolveCW Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs e).map Option.isSome =
      kzSolveC Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs (e.flatMap (·.cols)) :=
    kzSolveCW_isSome Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs
  generalize (decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) = b1
  generalize kzOK Fc ks m M A B kt l cs dC = b3
  generalize kzConst Fc ks m n j M g A B kt l cs = b4
  generalize kzFieldOK Fc ks m n j M g A B kt l cs zN gs = b5
  generalize ((List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)).map
    (kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs) = tors
  by_cases h1 : (!b1) = true
  · rw [if_pos h1, if_pos h1]; rfl
  rw [if_neg h1, if_neg h1]
  by_cases hcs : cs.length = 0
  · rw [if_pos hcs, if_pos hcs]; rfl
  rw [if_neg hcs, if_neg hcs]
  by_cases h3 : (!b3) = true
  · rw [if_pos h3, if_pos h3]; rfl
  rw [if_neg h3, if_neg h3]
  by_cases h4 : (!b4) = true
  · rw [if_pos h4, if_pos h4]; rfl
  rw [if_neg h4, if_neg h4]
  by_cases h5 : (!b5) = true
  · rw [if_pos h5, if_pos h5]; rfl
  rw [if_neg h5, if_neg h5]
  by_cases hn : tors.any (· == none) = true
  · rw [if_pos hn, if_pos hn]; rfl
  rw [if_neg hn, if_neg hn]
  generalize (!tors.any (· == some none)) = allT
  rcases hz : krZ Fc ks lv m n A with _ | z
  · simp only [hz]
    cases allT <;> (try split_ifs) <;> first | rfl | exact hs [] | simp_all
  · simp only [hz]
    by_cases hκ : (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
        (A.getD 0 (MO Fc ks m).zero))).getD 0 = 0
    · rw [if_pos hκ, if_pos hκ]; rfl
    rw [if_neg hκ, if_neg hκ]
    set κ := (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
        (A.getD 0 (MO Fc ks m).zero))).getD 0 with hκd
    · rcases ht : kyTorsPsiC Fc ks m n M A zN z κ cpf ps bound rs with _ | _ | N0
      · rfl
      · dsimp only
        cases allT <;> (try split_ifs) <;> first | rfl | exact hs [] | simp_all
      · dsimp only
        cases allT
        · (try split_ifs) <;> first | rfl | simp_all
        · simp only [if_true]
          rcases hw : kyWitPsi Fc ks m n M A zN z κ N0 with _ | W0
          · rfl
          · simp only
            rcases hc : kyColM Fc ks m n M (krAh Fc ks m n A z κ) z j W0 with _ | cols0
            · rfl
            · simp only
              have := hs [⟨krAh Fc ks m n A z κ, z, κ, W0, cols0⟩]
              simpa using this

/-- **Where a KY witness comes from**: `kzSolveCW` with no extra group, or with the group of the
witness of `Ψ` (with `κ ≠ 0`). -/
lemma kzDecideCW_src (m n j : ℕ) (g : LC m) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (w : KYW Fc M m) (h : kzDecideCW Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs =
      some (some w)) :
    (decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) = true ∧
    kzOK Fc ks m M A B kt l cs dC = true ∧
    ((kzSolveCW Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs [] = some (some w)) ∨
     ∃ z W0 cols0, krZ Fc ks lv m n A = some z ∧
      (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
        (A.getD 0 (MO Fc ks m).zero))).getD 0 ≠ 0 ∧
      kyColM Fc ks m n M (krAh Fc ks m n A z ((ratValC Fc ks m ((MO Fc ks m).mul
        (powC (MO Fc ks m) z n) (A.getD 0 (MO Fc ks m).zero))).getD 0)) z j W0 = some cols0 ∧
      kzSolveCW Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs
        [⟨krAh Fc ks m n A z ((ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
          (A.getD 0 (MO Fc ks m).zero))).getD 0), z, (ratValC Fc ks m ((MO Fc ks m).mul
          (powC (MO Fc ks m) z n) (A.getD 0 (MO Fc ks m).zero))).getD 0, W0, cols0⟩] =
        some (some w)) := by
  unfold kzDecideCW at h
  dsimp only at h
  generalize hb1 : (decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) = b1 at h
  cases b1
  · simp at h
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
  generalize hb3 : kzOK Fc ks m M A B kt l cs dC = b3 at h
  generalize kzConst Fc ks m n j M g A B kt l cs = b4 at h
  generalize kzFieldOK Fc ks m n j M g A B kt l cs zN gs = b5 at h
  generalize ((List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)).map
    (kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs) = tors at h
  by_cases hcs : cs.length = 0
  · rw [if_pos hcs] at h; simp at h
  rw [if_neg hcs] at h
  cases b3
  · simp at h
  cases b4
  · simp at h
  cases b5
  · simp at h
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
  refine ⟨rfl, rfl, ?_⟩
  by_cases hn : tors.any (· == none) = true
  · rw [if_pos hn] at h; simp at h
  rw [if_neg hn] at h
  generalize (!tors.any (· == some none)) = allT at h
  rcases hz : krZ Fc ks lv m n A with _ | z
  · simp only [hz] at h
    cases allT
    · rw [if_neg Bool.false_ne_true] at h
      split_ifs at h <;> simp at h
    · rw [if_pos rfl] at h; exact Or.inl h
  · simp only [hz] at h
    by_cases hκ : (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
        (A.getD 0 (MO Fc ks m).zero))).getD 0 = 0
    · rw [if_pos hκ] at h; simp at h
    rw [if_neg hκ] at h
    set κ := (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
        (A.getD 0 (MO Fc ks m).zero))).getD 0 with hκd
    rcases ht : kyTorsPsiC Fc ks m n M A zN z κ cpf ps bound rs with _ | _ | N0
    · simp [ht] at h
    · simp only [ht] at h
      cases allT
      · rw [if_neg Bool.false_ne_true] at h
        split_ifs at h <;> simp at h
      · rw [if_pos rfl] at h; exact Or.inl h
    · simp only [ht] at h
      cases allT
      · rw [if_neg Bool.false_ne_true] at h
        split_ifs at h <;> simp at h
      · rw [if_pos rfl] at h
        rcases hw : kyWitPsi Fc ks m n M A zN z κ N0 with _ | W0
        · simp [hw] at h
        · simp only [hw] at h
          rcases hc : kyColM Fc ks m n M (krAh Fc ks m n A z κ) z j W0 with _ | cols0
          · simp [hc] at h
          · simp only [hc] at h
            exact Or.inr ⟨z, W0, cols0, rfl, hκ, hc, h⟩

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **A valid KZ antiderivative**: a solution with `q₀ ≠ 0`; every group's columns are those of
`kyColM` for a twist `Â = (zⁿ/κ) θⁿ` (so `ky_root_logs` applies to each). -/
def KZW.Valid (lv : (m : ℕ) → LC m) (m n j : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m)) (θ : L) (w : KYW Fc M m) : Prop :=
  w.1 ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)
    (((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) :: w.2.flatMap (·.cols)) ∧
  w.1.1.getD 0 0 ≠ 0 ∧
  ∀ g ∈ w.2, kyColM Fc ks m n M g.Ah g.z j g.W = some g.cols ∧ g.κ ≠ 0 ∧ T.ev m g.z ≠ 0 ∧
    T.ev (m + 1) (pcP Fc ks m g.Ah) = T.ev m g.z ^ n * ((g.κ⁻¹ : ℚ) : L) * θ ^ n

lemma kzSolveCW_valid (m n j : ℕ) (hTr : T.Tr (m + 1)) (g : LC m) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (θ : L) (hθ : θ ^ n = T.evP m A) (extra : List (KYGrp Fc M m))
    (hextra : ∀ g ∈ extra, kyColM Fc ks m n M g.Ah g.z j g.W = some g.cols ∧ g.κ ≠ 0 ∧
      T.ev m g.z ≠ 0 ∧ T.ev (m + 1) (pcP Fc ks m g.Ah) = T.ev m g.z ^ n * ((g.κ⁻¹ : ℚ) : L) * θ ^ n)
    (w : KYW Fc M m)
    (hw : kzSolveCW Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs extra = some (some w)) :
    KZW.Valid T lv m n j M A B kt l cs dC θ w := by
  have hTm : T.Tr m := hTr.of_succ
  unfold kzSolveCW at hw
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
  rcases List.mem_append.mp hg with hg | hg
  · exact hextra gr hg
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

/-- **Every antiderivative returned by `kzDecideCW` is valid** (the columns then by
`ky_root_logs`). -/
theorem kzDecideCW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (n j : ℕ) (g : LC m) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A : GPoly (LC m))
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true) (hdegpos : 0 < degG (MO Fc ks m) A)
    (hcop : Nat.Coprime n (degG (MO Fc ks m) A)) (θ : L) (hθ : θ ^ n = T.evP m A)
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (w : KYW Fc M m)
    (hdec : kzDecideCW Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs = some (some w)) :
    KZW.Valid T lv m n j M A B kt l cs dC θ w := by
  obtain ⟨hTr, hsq, hdegA, hcopA, hM, hspecA, hA0⟩ :=
    T.kr_setup (lv := lv) hmon hdeg m hn hc n j A hsqc hdegpos hcop
  have hTm : T.Tr m := hTr.of_succ
  obtain ⟨hchk, hok, hsrc⟩ := kzDecideCW_src Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs w hdec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  have hn0 : 0 < n := by omega
  rcases hsrc with h0 | ⟨z, W0, cols0, hz, hκ0, hcol, h1⟩
  · exact T.kzSolveCW_valid m n j hTr g M zN gs A B kt l cs dC cpf ps bound rs θ hθ []
      (fun g hg ↦ absurd hg (by simp)) w h0
  · refine T.kzSolveCW_valid m n j hTr g M zN gs A B kt l cs dC cpf ps bound rs θ hθ _ ?_ w h1
    intro gr hgr
    simp only [List.mem_singleton] at hgr
    subst hgr
    have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
      simp only [kzOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hok
      exact hok.1.1
    obtain ⟨hz0, -⟩ := T.kr_zsem hmon hdeg m n hn0 hn hc hTm A ha0 z hz
    refine ⟨hcol, hκ0, fun h ↦ hz0 (Subtype.ext (by rw [T.sem_MP m hTm]; exact h)), ?_⟩
    rw [← T.sem_MP (m + 1) hTr, T.coe_Av m n hTr A z, hθ]

end MTower

end Curves.MT
