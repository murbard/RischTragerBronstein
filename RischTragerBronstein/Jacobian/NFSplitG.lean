import RischTragerBronstein.Algebraic.NFSplit

/-!
# Splitting fields for an arbitrary curve polynomial

`NFC.splitField` / `sqLoop` with the cubic `p` replaced by any `P ∈ ℚ[x]` (`pValG P α = P(α)`):
`splitFieldG P D` is a number field in which `D` splits and `P` is a non-zero square at every root
of `D` (`splitFieldG_spec`, for `D` squarefree and coprime to `P`).
-/

open Polynomial CPoly

namespace NFC

/-- `P(α)`. -/
noncomputable def pValG {K : Type*} [Field K] [CharZero K] (P : CPoly ℚ) (α : K) : K :=
  aeval α (toPoly P)

lemma map_pValG {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L] (φ : K →+* L)
    (P : CPoly ℚ) (α : K) : φ (pValG P α) = pValG P (φ α) :=
  aeval_ringHom_rat φ α (toPoly P)

/-- `D` has `k` distinct roots `α` in `ℚ[x]/(M)` at which `p(α)` is a square. -/
def SqRootsG (M : CPoly ℚ) (hM : Kron.irredQ M = true) (P : CPoly ℚ) (D : CPoly ℚ) (k : ℕ) : Prop :=
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  ∃ l : List (NF M), l.Nodup ∧ k ≤ l.length ∧
    ∀ α ∈ l, aeval α (toPoly D) = 0 ∧ ∃ β : NF M, β * β = pValG P α

/-- **The square-root loop**: adjoin `√p(α)` until `p` is a square at every root of `D`. -/
noncomputable def sqLoopG (P : CPoly ℚ) (D : CPoly ℚ) : ℕ → (M : CPoly ℚ) → Kron.irredQ M = true →
    Option (Σ' M : CPoly ℚ, Kron.irredQ M = true)
  | 0, _, _ => none
  | n + 1, M, hM =>
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    match rootsIn M (EllQuad.liftK (K := NF M) D) with
    | none => none
    | some rs =>
      match rs.dedup.find? (fun α ↦ (EllQuad.sqrtNF M (pValG P α)).isNone) with
      | none => some ⟨M, hM⟩
      | some α0 =>
        match extStep M (EllQuad.sqPoly M (pValG P α0)) with
        | some ⟨M', hM'⟩ => sqLoopG P D n M' hM'
        | none => none

set_option maxHeartbeats 3200000 in
/-- **The loop ends with a field in which `p` is a non-zero square at every root of `D`.** -/
theorem sqLoopG_spec (P : CPoly ℚ) (D : CPoly ℚ) (hDsq : Squarefree (toPoly D))
    (hcop : IsCoprime (toPoly D) (toPoly P)) :
    ∀ (n : ℕ) (M : CPoly ℚ) (hM : Kron.irredQ M = true) (k : ℕ),
      HasRoots M hM D (toPoly D).natDegree → SqRootsG M hM P D k →
      (toPoly D).natDegree < n + k →
      ∃ M' hM', sqLoopG P D n M hM = some ⟨M', hM'⟩ ∧ HasRoots M' hM' D (toPoly D).natDegree ∧
        (letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
        ∀ α : NF M', aeval α (toPoly D) = 0 → ∃ β : NF M', β ≠ 0 ∧ β * β = pValG P α)
  | 0, M, hM, k, _, hk, hn => by
    exfalso
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    obtain ⟨l, hl, hlen, hr⟩ := hk
    have := length_le_natDegree ((Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective).mpr
      hDsq.ne_zero) hl (fun a ha ↦ by rw [eval_map_algebraMap]; exact (hr a ha).1)
    rw [natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective] at this
    omega
  | n + 1, M, hM, k, hsplit, hk, hn => by
    classical
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    -- `p` does not vanish at the roots of `D`
    have hpne : ∀ α : NF M, aeval α (toPoly D) = 0 → pValG P α ≠ 0 := by
      intro α hα hp
      have := aeval_ne_zero_of_isCoprime hcop α
      apply this.elim (fun h ↦ h hα)
      intro h; apply h
      simpa [pValG] using hp
    have hgL : toPoly (EllQuad.liftK (K := NF M) D) = (toPoly D).map (algebraMap ℚ (NF M)) :=
      EllQuad.toPoly_liftK D
    have hgsq : Squarefree (toPoly (EllQuad.liftK (K := NF M) D)) := by
      rw [hgL]; exact ((PerfectField.separable_iff_squarefree).mpr hDsq).map.squarefree
    obtain ⟨rs, hrs, hall⟩ := rootsIn_complete M _ hgsq
    have hsound := rootsIn_sound M _ hrs
    have hrootiff : ∀ α : NF M, aeval α (toPoly D) = 0 ↔ α ∈ rs.dedup := by
      intro α; rw [List.mem_dedup]
      constructor
      · intro h; exact hall α (by rw [hgL, eval_map_algebraMap]; exact h)
      · intro h; have := hsound α h; rwa [hgL, eval_map_algebraMap] at this
    cases hfind : rs.dedup.find? (fun α ↦ (EllQuad.sqrtNF M (pValG P α)).isNone) with
    | none =>
      refine ⟨M, hM, ?_, hsplit, ?_⟩
      · simp only [sqLoopG]; rw [hrs]; simp only; rw [hfind]
      · intro α hα
        have hmem := (hrootiff α).mp hα
        have := List.find?_eq_none.mp hfind α hmem
        simp only [Option.isNone_iff_eq_none, Bool.not_eq_true, decide_eq_false_iff_not] at this
        obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp (by simpa using this)
        refine ⟨β, fun h0 ↦ hpne α hα ?_, EllQuad.sqrtNF_spec M hβ⟩
        rw [← EllQuad.sqrtNF_spec M hβ, h0, zero_mul]
    | some α0 =>
      have hα0mem : α0 ∈ rs.dedup := List.mem_of_find?_eq_some hfind
      have hα0none : EllQuad.sqrtNF M (pValG P α0) = none := by
        have := List.find?_some hfind; simpa using this
      have hα0root : aeval α0 (toPoly D) = 0 := (hrootiff α0).mpr hα0mem
      have hw0 : pValG P α0 ≠ 0 := hpne α0 hα0root
      have hnotsq : ∀ β : NF M, β * β ≠ pValG P α0 := fun β hβ ↦
        EllQuad.sqrtNF_ne_none M hβ hw0 hα0none
      have hsqp : Squarefree (toPoly (EllQuad.sqPoly M (pValG P α0))) :=
        EllQuad.sqPoly_squarefree M hw0
      have hsqe : toPoly (EllQuad.sqPoly M (pValG P α0)) = X ^ 2 - C (pValG P α0) := by
        simp [EllQuad.sqPoly, CPoly.toPoly]; ring
      obtain ⟨M', hM', hext, θ', hθ', α', hα'⟩ := extStep_spec M _ hsqp
        (by rw [hsqe, natDegree_sub_C, natDegree_X_pow]; norm_num)
      letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
      set e := emb M M' hθ'
      rw [hsqe, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X,
        eval_C, sub_eq_zero, map_pValG] at hα'
      have heroot : ∀ α : NF M, aeval α (toPoly D) = 0 → aeval (e α) (toPoly D) = 0 := by
        intro α hα; rw [← aeval_ringHom_rat e α, hα, map_zero]
      -- the new field
      have hsplit' : HasRoots M' hM' D (toPoly D).natDegree := by
        obtain ⟨l, hl, hlen, hr⟩ := hsplit
        exact ⟨l.map e, hl.map e.injective, by simpa using hlen, fun α hα ↦ by
          obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp hα; exact heroot β (hr β hβ)⟩
      have hk' : SqRootsG M' hM' P D (k + 1) := by
        obtain ⟨l, hl, hlen, hr⟩ := hk
        have hα0l : α0 ∉ l := fun h ↦ by
          obtain ⟨β, hβ⟩ := (hr α0 h).2; exact hnotsq β hβ
        refine ⟨(α0 :: l).map e, (List.nodup_cons.mpr ⟨hα0l, hl⟩).map e.injective,
          by simp; omega, ?_⟩
        intro α hα
        obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hα
        rcases List.mem_cons.mp hγ with rfl | hγ
        · exact ⟨heroot _ hα0root, α', by rw [← sq]; exact hα'⟩
        · obtain ⟨hr1, β, hβ⟩ := hr γ hγ
          exact ⟨heroot _ hr1, e β, by rw [← map_mul, hβ, map_pValG]⟩
      obtain ⟨M'', hM'', hloop, hfin, hsq⟩ :=
        sqLoopG_spec P D hDsq hcop n M' hM' (k + 1) hsplit' hk' (by omega)
      refine ⟨M'', hM'', ?_, hfin, hsq⟩
      simp only [sqLoopG]
      rw [hrs]
      simp only
      rw [hfind]
      simp only
      rw [hext]
      exact hloop

/-- **The field for `D` and `p`**: `D` splits, and `p` is a non-zero square at its roots. -/
noncomputable def splitFieldG (P : CPoly ℚ) (D : CPoly ℚ) : Option (Σ' M : CPoly ℚ, Kron.irredQ M = true) :=
  match splitLoop D (Kron.degC D + 1) [0, 1] irredQ_X with
  | some ⟨M, hM⟩ => sqLoopG P D (Kron.degC D + 1) M hM
  | none => none

theorem splitFieldG_spec (P : CPoly ℚ) (D : CPoly ℚ) (hDsq : Squarefree (toPoly D))
    (hcop : IsCoprime (toPoly D) (toPoly P)) :
    ∃ M hM, splitFieldG P D = some ⟨M, hM⟩ ∧ HasRoots M hM D (toPoly D).natDegree ∧
      (letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∀ α : NF M, aeval α (toPoly D) = 0 → ∃ β : NF M, β ≠ 0 ∧ β * β = pValG P α) := by
  have hdeg : Kron.degC D = (toPoly D).natDegree := Kron.degC_eq D hDsq.ne_zero
  have h0 : HasRoots [0, 1] irredQ_X D 0 := ⟨[], List.nodup_nil, le_rfl, by simp⟩
  obtain ⟨M, hM, hloop, hsplit⟩ := splitLoop_spec D hDsq (Kron.degC D + 1) [0, 1] irredQ_X 0 h0
    (by rw [hdeg]; omega)
  have hsq0 : SqRootsG M hM P D 0 := ⟨[], List.nodup_nil, le_rfl, by simp⟩
  obtain ⟨M', hM', hsq, hsplit', hfin⟩ := sqLoopG_spec P D hDsq hcop (Kron.degC D + 1) M hM 0
    hsplit hsq0 (by rw [hdeg]; omega)
  refine ⟨M', hM', ?_, hsplit', hfin⟩
  unfold splitFieldG
  rw [hloop]
  exact hsq

end NFC
