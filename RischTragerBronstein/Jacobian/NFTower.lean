import RischTragerBronstein.Jacobian.NFSplitG

/-!
# Towers of splitting fields

The loops `splitLoop` and `sqLoopG` extend their input field: `splitLoop_emb`, `sqLoopG_emb`
give an embedding of the input field into the output field. Roots and square roots transport
along embeddings (`HasRoots.map`, `sqFacts_map`), so loops can be chained.
-/

open Polynomial CPoly

namespace NFC

/-- **`splitLoop` extends its input field.** -/
theorem splitLoop_emb (D : CPoly ℚ) (hDsq : Squarefree (toPoly D)) :
    ∀ (n : ℕ) (M : CPoly ℚ) (hM : Kron.irredQ M = true) (M' : CPoly ℚ)
      (hM' : Kron.irredQ M' = true), splitLoop D n M hM = some ⟨M', hM'⟩ →
      (letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
      Nonempty (NF M →+* NF M'))
  | 0, M, hM, M', hM', h => by simp [splitLoop] at h
  | n + 1, M, hM, M', hM', h => by
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    have hgL : toPoly (EllQuad.liftK (K := NF M) D) = (toPoly D).map (algebraMap ℚ (NF M)) :=
      EllQuad.toPoly_liftK D
    have hgsq : Squarefree (toPoly (EllQuad.liftK (K := NF M) D)) := by
      rw [hgL]; exact ((PerfectField.separable_iff_squarefree).mpr hDsq).map.squarefree
    obtain ⟨rs, hrs, -⟩ := rootsIn_complete M _ hgsq
    have hsound := rootsIn_sound M _ hrs
    have hD0 : (toPoly D).map (algebraMap ℚ (NF M)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective).mpr hDsq.ne_zero
    have hdegM : ((toPoly D).map (algebraMap ℚ (NF M))).natDegree = (toPoly D).natDegree :=
      natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective _
    have hle : rs.dedup.length ≤ (toPoly D).natDegree := by
      rw [← hdegM]
      exact length_le_natDegree hD0 (List.nodup_dedup rs) (fun a ha ↦ by
        rw [← hgL]; exact hsound a (List.mem_dedup.mp ha))
    have hdegC : Kron.degC D = (toPoly D).natDegree := Kron.degC_eq D hDsq.ne_zero
    simp only [splitLoop] at h
    rw [hrs] at h
    simp only at h
    split_ifs at h with heq
    · simp only [Option.some.injEq, PSigma.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨RingHom.id _⟩
    · split at h
      · rename_i M1 hM1 hgrow
        have hlt : rs.dedup.length < (toPoly D).natDegree :=
          lt_of_le_of_ne hle (by rwa [hdegC] at heq)
        obtain ⟨M2, hM2, hgrow2, -, θ', hθ'⟩ := growStep_spec M D hDsq rs hrs hlt
        rw [hgrow] at hgrow2
        simp only [Option.some.injEq, PSigma.mk.injEq] at hgrow2
        obtain ⟨rfl, -⟩ := hgrow2
        letI : Fact (Irreducible (toPoly M1)) := ⟨Kron.irredQ_sound M1 hM1⟩
        obtain ⟨φ⟩ := splitLoop_emb D hDsq n M1 hM1 M' hM' h
        exact ⟨φ.comp (emb M M1 hθ')⟩
      · cases h

/-- **`sqLoopG` extends its input field.** -/
theorem sqLoopG_emb (P D : CPoly ℚ) (hcop : IsCoprime (toPoly D) (toPoly P))
    (hDsq : Squarefree (toPoly D)) :
    ∀ (n : ℕ) (M : CPoly ℚ) (hM : Kron.irredQ M = true) (M' : CPoly ℚ)
      (hM' : Kron.irredQ M' = true), sqLoopG P D n M hM = some ⟨M', hM'⟩ →
      (letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
      Nonempty (NF M →+* NF M'))
  | 0, M, hM, M', hM', h => by simp [sqLoopG] at h
  | n + 1, M, hM, M', hM', h => by
    classical
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    have hgL : toPoly (EllQuad.liftK (K := NF M) D) = (toPoly D).map (algebraMap ℚ (NF M)) :=
      EllQuad.toPoly_liftK D
    have hgsq : Squarefree (toPoly (EllQuad.liftK (K := NF M) D)) := by
      rw [hgL]; exact ((PerfectField.separable_iff_squarefree).mpr hDsq).map.squarefree
    obtain ⟨rs, hrs, -⟩ := rootsIn_complete M _ hgsq
    have hsound := rootsIn_sound M _ hrs
    simp only [sqLoopG] at h
    rw [hrs] at h
    simp only at h
    split at h
    · simp only [Option.some.injEq, PSigma.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨RingHom.id _⟩
    · rename_i α0 hfind
      split at h
      · rename_i M1 hM1 hext
        have hα0mem : α0 ∈ rs.dedup := List.mem_of_find?_eq_some hfind
        have hα0root : aeval α0 (toPoly D) = 0 := by
          have := hsound α0 (List.mem_dedup.mp hα0mem); rwa [hgL, eval_map_algebraMap] at this
        have hw0 : pValG P α0 ≠ 0 := by
          intro hp
          have := aeval_ne_zero_of_isCoprime hcop α0
          apply this.elim (fun h ↦ h hα0root)
          intro h; apply h
          simpa [pValG] using hp
        have hsqp : Squarefree (toPoly (EllQuad.sqPoly M (pValG P α0))) :=
          EllQuad.sqPoly_squarefree M hw0
        have hsqe : toPoly (EllQuad.sqPoly M (pValG P α0)) = X ^ 2 - C (pValG P α0) := by
          simp [EllQuad.sqPoly, CPoly.toPoly]; ring
        obtain ⟨M2, hM2, hext2, θ', hθ', -⟩ := extStep_spec M _ hsqp
          (by rw [hsqe, natDegree_sub_C, natDegree_X_pow]; norm_num)
        rw [hext] at hext2
        simp only [Option.some.injEq, PSigma.mk.injEq] at hext2
        obtain ⟨rfl, -⟩ := hext2
        letI : Fact (Irreducible (toPoly M1)) := ⟨Kron.irredQ_sound M1 hM1⟩
        obtain ⟨φ⟩ := sqLoopG_emb P D hcop hDsq n M1 hM1 M' hM' h
        exact ⟨φ.comp (emb M M1 hθ')⟩
      · cases h

section Transport

variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

/-- Distinct roots transport along an embedding. -/
lemma roots_map (φ : K →+* L) {D : ℚ[X]} {l : List K} (hl : l.Nodup)
    (hr : ∀ a ∈ l, aeval a D = 0) : (l.map φ).Nodup ∧ ∀ a ∈ l.map φ, aeval a D = 0 :=
  ⟨hl.map φ.injective, fun a ha ↦ by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [← aeval_ringHom_rat φ b, hr b hb, map_zero]⟩

/-- If `D` has `deg D` distinct roots `l` in `K`, every root of `D` in `L` is the image of one. -/
lemma root_mem_map (φ : K →+* L) {D : ℚ[X]} (hD0 : D ≠ 0) {l : List K} (hl : l.Nodup)
    (hlen : D.natDegree ≤ l.length) (hr : ∀ a ∈ l, aeval a D = 0) {β : L}
    (hβ : aeval β D = 0) : β ∈ l.map φ := by
  classical
  by_contra hβl
  obtain ⟨hl', hr'⟩ := roots_map φ hl hr
  have hlen' := length_le_natDegree ((Polynomial.map_ne_zero_iff (algebraMap ℚ L).injective).mpr
    hD0) (l := β :: l.map φ) (List.nodup_cons.mpr ⟨hβl, hl'⟩) (fun a ha ↦ by
      rw [eval_map_algebraMap]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hβ
      · exact hr' a ha)
  rw [natDegree_map_eq_of_injective (algebraMap ℚ L).injective] at hlen'
  simp at hlen'
  omega

/-- Square roots at the roots of a split `D` transport along an embedding. -/
lemma sqFacts_map (φ : K →+* L) (P : CPoly ℚ) {D : ℚ[X]} (hD0 : D ≠ 0) {l : List K}
    (hl : l.Nodup) (hlen : D.natDegree ≤ l.length) (hr : ∀ a ∈ l, aeval a D = 0)
    (hsq : ∀ α : K, aeval α D = 0 → ∃ β : K, β ≠ 0 ∧ β * β = pValG P α) :
    ∀ α : L, aeval α D = 0 → ∃ β : L, β ≠ 0 ∧ β * β = pValG P α := by
  intro α hα
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (root_mem_map φ hD0 hl hlen hr hα)
  obtain ⟨β, hβ0, hβ⟩ := hsq a (hr a ha)
  exact ⟨φ β, (map_ne_zero_iff φ φ.injective).mpr hβ0, by rw [← map_mul, hβ, map_pValG]⟩

end Transport

end NFC
