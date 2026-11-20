import RischTragerBronstein.Computable.MixN

/-!
# The elimination behind `hermKernelCert`

`(L.foldl kerStep ([], [])).2 = ws`: every rational relation `∑ cⱼ Pⱼ = 0` among the first
components gives `∑ cⱼ ρⱼ = ∑ βₖ wₖ` for some rational `β`, with `β = 0` only for the trivial
relation (`kerElim_spec`).
-/

open Polynomial CPoly

namespace Tower.MixN

lemma lcomb_append (cs : List ℚ) (vs : List (CPoly ℚ)) (c : ℚ) (v : CPoly ℚ)
    (h : cs.length = vs.length) :
    lcomb (cs ++ [c]) (vs ++ [v]) = lcomb cs vs + C c * toPoly v := by
  rw [lcomb, lcomb, List.zipWith_append h]
  simp

lemma lcomb_add : ∀ (α a : List ℚ) (vs : List (CPoly ℚ)), α.length = a.length →
    lcomb (List.zipWith (· + ·) α a) vs = lcomb α vs + lcomb a vs
  | [], [], vs, _ => by simp [lcomb]
  | x :: α, y :: a, [], _ => by simp [lcomb]
  | x :: α, y :: a, v :: vs, h => by
    have ih := lcomb_add α a vs (by simpa using h)
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, C_add]
    ring

lemma lcomb_mapMul (c : ℚ) : ∀ (a : List ℚ) (vs : List (CPoly ℚ)),
    lcomb (a.map (c * ·)) vs = C c * lcomb a vs
  | [], vs => by simp [lcomb]
  | x :: a, [] => by simp [lcomb]
  | x :: a, v :: vs => by
    have ih := lcomb_mapMul c a vs
    simp only [lcomb, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, C_mul]
    ring

lemma lcomb_of_zero : ∀ (α : List ℚ) (vs : List (CPoly ℚ)), (∀ a ∈ α, a = 0) → lcomb α vs = 0
  | [], vs, _ => by simp [lcomb]
  | x :: α, [], _ => by simp [lcomb]
  | x :: α, v :: vs, h => by
    have ih := lcomb_of_zero α vs fun a ha ↦ h a (List.mem_cons_of_mem _ ha)
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, h x List.mem_cons_self]
    simp

lemma toPoly_lcombC : ∀ (a : List ℚ) (ps : List (CPoly ℚ)), toPoly (lcombC a ps) = lcomb a ps
  | [], ps => by simp [lcombC, lcomb]
  | x :: a, [] => by simp [lcombC, lcomb]
  | x :: a, p :: ps => by
    have ih := toPoly_lcombC a ps
    simp only [lcombC, lcomb, List.zipWith_cons_cons, List.foldr_cons, List.sum_cons] at ih ⊢
    rw [toPoly_add, toPoly_smul, ih]

lemma lcombS_id' (cs : List ℚ) (vs : List (CPoly ℚ)) :
    lcombS (RingHom.id ℚ) cs vs = lcomb cs vs := by
  simp [lcombS, lcomb]

/-- The invariant of the elimination. -/
def KerInv (L : List (CPoly ℚ × CPoly ℚ)) (st : List (CPoly ℚ × CPoly ℚ) × List (CPoly ℚ)) :
    Prop :=
  (∀ α : List ℚ, α.length = st.1.length → lcomb α (st.1.map Prod.fst) = 0 → ∀ a ∈ α, a = 0) ∧
  ∀ cs : List ℚ, cs.length = L.length → ∃ α β : List ℚ, α.length = st.1.length ∧
    β.length = st.2.length ∧ lcomb cs (L.map Prod.fst) = lcomb α (st.1.map Prod.fst) ∧
    lcomb cs (L.map Prod.snd) = lcomb α (st.1.map Prod.snd) + lcomb β st.2 ∧
    ((∀ a ∈ α, a = 0) → (∀ b ∈ β, b = 0) → ∀ c ∈ cs, c = 0)

lemma kerInv_nil : KerInv [] ([], []) := by
  refine ⟨fun α hα _ a ha ↦ ?_, fun cs hcs ↦ ⟨[], [], rfl, rfl, ?_, ?_, fun _ _ c hc ↦ ?_⟩⟩
  · simp at hα; subst hα; simp at ha
  · simp at hcs; subst hcs; simp [lcomb]
  · simp at hcs; subst hcs; simp [lcomb]
  · simp at hcs; subst hcs; simp at hc

lemma kerInv_step (L : List (CPoly ℚ × CPoly ℚ)) (st : List (CPoly ℚ × CPoly ℚ) × List (CPoly ℚ))
    (x : CPoly ℚ × CPoly ℚ) (h : KerInv L st) : KerInv (L ++ [x]) (kerStep st x) := by
  obtain ⟨hind, hrel⟩ := h
  unfold kerStep
  cases hls : linSolve (st.1.map Prod.fst) x.1 with
  | none =>
    simp only
    refine ⟨fun α hα h0 a ha ↦ ?_, fun cs hcs ↦ ?_⟩
    · -- the new vector is independent of the kept ones
      simp only [List.length_append, List.length_singleton] at hα
      obtain ⟨α₀, c, rfl⟩ : ∃ α₀ c, α = α₀ ++ [c] := by
        rcases List.eq_nil_or_concat α with h | ⟨α₀, c, h⟩
        · subst h; simp at hα
        · exact ⟨α₀, c, by rw [h, List.concat_eq_append]⟩
      have hl₀ : α₀.length = st.1.length := by simpa using hα
      rw [List.map_append, List.map_singleton, lcomb_append _ _ _ _ (by simpa using hl₀)] at h0
      have hc : c = 0 := by
        by_contra hc
        refine absurd hls (linSolve_complete_map (RingHom.id ℚ) _ _ (α₀.map (-c⁻¹ * ·))
          (by simpa using hl₀) ?_)
        rw [lcombS_id', lcomb_mapMul, Polynomial.map_id]
        have : lcomb α₀ (st.1.map Prod.fst) = -(C c * toPoly x.1) := by linear_combination h0
        rw [this, mul_neg, ← mul_assoc, ← C_mul, neg_mul, inv_mul_cancel₀ hc, C_neg, C_1,
          neg_mul, one_mul, neg_neg]
      subst hc
      rw [C_0, zero_mul, add_zero] at h0
      rcases List.mem_append.mp ha with ha | ha
      · exact hind α₀ hl₀ h0 a ha
      · simpa using ha
    · obtain ⟨cs₀, c, rfl⟩ : ∃ cs₀ c, cs = cs₀ ++ [c] := by
        rcases List.eq_nil_or_concat cs with h | ⟨cs₀, c, h⟩
        · subst h; simp at hcs
        · exact ⟨cs₀, c, by rw [h, List.concat_eq_append]⟩
      have hl₀ : cs₀.length = L.length := by simpa using hcs
      obtain ⟨α, β, hα, hβ, h1, h2, h3⟩ := hrel cs₀ hl₀
      refine ⟨α ++ [c], β, by simp [hα], hβ, ?_, ?_, fun hα0 hβ0 c' hc' ↦ ?_⟩
      · simp only [List.map_append, List.map_singleton]
        rw [lcomb_append _ _ _ _ (by simpa using hl₀), lcomb_append _ _ _ _ (by simpa using hα), h1]
      · simp only [List.map_append, List.map_singleton]
        rw [lcomb_append _ _ _ _ (by simpa using hl₀), lcomb_append _ _ _ _ (by simpa using hα), h2]
        ring
      · rcases List.mem_append.mp hc' with hc' | hc'
        · exact h3 (fun a ha ↦ hα0 a (List.mem_append_left _ ha)) hβ0 c' hc'
        · have := hα0 c (List.mem_append_right _ List.mem_cons_self)
          simp at hc'; rw [hc']; exact this
  | some a =>
    obtain ⟨hla, hsol⟩ := linSolve_sound _ _ a hls
    have hla' : a.length = st.1.length := by simpa using hla
    simp only
    refine ⟨hind, fun cs hcs ↦ ?_⟩
    obtain ⟨cs₀, c, rfl⟩ : ∃ cs₀ c, cs = cs₀ ++ [c] := by
      rcases List.eq_nil_or_concat cs with h | ⟨cs₀, c, h⟩
      · subst h; simp at hcs
      · exact ⟨cs₀, c, by rw [h, List.concat_eq_append]⟩
    have hl₀ : cs₀.length = L.length := by simpa using hcs
    obtain ⟨α, β, hα, hβ, h1, h2, h3⟩ := hrel cs₀ hl₀
    refine ⟨List.zipWith (· + ·) α (a.map (c * ·)), β ++ [c], by simp [hα, hla'],
      by simp [hβ], ?_, ?_, fun hα0 hβ0 c' hc' ↦ ?_⟩
    · simp only [List.map_append, List.map_singleton]
      rw [lcomb_append _ _ _ _ (by simpa using hl₀), h1,
        lcomb_add _ _ _ (by simp [hα, hla']), lcomb_mapMul, hsol]
    · simp only [List.map_append, List.map_singleton]
      rw [lcomb_append _ _ _ _ (by simpa using hl₀), h2,
        lcomb_append _ _ _ _ hβ, lcomb_add _ _ _ (by simp [hα, hla']), lcomb_mapMul, toPoly_sub,
        toPoly_lcombC]
      ring
    · have hc : c = 0 := hβ0 c (List.mem_append_right _ List.mem_cons_self)
      subst hc
      have hα0' : ∀ x ∈ α, x = 0 := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        have hmem : (List.zipWith (· + ·) α (a.map (0 * ·)))[i]'(by simp [hα, hla']; omega) ∈
            List.zipWith (· + ·) α (a.map (0 * ·)) := List.getElem_mem _
        have := hα0 _ hmem
        simpa using this
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact h3 hα0' (fun b hb ↦ hβ0 b (List.mem_append_left _ hb)) c' hc'
      · simpa using hc'

lemma kerInv_foldl : ∀ (L : List (CPoly ℚ × CPoly ℚ)), KerInv L (L.foldl kerStep ([], [])) := by
  intro L
  induction L using List.reverseRecOn with
  | nil => exact kerInv_nil
  | append_singleton L x ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact kerInv_step L _ x ih

/-- **The elimination**: a relation among the first components gives the second components as a
combination of the recorded residue combinations, non-trivially. -/
theorem kerElim_spec (L : List (CPoly ℚ × CPoly ℚ)) (cs : List ℚ) (hcs : cs.length = L.length)
    (h0 : lcomb cs (L.map Prod.fst) = 0) :
    ∃ β : List ℚ, β.length = (L.foldl kerStep ([], [])).2.length ∧
      lcomb cs (L.map Prod.snd) = lcomb β (L.foldl kerStep ([], [])).2 ∧
      ((∀ b ∈ β, b = 0) → ∀ c ∈ cs, c = 0) := by
  obtain ⟨hind, hrel⟩ := kerInv_foldl L
  obtain ⟨α, β, hα, hβ, h1, h2, h3⟩ := hrel cs hcs
  have hα0 := hind α hα (by rw [← h1, h0])
  refine ⟨β, hβ, ?_, h3 hα0⟩
  rw [h2, lcomb_of_zero α _ hα0, zero_add]

end Tower.MixN
