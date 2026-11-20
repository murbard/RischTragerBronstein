import RischTragerBronstein.Computable.LinSolve

/-!
# Null spaces over the constants, complete over every extension

`nullBasis vs`: a basis of `{c : ∑ cⱼ vⱼ = 0}` (vectors `vⱼ` as coefficient lists), as coefficient
lists `w` (the relation `∑ⱼ w[j] vⱼ = 0`).

* `nullBasis_sound`: every basis vector is a relation;
* `nullBasis_complete`: every relation with coefficients in **any** extension field `S ⊇ R` is an
  `S`-combination of the basis vectors.

The elimination keeps the independent vectors `(Pᵢ, ρᵢ)` (`ρᵢ` records the combination of the
input vectors giving `Pᵢ`); a dependent vector `P = ∑ aᵢ Pᵢ` records the relation `ρ - ∑ aᵢ ρᵢ`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R S : Type*} [Field R] [DecidableEq R] [Field S] (ι : R →+* S)

/-- `∑ aᵢ pᵢ` as a coefficient list. -/
def lcombL (a : List R) (ps : List (CPoly R)) : CPoly R :=
  (List.zipWith (fun c p ↦ smul c p) a ps).foldr add []

/-- One elimination step. -/
def nsStep (st : List (CPoly R × CPoly R) × List (CPoly R)) (x : CPoly R × CPoly R) :
    List (CPoly R × CPoly R) × List (CPoly R) :=
  match linSolve (st.1.map Prod.fst) x.1 with
  | none => (st.1 ++ [x], st.2)
  | some a => (st.1, st.2 ++ [sub x.2 (lcombL a (st.1.map Prod.snd))])

/-- The unit coefficient list `Xʲ`. -/
def unitL (j : ℕ) : CPoly R := List.replicate j 0 ++ [1]

/-- The items `(vⱼ, Xʲ)`. -/
def nsItems (vs : List (CPoly R)) : List (CPoly R × CPoly R) :=
  (List.range vs.length).map fun j ↦ (vs.getD j [], unitL j)

/-- **A basis of the relations** among `vs`. -/
def nullBasis (vs : List (CPoly R)) : List (CPoly R) :=
  ((nsItems vs).foldl nsStep ([], [])).2

lemma toPoly_lcombL : ∀ (a : List R) (ps : List (CPoly R)), toPoly (lcombL a ps) = lcomb a ps
  | [], ps => by simp [lcombL, lcomb]
  | x :: a, [] => by simp [lcombL, lcomb]
  | x :: a, p :: ps => by
    have ih := toPoly_lcombL a ps
    simp only [lcombL, lcomb, List.zipWith_cons_cons, List.foldr_cons, List.sum_cons] at ih ⊢
    rw [toPoly_add, toPoly_smul, ih]

/-! ### Algebra of `lcombS` -/

lemma lcombS_append (cs : List S) (vs : List (CPoly R)) (c : S) (v : CPoly R)
    (h : cs.length = vs.length) :
    lcombS ι (cs ++ [c]) (vs ++ [v]) = lcombS ι cs vs + C c * (toPoly v).map ι := by
  rw [lcombS, lcombS, List.zipWith_append h]
  simp

lemma lcombS_add : ∀ (α a : List S) (vs : List (CPoly R)), α.length = a.length →
    lcombS ι (List.zipWith (· + ·) α a) vs = lcombS ι α vs + lcombS ι a vs
  | [], [], vs, _ => by simp [lcombS]
  | x :: α, y :: a, [], _ => by simp [lcombS]
  | x :: α, y :: a, v :: vs, h => by
    have ih := lcombS_add α a vs (by simpa using h)
    simp only [lcombS, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, C_add]
    ring

lemma lcombS_mapMul (c : S) : ∀ (a : List S) (vs : List (CPoly R)),
    lcombS ι (a.map (c * ·)) vs = C c * lcombS ι a vs
  | [], vs => by simp [lcombS]
  | x :: a, [] => by simp [lcombS]
  | x :: a, v :: vs => by
    have ih := lcombS_mapMul c a vs
    simp only [lcombS, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, C_mul]
    ring

lemma lcombS_of_zero : ∀ (α : List S) (vs : List (CPoly R)), (∀ a ∈ α, a = 0) →
    lcombS ι α vs = 0
  | [], vs, _ => by simp [lcombS]
  | x :: α, [], _ => by simp [lcombS]
  | x :: α, v :: vs, h => by
    have ih := lcombS_of_zero α vs fun a ha ↦ h a (List.mem_cons_of_mem _ ha)
    simp only [lcombS, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, h x List.mem_cons_self]
    simp

lemma lcombS_map_ns : ∀ (a : List R) (vs : List (CPoly R)),
    lcombS ι (a.map ι) vs = (lcomb a vs).map ι
  | [], vs => by simp [lcombS, lcomb]
  | x :: a, [] => by simp [lcombS, lcomb]
  | x :: a, v :: vs => by
    have ih := lcombS_map_ns a vs
    simp only [lcombS, lcomb, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, Polynomial.map_add, Polynomial.map_mul, map_C]

/-! ### The invariant -/

/-- Completeness invariant over `S`. -/
def NsInv (L : List (CPoly R × CPoly R)) (st : List (CPoly R × CPoly R) × List (CPoly R)) :
    Prop :=
  (∀ α : List S, α.length = st.1.length → lcombS ι α (st.1.map Prod.fst) = 0 →
      ∀ a ∈ α, a = 0) ∧
  ∀ cs : List S, cs.length = L.length → ∃ α β : List S, α.length = st.1.length ∧
    β.length = st.2.length ∧ lcombS ι cs (L.map Prod.fst) = lcombS ι α (st.1.map Prod.fst) ∧
    lcombS ι cs (L.map Prod.snd) = lcombS ι α (st.1.map Prod.snd) + lcombS ι β st.2

lemma nsInv_nil : NsInv ι [] ([], []) := by
  refine ⟨fun α hα _ a ha ↦ ?_, fun cs hcs ↦ ⟨[], [], rfl, rfl, ?_, ?_⟩⟩
  · simp at hα; subst hα; simp at ha
  · simp at hcs; subst hcs; simp [lcombS]
  · simp at hcs; subst hcs; simp [lcombS]

lemma exists_concat {α : Type*} (l : List α) (h : l ≠ []) : ∃ l₀ c, l = l₀ ++ [c] := by
  rcases List.eq_nil_or_concat l with h' | ⟨l₀, c, h'⟩
  · exact absurd h' h
  · exact ⟨l₀, c, by rw [h', List.concat_eq_append]⟩

lemma nsInv_step (L : List (CPoly R × CPoly R)) (st : List (CPoly R × CPoly R) × List (CPoly R))
    (x : CPoly R × CPoly R) (h : NsInv ι L st) : NsInv ι (L ++ [x]) (nsStep st x) := by
  obtain ⟨hind, hrel⟩ := h
  unfold nsStep
  cases hls : linSolve (st.1.map Prod.fst) x.1 with
  | none =>
    simp only
    refine ⟨fun α hα h0 a ha ↦ ?_, fun cs hcs ↦ ?_⟩
    · simp only [List.length_append, List.length_singleton] at hα
      obtain ⟨α₀, c, rfl⟩ := exists_concat α (by intro h; subst h; simp at hα)
      have hl₀ : α₀.length = st.1.length := by simpa using hα
      simp only [List.map_append, List.map_singleton] at h0
      rw [lcombS_append ι _ _ _ _ (by simpa using hl₀)] at h0
      have hc : c = 0 := by
        by_contra hc
        refine absurd hls (linSolve_complete_map ι _ _ (α₀.map (-c⁻¹ * ·))
          (by simpa using hl₀) ?_)
        rw [lcombS_mapMul]
        have : lcombS ι α₀ (st.1.map Prod.fst) = -(C c * (toPoly x.1).map ι) := by
          linear_combination h0
        rw [this, mul_neg, ← mul_assoc, ← C_mul, neg_mul, inv_mul_cancel₀ hc, C_neg, C_1,
          neg_mul, one_mul, neg_neg]
      subst hc
      rw [C_0, zero_mul, add_zero] at h0
      rcases List.mem_append.mp ha with ha | ha
      · exact hind α₀ hl₀ h0 a ha
      · simpa using ha
    · obtain ⟨cs₀, c, rfl⟩ := exists_concat cs (by intro h; subst h; simp at hcs)
      have hl₀ : cs₀.length = L.length := by simpa using hcs
      obtain ⟨α, β, hα, hβ, h1, h2⟩ := hrel cs₀ hl₀
      refine ⟨α ++ [c], β, by simp [hα], hβ, ?_, ?_⟩
      · simp only [List.map_append, List.map_singleton]
        rw [lcombS_append ι _ _ _ _ (by simpa using hl₀),
          lcombS_append ι _ _ _ _ (by simpa using hα), h1]
      · simp only [List.map_append, List.map_singleton]
        rw [lcombS_append ι _ _ _ _ (by simpa using hl₀),
          lcombS_append ι _ _ _ _ (by simpa using hα), h2]
        ring
  | some a =>
    obtain ⟨hla, hsol⟩ := linSolve_sound _ _ a hls
    have hla' : a.length = st.1.length := by simpa using hla
    simp only
    refine ⟨hind, fun cs hcs ↦ ?_⟩
    obtain ⟨cs₀, c, rfl⟩ := exists_concat cs (by intro h; subst h; simp at hcs)
    have hl₀ : cs₀.length = L.length := by simpa using hcs
    obtain ⟨α, β, hα, hβ, h1, h2⟩ := hrel cs₀ hl₀
    refine ⟨List.zipWith (· + ·) α ((a.map ι).map (c * ·)), β ++ [c], by simp [hα, hla'],
      by simp [hβ], ?_, ?_⟩
    · simp only [List.map_append, List.map_singleton]
      rw [lcombS_append ι _ _ _ _ (by simpa using hl₀), h1,
        lcombS_add ι _ _ _ (by simp [hα, hla']), lcombS_mapMul, lcombS_map_ns, hsol]
    · simp only [List.map_append, List.map_singleton]
      rw [lcombS_append ι _ _ _ _ (by simpa using hl₀), h2,
        lcombS_append ι _ _ _ _ hβ, lcombS_add ι _ _ _ (by simp [hα, hla']), lcombS_mapMul,
        lcombS_map_ns, toPoly_sub, toPoly_lcombL, Polynomial.map_sub]
      ring

lemma nsInv_foldl (L : List (CPoly R × CPoly R)) : NsInv ι L (L.foldl nsStep ([], [])) := by
  induction L using List.reverseRecOn with
  | nil => exact nsInv_nil ι
  | append_singleton L x ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact nsInv_step ι L _ x ih

/-! ### Soundness invariant -/

lemma lcomb_add1 : ∀ (a b : CPoly R) (vs : List (CPoly R)),
    lcomb (add a b) vs = lcomb a vs + lcomb b vs
  | [], b, vs => by simp [add, lcomb]
  | x :: a, [], vs => by simp [add, lcomb]
  | x :: a, y :: b, [] => by simp [add, lcomb]
  | x :: a, y :: b, v :: vs => by
    have ih := lcomb_add1 a b vs
    simp only [add, lcomb, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, C_add]
    ring

lemma lcomb_smul1 (c : R) : ∀ (a : CPoly R) (vs : List (CPoly R)),
    lcomb (smul c a) vs = C c * lcomb a vs
  | [], vs => by simp [smul, lcomb]
  | x :: a, [] => by simp [smul, lcomb]
  | x :: a, v :: vs => by
    have ih := lcomb_smul1 c a vs
    simp only [smul, List.map_cons, lcomb, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, C_mul]
    ring

lemma lcomb_sub1 (a b : CPoly R) (vs : List (CPoly R)) :
    lcomb (sub a b) vs = lcomb a vs - lcomb b vs := by
  rw [sub, lcomb_add1, neg, lcomb_smul1, C_neg, C_1]
  ring

lemma lcomb_lcombL (vs : List (CPoly R)) : ∀ (a : List R) (ps : List (CPoly R)),
    lcomb (lcombL a ps) vs = (List.zipWith (fun c p ↦ C c * lcomb p vs) a ps).sum
  | [], ps => by simp [lcombL, lcomb]
  | x :: a, [] => by simp [lcombL, lcomb]
  | x :: a, p :: ps => by
    have ih := lcomb_lcombL vs a ps
    simp only [lcombL, List.zipWith_cons_cons, List.foldr_cons, List.sum_cons] at ih ⊢
    rw [lcomb_add1, lcomb_smul1, ih]

lemma lcomb_unitL : ∀ (j : ℕ) (vs : List (CPoly R)), j < vs.length →
    lcomb (unitL j) vs = toPoly (vs.getD j [])
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, v :: vs, _ => by simp [unitL, lcomb]
  | j + 1, v :: vs, h => by
    have ih := lcomb_unitL j vs (by simpa using h)
    simp only [unitL, List.replicate_succ, List.cons_append, lcomb, List.zipWith_cons_cons,
      List.sum_cons, C_0, zero_mul, zero_add] at ih ⊢
    simpa using ih

/-- The soundness invariant. -/
def NsSound (vs : List (CPoly R)) (st : List (CPoly R × CPoly R) × List (CPoly R)) : Prop :=
  (∀ p ∈ st.1, lcomb p.2 vs = toPoly p.1) ∧ ∀ w ∈ st.2, lcomb w vs = 0

lemma lcomb_zip_eq (vs : List (CPoly R)) : ∀ (a : List R) (ps : List (CPoly R × CPoly R)),
    (∀ p ∈ ps, lcomb p.2 vs = toPoly p.1) →
    (List.zipWith (fun c p ↦ C c * lcomb p vs) a (ps.map Prod.snd)).sum =
      lcomb a (ps.map Prod.fst)
  | [], ps, _ => by simp [lcomb]
  | x :: a, [], _ => by simp [lcomb]
  | x :: a, p :: ps, h => by
    have ih := lcomb_zip_eq vs a ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, h p List.mem_cons_self]
    simp [lcomb]

lemma nsSound_step (vs : List (CPoly R)) (st : List (CPoly R × CPoly R) × List (CPoly R))
    (x : CPoly R × CPoly R) (hx : lcomb x.2 vs = toPoly x.1) (h : NsSound vs st) :
    NsSound vs (nsStep st x) := by
  obtain ⟨h1, h2⟩ := h
  unfold nsStep
  cases hls : linSolve (st.1.map Prod.fst) x.1 with
  | none =>
    refine ⟨fun p hp ↦ ?_, h2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact h1 p hp
    · simp at hp; subst hp; exact hx
  | some a =>
    obtain ⟨-, hsol⟩ := linSolve_sound _ _ a hls
    refine ⟨h1, fun w hw ↦ ?_⟩
    rcases List.mem_append.mp hw with hw | hw
    · exact h2 w hw
    · simp at hw; subst hw
      rw [lcomb_sub1, lcomb_lcombL, lcomb_zip_eq vs a st.1 h1, hsol, hx, sub_self]

lemma nsItems_spec (vs : List (CPoly R)) :
    ∀ x ∈ nsItems vs, lcomb x.2 vs = toPoly x.1 := by
  intro x hx
  simp only [nsItems, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact lcomb_unitL j vs hj

lemma nsSound_foldl (vs : List (CPoly R)) : ∀ (L : List (CPoly R × CPoly R)),
    (∀ x ∈ L, lcomb x.2 vs = toPoly x.1) → ∀ st, NsSound vs st →
      NsSound vs (L.foldl nsStep st)
  | [], _, st, h => h
  | x :: L, hL, st, h => by
    rw [List.foldl_cons]
    exact nsSound_foldl vs L (fun y hy ↦ hL y (List.mem_cons_of_mem _ hy)) _
      (nsSound_step vs st x (hL x List.mem_cons_self) h)

/-- **Soundness**: every basis vector is a relation. -/
theorem nullBasis_sound (vs : List (CPoly R)) : ∀ w ∈ nullBasis vs, lcomb w vs = 0 :=
  (nsSound_foldl vs _ (nsItems_spec vs) ([], []) ⟨by simp, by simp⟩).2

lemma nsItems_fst (vs : List (CPoly R)) : (nsItems vs).map Prod.fst = vs := by
  simp only [nsItems, List.map_map]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getElem?_eq_getElem h2]

lemma nsItems_length (vs : List (CPoly R)) : (nsItems vs).length = vs.length := by
  simp [nsItems]

/-- **Completeness over any extension**: a relation `∑ cⱼ vⱼ = 0` with `cⱼ ∈ S` is an
`S`-combination of the basis (as the polynomial `∑ cⱼ Xʲ`). -/
theorem nullBasis_complete (vs : List (CPoly R)) (cs : List S) (hl : cs.length = vs.length)
    (h0 : lcombS ι cs vs = 0) :
    ∃ β : List S, β.length = (nullBasis vs).length ∧
      lcombS ι cs ((nsItems vs).map Prod.snd) = lcombS ι β (nullBasis vs) := by
  obtain ⟨hind, hrel⟩ := nsInv_foldl ι (nsItems vs)
  obtain ⟨α, β, hα, hβ, h1, h2⟩ := hrel cs (by rw [nsItems_length]; exact hl)
  rw [nsItems_fst, h0] at h1
  have hα0 := hind α hα h1.symm
  refine ⟨β, hβ, ?_⟩
  rw [h2, lcombS_of_zero ι α _ hα0, zero_add]
  rfl

end CPoly
