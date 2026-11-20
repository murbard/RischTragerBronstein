import RischTragerBronstein.Computable.CField
import Mathlib.Data.List.GetD

/-!
# Linear independence of products of square roots

In any field `K` of characteristic `0`, let `rᵢ² = sᵢ ∈ ℚ` where the `sᵢ` are *multiplicatively
independent modulo squares* (`MIndep`: no `sᵢ` is a rational square times a product of the
following ones). Then:

* `not_sq`: a rational `a` which is not a square times a product of the `sᵢ` (`InG`) has no square
  root in `ℚ(r₁, …, rₖ)`;
* `prods_indep`: the `2ᵏ` products `∏_{i ∈ T} rᵢ` (`prods`) are linearly independent over `ℚ`.

The proof is the classical induction: every element of `F(y)`, `y² ∈ F`, is `u + v y`
(`mem_closure_insert`), and `(u + v y)² = a` forces `uv = 0`.
-/

open Polynomial

namespace SqrtIndep

variable {K : Type*} [Field K] [CharZero K]

/-- **Elements of `F(y)` with `y² ∈ F`** are `u + v y`. -/
theorem mem_closure_insert (S : Set K) (y : K) (hy : y ^ 2 ∈ Subfield.closure S) (z : K)
    (hz : z ∈ Subfield.closure (insert y S)) :
    ∃ u ∈ Subfield.closure S, ∃ v ∈ Subfield.closure S, z = u + v * y := by
  set F := Subfield.closure S
  let T : Subfield K :=
    { carrier := {z | ∃ u ∈ F, ∃ v ∈ F, z = u + v * y}
      zero_mem' := ⟨0, F.zero_mem, 0, F.zero_mem, by ring⟩
      one_mem' := ⟨1, F.one_mem, 0, F.zero_mem, by ring⟩
      add_mem' := by
        rintro _ _ ⟨u, hu, v, hv, rfl⟩ ⟨u', hu', v', hv', rfl⟩
        exact ⟨u + u', F.add_mem hu hu', v + v', F.add_mem hv hv', by ring⟩
      neg_mem' := by
        rintro _ ⟨u, hu, v, hv, rfl⟩
        exact ⟨-u, F.neg_mem hu, -v, F.neg_mem hv, by ring⟩
      mul_mem' := by
        rintro _ _ ⟨u, hu, v, hv, rfl⟩ ⟨u', hu', v', hv', rfl⟩
        refine ⟨u * u' + v * v' * y ^ 2, F.add_mem (F.mul_mem hu hu')
          (F.mul_mem (F.mul_mem hv hv') hy), u * v' + v * u', F.add_mem (F.mul_mem hu hv')
            (F.mul_mem hv hu'), by ring⟩
      inv_mem' := by
        rintro _ ⟨u, hu, v, hv, rfl⟩
        by_cases hz0 : u + v * y = 0
        · rw [hz0, inv_zero]; exact ⟨0, F.zero_mem, 0, F.zero_mem, by ring⟩
        set N := u ^ 2 - v ^ 2 * y ^ 2 with hN
        have hNm : N ∈ F := F.sub_mem (F.pow_mem hu 2) (F.mul_mem (F.pow_mem hv 2) hy)
        by_cases hN0 : N = 0
        · -- `u = v y`, so `y ∈ F`
          have hfac : (u - v * y) * (u + v * y) = 0 := by rw [← hN0, hN]; ring
          have huv : u = v * y := sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hz0)
          have hv0 : v ≠ 0 := fun h0 ↦ hz0 (by rw [huv, h0]; ring)
          have hyF : y ∈ F := by
            have : y = u / v := by rw [huv]; field_simp
            rw [this]; exact F.div_mem hu hv
          refine ⟨(u + v * y)⁻¹, F.inv_mem (F.add_mem hu (F.mul_mem hv hyF)), 0, F.zero_mem, ?_⟩
          ring
        · refine ⟨u / N, F.div_mem hu hNm, -v / N, F.div_mem (F.neg_mem hv) hNm, ?_⟩
          have hmul : (u + v * y) * (u / N + -v / N * y) = 1 := by
            rw [show (u + v * y) * (u / N + -v / N * y) = (u ^ 2 - v ^ 2 * y ^ 2) / N by
              field_simp; ring, ← hN, div_self hN0]
          exact inv_eq_of_mul_eq_one_right hmul }
  have hle : Subfield.closure (insert y S) ≤ T := by
    rw [Subfield.closure_le]
    intro w hw
    rcases hw with rfl | hw
    · exact ⟨0, F.zero_mem, 1, F.one_mem, by ring⟩
    · exact ⟨w, Subfield.subset_closure hw, 0, F.zero_mem, by ring⟩
  exact hle hz

/-- `a` is a nonzero square times a product of some of the `sᵢ`. -/
def InG : List ℚ → ℚ → Prop
  | [], a => ∃ c : ℚ, c ≠ 0 ∧ a = c ^ 2
  | x :: s, a => InG s a ∨ ∃ b, InG s b ∧ a = x * b

lemma InG_sq_mul : ∀ (s : List ℚ) (a c : ℚ), c ≠ 0 → InG s a → InG s (c ^ 2 * a)
  | [], a, c, hc, h => by
    obtain ⟨d, hd, had⟩ := h
    exact ⟨c * d, mul_ne_zero hc hd, by rw [had]; ring⟩
  | x :: s, a, c, hc, Or.inl h => Or.inl (InG_sq_mul s a c hc h)
  | x :: s, a, c, hc, Or.inr h => by
    obtain ⟨b, hb, hab⟩ := h
    exact Or.inr ⟨c ^ 2 * b, InG_sq_mul s b c hc hb, by rw [hab]; ring⟩

/-- Multiplicative independence modulo squares. -/
def MIndep : List ℚ → Prop
  | [] => True
  | x :: s => MIndep s ∧ x ≠ 0 ∧ ¬ InG s x

lemma closure_empty_rat (z : K) (hz : z ∈ Subfield.closure (∅ : Set K)) : ∃ q : ℚ, z = q := by
  have hle : Subfield.closure (∅ : Set K) ≤ (Rat.castHom K).fieldRange := by
    rw [Subfield.closure_le]; intro w hw; exact absurd hw (Set.notMem_empty w)
  obtain ⟨q, rfl⟩ := hle hz
  exact ⟨q, rfl⟩

lemma set_cons (y : K) (r : List K) : {w | w ∈ y :: r} = insert y {w | w ∈ r} := by
  ext w; simp

/-- **No square root outside the group.** -/
theorem not_sq : ∀ (s : List ℚ) (r : List K), r.length = s.length →
    (∀ i (hi : i < r.length) (hi' : i < s.length), r[i] ^ 2 = (s[i] : K)) → MIndep s →
    ∀ a : ℚ, a ≠ 0 → ¬ InG s a → ∀ z ∈ Subfield.closure {w | w ∈ r}, z ^ 2 ≠ (a : K)
  | [], r, hl, _, _, a, ha0, ha, z, hz => by
    have hr : r = [] := List.eq_nil_of_length_eq_zero hl
    subst hr
    have : {w : K | w ∈ ([] : List K)} = ∅ := by ext; simp
    rw [this] at hz
    obtain ⟨q, rfl⟩ := closure_empty_rat z hz
    intro h
    have h' : ((q ^ 2 : ℚ) : K) = (a : K) := by rw [← h]; exact map_pow (Rat.castHom K) q 2
    have hqa : q ^ 2 = a := Rat.cast_injective h'
    exact ha ⟨q, fun h0 ↦ ha0 (by rw [← hqa, h0]; ring), hqa.symm⟩
  | x :: s, [], hl, _, _, _, _, _, _, _ => by simp at hl
  | x :: s, y :: r, hl, hr, hm, a, ha0, ha, z, hz => by
    obtain ⟨hms, hx0, hxs⟩ := hm
    have hl' : r.length = s.length := by simpa using hl
    have hr' : ∀ i (hi : i < r.length) (hi' : i < s.length), r[i] ^ 2 = (s[i] : K) :=
      fun i hi hi' ↦ hr (i + 1) (by simp; omega) (by simp; omega)
    have hy : y ^ 2 = (x : K) := hr 0 (by simp) (by simp)
    have IH := not_sq s r hl' hr' hms
    rw [set_cons] at hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_closure_insert _ y
      (by rw [hy]; exact SubfieldClass.ratCast_mem _ x) z hz
    intro h
    have hexp : u ^ 2 + v ^ 2 * (x : K) + 2 * u * v * y = a := by rw [← hy, ← h]; ring
    by_cases huv : u ≠ 0 ∧ v ≠ 0
    · -- then `y ∈ F`
      have hyF : y ∈ Subfield.closure {w | w ∈ r} := by
        have hu0 := huv.1
        have hv0 := huv.2
        have : y = ((a : K) - u ^ 2 - v ^ 2 * x) / (2 * u * v) := by
          field_simp
          linear_combination hexp
        rw [this]
        exact Subfield.div_mem _ (Subfield.sub_mem _ (Subfield.sub_mem _
          (SubfieldClass.ratCast_mem _ a) (Subfield.pow_mem _ hu 2))
          (Subfield.mul_mem _ (Subfield.pow_mem _ hv 2) (SubfieldClass.ratCast_mem _ x)))
          (Subfield.mul_mem _ (Subfield.mul_mem _ (by simpa using Subfield.natCast_mem (Subfield.closure {w | w ∈ r}) 2) hu) hv)
      exact IH x hx0 hxs y hyF hy
    · rcases not_and_or.mp huv with hu0 | hv0
      · push Not at hu0
        subst hu0
        -- `(v x)² = a x`
        have hax : ¬ InG s (a * x) := by
          intro hg
          apply ha
          refine Or.inr ⟨(1 / x) ^ 2 * (a * x), InG_sq_mul s _ _ (by simpa using hx0) hg, ?_⟩
          field_simp
        refine IH (a * x) (mul_ne_zero ha0 hx0) hax (v * x)
          (Subfield.mul_mem _ hv (SubfieldClass.ratCast_mem _ x)) ?_
        push_cast
        linear_combination (x : K) * hexp
      · push Not at hv0
        subst hv0
        refine IH a ha0 (fun hg ↦ ha (Or.inl hg)) u hu ?_
        linear_combination hexp

/-- The products `∏_{i ∈ T} rᵢ`, in the order of the subsets `T` (binary counting). -/
def prods : List K → List K
  | [] => [1]
  | y :: r => prods r ++ (prods r).map (y * ·)

lemma length_prods : ∀ r : List K, (prods r).length = 2 ^ r.length
  | [] => rfl
  | y :: r => by simp [prods, length_prods r, pow_succ]; ring

lemma prods_mem : ∀ (r : List K), ∀ p ∈ prods r, p ∈ Subfield.closure {w | w ∈ r}
  | [], p, hp => by simp [prods] at hp; subst hp; exact Subfield.one_mem _
  | y :: r, p, hp => by
    have hsub : Subfield.closure {w | w ∈ r} ≤ Subfield.closure {w | w ∈ y :: r} :=
      Subfield.closure_mono (fun w hw ↦ by simp at hw ⊢; exact Or.inr hw)
    have hyc : y ∈ Subfield.closure {w | w ∈ y :: r} := Subfield.subset_closure (by simp)
    rcases List.mem_append.mp hp with hp | hp
    · exact hsub (prods_mem r p hp)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact Subfield.mul_mem _ hyc (hsub (prods_mem r q hq))

/-- A rational combination. -/
def comb (c : ℕ → ℚ) (l : List K) : K := ∑ i ∈ Finset.range l.length, (c i : K) * l.getD i 0

lemma comb_mem (c : ℕ → ℚ) (l : List K) (F : Subfield K) (hl : ∀ p ∈ l, p ∈ F) : comb c l ∈ F :=
  Subfield.sum_mem _ fun i hi ↦ Subfield.mul_mem _ (SubfieldClass.ratCast_mem _ _)
    (hl _ (by rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]; exact List.getElem_mem _))

lemma comb_prods_cons (c : ℕ → ℚ) (y : K) (r : List K) :
    comb c (prods (y :: r)) = comb c (prods r) + y * comb (fun i ↦ c ((prods r).length + i)) (prods r) := by
  unfold comb
  simp only [prods, List.length_append, List.length_map]
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.mp hi),
      List.getD_eq_getElem _ _ (Finset.mem_range.mp hi), List.getElem_map]
    ring

/-- **The products of the square roots are linearly independent over `ℚ`.** -/
theorem prods_indep : ∀ (s : List ℚ) (r : List K), r.length = s.length →
    (∀ i (hi : i < r.length) (hi' : i < s.length), r[i] ^ 2 = (s[i] : K)) → MIndep s →
    ∀ c : ℕ → ℚ, comb c (prods r) = 0 → ∀ i < (prods r).length, c i = 0
  | [], r, hl, _, _, c, h, i, hi => by
    have hr : r = [] := List.eq_nil_of_length_eq_zero hl
    subst hr
    simp only [prods, List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    simpa [comb, prods] using h
  | x :: s, [], hl, _, _, _, _, _, _ => by simp at hl
  | x :: s, y :: r, hl, hr, hm, c, h, i, hi => by
    obtain ⟨hms, hx0, hxs⟩ := hm
    have hl' : r.length = s.length := by simpa using hl
    have hr' : ∀ i (hi : i < r.length) (hi' : i < s.length), r[i] ^ 2 = (s[i] : K) :=
      fun i hi hi' ↦ hr (i + 1) (by simp; omega) (by simp; omega)
    have hy : y ^ 2 = (x : K) := hr 0 (by simp) (by simp)
    set F := Subfield.closure {w | w ∈ r}
    rw [comb_prods_cons] at h
    set n := (prods r).length
    set u := comb c (prods r)
    set v := comb (fun i ↦ c (n + i)) (prods r)
    have hu : u ∈ F := comb_mem _ _ F (prods_mem r)
    have hv : v ∈ F := comb_mem _ _ F (prods_mem r)
    have hv0 : v = 0 := by
      by_contra hv0
      have hyF : y ∈ F := by
        have : y = -u / v := by field_simp; linear_combination h
        rw [this]; exact F.div_mem (F.neg_mem hu) hv
      exact not_sq s r hl' hr' hms x hx0 hxs y hyF hy
    have hu0 : u = 0 := by rw [hv0, mul_zero, add_zero] at h; exact h
    have hi' : i < n + n := by simpa [prods, n] using hi
    rcases Nat.lt_or_ge i n with hin | hin
    · exact prods_indep s r hl' hr' hms c hu0 i hin
    · have := prods_indep s r hl' hr' hms (fun i ↦ c (n + i)) hv0 (i - n) (by omega)
      simpa [Nat.add_sub_cancel' hin] using this

end SqrtIndep
