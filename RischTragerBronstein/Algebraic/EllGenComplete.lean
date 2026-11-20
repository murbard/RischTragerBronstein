import RischTragerBronstein.Algebraic.HermiteBound
import RischTragerBronstein.Algebraic.EllGenTw

/-!
# Completeness of the elliptic front end

For `D` split over `ℚ` the Hermite decomposition exists (`hermite_poly`), fits the solver's degree
budget (`hermite_deg_bound`) and is unique (`hermite_unique`); so `ellHermiteRaw` finds exactly it,
and `ellDecideGen` / `ellDecideGenTw` answer whenever its residues lie over rational points, resp.
over one twist class.
-/

open Polynomial

namespace EllAlgo

open CPoly

/-- A relation over a mapped range. -/
lemma lcomb_range (f : ℕ → CPoly ℚ) : ∀ (n : ℕ) (w : List ℚ),
    lcomb w ((List.range n).map f) =
      ∑ k ∈ Finset.range (min n w.length), C (w.getD k 0) * toPoly (f k) := by
  intro n
  induction n with
  | zero => intro w; simp [lcomb_nil_right]
  | succ n ih =>
    intro w
    rw [List.range_succ, List.map_append, lcomb_append, ih, List.length_map, List.length_range]
    rcases Nat.lt_or_ge n w.length with hn | hn
    · rw [List.drop_eq_getElem_cons hn, List.map_singleton, lcomb_cons_cons, lcomb_nil_right,
        add_zero, List.length_take, min_eq_left hn.le, min_eq_left (show n + 1 ≤ w.length by omega),
        Finset.sum_range_succ, min_self]
      congr 1
      · refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [Finset.mem_range] at hk
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]; rfl
    · rw [List.drop_eq_nil_of_le hn, lcomb_nil_left, add_zero, List.length_take,
        min_eq_right hn, min_eq_right (show w.length ≤ n + 1 by omega), min_eq_right hn]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_range] at hk
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]

/-- A relation over a mapped range, as a full sum (`getD` pads with zeros). -/
lemma lcomb_range' (f : ℕ → CPoly ℚ) (n : ℕ) (w : List ℚ) :
    lcomb w ((List.range n).map f) = ∑ k ∈ Finset.range n, C (w.getD k 0) * toPoly (f k) := by
  rw [lcomb_range]
  rcases Nat.le_total n w.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, ← Finset.sum_range_add_sum_Ico _ h]
    have : ∑ k ∈ Finset.Ico w.length n, C (w.getD k 0) * toPoly (f k) = 0 :=
      Finset.sum_eq_zero fun k hk ↦ by
        rw [Finset.mem_Ico] at hk
        rw [List.getD_eq_default _ _ hk.1, C_0, zero_mul]
    rw [this, add_zero]

lemma lcomb_cons' (a : CPoly ℚ) (rest : List (CPoly ℚ)) (w : List ℚ) :
    lcomb w (a :: rest) = C (w.getD 0 0) * toPoly a + lcomb w.tail rest := by
  rcases w with _ | ⟨c, w⟩
  · simp [lcomb_nil_left]
  · rw [lcomb_cons_cons]; rfl

lemma lcomb_append' (w : List ℚ) (L₁ L₂ : List (CPoly ℚ)) :
    lcomb w (L₁ ++ L₂) = lcomb (w.take L₁.length) L₁ + lcomb (w.drop L₁.length) L₂ :=
  lcomb_append w L₁ L₂

lemma getD_take {w : List ℚ} {m k : ℕ} (hk : k < m) : (w.take m).getD k 0 = w.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

lemma getD_drop {w : List ℚ} {m k : ℕ} : (w.drop m).getD k 0 = w.getD (m + k) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **The value of a relation among the Hermite columns.** -/
lemma lcomb_genCols (p A D : CPoly ℚ) (αs : List ℚ) (dW nB : ℕ) (w : List ℚ) :
    lcomb w (genCols p A D αs dW nB) =
      C (w.getD 0 0) * (2 * toPoly A * (toPoly D * toPoly D) * toPoly (linProd αs)) +
      ∑ i ∈ Finset.range (dW + 1), C (w.getD (1 + i) 0) *
        (toPoly D * toPoly (linProd αs) * LD (toPoly p) (toPoly D) (X ^ i)) +
      ∑ j ∈ Finset.range nB, C (w.getD (1 + (dW + 1) + j) 0) *
        (2 * X ^ j * (toPoly D * toPoly D * (toPoly D * toPoly (linProd αs)))) +
      ∑ k ∈ Finset.range αs.length, C (w.getD (1 + (dW + 1) + nB + k) 0) *
        (2 * (toPoly D * toPoly D * (toPoly D * toPoly (linProd (αs.eraseIdx k))))) := by
  have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
    rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
  unfold genCols
  simp only
  rw [lcomb_append', lcomb_append', lcomb_cons']
  simp only [List.length_append, List.length_cons, List.length_map, List.length_range]
  rw [lcomb_range', lcomb_range', lcomb_range']
  simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, toPoly_monomial, h2, map_one,
    one_mul]
  have g0 : ((w.take (dW + 1 + 1 + nB)).take (dW + 1 + 1)).getD 0 0 = w.getD 0 0 := by
    rw [getD_take (by omega), getD_take (by omega)]
  rw [g0]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · ring
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    have : (((w.take (dW + 1 + 1 + nB)).take (dW + 1 + 1)).tail).getD i 0 = w.getD (1 + i) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_tail, ← List.getD_eq_getElem?_getD,
        getD_take (by omega), getD_take (by omega), add_comm]
    rw [this, LD]
    ring
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    have : ((w.take (dW + 1 + 1 + nB)).drop (dW + 1 + 1)).getD j 0 =
        w.getD (1 + (dW + 1) + j) 0 := by
      rw [getD_drop, getD_take (by omega)]; congr 1; omega
    rw [this, mul_assoc 2]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    have : (w.drop (dW + 1 + 1 + nB)).getD k 0 = w.getD (1 + (dW + 1) + nB + k) 0 := by
      rw [getD_drop]; congr 1; omega
    rw [this]

/-! ### Algebraic helpers -/

lemma evalQ_eq' (P : CPoly ℚ) (q : ℚ) : residuePts.evalQ P q = (toPoly P).eval q := by
  induction P with
  | nil => simp [residuePts.evalQ]
  | cons a t ih =>
    simp only [residuePts.evalQ, List.foldr_cons] at ih ⊢
    rw [ih, toPoly_cons, eval_add, eval_mul, eval_C, eval_X]

lemma toPoly_linProd : ∀ l : List ℚ, toPoly (linProd l) = (l.map fun α ↦ X - C α).prod
  | [] => by simp [linProd]
  | a :: t => by
    have := toPoly_linProd t
    simp only [linProd, List.map_cons, List.foldr_cons, List.prod_cons] at this ⊢
    rw [toPoly_mul, this]
    simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero, map_one, mul_one, map_neg]
    ring

/-- The residue sum over a duplicate-free list, as a `Finset` sum. -/
lemma sum_linProd_eraseIdx (g : ℚ → ℚ) : ∀ l : List ℚ, l.Nodup →
    ∑ k ∈ Finset.range l.length, C (g (l.getD k 0)) * toPoly (linProd (l.eraseIdx k)) =
      ∑ α ∈ l.toFinset, C (g α) * ∏ β ∈ l.toFinset.erase α, (X - C β)
  | [] => by simp
  | a :: t => by
    intro hnd
    rw [List.nodup_cons] at hnd
    have ih := sum_linProd_eraseIdx g t hnd.2
    have hat : a ∉ t.toFinset := by simpa using hnd.1
    rw [List.length_cons, Finset.sum_range_succ', List.toFinset_cons, Finset.sum_insert hat,
      Finset.erase_insert hat]
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.eraseIdx_cons_succ,
      List.eraseIdx_cons_zero]
    rw [toPoly_linProd t, List.prod_toFinset _ hnd.2, add_comm]
    congr 1
    have : ∀ k, toPoly (linProd (a :: t.eraseIdx k)) = (X - C a) * toPoly (linProd (t.eraseIdx k)) :=
      fun k ↦ by rw [toPoly_linProd, toPoly_linProd, List.map_cons, List.prod_cons]
    simp only [this]
    rw [show ∑ k ∈ Finset.range t.length, C (g (t.getD k 0)) *
        ((X - C a) * toPoly (linProd (t.eraseIdx k))) = (X - C a) *
        ∑ k ∈ Finset.range t.length, C (g (t.getD k 0)) * toPoly (linProd (t.eraseIdx k)) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα ↦ ?_
    have hne : α ≠ a := fun h ↦ hat (h ▸ hα)
    rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert (by simp [hat])]
    ring

/-- Enlarging the set of poles in a Hermite identity (with zero residues). -/
lemma hermite_extend (p A D W B₀ : ℚ[X]) (T U : Finset ℚ) (hTU : T ⊆ U) (c : ℚ → ℚ)
    (hid : 2 * A * D * (∏ α ∈ T, (X - C α)) = (∏ α ∈ T, (X - C α)) * LD p D W +
      2 * D ^ 2 * (∏ α ∈ T, (X - C α)) * B₀ +
      2 * D ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β)) :
    2 * A * D * (∏ α ∈ U, (X - C α)) = (∏ α ∈ U, (X - C α)) * LD p D W +
      2 * D ^ 2 * (∏ α ∈ U, (X - C α)) * B₀ +
      2 * D ^ 2 * ∑ α ∈ U, C (if α ∈ T then c α else 0) * ∏ β ∈ U.erase α, (X - C β) := by
  classical
  set R := ∏ α ∈ U \ T, (X - C α)
  have hU : ∏ α ∈ U, (X - C α) = (∏ α ∈ T, (X - C α)) * R := by
    rw [← Finset.prod_sdiff hTU, mul_comm]
  have hS : ∑ α ∈ U, C (if α ∈ T then c α else 0) * ∏ β ∈ U.erase α, (X - C β) =
      (∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β)) * R := by
    rw [Finset.sum_mul, ← Finset.sum_subset hTU (fun α _ hα ↦ by rw [if_neg hα, C_0, zero_mul])]
    refine Finset.sum_congr rfl fun α hα ↦ ?_
    rw [if_pos hα, mul_assoc]
    congr 1
    have hsub : T.erase α ⊆ U.erase α := Finset.erase_subset_erase α hTU
    have he : U.erase α \ T.erase α = U \ T := by
      ext β; simp only [Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, fun h ↦ h3 ⟨h1, h⟩⟩
      · rintro ⟨h2, h3⟩; exact ⟨⟨fun h ↦ h3 (h ▸ hα), h2⟩, fun h ↦ h3 h.2⟩
    rw [← Finset.prod_sdiff hsub, mul_comm, he]
  rw [hU, hS]
  linear_combination R * hid

lemma LD_sum (p D : ℚ[X]) (a : ℕ → ℚ) (s : Finset ℕ) :
    LD p D (∑ i ∈ s, C (a i) * X ^ i) = ∑ i ∈ s, C (a i) * LD p D (X ^ i) := by
  classical
  refine Finset.induction_on s (by simp [LD]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  simp only [LD, derivative_add, derivative_C_mul]
  ring

lemma sum_range_coeff (f : ℚ[X]) (n : ℕ) (h : f = 0 ∨ f.natDegree < n) :
    ∑ i ∈ Finset.range n, C (f.coeff i) * X ^ i = f := by
  rcases h with rfl | h
  · simp
  · conv_rhs => rw [as_sum_range' f n h]
    simp only [C_mul_X_pow_eq_monomial]

lemma getD_map_range (g : ℕ → ℚ) {N k : ℕ} (hk : k < N) :
    ((List.range N).map g).getD k 0 = g k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl

/-- **A relation with non-zero head forces a basis vector with non-zero head.** -/
lemma exists_head_basis (vs : List (CPoly ℚ)) (cs : List ℚ) (hl : cs.length = vs.length)
    (hrel : CPoly.lcomb cs vs = 0) (hne : cs.getD 0 0 ≠ 0) :
    ∃ u ∈ CPoly.nullBasis vs, u.getD 0 0 ≠ 0 := by
  by_contra hall
  push_neg at hall
  have h0 : CPoly.lcombS (RingHom.id ℚ) cs vs = 0 := by
    have := CPoly.lcombS_map_ns (RingHom.id ℚ) cs vs
    rw [RingHom.coe_id, List.map_id, Polynomial.map_id] at this
    rw [this, hrel]
  obtain ⟨β, -, hβ⟩ := CPoly.nullBasis_complete (RingHom.id ℚ) vs cs hl h0
  have e1 := CPoly.lcombS_map_ns (RingHom.id ℚ) cs ((CPoly.nsItems vs).map Prod.snd)
  have e2 := CPoly.lcombS_map_ns (RingHom.id ℚ) β (CPoly.nullBasis vs)
  rw [RingHom.coe_id, List.map_id, Polynomial.map_id] at e1 e2
  rw [e1, e2] at hβ
  have hns : (CPoly.nsItems vs).map Prod.snd = (List.range cs.length).map CPoly.unitL := by
    simp [CPoly.nsItems, hl]
  rw [hns, lcomb_units] at hβ
  apply hne
  rw [← CPoly.coeff_toPoly, hβ]
  refine coeff_lcomb_eq_zero 0 β _ fun w hw ↦ ?_
  rw [CPoly.coeff_toPoly, hall w hw]

lemma natDegree_toPoly_le_length (P : CPoly ℚ) : (toPoly P).natDegree ≤ P.length :=
  natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ by
    rw [CPoly.coeff_toPoly, List.getD_eq_default _ _ hk.le]

lemma length_genCols (p A D : CPoly ℚ) (αs : List ℚ) (dW nB : ℕ) :
    (genCols p A D αs dW nB).length = 1 + (dW + 1) + nB + αs.length := by
  simp [genCols]; omega

/-! ### The Hermite solve always succeeds -/

/-- **Completeness of the Hermite solve** (split denominator). -/
theorem ellHermiteRaw_ne_none (p A D : CPoly ℚ) (hsq : Squarefree (toPoly p))
    (hp1 : 1 ≤ (toPoly p).natDegree) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits) :
    ellHermiteRaw p A D ≠ none := by
  classical
  set αs := (ratRootsQ D).dedup.filter fun α ↦ residuePts.evalQ D α == 0 &&
    residuePts.evalQ p α != 0 with hαs
  set nB := (trim p).length - 2 with hnB
  set dW := A.length + D.length with hdW
  have hnd : αs.Nodup := (List.nodup_dedup _).filter _
  obtain ⟨W, B₀, T, c, hT, hB, hid⟩ := hermite_poly (toPoly p) hsq hp1 (toPoly A) (toPoly D) hD hsplit
  have hWd := hermite_deg_bound (toPoly p) hp1 (toPoly A) (toPoly D) W B₀ T c hD hB hid
  have hTU : T ⊆ αs.toFinset := fun α hα ↦ by
    obtain ⟨h1, h2⟩ := hT α hα
    rw [List.mem_toFinset, hαs, List.mem_filter, List.mem_dedup]
    refine ⟨ratRootsQ_spec D α hD h1, ?_⟩
    rw [evalQ_eq', evalQ_eq']
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    exact ⟨h1, h2⟩
  have hext := hermite_extend _ _ _ _ _ T _ hTU c hid
  set c' : ℚ → ℚ := fun α ↦ if α ∈ T then c α else 0
  have hL : toPoly (linProd αs) = ∏ α ∈ αs.toFinset, (X - C α) := by
    rw [toPoly_linProd, List.prod_toFinset _ hnd]
  -- degree budgets
  have hAd := natDegree_toPoly_le_length A
  have hDd := natDegree_toPoly_le_length D
  have hWn : W = 0 ∨ W.natDegree < dW + 1 := Or.inr (by
    have := max_le_max hAd hDd
    have : max A.length D.length ≤ dW := max_le (by omega) (by omega)
    omega)
  have hp0 : toPoly p ≠ 0 := hsq.ne_zero
  have htp : (trim p).length = (toPoly p).natDegree + 1 :=
    length_trim (fun h ↦ hp0 ((trim_eq_nil_iff p).mp h))
  have hBn : B₀ = 0 ∨ B₀.natDegree < nB := by
    rcases hB with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  -- the relation vector
  set N := 1 + (dW + 1) + nB + αs.length
  set g : ℕ → ℚ := fun k ↦ if k = 0 then 1 else if k < dW + 2 then -W.coeff (k - 1)
    else if k < dW + 2 + nB then -B₀.coeff (k - (dW + 2)) else -c' (αs.getD (k - (dW + 2 + nB)) 0)
  set w := (List.range N).map g
  have hwl : w.length = (genCols p A D αs dW nB).length := by
    rw [length_genCols]; simp [w, N]
  have hrel : lcomb w (genCols p A D αs dW nB) = 0 := by
    rw [lcomb_genCols, getD_map_range g (by omega)]
    have s1 : ∑ i ∈ Finset.range (dW + 1), C (w.getD (1 + i) 0) *
        (toPoly D * toPoly (linProd αs) * LD (toPoly p) (toPoly D) (X ^ i)) =
        -(toPoly D * toPoly (linProd αs) * LD (toPoly p) (toPoly D) W) := by
      conv_rhs => rw [← sum_range_coeff W _ hWn, LD_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [Finset.mem_range] at hi
      rw [getD_map_range g (by omega)]
      simp only [g, if_neg (show 1 + i ≠ 0 by omega), if_pos (show 1 + i < dW + 2 by omega),
        show 1 + i - 1 = i by omega, map_neg]
      ring
    have s2 : ∑ j ∈ Finset.range nB, C (w.getD (1 + (dW + 1) + j) 0) *
        (2 * X ^ j * (toPoly D * toPoly D * (toPoly D * toPoly (linProd αs)))) =
        -(2 * toPoly D ^ 2 * toPoly (linProd αs) * B₀ * toPoly D) := by
      conv_rhs => rw [← sum_range_coeff B₀ _ hBn, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [Finset.mem_range] at hj
      rw [getD_map_range g (by omega)]
      simp only [g, if_neg (show 1 + (dW + 1) + j ≠ 0 by omega),
        if_neg (show ¬ 1 + (dW + 1) + j < dW + 2 by omega),
        if_pos (show 1 + (dW + 1) + j < dW + 2 + nB by omega),
        show 1 + (dW + 1) + j - (dW + 2) = j by omega, map_neg]
      ring
    have s3 : ∑ k ∈ Finset.range αs.length, C (w.getD (1 + (dW + 1) + nB + k) 0) *
        (2 * (toPoly D * toPoly D * (toPoly D * toPoly (linProd (αs.eraseIdx k))))) =
        -(2 * toPoly D ^ 2 * toPoly D * ∑ α ∈ αs.toFinset, C (c' α) *
          ∏ β ∈ αs.toFinset.erase α, (X - C β)) := by
      rw [← sum_linProd_eraseIdx c' αs hnd, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_range] at hk
      rw [getD_map_range g (by omega)]
      simp only [g, if_neg (show 1 + (dW + 1) + nB + k ≠ 0 by omega),
        if_neg (show ¬ 1 + (dW + 1) + nB + k < dW + 2 by omega),
        if_neg (show ¬ 1 + (dW + 1) + nB + k < dW + 2 + nB by omega),
        show 1 + (dW + 1) + nB + k - (dW + 2 + nB) = k by omega, map_neg]
      ring
    rw [s1, s2, s3, hL]
    simp only [g, if_pos rfl, map_one, one_mul]
    rw [hL] at s1 s2
    linear_combination (toPoly D) * hext
  have hhead : w.getD 0 0 ≠ 0 := by
    rw [getD_map_range g (by omega)]; simp [g]
  obtain ⟨u, hu, hu0⟩ := exists_head_basis _ w hwl hrel hhead
  have hsome : ((nullBasis (genCols p A D αs dW nB)).find? fun u ↦ u.getD 0 0 ≠ 0).isSome := by
    rw [List.find?_isSome]; exact ⟨u, hu, by simpa using hu0⟩
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp hsome
  unfold ellHermiteRaw
  rw [← hαs, ← hnB, ← hdW]
  dsimp only
  rw [hu']
  simp

lemma toPoly_map_range' (f : ℕ → ℚ) (n : ℕ) :
    toPoly ((List.range n).map f) = ∑ i ∈ Finset.range n, C (f i) * X ^ i := by
  ext k
  rw [CPoly.coeff_toPoly, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rw [Finset.mem_range] at hk; exact getD_map_range f hk
  · rw [Finset.mem_range] at hk
    rw [List.getD_eq_default _ _ (by simp; omega)]

/-- **What the Hermite solve returns**: a Hermite identity over the rational roots of `D`. -/
lemma ellHermiteRaw_spec (p A D W B₀ : CPoly ℚ) (αs cs : List ℚ) (hD : toPoly D ≠ 0)
    (h : ellHermiteRaw p A D = some (W, B₀, αs, cs)) :
    αs = (ratRootsQ D).dedup.filter (fun α ↦ residuePts.evalQ D α == 0 &&
      residuePts.evalQ p α != 0) ∧ cs.length = αs.length ∧
    2 * toPoly A * toPoly D * toPoly (linProd αs) =
      toPoly (linProd αs) * LD (toPoly p) (toPoly D) (toPoly W) +
      2 * toPoly D ^ 2 * toPoly (linProd αs) * toPoly B₀ +
      2 * toPoly D ^ 2 * ∑ k ∈ Finset.range αs.length, C (cs.getD k 0) *
        toPoly (linProd (αs.eraseIdx k)) := by
  unfold ellHermiteRaw at h
  dsimp only at h
  split at h
  · rename_i u hu
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hW, hB, hα, hcs⟩ := h
    subst hW hB hα hcs
    refine ⟨rfl, by simp, ?_⟩
    have hmem := List.mem_of_find?_eq_some hu
    have hu0 : u.getD 0 0 ≠ 0 := by simpa using List.find?_some hu
    have hrel := nullBasis_sound _ u hmem
    rw [lcomb_genCols] at hrel
    set αs := (ratRootsQ D).dedup.filter (fun α ↦ residuePts.evalQ D α == 0 &&
      residuePts.evalQ p α != 0)
    set dW := A.length + D.length
    set nB := (trim p).length - 2
    set u0 := u.getD 0 0
    have key : ∀ k, C u0 * C (-u.getD k 0 / u0) = -C (u.getD k 0) := fun k ↦ by
      rw [← C_mul, ← C_neg]; congr 1; field_simp
    set L := toPoly (linProd αs)
    set Dp := toPoly D
    set co : ℕ → ℚ := fun k ↦ -u.getD k 0 / u0
    have key' : ∀ k, C u0 * C (co k) = -C (u.getD k 0) := key
    have S1 : ∑ i ∈ Finset.range (dW + 1), C (u.getD (1 + i) 0) * (Dp * L * LD (toPoly p) Dp (X ^ i))
        = -(C u0 * (Dp * L * LD (toPoly p) Dp (toPoly ((List.range (dW + 1)).map
          fun i ↦ co (i + 1))))) := by
      rw [toPoly_map_range', LD_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [add_comm 1 i]
      linear_combination (Dp * L * LD (toPoly p) Dp (X ^ i)) * key' (i + 1)
    have S2 : ∑ j ∈ Finset.range nB, C (u.getD (1 + (dW + 1) + j) 0) *
        (2 * X ^ j * (Dp * Dp * (Dp * L))) = -(C u0 * (2 * Dp ^ 3 * L *
          toPoly ((List.range nB).map fun j ↦ co (dW + 2 + j)))) := by
      rw [toPoly_map_range', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [show 1 + (dW + 1) + j = dW + 2 + j by omega]
      linear_combination (2 * X ^ j * (Dp * Dp * (Dp * L))) * key' (dW + 2 + j)
    have S3 : ∑ k ∈ Finset.range αs.length, C (u.getD (1 + (dW + 1) + nB + k) 0) *
        (2 * (Dp * Dp * (Dp * toPoly (linProd (αs.eraseIdx k))))) =
        -(C u0 * (2 * Dp ^ 3 * ∑ k ∈ Finset.range αs.length,
          C (((List.range αs.length).map fun k ↦ co (dW + 2 + nB + k)).getD k 0) *
            toPoly (linProd (αs.eraseIdx k)))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Finset.mem_range] at hk
      rw [getD_map_range _ hk]
      rw [show 1 + (dW + 1) + nB + k = dW + 2 + nB + k by omega]
      linear_combination (2 * (Dp * Dp * (Dp * toPoly (linProd (αs.eraseIdx k))))) *
        key' (dW + 2 + nB + k)
    rw [S1, S2, S3] at hrel
    have hu0' : C u0 ≠ 0 := by rwa [Ne, C_eq_zero]
    have hz : Dp * C u0 * ((2 * toPoly A * Dp * L) - (L * LD (toPoly p) Dp
        (toPoly ((List.range (dW + 1)).map fun i ↦ co (i + 1))) +
        2 * Dp ^ 2 * L * toPoly ((List.range nB).map fun j ↦ co (dW + 2 + j)) +
        2 * Dp ^ 2 * ∑ k ∈ Finset.range αs.length,
          C (((List.range αs.length).map fun k ↦ co (dW + 2 + nB + k)).getD k 0) *
            toPoly (linProd (αs.eraseIdx k)))) = 0 := by
      linear_combination hrel
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact absurd h0 (mul_ne_zero hD hu0')
    · exact sub_eq_zero.mp h0
  · exact absurd h (by simp)

/-! ### The kernel check passes -/

lemma linProd_eraseIdx (l : List ℚ) {k : ℕ} (hk : k < l.length) :
    toPoly (linProd l) = (X - C (l.getD k 0)) * toPoly (linProd (l.eraseIdx k)) := by
  rw [toPoly_linProd, toPoly_linProd, ← List.prod_cons]
  apply List.Perm.prod_eq
  rw [List.getD_eq_getElem _ _ hk]
  exact ((List.getElem_cons_eraseIdx_perm hk).map _).symm

/-- `genCheck` from the polynomial identities. -/
lemma genCheck_of_poly (p A D W B₀ : CPoly ℚ) (G : CPoly ℚ × CPoly ℚ) (αs cs : List ℚ)
    (hD : toPoly D ≠ 0) (hG2 : toPoly G.2 ≠ 0)
    (hid : 2 * toPoly A * toPoly D * toPoly (linProd αs) =
      toPoly (linProd αs) * LD (toPoly p) (toPoly D) (toPoly W) +
      2 * toPoly D ^ 2 * toPoly (linProd αs) * toPoly B₀ +
      2 * toPoly D ^ 2 * ∑ k ∈ Finset.range αs.length, C (cs.getD k 0) *
        toPoly (linProd (αs.eraseIdx k)))
    (hG : toPoly G.2 * (toPoly B₀ * toPoly (linProd αs) + ∑ k ∈ Finset.range αs.length,
      C (cs.getD k 0) * toPoly (linProd (αs.eraseIdx k))) = toPoly G.1 * toPoly (linProd αs)) :
    genCheck p A D W G = true := by
  have hL : toPoly (linProd αs) ≠ 0 := by
    rw [toPoly_linProd]
    refine List.prod_ne_zero ?_
    simp only [List.mem_map, not_exists, not_and]
    exact fun α _ h ↦ X_sub_C_ne_zero α h
  unfold genCheck
  simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, isZero_iff]
  refine ⟨⟨hD, hG2⟩, (beq_iff _ _).mpr ?_⟩
  have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
    rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
  simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, h2]
  have : toPoly (linProd αs) * (toPoly A * 2 * (toPoly D * toPoly D * toPoly G.2) -
      toPoly D * ((2 * (derivative (toPoly W) * toPoly D - toPoly W * derivative (toPoly D)) *
        toPoly p + toPoly W * toPoly D * derivative (toPoly p)) * toPoly G.2 +
        2 * toPoly G.1 * (toPoly D * toPoly D))) = 0 := by
    simp only [LD] at hid
    linear_combination (toPoly D * toPoly G.2) * hid + 2 * toPoly D ^ 3 * hG
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hL)

lemma sum_filter_ne_zero {K : Type*} [AddCommMonoid K] (g : ℚ × ℚ → K)
    (hg : ∀ q : ℚ × ℚ, q.2 = 0 → g q = 0) : ∀ l : List (ℚ × ℚ),
    ((l.filter fun q ↦ q.2 ≠ 0).map g).sum = (l.map g).sum
  | [] => rfl
  | q :: t => by
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    split_ifs with h
    · rw [List.map_cons, List.sum_cons, sum_filter_ne_zero g hg t]
    · rw [sum_filter_ne_zero g hg t, hg q (by simpa using h), zero_add]

lemma sum_zip_range {K : Type*} [AddCommMonoid K] (g : ℚ × ℚ → K) : ∀ (αs cs : List ℚ),
    cs.length = αs.length → ((αs.zip cs).map g).sum =
      ∑ k ∈ Finset.range αs.length, g (αs.getD k 0, cs.getD k 0)
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: t, c :: cs, h => by
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons,
      Finset.sum_range_succ', sum_zip_range g t cs (by simpa using h), add_comm]
    rfl

/-- The `fracG` output is the polynomial form of `B₀ + ∑ c_k / (x − α_k)`. -/
lemma fracG_poly (B₀ : CPoly ℚ) (D' : ℕ) (pts : List (ℚ × ℚ × ℤ)) (αs cs : List ℚ)
    (hl : cs.length = αs.length)
    (hpts : (pts.map fun q ↦ ((q.2.2 : ℚ) / D' * q.2.1, q.1)).Perm
      (((αs.zip cs).filter fun q ↦ q.2 ≠ 0).map fun q ↦ (q.2, q.1))) :
    toPoly (fracG B₀ D' pts).2 ≠ 0 ∧
    toPoly (fracG B₀ D' pts).2 * (toPoly B₀ * toPoly (linProd αs) + ∑ k ∈ Finset.range αs.length,
      C (cs.getD k 0) * toPoly (linProd (αs.eraseIdx k))) =
      toPoly (fracG B₀ D' pts).1 * toPoly (linProd αs) := by
  set K := QX
  set x : K := algebraMap ℚ[X] K X
  have hsc : ∀ q : ℚ, algebraMap ℚ[X] K (C q) = (q : K) := fun q ↦ by
    have : (algebraMap ℚ[X] K).comp (C : ℚ →+* ℚ[X]) = algebraMap ℚ K := RingHom.ext_rat _ _
    have h := RingHom.congr_fun this q
    rw [RingHom.comp_apply] at h
    rw [h, eq_ratCast]
  have hav : ∀ Q : ℚ[X], aeval x Q = algebraMap ℚ[X] K Q := fun Q ↦ by
    induction Q using Polynomial.induction_on' with
    | add P Q hP hQ => rw [map_add, map_add, hP, hQ]
    | monomial n a =>
      rw [aeval_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, hsc, eq_ratCast]
  have hinj : Function.Injective (algebraMap ℚ[X] K) := IsFractionRing.injective ℚ[X] K
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hQ ↦ by
    rw [hav]; exact (map_ne_zero_iff _ hinj).mpr hQ
  obtain ⟨h0, hfr⟩ := fracG_spec x hne B₀ D' pts
  refine ⟨h0, ?_⟩
  have hlin : ∀ α : ℚ, x - ((α : ℚ) : K) ≠ 0 := fun α ↦ by
    have := hne _ (X_sub_C_ne_zero α); simpa using this
  -- the sum over `pts` is the sum over all `k`
  have hsum : (pts.map fun q ↦ (((q.2.2 : ℚ) / D' * q.2.1 : ℚ) : K) / (x - ((q.1 : ℚ) : K))).sum =
      ∑ k ∈ Finset.range αs.length, ((cs.getD k 0 : ℚ) : K) / (x - ((αs.getD k 0 : ℚ) : K)) := by
    set g : ℚ × ℚ → K := fun r ↦ ((r.1 : ℚ) : K) / (x - ((r.2 : ℚ) : K))
    have e1 : (pts.map fun q ↦ (((q.2.2 : ℚ) / D' * q.2.1 : ℚ) : K) / (x - ((q.1 : ℚ) : K))) =
        (pts.map fun q ↦ ((q.2.2 : ℚ) / D' * q.2.1, q.1)).map g := by
      rw [List.map_map]; rfl
    rw [e1, (hpts.map g).sum_eq, List.map_map]
    have e2 := sum_filter_ne_zero (g ∘ fun q : ℚ × ℚ ↦ (q.2, q.1))
      (fun q hq ↦ by simp [g, hq]) (αs.zip cs)
    rw [e2, sum_zip_range _ αs cs hl]
    rfl
  have hLk : ∀ k ∈ Finset.range αs.length, aeval x (C (cs.getD k 0)) *
      aeval x (toPoly (linProd (αs.eraseIdx k))) = aeval x (toPoly (linProd αs)) *
        (((cs.getD k 0 : ℚ) : K) / (x - ((αs.getD k 0 : ℚ) : K))) := fun k hk ↦ by
    rw [Finset.mem_range] at hk
    rw [linProd_eraseIdx αs hk, map_mul, map_sub, aeval_X, aeval_C, aeval_C, eq_ratCast,
      eq_ratCast]
    linear_combination (-(((cs.getD k 0 : ℚ) : K) * aeval x (toPoly (linProd (αs.eraseIdx k))))) *
      mul_inv_cancel₀ (hlin (αs.getD k 0))
  apply hinj
  rw [← hav, ← hav]
  have hG0 := hne _ h0
  simp only [map_mul, map_add, map_sum]
  rw [Finset.sum_congr rfl hLk, ← Finset.mul_sum, ← hsum]
  rw [div_eq_iff hG0] at hfr
  have : aeval x (toPoly B₀) + (pts.map fun q ↦ (((q.2.2 : ℚ) / D' * q.2.1 : ℚ) : K) /
      (x - ((q.1 : ℚ) : K))).sum = aeval x (toPoly (fracG B₀ D' pts).1) /
        aeval x (toPoly (fracG B₀ D' pts).2) := by
    rw [eq_div_iff hG0]; exact hfr.symm
  rw [show aeval x (toPoly B₀) * aeval x (toPoly (linProd αs)) + aeval x (toPoly (linProd αs)) *
      (pts.map fun q ↦ (((q.2.2 : ℚ) / D' * q.2.1 : ℚ) : K) / (x - ((q.1 : ℚ) : K))).sum =
      aeval x (toPoly (linProd αs)) * (aeval x (toPoly B₀) + (pts.map fun q ↦
        (((q.2.2 : ℚ) / D' * q.2.1 : ℚ) : K) / (x - ((q.1 : ℚ) : K))).sum) by ring, this]
  linear_combination (aeval x (toPoly (linProd αs)) * aeval x (toPoly (fracG B₀ D' pts).1)) *
    mul_inv_cancel₀ hG0

/-! ### The residue step succeeds -/

lemma zip_map_self {α β : Type*} (f : α → β) : ∀ l : List α, l.zip (l.map f) = l.map fun a ↦ (a, f a)
  | [] => rfl
  | a :: t => by rw [List.map_cons, List.zip_cons_cons, zip_map_self f t, List.map_cons]

lemma dvd_foldr_lcm : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ∣ l.foldr Nat.lcm 1
  | b :: t, a, h => by
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.dvd_lcm_left _ _
    · exact (dvd_foldr_lcm h).trans (Nat.dvd_lcm_right _ _)

lemma foldr_lcm_ne_zero : ∀ l : List ℕ, (∀ a ∈ l, a ≠ 0) → l.foldr Nat.lcm 1 ≠ 0
  | [], _ => one_ne_zero
  | b :: t, h => by
    rw [List.foldr_cons]
    exact Nat.lcm_ne_zero (h b List.mem_cons_self)
      (foldr_lcm_ne_zero t fun a ha ↦ h a (List.mem_cons_of_mem _ ha))

lemma num_mul_of_den_dvd (q : ℚ) (n : ℕ) (h : q.den ∣ n) : (((q * n).num : ℤ) : ℚ) = q * n := by
  obtain ⟨m, hm⟩ := h
  have : q * n = ((q.num * m : ℤ) : ℚ) := by
    rw [hm]
    nth_rewrite 1 [← Rat.num_div_den q]
    push_cast
    have : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    field_simp
  rw [this, Rat.num_intCast]

/-- **The residue step** succeeds when every residue sits over a rational point. -/
lemma residuePts_ok (p : CPoly ℚ) (αs cs : List ℚ)
    (hsq : ∀ q ∈ αs.zip cs, q.2 ≠ 0 → ∃ β : ℚ, β ^ 2 = residuePts.evalQ p q.1 ∧
      residuePts.evalQ p q.1 ≠ 0) :
    ∃ pts D', residuePts p αs cs = some (pts, D') ∧ D' ≠ 0 ∧
      (∀ q ∈ pts, q.2.1 ^ 2 = residuePts.evalQ p q.1 ∧ q.2.1 ≠ 0) ∧
      pts.map Prod.fst = ((αs.zip cs).filter fun q ↦ q.2 ≠ 0).map Prod.fst ∧
      (pts.map fun q ↦ ((q.2.2 : ℚ) / D' * q.2.1, q.1)) =
        ((αs.zip cs).filter fun q ↦ q.2 ≠ 0).map fun q ↦ (q.2, q.1) := by
  set data := (αs.zip cs).filter fun q ↦ q.2 ≠ 0 with hdata
  have hmem : ∀ q ∈ data, q ∈ αs.zip cs ∧ q.2 ≠ 0 := fun q hq ↦ by
    rw [hdata, List.mem_filter] at hq; simpa using hq
  set bf : ℚ × ℚ → ℚ := fun q ↦ (qsqrt (residuePts.evalQ p q.1)).getD 1
  have hbf : ∀ q ∈ data, qsqrt (residuePts.evalQ p q.1) = some (bf q) ∧
      bf q ^ 2 = residuePts.evalQ p q.1 ∧ bf q ≠ 0 := fun q hq ↦ by
    obtain ⟨h1, h2⟩ := hmem q hq
    obtain ⟨β, hβ, hβ0⟩ := hsq q h1 h2
    have hs := qsqrt_sq β
    rw [hβ] at hs
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
    have hb2 := qsqrt_spec hb
    refine ⟨by simp [bf, hb], by simp [bf, hb, hb2], ?_⟩
    simp only [bf, hb, Option.getD_some]
    rintro rfl
    exact hβ0 (by rw [← hb2]; ring)
  set D' := (data.map fun q ↦ (q.2 / bf q).den).foldr Nat.lcm 1 with hD'
  have hD'0 : D' ≠ 0 := foldr_lcm_ne_zero _ fun a ha ↦ by
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; exact Rat.den_ne_zero _
  unfold residuePts
  simp only
  rw [← hdata, if_pos]
  swap
  · rw [List.all_eq_true]
    intro o ho
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
    obtain ⟨h1, -, h3⟩ := hbf q hq
    rw [h1]; simpa using h3
  refine ⟨_, _, rfl, ?_⟩
  rw [zip_map_self, List.map_map, List.map_map]
  simp only [Function.comp_def]
  have hD'eq : ((data.map fun q ↦ (q, qsqrt (residuePts.evalQ p q.1))).map fun q ↦
      (q.1.1, q.2.getD 1, q.1.2 / q.2.getD 1)).map (fun q ↦ q.2.2.den) =
      data.map fun q ↦ (q.2 / bf q).den := by
    simp only [List.map_map, Function.comp_def]; rfl
  simp only [List.map_map, Function.comp_def] at hD'eq
  rw [hD'eq, ← hD']
  simp only [List.map_map, Function.comp_def]
  refine ⟨hD'0, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨-, h2, h3⟩ := hbf r hr
    exact ⟨h2, h3⟩
  · trivial
  · refine List.map_congr_left fun q hq ↦ ?_
    obtain ⟨-, -, h3⟩ := hbf q hq
    have hdvd : (q.2 / bf q).den ∣ D' := dvd_foldr_lcm (List.mem_map_of_mem hq)
    have hq1 : (qsqrt (residuePts.evalQ p q.1)).getD 1 = bf q := rfl
    simp only [hq1, Prod.mk.injEq, and_true]
    rw [num_mul_of_den_dvd _ _ hdvd]
    have : (D' : ℚ) ≠ 0 := by exact_mod_cast hD'0
    field_simp

/-! ### Completeness of `ellDecideGen` -/

lemma ellHermite_eq (p A D : CPoly ℚ) : ellHermite p A D = (ellHermiteRaw p A D).bind fun r ↦
    (residuePts p r.2.2.1 r.2.2.2).map fun s ↦ (r.1, r.2.1, s.1, s.2) := by
  unfold ellHermite ellHermiteRaw
  dsimp only
  split
  · rename_i u hu
    rw [hu, Option.bind_some]
    split <;> simp_all
  · rename_i hu
    rw [hu]; rfl

lemma natDegree_pOf (a b c : ℤ) : (toPoly (pOf a b c)).natDegree = 3 := by
  rw [toPoly_pOf]; compute_degree!

lemma mem_αs {p D : CPoly ℚ} {α : ℚ} (h : α ∈ (ratRootsQ D).dedup.filter (fun α ↦
    residuePts.evalQ D α == 0 && residuePts.evalQ p α != 0)) :
    (toPoly D).eval α = 0 ∧ (toPoly p).eval α ≠ 0 := by
  rw [List.mem_filter] at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, evalQ_eq'] at h
  exact h.2

lemma nodup_data (αs cs : List ℚ) (hnd : αs.Nodup) (hl : cs.length = αs.length) :
    (((αs.zip cs).filter fun q ↦ q.2 ≠ 0).map Prod.fst).Nodup := by
  have : ((αs.zip cs).map Prod.fst) = αs := List.map_fst_zip (by omega)
  refine List.Nodup.sublist ?_ (this ▸ hnd)
  exact (List.filter_sublist).map _

/-- Completeness of `ellDecideGen` given the Hermite output. -/
lemma ellDecideGen_ne_none_of (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (W B₀ : CPoly ℚ) (αs cs : List ℚ)
    (hH : ellHermiteRaw (pOf a b c) A D = some (W, B₀, αs, cs))
    (hres : ∀ q ∈ αs.zip cs, q.2 ≠ 0 → ∃ β : ℚ, β ^ 2 = residuePts.evalQ (pOf a b c) q.1 ∧
      residuePts.evalQ (pOf a b c) q.1 ≠ 0)
    (fuel : ℕ) (hfuel : EllNL.fuelBound a b c ≤ fuel) :
    ellDecideGen a b c A D fuel ≠ none := by
  have hp : toPoly (pOf a b c) = X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) :=
    toPoly_pOf a b c
  have hev : ∀ α : ℚ, residuePts.evalQ (pOf a b c) α = α ^ 3 + a * α ^ 2 + b * α + c := fun α ↦ by
    rw [evalQ_eq', hp]; simp
  obtain ⟨hαs, hl, hid⟩ := ellHermiteRaw_spec _ _ _ _ _ _ _ hD hH
  have hnd : αs.Nodup := hαs ▸ (List.nodup_dedup _).filter _
  obtain ⟨pts, D', hR, hD'0, hon, hfst, hres⟩ := residuePts_ok (pOf a b c) αs cs hres
  have hHerm : ellHermite (pOf a b c) A D = some (W, B₀, pts, D') := by
    rw [ellHermite_eq, hH]; simp [hR]
  obtain ⟨hG2, hG⟩ := fracG_poly B₀ D' pts αs cs hl (hres ▸ List.Perm.refl _)
  have hchk := genCheck_of_poly (pOf a b c) A D W B₀ (fracG B₀ D' pts) αs cs hD hG2 hid hG
  unfold ellDecideGen
  rw [hHerm]
  dsimp only
  rw [if_pos hchk]
  refine ellDecide_ne_none a b c hsq B₀ pts (fun q hq ↦ ?_) ?_ D' hD'0 fuel hfuel
  · obtain ⟨h1, h2⟩ := hon q hq
    exact ⟨by rw [h1, hev], h2⟩
  · rw [hfst]; exact nodup_data αs cs hnd hl

lemma evalQ_pOf (a b c : ℤ) (α : ℚ) :
    residuePts.evalQ (pOf a b c) α = α ^ 3 + a * α ^ 2 + b * α + c := by
  rw [evalQ_eq', toPoly_pOf]; simp

lemma sq_pOf (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ))) :
    Squarefree (toPoly (pOf a b c)) ∧ 1 ≤ (toPoly (pOf a b c)).natDegree :=
  ⟨by rw [toPoly_pOf]; exact hsq, by rw [natDegree_pOf]; omega⟩

/-- **Completeness of `ellDecideGen`**: for a split denominator whose roots `α` (off the branch
points) all lie under rational points of `y² = p(x)`, the procedure answers with
`fuelBound` fuel. -/
theorem ellDecideGen_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (hrat : ∀ α : ℚ, (toPoly D).eval α = 0 → α ^ 3 + a * α ^ 2 + b * α + c ≠ 0 →
      ∃ β : ℚ, β ^ 2 = α ^ 3 + a * α ^ 2 + b * α + c)
    (fuel : ℕ) (hfuel : EllNL.fuelBound a b c ≤ fuel) :
    ellDecideGen a b c A D fuel ≠ none := by
  obtain ⟨hsqP, hp1⟩ := sq_pOf a b c hsq
  obtain ⟨⟨W, B₀, αs, cs⟩, hH⟩ := Option.ne_none_iff_exists'.mp
    (ellHermiteRaw_ne_none (pOf a b c) A D hsqP hp1 hD hsplit)
  obtain ⟨hαs, -, -⟩ := ellHermiteRaw_spec _ _ _ _ _ _ _ hD hH
  refine ellDecideGen_ne_none_of a b c hsq A D hD W B₀ αs cs hH (fun q hq _ ↦ ?_) fuel hfuel
  have hα := List.of_mem_zip hq
  obtain ⟨h1, h2⟩ := mem_αs (hαs ▸ hα.1)
  rw [← evalQ_eq', evalQ_pOf] at h2
  obtain ⟨β, hβ⟩ := hrat q.1 h1 h2
  exact ⟨β, by rw [evalQ_pOf]; exact hβ, by rw [evalQ_pOf]; exact h2⟩

section Decision

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem for `∫ A / (D √p)`** (`p = x³ + ax² + bx + c` squarefree, `D` split over
`ℚ`, every root `α` of `D` off the branch points under a rational point): `ellDecideGen` answers
`some b`, and `b = true` iff the integral is elementary. -/
theorem ellDecideGen_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (hrat : ∀ α : ℚ, (toPoly D).eval α = 0 → α ^ 3 + a * α ^ 2 + b * α + c ≠ 0 →
      ∃ β : ℚ, β ^ 2 = α ^ 3 + a * α ^ 2 + b * α + c) :
    ∃ ans : Bool, ellDecideGen a b c A D (EllNL.fuelBound a b c) = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp
    (ellDecideGen_ne_none a b c hsq A D hD hsplit hrat _ le_rfl)
  exact ⟨ans, hans, ellDecideGen_spec hC hCall x y hx a b c hsq hy hgen A D _ ans hans⟩

end Decision

end EllAlgo
