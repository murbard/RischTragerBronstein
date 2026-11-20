import RischTragerBronstein.Algebraic.EllAlgo

/-!
# Semantics of the solver `ellSolve`

* `toPoly_shiftPoly`: `shiftPoly p α = p(X + α)`;
* `sqrtSeries_spec`: `Y = sqrtSeries pt y₀ m` has `Y(0) = y₀` and `tᵐ ∣ pt − Y²`
  (when `pt(0) = y₀² ≠ 0`), and `sqrtSeries … (m + 1) ≡ sqrtSeries … m (mod tᵐ)`;
* `lcomb_cols`: a relation `w` among the columns means exactly that `A + B Y_q ≡ 0 (mod t^{m_q})`
  at every point `q` after the shift `x = α_q + t`, with `A = w[..na]`, `B = w[na..]`.
-/

open Polynomial

namespace EllAlgo

open CPoly

variable {K : Type*} [Field K] [DecidableEq K]

lemma toPoly_shiftPoly (α : K) : ∀ p : CPoly K, toPoly (shiftPoly p α) = (toPoly p).comp (X + C α)
  | [] => by simp [shiftPoly]
  | c :: p => by
    have ih := toPoly_shiftPoly α p
    simp only [shiftPoly, List.foldr_cons] at ih ⊢
    rw [toPoly_add, toPoly_mul, ih]
    simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero, map_one, add_comp, mul_comp, C_comp,
      X_comp]
    ring

/-! ### The Hensel lift -/

lemma sqrtSeries_succ (pt : CPoly K) (y₀ : K) (m : ℕ) (hm : 1 ≤ m) :
    sqrtSeries pt y₀ (m + 1) = sqrtStep pt y₀ (sqrtSeries pt y₀ m) m := by
  unfold sqrtSeries
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma toPoly_sqrtStep (pt : CPoly K) (y₀ : K) (Y : CPoly K) (k : ℕ) :
    toPoly (sqrtStep pt y₀ Y k) = toPoly Y +
      C ((toPoly pt - toPoly Y ^ 2).coeff k / (2 * y₀)) * X ^ k := by
  unfold sqrtStep
  rw [toPoly_add, toPoly_monomial, ← coeff_toPoly, toPoly_sub, toPoly_mul, sq]

lemma coeff_zero_sqrtSeries (pt : CPoly K) (y₀ : K) :
    ∀ m, (toPoly (sqrtSeries pt y₀ m)).coeff 0 = y₀
  | 0 => by simp [sqrtSeries]
  | 1 => by simp [sqrtSeries]
  | m + 2 => by
    rw [sqrtSeries_succ pt y₀ (m + 1) (by omega), toPoly_sqrtStep, coeff_add,
      coeff_zero_sqrtSeries pt y₀ (m + 1), coeff_C_mul, coeff_X_pow]
    simp

/-- **The Hensel lift is a square root mod `tᵐ`.** -/
lemma sqrtSeries_dvd [CharZero K] (pt : CPoly K) (y₀ : K) (hy₀ : y₀ ≠ 0) (h0 : (toPoly pt).coeff 0 = y₀ ^ 2) :
    ∀ m, 1 ≤ m → X ^ m ∣ toPoly pt - toPoly (sqrtSeries pt y₀ m) ^ 2
  | 0, h => by omega
  | 1, _ => by
    simp only [sqrtSeries, Nat.sub_self, List.range_zero, List.map_nil, List.foldl_nil,
      toPoly_cons, toPoly_nil, mul_zero, add_zero, pow_one]
    rw [X_dvd_iff, coeff_sub, h0, ← map_pow, coeff_C_zero, sub_self]
  | m + 2, _ => by
    have ih := sqrtSeries_dvd pt y₀ hy₀ h0 (m + 1) (by omega)
    rw [sqrtSeries_succ pt y₀ (m + 1) (by omega), toPoly_sqrtStep]
    set Y := toPoly (sqrtSeries pt y₀ (m + 1))
    obtain ⟨Q, hQ⟩ := ih
    have hY0 : Y.coeff 0 = y₀ := coeff_zero_sqrtSeries pt y₀ (m + 1)
    have he : (toPoly pt - Y ^ 2).coeff (m + 1) = Q.coeff 0 := by
      rw [hQ, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    rw [he]
    set c := Q.coeff 0 / (2 * y₀)
    have hc : Q.coeff 0 - 2 * c * y₀ = 0 := by
      simp only [c]; field_simp; ring
    have e : toPoly pt - (Y + C c * X ^ (m + 1)) ^ 2 =
        X ^ (m + 1) * (Q - 2 * C c * Y - C c ^ 2 * X ^ (m + 1)) := by
      linear_combination hQ
    rw [e, pow_succ]
    refine mul_dvd_mul_left _ ?_
    rw [X_dvd_iff]
    have h1 : (2 * C c * Y).coeff 0 = 2 * c * y₀ := by
      rw [show (2 : K[X]) * C c * Y = C (2 * c) * Y by rw [C_mul, map_ofNat], coeff_C_mul, hY0]
    have h2 : (C c ^ 2 * X ^ (m + 1)).coeff 0 = 0 := by
      rw [← map_pow, coeff_C_mul, coeff_X_pow]; simp
    rw [coeff_sub, coeff_sub, h1, h2]
    linear_combination hc

/-- Consecutive lifts agree mod `tᵐ`. -/
lemma sqrtSeries_succ_sub (pt : CPoly K) (y₀ : K) (m : ℕ) (hm : 1 ≤ m) :
    X ^ m ∣ toPoly (sqrtSeries pt y₀ (m + 1)) - toPoly (sqrtSeries pt y₀ m) := by
  rw [sqrtSeries_succ pt y₀ m hm, toPoly_sqrtStep, add_sub_cancel_left]
  exact dvd_mul_left _ _

/-! ### Truncation and the block structure of the columns -/

/-- `f mod Xᵐ`. -/
noncomputable def trunc (m : ℕ) (f : K[X]) : K[X] := ∑ k ∈ Finset.range m, C (f.coeff k) * X ^ k

lemma coeff_trunc (m : ℕ) (f : K[X]) (k : ℕ) : (trunc m f).coeff k = if k < m then f.coeff k else 0 := by
  simp only [trunc, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with hk
  · rw [Finset.sum_eq_single k (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp [hk])]; simp
  · exact Finset.sum_eq_zero fun b hb ↦ by
      simp only [Finset.mem_range] at hb; simp [show k ≠ b by omega]

lemma trunc_add (m : ℕ) (f g : K[X]) : trunc m (f + g) = trunc m f + trunc m g := by
  ext k; simp only [coeff_add, coeff_trunc]; split_ifs <;> simp

lemma trunc_C_mul (m : ℕ) (c : K) (f : K[X]) : trunc m (C c * f) = C c * trunc m f := by
  ext k; simp only [coeff_C_mul, coeff_trunc]; split_ifs <;> simp

lemma trunc_zero (m : ℕ) : trunc m (0 : K[X]) = 0 := by ext k; simp [coeff_trunc]

lemma trunc_eq_zero_iff (m : ℕ) (f : K[X]) : trunc m f = 0 ↔ X ^ m ∣ f := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h d hd
    have := congrArg (fun g ↦ g.coeff d) h
    simpa [coeff_trunc, hd] using this
  · intro h; ext k; rw [coeff_trunc]; split_ifs with hk
    · simp [h k hk]
    · simp

lemma natDegree_trunc_lt (m : ℕ) (f : K[X]) (k : ℕ) (hk : m ≤ k) : (trunc m f).coeff k = 0 := by
  rw [coeff_trunc, if_neg (by omega)]

lemma length_padTo (m : ℕ) (l : CPoly K) : (padTo m l).length = m := by
  simp only [padTo, List.length_append, List.length_take, List.length_replicate]; omega

lemma toPoly_padTo (m : ℕ) (l : CPoly K) : toPoly (padTo m l) = trunc m (toPoly l) := by
  ext k
  rw [coeff_toPoly, coeff_trunc, coeff_toPoly]
  unfold padTo
  split_ifs with hk
  · rcases Nat.lt_or_ge k l.length with hl | hl
    · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt hk, ← List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_default _ _ hl]
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_take]
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> simp
  · rw [List.getD_eq_default]
    simp only [List.length_append, List.length_take, List.length_replicate]; omega

/-- `∑ wⱼ vⱼ` as a polynomial. -/
lemma lcomb_nil_right (w : List K) : lcomb w ([] : List (CPoly K)) = 0 := by
  simp [lcomb]

lemma lcomb_cons_cons (c : K) (w : List K) (v : CPoly K) (vs : List (CPoly K)) :
    lcomb (c :: w) (v :: vs) = C c * toPoly v + lcomb w vs := by
  simp [lcomb]

lemma lcomb_nil_left (vs : List (CPoly K)) : lcomb [] vs = 0 := by
  simp [lcomb]

/-- Block decomposition of a relation. -/
lemma lcomb_block {ι' : Type*} (m : ℕ) (f g : ι' → CPoly K) :
    ∀ (L : List ι') (w : List K), lcomb w (L.map fun i ↦ padTo m (f i) ++ g i) =
      trunc m (lcomb w (L.map f)) + X ^ m * lcomb w (L.map g)
  | [], w => by simp [lcomb_nil_right, trunc_zero]
  | i :: L, [] => by simp [lcomb_nil_left, trunc_zero]
  | i :: L, c :: w => by
    simp only [List.map_cons, lcomb_cons_cons, lcomb_block m f g L w, toPoly_append,
      length_padTo, toPoly_padTo, trunc_add, trunc_C_mul]
    ring

/-- Linearity over an append of index lists. -/
lemma lcomb_append (w : List K) (L₁ L₂ : List (CPoly K)) :
    lcomb w (L₁ ++ L₂) = lcomb (w.take L₁.length) L₁ + lcomb (w.drop L₁.length) L₂ := by
  induction L₁ generalizing w with
  | nil => simp [lcomb_nil_right]
  | cons v L₁ ih =>
    cases w with
    | nil => simp [lcomb_nil_left]
    | cons c w =>
      simp only [List.cons_append, lcomb_cons_cons, List.length_cons, List.take_succ_cons,
        List.drop_succ_cons, ih]
      ring

/-- `∑ⱼ wⱼ (xʲ ∘ φ) · Y = (∑ wⱼ xʲ) ∘ φ · Y`. -/
lemma lcomb_range_comp (φ Y : K[X]) (f : ℕ → CPoly K) (hf : ∀ j, toPoly (f j) = (X ^ j).comp φ * Y) :
    ∀ (n : ℕ) (w : List K), lcomb w ((List.range n).map f) = (toPoly (w.take n)).comp φ * Y := by
  intro n
  induction n with
  | zero => intro w; simp [lcomb_nil_right]
  | succ n ih =>
    intro w
    rw [List.range_succ, List.map_append, lcomb_append, ih, List.length_map, List.length_range]
    rcases Nat.lt_or_ge n w.length with hn | hn
    · have hd : w.drop n = w[n] :: w.drop (n + 1) := List.drop_eq_getElem_cons hn
      rw [hd, List.map_singleton, lcomb_cons_cons, lcomb_nil_right, hf,
        List.take_succ, List.getElem?_eq_getElem hn, toPoly_append]
      simp only [List.length_take, Option.toList_some, toPoly_cons, toPoly_nil, mul_zero,
        add_zero, add_comp, mul_comp, C_comp, min_eq_left hn.le, List.take_take, min_self]
      ring
    · rw [List.drop_eq_nil_of_le hn, lcomb_nil_left, add_zero]
      simp only [List.take_of_length_le hn, List.take_of_length_le (show w.length ≤ n + 1 by omega)]

/-- The local expansion `Y_q` of `y` at the point `q = (α, y₀, m)`. -/
def Yq (p : CPoly K) (q : K × K × ℕ) : CPoly K := sqrtSeries (shiftPoly p q.1) q.2.1 q.2.2

/-- The value of `A + B y` at the point `q` (shifted, untruncated). -/
noncomputable def locVal (p : CPoly K) (A B : K[X]) (q : K × K × ℕ) : K[X] :=
  A.comp (X + C q.1) + B.comp (X + C q.1) * toPoly (Yq p q)

lemma lcomb_idx (p : CPoly K) (q : K × K × ℕ) (na nb : ℕ) (w : List K) :
    lcomb w ((ellIdx na nb).map fun bj ↦
      if bj.1 then mul (shiftPoly (monomial bj.2 1) q.1) (Yq p q)
      else shiftPoly (monomial bj.2 1) q.1) =
      locVal p (toPoly (w.take na)) (toPoly ((w.drop na).take nb)) q := by
  unfold ellIdx locVal
  rw [List.map_append, lcomb_append, List.map_map, List.map_map, List.length_map,
    List.length_range]
  have h1 := lcomb_range_comp (X + C q.1) 1
    ((fun bj : Bool × ℕ ↦ if bj.1 then mul (shiftPoly (monomial bj.2 1) q.1) (Yq p q)
      else shiftPoly (monomial bj.2 1) q.1) ∘ fun j ↦ (false, j))
    (fun j ↦ by simp [toPoly_shiftPoly]) na (w.take na)
  have h2 := lcomb_range_comp (X + C q.1) (toPoly (Yq p q))
    ((fun bj : Bool × ℕ ↦ if bj.1 then mul (shiftPoly (monomial bj.2 1) q.1) (Yq p q)
      else shiftPoly (monomial bj.2 1) q.1) ∘ fun j ↦ (true, j))
    (fun j ↦ by simp [toPoly_shiftPoly]) nb (w.drop na)
  rw [h1, h2, List.take_take, min_self, mul_one]

lemma colOf_cons (p : CPoly K) (q : K × K × ℕ) (rest : List (K × K × ℕ)) (isB : Bool) (j : ℕ) :
    colOf p (q :: rest) isB j = padTo q.2.2 (if isB then
      mul (shiftPoly (monomial j 1) q.1) (Yq p q) else shiftPoly (monomial j 1) q.1) ++
      colOf p rest isB j := by
  simp only [colOf, List.map_cons, List.flatten_cons, Yq]

lemma trunc_add_X_pow_eq_zero (m : ℕ) (T R : K[X]) :
    trunc m T + X ^ m * R = 0 ↔ trunc m T = 0 ∧ R = 0 := by
  constructor
  · intro h
    have hT : trunc m T = 0 := by
      ext k
      have := congrArg (fun g ↦ g.coeff k) h
      simp only [coeff_add, coeff_X_pow_mul', coeff_zero] at this
      rw [coeff_zero]
      rcases Nat.lt_or_ge k m with hk | hk
      · rw [if_neg (by omega), add_zero] at this; exact this
      · exact natDegree_trunc_lt m T k hk
    refine ⟨hT, ?_⟩
    rw [hT, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ X_ne_zero)
  · rintro ⟨h1, h2⟩; rw [h1, h2]; ring

/-- **The linear system means local vanishing.** -/
theorem lcomb_ellCols (p : CPoly K) (na nb : ℕ) (w : List K) :
    ∀ pts : List (K × K × ℕ), lcomb w (ellCols p pts na nb) = 0 ↔
      ∀ q ∈ pts, X ^ q.2.2 ∣ locVal p (toPoly (w.take na)) (toPoly ((w.drop na).take nb)) q
  | [] => by
    simp only [ellCols, colOf, List.map_nil, List.flatten_nil, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, iff_true]
    unfold lcomb
    induction (ellIdx na nb) generalizing w with
    | nil => simp
    | cons bj L ih =>
      cases w with
      | nil => simp
      | cons c w => simpa using ih w
  | q :: rest => by
    have e : ellCols p (q :: rest) na nb = (ellIdx na nb).map fun bj ↦
        padTo q.2.2 ((fun bj : Bool × ℕ ↦ if bj.1 then
          mul (shiftPoly (monomial bj.2 1) q.1) (Yq p q) else shiftPoly (monomial bj.2 1) q.1) bj) ++
          (fun bj : Bool × ℕ ↦ colOf p rest bj.1 bj.2) bj := by
      simp only [ellCols, colOf_cons]
    rw [e, lcomb_block, lcomb_idx, trunc_add_X_pow_eq_zero, trunc_eq_zero_iff]
    have ih := lcomb_ellCols p na nb w rest
    simp only [ellCols] at ih
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]

end EllAlgo
