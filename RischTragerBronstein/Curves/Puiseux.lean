import RischTragerBronstein.Algebraic.LocalExpansion
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The Newton–Puiseux theorem

Over an algebraically closed field `K` of characteristic zero, every monic polynomial over `K⟦X⟧`
splits into linear factors after the substitution `X ↦ Xᴺ` for some `N ≥ 1`
(`puiseux_split`). This is the local theory of algebraic curves: the branches of `F(x, y) = 0`
over `x = a` are the roots of `F(a + Tᴺ, y)` in `K⟦T⟧`.

* `hensel_simple`: Hensel's lemma for **non-monic** polynomials over `K⟦X⟧` (a simple root modulo
  `X` lifts), by rescaling and reversing into a monic polynomial.
* `exists_root_mult`: a root of multiplicity `m` of the reduction lifts to a root after some
  `X ↦ Xᴺ` (induction on `m`: Hensel on the `(m−1)`-th derivative kills the `Zᵐ⁻¹` coefficient,
  then the first edge of the Newton polygon gives `X = Tᵠ`, `Z = Tᵖ W`, whose edge polynomial has
  a non-zero root of smaller multiplicity).
-/

open PowerSeries

namespace Puiseux

variable {K : Type*} [Field K]

/-- The reduction of a polynomial over `K⟦X⟧` modulo `X`. -/
noncomputable def red (H : Polynomial K⟦X⟧) : Polynomial K := H.map (constantCoeff (R := K))

section Hensel

lemma mem_span_X_iff (f : K⟦X⟧) : f ∈ Ideal.span {(X : K⟦X⟧)} ↔ constantCoeff f = 0 := by
  rw [Ideal.mem_span_singleton, X_dvd_iff]

/-- **Hensel's lemma for non-monic polynomials over `K⟦X⟧`.** -/
theorem hensel_simple (f : Polynomial K⟦X⟧) (a₀ : K⟦X⟧)
    (h₁ : constantCoeff (f.eval a₀) = 0) (h₂ : constantCoeff (f.derivative.eval a₀) ≠ 0) :
    ∃ a : K⟦X⟧, f.eval a = 0 ∧ constantCoeff a = constantCoeff a₀ := by
  classical
  set g := Polynomial.taylor a₀ f with hg
  set u := g.coeff 0 with hu
  set v := g.coeff 1 with hv
  have hu0 : constantCoeff u = 0 := by rw [hu, hg, Polynomial.taylor_coeff_zero]; exact h₁
  have hv0 : constantCoeff v ≠ 0 := by rw [hv, hg, Polynomial.taylor_coeff_one]; exact h₂
  by_cases hu' : u = 0
  · refine ⟨a₀, ?_, rfl⟩
    rw [← Polynomial.taylor_coeff_zero]; exact hu'
  set N := g.natDegree with hN
  have hN1 : 1 ≤ N := by
    by_contra h
    have : g.coeff 1 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    apply hv0; rw [hv, this, map_zero]
  -- `g(u w) = u Q(w)`
  set Q : Polynomial K⟦X⟧ := ∑ i ∈ Finset.range (N + 1),
    Polynomial.C (if i = 0 then 1 else g.coeff i * u ^ (i - 1)) * Polynomial.X ^ i with hQ
  have hQcoeff : ∀ i, Q.coeff i = if i ≤ N then (if i = 0 then 1 else g.coeff i * u ^ (i - 1))
      else 0 := by
    intro i
    rw [hQ, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]
  have hgQ : ∀ w, g.eval (u * w) = u * Q.eval w := by
    intro w
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range' (n := N + 1)]
    · rw [Finset.mul_sum, Finset.sum_range_succ', Finset.sum_range_succ' (fun i ↦ u * _)]
      congr 1
      · refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [hQcoeff, if_pos (by rw [Finset.mem_range] at hi; omega), if_neg (by omega)]
        simp only [Nat.add_sub_cancel]
        ring
      · rw [hQcoeff, if_pos (by omega), if_pos rfl, ← hu]; ring
    · refine lt_of_le_of_lt (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_)
        (Nat.lt_succ_self N)
      rw [hQcoeff, if_neg (by exact_mod_cast not_le.mpr hi)]
  have hQdeg : Q.natDegree ≤ N := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
    rw [hQcoeff, if_neg (by exact_mod_cast not_le.mpr hi)]
  set v₀ := constantCoeff v with hv₀
  -- the reduction of `Q` is `v₀ X + 1`
  have hredQ : Q.map (constantCoeff (R := K)) =
      Polynomial.C v₀ * Polynomial.X ^ 1 + Polynomial.C 1 * Polynomial.X ^ 0 := by
    ext i
    rw [Polynomial.coeff_map, hQcoeff]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · simp
      · simp [if_pos hN1, hv₀, hv]
    · split_ifs <;> first | omega | simp [map_mul, map_pow, hu0, zero_pow (by omega : i - 1 ≠ 0)]
  set R := Polynomial.reflect N Q with hR
  have hRmon : R.Monic := by
    refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one N
      (le_trans Polynomial.natDegree_reflect_le (max_le le_rfl hQdeg)) ?_
    rw [hR, Polynomial.coeff_reflect, Polynomial.revAt_le le_rfl, Nat.sub_self, hQcoeff,
      if_pos (Nat.zero_le _), if_pos rfl]
  have hredR : R.map (constantCoeff (R := K)) =
      Polynomial.X ^ (N - 1) * (Polynomial.X + Polynomial.C v₀) := by
    rw [hR, ← Polynomial.reflect_map, hredQ, Polynomial.reflect_add,
      Polynomial.reflect_C_mul_X_pow, Polynomial.reflect_C_mul_X_pow,
      Polynomial.revAt_le hN1, Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero]
    have hXN : (Polynomial.X : Polynomial K) ^ N = Polynomial.X ^ (N - 1) * Polynomial.X := by
      rw [← pow_succ, Nat.sub_add_cancel hN1]
    simp only [map_one, one_mul, hXN]
    ring
  have hcc : ∀ (P : Polynomial K⟦X⟧) (t : K⟦X⟧),
      constantCoeff (P.eval t) = (P.map (constantCoeff (R := K))).eval (constantCoeff t) := by
    intro P t
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  set a0 : K⟦X⟧ := PowerSeries.C (-v₀) with ha0
  have hH1 : R.eval a0 ∈ Ideal.span {(X : K⟦X⟧)} := by
    rw [mem_span_X_iff, hcc, hredR, ha0, constantCoeff_C]
    simp
  have hH2 : IsUnit (Ideal.Quotient.mk (Ideal.span {(X : K⟦X⟧)}) (R.derivative.eval a0)) := by
    refine IsUnit.map _ ?_
    refine IsUnit.of_mul_eq_one (R.derivative.eval a0)⁻¹ (PowerSeries.mul_inv_cancel _ ?_)
    rw [hcc, ← Polynomial.derivative_map, hredR, ha0, constantCoeff_C]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_X,
      Polynomial.derivative_C, add_zero, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_one, neg_add_cancel,
      mul_zero, zero_add, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr hv0)
  obtain ⟨t, ht, hta⟩ := HenselianRing.is_henselian R hRmon a0 hH1 hH2
  have ht0 : constantCoeff t = -v₀ := by
    rw [mem_span_X_iff, map_sub, sub_eq_zero, ha0, constantCoeff_C] at hta; exact hta
  have ht0' : constantCoeff t ≠ 0 := by rw [ht0]; exact neg_ne_zero.mpr hv0
  set w := t⁻¹ with hw
  letI : Invertible w := ⟨t, by rw [hw, PowerSeries.mul_inv_cancel _ ht0'],
    by rw [hw, mul_comm, PowerSeries.mul_inv_cancel _ ht0']⟩
  have hQw : Q.eval w = 0 := by
    have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id _) w N Q hQdeg
    have hinv : (⅟w : K⟦X⟧) = t := rfl
    rw [hinv, ← hR] at h
    rw [Polynomial.eval, ← h, ← Polynomial.eval]
    rw [Polynomial.IsRoot.def] at ht
    rw [ht, zero_mul]
  refine ⟨u * w + a₀, ?_, ?_⟩
  · rw [← Polynomial.taylor_eval, ← hg, hgQ, hQw, mul_zero]
  · rw [map_add, map_mul, hu0, zero_mul, zero_add]

end Hensel

section Aux

/-- `f / Xᵏ` (exact when the first `k` coefficients vanish). -/
noncomputable def divXPow (k : ℕ) (f : K⟦X⟧) : K⟦X⟧ := mk fun j ↦ coeff (j + k) f

lemma coeff_divXPow (k j : ℕ) (f : K⟦X⟧) : coeff j (divXPow k f) = coeff (j + k) f :=
  coeff_mk _ _

lemma divXPow_zero (k : ℕ) : divXPow k (0 : K⟦X⟧) = 0 := by
  ext j; rw [coeff_divXPow, map_zero, map_zero]

lemma X_pow_mul_divXPow (k : ℕ) (f : K⟦X⟧) (h : ∀ j < k, coeff j f = 0) :
    X ^ k * divXPow k f = f := by
  ext n
  rw [coeff_X_pow_mul']
  split_ifs with hn
  · rw [coeff_divXPow, Nat.sub_add_cancel hn]
  · exact (h n (by omega)).symm

/-- The substitution `X ↦ Xᴺ` (the identity for `N = 0`). -/
noncomputable def ex (N : ℕ) : K⟦X⟧ →+* K⟦X⟧ :=
  if h : N = 0 then RingHom.id _ else (expand N h).toRingHom

lemma ex_apply {N : ℕ} (h : N ≠ 0) (f : K⟦X⟧) : ex N f = expand N h f := by
  simp [ex, h]

lemma ex_one (f : K⟦X⟧) : ex 1 f = f := by rw [ex_apply one_ne_zero, expand_one_apply]

lemma ex_ex {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (f : K⟦X⟧) : ex a (ex b f) = ex (a * b) f := by
  rw [ex_apply ha, ex_apply hb, ex_apply (mul_ne_zero ha hb), expand_mul]

lemma ex_C (N : ℕ) (c : K) : ex N (C c) = C c := by
  by_cases h : N = 0
  · simp [ex, h]
  · rw [ex_apply h, expand_C]

lemma constantCoeff_ex (N : ℕ) (f : K⟦X⟧) : constantCoeff (ex N f) = constantCoeff f := by
  by_cases h : N = 0
  · simp [ex, h]
  · rw [ex_apply h, constantCoeff_expand]

lemma map_ex_ex {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (H : Polynomial K⟦X⟧) :
    (H.map (ex b)).map (ex a) = H.map (ex (a * b)) := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext fun f ↦ ex_ex ha hb f

lemma map_ex_one (H : Polynomial K⟦X⟧) : H.map (ex 1) = H := by
  rw [show (ex 1 : K⟦X⟧ →+* K⟦X⟧) = RingHom.id _ from RingHom.ext ex_one, Polynomial.map_id]

lemma cc_eval (P : Polynomial K⟦X⟧) (t : K⟦X⟧) :
    constantCoeff (P.eval t) = (P.map (constantCoeff (R := K))).eval (constantCoeff t) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

lemma eval_scale {A : Type*} [CommRing A] (P G : Polynomial A) (s t w : A)
    (h : ∀ i, P.coeff i * s ^ i = t * G.coeff i) : P.eval (s * w) = t * G.eval w := by
  rw [Polynomial.eval_eq_sum_range' (n := max P.natDegree G.natDegree + 1) (by omega),
    Polynomial.eval_eq_sum_range' (p := G) (n := max P.natDegree G.natDegree + 1) (by omega),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_pow, ← mul_assoc, h i, mul_assoc]

end Aux

section NewtonPuiseux

variable [IsAlgClosed K] [CharZero K]

/-- **Newton–Puiseux, local step.** If the reduction of `H` has `0` as a root of multiplicity
exactly `m ≥ 1`, then after some substitution `X ↦ Xᴺ`, `H` has a root in `X K⟦X⟧`. -/
theorem exists_root_mult (m : ℕ) : ∀ (H : Polynomial K⟦X⟧), 1 ≤ m →
    (∀ i < m, constantCoeff (H.coeff i) = 0) → constantCoeff (H.coeff m) ≠ 0 →
    ∃ N, N ≠ 0 ∧ ∃ r : K⟦X⟧, (H.map (ex N)).eval r = 0 ∧ constantCoeff r = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro H hm hlow hm0
  classical
  -- kill the coefficient of `Zᵐ⁻¹` (Hensel on the `(m-1)`-th Hasse derivative)
  obtain ⟨b, hb, hb0⟩ := hensel_simple (Polynomial.hasseDeriv (m - 1) H) 0 (by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.hasseDeriv_coeff, zero_add,
        Nat.choose_self, Nat.cast_one, one_mul]
      exact hlow _ (by omega)) (by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
        Polynomial.hasseDeriv_coeff, show 1 + (m - 1) = m by omega, Nat.cast_zero, zero_add,
        mul_one, map_mul, map_natCast]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne') hm0)
  have hb0' : constantCoeff b = 0 := by rw [hb0, map_zero]
  set H' := Polynomial.taylor b H with hH'
  have hH'm1 : H'.coeff (m - 1) = 0 := by rw [hH', Polynomial.taylor_coeff]; exact hb
  have hred : ∀ i, constantCoeff (H'.coeff i) = constantCoeff (H.coeff i) := by
    intro i
    rw [← Polynomial.coeff_map, hH', Polynomial.map_taylor, hb0', Polynomial.taylor_zero,
      Polynomial.coeff_map]
  have htr : ∀ N r, (H'.map (ex N)).eval r = 0 → (H.map (ex N)).eval (r + ex N b) = 0 := by
    intro N r h
    rw [hH', Polynomial.map_taylor, Polynomial.taylor_eval] at h
    exact h
  have hccr : ∀ N r, constantCoeff r = 0 → constantCoeff (r + ex N b) = 0 := by
    intro N r h
    rw [map_add, h, constantCoeff_ex, hb0', add_zero]
  by_cases hall : ∀ i < m, H'.coeff i = 0
  · refine ⟨1, one_ne_zero, 0 + ex 1 b, htr 1 0 ?_, hccr 1 0 (map_zero _)⟩
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, hall 0 (by omega), map_zero]
  push Not at hall
  -- the first edge of the Newton polygon
  set S := (Finset.range m).filter (fun i ↦ H'.coeff i ≠ 0) with hSdef
  have hS : S.Nonempty := by
    obtain ⟨i, hi, h⟩ := hall
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, h⟩⟩
  set ord : ℕ → ℕ := fun i ↦ (H'.coeff i).order.toNat with hord
  obtain ⟨i0, hi0S, hi0min⟩ := S.exists_min_image (fun i ↦ (ord i : ℚ) / ((m : ℚ) - i)) hS
  obtain ⟨hi0m', hi0ne⟩ := Finset.mem_filter.mp hi0S
  have hi0m : i0 < m := Finset.mem_range.mp hi0m'
  set p := ord i0 with hp
  set q := m - i0 with hq
  have hi0m1 : i0 ≠ m - 1 := fun h ↦ hi0ne (by rw [h]; exact hH'm1)
  have hq0 : q ≠ 0 := by omega
  have hp1 : 1 ≤ p := by
    by_contra h
    have h0 : p = 0 := by omega
    have := coeff_order hi0ne
    have h0' : (H'.coeff i0).order.toNat = 0 := h0
    rw [h0', coeff_zero_eq_constantCoeff_apply, hred, hlow _ hi0m] at this
    exact this rfl
  have hmin : ∀ i < m, H'.coeff i ≠ 0 → p * (m - i) ≤ q * ord i := by
    intro i hi hne
    have h := hi0min i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hne⟩)
    have e1 : ((m : ℚ) - i) = ((m - i : ℕ) : ℚ) := by rw [Nat.cast_sub hi.le]
    have e2 : ((m : ℚ) - i0) = ((m - i0 : ℕ) : ℚ) := by rw [Nat.cast_sub hi0m.le]
    rw [e1, e2, div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < m - i0))
      (by exact_mod_cast (by omega : 0 < m - i))] at h
    have h' : ord i0 * (m - i) ≤ ord i * (m - i0) := by exact_mod_cast h
    rw [← hp, ← hq] at h'
    linarith
  -- the coefficients of `H'(T^q, T^p W)`
  set c : ℕ → K⟦X⟧ := fun i ↦ ex q (H'.coeff i) * X ^ (p * i) with hc
  have hlb : ∀ i, ∀ j < p * m, coeff j (c i) = 0 := by
    intro i j hj
    simp only [hc]
    rw [coeff_mul_X_pow']
    split_ifs with hij
    · have him : i < m := by
        by_contra h
        push Not at h
        have := Nat.mul_le_mul_left p h
        omega
      by_cases hne : H'.coeff i = 0
      · rw [hne, map_zero, map_zero]
      rw [ex_apply hq0, coeff_expand]
      split_ifs with hdvd
      · apply coeff_of_lt_order_toNat
        obtain ⟨k, hk⟩ := hdvd
        have hmi := hmin i him hne
        rw [hk, Nat.mul_div_cancel_left _ (by omega)]
        have e : p * (m - i) + p * i = p * m := by rw [← Nat.mul_add, Nat.sub_add_cancel him.le]
        have h1 : q * k < q * ord i := by omega
        exact lt_of_mul_lt_mul_left h1 (Nat.zero_le _)
      · rfl
    · rfl
  set g : ℕ → K⟦X⟧ := fun i ↦ divXPow (p * m) (c i) with hg
  have hcg : ∀ i, c i = X ^ (p * m) * g i := fun i ↦ (X_pow_mul_divXPow _ _ (hlb i)).symm
  set G : Polynomial K⟦X⟧ := ∑ i ∈ Finset.range (H'.natDegree + 1),
    Polynomial.C (g i) * Polynomial.X ^ i with hG
  have hGc : ∀ i, G.coeff i = g i := by
    intro i
    simp only [hG, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with h
    · rfl
    · have : H'.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp only [hg, hc, this, map_zero, zero_mul, divXPow_zero]
  have hkey : ∀ (φ : K⟦X⟧ →+* K⟦X⟧) (w : K⟦X⟧),
      ((H'.map (ex q)).map φ).eval (φ (X ^ p) * w) = φ (X ^ (p * m)) * (G.map φ).eval w := by
    intro φ w
    apply eval_scale
    intro i
    have := hcg i
    simp only [hc] at this
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map, hGc, ← map_pow,
      ← map_mul, ← map_mul, ← pow_mul, this]
  -- the reduction of `G` (the edge polynomial)
  have hGred : ∀ i, constantCoeff (G.coeff i) = coeff (p * m) (c i) := by
    intro i
    rw [hGc, ← coeff_zero_eq_constantCoeff_apply, hg, coeff_divXPow, zero_add]
  have hGm : constantCoeff (G.coeff m) ≠ 0 := by
    rw [hGred, hc]
    simp only
    rw [coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_ex, hred]
    exact hm0
  have hGi0 : constantCoeff (G.coeff i0) ≠ 0 := by
    rw [hGred, hc]
    simp only
    rw [coeff_mul_X_pow', if_pos (Nat.mul_le_mul_left p hi0m.le), ex_apply hq0]
    have e : p * m - p * i0 = q * p := by
      rw [← Nat.mul_sub, Nat.mul_comm]
    rw [e, coeff_expand_mul]
    exact coeff_order hi0ne
  have hGm1 : constantCoeff (G.coeff (m - 1)) = 0 := by
    rw [hGred, hc]
    simp only
    rw [hH'm1, map_zero, zero_mul, map_zero]
  have hGhi : ∀ i, m < i → constantCoeff (G.coeff i) = 0 := by
    intro i hi
    rw [hGred, hc]
    simp only
    rw [coeff_mul_X_pow', if_neg (not_le.mpr ((Nat.mul_lt_mul_left (by omega)).mpr hi))]
  set gb := G.map (constantCoeff (R := K)) with hgb
  have hgbc : ∀ i, gb.coeff i = constantCoeff (G.coeff i) := fun i ↦ Polynomial.coeff_map _ _
  have hgbdeg : gb.natDegree = m := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro i hi
      rw [hgbc]
      exact hGhi i (by exact_mod_cast hi)
    · rw [hgbc]; exact hGm
  have hgb0 : gb ≠ 0 := fun h ↦ hGm (by rw [← hgbc, h, Polynomial.coeff_zero])
  obtain ⟨c', hc'⟩ := IsAlgClosed.exists_root gb (by
    rw [Polynomial.degree_eq_natDegree hgb0, hgbdeg]
    exact_mod_cast (by omega : m ≠ 0))
  have htay : gb.rootMultiplicity c' = (Polynomial.taylor c' gb).natTrailingDegree := by
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree, Polynomial.taylor_apply]
  have hm'pos : 0 < gb.rootMultiplicity c' := (Polynomial.rootMultiplicity_pos hgb0).mpr hc'
  have hm'lt : gb.rootMultiplicity c' < m := by
    by_contra hge
    push Not at hge
    set cm := gb.coeff m with hcm
    have htg : Polynomial.taylor c' gb = Polynomial.C cm * Polynomial.X ^ m := by
      ext k
      rw [Polynomial.coeff_C_mul_X_pow]
      split_ifs with hk
      · rw [hk]
        have := Polynomial.coeff_taylor_natDegree (r := c') (f := gb)
        rw [hgbdeg] at this
        rw [this, Polynomial.leadingCoeff, hgbdeg]
      · rcases lt_or_gt_of_ne hk with h | h
        · exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by rw [← htay]; omega)
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [Polynomial.natDegree_taylor, hgbdeg]; exact h)
    have hback : gb = Polynomial.taylor (-c') (Polynomial.taylor c' gb) := by
      rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
    have hco : ∀ k, gb.coeff k = cm * ((-c') ^ (m - k) * (m.choose k : K)) := by
      intro k
      have e : gb.coeff k = (Polynomial.taylor (-c') (Polynomial.taylor c' gb)).coeff k := by
        rw [← hback]
      rw [e, htg, Polynomial.taylor_mul, Polynomial.taylor_C, Polynomial.taylor_X_pow,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
    have hcm0 : cm ≠ 0 := by rw [hcm, hgbc]; exact hGm
    have h1 := hco (m - 1)
    rw [hgbc, hGm1, show m - (m - 1) = 1 by omega, pow_one,
      Nat.choose_symm_of_eq_add (by omega : m = (m - 1) + 1), Nat.choose_one_right] at h1
    have hc'0 : c' = 0 := by
      have : cm * (-c' * (m : K)) = 0 := h1.symm
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hcm0
      rcases mul_eq_zero.mp h with h | h
      · exact neg_eq_zero.mp h
      · exact absurd h (Nat.cast_ne_zero.mpr (by omega))
    have h2 := hco i0
    rw [hgbc, hc'0, neg_zero, zero_pow (by omega), zero_mul, mul_zero] at h2
    exact hGi0 h2
  -- recurse on the edge root
  set G₁ := Polynomial.taylor (C c') G with hG₁
  have hG₁red : ∀ i, constantCoeff (G₁.coeff i) = (Polynomial.taylor c' gb).coeff i := by
    intro i
    rw [← Polynomial.coeff_map, hG₁, Polynomial.map_taylor, constantCoeff_C]
  obtain ⟨N', hN', w₁, hw₁, hw₁0⟩ := ih _ hm'lt G₁ hm'pos
    (fun i hi ↦ by
      rw [hG₁red]
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by rw [← htay]; exact hi))
    (by
      rw [hG₁red, htay]
      exact mt Polynomial.trailingCoeff_eq_zero.mp
        (mt (Polynomial.taylor_eq_zero c' gb).mp hgb0))
  have hGroot : (G.map (ex N')).eval (w₁ + C c') = 0 := by
    rw [hG₁, Polynomial.map_taylor, ex_C, Polynomial.taylor_eval] at hw₁
    exact hw₁
  have hH'root : (H'.map (ex (N' * q))).eval (ex N' (X ^ p) * (w₁ + C c')) = 0 := by
    rw [← map_ex_ex hN' hq0, hkey, hGroot, mul_zero]
  refine ⟨N' * q, mul_ne_zero hN' hq0, _, htr _ _ hH'root, hccr _ _ ?_⟩
  rw [map_mul, constantCoeff_ex, map_pow, constantCoeff_X, zero_pow (by omega), zero_mul]

/-- A monic polynomial of positive degree over `K⟦X⟧` has a root after some `X ↦ Xᴺ`, lifting any
root of its reduction. -/
theorem exists_root (H : Polynomial K⟦X⟧) (hmon : H.Monic) (hdeg : 1 ≤ H.natDegree) :
    ∃ N, N ≠ 0 ∧ ∃ r : K⟦X⟧, (H.map (ex N)).eval r = 0 := by
  classical
  set hb := H.map (constantCoeff (R := K)) with hhb
  have hbm : hb.Monic := hmon.map _
  have hbdeg : hb.natDegree = H.natDegree := hmon.natDegree_map _
  have hb0 : hb ≠ 0 := hbm.ne_zero
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root hb (by
    rw [Polynomial.degree_eq_natDegree hb0, hbdeg]
    exact_mod_cast (by omega : H.natDegree ≠ 0))
  have htay : hb.rootMultiplicity c = (Polynomial.taylor c hb).natTrailingDegree := by
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree, Polynomial.taylor_apply]
  set H₁ := Polynomial.taylor (C c) H with hH₁
  have hH₁red : ∀ i, constantCoeff (H₁.coeff i) = (Polynomial.taylor c hb).coeff i := by
    intro i
    rw [← Polynomial.coeff_map, hH₁, Polynomial.map_taylor, constantCoeff_C]
  obtain ⟨N, hN, r, hr, -⟩ := exists_root_mult _ H₁
    ((Polynomial.rootMultiplicity_pos hb0).mpr hc)
    (fun i hi ↦ by
      rw [hH₁red]
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by rw [← htay]; exact hi))
    (by
      rw [hH₁red, htay]
      exact mt Polynomial.trailingCoeff_eq_zero.mp (mt (Polynomial.taylor_eq_zero c hb).mp hb0))
  refine ⟨N, hN, r + C c, ?_⟩
  rw [hH₁, Polynomial.map_taylor, ex_C, Polynomial.taylor_eval] at hr
  exact hr

/-- **The Newton–Puiseux theorem.** A monic polynomial over `K⟦X⟧` (`K` algebraically closed of
characteristic zero) splits into linear factors after some substitution `X ↦ Xᴺ`. -/
theorem puiseux_split (n : ℕ) : ∀ (H : Polynomial K⟦X⟧), H.Monic → H.natDegree = n →
    ∃ N, N ≠ 0 ∧ ∃ l : List K⟦X⟧, l.length = n ∧
      H.map (ex N) = (l.map fun r ↦ Polynomial.X - Polynomial.C r).prod := by
  induction n with
  | zero =>
    intro H hmon hdeg
    refine ⟨1, one_ne_zero, [], rfl, ?_⟩
    rw [Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg, Polynomial.map_one]
    rfl
  | succ n ih =>
    intro H hmon hdeg
    obtain ⟨N, hN, r, hr⟩ := exists_root H hmon (by omega)
    set P := H.map (ex N) with hP
    have hPm : P.Monic := hmon.map _
    have hPdeg : P.natDegree = n + 1 := by rw [hP, hmon.natDegree_map, hdeg]
    set H₁ := P /ₘ (Polynomial.X - Polynomial.C r) with hH₁
    have hfac : (Polynomial.X - Polynomial.C r) * H₁ = P :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hr
    have hH₁m : H₁.Monic :=
      (Polynomial.monic_X_sub_C r).of_mul_monic_left (by rw [hfac]; exact hPm)
    have hH₁deg : H₁.natDegree = n := by
      rw [hH₁, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C r), hPdeg,
        Polynomial.natDegree_X_sub_C]
      omega
    obtain ⟨N₁, hN₁, l, hl, hH₁l⟩ := ih H₁ hH₁m hH₁deg
    refine ⟨N₁ * N, mul_ne_zero hN₁ hN, ex N₁ r :: l, by simp [hl], ?_⟩
    rw [← map_ex_ex hN₁ hN, ← hP, ← hfac, Polynomial.map_mul, hH₁l, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, List.map_cons, List.prod_cons]

end NewtonPuiseux

end Puiseux
