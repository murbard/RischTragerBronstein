import RischTragerBronstein.Algebraic.HermiteExist

/-!
# Uniqueness of the Hermite decomposition

Polynomial form: with `L_D(W) = 2(W′D − WD′)p + WDp′`, `S = ∏_{α ∈ T}(X − α)` over non-branch
roots `α` of `D` (`D` split), `deg B₀ ≤ n − 2`:

  `S L_D(W) + 2D² S B₀ + 2D² ∑ c_α S/(X − α) = 0   ⟹   W/D = 0, B₀ = 0, c = 0`.

After reducing `W/D` to lowest terms, a pole of order `j` of `W/D` at a root `r` makes `L` have
exact order `j − 1` (non-branch, coefficient `−2j W(r) D₃(r) p(r)`) or `j` (branch, coefficient
`(1 − 2j) W(r) D₃(r) p′(r)`) at `r`, which no other term can cancel; so `W/D` is a polynomial `V`,
evaluating at `α ∈ T` kills `c_α`, and `2V′p + Vp′ = −2B₀` forces `V = 0` by degree.
-/

open Polynomial

namespace EllAlgo

/-- `L_D(W) = 2(W′D − WD′)p + WDp′`. -/
noncomputable def LD (p D W : ℚ[X]) : ℚ[X] :=
  2 * (derivative W * D - W * derivative D) * p + W * D * derivative p

lemma LD_mul (p g D W : ℚ[X]) : LD p (g * D) (g * W) = g ^ 2 * LD p D W := by
  simp only [LD, derivative_mul]; ring

/-- **The exact order of `L_D(W)` at a root of `D`** (`W(r) ≠ 0`). -/
lemma LD_order (p D₃ W : ℚ[X]) (r : ℚ) (j : ℕ) (hj : 1 ≤ j) (hD₃ : D₃.eval r ≠ 0)
    (hW : W.eval r ≠ 0) (hsq : Squarefree p) :
    ∃ (v : ℕ) (f₀ : ℚ[X]), LD p ((X - C r) ^ j * D₃) W = (X - C r) ^ v * f₀ ∧ f₀.eval r ≠ 0 ∧
      (p.eval r ≠ 0 → v + 1 = j) ∧ (p.eval r = 0 → v = j) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hDd : derivative ((X - C r) ^ (i + 1) * D₃) =
      (X - C r) ^ i * (C ((i : ℚ) + 1) * D₃ + (X - C r) * derivative D₃) := by
    rw [derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C]
    simp only [sub_zero, mul_one, Nat.add_sub_cancel]
    push_cast
    rw [show (C ((i : ℚ) + 1) : ℚ[X]) = (i : ℚ[X]) + 1 by simp]
    ring
  by_cases hpr : p.eval r = 0
  · -- a branch point: `p = (X − r) q`
    set q := p /ₘ (X - C r)
    have hpq : p = (X - C r) * q := by
      have := modByMonic_add_div p (X - C r)
      rw [modByMonic_X_sub_C_eq_C_eval, hpr, C_0, zero_add] at this
      exact this.symm
    have hp' : (derivative p).eval r = q.eval r := by rw [hpq, derivative_mul]; simp
    have hsep : p.Separable := (PerfectField.separable_iff_squarefree).mpr hsq
    have hp'r : (derivative p).eval r ≠ 0 := by
      intro h0
      rw [Polynomial.separable_def] at hsep
      obtain ⟨u1, u2, huv⟩ := hsep
      have := congrArg (eval r) huv
      simp only [eval_add, eval_mul, eval_one, hpr, h0, mul_zero, add_zero] at this
      exact zero_ne_one this
    refine ⟨i + 1, 2 * derivative W * (X - C r) * D₃ * q -
        2 * W * (C ((i : ℚ) + 1) * D₃ + (X - C r) * derivative D₃) * q + W * D₃ * derivative p,
      ?_, ?_, fun h ↦ absurd hpr h, fun _ ↦ rfl⟩
    · rw [LD, hDd]
      linear_combination (2 * (derivative W * ((X - C r) ^ (i + 1) * D₃) - W * ((X - C r) ^ i *
        (C ((i : ℚ) + 1) * D₃ + (X - C r) * derivative D₃)))) * hpq
    · simp only [eval_add, eval_sub, eval_mul, eval_ofNat, eval_X, eval_C, sub_self, mul_zero,
        zero_mul, zero_add, zero_sub, hp']
      rw [← hp']
      have h2 : (1 : ℚ) - 2 * ((i : ℚ) + 1) ≠ 0 := by
        have : (0 : ℚ) ≤ i := Nat.cast_nonneg i
        linarith
      intro h0
      apply mul_ne_zero (mul_ne_zero (mul_ne_zero hW hD₃) hp'r) h2
      linear_combination h0
  · -- a non-branch point
    refine ⟨i, 2 * derivative W * (X - C r) * D₃ * p -
        2 * W * (C ((i : ℚ) + 1) * D₃ + (X - C r) * derivative D₃) * p +
          W * (X - C r) * D₃ * derivative p, ?_, ?_, fun _ ↦ rfl, fun h ↦ absurd h hpr⟩
    · rw [LD, hDd]; ring
    · simp only [eval_add, eval_sub, eval_mul, eval_ofNat, eval_X, eval_C, sub_self, mul_zero,
        zero_mul, zero_add, zero_sub, add_zero]
      have h2 : (2 : ℚ) * ((i : ℚ) + 1) ≠ 0 := by positivity
      intro h0
      apply mul_ne_zero (mul_ne_zero (mul_ne_zero hW hD₃) hpr) h2
      linear_combination -h0

/-- The top coefficient of `2W′p + Wp′`. -/
lemma coeff_top_Lpoly (p W : ℚ[X]) (hW : W ≠ 0) (hp1 : 1 ≤ p.natDegree) :
    (2 * derivative W * p + W * derivative p).coeff (W.natDegree + p.natDegree - 1) =
      W.leadingCoeff * p.leadingCoeff * (2 * W.natDegree + p.natDegree) := by
  set dW := W.natDegree
  set n := p.natDegree
  have h1 : (derivative W * p).coeff (dW + n - 1) = dW * W.leadingCoeff * p.leadingCoeff := by
    rcases Nat.eq_zero_or_pos dW with h0 | hpos
    · have : derivative W = 0 := by
        rw [eq_C_of_natDegree_eq_zero h0]; exact derivative_C
      rw [this, zero_mul, coeff_zero, h0, Nat.cast_zero, zero_mul, zero_mul]
    · rw [show dW + n - 1 = (dW - 1) + n by omega, coeff_mul_add_eq_of_natDegree_le
        (natDegree_derivative_le W) le_rfl, coeff_derivative, show dW - 1 + 1 = dW by omega]
      have hcast : ((dW - 1 : ℕ) : ℚ) + 1 = (dW : ℚ) := by
        rw [Nat.cast_sub hpos]; push_cast; ring
      rw [hcast]
      change W.leadingCoeff * (dW : ℚ) * p.leadingCoeff = _
      ring
  have h2 : (W * derivative p).coeff (dW + n - 1) = W.leadingCoeff * (n * p.leadingCoeff) := by
    rw [show dW + n - 1 = dW + (n - 1) by omega, coeff_mul_add_eq_of_natDegree_le le_rfl
      (natDegree_derivative_le p), coeff_derivative, show n - 1 + 1 = n by omega]
    have hcast : ((n - 1 : ℕ) : ℚ) + 1 = (n : ℚ) := by
      rw [Nat.cast_sub hp1]; push_cast; ring
    rw [hcast]
    change W.leadingCoeff * (p.leadingCoeff * (n : ℚ)) = _
    ring
  rw [coeff_add, mul_assoc, show (2 : ℚ[X]) = C 2 from (map_ofNat C 2).symm, coeff_C_mul, h1, h2]
  ring

/-- `L_{C d}(W) = d (2W′p + Wp′)`. -/
lemma LD_const (p W : ℚ[X]) (d : ℚ) : LD p (C d) W = C d * (2 * derivative W * p + W * derivative p) := by
  simp only [LD, derivative_C, mul_zero, sub_zero]; ring

/-- **Uniqueness of the Hermite decomposition** (split denominator). -/
theorem hermite_unique (p : ℚ[X]) (hsq : Squarefree p) (hp1 : 1 ≤ p.natDegree) (D W B₀ : ℚ[X])
    (T : Finset ℚ) (c : ℚ → ℚ) (hD : D ≠ 0) (hsplit : D.Splits)
    (hT : ∀ α ∈ T, D.IsRoot α ∧ ¬ p.IsRoot α) (hB : B₀ = 0 ∨ B₀.natDegree + 2 ≤ p.natDegree)
    (hid : (∏ α ∈ T, (X - C α)) * LD p D W + 2 * D ^ 2 * (∏ α ∈ T, (X - C α)) * B₀ +
      2 * D ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β) = 0) :
    W = 0 ∧ B₀ = 0 ∧ ∀ α ∈ T, c α = 0 := by
  classical
  set S := ∏ α ∈ T, (X - C α) with hS
  have hS0 : S ≠ 0 := Finset.prod_ne_zero_iff.mpr fun α _ ↦ X_sub_C_ne_zero α
  -- the residues and `B₀` once the `L`-term is gone
  have finish : ∀ (d : ℚ) (V : ℚ[X]), d ≠ 0 →
      S * (C d * (2 * derivative V * p + V * derivative p)) + 2 * C d ^ 2 * S * B₀ +
        2 * C d ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β) = 0 →
      V = 0 ∧ B₀ = 0 ∧ ∀ α ∈ T, c α = 0 := by
    intro d V hd h
    have hc : ∀ α ∈ T, c α = 0 := by
      intro α hα
      have := congrArg (eval α) h
      have hSα : S.eval α = 0 := by
        rw [hS, eval_prod]; exact Finset.prod_eq_zero hα (by simp)
      have hsum : (∑ β ∈ T, C (c β) * ∏ γ ∈ T.erase β, (X - C γ)).eval α =
          c α * ∏ γ ∈ T.erase α, (α - γ) := by
        rw [eval_finset_sum, Finset.sum_eq_single α]
        · simp [eval_prod]
        · intro β _ hβ
          rw [eval_mul, eval_prod]
          exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hβ, hα⟩)
            (by simp))
        · intro h'; exact absurd hα h'
      simp only [eval_add, eval_mul, hSα, zero_mul, zero_add, eval_pow, eval_C, eval_ofNat,
        hsum, eval_zero, mul_zero] at this
      have hprod : ∏ γ ∈ T.erase α, (α - γ) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun γ hγ ↦ sub_ne_zero.mpr (Finset.ne_of_mem_erase hγ).symm
      have h2 : (2 : ℚ) * d ^ 2 ≠ 0 := by positivity
      have := (mul_eq_zero.mp (show (2 * d ^ 2) * (c α * ∏ γ ∈ T.erase α, (α - γ)) = 0 by
        linear_combination this)).resolve_left h2
      exact (mul_eq_zero.mp this).resolve_right hprod
    have hsum0 : ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β) = 0 :=
      Finset.sum_eq_zero fun α hα ↦ by rw [hc α hα, C_0, zero_mul]
    rw [hsum0, mul_zero, add_zero] at h
    have h2 : S * C d * (2 * derivative V * p + V * derivative p + C (2 * d) * B₀) = 0 := by
      rw [C_mul, map_ofNat]; linear_combination h
    have h3 : 2 * derivative V * p + V * derivative p + C (2 * d) * B₀ = 0 :=
      (mul_eq_zero.mp h2).resolve_left (mul_ne_zero hS0 (C_ne_zero.mpr hd))
    by_cases hV : V = 0
    · refine ⟨hV, ?_, hc⟩
      rw [hV] at h3; simp at h3
      rcases h3 with h | h
      · exact absurd h hd
      · exact h
    · exfalso
      have htop := coeff_top_Lpoly p V hV hp1
      have hne : V.leadingCoeff * p.leadingCoeff * (2 * V.natDegree + p.natDegree) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hV) ?_) (by positivity)
        exact leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hp1)
      have hB0 : (C (2 * d) * B₀).coeff (V.natDegree + p.natDegree - 1) = 0 := by
        rw [coeff_C_mul]
        rcases hB with h | h
        · rw [h]; simp
        · rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      have := congrArg (fun P ↦ P.coeff (V.natDegree + p.natDegree - 1)) h3
      simp only [coeff_add, htop, hB0, add_zero, coeff_zero] at this
      exact hne this
  by_cases hW : W = 0
  · -- no `L`-term
    have h := finish 1 0 one_ne_zero (by
      rw [hW] at hid
      simp only [LD, derivative_zero, zero_mul, mul_zero, sub_self, add_zero, zero_add] at hid
      simp only [map_one, one_pow, mul_one, derivative_zero, zero_mul, mul_zero, zero_add]
      have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
      have : D ^ 2 * (2 * S * B₀ + 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β)) = 0 := by
        linear_combination hid
      linear_combination (mul_eq_zero.mp this).resolve_left hD2)
    exact ⟨hW, h.2⟩
  · -- reduce `W/D` to lowest terms
    exfalso
    obtain ⟨g, hgdef⟩ : ∃ g, g = gcd W D := ⟨_, rfl⟩
    have hg0 : g ≠ 0 := by
      intro h0; rw [hgdef, gcd_eq_zero_iff] at h0; exact hW h0.1
    obtain ⟨W₁, hW₁⟩ : g ∣ W := hgdef ▸ gcd_dvd_left W D
    obtain ⟨D₁, hD₁⟩ : g ∣ D := hgdef ▸ gcd_dvd_right W D
    have hcop : IsCoprime W₁ D₁ := by
      have := isCoprime_div_gcd_div_gcd (p := W) (q := D) hD
      rw [← hgdef] at this
      have e1 : W / g = W₁ := by rw [hW₁, mul_div_cancel_left₀ _ hg0]
      have e2 : D / g = D₁ := by rw [hD₁, mul_div_cancel_left₀ _ hg0]
      rwa [e1, e2] at this
    have hW₁0 : W₁ ≠ 0 := by rintro rfl; rw [mul_zero] at hW₁; exact hW hW₁
    have hD₁0 : D₁ ≠ 0 := by rintro rfl; rw [mul_zero] at hD₁; exact hD hD₁
    have hid₁ : S * LD p D₁ W₁ + 2 * D₁ ^ 2 * S * B₀ +
        2 * D₁ ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β) = 0 := by
      rw [hW₁, hD₁, LD_mul] at hid
      have : g ^ 2 * (S * LD p D₁ W₁ + 2 * D₁ ^ 2 * S * B₀ +
          2 * D₁ ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β)) = 0 := by
        linear_combination hid
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hg0)
    -- `D₁` has no root
    have hnoroot : ∀ r : ℚ, D₁.eval r ≠ 0 := by
      intro r hr
      obtain ⟨D₃, hD₃, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd D₁ hD₁0 r
      set j := D₁.rootMultiplicity r
      have hj : 1 ≤ j := (rootMultiplicity_pos hD₁0).mpr hr
      have hD₃r : D₃.eval r ≠ 0 := fun h ↦ hnd (dvd_iff_isRoot.mpr h)
      have hW₁r : W₁.eval r ≠ 0 := by
        intro h
        have h1 : X - C r ∣ W₁ := dvd_iff_isRoot.mpr h
        have h2 : X - C r ∣ D₁ := by
          rw [hD₃]; exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
        exact (Polynomial.irreducible_X_sub_C r).not_isUnit (hcop.isUnit_of_dvd' h1 h2)
      obtain ⟨v, f₀, hf, hf₀, hv1, hv2⟩ := LD_order p D₃ W₁ r j hj hD₃r hW₁r hsq
      rw [← hD₃] at hf
      -- `S = (X − r)^[r ∈ T] S'`
      obtain ⟨e, S', hS', hS'r, he⟩ : ∃ (e : ℕ) (S' : ℚ[X]), S = (X - C r) ^ e * S' ∧
          S'.eval r ≠ 0 ∧ (r ∈ T → e = 1) ∧ (r ∉ T → e = 0) := by
        by_cases hrT : r ∈ T
        · refine ⟨1, ∏ α ∈ T.erase r, (X - C α), ?_, ?_, fun _ ↦ rfl, fun h ↦ absurd hrT h⟩
          · rw [hS, ← Finset.mul_prod_erase T _ hrT, pow_one]
          · rw [eval_prod]
            exact Finset.prod_ne_zero_iff.mpr fun α hα ↦ by
              simp only [eval_sub, eval_X, eval_C]
              exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hα).symm
        · refine ⟨0, S, by simp, ?_, fun h ↦ absurd h hrT, fun _ ↦ rfl⟩
          rw [hS, eval_prod]
          exact Finset.prod_ne_zero_iff.mpr fun α hα ↦ by
            simp only [eval_sub, eval_X, eval_C]
            exact sub_ne_zero.mpr fun h ↦ hrT (h ▸ hα)
      -- the `L`-term has exact order `v + e`, the rest order `≥ 2j ≥ v + e + 1`
      have hle : v + e + 1 ≤ 2 * j := by
        by_cases hpr : p.eval r = 0
        · have hv := hv2 hpr
          have hrT : r ∉ T := fun h ↦ (hT r h).2 hpr
          have := he.2 hrT
          omega
        · have hv := hv1 hpr
          by_cases hrT : r ∈ T
          · have := he.1 hrT; omega
          · have := he.2 hrT; omega
      have hdvd_rest : (X - C r) ^ (v + e + 1) ∣ 2 * D₁ ^ 2 * S * B₀ +
          2 * D₁ ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β) := by
        have : (X - C r) ^ (v + e + 1) ∣ D₁ ^ 2 := by
          rw [hD₃, mul_pow, ← pow_mul]
          exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _
        exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this _) _) _)
          (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this _) _)
      have hdvd_L : (X - C r) ^ (v + e + 1) ∣ S * LD p D₁ W₁ := by
        have : S * LD p D₁ W₁ = -(2 * D₁ ^ 2 * S * B₀ +
            2 * D₁ ^ 2 * ∑ α ∈ T, C (c α) * ∏ β ∈ T.erase α, (X - C β)) := by
          linear_combination hid₁
        rw [this]; exact (dvd_neg).mpr hdvd_rest
      rw [hS', hf, show (X - C r) ^ e * S' * ((X - C r) ^ v * f₀) =
        (X - C r) ^ (v + e) * (S' * f₀) by ring, pow_succ] at hdvd_L
      have := (mul_dvd_mul_iff_left (pow_ne_zero _ (X_sub_C_ne_zero r))).mp hdvd_L
      rw [dvd_iff_isRoot, IsRoot, eval_mul] at this
      exact mul_ne_zero hS'r hf₀ this
    -- so `D₁` is a constant
    have hsplit₁ : D₁.Splits := hsplit.of_dvd hD (by rw [hD₁]; exact dvd_mul_left _ _)
    have hdeg₁ : D₁.degree = 0 := by
      by_contra hne
      obtain ⟨r, hr⟩ := hsplit₁.exists_eval_eq_zero hne
      exact hnoroot r hr
    obtain ⟨d₁, hd₁⟩ : ∃ d₁, D₁ = C d₁ :=
      ⟨D₁.coeff 0, eq_C_of_degree_eq_zero hdeg₁⟩
    have hd₁0 : d₁ ≠ 0 := by rintro rfl; rw [C_0] at hd₁; exact hD₁0 hd₁
    rw [hd₁, LD_const] at hid₁
    have := finish d₁ W₁ hd₁0 (by rw [← C_pow] at hid₁ ⊢; simpa [map_pow] using hid₁)
    exact hW₁0 this.1

end EllAlgo
