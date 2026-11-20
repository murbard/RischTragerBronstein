import RischTragerBronstein.Jacobian.PrincipalTest

/-!
# Abel's direction in any genus: the algebraic core

The Liouville/`ell_glue` analysis of an elementary integral produces functions `uⱼ = aⱼ + bⱼ y`
(`aⱼ, bⱼ` coprime) whose norms are `λⱼ ∏ (x − αᵢ)^{mᵢⱼ} · gⱼ` with `gⱼ ∣ f` (simple zeros at branch
points), and `uⱼ` vanishes at `(αᵢ, −εᵢⱼ βᵢ)`. For integer weights `wⱼ`, `abel_core` builds a
non-zero `ψ` of pole order `≤ ∑ 2|eᵢ|` vanishing at `(αᵢ, sgn(eᵢ) βᵢ)` to order `2|eᵢ|`, where
`eᵢ = ∑ⱼ wⱼ mᵢⱼ (−εᵢⱼ)`: the divisor `∑ eᵢ ([Pᵢ] − [σPᵢ])` has a principal multiple.

Steps: `uⱼ² = gⱼ · Uⱼ` (the branch-point zeros are removed, `U_of_u`); `Uⱼ` vanishes to order
`2mᵢⱼ` at `(αᵢ, −εᵢⱼβᵢ)` (`vanishAt_of_norm`); `F = ∏ Vⱼ^{|wⱼ|}` (`Vⱼ = Uⱼ` or its conjugate);
dividing `F` by `∏ (x − αᵢ)^{min}` leaves the net zeros; the pole order is read off the norm
(`poleLE_hnorm`).
-/

open Polynomial

namespace Jac

variable {k : Type*} [Field k]

/-- Pole order equals the degree of the norm (`deg f = 2g + 1`). -/
lemma poleLE_hnorm {f : k[X]} {g : ℕ} (hf : f.natDegree = 2 * g + 1) (ψ : k[X] × k[X]) :
    PoleLE g ψ (hnorm f ψ).natDegree := by
  have hf0 : f ≠ 0 := by intro h; rw [h] at hf; simp at hf
  by_cases hb : ψ.2 = 0
  · refine ⟨?_, Or.inl hb⟩
    simp [hnorm, hb, natDegree_pow]
  · have hbf : (ψ.2 ^ 2 * f).natDegree = 2 * ψ.2.natDegree + 2 * g + 1 := by
      rw [natDegree_mul (pow_ne_zero _ hb) hf0, natDegree_pow, hf]; ring
    by_cases ha : ψ.1 = 0
    · refine ⟨by simp [ha], Or.inr ?_⟩
      simp [hnorm, ha, natDegree_neg, hbf]
    · have hne : (ψ.1 ^ 2).natDegree ≠ (ψ.2 ^ 2 * f).natDegree := by
        rw [natDegree_pow, hbf]; omega
      have hN : (hnorm f ψ).natDegree = max (ψ.1 ^ 2).natDegree (ψ.2 ^ 2 * f).natDegree := by
        unfold hnorm
        rcases lt_or_gt_of_ne hne with h | h
        · rw [natDegree_sub_eq_right_of_natDegree_lt h, max_eq_right h.le]
        · rw [natDegree_sub_eq_left_of_natDegree_lt h, max_eq_left h.le]
      rw [hN, natDegree_pow, hbf]
      exact ⟨le_max_left _ _, Or.inr (le_max_right _ _)⟩

/-- Removing the branch-point zeros: `u² = g · U`. -/
lemma U_of_u {f : k[X]} (hfsq : Squarefree f) {u : k[X] × k[X]} {gq : k[X]} (hgq : gq ∣ f)
    (hN : gq ∣ hnorm f u) : ∃ U, hmul f u u = hsmul gq U := by
  have hgsq : Squarefree gq := hfsq.squarefree_of_dvd hgq
  have ha : gq ∣ u.1 := by
    have h1 : gq ∣ u.1 ^ 2 := by
      have : u.1 ^ 2 = hnorm f u + u.2 ^ 2 * f := by simp [hnorm]
      rw [this]; exact dvd_add hN (Dvd.dvd.mul_left hgq _)
    exact (hgsq.dvd_pow_iff_dvd two_ne_zero).mp h1
  obtain ⟨A, hA⟩ := ha
  obtain ⟨Fq, hFq⟩ := hgq
  refine ⟨(A * u.1 + u.2 * u.2 * Fq, 2 * A * u.2), ?_⟩
  simp only [hmul, hsmul]
  refine Prod.ext ?_ ?_
  · simp only; rw [hFq, hA]; ring
  · simp only; rw [hA]; ring

/-- **Vanishing from the norm**: if `(x − x₀)ᵐ` divides the norm and the conjugate point is not a
zero, then `a + b y` vanishes to order `m` at `(x₀, Y₀)`. -/
lemma vanishAt_of_norm {f a b : k[X]} {x₀ Y₀ : k} {m : ℕ} (h2Y : 2 * Y₀ ≠ 0)
    (hY : Y₀ ^ 2 = f.eval x₀) (hdvd : (X - C x₀) ^ m ∣ hnorm f (a, b))
    (hc : a.eval x₀ - b.eval x₀ * Y₀ ≠ 0) : VanishAt f a b x₀ Y₀ m := by
  obtain ⟨V, hV⟩ := exists_branch (IsUnit.mk0 _ h2Y) hY m
  refine ⟨V, hV, X_pow_dvd_of_mul (c := a.comp (X + C x₀) - b.comp (X + C x₀) * V) ?_ ?_⟩
  · refine IsUnit.mk0 _ ?_
    rw [coeff_sub, mul_coeff_zero, hV.1, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero,
      eval_comp, eval_comp]
    simpa using hc
  · have e : (a.comp (X + C x₀) - b.comp (X + C x₀) * V) * jet a b x₀ V =
        (hnorm f (a, b)).comp (X + C x₀) - (b.comp (X + C x₀)) ^ 2 * (V ^ 2 - f.comp (X + C x₀)) := by
      simp only [jet, hnorm, sub_comp, mul_comp, pow_comp]; ring
    rw [e]
    exact dvd_sub (comp_dvd_of_dvd hdvd) (Dvd.dvd.mul_left hV.2 _)

lemma hnorm_hpow (f : k[X]) (ψ : k[X] × k[X]) : ∀ n, hnorm f (hpow f ψ n) = hnorm f ψ ^ n
  | 0 => by simp [hpow, hnorm]
  | n + 1 => by rw [hpow, hnorm_hmul, hnorm_hpow f ψ n, pow_succ]

lemma hnorm_hconj' (f : k[X]) (ψ : k[X] × k[X]) : hnorm f (hconj ψ) = hnorm f ψ := by
  simp [hnorm, hconj]

lemma hconj_ne_zero {ψ : k[X] × k[X]} (h : ψ ≠ (0, 0)) : hconj ψ ≠ (0, 0) := by
  intro h'; apply h; simp only [hconj, Prod.mk.injEq, neg_eq_zero] at h'; exact Prod.ext h'.1 h'.2

lemma ne_zero_of_hnorm {f : k[X]} {ψ : k[X] × k[X]} (h : hnorm f ψ ≠ 0) : ψ ≠ (0, 0) := by
  rintro rfl; apply h; simp [hnorm]

section Product

variable {ι : Type*} [DecidableEq ι]

/-- Zeros at `(αᵢ, βᵢ)` contributed by the weights. -/
def zp (w : ℕ → ℤ) (m : ι → ℕ → ℕ) (ε : ι → ℕ → ℤ) (T : Finset ℕ) (i : ι) : ℕ :=
  ∑ j ∈ T, if 0 < w j * -ε i j then 2 * (w j).natAbs * m i j else 0

/-- Zeros at `(αᵢ, −βᵢ)`. -/
def zm (w : ℕ → ℤ) (m : ι → ℕ → ℕ) (ε : ι → ℕ → ℤ) (T : Finset ℕ) (i : ι) : ℕ :=
  ∑ j ∈ T, if w j * -ε i j < 0 then 2 * (w j).natAbs * m i j else 0

/-- **Per function**: `u² = g U`, `U` has norm `λ² ∏ (x − αᵢ)^{2mᵢ}` and zeros `(αᵢ, −εᵢβᵢ)`. -/
lemma single_U (f : k[X]) (hfo : Odd f.natDegree) (hfsq : Squarefree f) (h2 : (2 : k) ≠ 0) (s : Finset ι) (α β : ι → k)
    (hβ : ∀ i ∈ s, β i ≠ 0) (hαβ : ∀ i ∈ s, β i ^ 2 = f.eval (α i))
    (u : k[X] × k[X]) (hcop : IsCoprime u.1 u.2) (m : ι → ℕ) (ε : ι → ℤ)
    (hε : ∀ i ∈ s, ε i = 1 ∨ ε i = -1) (lam : k) (gq : k[X]) (hlam : lam ≠ 0) (hgq : gq ∣ f)
    (hfac : hnorm f u = C lam * (∏ i ∈ s, (X - C (α i)) ^ m i) * gq)
    (hval : ∀ i ∈ s, 0 < m i → u.1.eval (α i) = ε i * β i * u.2.eval (α i)) :
    ∃ U : k[X] × k[X], U ≠ (0, 0) ∧
      hnorm f U = C (lam ^ 2) * ∏ i ∈ s, (X - C (α i)) ^ (2 * m i) ∧
      ∀ i ∈ s, VanishAt f U.1 U.2 (α i) (-(ε i) * β i) (2 * m i) := by
  have hN0 : hnorm f u ≠ 0 := by
    refine hnorm_ne_zero hfo fun h ↦ ?_
    rw [h] at hcop
    exact not_isCoprime_zero_zero hcop
  have hgq0 : gq ≠ 0 := by rintro rfl; rw [hfac, mul_zero] at hN0; exact hN0 rfl
  obtain ⟨U, hU⟩ := U_of_u hfsq hgq (by rw [hfac]; exact dvd_mul_left _ _)
  have hNU : hnorm f U = C (lam ^ 2) * ∏ i ∈ s, (X - C (α i)) ^ (2 * m i) := by
    have e1 := hnorm_hmul f u u
    rw [hU] at e1
    have e2 : hnorm f (hsmul gq U) = gq ^ 2 * hnorm f U := by simp [hsmul, hnorm]; ring
    rw [e2, hfac] at e1
    apply mul_left_cancel₀ (pow_ne_zero 2 hgq0)
    rw [e1, show ∏ i ∈ s, (X - C (α i)) ^ (2 * m i) = (∏ i ∈ s, (X - C (α i)) ^ m i) ^ 2 by
      rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun i _ ↦ by rw [← pow_mul, mul_comm]]
    simp only [map_pow]; ring
  refine ⟨U, ne_zero_of_hnorm (by
    rw [hNU]
    exact mul_ne_zero (by simpa using pow_ne_zero 2 hlam) (Finset.prod_ne_zero_iff.mpr
      fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _))), hNU, fun i hi ↦ ?_⟩
  have hsign : (ε i : k) ^ 2 = 1 := by rcases hε i hi with h | h <;> rw [h] <;> norm_num
  have hY : (-(ε i : k) * β i) ^ 2 = f.eval (α i) := by
    rw [mul_pow, neg_sq, ← hαβ i hi, hsign, one_mul]
  have h2Y : 2 * (-(ε i : k) * β i) ≠ 0 := by
    refine mul_ne_zero h2 (mul_ne_zero ?_ (hβ i hi))
    rcases hε i hi with h | h <;> rw [h] <;> norm_num
  -- `u` vanishes to order `mᵢ`
  have hu : VanishAt f u.1 u.2 (α i) (-(ε i) * β i) (m i) := by
    rcases Nat.eq_zero_or_pos (m i) with h0 | hpos
    · rw [h0]; exact VanishAt.zero (IsUnit.mk0 _ h2Y) hY
    refine vanishAt_of_norm h2Y hY ?_ ?_
    · rw [show ((u.1, u.2) : k[X] × k[X]) = u from rfl, hfac]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hi) _) _
    · rw [hval i hi hpos]
      intro h0
      have hb : u.2.eval (α i) = 0 := by
        have : 2 * ((ε i : k) * β i * u.2.eval (α i)) = 0 := by linear_combination h0
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h h2
        · rcases mul_eq_zero.mp h with h | h
          · rcases mul_eq_zero.mp h with h | h
            · rcases hε i hi with h' | h' <;> rw [h'] at h <;> norm_num at h
            · exact absurd h (hβ i hi)
          · exact h
      have ha : u.1.eval (α i) = 0 := by rw [hval i hi hpos, hb, mul_zero]
      obtain ⟨r1, r2, hr⟩ := hcop
      have := congrArg (eval (α i)) hr
      simp [ha, hb] at this
  -- hence `u²` to order `2mᵢ`, and `U` too
  have hu2 := VanishAt.hmul (ψ := u) (φ := u) (IsUnit.mk0 _ h2Y) hY hu hu
  rw [hU, ← two_mul] at hu2
  refine VanishAt.of_hsmul_unit (w := gq) (IsUnit.mk0 _ fun h0 ↦ ?_) hu2
  obtain ⟨q, hq⟩ := hgq
  have := congrArg (eval (α i)) hq
  rw [eval_mul, h0, zero_mul, ← hαβ i hi] at this
  exact hβ i hi (pow_eq_zero_iff two_ne_zero |>.mp this)

/-- One factor `Vⱼ^{|wⱼ|}` and its zeros. -/
lemma single_power (f : k[X]) (hfo : Odd f.natDegree) (hfsq : Squarefree f) (h2 : (2 : k) ≠ 0)
    (s : Finset ι) (α β : ι → k) (hβ : ∀ i ∈ s, β i ≠ 0)
    (hαβ : ∀ i ∈ s, β i ^ 2 = f.eval (α i))
    (u : k[X] × k[X]) (hcop : IsCoprime u.1 u.2) (m : ι → ℕ) (ε : ι → ℤ)
    (hε : ∀ i ∈ s, ε i = 1 ∨ ε i = -1) (lam : k) (gq : k[X]) (hlam : lam ≠ 0) (hgq : gq ∣ f)
    (hfac : hnorm f u = C lam * (∏ i ∈ s, (X - C (α i)) ^ m i) * gq)
    (hval : ∀ i ∈ s, 0 < m i → u.1.eval (α i) = ε i * β i * u.2.eval (α i)) (w : ℤ) :
    ∃ P : k[X] × k[X], P ≠ (0, 0) ∧
      hnorm f P = C (lam ^ (2 * w.natAbs)) * ∏ i ∈ s, (X - C (α i)) ^ (2 * w.natAbs * m i) ∧
      ∀ i ∈ s, VanishAt f P.1 P.2 (α i) (β i)
          (if 0 < w * -ε i then 2 * w.natAbs * m i else 0) ∧
        VanishAt f P.1 P.2 (α i) (-β i) (if w * -ε i < 0 then 2 * w.natAbs * m i else 0) := by
  obtain ⟨U, hU0, hNU, hUv⟩ := single_U f hfo hfsq h2 s α β hβ hαβ u hcop m ε hε lam gq hlam hgq
    hfac hval
  set V := if 0 ≤ w then U else hconj U with hVdef
  have hV0 : V ≠ (0, 0) := by
    simp only [hVdef]; split_ifs; exacts [hU0, hconj_ne_zero hU0]
  have hNV : hnorm f V = hnorm f U := by
    simp only [hVdef]; split_ifs; · rfl
    · exact hnorm_hconj' f U
  refine ⟨hpow f V w.natAbs, hpow_ne_zero hfo hV0 _, ?_, fun i hi ↦ ?_⟩
  · rw [hnorm_hpow, hNV, hNU, mul_pow, ← map_pow, ← Finset.prod_pow, ← pow_mul]
    congr 1
    exact Finset.prod_congr rfl fun i _ ↦ by rw [← pow_mul]; ring_nf
  · have hY : ∀ σ : k, σ ^ 2 = 1 → IsUnit (2 * (σ * β i)) ∧ (σ * β i) ^ 2 = f.eval (α i) :=
      fun σ hσ ↦ ⟨IsUnit.mk0 _ (mul_ne_zero h2 (mul_ne_zero (by
        rintro rfl; simp at hσ) (hβ i hi))), by rw [mul_pow, hσ, one_mul, hαβ i hi]⟩
    have hp := hY 1 (by norm_num)
    have hn := hY (-1) (by norm_num)
    simp only [one_mul, neg_one_mul] at hp hn
    have hz : ∀ (σ : k) (hσ : σ ^ 2 = 1), VanishAt f (hpow f V w.natAbs).1
        (hpow f V w.natAbs).2 (α i) (σ * β i) 0 := fun σ hσ ↦
      VanishAt.zero (hY σ hσ).1 (hY σ hσ).2
    -- the zero of `V`
    have hVz : VanishAt f V.1 V.2 (α i) ((if 0 ≤ w then -(ε i : k) else (ε i : k)) * β i)
        (2 * m i) := by
      simp only [hVdef]
      split_ifs with hw
      · exact hUv i hi
      · have := (hUv i hi).hconj; simpa [hconj, neg_mul] using this
    have hsig : ((if 0 ≤ w then -(ε i : k) else (ε i : k))) ^ 2 = 1 := by
      split_ifs <;> rcases hε i hi with h | h <;> rw [h] <;> norm_num
    have hpw := VanishAt.hpow (hY _ hsig).1 (hY _ hsig).2 hVz w.natAbs
    rcases hε i hi with he | he <;> rcases lt_trichotomy w 0 with hw | hw | hw
    · -- ε = 1, w < 0: `V = σU`, zero at `(α, β)`
      rw [he] at hpw ⊢
      simp only [show ¬ (0 ≤ w) by omega, if_false, Int.cast_one, one_mul] at hpw
      refine ⟨?_, ?_⟩
      · rw [if_pos (by nlinarith)]; convert hpw using 1; ring
      · rw [if_neg (by nlinarith)]; simpa using hz (-1) (by norm_num)
    · subst hw; simp only [Int.natAbs_zero, mul_zero, zero_mul, lt_irrefl, if_false]
      exact ⟨by simpa using hz 1 (by norm_num), by simpa using hz (-1) (by norm_num)⟩
    · rw [he] at hpw ⊢
      simp only [show 0 ≤ w by omega, if_true, Int.cast_one, neg_mul, one_mul] at hpw
      refine ⟨?_, ?_⟩
      · rw [if_neg (by nlinarith)]; simpa using hz 1 (by norm_num)
      · rw [if_pos (by nlinarith)]; convert hpw using 1; ring
    · rw [he] at hpw ⊢
      simp only [show ¬ (0 ≤ w) by omega, if_false, Int.cast_neg, Int.cast_one, neg_mul,
        one_mul] at hpw
      refine ⟨?_, ?_⟩
      · rw [if_neg (by nlinarith)]; simpa using hz 1 (by norm_num)
      · rw [if_pos (by nlinarith)]; convert hpw using 1; ring
    · subst hw; simp only [Int.natAbs_zero, mul_zero, zero_mul, lt_irrefl, if_false]
      exact ⟨by simpa using hz 1 (by norm_num), by simpa using hz (-1) (by norm_num)⟩
    · rw [he] at hpw ⊢
      simp only [show 0 ≤ w by omega, if_true, Int.cast_neg, Int.cast_one, neg_neg,
        one_mul] at hpw
      refine ⟨?_, ?_⟩
      · rw [if_pos (by nlinarith)]; convert hpw using 1; ring
      · rw [if_neg (by nlinarith)]; simpa using hz (-1) (by norm_num)

lemma sign_terms (w : ℤ) (e : ℤ) (he : e = 1 ∨ e = -1) (m : ℕ) :
    ((if 0 < w * -e then 2 * w.natAbs * m else 0 : ℕ) : ℤ) -
      ((if w * -e < 0 then 2 * w.natAbs * m else 0 : ℕ) : ℤ) = 2 * (w * (m * -e)) ∧
    (if 0 < w * -e then 2 * w.natAbs * m else 0) + (if w * -e < 0 then 2 * w.natAbs * m else 0) =
      2 * w.natAbs * m := by
  rcases he with rfl | rfl <;> rcases lt_trichotomy w 0 with hw | rfl | hw
  · rw [if_pos (by nlinarith), if_neg (by nlinarith)]
    refine ⟨?_, by simp⟩; push_cast; rw [abs_of_neg hw]; ring
  · simp
  · rw [if_neg (by nlinarith), if_pos (by nlinarith)]
    refine ⟨?_, by simp⟩; push_cast; rw [abs_of_pos hw]; ring
  · rw [if_neg (by nlinarith), if_pos (by nlinarith)]
    refine ⟨?_, by simp⟩; push_cast; rw [abs_of_neg hw]; ring
  · simp
  · rw [if_pos (by nlinarith), if_neg (by nlinarith)]
    refine ⟨?_, by simp⟩; push_cast; rw [abs_of_pos hw]; ring

lemma VanishAt.zero'' {R : Type*} [CommRing R] (f a b : R[X]) (x₀ Y₀ : R) :
    VanishAt f a b x₀ Y₀ 0 := ⟨C Y₀, ⟨by simp, by simp⟩, by simp⟩

/-- **The weighted product.** -/
lemma abel_product (f : k[X]) (hfo : Odd f.natDegree) (hfsq : Squarefree f) (h2 : (2 : k) ≠ 0)
    (s : Finset ι) (α β : ι → k) (hβ : ∀ i ∈ s, β i ≠ 0)
    (hαβ : ∀ i ∈ s, β i ^ 2 = f.eval (α i)) (t : Finset ℕ) (u : ℕ → k[X] × k[X])
    (hcop : ∀ j ∈ t, IsCoprime (u j).1 (u j).2) (m : ι → ℕ → ℕ) (ε : ι → ℕ → ℤ)
    (hε : ∀ i ∈ s, ∀ j ∈ t, ε i j = 1 ∨ ε i j = -1) (lam : ℕ → k) (gq : ℕ → k[X])
    (hlam : ∀ j ∈ t, lam j ≠ 0) (hgq : ∀ j ∈ t, gq j ∣ f)
    (hfac : ∀ j ∈ t, hnorm f (u j) = C (lam j) * (∏ i ∈ s, (X - C (α i)) ^ m i j) * gq j)
    (hval : ∀ i ∈ s, ∀ j ∈ t, 0 < m i j → (u j).1.eval (α i) = ε i j * β i * (u j).2.eval (α i))
    (w : ℕ → ℤ) : ∀ T ⊆ t, ∃ F : k[X] × k[X], F ≠ (0, 0) ∧
      (∃ c : k, c ≠ 0 ∧ hnorm f F = C c * ∏ i ∈ s, (X - C (α i)) ^ (zp w m ε T i + zm w m ε T i)) ∧
      ∀ i ∈ s, VanishAt f F.1 F.2 (α i) (β i) (zp w m ε T i) ∧
        VanishAt f F.1 F.2 (α i) (-β i) (zm w m ε T i) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨(1, 0), by simp, ⟨1, one_ne_zero, by simp [hnorm, zp, zm]⟩, fun i _ ↦ ?_⟩
    simp only [zp, zm, Finset.sum_empty]
    exact ⟨VanishAt.zero'' _ _ _ _ _, VanishAt.zero'' _ _ _ _ _⟩
  | insert j T hjT ih =>
    intro hsub
    have hj : j ∈ t := hsub (Finset.mem_insert_self j T)
    obtain ⟨F, hF0, ⟨c, hc, hNF⟩, hFv⟩ := ih ((Finset.subset_insert j T).trans hsub)
    obtain ⟨P, hP0, hNP, hPv⟩ := single_power f hfo hfsq h2 s α β hβ hαβ (u j) (hcop j hj)
      (fun i ↦ m i j) (fun i ↦ ε i j) (fun i hi ↦ hε i hi j hj) (lam j) (gq j) (hlam j hj)
      (hgq j hj) (hfac j hj) (fun i hi ↦ hval i hi j hj) (w j)
    refine ⟨hmul f F P, hmul_ne_zero hfo hF0 hP0, ⟨c * lam j ^ (2 * (w j).natAbs), ?_, ?_⟩,
      fun i hi ↦ ?_⟩
    · exact mul_ne_zero hc (pow_ne_zero _ (hlam j hj))
    · rw [hnorm_hmul, hNF, hNP, map_mul]
      have e : ∀ i ∈ s, zp w m ε (insert j T) i + zm w m ε (insert j T) i =
          (zp w m ε T i + zm w m ε T i) + 2 * (w j).natAbs * m i j := by
        intro i hi
        simp only [zp, zm, Finset.sum_insert hjT]
        have := (sign_terms (w j) (ε i j) (hε i hi j hj) (m i j)).2
        omega
      have hprod : ∏ i ∈ s, (X - C (α i)) ^ (zp w m ε (insert j T) i + zm w m ε (insert j T) i) =
          (∏ i ∈ s, (X - C (α i)) ^ (zp w m ε T i + zm w m ε T i)) *
            ∏ i ∈ s, (X - C (α i)) ^ (2 * (w j).natAbs * m i j) := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i hi ↦ by rw [e i hi, pow_add]
      rw [hprod]; ring
    · have hY : ∀ σ : k, σ ^ 2 = 1 → IsUnit (2 * (σ * β i)) ∧ (σ * β i) ^ 2 = f.eval (α i) :=
        fun σ hσ ↦ ⟨IsUnit.mk0 _ (mul_ne_zero h2 (mul_ne_zero (by
          rintro rfl; simp at hσ) (hβ i hi))), by rw [mul_pow, hσ, one_mul, hαβ i hi]⟩
      have hp := hY 1 (by norm_num)
      have hn := hY (-1) (by norm_num)
      simp only [one_mul, neg_one_mul] at hp hn
      refine ⟨?_, ?_⟩
      · have := VanishAt.hmul hp.1 hp.2 (hFv i hi).1 (hPv i hi).1
        simp only [zp, Finset.sum_insert hjT]
        rwa [add_comm] at this
      · have := VanishAt.hmul hn.1 hn.2 (hFv i hi).2 (hPv i hi).2
        simp only [zm, Finset.sum_insert hjT]
        rwa [add_comm] at this

/-- **Abel's direction, algebraic core.** -/
theorem abel_core (f : k[X]) {g : ℕ} (hf : f.natDegree = 2 * g + 1) (hfsq : Squarefree f)
    (h2 : (2 : k) ≠ 0) (s : Finset ι) (α β : ι → k) (hβ : ∀ i ∈ s, β i ≠ 0)
    (hαβ : ∀ i ∈ s, β i ^ 2 = f.eval (α i)) (hinj : Set.InjOn α s) (t : Finset ℕ)
    (u : ℕ → k[X] × k[X]) (hcop : ∀ j ∈ t, IsCoprime (u j).1 (u j).2) (m : ι → ℕ → ℕ)
    (ε : ι → ℕ → ℤ) (hε : ∀ i ∈ s, ∀ j ∈ t, ε i j = 1 ∨ ε i j = -1) (lam : ℕ → k)
    (gq : ℕ → k[X]) (hlam : ∀ j ∈ t, lam j ≠ 0) (hgq : ∀ j ∈ t, gq j ∣ f)
    (hfac : ∀ j ∈ t, hnorm f (u j) = C (lam j) * (∏ i ∈ s, (X - C (α i)) ^ m i j) * gq j)
    (hval : ∀ i ∈ s, ∀ j ∈ t, 0 < m i j → (u j).1.eval (α i) = ε i j * β i * (u j).2.eval (α i))
    (w : ℕ → ℤ) :
    ∃ ψ : k[X] × k[X], ψ ≠ (0, 0) ∧
      PoleLE g ψ (∑ i ∈ s, 2 * (∑ j ∈ t, w j * (m i j * -ε i j)).natAbs) ∧
      ∀ i ∈ s, VanishAt f ψ.1 ψ.2 (α i) ((∑ j ∈ t, w j * (m i j * -ε i j)).sign * β i)
        (2 * (∑ j ∈ t, w j * (m i j * -ε i j)).natAbs) := by
  classical
  have hfo : Odd f.natDegree := ⟨g, by omega⟩
  obtain ⟨F, hF0, ⟨c, hc, hNF⟩, hFv⟩ := abel_product f hfo hfsq h2 s α β hβ hαβ t u hcop m ε hε
    lam gq hlam hgq hfac hval w t le_rfl
  set e : ι → ℤ := fun i ↦ ∑ j ∈ t, w j * (m i j * -ε i j) with hedef
  set zP := zp w m ε t
  set zM := zm w m ε t
  have hdiff : ∀ i ∈ s, (zP i : ℤ) - zM i = 2 * e i := by
    intro i hi
    simp only [zP, zM, zp, zm, Nat.cast_sum, ← Finset.sum_sub_distrib, e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj ↦ (sign_terms (w j) (ε i j) (hε i hi j hj) (m i j)).1
  set d : ι → ℕ := fun i ↦ min (zP i) (zM i)
  set W : k[X] := ∏ i ∈ s, (X - C (α i)) ^ d i
  have hW0 : W ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hdv : ∀ i ∈ s, (X - C (α i)) ^ d i ∣ F.1 ∧ (X - C (α i)) ^ d i ∣ F.2 := by
    intro i hi
    have h2Y : IsUnit (2 * β i) := IsUnit.mk0 _ (mul_ne_zero h2 (hβ i hi))
    exact dvd_of_vanish_both h2Y ((hFv i hi).1.mono (min_le_left _ _))
      ((hFv i hi).2.mono (min_le_right _ _))
  have hcop' : (s : Set ι).Pairwise (Function.onFun IsCoprime fun i ↦ (X - C (α i)) ^ d i) :=
    fun i hi j hj hij ↦ ((isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr fun h ↦ hij (hinj hi hj h)).isUnit)).pow
  obtain ⟨A, hA⟩ := Finset.prod_dvd_of_coprime hcop' fun i hi ↦ (hdv i hi).1
  obtain ⟨B, hB⟩ := Finset.prod_dvd_of_coprime hcop' fun i hi ↦ (hdv i hi).2
  have hFG : F = hsmul W (A, B) := Prod.ext hA hB
  refine ⟨(A, B), ?_, ?_, fun i hi ↦ ?_⟩
  · intro h; apply hF0; rw [hFG, h]; simp [hsmul]
  · -- the norm of `G`
    have hNG : hnorm f (A, B) = C c * ∏ i ∈ s, (X - C (α i)) ^ (2 * (e i).natAbs) := by
      have e1 : hnorm f F = W ^ 2 * hnorm f (A, B) := by rw [hFG]; simp [hsmul, hnorm]; ring
      rw [hNF] at e1
      apply mul_left_cancel₀ (pow_ne_zero 2 hW0)
      rw [← e1]
      simp only [W, ← Finset.prod_pow, ← pow_mul]
      rw [mul_left_comm, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      rw [← pow_add]
      congr 1
      have := hdiff i hi
      simp only [d]
      rcases le_total (zP i) (zM i) with h | h
      · rw [min_eq_left h]; omega
      · rw [min_eq_right h]; omega
    have hdeg : (hnorm f (A, B)).natDegree = ∑ i ∈ s, 2 * (e i).natAbs := by
      rw [hNG, natDegree_C_mul hc, natDegree_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C _).pow _]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    have := poleLE_hnorm hf (A, B)
    rwa [hdeg] at this
  · -- the zeros of `G`
    show VanishAt f A B (α i) ((e i).sign * β i) (2 * (e i).natAbs)
    obtain ⟨W', hW'⟩ : ∃ W', W = (X - C (α i)) ^ d i * W' ∧ W'.eval (α i) ≠ 0 := by
      refine ⟨∏ i' ∈ s.erase i, (X - C (α i')) ^ d i', (Finset.mul_prod_erase s _ hi).symm, ?_⟩
      rw [eval_prod]
      refine Finset.prod_ne_zero_iff.mpr fun i' hi' ↦ ?_
      rw [eval_pow, eval_sub, eval_X, eval_C]
      exact pow_ne_zero _ (sub_ne_zero.mpr fun h ↦ (Finset.ne_of_mem_erase hi')
        (hinj hi (Finset.mem_of_mem_erase hi') h).symm)
    have hsplit : F = hsmul ((X - C (α i)) ^ d i) (hsmul W' (A, B)) := by
      rw [hFG, hW'.1]; simp only [hsmul]; exact Prod.ext (by ring) (by ring)
    have hd := hdiff i hi
    rcases lt_trichotomy (e i) 0 with he | he | he
    · -- net zero at `(α, −β)`
      have hle : zP i ≤ zM i := by omega
      have hv := (hFv i hi).2
      rw [show zM i = 2 * (e i).natAbs + d i by simp only [d, min_eq_left hle]; omega,
        hsplit] at hv
      rw [Int.sign_eq_neg_one_of_neg he]
      have := VanishAt.of_hsmul_unit (IsUnit.mk0 _ hW'.2) (VanishAt.of_hsmul_pow hv)
      simpa using this
    · rw [he]; simp only [Int.natAbs_zero, mul_zero]; exact VanishAt.zero'' _ _ _ _ _
    · have hle : zM i ≤ zP i := by omega
      have hv := (hFv i hi).1
      rw [show zP i = 2 * (e i).natAbs + d i by simp only [d, min_eq_right hle]; omega,
        hsplit] at hv
      rw [Int.sign_eq_one_of_pos he]
      have := VanishAt.of_hsmul_unit (IsUnit.mk0 _ hW'.2) (VanishAt.of_hsmul_pow hv)
      simpa using this

end Product

end Jac
