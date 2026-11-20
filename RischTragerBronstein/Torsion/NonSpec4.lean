import RischTragerBronstein.Torsion.NonSpec3

/-!
# Non-special base points exist (4): adding a point

With `∑ⱼ δⱼ = g + n − 1` (`δ₀ = 0`), a configuration of `r < g` fibres whose kernel space at level `r` is
spanned by `e0 = ∏ₗ (x − x_l)` (i.e. `ℓ(P₁ + ⋯ + P_r) = 1`) can be extended by a point of any `k ≥ max δ`
fresh admissible fibres keeping this property (**`exists_step`**). Otherwise every point `(t, j)` of the
fresh fibres carries a function `h_{t,j}` of `ℓ(D + P_{t,j})`, and the functions
`∏_{t' ≠ t} (x − x_{t'}) h_{t,j}` show that evaluation at the `k n` fresh points is onto on the kernel space
`U` at level `r + k`, whose dimension is `k n + r − g + 1` (`finrank_kerSp`); but it also kills
`∏ (x − x_t) e0 ≠ 0`, so `k n ≤ k n + r − g`.

**`exists_nonspecial`**: given an infinite supply of admissible fibres, there are `g` fibres with distinct
abscissae and chosen points whose kernel space at level `g` is spanned by `e0`.
-/

open Polynomial Module

namespace Curves

open CPoly Sup GTors

section Step

variable {K : Type*} [Field K] {n : ℕ} {B : Fin n → K[X][X]} (δ : Fin n → ℕ)

lemma evPt_mulP (x y : K) (p : K[X]) (c : Fin n → K[X]) :
    evPt B x y (fun j ↦ p * c j) = p.eval x * evPt B x y c := by
  simp only [evPt_apply, eval_mul, Finset.mul_sum, mul_assoc]

lemma mem_Vsp_mulP {m d : ℕ} (p : K[X]) (hp : p.natDegree ≤ d) (c : Fin n → K[X])
    (hc : c ∈ Vsp K δ m) : (fun j ↦ p * c j) ∈ Vsp K δ (m + d) := by
  rw [mem_Vsp] at hc ⊢
  intro j
  have h1 := hc j
  rw [mem_degreeLT] at h1 ⊢
  by_cases h0 : c j = 0
  · rw [h0, mul_zero, degree_zero]; exact WithBot.bot_lt_coe _
  by_cases hp0 : p = 0
  · rw [hp0, zero_mul, degree_zero]; exact WithBot.bot_lt_coe _
  rw [← natDegree_lt_iff_degree_lt h0] at h1
  rw [← natDegree_lt_iff_degree_lt (mul_ne_zero hp0 h0), natDegree_mul hp0 h0]
  omega

/-- The product `∏ₜ (x − x_t)` over a family of fibres, restricted to a finset. -/
noncomputable def prodXs {k : ℕ} (gs : Fin k → AdmFib B) (s : Finset (Fin k)) : K[X] :=
  ∏ t ∈ s, (X - Polynomial.C (gs t).x)

lemma natDegree_prodXs {k : ℕ} (gs : Fin k → AdmFib B) (s : Finset (Fin k)) :
    (prodXs gs s).natDegree = s.card := by
  rw [prodXs, natDegree_prod _ _ fun t _ ↦ X_sub_C_ne_zero _]
  simp

lemma prodXs_ne_zero {k : ℕ} (gs : Fin k → AdmFib B) (s : Finset (Fin k)) : prodXs gs s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun t _ ↦ X_sub_C_ne_zero _

lemma prodXs_eval_mem {k : ℕ} (gs : Fin k → AdmFib B) (s : Finset (Fin k)) (t : Fin k) (ht : t ∈ s) :
    (prodXs gs s).eval (gs t).x = 0 := by
  rw [prodXs, eval_prod]
  exact Finset.prod_eq_zero ht (by simp)

lemma prodXs_eval_ne {k : ℕ} (gs : Fin k → AdmFib B) (s : Finset (Fin k)) (x : K)
    (hx : ∀ t ∈ s, x ≠ (gs t).x) : (prodXs gs s).eval x ≠ 0 := by
  rw [prodXs, eval_prod]
  exact Finset.prod_ne_zero_iff.mpr fun t ht ↦ by simpa [sub_eq_zero] using hx t ht

lemma prodX_snoc {r : ℕ} (f : Fin r → AdmFib B) (fb : AdmFib B) :
    prodX (Fin.snoc f fb : Fin (r + 1) → AdmFib B) = prodX f * (X - Polynomial.C fb.x) := by
  simp [prodX, Fin.prod_univ_castSucc]

variable (hn : 0 < n)

lemma e0_snoc {r : ℕ} (f : Fin r → AdmFib B) (fb : AdmFib B) :
    e0 hn (Fin.snoc f fb : Fin (r + 1) → AdmFib B) = fun j ↦ (X - Polynomial.C fb.x) * e0 hn f j := by
  classical
  funext j
  by_cases hj : j = ⟨0, hn⟩
  · subst hj; simp only [e0, Pi.single_eq_same, prodX_snoc]; ring
  · simp [e0, Pi.single_eq_of_ne hj]

lemma e0_mem_Vsp (hδ0 : δ ⟨0, hn⟩ = 0) {r : ℕ} (f : Fin r → AdmFib B) : e0 hn f ∈ Vsp K δ r :=
  ((mem_kerSp δ r r f (fun _ ↦ ⟨0, hn⟩) _).mp (e0_mem_kerSp δ hn hδ0 r r le_rfl f _)).1

lemma e0_evPt {r : ℕ} (f : Fin r → AdmFib B) (l : Fin r) (y : K) : evPt B (f l).x y (e0 hn f) = 0 := by
  rw [evPt_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  by_cases hj : j = ⟨0, hn⟩
  · subst hj; rw [e0, Pi.single_eq_same, prodX_eval, zero_mul]
  · rw [e0, Pi.single_eq_of_ne hj, eval_zero, zero_mul]

/-- **Vanishing on a whole fresh fibre** lands in the span of `e0`. -/
lemma mem_span_of_vanish {r : ℕ} (f : Fin r → AdmFib B) (j₀ : Fin r → Fin n)
    (h1 : kerSp δ r r f j₀ ≤ K ∙ e0 hn f) (fb : AdmFib B) (hdis : ∀ l, (f l).x ≠ fb.x) (j : Fin n)
    (h : Fin n → K[X])
    (hh : h ∈ kerSp δ (r + 1) (r + 1) (Fin.snoc f fb : Fin (r + 1) → AdmFib B)
      (Fin.snoc j₀ j : Fin (r + 1) → Fin n))
    (hj : evPt B fb.x (fb.ys j) h = 0) :
    h ∈ K ∙ e0 hn (Fin.snoc f fb : Fin (r + 1) → AdmFib B) := by
  rw [mem_kerSp] at hh
  obtain ⟨hV, hv⟩ := hh
  have hall : ∀ k, evPt B fb.x (fb.ys k) h = 0 := fun k ↦ by
    by_cases hk : k = j
    · rw [hk]; exact hj
    · have := hv (Fin.last r) k (by simpa using hk)
      simpa using this
  obtain ⟨h', hV', rfl⟩ := exists_div_of_vanish δ r h hV fb hall
  have hk' : h' ∈ kerSp δ r r f j₀ := by
    rw [mem_kerSp]
    refine ⟨hV', fun l k hk ↦ ?_⟩
    have := hv l.castSucc k (by simpa using hk)
    simp only [Fin.snoc_castSucc] at this
    rw [evPt_mulP] at this
    simp only [eval_sub, eval_X, eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (hdis l))
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h1 hk')
  refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
  rw [e0_snoc, ← ha]
  funext j'
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

variable (B) in
/-- Evaluation at all points of a family of fibres. -/
noncomputable def evFib {k : ℕ} (gs : Fin k → AdmFib B) : (Fin n → K[X]) →ₗ[K] (Fin k × Fin n → K) :=
  LinearMap.pi fun q : Fin k × Fin n ↦ evPt B (gs q.1).x ((gs q.1).ys q.2)

lemma sum_sub_delta (N : ℕ) (hN : ∀ j, δ j ≤ N) : ∑ j, (N - δ j) + ∑ j, δ j = n * N := by
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ ↦ Nat.sub_add_cancel (hN j)]
  simp

/-- **Adding a point.** -/
theorem exists_step (hδ0 : δ ⟨0, hn⟩ = 0) {g : ℕ} (hsum : ∑ j, δ j = g + n - 1) (r k : ℕ)
    (hr : r < g) (hk : ∀ j, δ j ≤ k) (f : Fin r → AdmFib B) (hx : Function.Injective fun l ↦ (f l).x)
    (j₀ : Fin r → Fin n) (h1 : kerSp δ r r f j₀ ≤ K ∙ e0 hn f) (gs : Fin k → AdmFib B)
    (hgx : Function.Injective fun t ↦ (gs t).x) (hdis : ∀ l t, (f l).x ≠ (gs t).x) :
    ∃ t j, kerSp δ (r + 1) (r + 1) (Fin.snoc f (gs t) : Fin (r + 1) → AdmFib B)
      (Fin.snoc j₀ j : Fin (r + 1) → Fin n) ≤ K ∙ e0 hn (Fin.snoc f (gs t) : Fin (r + 1) → AdmFib B) := by
  classical
  by_contra hne
  push_neg at hne
  have hne' := fun t j ↦ SetLike.not_le_iff_exists.mp (hne t j)
  choose h hmem hnot using hne'
  set U := kerSp δ (r + k) r f j₀ with hU
  set ev : U →ₗ[K] (Fin k × Fin n → K) := evFib B gs ∘ₗ U.subtype with hev
  -- the functions `H_{t,j}`
  have hH : ∀ t j, (fun j' ↦ prodXs gs (Finset.univ.erase t) * h t j j') ∈ U := by
    intro t j
    have hm := (mem_kerSp _ _ _ _ _ _).mp (hmem t j)
    rw [hU, mem_kerSp]
    refine ⟨?_, fun l k' hk' ↦ ?_⟩
    · have := mem_Vsp_mulP δ (d := k - 1) (prodXs gs (Finset.univ.erase t))
        (by rw [natDegree_prodXs]; simp) _ hm.1
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h0 ↦ (h0 ▸ t).elim0
      rwa [show r + 1 + (k - 1) = r + k by omega] at this
    · rw [evPt_mulP]
      have := hm.2 l.castSucc k' (by simpa using hk')
      simp only [Fin.snoc_castSucc] at this
      rw [this, mul_zero]
  have hsingle : ∀ q : Fin k × Fin n, Pi.single q 1 ∈ LinearMap.range ev := by
    rintro ⟨t, j⟩
    have hm := (mem_kerSp _ _ _ _ _ _).mp (hmem t j)
    have hv0 : evPt B (gs t).x ((gs t).ys j) (h t j) ≠ 0 := fun h0 ↦
      hnot t j (mem_span_of_vanish δ hn f j₀ h1 (gs t) (fun l ↦ hdis l t) j _ (hmem t j) h0)
    have hp0 : (prodXs gs (Finset.univ.erase t)).eval (gs t).x ≠ 0 :=
      prodXs_eval_ne gs _ _ fun t' ht' h' ↦ (Finset.ne_of_mem_erase ht') (hgx h').symm
    set v := (prodXs gs (Finset.univ.erase t)).eval (gs t).x * evPt B (gs t).x ((gs t).ys j) (h t j)
    refine ⟨v⁻¹ • ⟨_, hH t j⟩, ?_⟩
    rw [map_smul]
    funext ⟨t', j'⟩
    simp only [hev, LinearMap.comp_apply, Submodule.subtype_apply, evFib, LinearMap.pi_apply,
      Pi.smul_apply, smul_eq_mul, evPt_mulP]
    by_cases htt : t' = t
    · subst htt
      by_cases hjj : j' = j
      · subst hjj
        rw [Pi.single_eq_same]
        exact inv_mul_cancel₀ (mul_ne_zero hp0 hv0)
      · rw [Pi.single_eq_of_ne (by simp [hjj])]
        have := hm.2 (Fin.last r) j' (by simpa using hjj)
        simp only [Fin.snoc_last] at this
        rw [this, mul_zero, mul_zero]
    · rw [Pi.single_eq_of_ne (by simp [htt]), prodXs_eval_mem gs _ t' (by simp [htt]), zero_mul,
        mul_zero]
  have htop : LinearMap.range ev = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin k × Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    rw [Pi.basisFun_apply]
    exact hsingle q
  -- a nonzero element of the kernel
  have hE : (fun j ↦ prodXs gs Finset.univ * e0 hn f j) ∈ U := by
    rw [hU, mem_kerSp]
    refine ⟨?_, fun l k' _ ↦ ?_⟩
    · have := mem_Vsp_mulP δ (d := k) (prodXs gs Finset.univ) (by rw [natDegree_prodXs]; simp) _
        (e0_mem_Vsp δ hn hδ0 f)
      exact this
    · rw [evPt_mulP, e0_evPt, mul_zero]
  have hker : LinearMap.ker ev ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨⟨_, hE⟩, ?_, fun h0 ↦ ?_⟩
    · rw [LinearMap.mem_ker]
      funext ⟨t, j⟩
      simp only [hev, LinearMap.comp_apply, Submodule.subtype_apply, evFib, LinearMap.pi_apply,
        evPt_mulP, Pi.zero_apply]
      rw [prodXs_eval_mem gs _ t (Finset.mem_univ t), zero_mul]
    · have := congrFun (congrArg Subtype.val h0) ⟨0, hn⟩
      simp only [e0, Pi.single_eq_same, ZeroMemClass.coe_zero, Pi.zero_apply] at this
      exact mul_ne_zero (prodXs_ne_zero gs _) (prodX_ne_zero f) this
  have hker1 : 1 ≤ finrank K (LinearMap.ker ev) :=
    Nat.one_le_iff_ne_zero.mpr fun h0 ↦ hker (Submodule.finrank_eq_zero.mp h0)
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at hrn
  have hdim := finrank_kerSp δ f hx (r + k) (fun j ↦ by have := hk j; omega) j₀
  have hs := sum_sub_delta δ (r + k + 1) (fun j ↦ by have := hk j; omega)
  rw [← hU] at hdim
  have hA : n * (r + k + 1) = r * n + k * n + n := by ring
  have hB : r * (n - 1) + r = r * n := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  generalize r * n = a at *
  generalize k * n = b at *
  omega

end Step

section Exists

variable {K : Type*} [Field K] {n : ℕ} {B : Fin n → K[X][X]} (δ : Fin n → ℕ)

/-- `k` fresh admissible fibres with distinct abscissae outside `s`. -/
lemma exists_fresh (Q : AdmFib B → Prop) (hsup : ∀ s : Finset K, ∃ fb : AdmFib B, fb.x ∉ s ∧ Q fb)
    (k : ℕ) (s : Finset K) :
    ∃ gs : Fin k → AdmFib B, Function.Injective (fun t ↦ (gs t).x) ∧ ∀ t, (gs t).x ∉ s ∧ Q (gs t) := by
  classical
  induction k with
  | zero => exact ⟨Fin.elim0, fun a ↦ a.elim0, fun a ↦ a.elim0⟩
  | succ k ih =>
    obtain ⟨gs, hinj, hs⟩ := ih
    obtain ⟨fb, hfb, hQ⟩ := hsup (s ∪ Finset.univ.image fun t ↦ (gs t).x)
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or,
      not_exists] at hfb
    refine ⟨Fin.snoc gs fb, fun a b hab ↦ ?_, fun t ↦ ?_⟩
    · induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b => simp at hab; exact absurd hab.symm (hfb.2 b)
      | cast a =>
        induction b using Fin.lastCases with
        | last => simp at hab; exact absurd hab (hfb.2 a)
        | cast b => simp at hab; rw [hinj hab]
    · induction t using Fin.lastCases with
      | last => simpa using ⟨hfb.1, hQ⟩
      | cast t => simpa using hs t

variable (hn : 0 < n)

/-- **Non-special base points exist.** -/
theorem exists_nonspecial (hδ0 : δ ⟨0, hn⟩ = 0) (hδ : ∀ j, j ≠ ⟨0, hn⟩ → 1 ≤ δ j) {g : ℕ}
    (hsum : ∑ j, δ j = g + n - 1) (Q : AdmFib B → Prop)
    (hsup : ∀ s : Finset K, ∃ fb : AdmFib B, fb.x ∉ s ∧ Q fb) :
    ∃ f : Fin g → AdmFib B, Function.Injective (fun l ↦ (f l).x) ∧ (∀ l, Q (f l)) ∧
      ∃ j₀ : Fin g → Fin n, kerSp δ g g f j₀ ≤ K ∙ e0 hn f := by
  classical
  suffices H : ∀ r ≤ g, ∃ f : Fin r → AdmFib B, Function.Injective (fun l ↦ (f l).x) ∧
      (∀ l, Q (f l)) ∧ ∃ j₀ : Fin r → Fin n, kerSp δ r r f j₀ ≤ K ∙ e0 hn f from H g le_rfl
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨Fin.elim0, fun a ↦ a.elim0, fun a ↦ a.elim0, Fin.elim0, ?_⟩
    have h1 := finrank_kerSp_nil δ hn hδ0 hδ (Fin.elim0 : Fin 0 → AdmFib B) Fin.elim0
    have hmem := e0_mem_kerSp δ hn hδ0 0 0 le_rfl (Fin.elim0 : Fin 0 → AdmFib B) Fin.elim0
    have hne : (⟨_, hmem⟩ : kerSp δ 0 0 (Fin.elim0 : Fin 0 → AdmFib B) Fin.elim0) ≠ 0 :=
      fun h0 ↦ e0_ne_zero hn _ (congrArg Subtype.val h0)
    intro c hc
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp h1 ⟨c, hc⟩
    exact Submodule.mem_span_singleton.mpr ⟨a, congrArg Subtype.val ha⟩
  | succ r ih =>
    intro hr
    obtain ⟨f, hx, hQ, j₀, h1⟩ := ih (by omega)
    set k := Finset.univ.sup δ
    obtain ⟨gs, hgx, hgs⟩ := exists_fresh Q hsup k (Finset.univ.image fun l ↦ (f l).x)
    have hdis : ∀ l t, (f l).x ≠ (gs t).x := fun l t h ↦ (hgs t).1 (by simp [← h])
    obtain ⟨t, j, ht⟩ := exists_step δ hn hδ0 hsum r k (by omega)
      (fun j ↦ Finset.le_sup (f := δ) (Finset.mem_univ j)) f hx j₀ h1 gs hgx hdis
    refine ⟨Fin.snoc f (gs t), fun a b hab ↦ ?_, fun l ↦ ?_, Fin.snoc j₀ j, ht⟩
    swap
    · induction l using Fin.lastCases with
      | last => simpa using (hgs t).2
      | cast l => simpa using hQ l
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast b => simp at hab; exact absurd hab.symm (hdis b t)
    | cast a =>
      induction b using Fin.lastCases with
      | last => simp at hab; exact absurd hab (hdis a t)
      | cast b => simp at hab; rw [hx hab]

end Exists

end Curves
