import RischTragerBronstein.Mixed.KXExp2

/-!
# The Mordell–Weil exception when the divisors are dependent

In the exception of `kxDecide` (`P₊ − ∞` not torsion), a class divisor `Δ_k` may be dependent on
`δ₀ = P₊ − P₋`: `N Δ_k + μ δ₀` principal. Then the generator `Z = W² ∏(x − c_q)^{−N m_q} x^{−|μ|}`
of a witness `W` (orders `N Γ_k + |μ| P_±`) has divisor `N Δ_k + μ δ₀` (`ordAt_Zd`), and — because no
non-zero multiple of `δ₀` is principal (`nt_dZ`) — the divisor of every logarithm of a Liouville
form lies in the span of the generators, so a Liouville form forces the parametric Risch equation
with one column per generator (`kxe_dep`).
-/

open Polynomial IntermediateField

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

open Classical in
/-- The divisor of an augmented class: `N Γ_k + M (0, σ)`. -/
lemma gammaQ_aug {r nk : ℕ} (c β : Fin r → C) (m : Fin r → ℕ) (cl : Fin r → Fin nk) (k : Fin nk)
    (σ : C) (N M : ℕ) (Q : K × K) :
    gammaQ (Fin.cons 0 c) (Fin.cons σ β) (mK (Fin.cons M fun q ↦ N * m q) (Fin.cons k cl) k) Q =
      N * gammaQ c β (mK m cl k) Q + M * gammaP (algebraMap C K σ) Q := by
  simp only [gammaQ, gammaP, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mK, map_zero,
    if_true, Finset.mul_sum]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun q _ ↦ ?_
    split_ifs <;> simp
  · split_ifs <;> simp

section Gen

variable (hn2 : S.n = 2) (β₀ : K) (hβ₀ : β₀ ≠ 0)
  (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)
  {r nk : ℕ} (c β : Fin r → C) (hc : Function.Injective c) (hc0 : ∀ q, c q ≠ 0)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (cl : Fin r → Fin nk)

/-- The generator of a class witness with an extra `|μ| P_±` part. -/
noncomputable def zD (k : Fin nk) (W : C⟮S.x⟯⟮S.y⟯) (N M : ℕ) : C⟮S.x⟯⟮S.y⟯ :=
  S.zK c m cl k W N * S.xE ^ (-(M : ℤ))

open Classical in
include hn2 hβ₀ hv0 hc hc0 hβ in
/-- **The divisor of the generator**: `N Δ_k + μ δ₀` (`μ = ±M` according to the sign `σ`). -/
lemma ordAt_zD (k : Fin nk) (W : C⟮S.x⟯⟮S.y⟯) (hW : W ≠ 0) (N M : ℕ) (σ : K)
    (hσ : σ = β₀ ∨ σ = -β₀)
    (hWord : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K W α β' = N * gammaQ c β (mK m cl k) (α, β') + M * gammaP σ (α, β')) :
    S.zD c m cl k W N M ≠ 0 ∧ ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K (S.zD c m cl k W N M) α β' : ℚ) =
        N * dK c β m cl k (α, β') + (if σ = β₀ then (M : ℚ) else -(M : ℚ)) * dZ β₀ (α, β') := by
  have hX : ∀ q, S.polyX (X - Polynomial.C (c q)) ≠ 0 := fun q ↦ S.polyX_ne_zero (X_sub_C_ne_zero _)
  have hpr : ∏ q, S.polyX (X - Polynomial.C (c q)) ^ (-((N * mK m cl k q : ℕ) : ℤ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q _ ↦ zpow_ne_zero _ (hX q)
  have hzK : S.zK c m cl k W N ≠ 0 := mul_ne_zero (pow_ne_zero _ hW) hpr
  have hxp : S.xE ^ (-(M : ℤ)) ≠ 0 := zpow_ne_zero _ S.xE_ne
  refine ⟨mul_ne_zero hzK hxp, fun α β' hv ↦ ?_⟩
  rw [zD, S.ordAt_mul hv hzK hxp, zK, S.ordAt_mul hv (pow_ne_zero _ hW) hpr, S.ordAt_pow hv,
    hWord α β' hv, S.ordAt_prod hv _ _ (fun q _ ↦ zpow_ne_zero _ (hX q)), S.ordAt_zpow hv,
    S.ordAt_xE α β' hv]
  simp only [S.ordAt_zpow hv, S.ordAt_polyX_lin _ _ _ hv]
  by_cases hα : ∃ q, α = algebraMap C K (c q)
  · obtain ⟨q, rfl⟩ := hα
    have hcq0 : algebraMap C K (c q) ≠ 0 := fun h ↦ hc0 q ((algebraMap C K).injective
      (by rw [h, map_zero]))
    have hb' := S.over_cq_ne c β hβ q β' hv
    have hsum : ∑ q', -((N * mK m cl k q' : ℕ) : ℤ) *
        (if algebraMap C K (c q) = algebraMap C K (c q') then (if β' = 0 then (S.n : ℤ) else 1)
          else 0) = -((N * mK m cl k q : ℕ) : ℤ) := by
      rw [Finset.sum_eq_single q]
      · simp [hb']
      · intro q' _ hq'
        have : algebraMap C K (c q) ≠ algebraMap C K (c q') := fun h ↦
          hq' (hc ((algebraMap C K).injective h)).symm
        simp [this]
      · simp
    rw [hsum, gammaQ_at c β hc (mK m cl k) q β', gammaP_apply, dZ_off β₀ _ β' hcq0]
    simp only [Prod.ext_iff, hcq0, false_and, if_false, mul_zero, add_zero]
    rcases S.over_cq c β hβ hn2 q β' hv with rfl | rfl
    · rw [if_pos rfl, dK_plus S c β hc hβ m cl k q]; push_cast; ring
    · rw [if_neg (S.neg_ne_q c β hβ q), dK_minus S c β hc hβ m cl k q]; push_cast; ring
  · push Not at hα
    rw [gammaQ_off c β (mK m cl k) α β' hα, dK_off c β m cl k α β' hα]
    rw [Finset.sum_eq_zero fun q _ ↦ by rw [if_neg (hα q)]; ring]
    rw [gammaP_apply]
    by_cases h0 : α = 0
    · subst h0
      have hβ' : β' ≠ 0 := by
        intro h0; rw [h0, zero_pow S.hn.ne', ← hv0] at hv
        exact hβ₀ (pow_eq_zero_iff S.hn.ne' |>.mp hv.symm)
      rcases S.over_zero' hn2 β₀ hv0 β' hv with h | h <;> rcases hσ with hs | hs <;> subst β' <;>
        subst σ
      · simp [dZ_plus β₀ hβ₀, hβ₀]; ring
      · simp [dZ_plus β₀ hβ₀, hβ₀, neg_ne_self hβ₀, Prod.ext_iff]
        exact fun h ↦ absurd h.symm (neg_ne_self hβ₀)
      · simp [dZ_minus β₀ hβ₀, hβ₀, neg_ne_self hβ₀, Prod.ext_iff]
      · simp [dZ_minus β₀ hβ₀, hβ₀, neg_ne_self hβ₀]; ring
    · simp [dZ_off β₀ α β' h0, h0, Prod.ext_iff]

open Classical in
include hn2 hβ₀ hv0 hc hc0 hβ in
/-- **The converse of `ordAt_zD`**: a function of divisor `N Δ_k + μ δ₀`, times
`∏ (x − c_q)^{N m_q} x^{|μ|}`, has divisor `2N Γ_k + 2|μ| P_{sign μ}`. -/
lemma ordAt_unzD (k : Fin nk) (f : C⟮S.x⟯⟮S.y⟯) (hf : f ≠ 0) (N : ℕ) (μ : ℤ)
    (hfo : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K f α β' : ℚ) = N * dK c β m cl k (α, β') + μ * dZ β₀ (α, β')) :
    f * (∏ q, S.polyX (X - Polynomial.C (c q)) ^ (N * mK m cl k q)) * S.xE ^ μ.natAbs ≠ 0 ∧
    ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K (f * (∏ q, S.polyX (X - Polynomial.C (c q)) ^ (N * mK m cl k q)) *
        S.xE ^ μ.natAbs) α β' =
        (2 * N : ℕ) * gammaQ c β (mK m cl k) (α, β') +
          (2 * μ.natAbs : ℕ) * gammaP (if 0 ≤ μ then β₀ else -β₀) (α, β') := by
  have hX : ∀ q, S.polyX (X - Polynomial.C (c q)) ≠ 0 := fun q ↦ S.polyX_ne_zero (X_sub_C_ne_zero _)
  have hpr : ∏ q, S.polyX (X - Polynomial.C (c q)) ^ (N * mK m cl k q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q _ ↦ pow_ne_zero _ (hX q)
  have hxp : S.xE ^ μ.natAbs ≠ 0 := pow_ne_zero _ S.xE_ne
  have h1 : f * (∏ q, S.polyX (X - Polynomial.C (c q)) ^ (N * mK m cl k q)) ≠ 0 :=
    mul_ne_zero hf hpr
  refine ⟨mul_ne_zero h1 hxp, fun α β' hv ↦ ?_⟩
  apply Int.cast_injective (α := ℚ)
  rw [S.ordAt_mul hv h1 hxp, S.ordAt_mul hv hf hpr,
    S.ordAt_prod hv _ _ (fun q _ ↦ pow_ne_zero _ (hX q)), S.ordAt_pow hv, S.ordAt_xE α β' hv]
  simp only [S.ordAt_pow hv, S.ordAt_polyX_lin _ _ _ hv]
  push_cast
  rw [hfo α β' hv]
  by_cases hα : ∃ q, α = algebraMap C K (c q)
  · obtain ⟨q, rfl⟩ := hα
    have hcq0 : algebraMap C K (c q) ≠ 0 := fun h ↦ hc0 q ((algebraMap C K).injective
      (by rw [h, map_zero]))
    have hb' := S.over_cq_ne c β hβ q β' hv
    have hsum : ∑ q', (N : ℚ) * (mK m cl k q' : ℚ) *
        (if algebraMap C K (c q) = algebraMap C K (c q') then (if β' = 0 then (S.n : ℚ) else 1)
          else 0) = (N : ℚ) * (mK m cl k q : ℚ) := by
      rw [Finset.sum_eq_single q]
      · simp [hb']
      · intro q' _ hq'
        have : algebraMap C K (c q) ≠ algebraMap C K (c q') := fun h ↦
          hq' (hc ((algebraMap C K).injective h)).symm
        simp [this]
      · simp
    rw [hsum]
    rw [gammaQ_at c β hc (mK m cl k) q β', gammaP_apply, dZ_off β₀ _ β' hcq0]
    simp only [hcq0, false_and, if_false, mul_zero, add_zero]
    rcases S.over_cq c β hβ hn2 q β' hv with rfl | rfl
    · rw [if_pos rfl, dK_plus S c β hc hβ m cl k q]; push_cast; ring
    · rw [if_neg (S.neg_ne_q c β hβ q), dK_minus S c β hc hβ m cl k q]; push_cast; ring
  · push Not at hα
    rw [gammaQ_off c β (mK m cl k) α β' hα, dK_off c β m cl k α β' hα]
    rw [Finset.sum_eq_zero fun q _ ↦ by rw [if_neg (hα q)]; simp]
    rw [gammaP_apply]
    by_cases h0 : α = 0
    · subst h0
      have hβ' : β' ≠ 0 := by
        intro h0; rw [h0, zero_pow S.hn.ne', ← hv0] at hv
        exact hβ₀ (pow_eq_zero_iff S.hn.ne' |>.mp hv.symm)
      have hne := neg_ne_self hβ₀
      rcases S.over_zero' hn2 β₀ hv0 β' hv with h | h <;> subst β' <;>
        rcases le_or_gt 0 μ with hμ | hμ
      · have hq : (0 : ℚ) ≤ μ := by exact_mod_cast hμ
        simp [dZ_plus β₀ hβ₀, hβ₀, hμ, abs_of_nonneg hq] <;> ring
      · have hq : (μ : ℚ) < 0 := by exact_mod_cast hμ
        simp [dZ_plus β₀ hβ₀, hβ₀, not_le.mpr hμ, (neg_ne_self hβ₀).symm, abs_of_neg hq] <;> ring
      · have hq : (0 : ℚ) ≤ μ := by exact_mod_cast hμ
        simp [dZ_minus β₀ hβ₀, hβ₀, hμ, hne, abs_of_nonneg hq] <;> ring
      · have hq : (μ : ℚ) < 0 := by exact_mod_cast hμ
        simp [dZ_minus β₀ hβ₀, hβ₀, not_le.mpr hμ, abs_of_neg hq] <;> ring
    · simp [dZ_off β₀ α β' h0, h0]

end Gen

section ExpDep

variable (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η * X))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (hgood : ∀ α : K, ¬ α = 0 → α′ ≠ ((Polynomial.C η * X).map (algebraMap C K)).eval α)
  (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
  {r nk : ℕ} (c β : Fin r → C) (hc : Function.Injective c) (hc0 : ∀ q, c q ≠ 0)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (cl : Fin r → Fin nk)
  (ρ : Fin nk → C)
  (P : C[X]) (l : ℕ) (b : L) (hb : b ∈ C⟮S.x⟯)
  (D : C[X]) (R : Fin r → C[X]) (hDR : ∀ q, D = (X - Polynomial.C (c q)) * R q)
  (hRne : ∀ q, (R q).eval (c q) ≠ 0)
  (hDoff : ∀ α : K, ¬ α = 0 → (∀ q, α ≠ algebraMap C K (c q)) → (D.map (algebraMap C K)).eval α ≠ 0)
  (hbP : b * aeval S.x (D * S.p ^ l) = aeval S.x P)
  (hres : ∀ q, P.eval (c q) * β q = m q * ρ (cl q) * ((Polynomial.C η * X).eval (c q) - (c q)′) *
    (R q * S.p ^ l).eval (c q))
  (hn2 : S.n = 2) (hcop : Nat.Coprime S.n S.p.natDegree) (β₀ : K) (hβ₀ : β₀ ≠ 0)
  (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)

open Classical in
include hx hK hgood hconstC hc hc0 hβ hb hDR hRne hDoff hbP hres hn2 hcop hβ₀ hv0 in
/-- **Dependent classes.** If no non-zero multiple of `δ₀` is principal and every class `Δ_k` has a
witness `W_k` of `N_k Γ_k + M_k P_{σ_k}` (`σ_k = ±β₀`, so that `N_k Δ_k ± M_k δ₀` is principal),
then a Liouville form for `b y` forces `b y = (a y)′ + ∑ e_k B_k y` (the `B_k` of the `W_k`). -/
theorem kxe_dep
    (hntZ : ∀ f : C⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ M : ℤ, (∀ α β' : K,
      β' ^ S.n = (S.p.map (algebraMap C K)).eval α → (S.ordAt K f α β' : ℚ) = M * dZ β₀ (α, β')) →
      M = 0)
    (N M : Fin nk → ℕ) (hN : ∀ kk, 0 < N kk) (σ : Fin nk → K) (hσ : ∀ kk, σ kk = β₀ ∨ σ kk = -β₀)
    (W : Fin nk → C⟮S.x⟯⟮S.y⟯) (hW : ∀ kk, W kk ≠ 0)
    (hWord : ∀ kk, ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K (W kk) α β' = N kk * gammaQ c β (mK m cl kk) (α, β') + M kk * gammaP (σ kk) (α, β'))
    (W0 W1 : Fin nk → L) (hW0 : ∀ i, W0 i ∈ C⟮S.x⟯) (hW1 : ∀ i, W1 i ∈ C⟮S.x⟯)
    (hWe : ∀ i, (W i : L) = W0 i + W1 i * S.y)
    (hNm : ∀ i, W0 i ^ 2 - W1 i ^ 2 * aeval S.x S.p ≠ 0) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ a ∈ C⟮S.x⟯, ∃ e : Fin nk → C, (∀ i, (algebraMap C L (e i))′ = 0) ∧
      b * S.y = (a * S.y)′ + ∑ i, algebraMap C L (e i) *
        ((W0 i * ((W1 i)′ + W1 i * (aeval S.x (mapCoeffs S.p + Polynomial.C η * X * derivative S.p) /
          ((S.n : L) * aeval S.x S.p))) - (W0 i)′ * W1 i) /
          (W0 i ^ 2 - W1 i ^ 2 * aeval S.x S.p) * S.y) := by
  classical
  obtain ⟨k, d, w, hw, heq', hdc, -, lam, hord, -⟩ :=
    S.kxm_core (K := K) (Polynomial.C η * X) hx hK (fun α ↦ α = 0) hgood hconstC c β hc
      (hbadc_of c hc0) hβ m cl ρ P l b hb D R hDR hRne hDoff hbP hres hn2 hbm s cs u hcs hu v hv heq
  -- the generators and their divisors `N_k (Δ_k + (μ_k / N_k) δ₀)`
  set mu : Fin nk → ℚ := fun kk ↦ if σ kk = β₀ then (M kk : ℚ) else -(M kk : ℚ) with hmu
  have hZd := fun kk ↦ S.ordAt_zD hn2 β₀ hβ₀ hv0 c β hc hc0 hβ m cl kk (W kk) (hW kk) (N kk) (M kk)
    (σ kk) (hσ kk) (hWord kk)
  set δ : Fin nk → K × K → ℚ := fun kk Q ↦ dK c β m cl kk Q + mu kk / N kk * dZ β₀ Q with hδ
  have hZdo : ∀ kk, ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K (S.zD c m cl kk (W kk) (N kk) (M kk)) α β' : ℚ) = N kk * δ kk (α, β') := by
    intro kk α β' hv
    rw [(hZd kk).2 α β' hv, hδ]
    have : (N kk : ℚ) ≠ 0 := by exact_mod_cast (hN kk).ne'
    field_simp
    simp only [hmu]
    split_ifs <;> ring
  have hxL : ((S.xE : C⟮S.x⟯⟮S.y⟯) : L) ≠ 0 := by rw [S.xE_val]; exact S.x_ne_zero
  have hldZ : ∀ kk, ∃ G ∈ C⟮S.x⟯, logDeriv ((S.zD c m cl kk (W kk) (N kk) (M kk) :
      C⟮S.x⟯⟮S.y⟯) : L) = 2 * logDeriv (W kk : L) + G := by
    intro kk
    obtain ⟨G, hG, hGe⟩ := S.ld_zK (Polynomial.C η * X) hx c m cl kk (W kk) (hW kk) (N kk)
    have hzK : ((S.zK c m cl kk (W kk) (N kk) : C⟮S.x⟯⟮S.y⟯) : L) ≠ 0 := by
      have h := (hZd kk).1
      intro h0; apply h; rw [zD, show S.zK c m cl kk (W kk) (N kk) = 0 from Subtype.ext h0, zero_mul]
    refine ⟨G - (M kk : L) * algebraMap C L η, sub_mem hG (mul_mem (IntermediateField.natCast_mem _ _)
      (IntermediateField.algebraMap_mem _ _)), ?_⟩
    rw [zD, IntermediateField.coe_mul,
      show ((S.xE ^ (-(M kk : ℤ)) : C⟮S.x⟯⟮S.y⟯) : L) = ((S.xE : C⟮S.x⟯⟮S.y⟯) : L) ^ (-(M kk : ℤ))
        from map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val _ _,
      logDeriv_mul _ _ hzK (zpow_ne_zero _ hxL), logDeriv_zpow' _ hxL, S.logDeriv_xE η hx, hGe]
    push_cast; ring
  choose GZ hGZ hGZe using hldZ
  have hlog : ∀ j < k, ∃ (e : Fin nk → ℚ) (G : L), G ∈ C⟮S.x⟯ ∧
      logDeriv (w j) = ∑ i, (e i : L) * logDeriv (W i : L) + G := by
    intro j hj
    set wj : C⟮S.x⟯⟮S.y⟯ := ⟨w j, (hw j hj).1⟩
    have hwj0 : wj ≠ 0 := fun h ↦ (hw j hj).2 (congrArg Subtype.val h)
    obtain ⟨hz0, hzo⟩ := S.kxe_norm hn2 β₀ hβ₀ hv0 c β hc0 m cl wj hwj0 (fun kk ↦ lam kk j)
      (fun α β' hv hα ↦ hord j hj α β' hv hα)
    set rr := S.ordAt K wj 0 β₀
    set ss := S.ordAt K wj 0 (-β₀)
    set z := wj ^ 2 * S.xE ^ (-(rr + ss))
    -- the `δ₀` defect `ν` vanishes
    set ν : ℚ := ((rr - ss : ℤ) : ℚ) - ∑ kk, 2 * lam kk j * (mu kk / N kk) with hν
    have hzo' : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
        (S.ordAt K z α β' : ℚ) = ∑ kk, (2 * lam kk j) * δ kk (α, β') + ((1 : ℤ) : ℚ) *
          (ν * dZ β₀ (α, β')) := by
      intro α β' hv
      rw [hzo α β' hv, hν, hδ]
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      push_cast
      simp only [sub_mul, Finset.sum_mul]
      ring_nf
    obtain ⟨Dn, hDn, y, hy, hyo⟩ := S.kx_kill_gen z hz0 (fun kk ↦ S.zD c m cl kk (W kk) (N kk) (M kk))
      (fun kk ↦ (hZd kk).1) N hN (fun kk ↦ 2 * lam kk j) δ (fun Q ↦ ν * dZ β₀ Q) 1 hzo' hZdo
    have hν0 : ν = 0 := by
      have hM := hntZ y hy (S.ordAt K y 0 β₀) (fun α β' hv ↦ by
        rw [hyo α β' hv]
        have h1 := hyo 0 β₀ hv0
        rw [dZ_plus β₀ hβ₀] at h1
        rw [h1]; push_cast; ring)
      have h1 := hyo 0 β₀ hv0
      rw [dZ_plus β₀ hβ₀, hM] at h1
      push_cast at h1
      have : (Dn : ℚ) ≠ 0 := by exact_mod_cast hDn.ne'
      have : (Dn : ℚ) * ν = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (by assumption)
    obtain ⟨e', g, heg⟩ := S.kqm_log_gen (K := K) hcop z hz0
      (fun kk ↦ S.zD c m cl kk (W kk) (N kk) (M kk)) (fun kk ↦ (hZd kk).1)
      N hN (fun kk ↦ 2 * lam kk j) δ
      (fun α β' hv ↦ by rw [hzo' α β' hv, hν0]; simp)
      hZdo
    have hwL : (w j) ≠ 0 := (hw j hj).2
    have hzL : logDeriv ((z : C⟮S.x⟯⟮S.y⟯) : L) = 2 * logDeriv (w j) -
        ((rr + ss : ℤ) : L) * algebraMap C L η := by
      simp only [z]
      rw [IntermediateField.coe_mul, IntermediateField.coe_pow,
        show ((S.xE ^ (-(rr + ss)) : C⟮S.x⟯⟮S.y⟯) : L) = ((S.xE : C⟮S.x⟯⟮S.y⟯) : L) ^ (-(rr + ss)) from
          map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val _ _,
        logDeriv_mul _ _ (pow_ne_zero _ hwL) (zpow_ne_zero _ hxL), logDeriv_pow, logDeriv_zpow' _ hxL,
        S.logDeriv_xE η hx]
      push_cast; ring
    refine ⟨e', (algebraMap C L g + ((rr + ss : ℤ) : L) * algebraMap C L η +
        ∑ kk, (e' kk : L) * GZ kk) / 2, ?_, ?_⟩
    · exact div_mem (add_mem (add_mem (IntermediateField.algebraMap_mem _ _)
        (mul_mem (intCast_mem _ _) (IntermediateField.algebraMap_mem _ _)))
        (sum_mem fun kk _ ↦ mul_mem (SubfieldClass.ratCast_mem _ _) (hGZ kk))) (ofNat_mem _ 2)
    · simp only [hGZe] at heg
      have h2 : logDeriv (w j) = (logDeriv ((z : C⟮S.x⟯⟮S.y⟯) : L) +
          ((rr + ss : ℤ) : L) * algebraMap C L η) / 2 := by rw [hzL]; ring
      rw [h2, heg]
      simp only [mul_add, Finset.sum_add_distrib]
      field_simp
      simp only [mul_add, Finset.mul_sum, ← mul_assoc]
      ring
  obtain ⟨a, ha, e, he, hae⟩ := S.kxm_tail (Polynomial.C η * X) hx hn2 W W0 W1 hW0 hW1 hWe hNm
    b hb v hv k d w heq' hdc hlog
  exact ⟨a, ha, e, he, hae⟩

end ExpDep

end SuperData

end Differential
