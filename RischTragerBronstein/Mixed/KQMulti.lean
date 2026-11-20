import RischTragerBronstein.Mixed.KQLiouville
import RischTragerBronstein.Algebraic.SqrtIndep

/-!
# `b(x) y` over a logarithm with poles whose residues lie in several classes

The generalization of `KQLiouville` to residues `m_q ρ_{κ(q)}` where the class values `ρ_k` are
`ℚ`-linearly independent constants (for square roots of rationals: `SqrtIndep`).

* `kqm_log_gen`: if `ord z = ∑ L_k δ_k` and `ord Z_k = N_k δ_k` (`N_k > 0`), then
  `z′/z = ∑ e_k Z_k′/Z_k + (a logarithmic derivative in C)`;
* `kqm_core`: the logarithms of a Liouville form have divisor `∑_k λ^k_j Δ_k`,
  `Δ_k = ∑_{κ(q) = k} m_q ((c_q, β_q) − (c_q, −β_q))`, with `∑_j λ^k_j d_j = ρ_k`;
* `kqm_liouville_nontors`: if some class with a non-zero residue is not torsion, no Liouville form;
* `kqm_liouville_tors`: with witnesses `W_k = W₀ₖ + W₁ₖ y` of `N_k Γ_k`, `b y = (a y)′ + ∑ e_k B_k y`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Classical

set_option linter.unusedSectionVars false

/-- **A functional separating `ℚ`-independent elements.** -/
lemma exists_sep_functional {C : Type*} [Field C] [CharZero C] {n : ℕ} (ρ : Fin n → C)
    (hρ : ∀ e : Fin n → ℚ, ∑ k, (e k : C) * ρ k = 0 → ∀ k, e k = 0) :
    ∃ φ : C →ₗ[ℚ] (Fin n → ℚ), ∀ k, φ (ρ k) = Pi.single k 1 := by
  classical
  set f := Fintype.linearCombination ℚ ρ with hf
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro e he
    rw [hf, Fintype.linearCombination_apply] at he
    funext k
    refine hρ e ?_ k
    rw [← he]
    exact Finset.sum_congr rfl fun k _ ↦ (Rat.smul_def _ _).symm
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  refine ⟨g, fun k ↦ ?_⟩
  have := congrArg (fun φ ↦ φ (Pi.single k 1)) hg
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  rw [← this, hf, Fintype.linearCombination_apply_single, one_smul]

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

/-- An integer multiple `A` of a rational `L` by a common denominator `D`. -/
lemma exists_int_mul {n : ℕ} (L' : Fin n → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ A : Fin n → ℤ, ∀ k, (A k : ℚ) = D * L' k := by
  refine ⟨∏ k, (L' k).den, Finset.prod_pos fun k _ ↦ (L' k).den_pos, fun k ↦
    (((∏ k, (L' k).den) / (L' k).den : ℕ) : ℤ) * (L' k).num, fun k ↦ ?_⟩
  have hdvd : (L' k).den ∣ ∏ k, (L' k).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
  obtain ⟨t, ht⟩ := hdvd
  have hden : (L' k).den ≠ 0 := (L' k).den_pos.ne'
  dsimp only
  rw [ht, Nat.mul_div_cancel_left _ (L' k).den_pos]
  push_cast
  rw [mul_comm ((L' k).den : ℚ), mul_assoc, mul_comm ((L' k).den : ℚ), Rat.mul_den_eq_num]

section LogGen

variable (hcop : Nat.Coprime S.n S.p.natDegree)
include hcop

/-- **Logarithmic derivatives with proportional divisors.** -/
theorem kqm_log_gen {n : ℕ} (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0) (Z : Fin n → C⟮S.x⟯⟮S.y⟯)
    (hZ : ∀ k, Z k ≠ 0) (N : Fin n → ℕ) (hN : ∀ k, 0 < N k) (L' : Fin n → ℚ)
    (δ : Fin n → K × K → ℚ)
    (hzo : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K z α β' : ℚ) = ∑ k, L' k * δ k (α, β'))
    (hZo : ∀ k, ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K (Z k) α β' : ℚ) = N k * δ k (α, β')) :
    ∃ (e : Fin n → ℚ) (g : C), logDeriv (z : L) =
      ∑ k, (e k : L) * logDeriv (Z k : L) + algebraMap C L g := by
  obtain ⟨D, hD0, A, hA⟩ := exists_int_mul L'
  set NN : ℕ := ∏ k, N k with hNN
  have hNN0 : 0 < NN := Finset.prod_pos fun k _ ↦ hN k
  have hdiv : ∀ k, N k ∣ NN := fun k ↦ Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
  set E : Fin n → ℤ := fun k ↦ -(A k * ((NN / N k : ℕ) : ℤ)) with hE
  set y1 := z ^ (D * NN) * ∏ k, Z k ^ E k with hy1
  have hzp : z ^ (D * NN) ≠ 0 := pow_ne_zero _ hz
  have hpr : ∏ k, Z k ^ E k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hZ k)
  have hy10 : y1 ≠ 0 := mul_ne_zero hzp hpr
  have h0 : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α → S.ordAt K y1 α β' = 0 := by
    intro α β' hv
    rw [S.ordAt_mul hv hzp hpr, S.ordAt_pow hv,
      S.ordAt_prod hv _ _ (fun k _ ↦ zpow_ne_zero _ (hZ k))]
    have : (((D * NN : ℕ) : ℤ) * S.ordAt K z α β' + ∑ k, S.ordAt K (Z k ^ E k) α β' : ℤ) =
        ((0 : ℤ) : ℚ) := by
      push_cast
      rw [hzo α β' hv]
      simp only [S.ordAt_zpow hv, Int.cast_mul, hZo _ α β' hv, hE]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      have hk : ((NN / N k : ℕ) : ℚ) * N k = NN := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel (hdiv k)]
      simp only [Int.cast_neg, Int.cast_mul, Int.cast_natCast]
      rw [hA k]
      linear_combination (-(D : ℚ) * L' k * δ k (α, β')) * hk
    exact_mod_cast this
  obtain ⟨γ, hγ⟩ := S.const_of_ordAt_zero K hcop y1 hy10 h0
  have hγ0 : γ ≠ 0 := fun h ↦ hy10 (Subtype.ext (by rw [hγ, h, map_zero]; rfl))
  have hzL : (z : L) ≠ 0 := fun h ↦ hz (Subtype.ext h)
  have hZL : ∀ k, (Z k : L) ≠ 0 := fun k h ↦ hZ k (Subtype.ext h)
  have e1 : ((y1 : C⟮S.x⟯⟮S.y⟯) : L) = (z : L) ^ (D * NN) * ∏ k, (Z k : L) ^ E k := by
    rw [hy1, IntermediateField.coe_mul, IntermediateField.coe_pow]
    congr 1
    rw [show ((∏ k, Z k ^ E k : C⟮S.x⟯⟮S.y⟯) : L) = ∏ k, ((Z k ^ E k : C⟮S.x⟯⟮S.y⟯) : L) from
      map_prod (C⟮S.x⟯⟮S.y⟯).val _ _]
    exact Finset.prod_congr rfl fun k _ ↦ map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val (Z k) _
  have hl := congrArg logDeriv (e1.symm.trans hγ)
  have hprL : ∏ k, (Z k : L) ^ E k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hZL k)
  rw [logDeriv_mul (a := (z : L) ^ (D * NN)) (b := ∏ k, (Z k : L) ^ E k) (pow_ne_zero _ hzL) hprL,
    logDeriv_pow, logDeriv_prod _ _ _ (fun k _ ↦ zpow_ne_zero _ (hZL k)), logDeriv_algebraMap] at hl
  simp only [fun k ↦ logDeriv_zpow' (Z k : L) (hZL k) (E k)] at hl
  have hDN : ((D * NN : ℕ) : L) ≠ 0 := by exact_mod_cast (Nat.mul_pos hD0 hNN0).ne'
  refine ⟨fun k ↦ -(E k : ℚ) / (D * NN : ℕ), logDeriv γ / (D * NN : ℕ), ?_⟩
  show logDeriv (z : L) = ∑ k, ((-(E k : ℚ) / (D * NN : ℕ) : ℚ) : L) * logDeriv (Z k : L) +
    algebraMap C L (logDeriv γ / (D * NN : ℕ))
  rw [map_div₀, map_natCast]
  have hsum : ∑ k, ((-(E k : ℚ) / (D * NN : ℕ) : ℚ) : L) * logDeriv (Z k : L) =
      -(∑ k, ((E k : ℤ) : L) * logDeriv (Z k : L)) / ((D * NN : ℕ) : L) := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    push_cast
    ring
  rw [hsum]
  field_simp
  linear_combination hl

end LogGen

section Classes

variable {r nk : ℕ} (c β : Fin r → C) (hc : Function.Injective c)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (hn2 : S.n = 2)
  (cl : Fin r → Fin nk)

/-- The multiplicities of the class `k`. -/
def mK (k : Fin nk) : Fin r → ℕ := fun q ↦ if cl q = k then m q else 0

/-- The divisor `Δ_k = ∑_{κ(q) = k} m_q ((c_q, β_q) − (c_q, −β_q))`, as a function. -/
noncomputable def dK (k : Fin nk) (Q : K × K) : ℚ :=
  ∑ q, (mK m cl k q : ℚ) * (if Q = (algebraMap C K (c q), algebraMap C K (β q)) then 1 else
    if Q = (algebraMap C K (c q), -algebraMap C K (β q)) then -1 else 0)

include hc hβ in
lemma dK_plus (k : Fin nk) (q : Fin r) :
    dK (K := K) c β m cl k (algebraMap C K (c q), algebraMap C K (β q)) = mK m cl k q := by
  rw [dK, Finset.sum_eq_single q]
  · simp
  · intro q' _ hq'
    have : algebraMap C K (c q) ≠ algebraMap C K (c q') := fun h ↦
      hq' (hc ((algebraMap C K).injective h)).symm
    simp [Prod.ext_iff, this]
  · simp

include hc hβ in
lemma dK_minus (k : Fin nk) (q : Fin r) :
    dK (K := K) c β m cl k (algebraMap C K (c q), -algebraMap C K (β q)) = -(mK m cl k q : ℚ) := by
  rw [dK, Finset.sum_eq_single q]
  · rw [if_neg (by simp [Prod.ext_iff, S.neg_ne_q c β hβ q]), if_pos rfl]; ring
  · intro q' _ hq'
    have : algebraMap C K (c q) ≠ algebraMap C K (c q') := fun h ↦
      hq' (hc ((algebraMap C K).injective h)).symm
    simp [Prod.ext_iff, this]
  · simp

lemma dK_off (k : Fin nk) (α b : K) (hα : ∀ q, α ≠ algebraMap C K (c q)) :
    dK (K := K) c β m cl k (α, b) = 0 :=
  Finset.sum_eq_zero fun q _ ↦ by simp [Prod.ext_iff, hα q]

/-- `Z_k = W_k² ∏ (x − c_q)^{−N_k m_q}` has divisor `N_k Δ_k`. -/
noncomputable def zK (k : Fin nk) (W : C⟮S.x⟯⟮S.y⟯) (N : ℕ) : C⟮S.x⟯⟮S.y⟯ :=
  W ^ 2 * ∏ q, S.polyX (X - Polynomial.C (c q)) ^ (-((N * mK m cl k q : ℕ) : ℤ))

include hc hβ hn2 in
lemma ordAt_zK (k : Fin nk) (W : C⟮S.x⟯⟮S.y⟯) (hW : W ≠ 0) (N : ℕ)
    (hWord : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K W α β' = N * gammaQ c β (mK m cl k) (α, β')) :
    S.zK c m cl k W N ≠ 0 ∧ ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K (S.zK c m cl k W N) α β' : ℚ) = N * dK c β m cl k (α, β') := by
  have hX : ∀ q, S.polyX (X - Polynomial.C (c q)) ≠ 0 := fun q ↦ S.polyX_ne_zero (X_sub_C_ne_zero _)
  have hpr : ∏ q, S.polyX (X - Polynomial.C (c q)) ^ (-((N * mK m cl k q : ℕ) : ℤ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q _ ↦ zpow_ne_zero _ (hX q)
  refine ⟨mul_ne_zero (pow_ne_zero _ hW) hpr, fun α β' hv ↦ ?_⟩
  rw [zK, S.ordAt_mul hv (pow_ne_zero _ hW) hpr, S.ordAt_pow hv, hWord α β' hv,
    S.ordAt_prod hv _ _ (fun q _ ↦ zpow_ne_zero _ (hX q))]
  simp only [S.ordAt_zpow hv, S.ordAt_polyX_lin _ _ _ hv]
  by_cases hα : ∃ q, α = algebraMap C K (c q)
  · obtain ⟨q, rfl⟩ := hα
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
    rw [hsum, gammaQ_at c β hc (mK m cl k) q β']
    rcases S.over_cq c β hβ hn2 q β' hv with rfl | rfl
    · rw [if_pos rfl, dK_plus S c β hc hβ m cl k q]; push_cast; ring
    · rw [if_neg (S.neg_ne_q c β hβ q), dK_minus S c β hc hβ m cl k q]; push_cast; ring
  · push Not at hα
    rw [gammaQ_off c β (mK m cl k) α β' hα, dK_off c β m cl k α β' hα]
    rw [Finset.sum_eq_zero fun q _ ↦ by rw [if_neg (hα q)]; ring]
    simp

end Classes

section MultiLog

variable (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (hgood : ∀ α : K, α′ ≠ algebraMap C K η)
  (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
  {r nk : ℕ} (c β : Fin r → C) (hc : Function.Injective c)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (cl : Fin r → Fin nk)
  (ρ : Fin nk → C)
  (P : C[X]) (l : ℕ) (b : L) (hb : b ∈ C⟮S.x⟯)
  (D : C[X]) (R : Fin r → C[X]) (hDR : ∀ q, D = (X - Polynomial.C (c q)) * R q)
  (hRne : ∀ q, (R q).eval (c q) ≠ 0)
  (hDoff : ∀ α : K, (∀ q, α ≠ algebraMap C K (c q)) → (D.map (algebraMap C K)).eval α ≠ 0)
  (hbP : b * aeval S.x (D * S.p ^ l) = aeval S.x P)
  (hres : ∀ q, P.eval (c q) * β q = m q * ρ (cl q) * (η - (c q)′) * (R q * S.p ^ l).eval (c q))

include hx hK hgood hconstC hc hβ hb hDR hRne hDoff hbP hres in
/-- **The logarithms are rational combinations of the class divisors `Δ_k`.** -/
theorem kqm_core (hn2 : S.n = 2) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ (k : ℕ) (d : ℕ → C) (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0),
      b * S.y = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) ∧
      (∀ j < k, (algebraMap C L (d j))′ = 0) ∧
      (∀ t : ℕ → ℚ, ∑ j ∈ Finset.range k, (t j : C) * d j = 0 → ∀ j < k, t j = 0) ∧
      ∃ lam : Fin nk → ℕ → ℚ,
        (∀ j (hj : j < k), ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
          (S.ordAt K ⟨w j, (hw j hj).1⟩ α β' : ℚ) = ∑ kk, lam kk j * dK c β m cl kk (α, β')) ∧
        ∀ kk, (∃ q, cl q = kk ∧ m q ≠ 0) →
          ∑ j ∈ Finset.range k, (lam kk j : C) * d j = ρ kk := by
  classical
  have hpc : ∀ q, S.p.eval (c q) ≠ 0 := fun q h0 ↦ by
    have := (hβ q).2
    rw [h0] at this
    exact (hβ q).1 (pow_eq_zero_iff S.hn.ne' |>.mp this)
  obtain ⟨k, d, w, hw, hind, heq', hdc, hzero, hraw⟩ :=
    S.kq_prep0 η hx hK hgood hconstC c P l b hb D R hDR hRne hDoff hbP hpc (by omega) hbm s cs u
      hcs hu v hv heq
  refine ⟨k, d, w, hw, heq', hdc, hind, ?_⟩
  have hindK : ∀ t : ℕ → ℚ, ∑ j ∈ Finset.range k, algebraMap C K (d j) * (t j : K) = 0 →
      ∀ j < k, t j = 0 := by
    intro t ht
    apply hind t
    apply (algebraMap C K).injective
    rw [map_zero, ← ht, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_ratCast, mul_comm]
  have hvP : ∀ q, (algebraMap C K (β q)) ^ S.n =
      (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) := fun q ↦ by
    rw [eval_map, eval₂_at_apply, ← (hβ q).2, map_pow]
  have hvM : ∀ q, (-algebraMap C K (β q)) ^ S.n =
      (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) := fun q ↦ by
    rw [hn2, neg_sq, ← hn2]; exact hvP q
  set oP : Fin r → ℕ → ℤ := fun q j ↦ if h : j < k then
    S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) (algebraMap C K (β q)) else 0 with hoP
  set oM : Fin r → ℕ → ℤ := fun q j ↦ if h : j < k then
    S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) (-algebraMap C K (β q)) else 0 with hoM
  have hE : ∀ q, algebraMap C K ((η - (c q)′) * (R q * S.p ^ l).eval (c q)) ≠ 0 := fun q ↦ by
    refine (_root_.map_ne_zero _).mpr (mul_ne_zero (fun h0 ↦ ?_) ?_)
    · apply hgood (algebraMap C K (c q))
      rw [hK, sub_eq_zero.mp h0]
    · rw [eval_mul, eval_pow]
      exact mul_ne_zero (hRne q) (pow_ne_zero _ (hpc q))
  have hsP : ∀ q, ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oP q j : ℚ) : K) =
      algebraMap C K (m q * ρ (cl q)) := fun q ↦ by
    have h := hraw q _ (hvP q)
    refine mul_right_cancel₀ (hE q) ?_
    have e1 : ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oP q j : ℚ) : K) =
        ∑ j ∈ Finset.range k, algebraMap C K (d j) * (if h : j < k then
          (S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) (algebraMap C K (β q)) : K) else 0) :=
      Finset.sum_congr rfl fun j _ ↦ by simp only [hoP]; split_ifs <;> simp
    rw [e1, h, ← map_mul, ← map_mul, hres q]
    ring_nf
  have hsM : ∀ q, ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oM q j : ℚ) : K) =
      -algebraMap C K (m q * ρ (cl q)) := fun q ↦ by
    have h := hraw q _ (hvM q)
    refine mul_right_cancel₀ (hE q) ?_
    have e1 : ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oM q j : ℚ) : K) =
        ∑ j ∈ Finset.range k, algebraMap C K (d j) * (if h : j < k then
          (S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) (-algebraMap C K (β q)) : K) else 0) :=
      Finset.sum_congr rfl fun j _ ↦ by simp only [hoM]; split_ifs <;> simp
    rw [e1, h, mul_neg, neg_mul, ← map_mul, ← map_mul, hres q]
    ring_nf
  -- the coefficients of the classes
  set lam : Fin nk → ℕ → ℚ := fun kk j ↦ if h : ∃ q, cl q = kk ∧ m q ≠ 0 then
    (oP h.choose j : ℚ) / m h.choose else 0 with hlam
  have hsl : ∀ kk (h : ∃ q, cl q = kk ∧ m q ≠ 0),
      ∑ j ∈ Finset.range k, algebraMap C K (d j) * (lam kk j : K) = algebraMap C K (ρ kk) := by
    intro kk h
    have hq0 := h.choose_spec
    have hq0K : ((m h.choose : ℚ) : K) ≠ 0 := by exact_mod_cast hq0.2
    have hs := hsP h.choose
    rw [hq0.1, map_mul, map_natCast] at hs
    have : ∑ j ∈ Finset.range k, algebraMap C K (d j) * (lam kk j : K) =
        (∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oP h.choose j : ℚ) : K)) / (m h.choose : K) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [hlam, dif_pos h, Rat.cast_div, Rat.cast_natCast]
      ring
    have hq0K' : (m h.choose : K) ≠ 0 := by exact_mod_cast hq0.2
    rw [this, hs, mul_div_cancel_left₀ _ hq0K']
  have hcoef : ∀ q, ∀ j < k, (oP q j : ℚ) = m q * lam (cl q) j ∧
      (oM q j : ℚ) = -(m q * lam (cl q) j) := by
    intro q j hj
    by_cases hmq : m q = 0
    · have hP := hindK (fun j ↦ (oP q j : ℚ)) (by rw [hsP q, hmq]; simp) j hj
      have hM := hindK (fun j ↦ (oM q j : ℚ)) (by rw [hsM q, hmq]; simp) j hj
      rw [hP, hM, hmq]; simp
    · have hex : ∃ q', cl q' = cl q ∧ m q' ≠ 0 := ⟨q, rfl, hmq⟩
      have hs := hsl (cl q) hex
      have hmul : ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((m q : K) * (lam (cl q) j : K)) =
          (m q : K) * ∑ j ∈ Finset.range k, algebraMap C K (d j) * (lam (cl q) j : K) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
      have hP := hindK (fun j ↦ (oP q j : ℚ) - m q * lam (cl q) j) (by
        simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, mul_sub, Finset.sum_sub_distrib]
        rw [hsP q, hmul, hs, map_mul, map_natCast, sub_self]) j hj
      have hM := hindK (fun j ↦ (oM q j : ℚ) + m q * lam (cl q) j) (by
        simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, mul_add, Finset.sum_add_distrib]
        rw [hsM q, hmul, hs, map_mul, map_natCast, neg_add_cancel]) j hj
      constructor <;> linarith
  refine ⟨lam, fun j hj α β' hv ↦ ?_, fun kk h ↦ ?_⟩
  · by_cases hα : ∃ q, α = algebraMap C K (c q)
    · obtain ⟨q, rfl⟩ := hα
      have hsum : ∀ sgn : ℚ, ∑ kk, lam kk j * (sgn * (mK m cl kk q : ℚ)) = sgn * (m q * lam (cl q) j) := by
        intro sgn
        rw [Finset.sum_eq_single (cl q)]
        · simp [mK]; ring
        · intro kk _ hkk; simp [mK, Ne.symm hkk]
        · simp
      rcases S.over_cq c β hβ hn2 q β' hv with rfl | rfl
      · have e := (hcoef q j hj).1
        simp only [hoP, dif_pos hj] at e
        rw [e]
        simp only [dK_plus S c β hc hβ m cl _ q]
        have := hsum 1
        simp only [one_mul] at this
        rw [this]
      · have e := (hcoef q j hj).2
        simp only [hoM, dif_pos hj] at e
        rw [e]
        simp only [dK_minus S c β hc hβ m cl _ q]
        have := hsum (-1)
        simp only [neg_one_mul] at this
        rw [← this]
    · push Not at hα
      rw [hzero j hj α β' hv hα]
      simp [dK_off c β m cl _ α β' hα]
  · have := hsl kk h
    apply (algebraMap C K).injective
    rw [← this, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_ratCast, mul_comm]

include hx hK hgood hconstC hc hβ hb hDR hRne hDoff hbP hres in
/-- **Without torsion of a class carrying a non-zero residue, there is no Liouville form.** -/
theorem kqm_liouville_nontors (hn2 : S.n = 2) (k0 : Fin nk) (hk0 : ∃ q, cl q = k0 ∧ m q ≠ 0)
    (hρ : ∀ e : Fin nk → ℚ, ∑ kk, (e kk : C) * ρ kk = 0 → ∀ kk, e kk = 0)
    (hnt : ∀ N : ℕ, 0 < N → ¬ S.IsPrincipalS K (gammaQ c β (mK m cl k0)) N)
    (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) : False := by
  classical
  obtain ⟨k, d, w, hw, -, -, -, lam, hord, hsum⟩ :=
    S.kqm_core (K := K) η hx hK hgood hconstC c β hc hβ m cl ρ P l b hb D R hDR hRne hDoff hbP
      hres hn2 hbm s cs u hcs hu v hv heq
  obtain ⟨φ, hφ⟩ := _root_.exists_sep_functional (ρ := ρ) hρ
  set μ : Fin k → ℚ := fun j ↦ φ (d j) k0 with hμ
  obtain ⟨Dn, hD0, A, hA⟩ := exists_int_mul μ
  set wj : Fin k → C⟮S.x⟯⟮S.y⟯ := fun j ↦ ⟨w j, (hw j j.2).1⟩ with hwj
  have hwj0 : ∀ j, wj j ≠ 0 := fun j h ↦ (hw j j.2).2 (congrArg Subtype.val h)
  set z := ∏ j, wj j ^ A j with hz
  have hz0 : z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (hwj0 j)
  -- the class coefficients of `z`
  have hcoef : ∀ kk, (∃ q, cl q = kk ∧ m q ≠ 0) →
      ∑ j : Fin k, (A j : ℚ) * lam kk j = if kk = k0 then (Dn : ℚ) else 0 := by
    intro kk hkk
    have hs := hsum kk hkk
    have hφs := congrArg (fun x ↦ φ x k0) hs
    simp only [map_sum, hφ kk] at hφs
    have e1 : ∑ j ∈ Finset.range k, (φ ((lam kk j : C) * d j)) k0 =
        ∑ j : Fin k, lam kk j * μ j := by
      rw [← Fin.sum_univ_eq_sum_range (fun j ↦ (φ ((lam kk j : C) * d j)) k0)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Rat.smul_def, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_apply] at hφs
    rw [e1] at hφs
    simp only [hA, Pi.single_apply] at hφs ⊢
    have : ∑ j : Fin k, (Dn : ℚ) * μ j * lam kk j = Dn * ∑ j : Fin k, lam kk j * μ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [this, hφs]
    split_ifs with h1 h2 h2
    · ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring
  have hordz : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K z α β' : ℚ) = Dn * dK c β m cl k0 (α, β') := by
    intro α β' hv
    rw [hz, S.ordAt_prod hv _ _ (fun j _ ↦ zpow_ne_zero _ (hwj0 j))]
    push_cast
    simp only [S.ordAt_zpow hv, Int.cast_mul]
    have e2 : ∀ j : Fin k, (S.ordAt K (wj j) α β' : ℚ) = ∑ kk, lam kk j * dK c β m cl kk (α, β') :=
      fun j ↦ hord j j.2 α β' hv
    simp only [e2, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single k0]
    · by_cases hk0' : ∃ q, cl q = k0 ∧ m q ≠ 0
      · have := hcoef k0 hk0'
        rw [if_pos rfl] at this
        rw [← this, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      · exact absurd hk0 hk0'
    · intro kk _ hkk
      by_cases hkk' : ∃ q, cl q = kk ∧ m q ≠ 0
      · have := hcoef kk hkk'
        rw [if_neg hkk] at this
        rw [show ∑ j : Fin k, (A j : ℚ) * (lam kk j * dK c β m cl kk (α, β')) =
          (∑ j : Fin k, (A j : ℚ) * lam kk j) * dK c β m cl kk (α, β') by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ ↦ by ring, this, zero_mul]
      · push Not at hkk'
        have hd0 : dK (K := K) c β m cl kk (α, β') = 0 := Finset.sum_eq_zero fun q _ ↦ by
          by_cases hq : cl q = kk
          · simp [mK, hq, hkk' q hq]
          · simp [mK, hq]
        simp [hd0]
    · simp
  have hform : S.OrdForm (K := K) c β (mK m cl k0) z Dn := by
    refine ⟨fun α β' hv hα ↦ ?_, fun q ↦ ⟨?_, ?_⟩⟩
    · have := hordz α β' hv
      rw [dK_off c β m cl k0 α β' hα, mul_zero] at this
      exact_mod_cast this
    · rw [hordz _ _ (by rw [eval_map, eval₂_at_apply, ← (hβ q).2, map_pow]),
        dK_plus S c β hc hβ m cl k0 q]; ring
    · rw [hordz _ _ (by rw [hn2, neg_sq, ← hn2, eval_map, eval₂_at_apply, ← (hβ q).2, map_pow]),
        dK_minus S c β hc hβ m cl k0 q]; ring
  obtain ⟨N, hN, hP⟩ := S.kq_log_nontors c β hc hβ (mK m cl k0) hn2 z hz0 Dn
    (by exact_mod_cast hD0.ne') hform
  exact hnt N hN hP

include hx hK hgood hconstC hc hβ hb hDR hRne hDoff hbP hres in
/-- **With a witness of `N_k Γ_k` for every class, a Liouville form for `b y` forces
`b y = (a y)′ + ∑_k e_k B_k y`**, `W_k′/W_k = E_k + B_k y`. -/
theorem kqm_liouville_tors (hn2 : S.n = 2) (hcop : Nat.Coprime S.n S.p.natDegree)
    (N : Fin nk → ℕ) (hN : ∀ kk, 0 < N kk) (W : Fin nk → C⟮S.x⟯⟮S.y⟯) (hW : ∀ kk, W kk ≠ 0)
    (hWord : ∀ kk, ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K (W kk) α β' = N kk * gammaQ c β (mK m cl kk) (α, β'))
    (W0 W1 : Fin nk → L) (hW0 : ∀ kk, W0 kk ∈ C⟮S.x⟯) (hW1 : ∀ kk, W1 kk ∈ C⟮S.x⟯)
    (hWe : ∀ kk, (W kk : L) = W0 kk + W1 kk * S.y)
    (hNm : ∀ kk, W0 kk ^ 2 - W1 kk ^ 2 * aeval S.x S.p ≠ 0) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ a ∈ C⟮S.x⟯, ∃ e : Fin nk → C, (∀ kk, (algebraMap C L (e kk))′ = 0) ∧
      b * S.y = (a * S.y)′ + ∑ kk, algebraMap C L (e kk) *
        ((W0 kk * ((W1 kk)′ + W1 kk * (aeval S.x (mapCoeffs S.p + Polynomial.C η * derivative S.p) /
          ((S.n : L) * aeval S.x S.p))) - (W0 kk)′ * W1 kk) /
          (W0 kk ^ 2 - W1 kk ^ 2 * aeval S.x S.p) * S.y) := by
  classical
  obtain ⟨k, d, w, hw, heq', hdc, -, lam, hord, -⟩ :=
    S.kqm_core (K := K) η hx hK hgood hconstC c β hc hβ m cl ρ P l b hb D R hDR hRne hDoff hbP
      hres hn2 hbm s cs u hcs hu v hv heq
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedXW (Polynomial.C η) hx
  have hmemx : ∀ Q : C[X], aeval S.x Q ∈ C⟮S.x⟯ := fun Q ↦ by
    letI := algebraAdjoinSimple (F := C) S.x
    rw [← algebraMap_adjoinSimple (F := C) S.x Q]; exact SetLike.coe_mem _
  -- the logarithmic derivative of `Z_k`
  have hZ : ∀ kk, ∃ G ∈ C⟮S.x⟯,
      logDeriv ((S.zK c m cl kk (W kk) (N kk) : C⟮S.x⟯⟮S.y⟯) : L) = 2 * logDeriv (W kk : L) + G := by
    intro kk
    have hWL : (W kk : L) ≠ 0 := fun h ↦ hW kk (Subtype.ext h)
    have hXL : ∀ q, ((S.polyX (X - Polynomial.C (c q)) : C⟮S.x⟯⟮S.y⟯) : L) ≠ 0 := fun q h ↦
      S.polyX_ne_zero (X_sub_C_ne_zero (c q)) (Subtype.ext h)
    have e1 : ((S.zK c m cl kk (W kk) (N kk) : C⟮S.x⟯⟮S.y⟯) : L) = (W kk : L) ^ 2 *
        ∏ q, ((S.polyX (X - Polynomial.C (c q)) : C⟮S.x⟯⟮S.y⟯) : L) ^ (-((N kk * mK m cl kk q : ℕ) : ℤ)) := by
      rw [zK, IntermediateField.coe_mul, IntermediateField.coe_pow]
      congr 1
      rw [show ((∏ q, S.polyX (X - Polynomial.C (c q)) ^ (-((N kk * mK m cl kk q : ℕ) : ℤ)) :
          C⟮S.x⟯⟮S.y⟯) : L) = ∏ q, ((S.polyX (X - Polynomial.C (c q)) ^
            (-((N kk * mK m cl kk q : ℕ) : ℤ)) : C⟮S.x⟯⟮S.y⟯) : L) from map_prod (C⟮S.x⟯⟮S.y⟯).val _ _]
      exact Finset.prod_congr rfl fun q _ ↦ map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val _ _
    refine ⟨∑ q, ((-((N kk * mK m cl kk q : ℕ) : ℤ) : ℤ) : L) *
      logDeriv ((S.polyX (X - Polynomial.C (c q)) : C⟮S.x⟯⟮S.y⟯) : L), sum_mem fun q _ ↦ ?_, ?_⟩
    · refine mul_mem (intCast_mem _ _) ?_
      rw [S.polyX_coe]
      exact div_mem (hcl _ (hmemx _)) (hmemx _)
    · rw [e1, logDeriv_mul (a := (W kk : L) ^ 2) (b := ∏ q, ((S.polyX (X - Polynomial.C (c q)) :
          C⟮S.x⟯⟮S.y⟯) : L) ^ (-((N kk * mK m cl kk q : ℕ) : ℤ))) (pow_ne_zero _ hWL)
        (Finset.prod_ne_zero_iff.mpr fun q _ ↦ zpow_ne_zero _ (hXL q)), logDeriv_pow,
        logDeriv_prod _ _ _ (fun q _ ↦ zpow_ne_zero _ (hXL q))]
      simp only [fun q ↦ logDeriv_zpow' _ (hXL q)]
      push_cast
      ring
  choose GZ hGZ hGZe using hZ
  -- each logarithm
  have hlog : ∀ j < k, ∃ (e : Fin nk → ℚ) (G : L), G ∈ C⟮S.x⟯ ∧
      logDeriv (w j) = ∑ kk, (e kk : L) * logDeriv (W kk : L) + G := by
    intro j hj
    obtain ⟨e, g, heg⟩ := S.kqm_log_gen (K := K) hcop ⟨w j, (hw j hj).1⟩
      (fun h ↦ (hw j hj).2 (congrArg Subtype.val h))
      (fun kk ↦ S.zK c m cl kk (W kk) (N kk))
      (fun kk ↦ (S.ordAt_zK c β hc hβ m hn2 cl kk (W kk) (hW kk) (N kk) (hWord kk)).1) N hN
      (fun kk ↦ lam kk j) (fun kk ↦ dK c β m cl kk) (hord j hj)
      (fun kk ↦ (S.ordAt_zK c β hc hβ m hn2 cl kk (W kk) (hW kk) (N kk) (hWord kk)).2)
    refine ⟨fun kk ↦ 2 * e kk, ∑ kk, (e kk : L) * GZ kk + algebraMap C L g,
      add_mem (sum_mem fun kk _ ↦ mul_mem (SubfieldClass.ratCast_mem _ _) (hGZ kk))
        (IntermediateField.algebraMap_mem _ _), ?_⟩
    change logDeriv (w j) = _ at heg
    rw [heg]
    simp only [hGZe]
    push_cast
    rw [← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun kk _ ↦ by ring
  choose! e G hG hlogj using hlog
  set Es : Fin nk → C := fun kk ↦ ∑ j ∈ Finset.range k, d j * (e j kk : C)
  set Gs : L := ∑ j ∈ Finset.range k, algebraMap C L (d j) * G j
  have hGs : Gs ∈ C⟮S.x⟯ := sum_mem fun j hj ↦
    mul_mem (IntermediateField.algebraMap_mem _ _) (hG j (Finset.mem_range.mp hj))
  have hsum : ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) =
      Gs + ∑ kk, algebraMap C L (Es kk) * logDeriv (W kk : L) := by
    rw [Finset.sum_congr rfl fun j hj ↦ by rw [hlogj j (Finset.mem_range.mp hj)]]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [add_comm, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun kk _ ↦ ?_
    simp only [Es, map_sum, map_mul, map_ratCast, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hEs : ∀ kk, (algebraMap C L (Es kk))′ = 0 := by
    intro kk
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [map_mul, map_ratCast, Derivation.leibniz, hdc j (Finset.mem_range.mp hj),
      Tower.NestP.deriv_ratCastK (K := L) (e j kk)]
    simp
  rw [hsum] at heq'
  set P' := aeval S.x S.p with hP
  set r := aeval S.x (mapCoeffs S.p + Polynomial.C η * derivative S.p) / ((S.n : L) * P') with hr
  have hy2 : S.y ^ 2 = P' := by rw [← hn2]; exact S.hy
  have hyd : S.y′ = r * S.y := by rw [S.deriv_yW (Polynomial.C η) hx, hr]; ring
  have hrm : r ∈ C⟮S.x⟯ := S.r_memW (Polynomial.C η) hx
  have hPm : P' ∈ C⟮S.x⟯ := hmemx _
  set Bk : Fin nk → L := fun kk ↦
    (W0 kk * ((W1 kk)′ + W1 kk * r) - (W0 kk)′ * W1 kk) / (W0 kk ^ 2 - W1 kk ^ 2 * P')
  set Ek : Fin nk → L := fun kk ↦
    (W0 kk * (W0 kk)′ - W1 kk * ((W1 kk)′ + W1 kk * r) * P') / (W0 kk ^ 2 - W1 kk ^ 2 * P')
  have hab : ∀ kk, logDeriv (W kk : L) = Ek kk + Bk kk * S.y := fun kk ↦ by
    rw [hWe kk]; exact logDeriv_ab (y := S.y) (W0 kk) (W1 kk) P' r hy2 hyd (hNm kk)
  have hNm' : ∀ kk, W0 kk ^ 2 - W1 kk ^ 2 * P' ∈ C⟮S.x⟯ := fun kk ↦
    sub_mem (pow_mem (hW0 kk) 2) (mul_mem (pow_mem (hW1 kk) 2) hPm)
  have hBm : ∀ kk, Bk kk ∈ C⟮S.x⟯ := fun kk ↦ div_mem (sub_mem (mul_mem (hW0 kk)
    (add_mem (hcl _ (hW1 kk)) (mul_mem (hW1 kk) hrm))) (mul_mem (hcl _ (hW0 kk)) (hW1 kk))) (hNm' kk)
  have hEm : ∀ kk, Ek kk ∈ C⟮S.x⟯ := fun kk ↦ div_mem (sub_mem (mul_mem (hW0 kk) (hcl _ (hW0 kk)))
    (mul_mem (mul_mem (hW1 kk) (add_mem (hcl _ (hW1 kk)) (mul_mem (hW1 kk) hrm))) hPm)) (hNm' kk)
  simp only [hab] at heq'
  have heq2 : (b - ∑ kk, algebraMap C L (Es kk) * Bk kk) * S.y ^ 1 =
      v′ + (Gs + ∑ kk, algebraMap C L (Es kk) * Ek kk) := by
    rw [pow_one, sub_mul, Finset.sum_mul]
    rw [heq']
    simp only [mul_add, Finset.sum_add_distrib]
    have : ∑ kk, algebraMap C L (Es kk) * (Bk kk * S.y) = ∑ kk, algebraMap C L (Es kk) * Bk kk * S.y :=
      Finset.sum_congr rfl fun kk _ ↦ by ring
    rw [this]
    ring
  obtain ⟨a, ha, hae⟩ := S.exact_of_even (Polynomial.C η) hx 1 one_pos (by omega) _
    (sub_mem hb (sum_mem fun kk _ ↦ mul_mem (IntermediateField.algebraMap_mem _ _) (hBm kk))) v hv _
    (add_mem hGs (sum_mem fun kk _ ↦ mul_mem (IntermediateField.algebraMap_mem _ _) (hEm kk))) heq2
  refine ⟨a, ha, Es, hEs, ?_⟩
  simp only [pow_one] at hae
  rw [show ∑ kk, algebraMap C L (Es kk) * (Bk kk * S.y) = (∑ kk, algebraMap C L (Es kk) * Bk kk) * S.y by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun kk _ ↦ by ring]
  linear_combination hae

end MultiLog

end SuperData

end Differential
