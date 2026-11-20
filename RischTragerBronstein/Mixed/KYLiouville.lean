import RischTragerBronstein.Mixed.KYPrep
import RischTragerBronstein.Mixed.KYLin
import RischTragerBronstein.Mixed.KRLiouville

/-!
# `b(x) yʲ` over an exponential with simple poles at ordinary places: the projected form

* `ky_project`: the `yʲ`-projection of a normalized Liouville form;
* `over_k`: the points over `x = α` are `(α, ζᵏβ)`.
-/

open Polynomial IntermediateField Ramanujan

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

/-- **The points over `x = α`** are the `(α, ζᵏβ)`, `k < n`. -/
lemma over_k (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) (α β : K) (hβ : β ≠ 0)
    (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) (β' : K)
    (hv' : β' ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    ∃ k < S.n, β' = algebraMap C K ζ ^ k * β := by
  haveI : NeZero S.n := ⟨S.hn.ne'⟩
  have h1 : (β' / β) ^ S.n = 1 := by
    rw [div_pow, hv', ← hv, div_self (pow_ne_zero _ hβ)]
  obtain ⟨k, hk, hkeq⟩ := (S.algζ_prim (K := K) ζ hζ).eq_pow_of_pow_eq_one h1
  exact ⟨k, hk, by rw [hkeq, div_mul_cancel₀ _ hβ]⟩

variable (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η * X))
  (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) (j : Fin S.n)

include hx hζ in
/-- **The projected Liouville form**: `n b yʲ = (n a yʲ)′ + ∑ dᵢ four j (wᵢ′/wᵢ)`. -/
theorem ky_project (b : L) (hb : b ∈ C⟮S.x⟯) (hbm : b * S.y ^ (j : ℕ) ∈ C⟮S.x⟯⟮S.y⟯)
    (k : ℕ) (d : ℕ → C) (w : ℕ → L) (hw : ∀ i < k, w i ∈ C⟮S.x⟯⟮S.y⟯ ∧ w i ≠ 0)
    (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y ^ (j : ℕ) = v′ + ∑ i ∈ Finset.range k, algebraMap C L (d i) * logDeriv (w i)) :
    ∃ a : C⟮S.x⟯,
      (S.n : C⟮S.x⟯⟮S.y⟯) * (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨b, hb⟩ *
          AdjoinSimple.gen C⟮S.x⟯ S.y ^ (j : ℕ)) =
        S.dTW (Polynomial.C η * X) hx ((S.n : C⟮S.x⟯⟮S.y⟯) *
          (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (j : ℕ))) +
        ∑ i ∈ Finset.range k, S.cst (d i) * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx
          (if h : i < k then ⟨w i, (hw i h).1⟩ else 1)) := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  set W : ℕ → C⟮S.x⟯⟮S.y⟯ := fun i ↦ if h : i < k then ⟨w i, (hw i h).1⟩ else 1 with hW
  have hWi : ∀ i < k, (W i : L) = w i := fun i hi ↦ by simp [hW, dif_pos hi]
  obtain ⟨aV, haV⟩ := S.power_repr ⟨v, hv⟩
  refine ⟨aV j, ?_⟩
  have hF : (⟨b * S.y ^ (j : ℕ), hbm⟩ : C⟮S.x⟯⟮S.y⟯) =
      S.dTW (Polynomial.C η * X) hx ⟨v, hv⟩ + ∑ i ∈ Finset.range k, S.cst (d i) *
        S.dl (Polynomial.C η * X) hx (W i) := by
    apply Subtype.ext
    rw [IntermediateField.coe_add, coe_dTW,
      show ((∑ i ∈ Finset.range k, S.cst (d i) * S.dl (Polynomial.C η * X) hx (W i) :
        C⟮S.x⟯⟮S.y⟯) : L) = ∑ i ∈ Finset.range k, ((S.cst (d i) *
          S.dl (Polynomial.C η * X) hx (W i) : C⟮S.x⟯⟮S.y⟯) : L) from map_sum (C⟮S.x⟯⟮S.y⟯).val _ _]
    change b * S.y ^ (j : ℕ) = _
    rw [heq]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [IntermediateField.coe_mul, coe_dl, hWi i (Finset.mem_range.mp hi)]
    rfl
  have hFrepr : (⟨b * S.y ^ (j : ℕ), hbm⟩ : C⟮S.x⟯⟮S.y⟯) =
      ∑ i : Fin S.n, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (if i = j then ⟨b, hb⟩ else 0) *
        AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ) := by
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [if_neg hij, map_zero, zero_mul])
      (fun h ↦ absurd (Finset.mem_univ j) h), if_pos rfl]
    rfl
  have h4 := congrArg (S.four ζ hζ j) hF
  rw [S.four_add, S.four_dTW (Polynomial.C η * X) hx ζ hζ, S.four_sum] at h4
  simp_rw [S.four_cst_mul] at h4
  rw [hFrepr, S.four_repr, if_pos rfl, haV, S.four_repr] at h4
  exact h4

section Poles

variable (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (hgood : ∀ α : K, α ≠ 0 → α′ ≠ algebraMap C K η * α)
  (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
  {r : ℕ} (c : Fin r → C) (hc0 : ∀ q, c q ≠ 0)
  (P : C[X]) (l : ℕ) (b : L) (hb : b ∈ C⟮S.x⟯)
  (D : C[X]) (R : Fin r → C[X]) (hDR : ∀ q, D = (X - Polynomial.C (c q)) * R q)
  (hRne : ∀ q, (R q).eval (c q) ≠ 0)
  (hDoff : ∀ α : K, α ≠ 0 → (∀ q, α ≠ algebraMap C K (c q)) → (D.map (algebraMap C K)).eval α ≠ 0)
  (hbP : b * aeval S.x (D * S.p ^ l) = aeval S.x P)
  (βq : Fin r → C) (hβq : ∀ q, βq q ≠ 0 ∧ βq q ^ S.n = S.p.eval (c q))
  {E : Type*} [Fintype E] (ν : E → C) (rr : Fin r → ℕ → E → ℚ)
  (hres : ∀ q kk, P.eval (c q) * (ζ ^ kk * βq q) ^ (j : ℕ) =
    (∑ e, (rr q kk e : C) * ν e) * ((η * c q - (c q)′) * (R q * S.p ^ l).eval (c q)))

/-- The point `(c_q, ζᵏ β_q)`. -/
noncomputable def pq (q : Fin r) (kk : ℕ) : K × K :=
  (algebraMap C K (c q), algebraMap C K (ζ ^ kk * βq q))

include hβq hζ in
lemma pq_v (q : Fin r) (kk : ℕ) : (pq (K := K) ζ c βq q kk).2 ^ S.n =
    (S.p.map (algebraMap C K)).eval (pq (K := K) ζ c βq q kk).1 := by
  simp only [pq]
  rw [← map_pow, mul_pow, ← pow_mul, mul_comm kk, pow_mul, hζ.pow_eq_one, one_pow, one_mul,
    (hβq q).2, eval_map, eval₂_at_apply]

include hx hK hgood hconstC hb hDR hRne hDoff hbP hβq hres hc0 hζ in
/-- **The orders of the logarithms at the poles** are rational combinations of the components
`rr · e` of the residues. -/
theorem ky_orders (hj0 : 0 < (j : ℕ)) (hbm : b * S.y ^ (j : ℕ) ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y ^ (j : ℕ) = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ (k : ℕ) (d : ℕ → C) (w : ℕ → L) (hw : ∀ i < k, w i ∈ C⟮S.x⟯⟮S.y⟯ ∧ w i ≠ 0),
      (∀ t : ℕ → ℚ, ∑ i ∈ Finset.range k, (t i : C) * d i = 0 → ∀ i < k, t i = 0) ∧
      b * S.y ^ (j : ℕ) = v′ + ∑ i ∈ Finset.range k, algebraMap C L (d i) * logDeriv (w i) ∧
      (∀ i < k, (d i)′ = 0) ∧
      (∀ i (hi : i < k), ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
        α ≠ 0 → (∀ q, α ≠ algebraMap C K (c q)) → S.ordAt K ⟨w i, (hw i hi).1⟩ α β' = 0) ∧
      (∀ q kk, ∑ i ∈ Finset.range k, d i * (if h : i < k then
          (S.ordAt K ⟨w i, (hw i h).1⟩ (pq (K := K) ζ c βq q kk).1 (pq (K := K) ζ c βq q kk).2 : C)
          else 0) = ∑ e, (rr q kk e : C) * ν e) ∧
      ∀ i (hi : i < k), ∃ T : E → ℚ, ∀ q (kk : Fin S.n),
        (S.ordAt K ⟨w i, (hw i hi).1⟩ (pq (K := K) ζ c βq q kk).1 (pq (K := K) ζ c βq q kk).2 : ℚ) =
          ∑ e, T e * rr q kk e := by
  classical
  have hpc : ∀ q, S.p.eval (c q) ≠ 0 := fun q h0 ↦ by
    have := (hβq q).2
    rw [h0] at this
    exact (hβq q).1 (pow_eq_zero_iff S.hn.ne' |>.mp this)
  have hgood' : ∀ α : K, ¬ (α = 0) → α′ ≠ ((Polynomial.C η * X).map (algebraMap C K)).eval α :=
    fun α hα ↦ by
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_X]
      exact hgood α hα
  have hbadc : ∀ q, ¬ (algebraMap C K (c q) = 0) := fun q h ↦
    hc0 q ((algebraMap C K).injective (by rw [h, map_zero]))
  obtain ⟨k, d, w, hw, hind, heq', hdc, hzero, hraw⟩ :=
    S.ky_prep0 (K := K) _ hx hK (· = 0) hgood' hconstC c hbadc P l b hb D R hDR hRne hDoff hbP hpc
      j hj0 j.2 hbm s cs u hcs hu v hv heq
  -- the residues
  have hden : ∀ q, (η * c q - (c q)′) * (R q * S.p ^ l).eval (c q) ≠ 0 := fun q ↦ by
    refine mul_ne_zero (fun h0 ↦ ?_) ?_
    · apply hgood (algebraMap C K (c q)) (hbadc q)
      rw [hK, ← map_mul, show (c q)′ = η * c q by linear_combination -h0]
    · rw [eval_mul, eval_pow]; exact mul_ne_zero (hRne q) (pow_ne_zero _ (hpc q))
  have hresid : ∀ q kk, ∑ i ∈ Finset.range k, d i * (if h : i < k then
      (S.ordAt K ⟨w i, (hw i h).1⟩ (pq (K := K) ζ c βq q kk).1 (pq (K := K) ζ c βq q kk).2 : C)
      else 0) = ∑ e, (rr q kk e : C) * ν e := by
    intro q kk
    have h := hraw q _ (S.pq_v ζ hζ c βq hβq q kk)
    have hω : (Polynomial.C η * X).eval (c q) = η * c q := by simp
    rw [hω] at h
    apply mul_right_cancel₀ (hden q)
    rw [← hres q kk]
    apply (algebraMap C K).injective
    rw [map_mul, map_mul (algebraMap C K) (P.eval (c q)), map_pow]
    convert h using 1
    · rw [map_mul]
      congr 1
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      split_ifs <;> simp [pq]
    · rfl
  refine ⟨k, d, w, hw, hind, heq', hdc, hzero, hresid, fun i hi ↦ ?_⟩
  -- the rational matrix
  set o : ℕ → Fin r × Fin S.n → ℚ := fun i qk ↦ if h : i < k then
    (S.ordAt K ⟨w i, (hw i h).1⟩ (pq (K := K) ζ c βq qk.1 qk.2).1
      (pq (K := K) ζ c βq qk.1 qk.2).2 : ℚ) else 0 with ho
  obtain ⟨T, hT⟩ := exists_comb (fun qk : Fin r × Fin S.n ↦ rr qk.1 qk.2) (o i) (fun lam hlam ↦ by
    have hall : ∀ i' < k, ∑ qk : Fin r × Fin S.n, lam qk * o i' qk = 0 := by
      apply hind (fun i' ↦ ∑ qk : Fin r × Fin S.n, lam qk * o i' qk)
      have e1 : ∑ i' ∈ Finset.range k, ((∑ qk : Fin r × Fin S.n, lam qk * o i' qk : ℚ) : C) * d i' =
          ∑ qk : Fin r × Fin S.n, (lam qk : C) * ∑ i' ∈ Finset.range k, d i' *
            (if h : i' < k then (S.ordAt K ⟨w i', (hw i' h).1⟩ (pq (K := K) ζ c βq qk.1 qk.2).1
              (pq (K := K) ζ c βq qk.1 qk.2).2 : C) else 0) := by
        simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun qk _ ↦ Finset.sum_congr rfl fun i' hi' ↦ ?_
        have hi'' := Finset.mem_range.mp hi'
        simp only [ho, dif_pos hi'']
        push_cast
        ring
      rw [e1]
      simp_rw [hresid]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun e _ ↦ ?_
      have := hlam e
      have h2 : ∑ qk : Fin r × Fin S.n, (lam qk : C) * ((rr qk.1 qk.2 e : C) * ν e) =
          ((∑ qk : Fin r × Fin S.n, lam qk * rr qk.1 qk.2 e : ℚ) : C) * ν e := by
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun qk _ ↦ by ring
      rw [h2, this]; simp
    exact hall i hi)
  refine ⟨T, fun q kk ↦ ?_⟩
  have := hT (q, kk)
  simp only [ho, dif_pos hi] at this
  rw [← this]

/-- Clearing denominators: `L x ∈ ℤ` when `den x ∣ L`. -/
lemma rat_mul_den_int (x : ℚ) (L : ℕ) (h : x.den ∣ L) :
    ((L : ℚ) * x) = (((L / x.den : ℕ) : ℤ) * x.num : ℤ) := by
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div h (by exact_mod_cast x.den_nz)]
  conv_lhs => rw [← Rat.num_div_den x]
  have : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  field_simp

include hx hK hgood hconstC hb hDR hRne hDoff hbP hβq hres hc0 hζ in
/-- **With witnesses of the components**: `b yʲ = (a yʲ)′ + ∑_e e_e (E_e)ⱼ yʲ + e₀ (E₀)ⱼ yʲ`, where
`W_e` has divisor `m_e D_e` away from `x = 0`, `(E_e)ᵢ` are the coordinates of `W_e′/W_e`, and `W₀`
governs the projections of the logarithms supported over `x = 0` and `∞` (`hZ`). -/
theorem ky_liouville (hj0 : 0 < (j : ℕ)) (hbm : b * S.y ^ (j : ℕ) ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y ^ (j : ℕ) = v′ + ∑ i ∈ s, cs i * logDeriv (u i))
    (Wt : E → C⟮S.x⟯⟮S.y⟯) (hWt0 : ∀ e, Wt e ≠ 0) (me : E → ℕ) (hme : ∀ e, 0 < me e)
    (hWo : ∀ e q (kk : Fin S.n), (S.ordAt K (Wt e) (pq (K := K) ζ c βq q kk).1
      (pq (K := K) ζ c βq q kk).2 : ℚ) = me e * rr q kk e)
    (hWz : ∀ e (α β' : K), β' ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
      (∀ q, α ≠ algebraMap C K (c q)) → S.ordAt K (Wt e) α β' = 0)
    (W₀ : C⟮S.x⟯⟮S.y⟯)
    (hZ : ∀ U : C⟮S.x⟯⟮S.y⟯, U ≠ 0 → S.Supp (K := K) U → ∃ e : C, e′ = 0 ∧
      S.four ζ hζ j (S.dl (Polynomial.C η * X) hx U) = S.cst e * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx W₀))
    (EW : E → Fin S.n → C⟮S.x⟯) (hEW : ∀ e, S.dl (Polynomial.C η * X) hx (Wt e) =
      ∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (EW e i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ))
    (E0 : Fin S.n → C⟮S.x⟯) (hE0 : S.dl (Polynomial.C η * X) hx W₀ =
      ∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (E0 i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) :
    ∃ a ∈ C⟮S.x⟯, ∃ (ee : E → C) (e0 : C), (∀ e, (ee e)′ = 0) ∧ e0′ = 0 ∧
      b * S.y ^ (j : ℕ) = (a * S.y ^ (j : ℕ))′ +
        ∑ e, algebraMap C L (ee e) * ((EW e j : L) * S.y ^ (j : ℕ)) +
        algebraMap C L e0 * ((E0 j : L) * S.y ^ (j : ℕ)) := by
  classical
  obtain ⟨k, d, w, hw, hind, heq', hdc, hzero, hresid, hT⟩ :=
    S.ky_orders (K := K) η hx ζ hζ j hK hgood hconstC c hc0 P l b hb D R hDR hRne hDoff hbP βq hβq ν
      rr hres hj0 hbm s cs u hcs hu v hv heq
  choose! T hT using hT
  set xr : ℕ → E → ℚ := fun i e ↦ T i e / me e with hxr
  set Lc : ℕ := ∏ i ∈ Finset.range k, ∏ e, (xr i e).den with hLc
  have hLc0 : 0 < Lc := Finset.prod_pos fun i _ ↦ Finset.prod_pos fun e _ ↦ (xr i e).den_pos
  have hdvd : ∀ i < k, ∀ e, (xr i e).den ∣ Lc := fun i hi e ↦
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ e)).trans
      (Finset.dvd_prod_of_mem (fun i ↦ ∏ e, (xr i e).den) (Finset.mem_range.mpr hi))
  set z : ℕ → E → ℤ := fun i e ↦ ((Lc / (xr i e).den : ℕ) : ℤ) * (xr i e).num with hz
  have hzq : ∀ i < k, ∀ e, (z i e : ℚ) = Lc * xr i e := fun i hi e ↦
    (rat_mul_den_int (xr i e) Lc (hdvd i hi e)).symm
  set W : ℕ → C⟮S.x⟯⟮S.y⟯ := fun i ↦ if h : i < k then ⟨w i, (hw i h).1⟩ else 1 with hW
  have hW0 : ∀ i < k, W i ≠ 0 := fun i hi h ↦ (hw i hi).2 (by
    have := congrArg Subtype.val h; simpa [hW, dif_pos hi] using this)
  set U : ℕ → C⟮S.x⟯⟮S.y⟯ := fun i ↦ W i ^ (Lc : ℤ) * ∏ e, Wt e ^ (-z i e) with hU
  have hPr0 : ∀ i, ∏ e, Wt e ^ (-z i e) ≠ 0 := fun i ↦
    Finset.prod_ne_zero_iff.mpr fun e _ ↦ zpow_ne_zero _ (hWt0 e)
  have hU0 : ∀ i < k, U i ≠ 0 := fun i hi ↦ mul_ne_zero (zpow_ne_zero _ (hW0 i hi)) (hPr0 i)
  -- the orders of `U i`
  have hordU : ∀ i < k, ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K (U i) α β' = Lc * S.ordAt K (W i) α β' - ∑ e, z i e * S.ordAt K (Wt e) α β' := by
    intro i hi α β' hv'
    rw [hU, S.ordAt_mul hv' (zpow_ne_zero _ (hW0 i hi)) (hPr0 i), S.ordAt_zpow hv',
      S.ordAt_prod hv' _ _ (fun e _ ↦ zpow_ne_zero _ (hWt0 e))]
    simp only [S.ordAt_zpow hv', neg_mul, Finset.sum_neg_distrib]
    ring
  have hSuppU : ∀ i < k, S.Supp (K := K) (U i) := by
    intro i hi α β' hv' hα
    rw [hordU i hi α β' hv']
    by_cases hq : ∃ q, α = algebraMap C K (c q)
    · obtain ⟨q, rfl⟩ := hq
      have hb0 : algebraMap C K (βq q) ≠ 0 := (_root_.map_ne_zero _).mpr (hβq q).1
      have hv0 : (algebraMap C K (βq q)) ^ S.n =
          (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) := by
        have := S.pq_v (K := K) ζ hζ c βq hβq q 0
        simpa [pq] using this
      obtain ⟨kk, hkk, rfl⟩ := S.over_k ζ hζ _ _ hb0 hv0 β' hv'
      have hpt : (pq (K := K) ζ c βq q kk) = (algebraMap C K (c q),
          algebraMap C K ζ ^ kk * algebraMap C K (βq q)) := by simp [pq]
      have h1 := hT i hi q ⟨kk, hkk⟩
      simp only [hpt] at h1
      have hWo' : ∀ e, (S.ordAt K (Wt e) (algebraMap C K (c q))
          (algebraMap C K ζ ^ kk * algebraMap C K (βq q)) : ℚ) = me e * rr q kk e := fun e ↦ by
        have := hWo e q ⟨kk, hkk⟩
        simpa [pq] using this
      have hWi : S.ordAt K (W i) (algebraMap C K (c q)) (algebraMap C K ζ ^ kk * algebraMap C K (βq q)) =
          S.ordAt K ⟨w i, (hw i hi).1⟩ (algebraMap C K (c q))
            (algebraMap C K ζ ^ kk * algebraMap C K (βq q)) := by
        simp [hW, dif_pos hi]
      rw [hWi]
      have key : ((Lc * S.ordAt K ⟨w i, (hw i hi).1⟩ (algebraMap C K (c q))
          (algebraMap C K ζ ^ kk * algebraMap C K (βq q)) - ∑ e, z i e * S.ordAt K (Wt e)
            (algebraMap C K (c q)) (algebraMap C K ζ ^ kk * algebraMap C K (βq q)) : ℤ) : ℚ) = 0 := by
        push_cast
        rw [h1]
        simp only [hWo', fun e ↦ hzq i hi e, hxr]
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_eq_zero fun e _ ↦ ?_
        have : (me e : ℚ) ≠ 0 := by exact_mod_cast (hme e).ne'
        field_simp
        ring
      exact_mod_cast key
    · push Not at hq
      have hWi : S.ordAt K (W i) α β' = 0 := by
        have := hzero i hi α β' hv' hα (fun q h ↦ hq q h)
        simpa [hW, dif_pos hi] using this
      rw [hWi, mul_zero, zero_sub, neg_eq_zero]
      exact Finset.sum_eq_zero fun e _ ↦ by rw [hWz e α β' hv' hα (fun q h ↦ hq q h), mul_zero]
  -- the projections
  have hZi : ∀ i < k, ∃ eZ : C, eZ′ = 0 ∧ S.four ζ hζ j (S.dl (Polynomial.C η * X) hx (U i)) =
      S.cst eZ * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx W₀) := fun i hi ↦
    hZ (U i) (hU0 i hi) (hSuppU i hi)
  choose! eZ heZ0 heZ using hZi
  have hcstInt : ∀ m : ℤ, ((m : C⟮S.x⟯⟮S.y⟯)) = S.cst (m : C) := fun m ↦ Subtype.ext (by simp [cst])
  have hLne : (Lc : C) ≠ 0 := by exact_mod_cast hLc0.ne'
  have hproj_i : ∀ i < k, S.cst (d i) * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx (W i)) =
      S.cst (d i * eZ i / Lc) * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx W₀) +
        ∑ e, S.cst (d i * z i e / Lc) * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx (Wt e)) := by
    intro i hi
    have hdU : S.dl (Polynomial.C η * X) hx (U i) = ((Lc : ℤ) : C⟮S.x⟯⟮S.y⟯) *
        S.dl (Polynomial.C η * X) hx (W i) +
        ∑ e, ((-z i e : ℤ) : C⟮S.x⟯⟮S.y⟯) * S.dl (Polynomial.C η * X) hx (Wt e) := by
      rw [hU, S.dl_mul _ _ _ _ (zpow_ne_zero _ (hW0 i hi)) (hPr0 i), S.dl_zpow _ _ _ (hW0 i hi),
        S.dl_prod _ _ _ _ (fun e _ ↦ zpow_ne_zero _ (hWt0 e))]
      congr 1
      exact Finset.sum_congr rfl fun e _ ↦ S.dl_zpow _ _ _ (hWt0 e) _
    have h1 := heZ i hi
    rw [hdU, S.four_add, S.four_intCast_mul, S.four_sum] at h1
    simp_rw [S.four_intCast_mul] at h1
    rw [hcstInt] at h1
    simp_rw [hcstInt] at h1
    have h2 : S.cst (d i / Lc) * (S.cst ((Lc : ℤ) : C) * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx (W i)) +
        ∑ e, S.cst ((-z i e : ℤ) : C) * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx (Wt e))) =
        S.cst (d i / Lc) * (S.cst (eZ i) * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx W₀)) := by
      rw [h1]
    rw [mul_add, Finset.mul_sum, ← mul_assoc, ← S.cst_mul] at h2
    simp only [← mul_assoc, ← S.cst_mul] at h2
    have e1 : d i / Lc * ((Lc : ℤ) : C) = d i := by push_cast; field_simp
    rw [e1] at h2
    rw [eq_sub_of_add_eq h2, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · rw [show d i / Lc * eZ i = d i * eZ i / Lc by ring]
    · refine Finset.sum_congr rfl fun e _ ↦ ?_
      rw [← neg_mul]
      congr 1
      apply Subtype.ext
      simp only [cst, IntermediateField.coe_neg]
      rw [← map_neg]
      congr 1
      push_cast
      ring
  obtain ⟨a, h4⟩ := S.ky_project η hx ζ hζ j b hb hbm k d w hw v hv heq'
  set e0 : C := ∑ i ∈ Finset.range k, d i * eZ i / Lc with he0
  set ee : E → C := fun e ↦ ∑ i ∈ Finset.range k, d i * z i e / Lc with hee
  have hsum : ∑ i ∈ Finset.range k, S.cst (d i) * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx
      (if h : i < k then ⟨w i, (hw i h).1⟩ else 1)) =
      S.cst e0 * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx W₀) +
        ∑ e, S.cst (ee e) * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx (Wt e)) := by
    rw [Finset.sum_congr rfl fun i hi ↦ hproj_i i (Finset.mem_range.mp hi), Finset.sum_add_distrib,
      he0, S.cst_sum, Finset.sum_mul, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [hee, S.cst_sum, Finset.sum_mul]
  rw [hsum, hE0, S.four_repr] at h4
  simp_rw [hEW, S.four_repr] at h4
  refine ⟨a, a.2, ee, e0, fun e ↦ ?_, ?_, ?_⟩
  · simp only [hee, map_sum]
    exact Finset.sum_eq_zero fun i hi ↦ by
      rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz, hdc i (Finset.mem_range.mp hi),
        Derivation.map_intCast, Derivation.leibniz_inv, Derivation.map_natCast]
      simp
  · simp only [he0, map_sum]
    exact Finset.sum_eq_zero fun i hi ↦ by
      rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz, hdc i (Finset.mem_range.mp hi),
        heZ0 i (Finset.mem_range.mp hi), Derivation.leibniz_inv, Derivation.map_natCast]
      simp
  have hL := congrArg Subtype.val h4
  simp only [IntermediateField.coe_mul, IntermediateField.coe_add, coe_dTW,
    IntermediateField.coe_pow, IntermediateField.coe_sum] at hL
  have hn0 : ((S.n : C⟮S.x⟯⟮S.y⟯) : L) = (S.n : L) := by simp
  rw [hn0] at hL
  have hnL : (S.n : L) ≠ 0 := by exact_mod_cast S.hn.ne'
  rw [Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero, smul_eq_mul] at hL
  have hy : ((AdjoinSimple.gen C⟮S.x⟯ S.y : C⟮S.x⟯⟮S.y⟯) : L) = S.y := rfl
  simp only [IntermediateField.algebraMap_apply, hy] at hL
  apply mul_left_cancel₀ hnL
  have e1 : ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨b, hb⟩ : C⟮S.x⟯⟮S.y⟯) : L) = b := rfl
  have e2 : ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a : C⟮S.x⟯⟮S.y⟯) : L) = (a : L) := rfl
  have e3 : ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (E0 j) : C⟮S.x⟯⟮S.y⟯) : L) = (E0 j : L) := rfl
  have e4 : ((S.cst e0 : C⟮S.x⟯⟮S.y⟯) : L) = algebraMap C L e0 := rfl
  have e5 : ∀ e, ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (EW e j) : C⟮S.x⟯⟮S.y⟯) : L) = (EW e j : L) :=
    fun e ↦ rfl
  have e6 : ∀ e, ((S.cst (ee e) : C⟮S.x⟯⟮S.y⟯) : L) = algebraMap C L (ee e) := fun e ↦ rfl
  simp only [e1, e2, e3, e4, e5, e6] at hL
  rw [mul_add, mul_add, Finset.mul_sum, hL]
  have : ∀ x, (algebraMap C L) (ee x) * (↑S.n * (↑(EW x j) * S.y ^ (j : ℕ))) =
      ↑S.n * ((algebraMap C L) (ee x) * (↑(EW x j) * S.y ^ (j : ℕ))) := fun x ↦ by ring
  simp only [this]
  ring

include hx hK hgood hconstC hb hDR hRne hDoff hbP hβq hres hc0 hζ in
/-- **A component that is not torsion**: a Liouville form produces a function with divisor
`M D_e` away from `∞`, provided the parts over `x = 0` can be killed (`hkill`). -/
theorem ky_nontors (hj0 : 0 < (j : ℕ)) (hbm : b * S.y ^ (j : ℕ) ∈ C⟮S.x⟯⟮S.y⟯)
    (hν : ∀ t : E → ℚ, ∑ e, (t e : C) * ν e = 0 → ∀ e, t e = 0)
    (hkill : ∀ V : C⟮S.x⟯⟮S.y⟯, V ≠ 0 → (∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      α ≠ 0 → (∀ q, α ≠ algebraMap C K (c q)) → S.ordAt K V α β' = 0) →
      ∃ V' : C⟮S.x⟯⟮S.y⟯, V' ≠ 0 ∧ ∃ M : ℕ, 0 < M ∧
        (∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
          S.ordAt K V' α β' = M * S.ordAt K V α β') ∧
        (∀ β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval 0 → S.ordAt K V' 0 β' = 0))
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y ^ (j : ℕ) = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) (e : E) :
    ∃ V : C⟮S.x⟯⟮S.y⟯, V ≠ 0 ∧ ∃ M : ℕ, 0 < M ∧
      (∀ q (kk : Fin S.n), (S.ordAt K V (pq (K := K) ζ c βq q kk).1 (pq (K := K) ζ c βq q kk).2 : ℚ) =
        M * rr q kk e) ∧
      (∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
        (∀ q, α ≠ algebraMap C K (c q)) → S.ordAt K V α β' = 0) ∧
      (∀ β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval 0 → S.ordAt K V 0 β' = 0) := by
  classical
  obtain ⟨k, d, w, hw, hind, heq', hdc, hzero, hresid, -⟩ :=
    S.ky_orders (K := K) η hx ζ hζ j hK hgood hconstC c hc0 P l b hb D R hDR hRne hDoff hbP βq hβq ν
      rr hres hj0 hbm s cs u hcs hu v hv heq
  set o : Fin r × Fin S.n → Fin k → ℚ := fun qk i ↦
    (S.ordAt K ⟨w i, (hw i i.2).1⟩ (pq (K := K) ζ c βq qk.1 qk.2).1
      (pq (K := K) ζ c βq qk.1 qk.2).2 : ℚ) with ho
  obtain ⟨sv, hsv⟩ := exists_comb o (fun qk ↦ rr qk.1 qk.2 e) (fun lam hlam ↦ by
    have h0 : ∑ e', ((∑ qk : Fin r × Fin S.n, lam qk * rr qk.1 qk.2 e' : ℚ) : C) * ν e' = 0 := by
      have e1 : ∑ e', ((∑ qk : Fin r × Fin S.n, lam qk * rr qk.1 qk.2 e' : ℚ) : C) * ν e' =
          ∑ qk : Fin r × Fin S.n, (lam qk : C) * ∑ e', (rr qk.1 qk.2 e' : C) * ν e' := by
        simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [e1]
      simp_rw [← hresid]
      have e2 : ∀ qk : Fin r × Fin S.n, (lam qk : C) * ∑ i ∈ Finset.range k, d i *
          (if h : i < k then (S.ordAt K ⟨w i, (hw i h).1⟩ (pq (K := K) ζ c βq qk.1 qk.2).1
            (pq (K := K) ζ c βq qk.1 qk.2).2 : C) else 0) =
          ∑ i : Fin k, d i * ((lam qk * o qk i : ℚ) : C) := fun qk ↦ by
        rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun i ↦ (lam qk : C) * (d i *
          (if h : i < k then (S.ordAt K ⟨w i, (hw i h).1⟩ (pq (K := K) ζ c βq qk.1 qk.2).1
            (pq (K := K) ζ c βq qk.1 qk.2).2 : C) else 0)))]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [dif_pos i.2, ho]
        push_cast
        ring
      simp_rw [e2]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [← Finset.mul_sum, ← Rat.cast_sum, hlam i, Rat.cast_zero, mul_zero]
    exact hν _ h0 e)
  -- clear denominators
  set Lc : ℕ := ∏ i : Fin k, (sv i).den with hLc
  have hLc0 : 0 < Lc := Finset.prod_pos fun i _ ↦ (sv i).den_pos
  have hdvd : ∀ i, (sv i).den ∣ Lc := fun i ↦ Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set y : Fin k → ℤ := fun i ↦ ((Lc / (sv i).den : ℕ) : ℤ) * (sv i).num with hy
  have hyq : ∀ i, (y i : ℚ) = Lc * sv i := fun i ↦ (rat_mul_den_int (sv i) Lc (hdvd i)).symm
  set Wf : Fin k → C⟮S.x⟯⟮S.y⟯ := fun i ↦ ⟨w i, (hw i i.2).1⟩ with hWf
  have hWf0 : ∀ i, Wf i ≠ 0 := fun i h ↦ (hw i i.2).2 (by
    have := congrArg Subtype.val h; simpa [hWf] using this)
  set V : C⟮S.x⟯⟮S.y⟯ := ∏ i, Wf i ^ y i with hV
  have hV0 : V ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hWf0 i)
  have hordV : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K V α β' = ∑ i, y i * S.ordAt K (Wf i) α β' := fun α β' hv' ↦ by
    rw [hV, S.ordAt_prod hv' _ _ (fun i _ ↦ zpow_ne_zero _ (hWf0 i))]
    simp only [S.ordAt_zpow hv']
  have hVz : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
      (∀ q, α ≠ algebraMap C K (c q)) → S.ordAt K V α β' = 0 := fun α β' hv' hα hq ↦ by
    rw [hordV α β' hv']
    exact Finset.sum_eq_zero fun i _ ↦ by rw [show S.ordAt K (Wf i) α β' = 0 from hzero i i.2 α β' hv' hα hq, mul_zero]
  obtain ⟨V', hV'0, M, hM, hV'o, hV'z⟩ := hkill V hV0 hVz
  refine ⟨V', hV'0, M * Lc, Nat.mul_pos hM hLc0, fun q kk ↦ ?_, fun α β' hv' hα hq ↦ ?_, hV'z⟩
  · have hv' := S.pq_v (K := K) ζ hζ c βq hβq q kk
    have hne : (pq (K := K) ζ c βq q kk).1 ≠ 0 := by
      simp only [pq]; exact (_root_.map_ne_zero _).mpr (hc0 q)
    rw [hV'o _ _ hv' hne, hordV _ _ hv']
    push_cast
    have := hsv (q, kk)
    simp only [ho] at this
    rw [← this, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hyq i]
    ring
  · rw [hV'o α β' hv' hα, hVz α β' hv' hα hq, mul_zero]

end Poles

end SuperData

end Differential
