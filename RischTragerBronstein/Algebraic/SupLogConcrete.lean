import RischTragerBronstein.Algebraic.SupLogAbel

/-!
# The concrete integrand `B(x, y) + ∑ Gᵢ(x, y)/(x − aᵢ)`

`hInt B a G = elemW B + ∑ᵢ elemW Gᵢ / (x − aᵢ)`: its residue at an ordinary point `(aᵢ, β)` is
`Gᵢ(aᵢ, β)` (`res_hInt_nb`), it has no residue at the branch points when `p(aᵢ) ≠ 0`
(`res_hInt_br`), and its poles are simple at ordinary points (`ordAt_hInt_nb`), absent at branch
points (`ordAt_hInt_br`), of order `≤ H` at infinity (`ordInf_hInt`).
-/

open Polynomial IntermediateField HahnSeries

namespace Differential.SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

/-- `B(x, y) + B₁(x, y)/p(x) + ∑ᵢ Gᵢ(x, y) / (x − aᵢ)`. -/
noncomputable def hInt {m : ℕ} (B B₁ : C[X][X]) (a : Fin m → C) (G : Fin m → C[X][X]) :
    C⟮S.x⟯⟮S.y⟯ :=
  S.elemW B + S.elemW B₁ * (S.polyX S.p)⁻¹ +
    ∑ i, S.elemW (G i) * (S.polyX (X - Polynomial.C (a i)))⁻¹

lemma _root_.LaurentSeries.res_sum {ι : Type*} (s : Finset ι) (F : ι → LaurentSeries K) :
    LaurentSeries.res (∑ i ∈ s, F i) = ∑ i ∈ s, LaurentSeries.res (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LaurentSeries.res]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, LaurentSeries.res_add, ih]

lemma order_sum_ge {M : Type*} [Field M] (φ : M →+* LaurentSeries K) {t : ℤ} (ht : t ≤ 0)
    {ι : Type*} (s : Finset ι) (f : ι → M) (h : ∀ i ∈ s, t ≤ (φ (f i)).order) :
    t ≤ (φ (∑ i ∈ s, f i)).order := by
  rw [map_sum]
  exact Finset.sum_induction _ (fun F : LaurentSeries K ↦ t ≤ F.order)
    (fun F G hF hG ↦ LaurentSeries.order_add_ge ht F G hF hG)
    (by rw [HahnSeries.order_zero]; exact ht) h

/-- Order of `W / (x − a)` at a point, from lower bounds. -/
lemma order_div_X_sub_ge {M : Type*} [Field M] (φ : M →+* LaurentSeries K) {t : ℤ} (ht : t ≤ 0)
    (w d : M) (hw : 0 ≤ (φ w).order) (hd : (φ d).order ≤ -t) : t ≤ (φ (w * d⁻¹)).order := by
  by_cases h0 : w * d⁻¹ = 0
  · rw [h0, map_zero, HahnSeries.order_zero]; exact ht
  obtain ⟨hw0, hd0⟩ := mul_ne_zero_iff.mp h0
  rw [order_hom_mul φ hw0 hd0, order_hom_inv]
  omega

lemma elemW_ordAt_nonneg (W : C[X][X]) (α β : K)
    (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) : 0 ≤ S.ordAt K (S.elemW W) α β :=
  S.elemW_integral W α β hv

omit [CharZero C] in
lemma res_zero_of_order (F : LaurentSeries K) (h : 0 ≤ F.order) : LaurentSeries.res F = 0 := by
  by_cases hF : F = 0
  · rw [hF]; rfl
  exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)

omit [CharZero K] in
lemma ordAt_polyX_p_nb (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) : S.ordAt K (S.polyX S.p) α β = 0 := by
  rw [S.ordAt_polyX _ S.hsq.ne_zero α β hβp, if_neg hβ, rootMultiplicity_eq_zero]
  · simp
  · intro h
    rw [IsRoot.def, ← hβp] at h
    exact hβ (pow_eq_zero_iff S.hn.ne' |>.mp h)

omit [CharZero K] in
lemma ordAt_polyX_p_br (e : K) (he : (S.p.map (algebraMap C K)).eval e = 0) :
    S.ordAt K (S.polyX S.p) e 0 ≤ S.n := by
  have hv : (0 : K) ^ S.n = (S.p.map (algebraMap C K)).eval e := by rw [he, zero_pow S.hn.ne']
  rw [S.ordAt_polyX _ S.hsq.ne_zero e 0 hv, if_pos rfl]
  have hsep : (S.p.map (algebraMap C K)).Separable :=
    (PerfectField.separable_iff_squarefree.mpr S.hsq).map
  have := rootMultiplicity_le_one_of_separable hsep e
  have hn := S.hn
  nlinarith

omit [CharZero K] in
lemma order_sum_ge_or {M : Type*} [Field M] (φ : M →+* LaurentSeries K) (t : ℤ)
    {ι : Type*} (s : Finset ι) (f : ι → M) (h : ∀ i ∈ s, f i = 0 ∨ t ≤ (φ (f i)).order) :
    ∑ i ∈ s, f i = 0 ∨ t ≤ (φ (∑ i ∈ s, f i)).order := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    by_cases hs : f j + ∑ i ∈ s, f i = 0
    · left; exact hs
    right
    rcases h1 with h1 | h1
    · rw [h1, zero_add] at hs ⊢
      exact h2.resolve_left hs
    rcases h2 with h2 | h2
    · rw [h2, add_zero]; exact h1
    rw [map_add]
    refine le_trans (le_min h1 h2) (HahnSeries.min_order_le_order_add ?_)
    rw [← map_add]; exact (map_ne_zero_iff _ φ.injective).mpr hs

/-- Without a constant term in `y`, `elemW W` vanishes at the branch points. -/
lemma elemW_br_pos (W : C[X][X]) (hW : W.coeff 0 = 0) (e : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) :
    S.elemW W = 0 ∨ 1 ≤ S.ordAt K (S.elemW W) e 0 := by
  have hv : (0 : K) ^ S.n = (S.p.map (algebraMap C K)).eval e := by rw [he, zero_pow S.hn.ne']
  obtain ⟨φ, hφ⟩ := S.ordAt_hom e 0 hv
  rw [hφ, elemW]
  refine order_sum_ge_or φ 1 _ _ fun i _ ↦ ?_
  by_cases h0 : S.polyX (W.coeff i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ i = 0
  · left; exact h0
  right
  obtain ⟨hP0, hy0⟩ := mul_ne_zero_iff.mp h0
  have hi : i ≠ 0 := by
    rintro rfl
    apply hP0
    rw [hW]; simp [polyX]
  have hP : W.coeff i ≠ 0 := fun h ↦ hP0 (by rw [h]; simp [polyX])
  rw [order_hom_mul φ hP0 hy0, order_hom_pow, ← hφ, ← hφ, S.ordAt_polyX _ hP e 0 hv,
    S.ordAt_gen e 0 hv, if_pos rfl, if_pos rfl]
  have : 0 ≤ (((W.coeff i).map (algebraMap C K)).rootMultiplicity e : ℤ) := by positivity
  have : (1 : ℤ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
  nlinarith [S.hn]

lemma ordAt_B₁_nb (B₁ : C[X][X]) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    0 ≤ S.ordAt K (S.elemW B₁ * (S.polyX S.p)⁻¹) α β := by
  obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hβp
  rw [hφ]
  refine order_div_X_sub_ge φ le_rfl _ _ (by rw [← hφ]; exact S.elemW_ordAt_nonneg _ α β hβp) ?_
  rw [← hφ, S.ordAt_polyX_p_nb α β hβ hβp]; simp

lemma ordAt_B₁_br (B₁ : C[X][X]) (hB₁ : B₁.coeff 0 = 0) (e : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) :
    1 - (S.n : ℤ) ≤ S.ordAt K (S.elemW B₁ * (S.polyX S.p)⁻¹) e 0 := by
  have hv : (0 : K) ^ S.n = (S.p.map (algebraMap C K)).eval e := by rw [he, zero_pow S.hn.ne']
  rcases S.elemW_br_pos B₁ hB₁ e he with h0 | h1
  · rw [h0, zero_mul]
    obtain ⟨φ, hφ⟩ := S.ordAt_hom e 0 hv
    rw [hφ, map_zero, HahnSeries.order_zero]; have := S.hn; omega
  have hne : S.elemW B₁ ≠ 0 := by
    intro h; rw [h] at h1
    obtain ⟨φ, hφ⟩ := S.ordAt_hom e 0 hv
    rw [hφ, map_zero, HahnSeries.order_zero] at h1; omega
  rw [S.ordAt_mul hv hne (inv_ne_zero (S.polyX_ne_zero S.hsq.ne_zero)), S.ordAt_inv hv]
  have := S.ordAt_polyX_p_br (K := K) e he
  omega

open Classical in
/-- **Residues at ordinary points.** -/
theorem res_hInt_nb {m : ℕ} (B B₁ : C[X][X]) (a : Fin m → C) (G : Fin m → C[X][X])
    (hG : ∀ i j, S.n ≤ j → (G i).coeff j = 0) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    LaurentSeries.res (S.embXY α β hβ hβp (S.hInt B B₁ a G)) =
      ∑ i, if α = algebraMap C K (a i) then
        Sup.evalW ((G i).map (mapRingHom (algebraMap C K))) α β else 0 := by
  unfold hInt
  rw [map_add, map_add, LaurentSeries.res_add, LaurentSeries.res_add, map_sum, LaurentSeries.res_sum,
    res_zero_of_order _ (by rw [← S.ordAt_nb _ α β hβ hβp]; exact S.elemW_ordAt_nonneg B α β hβp),
    res_zero_of_order _ (by rw [← S.ordAt_nb _ α β hβ hβp]; exact S.ordAt_B₁_nb B₁ α β hβ hβp),
    zero_add, zero_add]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  split_ifs with hα
  · subst hα
    exact S.res_elemW_div (G i) (hG i) (a i) β hβ hβp
  · refine res_zero_of_order _ ?_
    rw [← S.ordAt_nb _ α β hβ hβp]
    obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hβp
    rw [hφ]
    refine order_div_X_sub_ge φ le_rfl _ _ (by rw [← hφ]; exact S.elemW_ordAt_nonneg _ α β hβp) ?_
    rw [← hφ, S.ordAt_X_sub _ _ _ hβp, if_neg hα]; simp

/-- **Poles at ordinary points are simple.** -/
theorem ordAt_hInt_nb {m : ℕ} (B B₁ : C[X][X]) (a : Fin m → C) (G : Fin m → C[X][X]) (α β : K)
    (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    -1 ≤ S.ordAt K (S.hInt B B₁ a G) α β := by
  obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hβp
  rw [hφ, hInt, map_add, map_add]
  refine LaurentSeries.order_add_ge (by norm_num) _ _
    (LaurentSeries.order_add_ge (by norm_num) _ _
      (by rw [← hφ]; exact le_trans (by norm_num) (S.elemW_ordAt_nonneg B α β hβp))
      (by rw [← hφ]; exact le_trans (by norm_num) (S.ordAt_B₁_nb B₁ α β hβ hβp))) ?_
  refine order_sum_ge φ (by norm_num) _ _ fun i _ ↦ order_div_X_sub_ge φ (by norm_num) _ _
    (by rw [← hφ]; exact S.elemW_ordAt_nonneg _ α β hβp) ?_
  rw [← hφ, S.ordAt_X_sub _ _ _ hβp, if_neg hβ]
  split_ifs <;> norm_num

/-- **No poles at branch points** (when no `aᵢ` is a root of `p`). -/
theorem ordAt_hInt_br {m : ℕ} (B B₁ : C[X][X]) (a : Fin m → C) (G : Fin m → C[X][X])
    (hB₁ : B₁.coeff 0 = 0) (ha : ∀ i, S.p.eval (a i) ≠ 0) (e : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) :
    1 - (S.n : ℤ) ≤ S.ordAt K (S.hInt B B₁ a G) e 0 := by
  have hv : (0 : K) ^ S.n = (S.p.map (algebraMap C K)).eval e := by rw [he, zero_pow S.hn.ne']
  have ht : 1 - (S.n : ℤ) ≤ 0 := by have := S.hn; omega
  obtain ⟨φ, hφ⟩ := S.ordAt_hom e 0 hv
  rw [hφ, hInt, map_add, map_add]
  refine LaurentSeries.order_add_ge ht _ _ (LaurentSeries.order_add_ge ht _ _
    (by rw [← hφ]; exact le_trans ht (S.elemW_ordAt_nonneg B e 0 hv))
    (by rw [← hφ]; exact S.ordAt_B₁_br B₁ hB₁ e he)) ?_
  refine order_sum_ge φ ht _ _ fun i _ ↦ order_div_X_sub_ge φ ht _ _
    (by rw [← hφ]; exact S.elemW_ordAt_nonneg _ e 0 hv) ?_
  have hne : e ≠ algebraMap C K (a i) := by
    rintro rfl
    apply ha i
    rw [eval_map, eval₂_hom] at he
    exact (map_eq_zero_iff _ (algebraMap C K).injective).mp he
  rw [← hφ, S.ordAt_X_sub _ _ _ hv, if_neg hne]; simp; omega

/-- **No residues at branch points.** -/
theorem res_hInt_br {m : ℕ} (B B₁ : C[X][X]) (a : Fin m → C) (G : Fin m → C[X][X])
    (hB₁ : B₁.coeff 0 = 0) (ha : ∀ i, S.p.eval (a i) ≠ 0) (e γ : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0) (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) :
    LaurentSeries.res (S.embB e γ he hγ hγp (S.hInt B B₁ a G) *
      single ((S.n : ℤ) - 1) (S.n : K)) = 0 := by
  by_cases hz : S.embB e γ he hγ hγp (S.hInt B B₁ a G) = 0
  · rw [hz, zero_mul]; rfl
  refine res_zero_of_order _ ?_
  have h1 := S.ordAt_hInt_br B B₁ a G hB₁ ha e he
  rw [S.ordAt_br _ e γ he hγ hγp] at h1
  have hn0 : (S.n : K) ≠ 0 := by exact_mod_cast S.hn.ne'
  rw [HahnSeries.order_mul hz (HahnSeries.single_ne_zero hn0), HahnSeries.order_single hn0]
  have := S.hn
  omega

/-- **The pole at infinity.** -/
theorem ordInf_hInt (hcop : Nat.Coprime S.n S.p.natDegree) {m : ℕ} (B B₁ : C[X][X])
    (a : Fin m → C) (G : Fin m → C[X][X]) (H : ℕ)
    (hB : ∀ i c, (B.coeff i).coeff c ≠ 0 → i < S.n ∧ S.n * c + S.p.natDegree * i ≤ H)
    (hB₁ : ∀ i c, (B₁.coeff i).coeff c ≠ 0 →
      i < S.n ∧ S.n * c + S.p.natDegree * i ≤ H + S.n * S.p.natDegree)
    (hG : ∀ k i c, ((G k).coeff i).coeff c ≠ 0 → i < S.n ∧ S.n * c + S.p.natDegree * i ≤ H + S.n) :
    -(H : ℤ) ≤ S.ordInf K (S.hInt B B₁ a G) := by
  obtain ⟨φ, hφ⟩ := S.ordInf_hom (K := K) hcop
  rw [hφ, hInt, map_add, map_add]
  refine LaurentSeries.order_add_ge (by omega) _ _ (LaurentSeries.order_add_ge (by omega) _ _ ?_ ?_) ?_
  · by_cases h0 : S.elemW B = 0
    · rw [h0, map_zero, HahnSeries.order_zero]; omega
    · rw [← hφ]; exact S.elemW_ordInf hcop B H hB h0
  · by_cases h0 : S.elemW B₁ * (S.polyX S.p)⁻¹ = 0
    · rw [h0, map_zero, HahnSeries.order_zero]; omega
    obtain ⟨hw0, hd0⟩ := mul_ne_zero_iff.mp h0
    rw [order_hom_mul φ hw0 hd0, order_hom_inv, ← hφ, ← hφ, S.ordInf_polyX hcop _ S.hsq.ne_zero]
    have := S.elemW_ordInf (K := K) hcop B₁ _ hB₁ hw0
    push_cast at this ⊢
    omega
  refine order_sum_ge φ (by omega) _ _ fun i _ ↦ ?_
  by_cases h0 : S.elemW (G i) * (S.polyX (X - Polynomial.C (a i)))⁻¹ = 0
  · rw [h0, map_zero, HahnSeries.order_zero]; omega
  obtain ⟨hw0, hd0⟩ := mul_ne_zero_iff.mp h0
  rw [order_hom_mul φ hw0 hd0, order_hom_inv, ← hφ, ← hφ,
    S.ordInf_polyX hcop _ (X_sub_C_ne_zero _), natDegree_X_sub_C]
  have := S.elemW_ordInf (K := K) hcop (G i) (H + S.n) (hG i) hw0
  push_cast at this ⊢
  omega

/-- The candidate logarithm `W(x, y) / D(x)`. -/
noncomputable def logW (W : C[X][X]) (D : C[X]) : C⟮S.x⟯⟮S.y⟯ := S.elemW W * (S.polyX D)⁻¹

/-- `∏ᵢ (x − aᵢ)^{eᵢ}`. -/
noncomputable def denX {m : ℕ} (a : Fin m → C) (e : Fin m → ℕ) : C[X] :=
  ∏ i, (X - Polynomial.C (a i)) ^ e i

lemma denX_ne_zero {m : ℕ} (a : Fin m → C) (e : Fin m → ℕ) : denX a e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)

open Classical in
lemma ordAt_denX_nb {m : ℕ} (a : Fin m → C) (e : Fin m → ℕ) (α β : K) (hβ : β ≠ 0)
    (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K (S.polyX (denX a e)) α β = ∑ i, if α = algebraMap C K (a i) then (e i : ℤ) else 0 := by
  rw [denX, S.ordAt_polyX_prod _ _ _ _ _ hv]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [S.ordAt_X_sub _ _ _ hv, if_neg hβ]
  split_ifs <;> simp

lemma ordAt_denX_br {m : ℕ} (a : Fin m → C) (e : Fin m → ℕ) (ha : ∀ i, S.p.eval (a i) ≠ 0)
    (e' : K) (he : (S.p.map (algebraMap C K)).eval e' = 0) :
    S.ordAt K (S.polyX (denX a e)) e' 0 = 0 := by
  have hv : (0 : K) ^ S.n = (S.p.map (algebraMap C K)).eval e' := by rw [he, zero_pow S.hn.ne']
  rw [denX, S.ordAt_polyX_prod _ _ _ _ _ hv]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hne : e' ≠ algebraMap C K (a i) := by
    rintro rfl
    apply ha i
    rw [eval_map, eval₂_hom] at he
    exact (map_eq_zero_iff _ (algebraMap C K).injective).mp he
  rw [S.ordAt_X_sub _ _ _ hv, if_neg hne, mul_zero]

section Diff

variable [CharZero L] [Differential C] [Differential L] [DifferentialAlgebra C L]

open Classical in
/-- **The logarithmic part of the concrete integrand.** If `h = B + ∑ Gᵢ/(x − aᵢ)` is
elementary-integrable and the candidates `wⱼ = Wⱼ/Dⱼ` (with `div Wⱼ = μⱼ` at the finite points)
account for all residues, then `h − ∑ cⱼ wⱼ′/wⱼ = (elemW V)′` with `n a + d i ≤ H + n` on the
support of `V`. -/
theorem log_concrete (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (hcop : Nat.Coprime S.n S.p.natDegree) {m : ℕ} (B B₁ : C[X][X]) (a : Fin m → C)
    (G : Fin m → C[X][X]) (ha : ∀ i, S.p.eval (a i) ≠ 0) (H : ℕ)
    (hB : ∀ i c, (B.coeff i).coeff c ≠ 0 → i < S.n ∧ S.n * c + S.p.natDegree * i ≤ H)
    (hB₁0 : B₁.coeff 0 = 0) (hB₁ : ∀ i c, (B₁.coeff i).coeff c ≠ 0 →
      i < S.n ∧ S.n * c + S.p.natDegree * i ≤ H + S.n * S.p.natDegree)
    (hG : ∀ k i c, ((G k).coeff i).coeff c ≠ 0 → i < S.n ∧ S.n * c + S.p.natDegree * i ≤ H + S.n)
    {J : ℕ} (c : Fin J → C) (W : Fin J → C[X][X]) (hW0 : ∀ j, S.elemW (W j) ≠ 0)
    (e : Fin J → Fin m → ℕ) (μ : Fin J → K → K → ℤ)
    (hμ : ∀ j (α β : K), β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K (S.elemW (W j)) α β = μ j α β)
    (hμbr : ∀ j (e' : K), (S.p.map (algebraMap C K)).eval e' = 0 →
      S.ordAt K (S.elemW (W j)) e' 0 = 0)
    (hmatch : ∀ α β : K, β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (∑ i, if α = algebraMap C K (a i) then
        Sup.evalW ((G i).map (mapRingHom (algebraMap C K))) α β else 0) =
      ∑ j, algebraMap C K (c j) * (((μ j α β - ∑ i, if α = algebraMap C K (a i) then
        (e j i : ℤ) else 0 : ℤ)) : K))
    (v0 : L) (hv0 : v0 ∈ C⟮S.x⟯⟮S.y⟯) {I : Type*} (sI : Finset I) (d u : I → L)
    (hd : ∀ i ∈ sI, (d i)′ = 0) (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : (S.hInt B B₁ a G : L) = v0′ + ∑ i ∈ sI, d i * logDeriv (u i)) :
    ∃ V : C[X][X], (∀ i c, (V.coeff i).coeff c ≠ 0 →
        i < S.n ∧ S.n * c + S.p.natDegree * i ≤ H + S.n) ∧
      (S.hInt B B₁ a G : L) - ∑ j, algebraMap C L (c j) *
        logDeriv ((S.logW (W j) (denX a (e j)) : C⟮S.x⟯⟮S.y⟯) : L) =
        ((S.elemW V : C⟮S.x⟯⟮S.y⟯) : L)′ := by
  set wT : Fin J → C⟮S.x⟯⟮S.y⟯ := fun j ↦ S.logW (W j) (denX a (e j))
  have hD0 : ∀ j, S.polyX (denX a (e j)) ≠ 0 := fun j ↦ S.polyX_ne_zero (denX_ne_zero a (e j))
  have hwT0 : ∀ j, wT j ≠ 0 := fun j ↦ mul_ne_zero (hW0 j) (inv_ne_zero (hD0 j))
  have hordw : ∀ j (α β : K), β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K (wT j) α β =
        S.ordAt K (S.elemW (W j)) α β - S.ordAt K (S.polyX (denX a (e j))) α β := by
    intro j α β hv
    simp only [wT, logW]
    rw [S.ordAt_mul hv (hW0 j) (inv_ne_zero (hD0 j)), S.ordAt_inv hv]
    ring
  have hGd : ∀ i j, S.n ≤ j → (G i).coeff j = 0 := by
    intro i j hj
    by_contra h0
    obtain ⟨c', hc'⟩ : ∃ c', ((G i).coeff j).coeff c' ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (hG i j c' hc').1
    omega
  obtain ⟨V, hVs, hV⟩ := S.log_exact (K := K) hC hx hconst hcop _ (S.hInt B B₁ a G).2 H
    (fun α β hβ hv ↦ S.ordAt_hInt_nb B B₁ a G α β hβ hv)
    (fun e' he ↦ le_trans (by omega) (S.ordAt_hInt_br B B₁ a G hB₁0 ha e' he))
    (S.ordInf_hInt hcop B B₁ a G H hB hB₁ hG) Finset.univ c (fun j ↦ (wT j : L)) (fun j ↦ (wT j).2)
    (fun j h0 ↦ hwT0 j (Subtype.ext h0))
    (fun α β hβ hv ↦ by
      rw [S.res_hInt_nb B B₁ a G hGd α β hβ hv, hmatch α β hβ hv]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [show (⟨(wT j : L), (wT j).2⟩ : C⟮S.x⟯⟮S.y⟯) = wT j from rfl, hordw j α β hv,
        hμ j α β hβ hv, S.ordAt_denX_nb a (e j) α β hβ hv])
    (fun e' γ he hγ hγp ↦ by
      rw [S.res_hInt_br B B₁ a G hB₁0 ha e' γ he hγ hγp]
      have hv : (0 : K) ^ S.n = (S.p.map (algebraMap C K)).eval e' := by
        rw [he, zero_pow S.hn.ne']
      symm
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [show (⟨(wT j : L), (wT j).2⟩ : C⟮S.x⟯⟮S.y⟯) = wT j from rfl, hordw j e' 0 hv,
        hμbr j e' he, S.ordAt_denX_br a (e j) ha e' he]
      simp)
    v0 hv0 sI d u hd hu heq
  exact ⟨V, hVs, hV⟩

end Diff

end Differential.SuperData
