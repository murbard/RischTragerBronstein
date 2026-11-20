import RischTragerBronstein.Algebraic.SupLog

/-!
# From principal divisors to `ψ`-form principality

`principalMulN_of_isPrincipalS`: if `m Γ − (m deg Γ)∞` is principal (as a divisor over the algebraic
closure) and `Γ` is supported on `C`-rational points, then `PrincipalMulN` holds over `C`.
-/

open Polynomial IntermediateField

namespace Differential.SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

open Classical in
/-- **Principal divisors in `ψ`-form.** -/
theorem principalMulN_of_isPrincipalS (hcop : Nat.Coprime S.n S.p.natDegree) {r : ℕ}
    (α β : Fin r → C) (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q))
    (hβ : ∀ q, β q ≠ 0) (hβf : ∀ q, β q ^ S.n = S.p.eval (α q)) (Γ : K × K → ℕ)
    (hΓ : ∀ Q : K × K, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 →
      Γ Q = ∑ q, if Q = (algebraMap C K (α q), algebraMap C K (β q)) then mq q else 0)
    (m : ℕ) (h : S.IsPrincipalS K Γ m) :
    Sup.PrincipalMulN S.p S.n S.p.natDegree α β mq m := by
  set ι := algebraMap C K with hι_def
  have hιi : Function.Injective ι := ι.injective
  obtain ⟨w, hw0, hint, hord⟩ := h
  set pt : Fin r → K × K := fun q ↦ (ι (α q), ι (β q)) with hpt_def
  have hptinj : Function.Injective pt := fun q q' h ↦
    hP (Prod.ext (hιi (Prod.ext_iff.mp h).1) (hιi (Prod.ext_iff.mp h).2))
  have hpv : ∀ q, (pt q).2 ^ S.n = (S.p.map ι).eval (pt q).1 := fun q ↦ by
    simp only [pt]; rw [← map_pow, hβf, eval_map, eval₂_hom]
  have hΓq : ∀ q, Γ (pt q) = mq q := fun q ↦ by
    rw [hΓ _ (hpv q), Finset.sum_eq_single q (fun q' _ hq' ↦ if_neg fun h ↦ hq' (hptinj h).symm)
      (fun h ↦ absurd (Finset.mem_univ q) h), if_pos rfl]
  set T : Finset (K × K) := Finset.univ.image pt
  have hT : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map ι).eval Q.1 := fun Q hQ ↦ by
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hQ; exact hpv q
  have hdeg := S.degree_eq' (K := K) hcop w hw0 hint T hT (fun a b hv hn ↦ by
    rw [hord (a, b) hv, hΓ _ hv, Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦
      hn (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, h.symm⟩)]
    simp)
  rw [Finset.sum_image fun q _ q' _ h ↦ hptinj h] at hdeg
  simp only [fun q ↦ hord (pt q) (hpv q), hΓq] at hdeg
  obtain ⟨W, hW, hW0, hWs⟩ := S.elem_repr (K := K) hcop w hw0 hint (m * ∑ q, mq q) (by
    have : -S.ordInf K w = ((m * ∑ q, mq q : ℕ) : ℤ) := by
      rw [← hdeg]; push_cast; rw [Finset.mul_sum]
    omega)
  have hWW : ∀ i, S.n ≤ i → W.coeff i = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨a, ha⟩ : ∃ a, (W.coeff i).coeff a ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (hWs i a ha).1
    omega
  refine ⟨W, hW0, hWs, fun q ↦ ?_⟩
  have hβK : ι (β q) ≠ 0 := (map_ne_zero_iff _ hιi).mpr (hβ q)
  have hle : ((m * mq q : ℕ) : ℤ) ≤ S.ordAt K (S.elemW W) (ι (α q)) (ι (β q)) := by
    rw [hW]
    have := hord (pt q) (hpv q)
    rw [hΓq] at this
    simp only [pt] at this
    rw [this]; push_cast; rfl
  have hv := (S.le_ordAt_iff_vanish W hWW (by rw [hW]; exact hw0) _ _ hβK (hpv q) _).mp hle
  have hnC : (S.n : C) ≠ 0 := by exact_mod_cast S.hn.ne'
  have hu : IsUnit ((S.n : C) * β q ^ (S.n - 1)) :=
    (mul_ne_zero hnC (pow_ne_zero _ (hβ q))).isUnit
  obtain ⟨V, hV⟩ := Sup.exists_branchN S.p S.hn hu (hβf q) (m * mq q)
  exact Sup.vanishAtN_of_map ι hιi S.hn (hV.mono (Nat.le_succ _))
    (by have := hu.map ι; rwa [map_mul, map_pow, map_natCast] at this) hv

section Rem

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

omit [CharZero K] in
lemma _root_.LaurentSeries.order_add_ge {t : ℤ} (ht : t ≤ 0) (F G : LaurentSeries K)
    (hF : t ≤ F.order) (hG : t ≤ G.order) : t ≤ (F + G).order := by
  by_cases h : F + G = 0
  · rw [h, HahnSeries.order_zero]; exact ht
  · exact le_trans (le_min hF hG) (HahnSeries.min_order_le_order_add h)

omit [CharZero K] in
/-- Lower bound for the order of `a − ∑ kⱼ W'ⱼ / Wⱼ`. -/
lemma order_sub_sum_ge {M : Type*} [Field M] (φ : M →+* LaurentSeries K) {t : ℤ} (ht : t ≤ 0)
    (a : M) (ha : t ≤ (φ a).order) {J : Type*} (s : Finset J) (k W W' : J → M)
    (hk : ∀ j ∈ s, (φ (k j)).order = 0)
    (hW : ∀ j ∈ s, W' j ≠ 0 → (φ (W j)).order + t ≤ (φ (W' j)).order) :
    t ≤ (φ (a - ∑ j ∈ s, k j * (W' j / W j))).order := by
  rw [sub_eq_add_neg, map_add]
  refine LaurentSeries.order_add_ge ht _ _ ha ?_
  rw [map_neg, HahnSeries.order_neg, map_sum]
  refine Finset.sum_induction _ (fun F : LaurentSeries K ↦ t ≤ F.order)
    (fun F G hF hG ↦ LaurentSeries.order_add_ge ht F G hF hG)
    (by rw [HahnSeries.order_zero]; exact ht) fun j hj ↦ ?_
  by_cases h0 : k j * (W' j / W j) = 0
  · rw [h0, map_zero, HahnSeries.order_zero]; exact ht
  obtain ⟨hk0, hd0⟩ := mul_ne_zero_iff.mp h0
  rw [div_eq_mul_inv] at hd0 ⊢
  obtain ⟨hW'0, hWi⟩ := mul_ne_zero_iff.mp hd0
  rw [order_hom_mul φ hk0 hd0, order_hom_mul φ hW'0 hWi, order_hom_inv, hk j hj]
  have := hW j hj hW'0
  omega

omit [CharZero L] [Differential C] [Differential L] [DifferentialAlgebra C L] [CharZero K] in
lemma ordAt_cst (c : C) (hc : c ≠ 0) (α β : K)
    (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) : S.ordAt K (S.cst c) α β = 0 := by
  rw [S.cst_eq_polyX, S.ordAt_polyX _ (Polynomial.C_ne_zero.mpr hc) α β hv, Polynomial.map_C,
    rootMultiplicity_C]
  simp

omit [CharZero L] [Differential C] [Differential L] [DifferentialAlgebra C L] [CharZero K] in
lemma ordInf_cst (hcop : Nat.Coprime S.n S.p.natDegree) (c : C) (hc : c ≠ 0) :
    S.ordInf K (S.cst c) = 0 := by
  rw [S.cst_eq_polyX, S.ordInf_polyX hcop _ (Polynomial.C_ne_zero.mpr hc), natDegree_C]
  simp

omit [CharZero K] in
lemma res_sub' (F G : LaurentSeries K) :
    LaurentSeries.res (F - G) = LaurentSeries.res F - LaurentSeries.res G := by
  simp [LaurentSeries.res]

open Classical in
/-- **The logarithmic remainder is exact.** Let `h` be elementary-integrable (a Liouville form),
with at most simple poles at ordinary points, poles of order `≤ n` at branch points and
`ord∞ h ≥ −H`. If `∑ cⱼ log wⱼ` has the same residues as `h` everywhere, then
`h − ∑ cⱼ wⱼ′/wⱼ = (elemW V)′` with `n a + d i ≤ H + n` on the support of `V`. -/
theorem log_exact (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (hcop : Nat.Coprime S.n S.p.natDegree) (h : L) (hh : h ∈ C⟮S.x⟯⟮S.y⟯) (H : ℕ)
    (hnb : ∀ α β : K, β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      -1 ≤ S.ordAt K ⟨h, hh⟩ α β)
    (hbr : ∀ e : K, (S.p.map (algebraMap C K)).eval e = 0 → -(S.n : ℤ) ≤ S.ordAt K ⟨h, hh⟩ e 0)
    (hinf : -(H : ℤ) ≤ S.ordInf K ⟨h, hh⟩)
    {J : Type*} (sJ : Finset J) (c : J → C) (w : J → L) (hw : ∀ j, w j ∈ C⟮S.x⟯⟮S.y⟯)
    (hw0 : ∀ j, w j ≠ 0)
    (hresnb : ∀ (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α),
      LaurentSeries.res (S.embXY α β hβ hβp ⟨h, hh⟩) =
        ∑ j ∈ sJ, algebraMap C K (c j) * (S.ordAt K ⟨w j, hw j⟩ α β : K))
    (hresbr : ∀ (e γ : K) (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
      (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e),
      LaurentSeries.res (S.embB e γ he hγ hγp ⟨h, hh⟩ * HahnSeries.single ((S.n : ℤ) - 1)
        (S.n : K)) = ∑ j ∈ sJ, algebraMap C K (c j) * (S.ordAt K ⟨w j, hw j⟩ e 0 : K))
    (v0 : L) (hv0 : v0 ∈ C⟮S.x⟯⟮S.y⟯) {I : Type*} (sI : Finset I) (d u : I → L)
    (hd : ∀ i ∈ sI, (d i)′ = 0) (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : h = v0′ + ∑ i ∈ sI, d i * logDeriv (u i)) :
    ∃ V : C[X][X], (∀ i a, (V.coeff i).coeff a ≠ 0 →
        i < S.n ∧ S.n * a + S.p.natDegree * i ≤ H + S.n) ∧
      h - ∑ j ∈ sJ, algebraMap C L (c j) * logDeriv (w j) = ((S.elemW V : C⟮S.x⟯⟮S.y⟯) : L)′ := by
  set T := C⟮S.x⟯⟮S.y⟯
  have hdc := S.derivClosedXY hC hx
  set W : J → T := fun j ↦ ⟨w j, hw j⟩
  set W' : J → T := fun j ↦ ⟨(w j)′, hdc _ (hw j)⟩
  set gT : T := ∑ j ∈ sJ, S.cst (c j) * (W' j / W j)
  set ρT : T := ⟨h, hh⟩ - gT
  have hg : ((gT : T) : L) = ∑ j ∈ sJ, algebraMap C L (c j) * logDeriv (w j) := by
    simp [gT, W, W', cst, logDeriv]
  have hρ : ((ρT : T) : L) = h - ∑ j ∈ sJ, algebraMap C L (c j) * logDeriv (w j) := by
    rw [← hg]; rfl
  -- residues of `∑ cⱼ log wⱼ`
  have hgl : ((gT : T) : L) = (0 : L)′ + ∑ j ∈ sJ, algebraMap C L (c j) * ((w j)′ / w j) := by
    rw [hg, map_zero, zero_add]; rfl
  have hnb0 : ∀ (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α),
      LaurentSeries.res (S.embXY α β hβ hβp ⟨_, ρT.2⟩) = 0 := by
    intro α β hβ hβp
    have h1 := S.res_liouville hC hx α β hβ hβp sJ c w hw hw0 0 _ (zero_mem _) gT.2 hgl
    have e : (⟨_, ρT.2⟩ : T) = ⟨h, hh⟩ - ⟨_, gT.2⟩ := rfl
    rw [e, map_sub, res_sub', hresnb, h1]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [S.ordAt_nb _ α β hβ hβp]
  have hbr0 : ∀ (e γ : K) (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
      (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e),
      LaurentSeries.res (S.embB e γ he hγ hγp ⟨_, ρT.2⟩ *
        HahnSeries.single ((S.n : ℤ) - 1) (S.n : K)) = 0 := by
    intro e γ he hγ hγp
    have h1 := S.res_liouville_branch hC hx e γ he hγ hγp sJ c w hw hw0 0 _ (zero_mem _) gT.2 hgl
    have e' : (⟨_, ρT.2⟩ : T) = ⟨h, hh⟩ - ⟨_, gT.2⟩ := rfl
    rw [e', map_sub, sub_mul, res_sub', hresbr, h1]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [S.ordAt_br _ e γ he hγ hγp]
  -- the second-kind theorem
  have hρv : ((ρT : T) : L) = v0′ := by
    refine S.super_second_kind K hC hx hconst hcop _ v0 ρT.2 hv0 (sI.disjSum sJ)
      (Sum.elim d fun j ↦ -algebraMap C L (c j)) (Sum.elim u w) ?_ ?_ ?_ hnb0 hbr0
    · intro i hi
      rcases i with i | j
      · exact hd i (Finset.inl_mem_disjSum.mp hi)
      · show (-(algebraMap C L (c j)))′ = 0
        rw [map_neg, deriv_algebraMap, hC, map_zero, neg_zero]
    · intro i hi
      rcases i with i | j
      · exact hu i (Finset.inl_mem_disjSum.mp hi)
      · exact ⟨hw0 j, hw j⟩
    · rw [Finset.sum_disjSum, hρ, heq]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
      ring
  -- orders of the remainder
  have hvT : (⟨v0′, hdc v0 hv0⟩ : T) = ρT := Subtype.ext hρv.symm
  have hW : ∀ j, W j ≠ 0 := fun j h0 ↦ hw0 j (congrArg Subtype.val h0)
  have hW' : ∀ j, W' j ≠ 0 → (w j)′ ≠ 0 := fun j h0 h1 ↦ h0 (Subtype.ext h1)
  have hcst : ∀ (φ : T →+* LaurentSeries K), (∀ c : C, c ≠ 0 → (φ (S.cst c)).order = 0) →
      ∀ j ∈ sJ, (φ (S.cst (c j))).order = 0 := fun φ h0 j _ ↦ by
    by_cases hc : c j = 0
    · have : S.cst (c j) = 0 := Subtype.ext (by simp [cst, hc])
      rw [this, map_zero, HahnSeries.order_zero]
    · exact h0 _ hc
  obtain ⟨V, hV, hVs⟩ := S.exact_repr (K := K) hC hx hcop v0 hv0 H
    (fun α β hβ hv ↦ by
      rw [hvT]
      obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hv
      rw [hφ]
      refine order_sub_sum_ge φ (by norm_num) _ (by rw [← hφ]; exact hnb α β hβ hv) sJ _ W W'
        (hcst φ fun c hc ↦ by rw [← hφ]; exact S.ordAt_cst c hc α β hv) fun j _ hj ↦ ?_
      rw [← hφ, ← hφ]
      have := S.ordAt_deriv_ge_nb (K := K) hC hx α β hβ hv (w j) (hw j) (hW' j hj)
      simp only [W, W']; omega)
    (fun e he ↦ by
      have hv : (0 : K) ^ S.n = (S.p.map (algebraMap C K)).eval e := by
        rw [he, zero_pow S.hn.ne']
      rw [hvT]
      obtain ⟨φ, hφ⟩ := S.ordAt_hom e 0 hv
      rw [hφ]
      refine order_sub_sum_ge φ (by omega) _ (by rw [← hφ]; exact hbr e he) sJ _ W W'
        (hcst φ fun c hc ↦ by rw [← hφ]; exact S.ordAt_cst c hc e 0 hv) fun j _ hj ↦ ?_
      rw [← hφ, ← hφ]
      have := S.ordAt_deriv_ge_br (K := K) hC hx e he (w j) (hw j) (hW' j hj)
      simp only [W, W']; omega)
    (by
      rw [hvT]
      obtain ⟨φ, hφ⟩ := S.ordInf_hom (K := K) hcop
      rw [hφ]
      refine order_sub_sum_ge φ (by omega) _ (by rw [← hφ]; exact hinf) sJ _ W W'
        (hcst φ fun c hc ↦ by rw [← hφ]; exact S.ordInf_cst hcop c hc) fun j _ hj ↦ ?_
      rw [← hφ, ← hφ]
      have := S.ordInf_deriv_ge (K := K) hC hx hcop (w j) (hw j) (hW' j hj)
      simp only [W, W']; omega)
  refine ⟨V, hVs, ?_⟩
  rw [← hρ, hρv, hV]

end Rem

end Differential.SuperData
