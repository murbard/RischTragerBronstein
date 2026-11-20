import RischTragerBronstein.Algebraic.SupBivar

/-!
# The logarithmic part on superelliptic curves

* `ordInf_deriv`: at infinity (`x = s⁻ⁿ`), `ord (w′) = ord w + n` when `ord w ≠ 0`.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

/-- **The order of a derivative at infinity.** -/
theorem ordInf_deriv (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hcop : Nat.Coprime S.n S.p.natDegree) (w : L) (hw : w ∈ C⟮S.x⟯⟮S.y⟯) (hw0 : w ≠ 0)
    (h0 : S.ordInf K ⟨w, hw⟩ ≠ 0) :
    S.ordInf K ⟨w′, S.derivClosedXY hC hx w hw⟩ = S.ordInf K ⟨w, hw⟩ + S.n := by
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  have hX : LaurentSeries.derivation (single (-(S.n : ℤ)) (1 : K)) ≠ 0 := by
    rw [derivation_infX]
    exact HahnSeries.single_ne_zero (neg_ne_zero.mpr (by exact_mod_cast S.hn.ne'))
  rw [S.ordInf_eq hcop _ lam hlam hlp, S.ordInf_eq hcop _ lam hlam hlp] at *
  unfold embI at *
  rw [S.embG_derivG _ hX (infSub S.n) (infSub_injective S.n S.hn)
    (fun P ↦ by rw [infSub_eq_subst]) hC hx _ _ w hw, deltaX_apply, derivation_infX]
  set F := S.embG (infSub S.n) (infSub_injective S.n S.hn) (S.infY lam hlam hlp)
    (S.infY_pow lam hlam hlp) ⟨w, hw⟩ with hF
  have hF0 : F ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr
    (fun h ↦ hw0 (congrArg Subtype.val h))
  have hn0 : (S.n : K) ≠ 0 := by exact_mod_cast S.hn.ne'
  set A : LaurentSeries K := single (-(S.n : ℤ) - 1) (-(S.n : K)) with hA
  have hA0 : A ≠ 0 := HahnSeries.single_ne_zero (neg_ne_zero.mpr hn0)
  have hAo : A.order = -(S.n : ℤ) - 1 := HahnSeries.order_single (neg_ne_zero.mpr hn0)
  have hAi : A⁻¹.order = (S.n : ℤ) + 1 := by
    have := HahnSeries.order_mul hA0 (inv_ne_zero hA0)
    rw [mul_inv_cancel₀ hA0, HahnSeries.order_one, hAo] at this
    linarith
  have hc : (LaurentSeries.derivation F).coeff (F.order - 1) ≠ 0 := by
    rw [LaurentSeries.derivation_apply, LaurentSeries.derivative_coeff, sub_add_cancel]
    exact mul_ne_zero (by exact_mod_cast h0) ((not_congr HahnSeries.coeff_order_eq_zero).mpr hF0)
  have hD0 : LaurentSeries.derivation F ≠ 0 := fun h ↦ hc (by rw [h]; rfl)
  rw [HahnSeries.order_mul (inv_ne_zero hA0) hD0, hAi, LaurentSeries.derivation_apply,
    LaurentSeries.order_derivative F hF0 h0]
  ring

omit [CharZero L] [Differential C] [Differential L] [DifferentialAlgebra C L] [CharZero K] in
/-- A function with `ord ≥ 0` at an ordinary point has no residue there. -/
lemma res_embXY_of_ordAt_nonneg (w : C⟮S.x⟯⟮S.y⟯) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) (h : 0 ≤ S.ordAt K w α β) :
    LaurentSeries.res (S.embXY α β hβ hβp w) = 0 := by
  by_cases hw : w = 0
  · rw [hw, map_zero]; rfl
  rw [S.ordAt_nb _ α β hβ hβp] at h
  unfold LaurentSeries.res
  exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)

omit [CharZero L] [Differential C] [Differential L] [DifferentialAlgebra C L] [CharZero K] in
/-- The value of `∑ Wᵢ(x) yⁱ` at an ordinary point is the constant term of its expansion. -/
lemma coeff_zero_embXY_elemW (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) (W : C[X][X])
    (hW : ∀ i, S.n ≤ i → W.coeff i = 0) :
    (S.embXY α β hβ hβp (S.elemW W)).coeff 0 =
      Sup.evalW (W.map (mapRingHom (algebraMap C K))) α β := by
  rw [S.embXY_elemW, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff,
    Sup.jetPS, map_sum]
  have hn : (W.map (mapRingHom (algebraMap C K))).natDegree < S.n :=
    S.natDegree_lt_of_coeff (K := K) W hW
  rw [Sup.evalW, eval_eq_sum_range' (n := S.n) (lt_of_le_of_lt natDegree_map_le hn)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, branchY_const, Polynomial.coeff_map]
  congr 1
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    coeff_zero_eq_eval_zero, eval_comp]
  simp [eval_map, aeval_def]

omit [CharZero L] [Differential C] [Differential L] [DifferentialAlgebra C L] [CharZero K] in
/-- **The residue of `W(x, y)/(x − a)`** at a point `(a, β)`: the value `W(a, β)`. -/
lemma res_elemW_div (W : C[X][X]) (hW : ∀ i, S.n ≤ i → W.coeff i = 0) (a : C) (β : K)
    (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval (algebraMap C K a)) :
    LaurentSeries.res (S.embXY (algebraMap C K a) β hβ hβp
      (S.elemW W * (S.polyX (X - Polynomial.C a))⁻¹)) =
      Sup.evalW (W.map (mapRingHom (algebraMap C K))) (algebraMap C K a) β := by
  have hlin : S.embXY (algebraMap C K a) β hβ hβp (S.polyX (X - Polynomial.C a)) =
      single (1 : ℤ) (1 : K) := by
    rw [S.embXY_polyX]
    have : ((X - Polynomial.C a).map (algebraMap C K)).comp (X + Polynomial.C (algebraMap C K a)) =
        (X : K[X]) := by simp
    rw [this]
    simp
  rw [map_mul, map_inv₀, hlin, show (single (1 : ℤ) (1 : K))⁻¹ = single (-1 : ℤ) (1 : K) from by
    rw [inv_eq_of_mul_eq_one_right]; rw [HahnSeries.single_mul_single]; simp]
  unfold LaurentSeries.res
  have h := HahnSeries.coeff_mul_single_add (x := S.embXY (algebraMap C K a) β hβ hβp (S.elemW W))
    (r := (1 : K)) (a := (0 : ℤ)) (b := (-1 : ℤ))
  rw [zero_add, mul_one] at h
  rw [h, S.coeff_zero_embXY_elemW _ _ hβ hβp W hW]

/-- Differentiation lowers the order by at most one. -/
theorem _root_.LaurentSeries.order_derivative_ge (F : LaurentSeries K)
    (hF' : LaurentSeries.derivative K F ≠ 0) :
    F.order - 1 ≤ (LaurentSeries.derivative K F).order := by
  by_contra hlt
  push_neg at hlt
  have hc := (not_congr HahnSeries.coeff_order_eq_zero).mpr hF'
  rw [LaurentSeries.derivative_coeff] at hc
  have h0 : F.coeff ((LaurentSeries.derivative K F).order + 1) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_order (by omega)
  rw [h0, mul_zero] at hc
  exact hc rfl

/-- **Orders of derivatives at ordinary points**: `ord (w′) ≥ ord w − 1`. -/
theorem ordAt_deriv_ge_nb (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (α β : K) (hβ : β ≠ 0)
    (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) (w : L) (hw : w ∈ C⟮S.x⟯⟮S.y⟯)
    (hw' : w′ ≠ 0) :
    S.ordAt K ⟨w, hw⟩ α β - 1 ≤ S.ordAt K ⟨w′, S.derivClosedXY hC hx w hw⟩ α β := by
  rw [S.ordAt_nb _ α β hβ hv, S.ordAt_nb _ α β hβ hv, S.embXY_deriv hC hx α β hβ hv w hw,
    LaurentSeries.derivation_apply]
  refine LaurentSeries.order_derivative_ge _ fun h ↦ hw' ?_
  have := S.embXY_deriv hC hx α β hβ hv w hw
  rw [LaurentSeries.derivation_apply, h] at this
  exact congrArg Subtype.val ((map_eq_zero_iff _ (RingHom.injective _)).mp this)

/-- **Orders of derivatives at branch points**: `ord (w′) ≥ ord w − n`. -/
theorem ordAt_deriv_ge_br (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (e : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) (w : L) (hw : w ∈ C⟮S.x⟯⟮S.y⟯)
    (hw' : w′ ≠ 0) :
    S.ordAt K ⟨w, hw⟩ e 0 - S.n ≤ S.ordAt K ⟨w′, S.derivClosedXY hC hx w hw⟩ e 0 := by
  obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma e he
  rw [S.ordAt_br _ e γ he hγ hγp, S.ordAt_br _ e γ he hγ hγp]
  set Xh : LaurentSeries K := HahnSeries.C e + single (S.n : ℤ) 1
  have hX : LaurentSeries.derivation Xh ≠ 0 := by
    rw [derivation_branchX S.n S.hn e]
    exact HahnSeries.single_ne_zero (by exact_mod_cast S.hn.ne')
  have hd := S.embG_derivG Xh hX (branchSub S.n e) (branchSub_injective S.n S.hn e)
    (fun P ↦ by rw [branchSub_eq_subst]) hC hx (S.branchYe e γ hγ hγp)
    (S.branchYe_pow e γ he hγ hγp) w hw
  unfold embB
  rw [hd, deltaX_apply]
  have hne : (LaurentSeries.derivation Xh)⁻¹ * LaurentSeries.derivation
      (S.embG (branchSub S.n e) (branchSub_injective S.n S.hn e) (S.branchYe e γ hγ hγp)
        (S.branchYe_pow e γ he hγ hγp) ⟨w, hw⟩) ≠ 0 := by
    rw [← deltaX_apply, ← hd]
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr (fun h ↦ hw' (congrArg Subtype.val h))
  have hD := right_ne_zero_of_mul hne
  rw [HahnSeries.order_mul (inv_ne_zero hX) hD, order_inv' _ hX,
    derivation_branchX S.n S.hn e, HahnSeries.order_single (by exact_mod_cast S.hn.ne'),
    LaurentSeries.derivation_apply]
  have := LaurentSeries.order_derivative_ge _ (by rwa [LaurentSeries.derivation_apply] at hD)
  linarith

/-- **Orders of derivatives at infinity**: `ord (w′) ≥ ord w + n`. -/
theorem ordInf_deriv_ge (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hcop : Nat.Coprime S.n S.p.natDegree) (w : L) (hw : w ∈ C⟮S.x⟯⟮S.y⟯) (hw' : w′ ≠ 0) :
    S.ordInf K ⟨w, hw⟩ + S.n ≤ S.ordInf K ⟨w′, S.derivClosedXY hC hx w hw⟩ := by
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  have hX : LaurentSeries.derivation (single (-(S.n : ℤ)) (1 : K)) ≠ 0 := by
    rw [derivation_infX]
    exact HahnSeries.single_ne_zero (neg_ne_zero.mpr (by exact_mod_cast S.hn.ne'))
  rw [S.ordInf_eq hcop _ lam hlam hlp, S.ordInf_eq hcop _ lam hlam hlp]
  unfold embI
  have hd := S.embG_derivG _ hX (infSub S.n) (infSub_injective S.n S.hn)
    (fun P ↦ by rw [infSub_eq_subst]) hC hx _ (S.infY_pow lam hlam hlp) w hw
  rw [hd, deltaX_apply]
  have hne : (LaurentSeries.derivation (single (-(S.n : ℤ)) (1 : K)))⁻¹ *
      LaurentSeries.derivation (S.embG (infSub S.n) (infSub_injective S.n S.hn)
        (S.infY lam hlam hlp) (S.infY_pow lam hlam hlp) ⟨w, hw⟩) ≠ 0 := by
    rw [← deltaX_apply, ← hd]
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr (fun h ↦ hw' (congrArg Subtype.val h))
  have hD := right_ne_zero_of_mul hne
  have hn0 : (S.n : K) ≠ 0 := by exact_mod_cast S.hn.ne'
  rw [HahnSeries.order_mul (inv_ne_zero hX) hD, order_inv' _ hX, derivation_infX,
    HahnSeries.order_single (neg_ne_zero.mpr hn0), LaurentSeries.derivation_apply]
  have := LaurentSeries.order_derivative_ge _ (by rwa [LaurentSeries.derivation_apply] at hD)
  linarith

/-- **An exact form with controlled poles has a controlled primitive.** If `v′` has at most simple
poles at ordinary points, poles of order `≤ n` at branch points and `ord∞ v′ ≥ −H`, then `v` is
`elemW V` with `n a + d i ≤ H + n` on the support of `V`. -/
theorem exact_repr (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hcop : Nat.Coprime S.n S.p.natDegree) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (H : ℕ)
    (hnb : ∀ α β : K, β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      -1 ≤ S.ordAt K ⟨v′, S.derivClosedXY hC hx v hv⟩ α β)
    (hbr : ∀ e : K, (S.p.map (algebraMap C K)).eval e = 0 →
      -(S.n : ℤ) ≤ S.ordAt K ⟨v′, S.derivClosedXY hC hx v hv⟩ e 0)
    (hinf : -(H : ℤ) ≤ S.ordInf K ⟨v′, S.derivClosedXY hC hx v hv⟩) :
    ∃ V : C[X][X], S.elemW V = ⟨v, hv⟩ ∧
      ∀ i a, (V.coeff i).coeff a ≠ 0 → i < S.n ∧ S.n * a + S.p.natDegree * i ≤ H + S.n := by
  by_cases hv0 : v = 0
  · refine ⟨0, ?_, fun i a h ↦ by simp at h⟩
    subst hv0
    apply Subtype.ext
    simp [elemW, polyX]
  have hint : S.IsIntegralS K ⟨v, hv⟩ := by
    intro α β hβp
    by_contra hneg; push_neg at hneg
    by_cases hβ : β = 0
    · subst hβ
      have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hβp, zero_pow S.hn.ne']
      have := S.ordAt_deriv_br (K := K) hC hx α he v hv hv0 hneg.ne
      have := hbr α he
      omega
    · have := S.ordAt_deriv_nb (K := K) hC hx α β hβ hβp v hv hv0 hneg.ne
      have := hnb α β hβ hβp
      omega
  have hinfv : -((H + S.n : ℕ) : ℤ) ≤ S.ordInf K ⟨v, hv⟩ := by
    by_cases h0 : S.ordInf K ⟨v, hv⟩ = 0
    · rw [h0]; omega
    · have := S.ordInf_deriv (K := K) hC hx hcop v hv hv0 h0
      push_cast; omega
  obtain ⟨V, hV, -, hsupp⟩ := S.elem_repr (K := K) hcop ⟨v, hv⟩ (fun h ↦ hv0 (congrArg Subtype.val h :))
    hint (H + S.n) hinfv
  exact ⟨V, hV, hsupp⟩

end SuperData

end Differential
