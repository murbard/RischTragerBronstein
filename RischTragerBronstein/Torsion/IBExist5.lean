import RischTragerBronstein.Torsion.IBExist4
import RischTragerBronstein.Torsion.LogWitExpand

/-!
# Integral bases exist (5): normalization at infinity

With pole bounds `δⱼ` above infinity (`PoleBd`), a dependence `∑ cⱼ T^{N δⱼ} wⱼ ≡ 0 mod T^N` of the
leading terms gives the reduced element `w'_{j₀} = ∑ cⱼ x^{δ_{j₀} − δⱼ} wⱼ` (`δ_{j₀}` maximal among
`cⱼ ≠ 0`), with pole order `δ_{j₀} − 1` (`stepI`). The finite invariants survive
(`finGood_stepI`, `indepAt_stepI`: the change of basis is unimodular over `C[x]`), and `δ_{j₀} = 0`
is impossible (`evXY_eq_zero_of_vanish`). Induction on `∑ δⱼ` gives **`exists_basis`**: a basis
locally integral and independent at the given points and independent at infinity, with `w₀ = 1`,
`δ₀ = 0`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Norm

variable {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]

namespace CurveData

variable {S : CurveData C L}

/-- Pole bounds above infinity. -/
def PoleBd (τ : S.InfSys) (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (δ : Fin S.F.natDegree → ℕ) :
    Prop :=
  ∀ j k, LowerBd (τ.ev k (S.fnWQ (B j) D)) (-((τ.N * δ j : ℕ) : ℤ))

/-- Independence of the leading terms above infinity. -/
def IndepInf (τ : S.InfSys) (B : Fin S.F.natDegree → C[X][X]) (D : C[X])
    (δ : Fin S.F.natDegree → ℕ) : Prop :=
  ∀ c : Fin S.F.natDegree → C,
    (∀ k, LowerBd (∑ j, HahnSeries.C (c j) * (single ((τ.N * δ j : ℕ) : ℤ) (1 : C) *
      τ.ev k (S.fnWQ (B j) D))) τ.N) → c = 0

/-- The reduced numerators at infinity. -/
noncomputable def stepI (B : Fin S.F.natDegree → C[X][X]) (c : Fin S.F.natDegree → C)
    (δ : Fin S.F.natDegree → ℕ) (j₀ : Fin S.F.natDegree) : Fin S.F.natDegree → C[X][X] := fun j ↦
  if j = j₀ then ∑ l, Polynomial.C (Polynomial.C (c l) * X ^ (δ j₀ - δ l)) * B l else B j

lemma stepI_deg {B : Fin S.F.natDegree → C[X][X]} (hB : ∀ j, (B j).natDegree < S.F.natDegree)
    (c : Fin S.F.natDegree → C) (δ : Fin S.F.natDegree → ℕ) (j₀ j : Fin S.F.natDegree) :
    (stepI B c δ j₀ j).natDegree < S.F.natDegree := by
  have hn : 0 < S.F.natDegree := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  unfold stepI
  split_ifs
  · refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := S.F.natDegree - 1)
      fun l _ ↦ ?_) (by omega)
    exact natDegree_C_mul_le _ _ |>.trans (by have := hB l; omega)
  · exact hB j

lemma det_stepI (B : Fin S.F.natDegree → C[X][X]) (c : Fin S.F.natDegree → C)
    (δ : Fin S.F.natDegree → ℕ) (j₀ : Fin S.F.natDegree) :
    (coeffMat (stepI B c δ j₀)).det = Polynomial.C (c j₀) * (coeffMat B).det := by
  classical
  have hM : coeffMat (stepI B c δ j₀) = (coeffMat B).updateCol j₀
      (fun i ↦ ∑ l, (Polynomial.C (c l) * X ^ (δ j₀ - δ l)) • coeffMat B i l) := by
    refine Matrix.ext fun i j ↦ ?_
    simp only [coeffMat, stepI, Matrix.of_apply, Matrix.updateCol_apply]
    by_cases hj : j = j₀
    · subst hj
      simp only [if_true, finset_sum_coeff, coeff_C_mul, smul_eq_mul]
    · simp only [hj, if_false]
  rw [hM, Matrix.det_updateCol_sum, Nat.sub_self, pow_zero, mul_one, smul_eq_mul]

lemma fnWQ_stepI (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (c : Fin S.F.natDegree → C)
    (δ : Fin S.F.natDegree → ℕ) (j₀ : Fin S.F.natDegree) :
    S.fnWQ (stepI B c δ j₀ j₀) D =
      ∑ l, S.polyF (Polynomial.C (c l) * X ^ (δ j₀ - δ l)) * S.fnWQ (B l) D := by
  simp only [stepI, if_true, fnWQ]
  have e1 : S.evT (∑ l, Polynomial.C (Polynomial.C (c l) * X ^ (δ j₀ - δ l)) * B l) =
      ∑ l, S.polyF (Polynomial.C (c l) * X ^ (δ j₀ - δ l)) * S.evT (B l) := by
    apply Subtype.ext
    rw [S.coe_evT, IntermediateField.coe_sum]
    simp only [IntermediateField.coe_mul, coe_polyF, S.coe_evT, evXY, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, eval_finset_sum, eval_mul, eval_C]
    rfl
  rw [e1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

lemma fnWQ_stepI_ne (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (c : Fin S.F.natDegree → C)
    (δ : Fin S.F.natDegree → ℕ) (j₀ j : Fin S.F.natDegree) (hj : j ≠ j₀) :
    S.fnWQ (stepI B c δ j₀ j) D = S.fnWQ (B j) D := by
  simp only [stepI, hj, if_false]

lemma ev_polyF_fin (σ : S.LocSys) (k : Fin S.F.natDegree) (P : C[X]) :
    LowerBd (σ.ev k (S.polyF P)) 0 := by
  rw [LocSys.ev, S.embG_polyF]; exact lowerBd_ofPS _

/-- `xᵉ ≡ aᵉ mod (x − a)` along a system above `a`. -/
lemma ev_polyF_pow_sub (σ : S.LocSys) (k : Fin S.F.natDegree) (e : ℕ) :
    LowerBd (σ.ev k (S.polyF (X ^ e)) - HahnSeries.C (σ.a ^ e)) σ.N := by
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (X : C[X]) (Polynomial.C σ.a) e
  have e1 : σ.ev k (S.polyF (X ^ e)) - HahnSeries.C (σ.a ^ e) =
      σ.ev k (S.polyF (X - Polynomial.C σ.a)) * σ.ev k (S.polyF q) := by
    rw [← ev_polyF_C σ k]
    unfold LocSys.ev
    rw [← map_sub, ← map_mul]
    congr 1
    rw [show S.polyF (X ^ e) - S.polyF (Polynomial.C (σ.a ^ e)) =
      S.polyF (X ^ e - Polynomial.C σ.a ^ e) by simp [polyF, map_sub, Polynomial.C_pow], hq]
    simp [polyF]
  rw [e1, polyF_X_sub, sub_self, map_zero, zero_add]
  simpa using (lowerBd_single (σ.N : ℤ) (1 : C)).mul (ev_polyF_fin σ k q)

lemma ev_polyF_inf (τ : S.InfSys) (k : Fin S.F.natDegree) (c : C) (e : ℕ) :
    τ.ev k (S.polyF (Polynomial.C c * X ^ e)) =
      HahnSeries.C c * single (-((τ.N * e : ℕ) : ℤ)) (1 : C) := by
  rw [InfSys.ev, S.embG_polyF, map_mul, is_C, infSub_X_pow]; rfl

lemma ev_stepI (σ : S.LocSys) (k : Fin S.F.natDegree) (B : Fin S.F.natDegree → C[X][X])
    (D : C[X]) (c : Fin S.F.natDegree → C) (δ : Fin S.F.natDegree → ℕ) (j₀ : Fin S.F.natDegree) :
    σ.ev k (S.fnWQ (stepI B c δ j₀ j₀) D) =
      ∑ l, HahnSeries.C (c l) * σ.ev k (S.polyF (X ^ (δ j₀ - δ l))) * σ.ev k (S.fnWQ (B l) D) := by
  rw [fnWQ_stepI]
  unfold LocSys.ev
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_mul, show S.polyF (Polynomial.C (c l) * X ^ (δ j₀ - δ l)) =
    S.polyF (Polynomial.C (c l)) * S.polyF (X ^ (δ j₀ - δ l)) by simp [polyF], map_mul]
  congr 2
  rw [S.embG_polyF, bs_C]; rfl

lemma regAt_stepI (σ : S.LocSys) (B : Fin S.F.natDegree → C[X][X]) (D : C[X])
    (hreg : RegAt σ B D) (c : Fin S.F.natDegree → C) (δ : Fin S.F.natDegree → ℕ)
    (j₀ : Fin S.F.natDegree) : RegAt σ (stepI B c δ j₀) D := by
  intro j k
  by_cases hj : j = j₀
  · subst hj
    rw [ev_stepI]
    refine lowerBd_sum _ _ fun l _ ↦ ?_
    exact ((((lowerBd_C (c l)).mul (ev_polyF_fin σ k _)).mul (hreg l k))).mono (by simp)
  · rw [fnWQ_stepI_ne B D c δ j₀ j hj]; exact hreg j k

/-- **Finite independence survives the reduction at infinity.** -/
lemma indepAt_stepI (σ : S.LocSys) (B : Fin S.F.natDegree → C[X][X]) (D : C[X])
    (hreg : RegAt σ B D) (hind : IndepAt σ B D) (c : Fin S.F.natDegree → C)
    (δ : Fin S.F.natDegree → ℕ) (j₀ : Fin S.F.natDegree) (hc : c j₀ ≠ 0) :
    IndepAt σ (stepI B c δ j₀) D := by
  classical
  intro d hd
  set e : Fin S.F.natDegree → ℕ := fun l ↦ δ j₀ - δ l with he
  set d' : Fin S.F.natDegree → C := fun i ↦
    (if i = j₀ then 0 else d i) + d j₀ * (c i * σ.a ^ e i) with hd'
  have hsplit : ∀ k, ∑ i, HahnSeries.C (d i) * σ.ev k (S.fnWQ (stepI B c δ j₀ i) D) =
      ∑ i, HahnSeries.C (d' i) * σ.ev k (S.fnWQ (B i) D) +
        HahnSeries.C (d j₀) * ∑ l, HahnSeries.C (c l) *
          (σ.ev k (S.polyF (X ^ e l)) - HahnSeries.C (σ.a ^ e l)) * σ.ev k (S.fnWQ (B l) D) := by
    intro k
    have h1 : ∑ i, HahnSeries.C (d i) * σ.ev k (S.fnWQ (stepI B c δ j₀ i) D) =
        ∑ i, (HahnSeries.C (if i = j₀ then 0 else d i) * σ.ev k (S.fnWQ (B i) D) +
          if i = j₀ then HahnSeries.C (d j₀) * σ.ev k (S.fnWQ (stepI B c δ j₀ j₀) D) else 0) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hi : i = j₀
      · subst hi; simp
      · simp [hi, fnWQ_stepI_ne B D c δ j₀ i hi]
    rw [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ev_stepI]
    simp only [hd', map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    rw [add_assoc]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [he, map_pow]
    ring
  have hlow : ∀ k, LowerBd (∑ i, HahnSeries.C (d' i) * σ.ev k (S.fnWQ (B i) D)) σ.N := by
    intro k
    have h2 : LowerBd (HahnSeries.C (d j₀) * ∑ l, HahnSeries.C (c l) *
        (σ.ev k (S.polyF (X ^ e l)) - HahnSeries.C (σ.a ^ e l)) * σ.ev k (S.fnWQ (B l) D)) σ.N := by
      refine ((lowerBd_C _).mul (lowerBd_sum (m := (σ.N : ℤ)) _ _ fun l _ ↦ ?_)).mono (by simp)
      exact (((lowerBd_C (c l)).mul (ev_polyF_pow_sub σ k (e l))).mul (hreg l k)).mono (by simp)
    have := (hd k).sub h2
    rwa [hsplit k, add_sub_cancel_right] at this
  have h0 := hind d' hlow
  have hj₀ : d j₀ = 0 := by
    have := congrFun h0 j₀
    simp only [hd', ↓reduceIte, zero_add, he, Nat.sub_self, pow_zero, mul_one, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_right hc
  funext i
  by_cases hi : i = j₀
  · rw [hi, hj₀]; rfl
  · have := congrFun h0 i
    simp only [hd', if_neg hi, hj₀, zero_mul, add_zero, Pi.zero_apply] at this
    exact this

lemma ev_inf_stepI (τ : S.InfSys) (k : Fin S.F.natDegree) (B : Fin S.F.natDegree → C[X][X])
    (D : C[X]) (δ : Fin S.F.natDegree → ℕ) (c : Fin S.F.natDegree → C) (j₀ : Fin S.F.natDegree)
    (hmax : ∀ l, c l ≠ 0 → δ l ≤ δ j₀) :
    τ.ev k (S.fnWQ (stepI B c δ j₀ j₀) D) = single (-((τ.N * δ j₀ : ℕ) : ℤ)) (1 : C) *
      ∑ l, HahnSeries.C (c l) * (single ((τ.N * δ l : ℕ) : ℤ) (1 : C) *
        τ.ev k (S.fnWQ (B l) D)) := by
  rw [fnWQ_stepI]
  unfold InfSys.ev
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_mul, ← InfSys.ev, ← InfSys.ev, ev_polyF_inf]
  by_cases hl : c l = 0
  · simp [hl]
  · have hle := hmax l hl
    rw [show single (-((τ.N * δ j₀ : ℕ) : ℤ)) (1 : C) * (HahnSeries.C (c l) *
        (single ((τ.N * δ l : ℕ) : ℤ) (1 : C) * τ.ev k (S.fnWQ (B l) D))) =
        HahnSeries.C (c l) * (single (-((τ.N * δ j₀ : ℕ) : ℤ)) (1 : C) *
          single ((τ.N * δ l : ℕ) : ℤ) (1 : C)) * τ.ev k (S.fnWQ (B l) D) by ring,
      single_mul_single, one_mul]
    congr 3
    push_cast [Nat.cast_sub hle]
    ring

/-- **The reduced element has a smaller pole.** -/
lemma poleBd_stepI (τ : S.InfSys) (B : Fin S.F.natDegree → C[X][X]) (D : C[X])
    (δ : Fin S.F.natDegree → ℕ) (hP : PoleBd τ B D δ) (c : Fin S.F.natDegree → C)
    (j₀ : Fin S.F.natDegree) (hmax : ∀ l, c l ≠ 0 → δ l ≤ δ j₀)
    (hdep : ∀ k, LowerBd (∑ j, HahnSeries.C (c j) * (single ((τ.N * δ j : ℕ) : ℤ) (1 : C) *
      τ.ev k (S.fnWQ (B j) D))) τ.N) :
    PoleBd τ (stepI B c δ j₀) D (Function.update δ j₀ (δ j₀ - 1)) := by
  classical
  intro j k
  by_cases hj : j = j₀
  · subst hj
    rw [Function.update_self]
    have hev := ev_inf_stepI τ k B D δ c j hmax
    rw [hev]
    have h := (lowerBd_single (-((τ.N * δ j : ℕ) : ℤ)) (1 : C)).mul (hdep k)
    refine h.mono ?_
    by_cases h0 : δ j = 0
    · rw [h0]; simp
    · push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h0)]
      ring_nf; omega
  · rw [Function.update_of_ne hj, fnWQ_stepI_ne B D c δ j₀ j hj]; exact hP j k

lemma finGood_stepI (A : List S.LocSys) (B : Fin S.F.natDegree → C[X][X]) (D : C[X])
    (hG : FinGood A B D) (c : Fin S.F.natDegree → C) (δ : Fin S.F.natDegree → ℕ)
    (j₀ : Fin S.F.natDegree) (hc : c j₀ ≠ 0) (hj₀ : (j₀ : ℕ) ≠ 0) :
    FinGood A (stepI B c δ j₀) D := by
  refine ⟨stepI_deg hG.deg c δ j₀, by rw [det_stepI]; exact mul_ne_zero (C_ne_zero.mpr hc) hG.det,
    hG.hD, fun σ hσ ↦ regAt_stepI σ B D (hG.reg σ hσ) c δ j₀, fun h ↦ ?_, fun b hb ↦ ?_, hG.split,
    hG.monic, ?_⟩
  · have hne : (⟨0, h⟩ : Fin S.F.natDegree) ≠ j₀ := fun e ↦ hj₀ (by rw [← e])
    rw [stepI, if_neg hne, hG.one h]
  · refine hG.roots b ?_
    rw [det_stepI] at hb
    simp only [IsRoot, eval_mul, eval_C] at hb ⊢
    have : eval b D * eval b (coeffMat B).det * c j₀ = 0 := by rw [← hb]; ring
    exact (mul_eq_zero.mp this).resolve_right hc
  · have hC : Polynomial.C (c j₀) ≠ 0 := Polynomial.C_ne_zero.mpr hc
    rw [det_stepI, roots_mul (mul_ne_zero hC hG.det), roots_C, zero_add, hG.detsplit,
      natDegree_mul hC hG.det, natDegree_C, zero_add]

lemma evInf_one (τ : S.InfSys) (k : Fin S.F.natDegree) (D : C[X]) (hD : D ≠ 0) :
    τ.ev k (S.fnWQ (Polynomial.C D) D) = 1 := by
  rw [InfSys.ev, S.embG_fnWQ, Polynomial.map_C, eval_C]
  exact mul_inv_cancel₀ ((map_ne_zero_iff _ (infSub_injective _ τ.hN)).mpr hD)

lemma fnWQ_sub_const (W : C[X][X]) (D : C[X]) (hD : D ≠ 0) (c : C) :
    S.fnWQ (W - Polynomial.C (Polynomial.C c * D)) D = S.fnWQ W D - S.polyF (Polynomial.C c) := by
  have hD' : aeval S.x D ≠ 0 := by
    rw [← coe_polyF]; exact fun h ↦ S.polyF_ne_zero hD (Subtype.ext h)
  apply Subtype.ext
  push_cast [S.coe_fnWQ, coe_polyF]
  rw [S.evXY_sub]
  field_simp
  simp only [evXY, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, aeval_C, Polynomial.C_mul]
  ring

lemma coeffMat_det_zero_of_col (B : Fin S.F.natDegree → C[X][X]) (j j' : Fin S.F.natDegree)
    (hjj : j ≠ j') (q : C[X]) (h : B j = Polynomial.C q * B j') : (coeffMat B).det = 0 := by
  classical
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun l ↦ if l = j then -1 else if l = j' then q else 0, fun h0 ↦ ?_, ?_⟩
  · have := congrFun h0 j
    simp at this
  · funext i
    simp only [Matrix.mulVec, dotProduct, coeffMat, Matrix.of_apply, Pi.zero_apply]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hjj, Finset.mem_univ j'⟩)]
    rw [Finset.sum_eq_zero (fun l hl ↦ by
      obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hl
      obtain ⟨h3, -⟩ := Finset.mem_erase.mp h2
      rw [if_neg h3, if_neg h1, mul_zero])]
    rw [if_pos rfl, if_neg (Ne.symm hjj), if_pos rfl, h, coeff_C_mul]
    ring

theorem exists_basis_aux (A : List S.LocSys) (hA : (A.map LocSys.a).Nodup) (τ : S.InfSys) :
    ∃ (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (δ : Fin S.F.natDegree → ℕ),
      FinGood A B D ∧ (∀ σ ∈ A, IndepAt σ B D) ∧ PoleBd τ B D δ ∧ IndepInf τ B D δ ∧
      ∀ h : 0 < S.F.natDegree, δ ⟨0, h⟩ = 0 := by
  classical
  have hn : 0 < S.F.natDegree := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  obtain ⟨B₀, D₀, hG₀, hI₀⟩ := exists_finite_basis A hA
  set δ₀ : Fin S.F.natDegree → ℕ := fun j ↦
    ∑ k, (-(τ.ev k (S.fnWQ (B₀ j) D₀)).order).toNat with hδ₀
  have hP₀ : PoleBd τ B₀ D₀ δ₀ := by
    intro j k
    refine (show LowerBd (τ.ev k (S.fnWQ (B₀ j) D₀)) (τ.ev k (S.fnWQ (B₀ j) D₀)).order from
      fun _ hk ↦ HahnSeries.coeff_eq_zero_of_lt_order hk).mono ?_
    have h1 : (-(τ.ev k (S.fnWQ (B₀ j) D₀)).order).toNat ≤ δ₀ j :=
      Finset.single_le_sum (f := fun k ↦ (-(τ.ev k (S.fnWQ (B₀ j) D₀)).order).toNat)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (-(τ.ev k (S.fnWQ (B₀ j) D₀)).order)
    have h3 : (δ₀ j : ℤ) ≤ (τ.N * δ₀ j : ℕ) := by
      exact_mod_cast Nat.le_mul_of_pos_left _ τ.hN
    omega
  have hz₀ : δ₀ ⟨0, hn⟩ = 0 := by
    simp only [hδ₀, hG₀.one hn, evInf_one τ _ D₀ hG₀.hD, HahnSeries.order_one, neg_zero,
      Int.toNat_zero, Finset.sum_const_zero]
  suffices key : ∀ m (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (δ : Fin S.F.natDegree → ℕ),
      FinGood A B D → (∀ σ ∈ A, IndepAt σ B D) → PoleBd τ B D δ → δ ⟨0, hn⟩ = 0 →
      ∑ j, δ j = m →
      ∃ (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (δ : Fin S.F.natDegree → ℕ),
        FinGood A B D ∧ (∀ σ ∈ A, IndepAt σ B D) ∧ PoleBd τ B D δ ∧ IndepInf τ B D δ ∧
        ∀ h : 0 < S.F.natDegree, δ ⟨0, h⟩ = 0 from
    key _ B₀ D₀ δ₀ hG₀ hI₀ hP₀ hz₀ rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro B D δ hG hI hP hz hm
  by_cases hall : IndepInf τ B D δ
  · exact ⟨B, D, δ, hG, hI, hP, hall, fun h ↦ hz⟩
  simp only [IndepInf, not_forall] at hall
  obtain ⟨c, hdep, hc⟩ := hall
  have hsupp : (Finset.univ.filter fun l ↦ c l ≠ 0).Nonempty := by
    by_contra h
    apply hc
    funext l
    by_contra hl
    exact h ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩⟩
  obtain ⟨j₀, hj₀s, hmax⟩ := Finset.exists_max_image _ δ hsupp
  have hcj₀ : c j₀ ≠ 0 := (Finset.mem_filter.mp hj₀s).2
  have hmax' : ∀ l, c l ≠ 0 → δ l ≤ δ j₀ := fun l hl ↦
    hmax l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
  by_cases hδ0 : δ j₀ = 0
  · -- impossible: an integral function vanishing at infinity
    exfalso
    set W := stepI B c δ j₀ j₀ with hW
    have hWdeg : W.natDegree < S.F.natDegree := stepI_deg hG.deg c δ j₀ j₀
    have hvan := evXY_eq_zero_of_vanish A τ W hWdeg D hG.hD hG.split
      (fun b hb ↦ hG.roots b (by rw [IsRoot, eval_mul, hb.eq_zero, zero_mul]))
      (fun σ hσ k ↦ regAt_stepI σ B D (hG.reg σ hσ) c δ j₀ j₀ k)
      (fun k ↦ by
        rw [ev_inf_stepI τ k B D δ c j₀ hmax', hδ0, Nat.mul_zero, Nat.cast_zero, neg_zero,
          ← HahnSeries.C_apply, map_one, one_mul]
        exact (hdep k).mono (by exact_mod_cast Nat.zero_le _)) ⟨0, hn⟩
      (by
        rw [ev_inf_stepI τ _ B D δ c j₀ hmax', hδ0, Nat.mul_zero, Nat.cast_zero, neg_zero,
          ← HahnSeries.C_apply, map_one, one_mul]
        exact (hdep _).mono (by exact_mod_cast τ.hN))
    have hW0 : W = 0 := S.irr W hWdeg hvan
    apply hG.det
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun l ↦ Polynomial.C (c l) * X ^ (δ j₀ - δ l), fun h ↦ ?_, ?_⟩
    · have := congrFun h j₀
      simp only [Nat.sub_self, pow_zero, mul_one, Pi.zero_apply, C_eq_zero] at this
      exact hcj₀ this
    · funext i
      have := congrArg (fun P ↦ P.coeff i) hW0
      simp only [hW, stepI, if_true, finset_sum_coeff, coeff_C_mul, Polynomial.coeff_zero] at this
      simp only [Matrix.mulVec, dotProduct, coeffMat, Matrix.of_apply, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun l _ ↦ mul_comm _ _
  -- the reduction step
  have hj₀0 : (j₀ : ℕ) ≠ 0 := by
    intro h
    have : j₀ = ⟨0, hn⟩ := Fin.ext h
    rw [this, hz] at hδ0
    exact hδ0 rfl
  set δ' := Function.update δ j₀ (δ j₀ - 1) with hδ'
  have hlt : ∑ j, δ' j < m := by
    rw [← hm, hδ', Finset.sum_update_of_mem (Finset.mem_univ j₀),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
    have : Finset.univ \ {j₀} = Finset.univ.erase j₀ := by ext; simp
    rw [this]
    omega
  refine ih _ hlt (stepI B c δ j₀) D δ' (finGood_stepI A B D hG c δ j₀ hcj₀ hj₀0)
    (fun σ hσ ↦ indepAt_stepI σ B D (hG.reg σ hσ) (hI σ hσ) c δ j₀ hcj₀)
    (poleBd_stepI τ B D δ hP c j₀ hmax' hdep) ?_ rfl
  have hne : (⟨0, hn⟩ : Fin S.F.natDegree) ≠ j₀ := fun e ↦ hj₀0 (by rw [← e])
  rw [hδ', Function.update_of_ne hne, hz]


/-- **Normalized integral bases exist**: locally integral and independent at the given points,
independent at infinity, `w₀ = 1`, `δ₀ = 0`. -/
theorem exists_basis (A : List S.LocSys) (hA : (A.map LocSys.a).Nodup) (τ : S.InfSys) :
    ∃ (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (δ : Fin S.F.natDegree → ℕ),
      FinGood A B D ∧ (∀ σ ∈ A, IndepAt σ B D) ∧ PoleBd τ B D δ ∧ IndepInf τ B D δ ∧
      (∀ h : 0 < S.F.natDegree, δ ⟨0, h⟩ = 0) ∧ ∀ j : Fin S.F.natDegree, (j : ℕ) ≠ 0 → 1 ≤ δ j := by
  classical
  have hn : 0 < S.F.natDegree := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  obtain ⟨B, D, δ, hG, hI, hP, hII, hz⟩ := exists_basis_aux A hA τ
  refine ⟨B, D, δ, hG, hI, hP, hII, hz, fun j hj ↦ ?_⟩
  by_contra hδ
  push Not at hδ
  have hδ0 : δ j = 0 := by omega
  have hj0 : j ≠ ⟨0, hn⟩ := fun e ↦ hj (by rw [e])
  -- `wⱼ` is regular at infinity, hence constant
  set c := (τ.ev ⟨0, hn⟩ (S.fnWQ (B j) D)).coeff 0 with hc
  set W := B j - Polynomial.C (Polynomial.C c * D) with hW
  have hWdeg : W.natDegree < S.F.natDegree := by
    refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt (hG.deg j) ?_)
    rw [natDegree_C]; exact hn
  have hevI : ∀ k, τ.ev k (S.fnWQ W D) = τ.ev k (S.fnWQ (B j) D) - HahnSeries.C c := by
    intro k
    rw [hW, fnWQ_sub_const _ _ hG.hD, InfSys.ev, map_sub, S.embG_polyF, is_C]; rfl
  have hevF : ∀ σ ∈ A, ∀ k, LowerBd (σ.ev k (S.fnWQ W D)) 0 := by
    intro σ hσ k
    rw [hW, fnWQ_sub_const _ _ hG.hD, LocSys.ev, map_sub, ← LocSys.ev]
    exact (hG.reg σ hσ j k).sub (by rw [S.embG_polyF, bs_C]; exact lowerBd_C _)
  have hPj : ∀ k, LowerBd (τ.ev k (S.fnWQ (B j) D)) 0 := fun k ↦ by
    have := hP j k; rwa [hδ0, Nat.mul_zero, Nat.cast_zero, neg_zero] at this
  have hvan := evXY_eq_zero_of_vanish A τ W hWdeg D hG.hD hG.split
    (fun b hb ↦ hG.roots b (by rw [IsRoot, eval_mul, hb.eq_zero, zero_mul])) hevF
    (fun k ↦ by rw [hevI]; exact (hPj k).sub (lowerBd_C c)) ⟨0, hn⟩ (by
      rw [hevI]
      intro t ht
      have ht0 : t ≤ 0 := by omega
      rcases lt_or_eq_of_le ht0 with h | h
      · rw [HahnSeries.coeff_sub, hPj _ t h, HahnSeries.C_apply, coeff_single, if_neg (by omega),
          sub_zero]
      · subst h
        rw [HahnSeries.coeff_sub, HahnSeries.C_apply, coeff_single, if_pos rfl, hc, sub_self])
  have hW0 : W = 0 := S.irr W hWdeg hvan
  apply hG.det
  refine coeffMat_det_zero_of_col B j ⟨0, hn⟩ hj0 (Polynomial.C c) ?_
  rw [hG.one hn, ← Polynomial.C_mul]
  exact sub_eq_zero.mp hW0

end CurveData

end Norm

end Curves
