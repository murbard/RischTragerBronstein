import RischTragerBronstein.Torsion.NonSpec6

/-!
# Non-special base points exist (7): independence of the integral basis

For two integral bases `(B, D, δ)`, `(B', D', δ')` of the same curve (`IsIntBasis`, normalised by
`w₀ = 1`, `δ₀ = 0`), the coefficient spaces `Vsp m` describe the same functions (`lspace_complete`),
so:

* `evPt_of_elt_eq`: equal functions have proportional values `Ψ_B(c)(x, y) D'(x) = Ψ_{B'}(c')(x, y) D(x)`
  at every point (`S.irr`);
* **`kerSp_transfer`**: `kerSp ≤ span e0` for points of `B` gives the same for `B'` (same points,
  `D D'` nonzero at the abscissae);
* **`sum_delta_eq`**: `∑ δ = ∑ δ'` (dimension count), so both bases give the same `g`.
-/

open Polynomial Module IntermediateField

namespace Curves

open CPoly Sup GTors LaurentSeries

section Transfer

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma natDegree_PsiC_lt (B : Fin S.F.natDegree → C[X][X]) (hB : ∀ j, (B j).natDegree < S.F.natDegree)
    (c : Fin S.F.natDegree → C[X]) : (PsiC B c).natDegree < S.F.natDegree := by
  have hpos : 0 < S.F.natDegree := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := S.F.natDegree - 1)
    fun j _ ↦ ?_) (by omega)
  refine (natDegree_C_mul_le _ _).trans ?_
  have := hB j; omega

/-- **Equal functions have proportional values.** -/
theorem evPt_of_elt_eq {B B' : Fin S.F.natDegree → C[X][X]} {D D' : C[X]} (hD : D ≠ 0)
    (hD' : D' ≠ 0) (hB : ∀ j, (B j).natDegree < S.F.natDegree)
    (hB' : ∀ j, (B' j).natDegree < S.F.natDegree) (c c' : Fin S.F.natDegree → C[X])
    (h : S.elt B D c = S.elt B' D' c') (x y : C) :
    evPt B x y c * D'.eval x = evPt B' x y c' * D.eval x := by
  set H := PsiC B c * Polynomial.C D' - PsiC B' c' * Polynomial.C D
  have hdeg : H.natDegree < S.F.natDegree := by
    refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ ?_)
    · rw [natDegree_mul_C hD']; exact S.natDegree_PsiC_lt B hB c
    · rw [natDegree_mul_C hD]; exact S.natDegree_PsiC_lt B' hB' c'
  have hev : S.evXY H = 0 := by
    have h1 := S.fnWQ_mul (PsiC B c) D hD
    have h2 := S.fnWQ_mul (PsiC B' c') D' hD'
    rw [← elt_eq_fnWQ, h] at h1
    rw [← elt_eq_fnWQ] at h2
    simp only [H, evXY_sub, evXY_mul, evXY_C, ← h1, ← h2]
    ring
  have hH : H = 0 := S.irr H hdeg hev
  have := congrArg (fun W ↦ evalW W x y) hH
  simp only [H, evalW, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, eval_sub,
    eval_mul, eval_C, coe_evalRingHom, Polynomial.map_zero, eval_zero] at this
  rw [evPt_apply, evPt_apply, ← evalW_PsiC, ← evalW_PsiC]
  simp only [evalW]
  exact sub_eq_zero.mp this

lemma elt_single (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (j₀ : Fin S.F.natDegree) (P : C[X]) :
    S.elt B D (Pi.single j₀ P) = S.polyF P * S.fnWQ (B j₀) D := by
  classical
  rw [elt, Finset.sum_eq_single j₀ (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, polyF_zero, zero_mul])
    (by simp), Pi.single_eq_same]

lemma fnWQ_C_self (D : C[X]) (hD : D ≠ 0) : S.fnWQ (Polynomial.C D) D = 1 := by
  apply Subtype.ext
  rw [coe_fnWQ, evXY_C, IntermediateField.coe_one]
  refine mul_inv_cancel₀ ?_
  rw [← coe_polyF]; exact fun h ↦ S.polyF_ne_zero hD (Subtype.ext h)

variable {S}

lemma mem_Vsp_iff_bound (δ : Fin S.F.natDegree → ℕ) (m : ℕ) (c : Fin S.F.natDegree → C[X]) :
    c ∈ Vsp C δ m ↔ ∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ m := by
  rw [mem_Vsp]
  refine forall_congr' fun j ↦ ?_
  rw [mem_degreeLT]
  by_cases h0 : c j = 0
  · simp only [h0, degree_zero, ne_eq, not_true_eq_false, IsEmpty.forall_iff, iff_true]
    exact WithBot.bot_lt_coe _
  · rw [← natDegree_lt_iff_degree_lt h0]
    simp only [ne_eq, h0, not_false_eq_true, forall_const]
    constructor <;> intro h
    · have : δ j ≤ m := by
        by_contra hlt; push_neg at hlt; have : m + 1 - δ j = 0 := by omega
        omega
      omega
    · omega

variable [IsAlgClosed K]

/-- **Transport of coordinates** between two integral bases. -/
lemma exists_transport {B B' : Fin S.F.natDegree → C[X][X]} {D D' : C[X]}
    {δ δ' : Fin S.F.natDegree → ℕ} (hB : S.IsIntBasis K B D δ) (hB' : S.IsIntBasis K B' D' δ')
    (m : ℕ) (c' : Fin S.F.natDegree → C[X]) (hc' : c' ∈ Vsp C δ' m) :
    ∃ c ∈ Vsp C δ m, S.elt B D c = S.elt B' D' c' := by
  obtain ⟨c, hc, hb⟩ := lspace_complete hB (S.elt B' D' c') (regular_elt hB'.reg c') m
    (inf_elt hB'.inf c' m ((mem_Vsp_iff_bound δ' m c').mp hc'))
  exact ⟨c, (mem_Vsp_iff_bound δ m c).mpr hb, hc.symm⟩

variable (hn : 0 < S.F.natDegree)

/-- **Non-speciality does not depend on the integral basis.** -/
theorem kerSp_transfer {B B' : Fin S.F.natDegree → C[X][X]} {D D' : C[X]}
    {δ δ' : Fin S.F.natDegree → ℕ} (hB : S.IsIntBasis K B D δ) (hB' : S.IsIntBasis K B' D' δ')
    (hB0 : B ⟨0, hn⟩ = Polynomial.C D) (hB0' : B' ⟨0, hn⟩ = Polynomial.C D')
    (m r : ℕ) (f : Fin r → AdmFib B) (f' : Fin r → AdmFib B') (hx : ∀ l, (f l).x = (f' l).x)
    (hy : ∀ l, (f l).ys = (f' l).ys) (hDx : ∀ l, D.eval (f l).x ≠ 0)
    (hDx' : ∀ l, D'.eval (f l).x ≠ 0) (j₀ : Fin r → Fin S.F.natDegree)
    (h : kerSp δ m r f j₀ ≤ C ∙ e0 hn f) : kerSp δ' m r f' j₀ ≤ C ∙ e0 hn f' := by
  classical
  intro c' hc'
  rw [mem_kerSp] at hc'
  obtain ⟨c, hcV, hce⟩ := exists_transport hB hB' m c' hc'.1
  have hc : c ∈ kerSp δ m r f j₀ := by
    rw [mem_kerSp]
    refine ⟨hcV, fun l k hk ↦ ?_⟩
    have e := S.evPt_of_elt_eq hB.hD hB'.hD hB.deg hB'.deg c c' hce (f l).x ((f l).ys k)
    rw [hx l, hy l, hc'.2 l k hk, zero_mul, ← hx l] at e
    rw [hy l]
    exact (mul_eq_zero.mp e).resolve_right (hDx' l)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h hc)
  refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
  have hprod : prodX f = prodX f' := by simp [prodX, hx]
  have hsm : ∀ (P : C[X]), a • (Pi.single ⟨0, hn⟩ P : Fin S.F.natDegree → C[X]) =
      Pi.single ⟨0, hn⟩ (Polynomial.C a * P) := fun P ↦ by
    funext j
    by_cases hj : j = ⟨0, hn⟩
    · subst hj; simp [Polynomial.smul_eq_C_mul]
    · simp [Pi.single_eq_of_ne hj]
  refine elt_injective hB'.hD hB'.deg hB'.det _ _ ?_
  rw [← hce, ← ha]
  simp only [e0, hsm, elt_single, hB0, hB0', S.fnWQ_C_self D hB.hD, S.fnWQ_C_self D' hB'.hD, hprod]

/-- The functions as a `C`-linear map into `L`. -/
noncomputable def eltL (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) :
    (Fin S.F.natDegree → C[X]) →ₗ[C] L where
  toFun c := (S.elt B D c : L)
  map_add' c c' := by rw [elt_add, IntermediateField.coe_add]
  map_smul' a c := by
    simp only [elt, IntermediateField.coe_sum, IntermediateField.coe_mul, coe_polyF,
      Pi.smul_apply, map_mul, Polynomial.algebraMap_eq, aeval_C, RingHom.id_apply, Finset.mul_sum,
      Algebra.smul_def, mul_assoc]

lemma eltL_injective {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) : Function.Injective (eltL B D (S := S)) := fun c c' h ↦
  elt_injective hB.hD hB.deg hB.det c c' (Subtype.ext h)

/-- **The sum of the weights is independent of the integral basis.** -/
theorem sum_delta_eq {B B' : Fin S.F.natDegree → C[X][X]} {D D' : C[X]}
    {δ δ' : Fin S.F.natDegree → ℕ} (hB : S.IsIntBasis K B D δ) (hB' : S.IsIntBasis K B' D' δ') :
    ∑ j, δ j = ∑ j, δ' j := by
  classical
  set m := Finset.univ.sup δ + Finset.univ.sup δ'
  have hm : ∀ j, δ j ≤ m + 1 := fun j ↦ by
    have := Finset.le_sup (f := δ) (Finset.mem_univ j); omega
  have hm' : ∀ j, δ' j ≤ m + 1 := fun j ↦ by
    have := Finset.le_sup (f := δ') (Finset.mem_univ j); omega
  have himg : (Vsp C δ m).map (eltL B D (S := S)) = (Vsp C δ' m).map (eltL B' D' (S := S)) := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      obtain ⟨c', hc', he⟩ := exists_transport hB' hB m c hc
      exact ⟨c', hc', by simp only [eltL, LinearMap.coe_mk, AddHom.coe_mk, he]⟩
    · rintro _ ⟨c', hc', rfl⟩
      obtain ⟨c, hc, he⟩ := exists_transport hB hB' m c' hc'
      exact ⟨c, hc, by simp only [eltL, LinearMap.coe_mk, AddHom.coe_mk, he]⟩
  have h1 := LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (eltL_injective hB) (Vsp C δ m))
  have h2 := LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (eltL_injective hB') (Vsp C δ' m))
  rw [finrank_Vsp] at h1 h2
  rw [himg, ← h2] at h1
  have s1 := sum_sub_delta δ (m + 1) hm
  have s2 := sum_sub_delta δ' (m + 1) hm'
  omega

end CurveData

end Transfer

end Curves
