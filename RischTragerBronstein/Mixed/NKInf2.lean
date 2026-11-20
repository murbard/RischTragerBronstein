import RischTragerBronstein.Torsion.MobCurve
import RischTragerBronstein.Mixed.NKTorsionP
import RischTragerBronstein.Torsion.MobInf
import RischTragerBronstein.Torsion.RamNonTors
import RischTragerBronstein.Mixed.KBIrr

/-!
# Two charts: `x` and `x′ = 1/x`

For `S : CurveData C L` and the transformed curve `S′ = mobCurve S 0 k M` (`x′ = 1/x`,
`y′ = y x′ᵏ`), both generate the same field (`mob_mem_iff`), and the embedding of `S` along a
branch above `x = ∞` (`x = T⁻ᴺ`, `y = r`) is the embedding of `S′` along the branch above `x′ = 0`
(`x′ = Tᴺ`, `y′ = r Tᵏᴺ`) (`embG_mob`): the places of `S` at infinity are finite places of `S′`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Mob2

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

lemma mem_adj2 (a b z : L) : z ∈ C⟮a⟯⟮b⟯ ↔ z ∈ C⟮a, b⟯ := by
  rw [← IntermediateField.mem_restrictScalars C, adjoin_simple_adjoin_simple]

namespace CurveData

variable (S : CurveData C L) (k M : ℕ)
  (hM : ∀ i ≤ (shiftP S.F 0).natDegree, ((shiftP S.F 0).coeff i).natDegree + k * i ≤ M)
  (hGm : (invP (shiftP S.F 0) k M).Monic)
  (hGn : (invP (shiftP S.F 0) k M).natDegree = S.F.natDegree)

lemma mob_x : (mobCurve S 0 k M hM hGm hGn).x = 1 / S.x := by
  show 1 / (S.x - algebraMap C L 0) = 1 / S.x
  rw [map_zero, sub_zero]

lemma mob_y : (mobCurve S 0 k M hM hGm hGn).y = S.y * (1 / S.x) ^ k := by
  show S.y * (1 / (S.x - algebraMap C L 0)) ^ k = S.y * (1 / S.x) ^ k
  rw [map_zero, sub_zero]

lemma x_ne_zero' : S.x ≠ 0 := by
  have := x_sub_ne S (0 : C); rwa [map_zero, sub_zero] at this

/-- **The same field.** -/
lemma mob_mem_iff (z : L) :
    z ∈ C⟮(mobCurve S 0 k M hM hGm hGn).x⟯⟮(mobCurve S 0 k M hM hGm hGn).y⟯ ↔
      z ∈ C⟮S.x⟯⟮S.y⟯ := by
  set S' := mobCurve S 0 k M hM hGm hGn with hS'
  have hx0 := S.x_ne_zero'
  rw [mem_adj2, mem_adj2]
  constructor
  · intro hz
    refine (adjoin_le_iff.mpr ?_) hz
    have hxm : S.x ∈ C⟮S.x, S.y⟯ := subset_adjoin _ _ (Set.mem_insert _ _)
    have hym : S.y ∈ C⟮S.x, S.y⟯ := subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
    intro v hv
    rcases hv with hv | hv
    · rw [hv, S.mob_x k M hM hGm hGn]; exact div_mem (one_mem _) hxm
    · rw [Set.mem_singleton_iff] at hv
      rw [hv, S.mob_y k M hM hGm hGn]
      exact mul_mem hym (pow_mem (div_mem (one_mem _) hxm) _)
  · intro hz
    refine (adjoin_le_iff.mpr ?_) hz
    have hxm : S'.x ∈ C⟮S'.x, S'.y⟯ := subset_adjoin _ _ (Set.mem_insert _ _)
    have hym : S'.y ∈ C⟮S'.x, S'.y⟯ := subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
    have hx' : S'.x = 1 / S.x := S.mob_x k M hM hGm hGn
    have hy' : S'.y = S.y * (1 / S.x) ^ k := S.mob_y k M hM hGm hGn
    intro v hv
    rcases hv with hv | hv
    · rw [hv, show S.x = 1 / S'.x by rw [hx', one_div_one_div]]
      exact div_mem (one_mem _) hxm
    · rw [Set.mem_singleton_iff] at hv
      rw [hv, show S.y = S'.y / S'.x ^ k by
        rw [hy', hx', mul_div_cancel_right₀ _ (pow_ne_zero _ (one_div_ne_zero hx0))]]
      exact div_mem hym (pow_mem hxm _)

lemma infSub_X_K (N : ℕ) : infSub (C := C) (K := K) N X = single (-(N : ℤ)) 1 := by
  rw [infSub, coe_eval₂RingHom, eval₂_X]

lemma branchSub_zero_X (N : ℕ) : branchSub (C := C) (K := K) N 0 X = single (N : ℤ) 1 := by
  rw [branchSub_apply, Polynomial.map_X, X_comp, map_zero, zero_add, Polynomial.coe_pow,
    Polynomial.coe_X, ← ofPowerSeries_X_pow]

lemma infSub_C (N : ℕ) (c : C) : infSub (K := K) N (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := by
  rw [infSub, coe_eval₂RingHom, eval₂_C]; rfl

lemma branchSub_C (N : ℕ) (e : K) (c : C) :
    branchSub (C := C) (K := K) N e (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := by
  rw [branchSub_apply, Polynomial.map_C, C_comp, Polynomial.coe_C, ofPowerSeries_C]

lemma single_neg_invK (N : ℕ) : (single (-(N : ℤ)) (1 : K))⁻¹ = single (N : ℤ) 1 :=
  inv_eq_of_mul_eq_one_right (by rw [single_mul_single, neg_add_cancel, mul_one]; rfl)

/-- **Uniqueness of the expansion**: a ring map agreeing with `g` on `C[x]` and sending `y ↦ Y`. -/
lemma embG_unique (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K)
    (h1 : ∀ Q, φ (S.polyF Q) = g Q) (h2 : φ (AdjoinSimple.gen C⟮S.x⟯ S.y) = Y) :
    φ = S.embG g hg Y hY := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  refine S.ringHom_ext' _ _ (fun a ↦ ?_) (by rw [h2, S.embG_gen])
  rw [S.embG_algebraMap]
  have : φ.comp (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯) = S.embXG g hg :=
    IsLocalization.ringHom_ext (nonZeroDivisors C[X]) (RingHom.ext fun P ↦ by
      simp only [RingHom.comp_apply, S.embXG_algebraMap]; exact h1 P)
  exact congrArg (fun ψ : C⟮S.x⟯ →+* LaurentSeries K ↦ ψ a) this

/-- The image of `y` under a ring map extending `g` is a root of `F` over `g`. -/
lemma root_of_hom (g : C[X] →+* LaurentSeries K) (φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K)
    (h1 : ∀ Q, φ (S.polyF Q) = g Q) :
    (S.F.map g).eval (φ (AdjoinSimple.gen C⟮S.x⟯ S.y)) = 0 := by
  letI := algebraAdjoinSimple (F := C) S.x
  have h0 : S.evT S.F = 0 := Subtype.ext (by rw [S.coe_evT, S.evXY_F]; rfl)
  have hg : φ.comp ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯).comp (algebraMap C[X] C⟮S.x⟯)) = g :=
    RingHom.ext fun Q ↦ h1 Q
  rw [← hg, eval_map, ← Polynomial.hom_eval₂, ← eval_map]
  exact (congrArg φ h0).trans (map_zero φ)

/-- The inclusion `C⟮x′⟯⟮y′⟯ → C⟮x⟯⟮y⟯` (an equality of subfields of `L`). -/
def mobι : C⟮(mobCurve S 0 k M hM hGm hGn).x⟯⟮(mobCurve S 0 k M hM hGm hGn).y⟯ →+*
    C⟮S.x⟯⟮S.y⟯ where
  toFun z := ⟨z, (S.mob_mem_iff k M hM hGm hGn z).1 z.2⟩
  map_one' := Subtype.ext (by simp only [OneMemClass.coe_one])
  map_mul' _ _ := Subtype.ext (by simp only [MulMemClass.coe_mul])
  map_zero' := Subtype.ext (by simp only [ZeroMemClass.coe_zero])
  map_add' _ _ := Subtype.ext (by simp only [AddMemClass.coe_add])

lemma coe_mobι (z : C⟮(mobCurve S 0 k M hM hGm hGn).x⟯⟮(mobCurve S 0 k M hM hGm hGn).y⟯) :
    (S.mobι k M hM hGm hGn z).val = z.val := by
  unfold mobι; exact Subtype.coe_mk _ _

/-- **The two charts**: the expansion of `S′` along `x′ = Tᴺ`, `y′ = r Tᵏᴺ` is the expansion of
`S` along `x = T⁻ᴺ`, `y = r`. -/
theorem embG_mob (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0) :
    ∃ hr' : ((mobCurve S 0 k M hM hGm hGn).F.map (branchSub (C := C) N 0)).eval
        (r * single ((k * N : ℕ) : ℤ) 1) = 0,
      (mobCurve S 0 k M hM hGm hGn).embG (branchSub N 0) (branchSub_injective N hN 0) _ hr' =
        (S.embG (infSub N) (infSub_injective N hN) r hr).comp (S.mobι k M hM hGm hGn) := by
  set S' := mobCurve S 0 k M hM hGm hGn with hS'
  set Ψ := (S.embG (infSub N) (infSub_injective N hN) r hr).comp (S.mobι k M hM hGm hGn) with hΨ
  have hx0 := S.x_ne_zero'
  letI := algebraAdjoinSimple (F := C) S'.x
  have hX : S.mobι k M hM hGm hGn (S'.polyF X) = (S.polyF X)⁻¹ := Subtype.ext (by
    rw [coe_mobι, S'.coe_polyF, aeval_X, IntermediateField.coe_inv, S.coe_polyF, aeval_X,
      S.mob_x k M hM hGm hGn, one_div])
  have hC : ∀ a : C, S.mobι k M hM hGm hGn (S'.polyF (Polynomial.C a)) = S.polyF (Polynomial.C a) :=
    fun a ↦ Subtype.ext (by rw [coe_mobι, S'.coe_polyF, aeval_C, S.coe_polyF, aeval_C])
  have h1 : ∀ Q, Ψ (S'.polyF Q) = branchSub N 0 Q := by
    have : Ψ.comp ((algebraMap C⟮S'.x⟯ C⟮S'.x⟯⟮S'.y⟯).comp (algebraMap C[X] C⟮S'.x⟯)) =
        branchSub N 0 := by
      refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
      · show Ψ (S'.polyF (Polynomial.C a)) = _
        rw [hΨ, RingHom.comp_apply, hC, S.embG_polyF, infSub_C, branchSub_C]
      · show Ψ (S'.polyF X) = _
        rw [hΨ, RingHom.comp_apply, hX, map_inv₀, S.embG_polyF, infSub_X_K, single_neg_invK,
          branchSub_zero_X]
    exact fun Q ↦ congrArg (fun φ : C[X] →+* LaurentSeries K ↦ φ Q) this
  have h2 : Ψ (AdjoinSimple.gen C⟮S'.x⟯ S'.y) = r * single ((k * N : ℕ) : ℤ) 1 := by
    have e : S.mobι k M hM hGm hGn (AdjoinSimple.gen C⟮S'.x⟯ S'.y) =
        AdjoinSimple.gen C⟮S.x⟯ S.y * ((S.polyF X)⁻¹) ^ k := Subtype.ext (by
      rw [coe_mobι, AdjoinSimple.coe_gen, IntermediateField.coe_mul, AdjoinSimple.coe_gen,
        IntermediateField.coe_pow, IntermediateField.coe_inv, S.coe_polyF, aeval_X,
        S.mob_y k M hM hGm hGn, one_div])
    rw [hΨ, RingHom.comp_apply, e, map_mul, S.embG_gen, map_pow, map_inv₀, S.embG_polyF,
      infSub_X_K, single_neg_invK, single_pow, one_pow]
    congr 2
  have hr' := S'.root_of_hom (branchSub N 0) Ψ h1
  rw [h2] at hr'
  exact ⟨hr', (S'.embG_unique _ _ _ _ Ψ h1 h2).symm⟩

end CurveData

end Mob2

section Integral

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]
  [IsAlgClosed K] [CharZero K]

lemma orderTop_eval₂_nonneg (t : LaurentSeries K) (ht : 0 ≤ t.orderTop) (Q : C[X]) :
    0 ≤ (Q.eval₂ ((HahnSeries.C).comp (algebraMap C K)) t).orderTop := by
  set v := HahnSeries.addVal ℤ K with hv
  have hvx : ∀ x : LaurentSeries K, v x = x.orderTop := fun x ↦ HahnSeries.addVal_apply
  rw [← hvx, eval₂_eq_sum_range]
  refine AddValuation.map_le_sum v fun i _ ↦ ?_
  rw [AddValuation.map_mul, AddValuation.map_pow, hvx, hvx]
  refine add_nonneg ?_ (nsmul_nonneg ht _)
  rw [RingHom.comp_apply]
  by_cases h0 : algebraMap C K (Q.coeff i) = 0
  · rw [h0, map_zero, HahnSeries.orderTop_zero]; exact le_top
  · rw [HahnSeries.C_apply, HahnSeries.orderTop_single h0]; exact le_refl _

namespace CurveData

variable (S2 : CurveData C L)

/-- **Integral over `C[1/x]`**: if `z` is a root of a monic polynomial with coefficients in
`C[1/x]`, then `z` has no pole along any branch where `1/x` has none. -/
lemma orderTop_nonneg_of_inv_integral (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (hgC : ∀ c : C, g (Polynomial.C c) = HahnSeries.C (algebraMap C K c))
    (hgX : 0 ≤ ((g X)⁻¹).orderTop) (Y : LaurentSeries K) (hY : (S2.F.map g).eval Y = 0)
    (z : C⟮S2.x⟯⟮S2.y⟯) (M : C[X][X]) (hM : M.Monic)
    (hz : (M.map (aeval (1 / S2.x)).toRingHom).eval (z : L) = 0) :
    0 ≤ (S2.embG g hg Y hY z).orderTop := by
  letI := algebraAdjoinSimple (F := C) S2.x
  set ψ := S2.embG g hg Y hY with hψ
  set xi : C⟮S2.x⟯⟮S2.y⟯ := (S2.polyF X)⁻¹ with hxi
  set h : C[X] →+* C⟮S2.x⟯⟮S2.y⟯ := eval₂RingHom (algebraMap C _) xi with hh
  have hval : ((C⟮S2.x⟯⟮S2.y⟯).val.toRingHom).comp h = (aeval (1 / S2.x)).toRingHom := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [RingHom.comp_apply, hh, coe_eval₂RingHom, eval₂_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_C]
      rfl
    · simp only [RingHom.comp_apply, hh, coe_eval₂RingHom, eval₂_X, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_X, hxi]
      show ((S2.polyF X)⁻¹ : C⟮S2.x⟯⟮S2.y⟯).val = _
      rw [IntermediateField.coe_inv, S2.coe_polyF, aeval_X, one_div]
  have h0 : (M.map h).eval z = 0 := by
    apply (C⟮S2.x⟯⟮S2.y⟯).val.toRingHom.injective
    rw [map_zero, eval_map, Polynomial.hom_eval₂, hval, ← eval_map]
    exact hz
  have hψh : ψ.comp h = eval₂RingHom ((HahnSeries.C).comp (algebraMap C K)) ((g X)⁻¹) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [RingHom.comp_apply, hh, coe_eval₂RingHom, eval₂_C]
      exact congrArg (fun φ : C →+* LaurentSeries K ↦ φ a) (S2.embG_algebraMapC g hg hgC Y hY)
    · simp only [RingHom.comp_apply, hh, coe_eval₂RingHom, eval₂_X, hxi]
      rw [map_inv₀, hψ, S2.embG_polyF]
  have h1 := congrArg ψ h0
  rw [map_zero, eval_map, Polynomial.hom_eval₂, ← eval_map, hψh] at h1
  refine orderTop_nonneg_of_monic_root _ (hM.map _) (fun i ↦ ?_) _ h1
  rw [coeff_map, coe_eval₂RingHom]
  exact orderTop_eval₂_nonneg _ hgX _

lemma orderTop_inv_branchSub (N : ℕ) (hN : 0 < N) (b : K) (hb : b ≠ 0) :
    0 ≤ ((branchSub (C := C) N b X)⁻¹).orderTop := by
  have hX0 : branchSub (C := C) N b X ≠ 0 := fun h ↦ X_ne_zero (branchSub_injective N hN b
    (h.trans (map_zero _).symm))
  have ho : (branchSub (C := C) N b X).order = 0 := by
    rw [order_branchSub N hN b X X_ne_zero, Polynomial.map_X,
      rootMultiplicity_eq_zero (by simpa [IsRoot] using hb), mul_zero, Nat.cast_zero]
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero (inv_ne_zero hX0), order_inv_nk _ hX0, ho]
  exact le_refl _

lemma orderTop_inv_infSub (N : ℕ) : 0 ≤ ((infSub (C := C) (K := K) N X)⁻¹).orderTop := by
  rw [infSub_X_K, single_neg_invK, HahnSeries.orderTop_single one_ne_zero]
  exact_mod_cast Nat.zero_le N

end CurveData

end Integral

section FibreSum

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]
  [IsAlgClosed K] [CharZero K]

namespace CurveData

variable (S : CurveData C L)

lemma F_ne_one : S.F ≠ 1 := fun h ↦ by
  have := S.evXY_F
  rw [h] at this
  simp [evXY] at this

/-- **Degree zero over one fibre**: a function with order `0` along every branch outside the fibre
above `α` (including infinity) has order sum `0` along the branches above `α`. -/
theorem fibre_sum_zero (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0) (α : K) (Nf : ℕ) (hNf : 0 < Nf)
    (lf : List (LaurentSeries K))
    (hlf : S.F.map (branchSub Nf α) = (lf.map fun r ↦ X - Polynomial.C r).prod)
    (o : LaurentSeries K → ℤ)
    (ho : ∀ r (hr : r ∈ lf), (S.embG (branchSub Nf α) (branchSub_injective _ hNf _)
      r (S.root_of_mem hlf hr) z).order = o r)
    (hother : ∀ b : K, b ≠ α → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), (S.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S.root_of_mem hl hr) z).order = 0)
    (hinf : ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), (S.embG (infSub N)
        (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S.root_of_mem hl hr) z).order = 0) :
    (lf.map o).sum = 0 := by
  classical
  set n := S.F.natDegree with hn
  obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt z S.F_ne_one
  have hxQ : aeval S.x Q ≠ 0 := fun h ↦ hQ ((transcendental_iff.mp S.htr) Q h)
  have hW : S.evXY W ≠ 0 := by
    rw [← hWQ]; exact mul_ne_zero (fun h ↦ hz (Subtype.ext h)) hxQ
  set R := S.normW W S.F.natDegree with hR
  have hrel : ∀ (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (r : LaurentSeries K)
      (hr : (S.F.map g).eval r = 0),
      ((W.map g).eval r).order = (S.embG g hg r hr z).order + (g Q).order := fun g hg r hr ↦ by
    have he := S.eval_W_branch g hg r hr z W Q hWQ
    have h1 : S.embG g hg r hr z ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hz
    have h2 : g Q ≠ 0 := (map_ne_zero_iff _ hg).mpr hQ
    rw [he, HahnSeries.order_mul h1 h2]
  have hfib : ∀ (b : K) (M : ℕ) (hM : 0 < M) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub M b) = (l.map fun r ↦ X - Polynomial.C r).prod),
      (l.map fun r ↦ ((W.map (branchSub M b)).eval r).order).sum =
        M * ((R.map (algebraMap C K)).rootMultiplicity b : ℤ) := fun b M hM l hl ↦ by
    rw [S.sum_order_eval W hW hWn _ (branchSub_injective M hM b) l hl]
    have hR0 := S.normW_ne_zero W S.F.natDegree hWn.le hW _ (branchSub_injective M hM b) l hl
    rw [order_branchSub M hM b R hR0]; push_cast; ring
  have hQo : ∀ (b : K) (M : ℕ) (hM : 0 < M),
      (branchSub M b Q).order = M * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ) :=
    fun b M hM ↦ by rw [order_branchSub M hM b Q hQ]; push_cast; ring
  -- outside `α`: `mult R = n mult Q`
  have hout : ∀ b : K, b ≠ α → ((R.map (algebraMap C K)).rootMultiplicity b : ℤ) =
      n * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ) := by
    intro b hb
    obtain ⟨M, hM, l0, hl0, hs0⟩ := S.branches_at b
    set l' := l0.map (HahnSeries.ofPowerSeries ℤ K) with hl'
    have hs' : S.F.map (branchSub M b) = (l'.map fun r ↦ X - Polynomial.C r).prod := by
      rw [hs0, hl', List.map_map]; rfl
    have h1 := hfib b M (Nat.pos_of_ne_zero hM) l' hs'
    have hlen : l'.length = n := by rw [hl', List.length_map, hl0]
    rw [list_sum_const l' _ ((M : ℤ) * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ))
      (fun r hr' ↦ by
        rw [hrel _ (branchSub_injective M (Nat.pos_of_ne_zero hM) b) r (S.root_of_mem hs' hr'),
          hother b hb M hM l' hs' r hr', zero_add, hQo b M (Nat.pos_of_ne_zero hM)]), hlen] at h1
    have hMp : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
    have : (M : ℤ) * (n * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ)) =
        M * ((R.map (algebraMap C K)).rootMultiplicity b : ℤ) := by rw [← h1]; ring
    exact (mul_left_cancel₀ hMp.ne' this).symm
  -- at `α`
  have hat : (lf.map o).sum = Nf * (((R.map (algebraMap C K)).rootMultiplicity α : ℤ) -
      n * ((Q.map (algebraMap C K)).rootMultiplicity α : ℤ)) := by
    have h1 := hfib α Nf hNf lf hlf
    have h2 : lf.map (fun r ↦ ((W.map (branchSub Nf α)).eval r).order) =
        lf.map (fun r ↦ o r + (Nf : ℤ) * ((Q.map (algebraMap C K)).rootMultiplicity α : ℤ)) :=
      List.map_congr_left fun r hr ↦ by
        rw [hrel _ (branchSub_injective _ hNf _) r (S.root_of_mem hlf hr), ho r hr,
          hQo α Nf hNf]
    rw [h2, List.sum_map_add, list_sum_const lf _ _ (fun _ _ ↦ rfl),
      S.length_of_split hlf] at h1
    linear_combination h1
  -- the degrees
  have hR0 : R ≠ 0 := S.normW_ne_zero W S.F.natDegree hWn.le hW _
    (branchSub_injective Nf hNf α) lf hlf
  set U : Finset K := (R.map (algebraMap C K)).roots.toFinset ∪
    (Q.map (algebraMap C K)).roots.toFinset ∪ {α} with hU
  have hdegR := natDegree_eq_sum_mult R hR0 U (by intro a ha; simp [hU, ha])
  have hdegQ := natDegree_eq_sum_mult Q hQ U (by intro a ha; simp [hU, ha])
  have hdeg : (R.natDegree : ℤ) - n * Q.natDegree =
      ((R.map (algebraMap C K)).rootMultiplicity α : ℤ) -
        n * ((Q.map (algebraMap C K)).rootMultiplicity α : ℤ) := by
    rw [hdegR, hdegQ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := (R.map (algebraMap C K)).roots.toFinset ∪
      (Q.map (algebraMap C K)).roots.toFinset) (s₂ := {α})) (fun a _ ha ↦ by
        rw [hout a (fun h ↦ ha (by rw [h]; exact Finset.mem_singleton_self α)), sub_self])]
    rw [Finset.sum_singleton]
  -- infinity
  obtain ⟨N, hN, l, -, hl⟩ := S.hasBranchesInf (K := K)
  have hNp := Nat.pos_of_ne_zero hN
  have hsumInf : (l.map fun r ↦ ((W.map (infSub N)).eval r).order).sum =
      -((N : ℤ) * R.natDegree) := by
    rw [S.sum_order_eval W hW hWn _ (infSub_injective N hNp) l hl, order_infSub N hNp R hR0]
  rw [list_sum_const l _ (-((N : ℤ) * Q.natDegree)) (fun r hr ↦ by
    rw [hrel _ (infSub_injective N hNp) r (S.root_of_mem hl hr), hinf N hN l hl r hr, zero_add,
      order_infSub N hNp Q hQ]), S.length_of_split hl] at hsumInf
  have hNz : (0 : ℤ) < N := by exact_mod_cast hNp
  have h0 : (R.natDegree : ℤ) - n * Q.natDegree = 0 := by
    have : (N : ℤ) * ((R.natDegree : ℤ) - n * Q.natDegree) = 0 := by linear_combination hsumInf
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hNz.ne'
    · exact h
  rw [hat, ← hdeg, h0, mul_zero]

end CurveData

end FibreSum

section Places

open GTors CPoly Sup

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Roots of one place are rotations of each other.** -/
lemma rCK_rot (Fc : BPoly F) (Pc : PlaceCert F) {n : ℕ} (hPc : Pc.Facts Fc n) (j : ℕ)
    (hj : j < Pc.fib.length) (k k0 : ℕ) (hk : k < n) (hk0 : k0 < n)
    (hπ : Pc.rπ j k = Pc.rπ j k0) :
    ∃ (ξ : F) (hξ : ξ ≠ 0), ξ ^ Pc.fN j = 1 ∧ rCK Fc Pc j k = rot ξ hξ (rCK Fc Pc j k0) := by
  obtain ⟨-, hrt⟩ := hPc.rt j hj
  obtain ⟨hπk, -, hsk, hNk, hζk, -⟩ := hrt k hk
  obtain ⟨-, -, hsk0, hNk0, hζk0, -⟩ := hrt k0 hk0
  have he := (hPc.pl _ hπk).2.1
  have hN0 : 0 < Pc.fN j := by rw [hNk]; exact Nat.mul_pos hsk he
  have hss : Pc.rs j k = Pc.rs j k0 := by
    rw [hπ] at hNk he
    exact Nat.eq_of_mul_eq_mul_right he (hNk.symm.trans hNk0)
  have hz : Pc.rζ j k ≠ 0 := ne_zero_of_pow_eq_one hN0 hζk
  have hz0 : Pc.rζ j k0 ≠ 0 := ne_zero_of_pow_eq_one hN0 hζk0
  refine ⟨Pc.rζ j k * (Pc.rζ j k0)⁻¹, mul_ne_zero hz (inv_ne_zero hz0), ?_, ?_⟩
  · rw [mul_pow, inv_pow, hζk, hζk0, inv_one, mul_one]
  · rw [rCK, rCK, ofPS_conjPS _ hz _ hsk, ofPS_conjPS _ hz0 _ hsk0, rot_rot,
      hπ, lsub_congr' hss hsk hsk0]
    exact rot_congr' (by field_simp) _ _ _

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

/-- **Roots of one place give the same order.** -/
lemma order_rCC_place (S2 : CurveData C L) (ι : F →+* C) (Fc : BPoly F) (Pc : PlaceCert F) {n : ℕ}
    (hPc : Pc.Facts Fc n) (j : ℕ) (hj : j < Pc.fib.length) (k k0 : ℕ) (hk : k < n) (hk0 : k0 < n)
    (hπ : Pc.rπ j k = Pc.rπ j k0) (hN : 0 < Pc.fN j)
    (hr : (S2.F.map (branchSub (Pc.fN j) (algebraMap C K (ι (Pc.fα j))))).eval
      (lmap (algebraMap C K) (rCC ι Fc Pc j k)) = 0)
    (hr0 : (S2.F.map (branchSub (Pc.fN j) (algebraMap C K (ι (Pc.fα j))))).eval
      (lmap (algebraMap C K) (rCC ι Fc Pc j k0)) = 0) (z : C⟮S2.x⟯⟮S2.y⟯) :
    (S2.embG (branchSub (Pc.fN j) (algebraMap C K (ι (Pc.fα j)))) (branchSub_injective _ hN _)
      _ hr z).order =
    (S2.embG (branchSub (Pc.fN j) (algebraMap C K (ι (Pc.fα j)))) (branchSub_injective _ hN _)
      _ hr0 z).order := by
  obtain ⟨ξ, hξ, hξN, hrot⟩ := rCK_rot Fc Pc hPc j hj k k0 hk hk0 hπ
  set φ := (algebraMap C K).comp ι with hφ
  have hφξ : φ ξ ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr hξ
  have he : lmap (algebraMap C K) (rCC ι Fc Pc j k) =
      rot (φ ξ) hφξ (lmap (algebraMap C K) (rCC ι Fc Pc j k0)) := by
    rw [rCC, rCC, hrot, lmap_rot, lmap_rot]
    rfl
  have hφN : φ ξ ^ Pc.fN j = 1 := by rw [← map_pow, hξN, map_one]
  have h1 := S2.embG_rot (φ ξ) hφξ (Pc.fN j) hN hφN (algebraMap C K (ι (Pc.fα j))) _ hr0 z
  have h2 : S2.embG (branchSub (Pc.fN j) (algebraMap C K (ι (Pc.fα j))))
      (branchSub_injective _ hN _) _ hr z =
      S2.embG (branchSub (Pc.fN j) (algebraMap C K (ι (Pc.fα j))))
      (branchSub_injective _ hN _) _ (rot_root (φ ξ) hφξ (Pc.fN j) hφN _ S2.F _ hr0) z :=
    congrArg (fun ψ : C⟮S2.x⟯⟮S2.y⟯ →+* LaurentSeries K ↦ ψ z)
      (S2.embG_congr' rfl _ _ he _ _)
  rw [h2, h1, order_rot]

end Places

section TwoPlaces

open GTors CPoly Sup

lemma order_zpow_ls {K : Type*} [Field K] (w : LaurentSeries K) (hw : w ≠ 0) (a : ℤ) :
    (w ^ a).order = a * w.order := by
  rcases a with a | a
  · rw [Int.ofNat_eq_natCast, zpow_natCast, HahnSeries.order_pow, nsmul_eq_mul]
  · rw [zpow_negSucc, order_inv_nk _ (pow_ne_zero _ hw), HahnSeries.order_pow, nsmul_eq_mul,
      Int.negSucc_eq]
    push_cast; ring

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L Kb : Type*} [Field C] [Field L] [Algebra C L] [Field Kb] [Algebra C Kb]
  [IsAlgClosed Kb] [CharZero Kb]

namespace CurveData

/-- The order of `zᵃ (x − c)ᵐ` along a branch. -/
lemma order_embG_zpow_lin (S2 : CurveData C L) (g : C[X] →+* LaurentSeries Kb)
    (hg : Function.Injective g) (Y : LaurentSeries Kb) (hY : (S2.F.map g).eval Y = 0)
    (z : C⟮S2.x⟯⟮S2.y⟯) (hz : z ≠ 0) (a : ℤ) (c : C) (m : ℕ) :
    (S2.embG g hg Y hY (z ^ a * S2.polyF (X - Polynomial.C c) ^ m)).order =
      a * (S2.embG g hg Y hY z).order + m * (g (X - Polynomial.C c)).order := by
  have h1 : S2.embG g hg Y hY z ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hz
  have h2 : g (X - Polynomial.C c) ≠ 0 := (map_ne_zero_iff _ hg).mpr (X_sub_C_ne_zero c)
  rw [map_mul, map_zpow₀, map_pow, S2.embG_polyF, HahnSeries.order_mul (zpow_ne_zero _ h1)
    (pow_ne_zero _ h2), order_zpow_ls _ h1, HahnSeries.order_pow, nsmul_eq_mul]

set_option maxHeartbeats 8000000 in
/-- **Two places above one fibre, with a certified non-torsion class**: a function with order `0`
outside the fibre above `α` (including infinity) has order `0` along every branch above `α`. -/
theorem fibre_orders_zero (S2 : CurveData C L) (ι : F →+* C) (T : GlobalCert F)
    (hSF : S2.F = (toB T.Fc).map (mapRingHom ι)) (hT : T.globalCheckR = true)
    (Pc : PlaceCert F) (hPc : Pc.check T.Fc T.n = true)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Rp : RedFns p F) (φp : F →+* ℚ_[p]) (hRp : RedValid p Rp φp) (Pp : PrimeCert p)
    (hPp : primeCheck Rp T Pp = true) (Qp : PlaceCert.PrimeData p)
    (hQp : Pc.primeCheck Rp T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pp.xs Qp = true)
    (Rq : RedFns q F) (φq : F →+* ℚ_[q]) (hRq : RedValid q Rq φq) (Pq : PrimeCert q)
    (hPq : primeCheck Rq T Pq = true) (Qq : PlaceCert.PrimeData q)
    (hQq : Pc.primeCheck Rq T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pq.xs Qq = true)
    (Pb : ℕ) (Lm : List (List F))
    (htest : nonPrincOK T.n ((Qp.mp * Qq.mp) * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (Qp.mp * Qq.mp)) Lm = true ∨
      nonPrincOK T.n (pairMult p q Qp.mp Qq.mp * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (pairMult p q Qp.mp Qq.mp)) Lm = true)
    (hfib1 : Pc.fib.length = 1) (hpl2 : Pc.pl.length = 2)
    (z : C⟮S2.x⟯⟮S2.y⟯) (hz : z ≠ 0)
    (hother : ∀ b : Kb, b ≠ algebraMap C Kb (ι (Pc.fα 0)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries Kb))
      (hl : S2.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S2.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S2.root_of_mem hl hr) z).order = 0)
    (hinf : ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S2.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S2.embG (infSub N)
        (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S2.root_of_mem hl hr) z).order = 0) :
    ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S2.F.map (branchSub N (algebraMap C Kb (ι (Pc.fα 0)))) =
        (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S2.embG (branchSub N (algebraMap C Kb (ι (Pc.fα 0))))
        (branchSub_injective N (Nat.pos_of_ne_zero hN) _) r (S2.root_of_mem hl hr) z).order = 0 := by
  classical
  have hTf := globalCheckR_spec hT
  obtain ⟨hn0, hmon, hdeg, -⟩ := hTf.shape
  have hnS : S2.F.natDegree = T.n := by rw [hSF, hmon.natDegree_map, hdeg]
  have hn' : (toB T.Fc).natDegree = S2.F.natDegree := by rw [hdeg, hnS]
  have hPcF := Pc.check_spec hPc
  have hPcd : Pc.Facts T.Fc (toB T.Fc).natDegree := by rw [hdeg]; exact hPcF
  have hNpos : ∀ j : Fin Pc.fib.length, 0 < Pc.fN j := fun j ↦ PlaceCert.fN_pos hPcF hn0 j j.2
  have hspC := fun j : Fin Pc.fib.length ↦ split_places_map S2 ι T.Fc hmon hSF Pc hPcd j j.2
  have hlf : ∀ j : Fin Pc.fib.length,
      S2.F.map (branchSub (Pc.fN j) (algebraMap C Kb (ι (Pc.fα j)))) =
      ((List.ofFn fun k : Fin S2.F.natDegree ↦ lmap (algebraMap C Kb) (rCC ι T.Fc Pc j k)).map
        fun r ↦ X - Polynomial.C r).prod := fun j ↦
    S2.split_lmap (K := Kb) (Pc.fN j) (ι (Pc.fα j)) (fun k ↦ rCC ι T.Fc Pc j k) (hspC j).1
  have hinjK : ∀ j : Fin Pc.fib.length, Function.Injective fun k : Fin S2.F.natDegree ↦
      lmap (algebraMap C Kb) (rCC ι T.Fc Pc j k) := fun j ↦ (lmap_injective _).comp (hspC j).2
  have hj0lt : 0 < Pc.fib.length := by rw [hfib1]; exact Nat.zero_lt_one
  set j0 : Fin Pc.fib.length := ⟨0, hj0lt⟩ with hj0
  have hjj : ∀ j : Fin Pc.fib.length, j = j0 := fun j ↦
    Fin.ext (by have h1 := j.2; have h2 : (j : ℕ) < 1 := hfib1 ▸ h1; simp only [hj0]; omega)
  set α0 := algebraMap C Kb (ι (Pc.fα 0)) with hα0
  set N := Pc.fN 0 with hNdef
  have hN : 0 < N := hNpos j0
  set R : Fin S2.F.natDegree → LaurentSeries Kb :=
    fun k ↦ lmap (algebraMap C Kb) (rCC ι T.Fc Pc 0 k) with hR
  have hl0 : S2.F.map (branchSub N α0) = ((List.ofFn R).map fun r ↦ X - Polynomial.C r).prod :=
    hlf j0
  have hRmem : ∀ k, R k ∈ List.ofFn R := fun k ↦ List.mem_ofFn.mpr ⟨k, rfl⟩
  set O : Fin S2.F.natDegree → ℤ := fun k ↦ (S2.embG (branchSub N α0)
    (branchSub_injective N hN α0) (R k) (S2.root_of_mem hl0 (hRmem k)) z).order with hO
  -- the orders sum to zero
  set o : LaurentSeries Kb → ℤ := fun r ↦ if hr : r ∈ List.ofFn R then
      (S2.embG (branchSub N α0) (branchSub_injective N hN α0) r (S2.root_of_mem hl0 hr) z).order
    else 0 with ho
  have hsum0 := S2.fibre_sum_zero z hz α0 N hN (List.ofFn R) hl0 o
    (fun r hr ↦ by simp only [ho]; rw [dif_pos hr]) hother hinf
  have hsum : ∑ k, O k = 0 := by
    rw [List.map_ofFn, List.sum_ofFn] at hsum0
    rw [← hsum0]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Function.comp_apply, ho, dif_pos (hRmem k), hO]
  -- the orders are constant on places
  have hk' : ∀ k : Fin S2.F.natDegree, (k : ℕ) < (toB T.Fc).natDegree := fun k ↦ by
    rw [hn']; exact k.2
  have hplace : ∀ k k' : Fin S2.F.natDegree, Pc.rπ 0 k = Pc.rπ 0 k' → O k = O k' :=
    fun k k' h ↦ order_rCC_place S2 ι T.Fc Pc hPcd 0 hj0lt k k' (hk' k) (hk' k') h hN _ _ z
  have hrt := fun k : Fin S2.F.natDegree ↦ (hPcd.rt 0 hj0lt).2 k (hk' k)
  have hπlt : ∀ k : Fin S2.F.natDegree, Pc.rπ 0 k < 2 := fun k ↦ by
    have := (hrt k).1; rwa [hpl2] at this
  have hrep : ∀ π < 2, ∃ k : Fin S2.F.natDegree, Pc.rπ 0 k = π := fun π hπ ↦ by
    obtain ⟨j, hj, k, hk, hk2⟩ := hPcd.surj π (by rw [hpl2]; exact hπ)
    have : j = 0 := by rw [hfib1] at hj; omega
    subst this
    exact ⟨⟨k, by rw [← hn']; exact hk⟩, hk2⟩
  haveI : Nonempty (Fin S2.F.natDegree) := ⟨⟨0, by rw [hnS]; exact hn0⟩⟩
  choose! kr hkr using hrep
  set Ô : ℕ → ℤ := fun π ↦ O (kr π) with hÔ
  have hOk : ∀ k, O k = Ô (Pc.rπ 0 k) := fun k ↦ hplace k _ (hkr _ (hπlt k)).symm
  -- ramification indices along a place
  set σ : ℕ → ℕ := fun π ↦ Pc.rs 0 (kr π) with hσ
  have hsk : ∀ k : Fin S2.F.natDegree, Pc.rs 0 k = σ (Pc.rπ 0 k) := fun k ↦ by
    obtain ⟨hπk, -, -, hNk, -⟩ := hrt k
    obtain ⟨-, -, -, hNk', -⟩ := hrt (kr (Pc.rπ 0 k))
    rw [hkr _ (hπlt k)] at hNk'
    exact Nat.eq_of_mul_eq_mul_right (hPcd.pl _ hπk).2.1 (hNk.symm.trans hNk')
  -- the counts of the places
  set c : ℕ → ℕ := fun π ↦ (Finset.univ.filter fun k : Fin S2.F.natDegree ↦ Pc.rπ 0 k = π).card
    with hc
  have hcpos : ∀ π < 2, 0 < c π := fun π hπ ↦
    Finset.card_pos.mpr ⟨kr π, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkr π hπ⟩⟩
  have hsplit : ∀ f : ℕ → ℤ, ∑ k : Fin S2.F.natDegree, f (Pc.rπ 0 k) =
      (c 0 : ℤ) * f 0 + (c 1 : ℤ) * f 1 := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k : Fin S2.F.natDegree ↦ Pc.rπ 0 k = 0)]
    congr 1
    · rw [Finset.sum_congr rfl fun k hk ↦ by rw [(Finset.mem_filter.mp hk).2], Finset.sum_const,
        nsmul_eq_mul]
    · have e : Finset.univ.filter (fun k : Fin S2.F.natDegree ↦ ¬ Pc.rπ 0 k = 0) =
          Finset.univ.filter (fun k : Fin S2.F.natDegree ↦ Pc.rπ 0 k = 1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := hπlt k
        omega
      rw [e, Finset.sum_congr rfl fun k hk ↦ by rw [(Finset.mem_filter.mp hk).2], Finset.sum_const,
        nsmul_eq_mul]
  have eqO : (c 0 : ℤ) * Ô 0 + (c 1 : ℤ) * Ô 1 = 0 := by
    rw [← hsplit Ô, ← hsum]
    exact Finset.sum_congr rfl fun k _ ↦ (hOk k).symm
  -- the certificate divisor
  set V : ℕ → ℤ := fun π ↦ (σ π : ℤ) * (Pc.Γp.getD π 0 : ℤ) - N * Pc.cΓ with hV
  have hdsum : ∑ k : Fin S2.F.natDegree, ((Pc.rs 0 k * Pc.Γp.getD (Pc.rπ 0 k) 0 : ℕ) : ℤ) =
      N * (Pc.cΓ * S2.F.natDegree) := by
    have h1 := (hPcd.dΓ 0 hj0lt).1
    have h2 := hPcd.sum
    rw [hfib1, Finset.sum_range_one] at h2
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ ((Pc.rs 0 k * Pc.Γp.getD (Pc.rπ 0 k) 0 : ℕ) : ℤ)), ← hn',
      ← Nat.cast_sum, h1, h2]
    push_cast; ring
  have eqV : (c 0 : ℤ) * V 0 + (c 1 : ℤ) * V 1 = 0 := by
    rw [← hsplit V]
    have h3 : ∑ k : Fin S2.F.natDegree, (σ (Pc.rπ 0 k) : ℤ) * (Pc.Γp.getD (Pc.rπ 0 k) 0 : ℤ) =
        N * (Pc.cΓ * S2.F.natDegree) := by
      rw [← hdsum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [hsk k]; push_cast; ring
    simp only [hV, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, h3]
    ring
  -- all orders vanish
  have hall : ∀ k, O k = 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨k1, hk1⟩ := hne
    have hc1 : (0 : ℤ) < c 1 := by exact_mod_cast hcpos 1 (by norm_num)
    have hÔ0 : Ô 0 ≠ 0 := by
      intro h0
      rw [h0, mul_zero, zero_add] at eqO
      have h1 : Ô 1 = 0 := (mul_eq_zero.mp eqO).resolve_left hc1.ne'
      apply hk1
      rw [hOk k1]
      have := hπlt k1
      interval_cases (Pc.rπ 0 k1)
      · exact h0
      · exact h1
    have hcross : V 0 * Ô 1 = V 1 * Ô 0 := by
      have : (c 1 : ℤ) * (V 0 * Ô 1 - V 1 * Ô 0) = 0 := by
        linear_combination V 0 * eqO - Ô 0 * eqV
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc1.ne')
    set M : ℕ := (Ô 0).natAbs * (Ô 0).natAbs with hMdef
    have hMz : (M : ℤ) = Ô 0 * Ô 0 := by rw [hMdef]; exact Int.natAbs_mul_self' _
    have hM : 0 < M := by
      have := Int.natAbs_pos.mpr hÔ0
      positivity
    set a : ℤ := V 0 * Ô 0 with ha
    have haO : ∀ π < 2, a * Ô π = M * V π := fun π hπ ↦ by
      rw [hMz]
      interval_cases π
      · ring
      · rw [ha, mul_assoc, mul_comm (Ô 0) (Ô 1), ← mul_assoc, hcross]; ring
    set cc : C := ι (Pc.fα 0) with hcc
    set γ : C⟮S2.x⟯⟮S2.y⟯ := z ^ a * S2.polyF (X - Polynomial.C cc) ^ (M * Pc.cΓ) with hγ
    have hγ0 : γ ≠ 0 := mul_ne_zero (zpow_ne_zero _ hz)
      (pow_ne_zero _ (S2.polyF_ne_zero (X_sub_C_ne_zero cc)))
    refine not_torsion_places_map (Kb := Kb) S2 ι T hSF hT Pc hPc hpq Rp φp hRp Pp hPp Qp hQp
      Rq φq hRq Pq hPq Qq hQq Pb Lm htest M hM hNpos hlf ⟨γ, hγ0, ?_, ?_, ?_⟩
    · intro j r hr
      have hj := hjj j
      subst hj
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
      beta_reduce
      rw [(hinjK j0).extend_apply]
      rw [S2.order_embG_zpow_lin _ _ _ _ z hz a cc (M * Pc.cΓ)]
      have hOk2 : (S2.embG (branchSub (Pc.fN ↑j0) (algebraMap C Kb (ι (Pc.fα ↑j0))))
          (branchSub_injective _ (hNpos j0) _) (lmap (algebraMap C Kb) (rCC ι T.Fc Pc (↑j0) k))
          (S2.root_of_mem (hlf j0) hr) z).order = O k := rfl
      rw [hOk2, hOk k, haO _ (hπlt k)]
      have hlin : (branchSub (C := C) (Pc.fN ↑j0) (algebraMap C Kb (ι (Pc.fα ↑j0)))
          (X - Polynomial.C cc)).order = N := by
        rw [order_branchSub _ (hNpos j0) _ _ (X_sub_C_ne_zero cc), Polynomial.map_sub,
          Polynomial.map_X, Polynomial.map_C, rootMultiplicity_X_sub_C_self, mul_one]
      rw [hlin, hV, hsk k]
      push_cast
      ring_nf
      exact le_refl _
    · intro b hb N' hN' l hl r hr
      have hbα : b ≠ α0 := fun h ↦ hb ⟨j0, h.symm⟩
      rw [S2.order_embG_zpow_lin _ _ _ _ z hz a cc (M * Pc.cΓ), hother b hbα N' hN' l hl r hr,
        mul_zero, zero_add, order_branchSub _ (Nat.pos_of_ne_zero hN') _ _ (X_sub_C_ne_zero cc)]
      positivity
    · intro N' hN' l hl r hr
      rw [S2.order_embG_zpow_lin _ _ _ _ z hz a cc (M * Pc.cΓ), hinf N' hN' l hl r hr,
        mul_zero, zero_add, order_infSub _ (Nat.pos_of_ne_zero hN') _ (X_sub_C_ne_zero cc),
        natDegree_X_sub_C]
      push_cast
      ring_nf
      exact le_refl _
  -- any branch system above `α`
  intro N' hN' l hl r hr
  obtain ⟨r0, hr0, hrel⟩ := S2.order_transfer α0 N N' hN (Nat.pos_of_ne_zero hN') (List.ofFn R) l
    hl0 hl r hr
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr0
  have h := hrel z
  have hk : (S2.embG (branchSub N α0) (branchSub_injective N hN α0) (R k)
      (S2.root_of_mem hl0 hr0) z).order = O k := rfl
  rw [hk, hall k, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hN.ne')

end CurveData

end TwoPlaces

section Geo

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]
  [IsAlgClosed K] [CharZero K]

namespace CurveData

variable (S : CurveData C L)

lemma branchSub_mapK (m : ℕ) (e : K) (P : C[X]) :
    branchSub (C := K) m e (P.map (algebraMap C K)) = branchSub m e P := by
  rw [branchSub_apply, branchSub_apply, Polynomial.map_map, Algebra.algebraMap_self,
    RingHom.id_comp]

set_option maxHeartbeats 2000000 in
/-- **Algebraic functions are constants on a geometrically irreducible curve.** -/
theorem mem_const_of_alg_geo (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C K))))
    (u : C⟮S.x⟯⟮S.y⟯) (M0 : C[X]) (hM0 : M0.Monic) (hu : aeval (u : L) M0 = 0) :
    ∃ c' : C, (u : L) = algebraMap C L c' := by
  classical
  set n := S.F.natDegree with hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  obtain ⟨N, hN, l0, hl0, hs0⟩ := S.branches_at (0 : K)
  have hNp := Nat.pos_of_ne_zero hN
  set l := l0.map (HahnSeries.ofPowerSeries ℤ K) with hl
  have hs : S.F.map (branchSub N 0) = (l.map fun r ↦ X - Polynomial.C r).prod := by
    rw [hs0, hl, List.map_map]; rfl
  obtain ⟨r, hr⟩ : ∃ r, r ∈ l :=
    List.exists_mem_of_length_pos (by rw [hl, List.length_map, hl0]; exact hn0)
  have hroot := S.root_of_mem hs hr
  have hinj := branchSub_injective (C := C) N hNp (0 : K)
  -- constant along the branch
  have h1 : aeval u M0 = 0 := by
    apply (algebraMap (C⟮S.x⟯⟮S.y⟯) L).injective
    have e : (algebraMap (C⟮S.x⟯⟮S.y⟯) L).comp (algebraMap C (C⟮S.x⟯⟮S.y⟯)) = algebraMap C L :=
      RingHom.ext fun c ↦ rfl
    rw [map_zero, aeval_def, hom_eval₂, e, ← aeval_def]
    exact hu
  have h2 := congrArg (S.embG (branchSub N 0) hinj r hroot) h1
  rw [map_zero, aeval_def, hom_eval₂, S.embG_algebraMapC (branchSub N 0) hinj
    (fun c ↦ branchSub_C N 0 c) r hroot, ← eval_map, ← Polynomial.map_map] at h2
  obtain ⟨c, hc⟩ := const_of_root _ ((Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr
    hM0.ne_zero) _ h2
  -- `u Q = W`
  obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt u S.F_ne_one
  have he := S.eval_W_branch (branchSub N 0) hinj r hroot u W Q hWQ
  rw [hc] at he
  set φ : C[X] →+* K[X] := Polynomial.mapRingHom (algebraMap C K) with hφ
  have hφi : Function.Injective φ := Polynomial.map_injective _ (algebraMap C K).injective
  have hcomp : (branchSub (C := K) (K := K) N (0 : K)).comp φ = branchSub (C := C) (K := K) N 0 :=
    RingHom.ext fun P ↦ by
      rw [RingHom.comp_apply, hφ, coe_mapRingHom, branchSub_mapK (C := C) N (0 : K) P]
  obtain ⟨W', hW'⟩ : ∃ W' : K[X][X],
      W' = W.map φ - Polynomial.C (Polynomial.C c * Q.map (algebraMap C K)) := ⟨_, rfl⟩
  have hev : (W'.map (branchSub (C := K) (K := K) N 0)).eval r = 0 := by
    rw [hW', Polynomial.map_sub, Polynomial.map_map, hcomp, eval_sub, Polynomial.map_C, eval_C,
      he, map_mul, branchSub_C, Algebra.algebraMap_self, RingHom.id_apply,
      branchSub_mapK (C := C), sub_self]
  -- the branch as a point of the curve over `K`
  set x0 : LaurentSeries K := single (N : ℤ) 1 with hx0
  have haev : (aeval x0).toRingHom = branchSub (C := K) (K := K) N 0 := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · rw [branchSub_C, Algebra.algebraMap_self, RingHom.id_apply]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, HahnSeries.ofPowerSeries_C]
    · rw [branchSub_zero_X]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, hx0]
  have htr : Transcendental K x0 := by
    rw [transcendental_iff_injective]
    intro P P' h
    have h' : (aeval x0).toRingHom P = (aeval x0).toRingHom P' := h
    rw [haev] at h'
    exact branchSub_injective N hNp 0 h'
  have hF'm : (S.F.map φ).Monic := S.monic.map _
  have hy : ((S.F.map φ).map (aeval x0).toRingHom).eval r = 0 := by
    rw [haev, Polynomial.map_map, hcomp]; exact hroot
  have hW'0 : W' = 0 := by
    refine Curves.MT.curve_irr x0 r htr _ hF'm hgeo hy W' ?_ (by rw [haev]; exact hev)
    rw [natDegree_map_eq_of_injective hφi]
    rw [hW']
    refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt natDegree_map_le hWn
    · rw [natDegree_C]; exact hn0
  -- read off the coefficients
  have hcoef : ∀ j, φ (W.coeff j) = if j = 0 then Polynomial.C c * Q.map (algebraMap C K) else 0 :=
    fun j ↦ by
      have := congrArg (fun P ↦ P.coeff j) hW'0
      simp only [hW', Polynomial.coeff_sub, coeff_map, coeff_C, Polynomial.coeff_zero] at this
      rw [sub_eq_zero] at this
      rw [this]
  have hQ0 : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  set c' : C := (W.coeff 0).leadingCoeff / Q.leadingCoeff with hc'
  have h0 := hcoef 0
  rw [if_pos rfl] at h0
  have hcc : c = algebraMap C K c' := by
    have hlc := congrArg Polynomial.leadingCoeff h0
    rw [hφ, coe_mapRingHom, leadingCoeff_map_of_injective (algebraMap C K).injective,
      Polynomial.leadingCoeff_mul, leadingCoeff_C,
      leadingCoeff_map_of_injective (algebraMap C K).injective] at hlc
    rw [hc', map_div₀, hlc]
    field_simp [(map_ne_zero_iff _ (algebraMap C K).injective).mpr hQ0]
  have hW0 : W.coeff 0 = Polynomial.C c' * Q := by
    apply hφi
    rw [h0, hcc, map_mul, hφ, coe_mapRingHom, Polynomial.map_C]
  have hWC : W = Polynomial.C (W.coeff 0) := by
    refine Polynomial.ext fun j ↦ ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [coeff_C_zero]
    · rw [coeff_C, if_neg hj.ne']
      apply hφi
      rw [hcoef j, if_neg hj.ne', map_zero]
  refine ⟨c', ?_⟩
  have hx0' : aeval S.x Q ≠ 0 := fun h ↦ hQ ((transcendental_iff.mp S.htr) Q h)
  rw [hWC, hW0] at hWQ
  rw [evXY, Polynomial.map_C, eval_C] at hWQ
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, aeval_C] at hWQ
  exact mul_right_cancel₀ hx0' hWQ

end CurveData

end Geo

section Assembly

open GTors CPoly Sup

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L Kb : Type*} [Field C] [Field L] [Algebra C L] [Field Kb] [Algebra C Kb]
  [IsAlgClosed Kb] [CharZero Kb]

namespace CurveData

/-- Order `0` from integrality of `z` and `z⁻¹` over `C[1/x]`. -/
lemma order_zero_of_inv_integral (S2 : CurveData C L) (g : C[X] →+* LaurentSeries Kb)
    (hg : Function.Injective g)
    (hgC : ∀ c : C, g (Polynomial.C c) = HahnSeries.C (algebraMap C Kb c))
    (hgX : 0 ≤ ((g X)⁻¹).orderTop) (Y : LaurentSeries Kb) (hY : (S2.F.map g).eval Y = 0)
    (z : C⟮S2.x⟯⟮S2.y⟯) (hz : z ≠ 0) (M1 M2 : C[X][X]) (hM1 : M1.Monic) (hM2 : M2.Monic)
    (h1 : (M1.map (aeval (1 / S2.x)).toRingHom).eval (z : L) = 0)
    (h2 : (M2.map (aeval (1 / S2.x)).toRingHom).eval ((z : L)⁻¹) = 0) :
    (S2.embG g hg Y hY z).order = 0 := by
  have hE : S2.embG g hg Y hY z ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hz
  have o1 := S2.orderTop_nonneg_of_inv_integral g hg hgC hgX Y hY z M1 hM1 h1
  have o2 := S2.orderTop_nonneg_of_inv_integral g hg hgC hgX Y hY z⁻¹ M2 hM2
    (by rw [IntermediateField.coe_inv]; exact h2)
  rw [map_inv₀, ← HahnSeries.order_eq_orderTop_of_ne_zero (inv_ne_zero hE), order_inv_nk _ hE] at o2
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hE] at o1
  have o1' : (0 : ℤ) ≤ (S2.embG g hg Y hY z).order := by exact_mod_cast o1
  have o2' : (0 : ℤ) ≤ -(S2.embG g hg Y hY z).order := by exact_mod_cast o2
  omega

set_option maxHeartbeats 8000000 in
/-- **Units of a curve with two places at infinity are constants**, when the difference of the
places (on the inverted curve `x′ = 1/x`, both above `x′ = 0`) is certified non-torsion. -/
theorem mem_const_of_unit_two (S : CurveData C L) (k M : ℕ)
    (hM : ∀ i ≤ (shiftP S.F 0).natDegree, ((shiftP S.F 0).coeff i).natDegree + k * i ≤ M)
    (hGm : (invP (shiftP S.F 0) k M).Monic)
    (hGn : (invP (shiftP S.F 0) k M).natDegree = S.F.natDegree)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (ι : F →+* C) (T : GlobalCert F)
    (hSF : (mobCurve S 0 k M hM hGm hGn).F = (toB T.Fc).map (mapRingHom ι))
    (hT : T.globalCheckR = true) (Pc : PlaceCert F) (hPc : Pc.check T.Fc T.n = true)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Rp : RedFns p F) (φp : F →+* ℚ_[p]) (hRp : RedValid p Rp φp) (Pp : PrimeCert p)
    (hPp : primeCheck Rp T Pp = true) (Qp : PlaceCert.PrimeData p)
    (hQp : Pc.primeCheck Rp T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pp.xs Qp = true)
    (Rq : RedFns q F) (φq : F →+* ℚ_[q]) (hRq : RedValid q Rq φq) (Pq : PrimeCert q)
    (hPq : primeCheck Rq T Pq = true) (Qq : PlaceCert.PrimeData q)
    (hQq : Pc.primeCheck Rq T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pq.xs Qq = true)
    (Pb : ℕ) (Lm : List (List F))
    (htest : nonPrincOK T.n ((Qp.mp * Qq.mp) * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (Qp.mp * Qq.mp)) Lm = true ∨
      nonPrincOK T.n (pairMult p q Qp.mp Qq.mp * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (pairMult p q Qp.mp Qq.mp)) Lm = true)
    (hfib1 : Pc.fib.length = 1) (hpl2 : Pc.pl.length = 2) (hα0 : Pc.fα 0 = 0)
    (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0)
    (hfin : ∀ (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) u).order = 0) :
    ∃ c : C, (u : L) = algebraMap C L c := by
  classical
  set S' := mobCurve S 0 k M hM hGm hGn with hS'
  have hreg : S.RegularFinite Kb u := fun a N hN l hl r hr ↦ (hfin a N hN l hl r hr).ge
  have hregI : S.RegularFinite Kb u⁻¹ := fun a N hN l hl r hr ↦ by
    rw [map_inv₀, order_inv_nk _ ((map_ne_zero_iff _ (RingHom.injective _)).mpr hu),
      hfin a N hN l hl r hr, neg_zero]
  obtain ⟨M1, hM1, hev1⟩ := S.integral_of_regular u hreg
  obtain ⟨M2, hM2, hev2⟩ := S.integral_of_regular u⁻¹ hregI
  obtain ⟨z, hzv⟩ : ∃ z : C⟮S'.x⟯⟮S'.y⟯, (z : L) = u :=
    ⟨⟨u, (S.mob_mem_iff k M hM hGm hGn u).2 u.2⟩, rfl⟩
  have hz0 : z ≠ 0 := by
    intro h; apply hu; apply Subtype.ext
    rw [ZeroMemClass.coe_zero, ← hzv, h, ZeroMemClass.coe_zero]
  have hxinv : 1 / S'.x = S.x := by rw [S.mob_x k M hM hGm hGn, one_div_one_div]
  have h1 : (M1.map (aeval (1 / S'.x)).toRingHom).eval (z : L) = 0 := by
    rw [hxinv, hzv]; exact hev1
  have h2 : (M2.map (aeval (1 / S'.x)).toRingHom).eval ((z : L)⁻¹) = 0 := by
    rw [hxinv, hzv]; rw [IntermediateField.coe_inv] at hev2; exact hev2
  have hα : algebraMap C Kb (ι (Pc.fα 0)) = 0 := by rw [hα0, map_zero, map_zero]
  have hother : ∀ b : Kb, b ≠ algebraMap C Kb (ι (Pc.fα 0)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries Kb))
      (hl : S'.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S'.root_of_mem hl hr) z).order = 0 :=
    fun b hb N hN l hl r hr ↦ S'.order_zero_of_inv_integral _ _ (fun c ↦ branchSub_C N b c)
      (orderTop_inv_branchSub N (Nat.pos_of_ne_zero hN) b (by rwa [hα] at hb)) r _ z hz0 M1 M2
      hM1 hM2 h1 h2
  have hinf : ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S'.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l), (S'.embG (infSub N)
        (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S'.root_of_mem hl hr) z).order = 0 :=
    fun N hN l hl r hr ↦ S'.order_zero_of_inv_integral _ _ (fun c ↦ infSub_C N c)
      (orderTop_inv_infSub N) r _ z hz0 M1 M2 hM1 hM2 h1 h2
  have hfib := S'.fibre_orders_zero ι T hSF hT Pc hPc hpq Rp φp hRp Pp hPp Qp hQp Rq φq hRq Pq
    hPq Qq hQq Pb Lm htest hfib1 hpl2 z hz0 hother hinf
  have hregS' : S'.RegularFinite Kb z := by
    intro a N hN l hl r hr
    by_cases ha : a = algebraMap C Kb (ι (Pc.fα 0))
    · subst ha; exact (hfib N hN l hl r hr).ge
    · exact (hother a ha N hN l hl r hr).ge
  have hinfS' : S'.RegularInf Kb z := fun N hN l hl r hr ↦ (hinf N hN l hl r hr).ge
  obtain ⟨M0, hM0, hzM⟩ := S'.algebraic_of_regularG (K := Kb) S'.hasBranches S'.hasBranchesInf z
    hregS' hinfS'
  rw [hzv] at hzM
  exact S.mem_const_of_alg_geo hgeo u M0 hM0 hzM

end CurveData

end Assembly

end Curves
