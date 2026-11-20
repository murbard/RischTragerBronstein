import RischTragerBronstein.Algebraic.SuperAbelL

/-!
# Derivations and residues at every place of a superelliptic curve

All the local expansions substitute `x ↦ X̂(s)` for a Laurent series `X̂` (`substHom X̂`): `α + s`
at an ordinary point, `e + sⁿ` at a branch point, `s⁻ⁿ` at infinity. Along such an expansion
`d/dx` becomes `δ = (dX̂/ds)⁻¹ d/ds`:

* `embG_derivG`: `embG (w′) = δ (embG w)`;
* `res_liouvilleG`: for a Liouville form `f = v′ + ∑ cᵢ uᵢ′/uᵢ`, the residue of `f dx` at the place,
  `res (embG f · dX̂/ds)`, is `∑ cᵢ ord (embG uᵢ)`.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

section Subst

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- The substitution `x ↦ X̂`. -/
noncomputable def substHom (Xh : LaurentSeries K) : C[X] →+* LaurentSeries K :=
  (aeval Xh : K[X] →ₐ[K] LaurentSeries K).toRingHom.comp (mapRingHom (algebraMap C K))

lemma substHom_apply (Xh : LaurentSeries K) (P : C[X]) :
    substHom Xh P = aeval Xh (P.map (algebraMap C K)) := rfl

/-- **Chain rule.** -/
lemma substHom_deriv [CharZero K] (Xh : LaurentSeries K) (P : C[X]) :
    LaurentSeries.derivation (substHom Xh P) =
      substHom Xh (Polynomial.derivative P) * LaurentSeries.derivation Xh := by
  rw [substHom_apply, Derivation.map_aeval, substHom_apply, derivative_map, smul_eq_mul]

lemma derivation_single [CharZero K] (k : ℤ) :
    LaurentSeries.derivation (single k (1 : K)) = single (k - 1) (k : K) := by
  ext m
  rw [LaurentSeries.derivation_apply, LaurentSeries.derivative_coeff, coeff_single, coeff_single]
  by_cases h : m = k - 1
  · rw [if_pos (by omega), if_pos h, h]; simp
  · rw [if_neg (by omega), if_neg h]; simp

end Subst

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K]

variable (S : SuperData C L)

/-- The rescaled derivation `(dX̂/ds)⁻¹ d/ds`. -/
noncomputable def deltaX (Xh : LaurentSeries K) : Derivation K (LaurentSeries K) (LaurentSeries K) where
  toFun f := (LaurentSeries.derivation Xh)⁻¹ * LaurentSeries.derivation f
  map_add' f g := by rw [map_add, mul_add]
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [(LaurentSeries.derivation (K := K)).map_smul c f, ← HahnSeries.C_mul_eq_smul,
      ← HahnSeries.C_mul_eq_smul]
    ring
  map_one_eq_zero' := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [(LaurentSeries.derivation (K := K)).map_one_eq_zero, mul_zero]
  leibniz' f g := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Derivation.leibniz, smul_eq_mul]
    ring

lemma deltaX_apply (Xh f : LaurentSeries K) :
    deltaX Xh f = (LaurentSeries.derivation Xh)⁻¹ * LaurentSeries.derivation f := rfl

lemma deltaX_subst (Xh : LaurentSeries K) (hX : LaurentSeries.derivation Xh ≠ 0) (P : C[X]) :
    deltaX Xh (substHom Xh P) = substHom Xh (Polynomial.derivative P) := by
  rw [deltaX_apply, substHom_deriv]
  field_simp

lemma deltaX_C (Xh : LaurentSeries K) (c : K) : deltaX Xh (HahnSeries.C c) = 0 := by
  rw [deltaX_apply]
  simp only [LaurentSeries.derivation_apply, derivative_laurent_C, mul_zero]

section Generic

variable (Xh : LaurentSeries K) (hX : LaurentSeries.derivation Xh ≠ 0)
  (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
include hX hgX

/-- `embXG g` intertwines `d/dx` and `δ`. -/
theorem embXG_derivG (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) :
    ∀ a (ha : a ∈ C⟮S.x⟯), ∃ ha' : a′ ∈ C⟮S.x⟯,
      S.embXG g hg ⟨a′, ha'⟩ = deltaX Xh (S.embXG g hg ⟨a, ha⟩) := by
  letI := algebraAdjoinSimple (F := C) S.x
  have hcl : DerivClosed C⟮S.x⟯ := derivClosed_adjoin_simple S.x 1 (by rw [hx, map_one])
  intro a ha
  refine ⟨hcl a ha, ?_⟩
  induction ha using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have e1 : (⟨S.x′, hcl S.x (mem_adjoin_simple_self C S.x)⟩ : C⟮S.x⟯) = 1 := Subtype.ext hx
    have e2 : (⟨S.x, mem_adjoin_simple_self C S.x⟩ : C⟮S.x⟯) = algebraMap C[X] C⟮S.x⟯ X :=
      Subtype.ext (by rw [algebraMap_adjoinSimple, aeval_X])
    rw [e1, map_one, e2, S.embXG_algebraMap, hgX, deltaX_subst Xh hX, derivative_X, map_one]
  | algebraMap c =>
    have e1 : (⟨(algebraMap C L c)′, hcl _ (IntermediateField.algebraMap_mem _ c)⟩ : C⟮S.x⟯) = 0 :=
      Subtype.ext (by
        show (algebraMap C L c)′ = 0
        rw [deriv_algebraMap, hC, map_zero])
    have e2 : (⟨algebraMap C L c, IntermediateField.algebraMap_mem _ c⟩ : C⟮S.x⟯) =
        algebraMap C[X] C⟮S.x⟯ (Polynomial.C c) :=
      Subtype.ext (by rw [algebraMap_adjoinSimple, aeval_C])
    rw [e1, map_zero, e2, S.embXG_algebraMap, hgX, deltaX_subst Xh hX, derivative_C, map_zero]
  | add u v hu hv ihu ihv =>
    have e1 : (⟨(u + v)′, hcl _ (add_mem hu hv)⟩ : C⟮S.x⟯) =
        ⟨u′, hcl u hu⟩ + ⟨v′, hcl v hv⟩ := Subtype.ext (by simp)
    have e2 : (⟨u + v, add_mem hu hv⟩ : C⟮S.x⟯) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_add, map_add, ihu, ihv]
  | mul u v hu hv ihu ihv =>
    have e1 : (⟨(u * v)′, hcl _ (mul_mem hu hv)⟩ : C⟮S.x⟯) =
        ⟨u, hu⟩ * ⟨v′, hcl v hv⟩ + ⟨v, hv⟩ * ⟨u′, hcl u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz])
    have e2 : (⟨u * v, mul_mem hu hv⟩ : C⟮S.x⟯) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_mul, map_mul, ihu, ihv, map_mul, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul]
  | inv u hu ihu =>
    have e1 : (⟨u⁻¹′, hcl _ (inv_mem hu)⟩ : C⟮S.x⟯) = -(⟨u, hu⟩ : C⟮S.x⟯)⁻¹ ^ 2 * ⟨u′, hcl u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz_inv])
    have e2 : (⟨u⁻¹, inv_mem hu⟩ : C⟮S.x⟯) = (⟨u, hu⟩ : C⟮S.x⟯)⁻¹ := rfl
    rw [e1, e2, map_mul, map_neg, map_pow, map_inv₀, ihu, Derivation.leibniz_inv, smul_eq_mul]

/-- `embG` intertwines `d/dx` and `δ`. -/
theorem embG_derivG (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (Y : LaurentSeries K)
    (hY : Y ^ S.n = g S.p) :
    ∀ w (hw : w ∈ C⟮S.x⟯⟮S.y⟯),
      S.embG g hg Y hY ⟨w′, S.derivClosedXY hC hx w hw⟩ =
        deltaX Xh (S.embG g hg Y hY ⟨w, hw⟩) := by
  letI := algebraAdjoinSimple (F := C) S.x
  have hdc := S.derivClosedXY hC hx
  set φ := S.embG g hg Y hY
  intro w hw
  induction hw using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hpx : aeval S.x S.p ∈ C⟮S.x⟯ := by
      rw [← algebraMap_adjoinSimple (F := C) S.x S.p]; exact SetLike.coe_mem _
    have hdpx : aeval S.x (Polynomial.derivative S.p) ∈ C⟮S.x⟯ := by
      rw [← algebraMap_adjoinSimple (F := C) S.x _]; exact SetLike.coe_mem _
    have e : (⟨S.y′, hdc _ (mem_adjoin_simple_self _ _)⟩ : C⟮S.x⟯⟮S.y⟯) =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨_, hdpx⟩ * AdjoinSimple.gen C⟮S.x⟯ S.y /
          ((S.n : C⟮S.x⟯⟮S.y⟯) * algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨_, hpx⟩) :=
      Subtype.ext (by
        show S.y′ = _
        rw [S.deriv_y hC hx]
        simp)
    have e2 : (⟨S.y, mem_adjoin_simple_self _ _⟩ : C⟮S.x⟯⟮S.y⟯) = AdjoinSimple.gen C⟮S.x⟯ S.y := rfl
    have ep : (⟨_, hpx⟩ : C⟮S.x⟯) = algebraMap C[X] C⟮S.x⟯ S.p :=
      Subtype.ext (algebraMap_adjoinSimple S.x S.p).symm
    have edp : (⟨_, hdpx⟩ : C⟮S.x⟯) = algebraMap C[X] C⟮S.x⟯ (Polynomial.derivative S.p) :=
      Subtype.ext (algebraMap_adjoinSimple S.x _).symm
    rw [e, e2, ep, edp, map_div₀, map_mul, map_mul, map_natCast, S.embG_algebraMap,
      S.embG_algebraMap, S.embG_gen, S.embXG_algebraMap, S.embXG_algebraMap]
    -- differentiate `Yⁿ = g p`
    have hp0 : g S.p ≠ 0 := (map_ne_zero_iff _ hg).mpr S.hsq.ne_zero
    have hY0 : Y ≠ 0 := fun h0 ↦ hp0 (by rw [← hY, h0, zero_pow S.hn.ne'])
    have hn0 : (S.n : LaurentSeries K) ≠ 0 := by
      rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := K))]
      intro h0
      have := HahnSeries.C_injective (Γ := ℤ) (R := K) (h0.trans (map_zero _).symm)
      exact S.hn.ne' (by exact_mod_cast this)
    have hd := congrArg (deltaX Xh) hY
    rw [Derivation.leibniz_pow, hgX, deltaX_subst Xh hX, ← hgX] at hd
    rw [div_eq_iff (mul_ne_zero hn0 hp0), ← hd]
    rw [← hY]
    obtain ⟨m, hm⟩ : ∃ m, S.n = m + 1 := ⟨S.n - 1, by have := S.hn; omega⟩
    rw [hm, Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  | algebraMap a =>
    have e1 : (⟨(algebraMap C⟮S.x⟯ L a)′, hdc _ (IntermediateField.algebraMap_mem _ a)⟩ :
        C⟮S.x⟯⟮S.y⟯) = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨(a : L)′,
          derivClosed_adjoin_simple S.x 1 (by rw [hx, map_one]) _ a.2⟩ := rfl
    have e2 : (⟨algebraMap C⟮S.x⟯ L a, IntermediateField.algebraMap_mem _ a⟩ : C⟮S.x⟯⟮S.y⟯) =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a := rfl
    rw [e1, e2, S.embG_algebraMap, S.embG_algebraMap]
    obtain ⟨ha', h⟩ := S.embXG_derivG Xh hX g hg hgX hC hx (a : L) a.2
    exact h
  | add u v hu hv ihu ihv =>
    have e1 : (⟨(u + v)′, hdc _ (add_mem hu hv)⟩ : C⟮S.x⟯⟮S.y⟯) =
        ⟨u′, hdc u hu⟩ + ⟨v′, hdc v hv⟩ := Subtype.ext (by simp)
    have e2 : (⟨u + v, add_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_add, map_add, ihu, ihv]
  | mul u v hu hv ihu ihv =>
    have e1 : (⟨(u * v)′, hdc _ (mul_mem hu hv)⟩ : C⟮S.x⟯⟮S.y⟯) =
        ⟨u, hu⟩ * ⟨v′, hdc v hv⟩ + ⟨v, hv⟩ * ⟨u′, hdc u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz])
    have e2 : (⟨u * v, mul_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_mul, map_mul, ihu, ihv, map_mul, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul]
  | inv u hu ihu =>
    have e1 : (⟨u⁻¹′, hdc _ (inv_mem hu)⟩ : C⟮S.x⟯⟮S.y⟯) =
        -(⟨u, hu⟩ : C⟮S.x⟯⟮S.y⟯)⁻¹ ^ 2 * ⟨u′, hdc u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz_inv])
    have e2 : (⟨u⁻¹, inv_mem hu⟩ : C⟮S.x⟯⟮S.y⟯) = (⟨u, hu⟩ : C⟮S.x⟯⟮S.y⟯)⁻¹ := rfl
    rw [e1, e2, map_mul, map_neg, map_pow, map_inv₀, ihu, Derivation.leibniz_inv, smul_eq_mul]

/-- **The residue of a Liouville form at any place.** -/
theorem res_liouvilleG (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (Y : LaurentSeries K)
    (hY : Y ^ S.n = g S.p) {ι : Type*} (s : Finset ι) (c : ι → C)
    (u : ι → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i)) :
    LaurentSeries.res (S.embG g hg Y hY ⟨f, hf⟩ * LaurentSeries.derivation Xh) =
      ∑ i ∈ s, algebraMap C K (c i) * ((S.embG g hg Y hY ⟨u i, hu i⟩).order : K) := by
  set T := C⟮S.x⟯⟮S.y⟯
  set φ := S.embG g hg Y hY
  have hdc := S.derivClosedXY hC hx
  have hT : (⟨f, hf⟩ : T) = ⟨v′, hdc v hv⟩ + ∑ i ∈ s,
      (⟨algebraMap C L (c i), S.const_mem (c i)⟩ : T) *
        ((⟨(u i)′, hdc _ (hu i)⟩ : T) / ⟨u i, hu i⟩) :=
    Subtype.ext (by simp [heq])
  have hφ0 : ∀ i, φ ⟨u i, hu i⟩ ≠ 0 := fun i ↦
    (map_ne_zero_iff φ φ.injective).mpr (fun h ↦ hu0 i (congrArg Subtype.val h))
  have hcst : ∀ i, φ ⟨algebraMap C L (c i), S.const_mem (c i)⟩ =
      HahnSeries.C (algebraMap C K (c i)) := fun i ↦ by
    letI := algebraAdjoinSimple (F := C) S.x
    have e : (⟨algebraMap C L (c i), S.const_mem (c i)⟩ : T) =
        algebraMap C⟮S.x⟯ T (algebraMap C[X] C⟮S.x⟯ (Polynomial.C (c i))) :=
      Subtype.ext (by
        show algebraMap C L (c i) = ((algebraMap C[X] C⟮S.x⟯ (Polynomial.C (c i)) : C⟮S.x⟯) : L)
        rw [algebraMap_adjoinSimple, aeval_C])
    rw [e, S.embG_algebraMap, S.embXG_algebraMap, hgX, substHom_apply, Polynomial.map_C, aeval_C,
      HahnSeries.algebraMap_apply']
    exact ofPowerSeries_C _
  have hδ : ∀ F : LaurentSeries K, deltaX Xh F * LaurentSeries.derivation Xh =
      LaurentSeries.derivation F := fun F ↦ by
    rw [deltaX_apply]; field_simp
  rw [hT, map_add, map_sum, S.embG_derivG Xh hX g hg hgX hC hx Y hY v hv, add_mul, hδ,
    LaurentSeries.res_add, LaurentSeries.derivation_apply, LaurentSeries.res_derivative, zero_add,
    Finset.sum_mul, res_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_div₀, S.embG_derivG Xh hX g hg hgX hC hx Y hY (u i) (hu i), hcst,
    show HahnSeries.C (algebraMap C K (c i)) * (deltaX Xh (φ ⟨u i, hu i⟩) / φ ⟨u i, hu i⟩) *
      LaurentSeries.derivation Xh = HahnSeries.C (algebraMap C K (c i)) *
        (deltaX Xh (φ ⟨u i, hu i⟩) * LaurentSeries.derivation Xh / φ ⟨u i, hu i⟩) by ring,
    hδ, res_C_mul, LaurentSeries.derivation_apply, LaurentSeries.res_logDeriv _ (hφ0 i)]

end Generic

/-! ### The branch points and infinity -/

lemma substHom_C (Xh : LaurentSeries K) (c : C) :
    substHom Xh (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := by
  rw [substHom_apply, Polynomial.map_C, aeval_C, HahnSeries.algebraMap_apply']
  exact ofPowerSeries_C _

lemma branchSub_eq_subst (m : ℕ) (e : K) :
    branchSub (C := C) m e = substHom (HahnSeries.C e + single (m : ℤ) 1) := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · rw [branchSub_C, substHom_C]
  · rw [substHom_apply, Polynomial.map_X, aeval_X, branchSub_apply, Polynomial.map_X, X_comp,
      Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, map_add,
      ofPowerSeries_C, ofPowerSeries_X_pow]

lemma infSub_eq_subst (m : ℕ) : infSub (C := C) (K := K) m = substHom (single (-(m : ℤ)) 1) := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · rw [infSub_C, substHom_C]
  · rw [substHom_apply, Polynomial.map_X, aeval_X, infSub, coe_eval₂RingHom, eval₂_X]

lemma derivation_branchX (m : ℕ) (hm : 0 < m) (e : K) :
    LaurentSeries.derivation (HahnSeries.C e + single (m : ℤ) (1 : K)) = single ((m : ℤ) - 1) (m : K) := by
  rw [map_add, LaurentSeries.derivation_apply, derivative_laurent_C, zero_add, derivation_single]
  simp

lemma derivation_infX (m : ℕ) :
    LaurentSeries.derivation (single (-(m : ℤ)) (1 : K)) = single (-(m : ℤ) - 1) (-(m : K)) := by
  rw [derivation_single]; simp

/-- **Residues of a Liouville form at a branch point** (`dx = n sⁿ⁻¹ ds`). -/
theorem res_liouville_branch (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (e γ : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e)
    {ι : Type*} (s : Finset ι) (c : ι → C)
    (u : ι → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i)) :
    LaurentSeries.res (S.embB e γ he hγ hγp ⟨f, hf⟩ * single ((S.n : ℤ) - 1) (S.n : K)) =
      ∑ i ∈ s, algebraMap C K (c i) * ((S.embB e γ he hγ hγp ⟨u i, hu i⟩).order : K) := by
  have hX : LaurentSeries.derivation (HahnSeries.C e + single (S.n : ℤ) (1 : K)) ≠ 0 := by
    rw [derivation_branchX S.n S.hn e]
    exact HahnSeries.single_ne_zero (by exact_mod_cast S.hn.ne')
  rw [← derivation_branchX S.n S.hn e]
  exact S.res_liouvilleG _ hX (branchSub S.n e) (branchSub_injective S.n S.hn e)
    (fun P ↦ by rw [branchSub_eq_subst]) hC hx _ _ s c u hu hu0 v f hv hf heq

/-- **Residues of a Liouville form at infinity** (`dx = −n s⁻ⁿ⁻¹ ds`). -/
theorem res_liouville_inf (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (lam : K) (hlam : lam ≠ 0)
    (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff)
    {ι : Type*} (s : Finset ι) (c : ι → C)
    (u : ι → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i)) :
    LaurentSeries.res (S.embI lam hlam hlp ⟨f, hf⟩ * single (-(S.n : ℤ) - 1) (-(S.n : K))) =
      ∑ i ∈ s, algebraMap C K (c i) * ((S.embI lam hlam hlp ⟨u i, hu i⟩).order : K) := by
  have hX : LaurentSeries.derivation (single (-(S.n : ℤ)) (1 : K)) ≠ 0 := by
    rw [derivation_infX]
    exact HahnSeries.single_ne_zero (neg_ne_zero.mpr (by exact_mod_cast S.hn.ne'))
  rw [← derivation_infX]
  exact S.res_liouvilleG _ hX (infSub S.n) (infSub_injective S.n S.hn)
    (fun P ↦ by rw [infSub_eq_subst]) hC hx _ _ s c u hu hu0 v f hv hf heq

end SuperData

end Differential
