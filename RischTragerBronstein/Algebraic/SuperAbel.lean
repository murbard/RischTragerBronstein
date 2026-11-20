import RischTragerBronstein.Algebraic.SuperEmbed

/-!
# Residues of Liouville forms on a superelliptic curve

`SuperData.res_liouville`: if `f = v′ + ∑ cᵢ uᵢ′/uᵢ` in `C⟮x⟯⟮y⟯` (constants `cᵢ ∈ C`), then at every
non-branch point `P = (α, β)` (coordinates in any field `K ⊇ C`) the residue of the expansion of
`f` is `∑ cᵢ ord_P(uᵢ)`: derivatives have no residue, logarithmic derivatives have the order as
residue (`LaurentSeries.res_derivative`, `LaurentSeries.res_logDeriv`), and the expansion commutes
with the derivations (`embXY_deriv`).
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K]

lemma res_C_mul (c : K) (z : LaurentSeries K) :
    LaurentSeries.res (HahnSeries.C c * z) = c * LaurentSeries.res z := by
  rw [LaurentSeries.res, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  rfl

variable (S : SuperData C L)

lemma const_mem (c : C) : algebraMap C L c ∈ C⟮S.x⟯⟮S.y⟯ :=
  IntermediateField.algebraMap_mem _
    (⟨algebraMap C L c, IntermediateField.algebraMap_mem _ c⟩ : C⟮S.x⟯)

lemma embXY_const (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (c : C) :
    S.embXY α β hβ hβp ⟨algebraMap C L c, S.const_mem c⟩ =
      HahnSeries.C (algebraMap C K c) := by
  have e : (⟨algebraMap C L c, S.const_mem c⟩ : C⟮S.x⟯⟮S.y⟯) =
      algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨algebraMap C L c, IntermediateField.algebraMap_mem _ _⟩ :=
    rfl
  have e2 : (⟨algebraMap C L c, IntermediateField.algebraMap_mem _ _⟩ : C⟮S.x⟯) =
      ⟨aeval S.x (Polynomial.C c), by rw [aeval_C]; exact IntermediateField.algebraMap_mem _ c⟩ :=
    Subtype.ext (aeval_C S.x c).symm
  rw [e, S.embXY_algebraMap, e2, embX_aeval, shiftHom_C]

lemma res_sum {ι : Type*} (s : Finset ι) (g : ι → LaurentSeries K) :
    LaurentSeries.res (∑ i ∈ s, g i) = ∑ i ∈ s, LaurentSeries.res (g i) := by
  simp only [LaurentSeries.res]
  exact map_sum (HahnSeries.coeff.addMonoidHom (-1 : ℤ) : LaurentSeries K →+ K) g s

section Liouville

variable [CharZero C] [CharZero L] [CharZero K] [Differential C] [Differential L]
  [DifferentialAlgebra C L]

/-- **The residue of a Liouville form at a non-branch point.** -/
theorem res_liouville (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) {ι : Type*} (s : Finset ι) (c : ι → C)
    (u : ι → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i)) :
    LaurentSeries.res (S.embXY α β hβ hβp ⟨f, hf⟩) =
      ∑ i ∈ s, algebraMap C K (c i) * ((S.embXY α β hβ hβp ⟨u i, hu i⟩).order : K) := by
  set T := C⟮S.x⟯⟮S.y⟯
  set φ := S.embXY α β hβ hβp
  have hdc := S.derivClosedXY hC hx
  have hT : (⟨f, hf⟩ : T) = ⟨v′, hdc v hv⟩ + ∑ i ∈ s,
      (⟨algebraMap C L (c i), S.const_mem (c i)⟩ : T) *
        ((⟨(u i)′, hdc _ (hu i)⟩ : T) / ⟨u i, hu i⟩) :=
    Subtype.ext (by simp [heq])
  have hφ0 : ∀ i, φ ⟨u i, hu i⟩ ≠ 0 := fun i ↦
    (map_ne_zero_iff φ φ.injective).mpr (fun h ↦ hu0 i (congrArg Subtype.val h))
  rw [hT, map_add, map_sum, S.embXY_deriv hC hx α β hβ hβp v hv, LaurentSeries.res_add,
    LaurentSeries.derivation_apply, LaurentSeries.res_derivative, zero_add, res_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_div₀, S.embXY_deriv hC hx α β hβ hβp (u i) (hu i), S.embXY_const, res_C_mul,
    LaurentSeries.derivation_apply, LaurentSeries.res_logDeriv _ (hφ0 i)]

end Liouville

/-! ### Conjugation `y ↦ ζ y` -/

lemma conj_root (ζ : C) (hζ : ζ ^ S.n = 1) :
    (minpoly C⟮S.x⟯ S.y).eval₂ (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯)
      (⟨algebraMap C L ζ, S.const_mem ζ⟩ * AdjoinSimple.gen C⟮S.x⟯ S.y) = 0 := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [S.minpoly_eq, eval₂_sub, eval₂_X_pow, eval₂_C, mul_pow]
  have h1 : ((algebraMap C[X] C⟮S.x⟯ S.p : C⟮S.x⟯) : L) = aeval S.x S.p :=
    algebraMap_adjoinSimple S.x S.p
  have hz : (⟨algebraMap C L ζ, S.const_mem ζ⟩ : C⟮S.x⟯⟮S.y⟯) ^ S.n = 1 :=
    Subtype.ext (by
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, hζ, map_one])
  have hg : AdjoinSimple.gen C⟮S.x⟯ S.y ^ S.n =
      algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ S.p) :=
    Subtype.ext (by
      simp only [SubmonoidClass.coe_pow, AdjoinSimple.coe_gen]
      rw [S.hy]; exact h1.symm)
  rw [hz, hg, one_mul, sub_self]

/-- **The conjugation `y ↦ ζ y`** (for `ζⁿ = 1`). -/
noncomputable def conj (ζ : C) (hζ : ζ ^ S.n = 1) : C⟮S.x⟯⟮S.y⟯ →+* C⟮S.x⟯⟮S.y⟯ :=
  (AdjoinRoot.lift (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯) _ (S.conj_root ζ hζ)).comp
    (adjoinRootEquivAdjoin C⟮S.x⟯ S.isIntegral).symm.toRingEquiv.toRingHom

lemma conj_gen (ζ : C) (hζ : ζ ^ S.n = 1) :
    S.conj ζ hζ (AdjoinSimple.gen C⟮S.x⟯ S.y) =
      ⟨algebraMap C L ζ, S.const_mem ζ⟩ * AdjoinSimple.gen C⟮S.x⟯ S.y := by
  simp only [conj, RingHom.comp_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_ringEquiv, adjoinRootEquivAdjoin_symm_apply_gen,
    AdjoinRoot.lift_root]

lemma conj_algebraMap (ζ : C) (hζ : ζ ^ S.n = 1) (a : C⟮S.x⟯) :
    S.conj ζ hζ (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a := by
  simp only [conj, RingHom.comp_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  exact AdjoinRoot.lift_of _

/-- Ring homs out of `C⟮x⟯⟮y⟯` agreeing on `C⟮x⟯` and on `y` are equal. -/
lemma ringHom_ext_XY {M : Type*} [Field M] (f g : C⟮S.x⟯⟮S.y⟯ →+* M)
    (hF : ∀ a : C⟮S.x⟯, f (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) = g (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a))
    (hy : f (AdjoinSimple.gen C⟮S.x⟯ S.y) = g (AdjoinSimple.gen C⟮S.x⟯ S.y)) : f = g := by
  ext ⟨w, hw⟩
  induction hw using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hy
  | algebraMap a => exact hF a
  | add u v hu hv ihu ihv =>
    rw [show (⟨u + v, add_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ + ⟨v, hv⟩ from rfl, map_add, map_add,
      ihu, ihv]
  | mul u v hu hv ihu ihv =>
    rw [show (⟨u * v, mul_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ * ⟨v, hv⟩ from rfl, map_mul, map_mul,
      ihu, ihv]
  | inv u hu ihu =>
    rw [show (⟨u⁻¹, inv_mem hu⟩ : C⟮S.x⟯⟮S.y⟯) = (⟨u, hu⟩ : C⟮S.x⟯⟮S.y⟯)⁻¹ from rfl, map_inv₀,
      map_inv₀, ihu]

/-- **Expanding a conjugate**: `embXY α β ∘ conj ζ = embXY α (ζ β)`. -/
theorem embXY_conj (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (ζ : C) (hζ : ζ ^ S.n = 1) :
    (S.embXY α β hβ hβp).comp (S.conj ζ hζ) =
      S.embXY α (algebraMap C K ζ * β)
        (mul_ne_zero (fun h ↦ by
          have : (algebraMap C K ζ) ^ S.n = 1 := by rw [← map_pow, hζ, map_one]
          rw [h, zero_pow S.hn.ne'] at this; exact zero_ne_one this) hβ)
        (by rw [mul_pow, ← map_pow, hζ, map_one, one_mul, hβp]) := by
  refine S.ringHom_ext_XY _ _ (fun a ↦ ?_) ?_
  · rw [RingHom.comp_apply, S.conj_algebraMap, S.embXY_algebraMap, S.embXY_algebraMap]
  · rw [RingHom.comp_apply, S.conj_gen, map_mul, S.embXY_gen, S.embXY_gen]
    have e : (⟨algebraMap C L ζ, S.const_mem ζ⟩ : C⟮S.x⟯⟮S.y⟯) =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨algebraMap C L ζ, IntermediateField.algebraMap_mem _ _⟩ :=
      rfl
    have e2 : (⟨algebraMap C L ζ, IntermediateField.algebraMap_mem _ _⟩ : C⟮S.x⟯) =
        ⟨aeval S.x (Polynomial.C ζ), by rw [aeval_C]; exact IntermediateField.algebraMap_mem _ ζ⟩ :=
      Subtype.ext (aeval_C S.x ζ).symm
    rw [e, S.embXY_algebraMap, e2, embX_aeval, shiftHom_C, ← ofPowerSeries_C, ← map_mul]
    congr 1
    refine (LaurentSeries.pow_eq_pow_unique S.n S.hn (S.hnK K) ?_ ?_ ?_).symm
    · rw [branchY_pow, mul_pow, ← map_pow, ← map_pow, hζ, map_one, map_one, one_mul, branchY_pow]
    · rw [branchY_const, map_mul, PowerSeries.constantCoeff_C, branchY_const]
    · rw [map_mul, PowerSeries.constantCoeff_C, branchY_const]
      exact mul_ne_zero (fun h ↦ by
          have : (algebraMap C K ζ) ^ S.n = 1 := by rw [← map_pow, hζ, map_one]
          rw [h, zero_pow S.hn.ne'] at this; exact zero_ne_one this) hβ

end SuperData

end Differential
