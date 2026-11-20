import RischTragerBronstein.Mixed.KXExp2

/-!
# Orders on `yⁿ = p(x)` under Galois automorphisms and under `y ↦ ζ y`

* `laurentMap τ`: a ring endomorphism `τ` of `K` applied to the coefficients of Laurent series;
  it preserves orders when `τ` is injective (`order_laurentMap`);
* `embXY_galois`: for a `C`-algebra automorphism `τ` of `K`, `τ ∘ embXY α β = embXY (τ α) (τ β)`
  (uniqueness of the branch `ⁿ√p(α + u)` with a given constant term), hence
  `ordAt_galois`: `ord_{(α, β)} w = ord_{(τ α, τ β)} w` for `w ∈ C(x, y)`;
* `ordAt_conj`: `ord_{(α, β)} (σ w) = ord_{(α, ζ β)} w` for `σ : y ↦ ζ y`.
-/

open Polynomial IntermediateField HahnSeries

set_option linter.unusedSectionVars false

namespace LaurentSeries

variable {K : Type*} [Field K]

/-- A ring endomorphism of `K` applied to the coefficients. -/
noncomputable def laurentMap (τ : K →+* K) : LaurentSeries K →+* LaurentSeries K where
  toFun z := z.map τ
  map_one' := by
    ext g
    simp only [HahnSeries.map_coeff, HahnSeries.coeff_one]
    split_ifs <;> simp
  map_mul' x y := HahnSeries.map_mul (τ : K →ₙ+* K)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

lemma laurentMap_coeff (τ : K →+* K) (z : LaurentSeries K) (g : ℤ) :
    (laurentMap τ z).coeff g = τ (z.coeff g) := rfl

lemma order_laurentMap (τ : K →+* K) (z : LaurentSeries K) :
    (laurentMap τ z).order = z.order := by
  by_cases hz : z = 0
  · rw [hz, map_zero]
  have hz' : laurentMap τ z ≠ 0 := fun h ↦ hz (by
    ext g
    have := congrArg (fun w : LaurentSeries K ↦ w.coeff g) h
    simp only [laurentMap_coeff, HahnSeries.coeff_zero] at this
    rw [HahnSeries.coeff_zero]
    exact τ.injective (by rw [this, map_zero]))
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    rw [laurentMap_coeff]
    exact (map_ne_zero τ).mpr ((not_congr HahnSeries.coeff_order_eq_zero).mpr hz)
  · apply HahnSeries.order_le_of_coeff_ne_zero
    have := (not_congr HahnSeries.coeff_order_eq_zero).mpr hz'
    rw [laurentMap_coeff] at this
    exact fun h ↦ this (by rw [h, map_zero])

lemma laurentMap_ofPowerSeries (τ : K →+* K) (F : PowerSeries K) :
    laurentMap τ (HahnSeries.ofPowerSeries ℤ K F) =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.map τ F) := by
  ext g
  rw [laurentMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · rw [map_zero]
  · rw [PowerSeries.coeff_map]

end LaurentSeries

namespace Differential

namespace SuperData

open LaurentSeries

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]
variable (S : SuperData C L)

lemma laurentMap_shiftHom (τ : K ≃ₐ[C] K) (α : K) (P : C[X]) :
    laurentMap (τ : K →+* K) (shiftHom α P) = shiftHom (τ α) P := by
  rw [shiftHom_apply, shiftHom_apply, laurentMap_ofPowerSeries]
  congr 1
  ext m
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe, Polynomial.coeff_coe, ← Polynomial.coeff_map,
    Polynomial.map_comp, Polynomial.map_map]
  have e : (τ : K →+* K).comp (algebraMap C K) = algebraMap C K := by
    ext c; exact τ.commutes c
  rw [e]
  simp

lemma laurentMap_embX (τ : K ≃ₐ[C] K) (α : K) :
    (laurentMap (τ : K →+* K)).comp (embX S.x S.htr α) = embX S.x S.htr (τ α) := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  refine IsLocalization.ringHom_ext (nonZeroDivisors C[X]) (RingHom.ext fun P ↦ ?_)
  simp only [RingHom.comp_apply]
  rw [S.embX_algebraMap, S.embX_algebraMap, laurentMap_shiftHom]

lemma hv_galois (τ : K ≃ₐ[C] K) (α β : K) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    (τ β) ^ S.n = (S.p.map (algebraMap C K)).eval (τ α) := by
  rw [← map_pow, hβp, Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap]
  exact (Polynomial.aeval_algHom_apply (τ : K →ₐ[C] K) α S.p).symm

/-- **Galois conjugate expansions**: `τ ∘ embXY α β = embXY (τ α) (τ β)`. -/
theorem embXY_galois (τ : K ≃ₐ[C] K) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    (laurentMap (τ : K →+* K)).comp (S.embXY α β hβ hβp) =
      S.embXY (τ α) (τ β) ((map_ne_zero τ).mpr hβ) (S.hv_galois τ α β hβp) := by
  refine S.ringHom_ext_XY _ _ (fun a ↦ ?_) ?_
  · rw [RingHom.comp_apply, S.embXY_algebraMap, S.embXY_algebraMap, ← RingHom.comp_apply,
      S.laurentMap_embX]
  · rw [RingHom.comp_apply, S.embXY_gen, S.embXY_gen, laurentMap_ofPowerSeries]
    congr 1
    refine LaurentSeries.pow_eq_pow_unique S.n S.hn (S.hnK K) ?_ ?_ ?_
    · rw [← map_pow, branchY_pow, branchY_pow]
      ext m
      rw [PowerSeries.coeff_map, pShift, pShift, Polynomial.coeff_coe, Polynomial.coeff_coe,
        ← Polynomial.coeff_map, Polynomial.map_comp, Polynomial.map_map]
      have e : (τ : K →+* K).comp (algebraMap C K) = algebraMap C K := by
        ext c; exact τ.commutes c
      rw [e]
      simp
    · rw [branchY_const, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, branchY_const]
      rfl
    · rw [branchY_const]; exact (map_ne_zero τ).mpr hβ

/-- **Orders are Galois invariant.** -/
theorem ordAt_galois (τ : K ≃ₐ[C] K) (w : C⟮S.x⟯⟮S.y⟯) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K w (τ α) (τ β) = S.ordAt K w α β := by
  rw [S.ordAt_nb w α β hβ hβp, S.ordAt_nb w (τ α) (τ β) ((map_ne_zero τ).mpr hβ)
    (S.hv_galois τ α β hβp), ← S.embXY_galois τ α β hβ hβp, RingHom.comp_apply,
    order_laurentMap]

/-- **Orders of a conjugate** under `σ : y ↦ ζ y`. -/
theorem ordAt_conj (ζ : C) (hζ : ζ ^ S.n = 1) (w : C⟮S.x⟯⟮S.y⟯) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K (S.conj ζ hζ w) α β = S.ordAt K w α (algebraMap C K ζ * β) := by
  have hζK : algebraMap C K ζ ≠ 0 := fun h ↦ by
    have : (algebraMap C K ζ) ^ S.n = 1 := by rw [← map_pow, hζ, map_one]
    rw [h, zero_pow S.hn.ne'] at this; exact zero_ne_one this
  rw [S.ordAt_nb _ α β hβ hβp, S.ordAt_nb w α _ (mul_ne_zero hζK hβ)
    (by rw [mul_pow, ← map_pow, hζ, map_one, one_mul, hβp]), ← RingHom.comp_apply,
    S.embXY_conj α β hβ hβp ζ hζ]

end SuperData

end Differential
