import RischTragerBronstein.Algebraic.LocalExpansion
import RischTragerBronstein.Algebraic.SuperIrred
import RischTragerBronstein.Liouville.SimpleTranscendental
import RischTragerBronstein.Algebraic.HypGlue

/-!
# Local expansions on a superelliptic curve

For `y ∈ L` with `yⁿ = p(x)` (`p ∈ C[x]` squarefree, non-constant, `x` transcendental over `C`)
and a point `(α, β)` with `βⁿ = p(α) ≠ 0`, `embXY` is the ring embedding of `C⟮x⟯⟮y⟯` into the
Laurent series `C⸨u⸩` with `x ↦ α + u` and `y ↦ Y(u)`, the `n`-th root of `p(α + u)` with
`Y(0) = β`.

* `embX`: `C⟮x⟯ → C⸨u⸩` (fraction field of `C[x]`, `IsFractionRing.lift`), `embX_aeval`;
* `minpoly_superelliptic`: the minimal polynomial of `y` over `C⟮x⟯` is `Tⁿ − p(x)`;
* `embXY`: the extension through `AdjoinRoot`, `embXY_gen`, `embXY_of`.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

section Shift

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- `α + u`. -/
noncomputable def shiftX (α : K) : LaurentSeries K :=
  HahnSeries.C α + HahnSeries.single 1 1

/-- The ring map `C[x] → K⸨u⸩`, `P ↦ P(α + u)`, through power series. -/
noncomputable def shiftHom (α : K) : C[X] →+* LaurentSeries K :=
  (ofPowerSeries ℤ K).comp ((Polynomial.coeToPowerSeries.ringHom (R := K)).comp
    ((Polynomial.compRingHom (X + Polynomial.C α)).comp (Polynomial.mapRingHom (algebraMap C K))))

lemma shiftHom_apply (α : K) (P : C[X]) :
    shiftHom α P = ofPowerSeries ℤ K
      (((P.map (algebraMap C K)).comp (X + Polynomial.C α) : K[X]) : PowerSeries K) := rfl

lemma shiftHom_X (α : K) : shiftHom (C := C) α X = shiftX α := by
  rw [shiftHom_apply, Polynomial.map_X, X_comp, Polynomial.coe_add, Polynomial.coe_X,
    Polynomial.coe_C, map_add, ofPowerSeries_X, ofPowerSeries_C, shiftX, add_comm]

lemma shiftHom_C (α : K) (c : C) :
    shiftHom α (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := by
  rw [shiftHom_apply, Polynomial.map_C, C_comp, Polynomial.coe_C, ofPowerSeries_C]

lemma shiftHom_injective (α : K) : Function.Injective (shiftHom (C := C) α) := by
  intro P Q h
  rw [shiftHom_apply, shiftHom_apply] at h
  have h1 := HahnSeries.ofPowerSeries_injective h
  have h2 : (P.map (algebraMap C K)).comp (X + Polynomial.C α) =
      (Q.map (algebraMap C K)).comp (X + Polynomial.C α) :=
    Polynomial.coe_injective K h1
  have h3 := congrArg (fun R : K[X] ↦ R.comp (X - Polynomial.C α)) h2
  simp only [Polynomial.comp_assoc] at h3
  simp at h3
  exact Polynomial.map_injective _ (algebraMap C K).injective h3

end Shift

section Embed

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

/-- **The expansion of `C⟮x⟯` at `x = α`.** -/
noncomputable def embX (x : L) (htr : Transcendental C x) (α : K) : C⟮x⟯ →+* LaurentSeries K :=
  letI := algebraAdjoinSimple (F := C) x
  haveI := isFractionRing_adjoin_simple x htr
  IsFractionRing.lift (shiftHom_injective (C := C) α)

lemma embX_aeval (x : L) (htr : Transcendental C x) (α : K) (P : C[X]) :
    embX x htr α ⟨aeval x P, by
      rw [← algebraMap_adjoinSimple (F := C) x P]; exact SetLike.coe_mem _⟩ = shiftHom α P := by
  letI := algebraAdjoinSimple (F := C) x
  haveI := isFractionRing_adjoin_simple x htr
  have : (⟨aeval x P, by
      rw [← algebraMap_adjoinSimple (F := C) x P]; exact SetLike.coe_mem _⟩ : C⟮x⟯) =
      algebraMap C[X] C⟮x⟯ P := Subtype.ext (algebraMap_adjoinSimple x P).symm
  rw [this, embX, IsFractionRing.lift_algebraMap]

/-- **The minimal polynomial of `y`** over `C⟮x⟯` is `Tⁿ − p(x)`. -/
theorem minpoly_superelliptic (x y : L) (htr : Transcendental C x) (n : ℕ) (hn : 0 < n)
    (p : C[X]) (hsq : Squarefree p) (hp : 0 < p.natDegree) (hy : y ^ n = aeval x p) :
    letI := algebraAdjoinSimple (F := C) x
    minpoly C⟮x⟯ y = X ^ n - Polynomial.C (algebraMap C[X] C⟮x⟯ p) := by
  letI := algebraAdjoinSimple (F := C) x
  haveI := isFractionRing_adjoin_simple x htr
  have hirr := irreducible_X_pow_sub_C_fraction n hn p hsq hp C⟮x⟯
  refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C _ hn.ne')).symm
  rw [map_sub, map_pow, aeval_X, aeval_C, hy]
  change aeval x p - ((algebraMap C[X] C⟮x⟯ p : C⟮x⟯) : L) = 0
  rw [algebraMap_adjoinSimple, sub_self]

/-- The power series `p(α + u)`. -/
noncomputable def pShift (p : C[X]) (α : K) : PowerSeries K :=
  (((p.map (algebraMap C K)).comp (X + Polynomial.C α) : K[X]) : PowerSeries K)

lemma constantCoeff_pShift (p : C[X]) (α : K) :
    PowerSeries.constantCoeff (pShift p α) = (p.map (algebraMap C K)).eval α := by
  rw [pShift, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    coeff_zero_eq_eval_zero, eval_comp]
  simp

lemma shiftHom_eq_pShift (p : C[X]) (α : K) : shiftHom α p = ofPowerSeries ℤ K (pShift p α) := rfl

/-- The branch `Y(u)` of `ⁿ√p(α + u)` with `Y(0) = β`. -/
noncomputable def branchY (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (p : C[X]) (α β : K)
    (hβ : β ≠ 0) (hβp : β ^ n = (p.map (algebraMap C K)).eval α) : PowerSeries K :=
  Classical.choose (LaurentSeries.exists_pow_eq n hn hnK (pShift p α) β hβ
    (by rw [constantCoeff_pShift, hβp]))

lemma branchY_pow (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (p : C[X]) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ n = (p.map (algebraMap C K)).eval α) :
    branchY n hn hnK p α β hβ hβp ^ n = pShift p α :=
  (Classical.choose_spec (LaurentSeries.exists_pow_eq n hn hnK (pShift p α) β hβ
    (by rw [constantCoeff_pShift, hβp]))).1

lemma branchY_const (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (p : C[X]) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ n = (p.map (algebraMap C K)).eval α) :
    PowerSeries.constantCoeff (branchY n hn hnK p α β hβ hβp) = β :=
  (Classical.choose_spec (LaurentSeries.exists_pow_eq n hn hnK (pShift p α) β hβ
    (by rw [constantCoeff_pShift, hβp]))).2

/-- The data of a superelliptic point expansion. -/
structure SuperData (C L : Type*) [Field C] [Field L] [Algebra C L] where
  x : L
  y : L
  n : ℕ
  p : C[X]
  htr : Transcendental C x
  hn : 0 < n
  hsq : Squarefree p
  hp : 0 < p.natDegree
  hy : y ^ n = aeval x p
  hnC : (n : C) ≠ 0

namespace SuperData

variable (S : SuperData C L)

lemma hnK (K : Type*) [Field K] [Algebra C K] : ((S.n : ℕ) : K) ≠ 0 := by
  rw [← map_natCast (algebraMap C K)]
  exact (map_ne_zero_iff _ (algebraMap C K).injective).mpr S.hnC

lemma isIntegral : IsIntegral C⟮S.x⟯ S.y := by
  letI := algebraAdjoinSimple (F := C) S.x
  refine ⟨X ^ S.n - Polynomial.C (algebraMap C[X] C⟮S.x⟯ S.p), monic_X_pow_sub_C _ S.hn.ne', ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, S.hy]
  change aeval S.x S.p - ((algebraMap C[X] C⟮S.x⟯ S.p : C⟮S.x⟯) : L) = 0
  rw [algebraMap_adjoinSimple, sub_self]

lemma minpoly_eq :
    letI := algebraAdjoinSimple (F := C) S.x
    minpoly C⟮S.x⟯ S.y = X ^ S.n - Polynomial.C (algebraMap C[X] C⟮S.x⟯ S.p) :=
  minpoly_superelliptic S.x S.y S.htr S.n S.hn S.p S.hsq S.hp S.hy

lemma embX_algebraMap (α : K) (P : C[X]) :
    letI := algebraAdjoinSimple (F := C) S.x
    embX S.x S.htr α (algebraMap C[X] C⟮S.x⟯ P) = shiftHom α P := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  rw [embX, IsFractionRing.lift_algebraMap]

lemma root_eval (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    (minpoly C⟮S.x⟯ S.y).eval₂ (embX S.x S.htr α)
      (ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p α β hβ hβp)) = 0 := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [S.minpoly_eq, eval₂_sub, eval₂_X_pow, eval₂_C, S.embX_algebraMap, ← map_pow,
    branchY_pow, shiftHom_eq_pShift, sub_self]

/-- **The expansion of `C⟮x⟯⟮y⟯` at the point `(α, β)`.** -/
noncomputable def embXY (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K :=
  (AdjoinRoot.lift (embX S.x S.htr α) _ (S.root_eval α β hβ hβp)).comp
    (adjoinRootEquivAdjoin C⟮S.x⟯ S.isIntegral).symm.toRingEquiv.toRingHom

lemma embXY_gen (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.embXY α β hβ hβp (AdjoinSimple.gen C⟮S.x⟯ S.y) =
      ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p α β hβ hβp) := by
  simp only [embXY, RingHom.comp_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_ringEquiv, adjoinRootEquivAdjoin_symm_apply_gen,
    AdjoinRoot.lift_root]

lemma embXY_algebraMap (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (a : C⟮S.x⟯) :
    S.embXY α β hβ hβp (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) = embX S.x S.htr α a := by
  simp only [embXY, RingHom.comp_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  exact AdjoinRoot.lift_of _

lemma y_ne_zero : S.y ≠ 0 := by
  intro h0
  have h1 := S.hy
  rw [h0, zero_pow S.hn.ne'] at h1
  have hp := S.hp
  exact S.htr ⟨S.p, fun h ↦ by rw [h] at hp; simp at hp, h1.symm⟩

lemma p_ne_zero : aeval S.x S.p ≠ 0 := by
  rw [← S.hy]; exact pow_ne_zero _ S.y_ne_zero

end SuperData

end Embed

section Deriv

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K]

lemma derivative_laurent_C (c : K) : LaurentSeries.derivative K (HahnSeries.C c) = 0 := by
  ext m
  rw [LaurentSeries.derivative_coeff, HahnSeries.coeff_zero, HahnSeries.C_apply,
    HahnSeries.coeff_single]
  split_ifs with h
  · rw [h, Int.cast_zero, zero_mul]
  · rw [mul_zero]

lemma derivative_shiftX (α : K) : LaurentSeries.derivative K (shiftX α) = 1 := by
  ext m
  rw [shiftX, map_add, derivative_laurent_C, zero_add, LaurentSeries.derivative_coeff,
    HahnSeries.coeff_single, show (1 : LaurentSeries K) = HahnSeries.single 0 1 from rfl,
    HahnSeries.coeff_single]
  split_ifs with h1 h2 h2
  · simp [show m = 0 by omega]
  · omega
  · omega
  · rw [mul_zero]

/-- **`embX` commutes with the derivations.** -/
theorem embX_deriv (x : L) (htr : Transcendental C x) (α : K) (hC : ∀ c : C, c′ = 0)
    (hx : x′ = 1) :
    ∀ a (ha : a ∈ C⟮x⟯), ∃ ha' : a′ ∈ C⟮x⟯,
      embX x htr α ⟨a′, ha'⟩ = LaurentSeries.derivation (embX x htr α ⟨a, ha⟩) := by
  have hcl : DerivClosed C⟮x⟯ := derivClosed_adjoin_simple x 1 (by rw [hx, map_one])
  intro a ha
  refine ⟨hcl a ha, ?_⟩
  induction ha using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have e1 : (⟨w′, hcl w (mem_adjoin_simple_self C w)⟩ : C⟮w⟯) = 1 := Subtype.ext hx
    have e2 : (⟨w, mem_adjoin_simple_self C w⟩ : C⟮w⟯) =
        ⟨aeval w (X : C[X]), by rw [aeval_X]; exact mem_adjoin_simple_self C w⟩ :=
      Subtype.ext (aeval_X w).symm
    rw [e1, map_one, e2, embX_aeval, shiftHom_X, LaurentSeries.derivation_apply,
      derivative_shiftX]
  | algebraMap c =>
    have e1 : (⟨(algebraMap C L c)′, hcl _ (IntermediateField.algebraMap_mem _ c)⟩ : C⟮x⟯) = 0 :=
      Subtype.ext (by
        show (algebraMap C L c)′ = 0
        rw [deriv_algebraMap, hC, map_zero])
    have e2 : (⟨algebraMap C L c, IntermediateField.algebraMap_mem _ c⟩ : C⟮x⟯) =
        ⟨aeval x (Polynomial.C c), by rw [aeval_C]; exact IntermediateField.algebraMap_mem _ c⟩ :=
      Subtype.ext (aeval_C x c).symm
    rw [e1, map_zero, e2, embX_aeval, shiftHom_C, LaurentSeries.derivation_apply,
      derivative_laurent_C]
  | add u v hu hv ihu ihv =>
    have e1 : (⟨(u + v)′, hcl _ (add_mem hu hv)⟩ : C⟮x⟯) =
        ⟨u′, hcl u hu⟩ + ⟨v′, hcl v hv⟩ := Subtype.ext (by simp)
    have e2 : (⟨u + v, add_mem hu hv⟩ : C⟮x⟯) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_add, map_add, ihu, ihv]
  | mul u v hu hv ihu ihv =>
    have e1 : (⟨(u * v)′, hcl _ (mul_mem hu hv)⟩ : C⟮x⟯) =
        ⟨u, hu⟩ * ⟨v′, hcl v hv⟩ + ⟨v, hv⟩ * ⟨u′, hcl u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz])
    have e2 : (⟨u * v, mul_mem hu hv⟩ : C⟮x⟯) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_mul, map_mul, ihu, ihv, map_mul, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul]
  | inv u hu ihu =>
    have e1 : (⟨u⁻¹′, hcl _ (inv_mem hu)⟩ : C⟮x⟯) = -(⟨u, hu⟩ : C⟮x⟯)⁻¹ ^ 2 * ⟨u′, hcl u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz_inv])
    have e2 : (⟨u⁻¹, inv_mem hu⟩ : C⟮x⟯) = (⟨u, hu⟩ : C⟮x⟯)⁻¹ := rfl
    rw [e1, e2, map_mul, map_neg, map_pow, map_inv₀, ihu, Derivation.leibniz_inv, smul_eq_mul]

lemma derivation_ofPS (H : PowerSeries K) :
    LaurentSeries.derivation (ofPowerSeries ℤ K H) = ofPowerSeries ℤ K (PowerSeries.derivative H) := by
  have := LaurentSeries.derivative_single_mul_ofPS (K := K) 0 H
  simp only [HahnSeries.single_zero_one, one_mul, Int.cast_zero, zero_smul, add_zero] at this
  rw [LaurentSeries.derivation_apply, this]

lemma derivative_pShift (p : C[X]) (α : K) :
    PowerSeries.derivative (pShift p α) = pShift (Polynomial.derivative p) α := by
  rw [pShift, pShift, PowerSeries.derivative_coe, Polynomial.derivative_comp,
    Polynomial.derivative_map]
  simp

namespace SuperData

variable (S : SuperData C L)

/-- `y′ = p′(x) y / (n p(x))`. -/
lemma deriv_y (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) :
    S.y′ = aeval S.x (Polynomial.derivative S.p) * S.y / ((S.n : L) * aeval S.x S.p) := by
  have h1 := congrArg (fun z : L ↦ z′) S.hy
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at h1
  rw [deriv_aeval_x S.x hC hx] at h1
  have hy0 := S.y_ne_zero
  have hn0 : (S.n : L) ≠ 0 := by exact_mod_cast S.hn.ne'
  rw [eq_div_iff (mul_ne_zero hn0 S.p_ne_zero), ← S.hy, ← h1]
  obtain ⟨m, hm⟩ : ∃ m, S.n = m + 1 := ⟨S.n - 1, by have := S.hn; omega⟩
  rw [hm, Nat.add_sub_cancel]
  push_cast
  ring

/-- `C⟮x⟯⟮y⟯` is closed under the derivation. -/
lemma derivClosedXY (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) :
    ∀ w ∈ C⟮S.x⟯⟮S.y⟯, w′ ∈ C⟮S.x⟯⟮S.y⟯ := by
  have hcl : DerivClosed C⟮S.x⟯ := derivClosed_adjoin_simple S.x 1 (by rw [hx, map_one])
  set T := C⟮S.x⟯⟮S.y⟯
  have hF : ∀ a ∈ C⟮S.x⟯, a ∈ T := fun a ha ↦ by
    have := IntermediateField.algebraMap_mem T (⟨a, ha⟩ : C⟮S.x⟯)
    exact this
  let U : IntermediateField C⟮S.x⟯ L :=
    { carrier := {w | w ∈ T ∧ w′ ∈ T}
      mul_mem' := fun {u v} hu hv ↦ ⟨mul_mem hu.1 hv.1, by
        rw [Derivation.leibniz]
        exact add_mem (mul_mem hu.1 hv.2) (mul_mem hv.1 hu.2)⟩
      one_mem' := ⟨one_mem _, by simp⟩
      add_mem' := fun {u v} hu hv ↦ ⟨add_mem hu.1 hv.1, by
        rw [map_add]; exact add_mem hu.2 hv.2⟩
      zero_mem' := ⟨zero_mem _, by simp⟩
      algebraMap_mem' := fun a ↦ ⟨T.algebraMap_mem a, hF _ (hcl _ a.2)⟩
      inv_mem' := fun u hu ↦ ⟨inv_mem hu.1, by
        rw [Derivation.leibniz_inv]
        exact mul_mem (neg_mem (pow_mem (inv_mem hu.1) 2)) hu.2⟩ }
  have hyU : S.y ∈ U := by
    refine ⟨mem_adjoin_simple_self _ _, ?_⟩
    rw [S.deriv_y hC hx]
    have hpx : aeval S.x S.p ∈ T := hF _ (by
      rw [← algebraMap_adjoinSimple (F := C) S.x S.p]; exact SetLike.coe_mem _)
    have hdpx : aeval S.x (Polynomial.derivative S.p) ∈ T := hF _ (by
      rw [← algebraMap_adjoinSimple (F := C) S.x _]; exact SetLike.coe_mem _)
    have hnT : (S.n : L) ∈ T := IntermediateField.natCast_mem T S.n
    exact div_mem (mul_mem hdpx (mem_adjoin_simple_self _ _)) (mul_mem hnT hpx)
  have hle : T ≤ U := adjoin_simple_le_iff.mpr hyU
  intro w hw
  exact (hle hw).2

/-- The derivative of the branch: `Y′ = p′(α + u) Y / (n p(α + u))`. -/
lemma deriv_branch (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    LaurentSeries.derivation (ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p α β hβ hβp)) =
      shiftHom α (Polynomial.derivative S.p) * ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p α β hβ hβp) /
        ((S.n : LaurentSeries K) * shiftHom α S.p) := by
  set Y := branchY S.n S.hn (S.hnK K) S.p α β hβ hβp
  set Z := ofPowerSeries ℤ K Y
  have hZn : Z ^ S.n = shiftHom α S.p := by
    rw [← map_pow, branchY_pow, shiftHom_eq_pShift]
  have hY0 : Y ≠ 0 := fun h0 ↦ by
    have := branchY_const S.n S.hn (S.hnK K) S.p α β hβ hβp
    rw [← show Y = branchY S.n S.hn (S.hnK K) S.p α β hβ hβp from rfl, h0, map_zero] at this
    exact hβ this.symm
  have hZ0 : Z ≠ 0 := by
    intro h0
    apply hY0
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    rw [map_zero]; exact h0
  have hn0 : (S.n : LaurentSeries K) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := K))]
    intro h0
    have := HahnSeries.C_injective (Γ := ℤ) (R := K) (h0.trans (map_zero _).symm)
    exact S.hn.ne' (by exact_mod_cast this)
  have hp0 : shiftHom α S.p ≠ 0 := by rw [← hZn]; exact pow_ne_zero _ hZ0
  have hd := congrArg LaurentSeries.derivation hZn
  rw [Derivation.leibniz_pow, shiftHom_eq_pShift, derivation_ofPS (pShift S.p α),
    derivative_pShift, ← shiftHom_eq_pShift] at hd
  rw [eq_div_iff (mul_ne_zero hn0 hp0), ← hZn, ← hd]
  obtain ⟨m, hm⟩ : ∃ m, S.n = m + 1 := ⟨S.n - 1, by have := S.hn; omega⟩
  rw [hm, Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- **`embXY` commutes with the derivations.** -/
theorem embXY_deriv (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    ∀ w (hw : w ∈ C⟮S.x⟯⟮S.y⟯),
      S.embXY α β hβ hβp ⟨w′, S.derivClosedXY hC hx w hw⟩ =
        LaurentSeries.derivation (S.embXY α β hβ hβp ⟨w, hw⟩) := by
  have hcl : DerivClosed C⟮S.x⟯ := derivClosed_adjoin_simple S.x 1 (by rw [hx, map_one])
  have hdc := S.derivClosedXY hC hx
  set φ := S.embXY α β hβ hβp
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
    rw [e, e2, map_div₀, map_mul, map_mul, map_natCast, S.embXY_algebraMap, S.embXY_algebraMap,
      S.embXY_gen, embX_aeval, embX_aeval, S.deriv_branch]
  | algebraMap a =>
    have e1 : (⟨(algebraMap C⟮S.x⟯ L a)′, hdc _ (IntermediateField.algebraMap_mem _ a)⟩ :
        C⟮S.x⟯⟮S.y⟯) = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨(a : L)′, hcl _ a.2⟩ := rfl
    have e2 : (⟨algebraMap C⟮S.x⟯ L a, IntermediateField.algebraMap_mem _ a⟩ : C⟮S.x⟯⟮S.y⟯) =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a := rfl
    rw [e1, e2, S.embXY_algebraMap, S.embXY_algebraMap]
    obtain ⟨ha', h⟩ := embX_deriv S.x S.htr α hC hx (a : L) a.2
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

end SuperData

end Deriv

end Differential
