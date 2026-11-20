import RischTragerBronstein.Mixed.KPDecideMain2

/-!
# Galois projection of Liouville forms on `yⁿ = p(x)` over a differential base

`S : SuperData C L` with `x′ = η ∈ C`, `ζ ∈ C` a primitive `n`-th root of unity. The automorphism
`σ = conj ζ` (`y ↦ ζ y`) of `C(x, y)` commutes with the derivation (`conj_deriv`). Averaging a
Liouville form `f = v′ + ∑ cᵢ uᵢ′/uᵢ` with the weights `ζ^{−jk}` (`fourier`) gives a Liouville form
for the `yʲ`-component of `f` (`proj_liouville`); for `j = 0` the logarithms are the norms, in
`C(x)` (`proj_liouville_zero`).
-/

open Polynomial IntermediateField

namespace Differential

namespace SuperData

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable (S : SuperData C L) (η : C) (hx : S.x′ = algebraMap C L η)

/-- The derivation of `C(x, y)`, on the subfield. -/
noncomputable def dT (w : C⟮S.x⟯⟮S.y⟯) : C⟮S.x⟯⟮S.y⟯ := ⟨(w : L)′, S.derivClosedXY' η hx _ w.2⟩

lemma coe_dT (w : C⟮S.x⟯⟮S.y⟯) : ((S.dT η hx w : C⟮S.x⟯⟮S.y⟯) : L) = (w : L)′ := rfl

lemma dT_add (u w : C⟮S.x⟯⟮S.y⟯) : S.dT η hx (u + w) = S.dT η hx u + S.dT η hx w :=
  Subtype.ext (by simp [coe_dT])

lemma dT_mul (u w : C⟮S.x⟯⟮S.y⟯) :
    S.dT η hx (u * w) = u * S.dT η hx w + w * S.dT η hx u :=
  Subtype.ext (by simp [coe_dT, Derivation.leibniz])

lemma dT_cst (c : C) : S.dT η hx (S.cst c) = S.cst c′ :=
  Subtype.ext (by
    rw [coe_dT]
    exact deriv_algebraMap (A := C) (B := L) c)

lemma dT_sum {ι : Type*} (t : Finset ι) (w : ι → C⟮S.x⟯⟮S.y⟯) :
    S.dT η hx (∑ i ∈ t, w i) = ∑ i ∈ t, S.dT η hx (w i) :=
  Subtype.ext (by simp [coe_dT, map_sum])

include hx in
/-- **`conj` commutes with the derivation.** -/
theorem conj_deriv (ζ : C) (hζ : ζ ^ S.n = 1) (w : C⟮S.x⟯⟮S.y⟯) :
    S.conj ζ hζ (S.dT η hx w) = S.dT η hx (S.conj ζ hζ w) := by
  letI := algebraAdjoinSimple (F := C) S.x
  have hζ' : ζ′ = 0 := LaurentSeries.deriv_root_of_unity S.hn hζ
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedX' η hx
  obtain ⟨w, hw⟩ := w
  induction hw using IntermediateField.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff] at hz
    subst hz
    -- `y′ = r y`
    have hrm := S.r_mem η hx
    set r := aeval S.x (mapCoeffs S.p + Polynomial.C η * derivative S.p) /
      ((S.n : L) * aeval S.x S.p) with hr
    have hy' : S.y′ = r * S.y := by rw [S.deriv_y' η hx, hr]; ring
    have e1 : S.dT η hx ⟨S.y, mem_adjoin_simple_self _ _⟩ =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨r, hrm⟩ * AdjoinSimple.gen C⟮S.x⟯ S.y :=
      Subtype.ext (by rw [coe_dT, hy']; rfl)
    have e2 : (⟨S.y, mem_adjoin_simple_self _ _⟩ : C⟮S.x⟯⟮S.y⟯) = AdjoinSimple.gen C⟮S.x⟯ S.y := rfl
    rw [e1, e2, map_mul, S.conj_algebraMap, S.conj_gen]
    apply Subtype.ext
    change (r : L) * (algebraMap C L ζ * S.y) = (algebraMap C L ζ * S.y)′
    rw [Derivation.leibniz, deriv_algebraMap, hζ', map_zero, smul_zero, add_zero, hy', smul_eq_mul]
    ring
  | algebraMap a =>
    have e1 : S.dT η hx ⟨algebraMap C⟮S.x⟯ L a, IntermediateField.algebraMap_mem _ a⟩ =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨(a : L)′, hcl _ a.2⟩ := rfl
    have e2 : (⟨algebraMap C⟮S.x⟯ L a, IntermediateField.algebraMap_mem _ a⟩ : C⟮S.x⟯⟮S.y⟯) =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a := rfl
    rw [e1, e2, S.conj_algebraMap, S.conj_algebraMap]
    rfl
  | add u v hu hv ihu ihv =>
    have e : (⟨u + v, add_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
    rw [e, S.dT_add, map_add, map_add, ihu, ihv, S.dT_add]
  | mul u v hu hv ihu ihv =>
    have e : (⟨u * v, mul_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [e, S.dT_mul, map_add, map_mul, map_mul, ihu, ihv, map_mul, S.dT_mul]
  | inv u hu ihu =>
    have e : (⟨u⁻¹, inv_mem hu⟩ : C⟮S.x⟯⟮S.y⟯) = (⟨u, hu⟩ : C⟮S.x⟯⟮S.y⟯)⁻¹ := rfl
    have hinv : ∀ z : C⟮S.x⟯⟮S.y⟯, S.dT η hx z⁻¹ = -(z⁻¹ ^ 2) * S.dT η hx z := fun z ↦
      Subtype.ext (by simp [coe_dT, Derivation.leibniz_inv])
    rw [e, hinv, map_mul, map_neg, map_pow, map_inv₀, ihu]
    exact (hinv _).symm

lemma dT_cst_mul (c : C) (hc : c′ = 0) (w : C⟮S.x⟯⟮S.y⟯) :
    S.dT η hx (S.cst c * w) = S.cst c * S.dT η hx w := by
  rw [S.dT_mul, S.dT_cst, hc, show S.cst 0 = 0 from Subtype.ext (by simp [cst]), mul_zero,
    add_zero]

include hx in
/-- A Liouville form is transported by `σ`. -/
lemma conj_liouville (ζ : C) (hζ : ζ ^ S.n = 1) {ι : Type*} (s : Finset ι) (c : ι → C)
    (U : ι → C⟮S.x⟯⟮S.y⟯) (V F : C⟮S.x⟯⟮S.y⟯)
    (heq : F = S.dT η hx V + ∑ i ∈ s, S.cst (c i) * (S.dT η hx (U i) * (U i)⁻¹)) :
    S.conj ζ hζ F = S.dT η hx (S.conj ζ hζ V) + ∑ i ∈ s, S.cst (c i) *
      (S.dT η hx (S.conj ζ hζ (U i)) * (S.conj ζ hζ (U i))⁻¹) := by
  rw [heq, map_add, map_sum, S.conj_deriv η hx]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_mul, map_inv₀, S.conj_cst, S.conj_deriv η hx]

include hx in
/-- **The Galois projection of a Liouville form** onto the `yʲ`-component. -/
theorem proj_liouville (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) {ι : Type*} (s : Finset ι)
    (c : ι → C) (hc : ∀ i, (c i)′ = 0) (U : ι → C⟮S.x⟯⟮S.y⟯) (V F : C⟮S.x⟯⟮S.y⟯)
    (heq : F = S.dT η hx V + ∑ i ∈ s, S.cst (c i) * (S.dT η hx (U i) * (U i)⁻¹))
    (a : Fin S.n → C⟮S.x⟯)
    (hFa : F = ∑ k : Fin S.n, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a k) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (k : ℕ)) (j : Fin S.n) :
    algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a j) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (j : ℕ) =
      S.dT η hx (S.cst ((S.n : C)⁻¹) * ∑ k : Fin S.n, S.cst ((ζ ^ (k : ℕ)) ^ (S.n - j)) *
        S.conj (ζ ^ (k : ℕ)) (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) V) +
      ∑ ki ∈ (Finset.univ : Finset (Fin S.n)) ×ˢ s,
        S.cst ((S.n : C)⁻¹ * (ζ ^ (ki.1 : ℕ)) ^ (S.n - j) * c ki.2) *
          (S.dT η hx (S.conj (ζ ^ (ki.1 : ℕ))
            (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (U ki.2)) *
           (S.conj (ζ ^ (ki.1 : ℕ))
            (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (U ki.2))⁻¹) := by
  have hpow : ∀ k : ℕ, (ζ ^ k) ^ S.n = 1 := fun k ↦ by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hwc : ∀ k : ℕ, ((ζ ^ k) ^ (S.n - j))′ = 0 := fun k ↦
    LaurentSeries.deriv_root_of_unity S.hn (by
      rw [← pow_mul, mul_comm, pow_mul, hpow k, one_pow])
  have hn0 : (S.n : C) ≠ 0 := by exact_mod_cast S.hn.ne'
  have hnc : ((S.n : C)⁻¹)′ = 0 := by
    rw [Derivation.leibniz_inv, Derivation.map_natCast, smul_zero]
  have hfour := S.fourier ζ hζ a j
  rw [← hFa] at hfour
  simp_rw [S.conj_liouville η hx _ (hpow _) s c U V F heq] at hfour
  -- divide by `n`
  have hn : S.cst ((S.n : C)⁻¹) * (S.n : C⟮S.x⟯⟮S.y⟯) = 1 := by
    rw [← S.cst_natCast, ← S.cst_mul, inv_mul_cancel₀ hn0]
    exact Subtype.ext (by simp [cst])
  calc algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a j) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (j : ℕ)
      = S.cst ((S.n : C)⁻¹) * ((S.n : C⟮S.x⟯⟮S.y⟯) * (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a j) *
          AdjoinSimple.gen C⟮S.x⟯ S.y ^ (j : ℕ))) := by rw [← mul_assoc, hn, one_mul]
    _ = _ := by
      rw [← hfour, S.dT_cst_mul η hx _ hnc, S.dT_sum η hx, Finset.sum_product]
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [S.dT_cst_mul η hx _ (hwc k)]
      · refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
        rw [S.cst_mul, S.cst_mul]
        ring

end SuperData

end Differential
