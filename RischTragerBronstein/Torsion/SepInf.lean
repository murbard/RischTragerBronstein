import RischTragerBronstein.Torsion.ValidExist
import RischTragerBronstein.Torsion.MobCurve

/-!
# Separability at infinity

The curve at infinity `F̃(u, W) = u^{kn} F(1/u, W/uᵏ)` (`invB F k (kn)`) is separable over `F(u)`
as soon as `F` is separable over `F(x)`: over Laurent series,
`F̃(t, tᵏ Y) = t^{kn} F(t⁻¹, Y)` (`invB_scale`), and separability survives the rescaling
`Y ↦ c Y` (`sep_comp_scale`). **`resultant_invB_ne_zero`**: `Res(F, F_Y) ≠ 0` gives
`Res(F̃, F̃_W) ≠ 0`. **`hsepI_of_shapeOK`**: the Bézout identity at infinity needed by
`exists_valid` follows from the shape conditions, so separability at infinity is no longer a
hypothesis.
-/

open Polynomial

namespace Curves

open CPoly Sup Differential

section Scale

variable {L : Type*} [Field L]

lemma coeff_comp_C_mul_X (p : L[X]) (c : L) (i : ℕ) :
    (p.comp (C c * X)).coeff i = c ^ i * p.coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, coeff_add, hp, hq, mul_add]
  | monomial m a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc,
      ← C_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

/-- Separability survives the rescaling `Y ↦ c Y`. -/
lemma sep_comp_scale (p : L[X]) (hp : p.Separable) (c : L) (hc : c ≠ 0) :
    (p.comp (C c * X)).Separable := by
  obtain ⟨a, b, hab⟩ := hp
  refine ⟨a.comp (C c * X), C c⁻¹ * b.comp (C c * X), ?_⟩
  rw [derivative_comp, derivative_C_mul_X]
  have e : C c⁻¹ * b.comp (C c * X) * (C c * (derivative p).comp (C c * X)) =
      b.comp (C c * X) * (derivative p).comp (C c * X) := by
    rw [show C c⁻¹ * b.comp (C c * X) * (C c * (derivative p).comp (C c * X)) =
        (C c⁻¹ * C c) * (b.comp (C c * X) * (derivative p).comp (C c * X)) by ring, ← C_mul,
      inv_mul_cancel₀ hc, C_1, one_mul]
  rw [e, ← mul_comp, ← mul_comp, ← add_comp, hab, one_comp]

variable [CharZero L]

lemma separable_of_resultant_ne_zero (p : L[X]) (n : ℕ) (hmon : p.Monic) (hn : p.natDegree = n)
    (h : resultant p (derivative p) n (n - 1) ≠ 0) : p.Separable := by
  have h' : resultant p (derivative p) ≠ 0 := by
    rw [natDegree_derivative, hn]; exact h
  by_contra hs
  exact h' (resultant_eq_zero_iff.mpr ⟨Or.inl hmon.ne_zero, hs⟩)

lemma resultant_ne_zero_of_separable (p : L[X]) (n : ℕ) (hn : p.natDegree = n)
    (hs : p.Separable) : resultant p (derivative p) n (n - 1) ≠ 0 := by
  have := resultant_ne_zero p _ hs
  rwa [natDegree_derivative, hn] at this

end Scale

section Inf

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- **`Res(F, F_Y) ≠ 0` gives `Res(F̃, F̃_W) ≠ 0`** for the curve at infinity. -/
theorem resultant_invB_ne_zero (Fc : BPoly F) (n k : ℕ) (hmon : (toB Fc).Monic)
    (hn : (toB Fc).natDegree = n) (hInv : InvOK k (k * n) 0 Fc)
    (hmon' : (toB (invB Fc k (k * n))).Monic) (hn' : (toB (invB Fc k (k * n))).natDegree = n)
    (hR : resultant (toB Fc) (derivative (toB Fc)) n (n - 1) ≠ 0) :
    resultant (toB (invB Fc k (k * n))) (derivative (toB (invB Fc k (k * n)))) n (n - 1) ≠ 0 := by
  set G := toB Fc with hG
  set Gi := toB (invB Fc k (k * n)) with hGi
  set φx : F[X] →+* LaurentSeries F := infSub (C := F) (K := F) 1 with hφx
  set φu : F[X] →+* LaurentSeries F := branchSub (C := F) (K := F) 1 0 with hφu
  haveI : CharZero (LaurentSeries F) := charZero_of_injective_ringHom (f := HahnSeries.C)
    HahnSeries.C_injective
  set t : LaurentSeries F := HahnSeries.single (1 : ℤ) (1 : F) with ht
  have ht0 : t ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  have htp : ∀ M : ℕ, t ^ M = HahnSeries.single (M : ℤ) (1 : F) := fun M ↦ by
    rw [ht, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  have hGi' : Gi = invP G k (k * n) := toB_invB Fc k (k * n) hInv
  -- the coefficient identity `F̃(t, tᵏ Y) = t^{kn} F(t⁻¹, Y)`
  have hid : (Gi.map φu).comp (C (t ^ k) * X) = C (t ^ (k * n)) * G.map φx := by
    ext1 i
    rw [coeff_comp_C_mul_X, coeff_map, coeff_C_mul, coeff_map, hGi', coeff_invP]
    by_cases hi : i ≤ n
    · set M := k * n - k * i with hM
      have hki : k * i ≤ k * n := Nat.mul_le_mul_left _ hi
      have hdeg : (G.coeff i).natDegree ≤ M := by
        by_cases hil : i < Fc.length
        · have h1 := hInv i hil
          rw [zero_add] at h1
          refine natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ ?_
          rw [hG, coeff_toB, coeff_toPoly, List.getD_eq_default _ _ (by
            have : M < j := by exact_mod_cast hj
            omega)]
        · rw [hG, coeff_toB, List.getD_eq_default _ _ (by omega), toPoly_nil, natDegree_zero]
          exact Nat.zero_le _
      have e := infSub_reflect (K := F) 1 (G.coeff i) M hdeg
      rw [← hφx, ← hφu] at e
      have e2 : φu (reflect M (G.coeff i)) = φx (G.coeff i) * t ^ M := by
        rw [e, mul_assoc, htp, HahnSeries.single_mul_single, one_mul]
        simp
      rw [e2, ← pow_mul, show t ^ (k * i) * (φx (G.coeff i) * t ^ M) =
        φx (G.coeff i) * (t ^ (k * i) * t ^ M) by ring, ← pow_add,
        show k * i + M = k * n by omega]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), reflect_zero, map_zero, map_zero, mul_zero,
        mul_zero]
  -- separability
  have hsepG : (G.map φx).Separable := by
    refine separable_of_resultant_ne_zero _ n (hmon.map _) (by rw [hmon.natDegree_map, hn]) ?_
    rw [derivative_map, resultant_map_map]
    exact (map_ne_zero_iff _ (infSub_injective 1 one_pos)).mpr hR
  have hq : (C (t ^ (k * n)) * G.map φx).Separable :=
    Separable.unit_mul (isUnit_C.mpr (IsUnit.mk0 _ (pow_ne_zero _ ht0))) hsepG
  have hp : Gi.map φu = (C (t ^ (k * n)) * G.map φx).comp (C (t ^ k)⁻¹ * X) := by
    rw [← hid, comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ (pow_ne_zero _ ht0), C_1, one_mul, comp_X]
  have hsp : (Gi.map φu).Separable := by
    rw [hp]; exact sep_comp_scale _ hq _ (inv_ne_zero (pow_ne_zero _ ht0))
  have := resultant_ne_zero_of_separable _ n (by rw [hmon'.natDegree_map, hn']) hsp
  rw [derivative_map, resultant_map_map] at this
  exact fun h ↦ this (by rw [h, map_zero])

end Inf

/-- `Res(F, F_Y) ≠ 0` from the shape conditions (`disc · D ≠ 0`). -/
theorem resultant_ne_zero_of_shapeOK (P0 : CurveProb ℚ) (hS : P0.shapeOK = true) :
    resultant (toB P0.Fc) (derivative (toB P0.Fc)) P0.n (P0.n - 1) ≠ 0 := by
  have hS' := hS
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩, h7⟩, -⟩, h9⟩, -⟩, -⟩ := hS'
  obtain ⟨hmon, hn, hk⟩ := shape_monic P0.Fc P0.n P0.k h2 h3 h7
  rw [← toPoly_discRC P0.Fc P0.n P0.k hmon hn hk]
  intro h0
  have hR0 : toPoly P0.R0 = 0 := by
    simp only [CurveProb.R0, toPoly_trim, CPoly.toPoly_mul, h0, zero_mul]
  rw [← trim_eq_nil_iff] at hR0
  rw [hR0] at h9
  simp at h9

/-- **Separability at infinity from the shape**: the Bézout identity for the curve at infinity. -/
theorem hsepI_of_shapeOK (P0 : CurveProb ℚ) (hS : P0.shapeOK = true) :
    ∃ (R : ℚ[X]) (A B : ℚ[X][X]), R ≠ 0 ∧ Polynomial.C R =
      A * toB (invB P0.Fc P0.k (P0.k * P0.n)) +
        B * derivative (toB (invB P0.Fc P0.k (P0.k * P0.n))) := by
  have hR := resultant_ne_zero_of_shapeOK P0 hS
  have hS' := hS
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hS'
  obtain ⟨hmon, hn⟩ := monic_of_shape P0.Fc P0.n h2 h3
  obtain ⟨hmonI, hnI⟩ := monic_of_shape (invB P0.Fc P0.k (P0.k * P0.n)) P0.n h4 h5
  have hInv : InvOK P0.k (P0.k * P0.n) 0 P0.Fc := fun j hj ↦ by
    have := h6 j hj; rw [zero_add]; omega
  have hRI := resultant_invB_ne_zero P0.Fc P0.n P0.k hmon hn hInv hmonI hnI hR
  set G := toB (invB P0.Fc P0.k (P0.k * P0.n))
  obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant G (derivative G)
    (m := P0.n) (n := P0.n - 1) (by rw [hnI])
    (by have := natDegree_derivative_le G; rw [hnI] at this; exact this) (Or.inl (by omega))
  exact ⟨_, p, q, hRI, by rw [← hpq]; ring⟩

end Curves
