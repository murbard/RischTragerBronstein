import RischTragerBronstein.Mixed.RdeLocalLog
import RischTragerBronstein.Mixed.RdeBounds
import RischTragerBronstein.Algebraic.LocalExpansion
import RischTragerBronstein.Algebraic.SuperAbel

/-!
# Pole bounds for the Risch equation with a logarithmic part, on a curve

For `z′ + (h′ + ∑ⱼ cⱼ uⱼ′/uⱼ) z = w` in `C⟮x⟯⟮y⟯` with `cⱼ ∈ ℚ`, `|cⱼ| ≤ kⱼ`, and representations
`uⱼ Qⱼ = Wⱼ`, `uⱼ⁻¹ Q'ⱼ = W'ⱼ` (`Qⱼ, Q'ⱼ ∈ C[x]`):

* `rde_branch_log`: along a branch, `ord z ≥ min(0, ord(w · dX̂/dT) + 1, −B)` whenever the residue
  `∑ cⱼ ord uⱼ` of the logarithmic part has absolute value `≤ B`;
* `ord_branch_le`: along a finite branch `|ord uⱼ| ≤ N (mult_a Qⱼ + mult_a Q'ⱼ)`; above infinity
  `|ord uⱼ| ≤ N · max(D_Wⱼ, D_W'ⱼ)`.

So the only change to the exact case is a larger denominator in `x` and a larger degree bound —
no computation of places is needed.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Bounds

variable {K : Type*} [Field K] [CharZero K]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- A lower bound on a non-zero series bounds its order. -/
lemma order_ge_of_lowerBd {z : LaurentSeries K} (hz : z ≠ 0) {m : ℤ} (h : LowerBd z m) :
    m ≤ z.order := by
  by_contra hlt
  push Not at hlt
  exact HahnSeries.coeff_order_eq_zero.not.mpr hz (h _ hlt)

/-- **The Risch equation with a logarithmic part along a branch.** -/
lemma rde_branch_log (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (Xh : LaurentSeries K) (hX : LaurentSeries.derivation Xh ≠ 0)
    (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (z h w : C⟮S.x⟯⟮S.y⟯)
    (s : Finset ℕ) (c : ℕ → ℚ) (u : ℕ → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i ∈ s, u i ≠ 0)
    (hE : (z : L)′ + ((h : L)′ + ∑ i ∈ s, (c i : L) * logDeriv (u i : L)) * z = w) (b : ℤ)
    (hw : LowerBd (S.embG g hg Y hY w * LaurentSeries.derivation Xh) b) (B : ℕ)
    (hB : ∑ i ∈ s, |c i| * |((S.embG g hg Y hY (u i)).order : ℚ)| ≤ B) :
    LowerBd (S.embG g hg Y hY z) (min (min 0 (b + 1)) (-(B : ℤ))) := by
  set φ := S.embG g hg Y hY
  have hφ0 : ∀ i ∈ s, φ (u i) ≠ 0 := fun i hi ↦ (map_ne_zero φ).mpr (hu i hi)
  have hz := S.embG_derivG Xh hX g hg hgX hC hx Y hY z z.2
  have hh := S.embG_derivG Xh hX g hg hgX hC hx Y hY h h.2
  have hui : ∀ i, φ ⟨(u i : L)′, S.derivClosedXY hC hx _ (u i).2⟩ =
      SuperData.deltaX Xh (φ (u i)) := fun i ↦
    S.embG_derivG Xh hX g hg hgX hC hx Y hY (u i) (u i).2
  have hδ : ∀ F : LaurentSeries K, SuperData.deltaX Xh F * LaurentSeries.derivation Xh =
      LaurentSeries.derivation F := fun F ↦ by
    rw [SuperData.deltaX_apply]; field_simp
  -- the equation inside the function field
  set lg : C⟮S.x⟯⟮S.y⟯ := ∑ i ∈ s, (c i : C⟮S.x⟯⟮S.y⟯) *
    (⟨(u i : L)′, S.derivClosedXY hC hx _ (u i).2⟩ / u i) with hlg
  have hlgL : (lg : L) = ∑ i ∈ s, (c i : L) * logDeriv (u i : L) := by
    rw [hlg, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_div, logDeriv]
    simp
  have hE' : (⟨(z : L)′, S.derivClosedXY hC hx _ z.2⟩ : C⟮S.x⟯⟮S.y⟯) +
      (⟨(h : L)′, S.derivClosedXY hC hx _ h.2⟩ + lg) * z = w :=
    Subtype.ext (by rw [IntermediateField.coe_add, IntermediateField.coe_mul,
      IntermediateField.coe_add, hlgL]; exact hE)
  have h1 := congrArg φ hE'
  rw [map_add, map_mul, map_add, hz, hh] at h1
  -- the logarithmic part along the branch
  set R : LaurentSeries K := ∑ i ∈ s, HahnSeries.C ((c i : ℚ) : K) *
    (LaurentSeries.derivation (φ (u i)) / φ (u i)) with hR
  have hlgφ : φ lg * LaurentSeries.derivation Xh = R := by
    rw [hlg, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_div₀, hui, map_ratCast]
    have : ((c i : ℚ) : LaurentSeries K) = HahnSeries.C ((c i : ℚ) : K) := by
      rw [map_ratCast]
    rw [this, mul_assoc, div_mul_eq_mul_div, hδ]
  have hRb : LowerBd R (-1) := by
    rw [hR]
    refine lowerBd_sum _ _ fun i hi ↦ ?_
    have := (lowerBd_C ((c i : ℚ) : K)).mul (lowerBd_logDeriv (φ (u i)) (hφ0 i hi))
    simpa [LaurentSeries.derivation_apply] using this
  have hRres : R.coeff (-1) = ∑ i ∈ s, ((c i : ℚ) : K) * ((φ (u i)).order : K) := by
    change LaurentSeries.res R = _
    rw [hR, Differential.SuperData.res_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Differential.SuperData.res_C_mul, LaurentSeries.derivation_apply,
      LaurentSeries.res_logDeriv _ (hφ0 i hi)]
  refine rde_local_lowerBd_log (φ z) (φ h) R _ ?_ b hw hRb B ?_
  · rw [← h1]
    simp only [Subtype.coe_eta]
    rw [← hlgφ, SuperData.deltaX_apply, SuperData.deltaX_apply]
    field_simp
    ring
  · intro m hm h0
    rw [hRres] at h0
    have hq : ((m : ℚ) + ∑ i ∈ s, c i * ((φ (u i)).order : ℚ) : ℚ) = 0 := by
      have : (((m : ℚ) + ∑ i ∈ s, c i * ((φ (u i)).order : ℚ) : ℚ) : K) = 0 := by
        push_cast; exact h0
      exact_mod_cast this
    have habs : |∑ i ∈ s, c i * ((φ (u i)).order : ℚ)| ≤ B := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ abs_mul _ _)) hB
    have hmq : ((m : ℤ) : ℚ) < -(B : ℚ) := by exact_mod_cast hm
    have : |(m : ℚ)| ≤ B := by
      rw [show (m : ℚ) = -∑ i ∈ s, c i * ((φ (u i)).order : ℚ) by linarith, abs_neg]
      exact habs
    have := abs_le.mp this
    linarith

/-- The order of the inverse. -/
lemma order_inv_eq {z : LaurentSeries K} (hz : z ≠ 0) : (z⁻¹).order = -z.order := by
  have h := HahnSeries.order_mul hz (inv_ne_zero hz)
  rw [mul_inv_cancel₀ hz, HahnSeries.order_one] at h
  omega

/-- **Orders of a function along a branch**, from lower bounds for it and its inverse. -/
lemma abs_order_le {z : LaurentSeries K} (hz : z ≠ 0) {A A' : ℕ} (h1 : LowerBd z (-(A : ℤ)))
    (h2 : LowerBd z⁻¹ (-(A' : ℤ))) : |(z.order : ℚ)| ≤ (A + A' : ℕ) := by
  have e1 := order_ge_of_lowerBd hz h1
  have e2 := order_ge_of_lowerBd (inv_ne_zero hz) h2
  rw [order_inv_eq hz] at e2
  have : |z.order| ≤ ((A + A' : ℕ) : ℤ) := by
    rw [abs_le]; push_cast; constructor <;> omega
  exact_mod_cast this

/-- Root multiplicities of a product of powers. -/
lemma rootMultiplicity_prod_pow (s : Finset ℕ) (f : ℕ → C[X]) (k : ℕ → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) (a : K) :
    ((∏ i ∈ s, f i ^ k i).map (algebraMap C K)).rootMultiplicity a =
      ∑ i ∈ s, k i * ((f i).map (algebraMap C K)).rootMultiplicity a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Polynomial.map_mul, Polynomial.map_pow]
    have h1 : ((f j).map (algebraMap C K)) ^ k j ≠ 0 :=
      pow_ne_zero _ ((Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr
        (hf j (Finset.mem_insert_self j s)))
    have h2 : (∏ i ∈ s, f i ^ k i).map (algebraMap C K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr
        (Finset.prod_ne_zero_iff.mpr fun i hi ↦ pow_ne_zero _ (hf i (Finset.mem_insert_of_mem hi)))
    rw [rootMultiplicity_mul (mul_ne_zero h1 h2), ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]
    congr 1
    clear ih h2
    induction k j with
    | zero => simp
    | succ n ihn =>
      rw [pow_succ, rootMultiplicity_mul (by
        exact mul_ne_zero (pow_ne_zero _ ((Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr
          (hf j (Finset.mem_insert_self j s))))
          ((Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr
          (hf j (Finset.mem_insert_self j s)))), ihn]
      ring

variable [IsAlgClosed K]

set_option maxHeartbeats 1000000 in
/-- **Finite pole bounds of solutions** with a logarithmic part: the denominator is enlarged by the
denominators `Qᵢ Q'ᵢ` of `uᵢ` and `uᵢ⁻¹`, to the power `kᵢ ≥ |cᵢ|`. -/
theorem rdeL_poleBoundFin (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (z h w : C⟮S.x⟯⟮S.y⟯)
    (s : Finset ℕ) (c : ℕ → ℚ) (u : ℕ → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i ∈ s, u i ≠ 0)
    (hE : (z : L)′ + ((h : L)′ + ∑ i ∈ s, (c i : L) * logDeriv (u i : L)) * z = w)
    (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0) (hw : (w : L) * aeval S.x Q = S.evXY W)
    (Wu Wi : ℕ → C[X][X]) (Qu Qi : ℕ → C[X]) (hQu : ∀ i ∈ s, Qu i ≠ 0) (hQi : ∀ i ∈ s, Qi i ≠ 0)
    (hru : ∀ i ∈ s, (u i : L) * aeval S.x (Qu i) = S.evXY (Wu i))
    (hri : ∀ i ∈ s, (u i : L)⁻¹ * aeval S.x (Qi i) = S.evXY (Wi i))
    (k : ℕ → ℕ) (hk : ∀ i ∈ s, |c i| ≤ k i) :
    S.PoleBoundFin K z (Q * ∏ i ∈ s, (Qu i * Qi i) ^ k i) := by
  intro a N hN r hsplit kk
  have hN' := Nat.pos_of_ne_zero hN
  set φ := S.embG (branchSub N a) (branchSub_injective N hN' a) (r kk)
    (S.root_of_split _ r hsplit kk) with hφ
  set mQ : ℕ → ℕ := fun i ↦ ((Qu i * Qi i).map (algebraMap C K)).rootMultiplicity a with hmQ
  have hf : ∀ i ∈ s, Qu i * Qi i ≠ 0 := fun i hi ↦ mul_ne_zero (hQu i hi) (hQi i hi)
  -- orders of the `uᵢ`
  have hord : ∀ i ∈ s, |((φ (u i)).order : ℚ)| ≤ (N * mQ i : ℕ) := by
    intro i hi
    have h1 := S.lowerBd_fin N hN' a (r kk) (S.root_of_split _ r hsplit kk) (u i) (Wu i) (Qu i)
      (hQu i hi) (hru i hi)
    have h2 := S.lowerBd_fin N hN' a (r kk) (S.root_of_split _ r hsplit kk) (u i)⁻¹ (Wi i) (Qi i)
      (hQi i hi) (by rw [IntermediateField.coe_inv]; exact hri i hi)
    rw [map_inv₀] at h2
    have h3 := abs_order_le ((map_ne_zero φ).mpr (hu i hi)) h1 h2
    have hm : ((Qu i * Qi i).map (algebraMap C K)).rootMultiplicity a =
        ((Qu i).map (algebraMap C K)).rootMultiplicity a +
          ((Qi i).map (algebraMap C K)).rootMultiplicity a := by
      rw [Polynomial.map_mul, rootMultiplicity_mul (by
        rw [← Polynomial.map_mul]
        exact (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr (hf i hi))]
    refine h3.trans (le_of_eq ?_)
    simp only [hmQ, hm]
    push_cast; ring
  set B : ℕ := ∑ i ∈ s, k i * (N * mQ i) with hB
  have hBq : ∑ i ∈ s, |c i| * |((φ (u i)).order : ℚ)| ≤ B := by
    rw [hB]; push_cast
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have := hord i hi
    push_cast at this
    exact mul_le_mul (hk i hi) this (abs_nonneg _) (by positivity)
  have hwb := S.lowerBd_fin N hN' a (r kk) (S.root_of_split _ r hsplit kk) w W Q hQ hw
  have hD := lowerBd_single ((N : ℤ) - 1) (N : K)
  rw [← SuperData.derivation_branchX N hN' a] at hD
  have := S.rde_branch_log hC hx _ (hX_fin N hN' a) (branchSub N a) (branchSub_injective N hN' a)
    (fun P ↦ by rw [SuperData.branchSub_eq_subst]) (r kk) (S.root_of_split _ r hsplit kk) z h w
    s c u hu hE _ (hwb.mul hD) B hBq
  refine this.mono ?_
  have hmul : ((Q * ∏ i ∈ s, (Qu i * Qi i) ^ k i).map (algebraMap C K)).rootMultiplicity a =
      (Q.map (algebraMap C K)).rootMultiplicity a + ∑ i ∈ s, k i * mQ i := by
    rw [Polynomial.map_mul, rootMultiplicity_mul (by
      rw [← Polynomial.map_mul]
      exact (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr
        (mul_ne_zero hQ (Finset.prod_ne_zero_iff.mpr fun i hi ↦ pow_ne_zero _ (hf i hi)))),
      rootMultiplicity_prod_pow s _ k hf a]
  rw [hmul]
  have e : (B : ℤ) = (N : ℤ) * ((∑ i ∈ s, k i * mQ i : ℕ) : ℤ) := by
    rw [hB]; push_cast; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_; ring
  have h0 : (0 : ℤ) ≤ (N : ℤ) * ((Q.map (algebraMap C K)).rootMultiplicity a : ℤ) := by positivity
  have hNS : (0 : ℤ) ≤ (N : ℤ) * ((∑ i ∈ s, k i * mQ i : ℕ) : ℤ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  push_cast at hNS
  refine le_min (le_min ?_ ?_) ?_
  · push_cast; nlinarith [e]
  · push_cast; nlinarith [e]
  · rw [e]; push_cast; nlinarith

set_option maxHeartbeats 1000000 in
/-- **Pole bounds of solutions above infinity** with a logarithmic part. -/
theorem rdeL_poleBoundInf (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (z h w : C⟮S.x⟯⟮S.y⟯)
    (s : Finset ℕ) (c : ℕ → ℚ) (u : ℕ → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i ∈ s, u i ≠ 0)
    (hE : (z : L)′ + ((h : L)′ + ∑ i ∈ s, (c i : L) * logDeriv (u i : L)) * z = w)
    (kF : ℕ) (hkF : ∀ i, (S.F.coeff i).natDegree ≤ kF)
    (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0) (hw : (w : L) * aeval S.x Q = S.evXY W) (DW : ℕ)
    (hDW : ∀ i, W.coeff i ≠ 0 → (W.coeff i).natDegree + kF * i ≤ DW)
    (Wu Wi : ℕ → C[X][X]) (Qu Qi : ℕ → C[X]) (hQu : ∀ i ∈ s, Qu i ≠ 0) (hQi : ∀ i ∈ s, Qi i ≠ 0)
    (hru : ∀ i ∈ s, (u i : L) * aeval S.x (Qu i) = S.evXY (Wu i))
    (hri : ∀ i ∈ s, (u i : L)⁻¹ * aeval S.x (Qi i) = S.evXY (Wi i))
    (Du Di : ℕ → ℕ)
    (hDu : ∀ i ∈ s, ∀ j, (Wu i).coeff j ≠ 0 → ((Wu i).coeff j).natDegree + kF * j ≤ Du i)
    (hDi : ∀ i ∈ s, ∀ j, (Wi i).coeff j ≠ 0 → ((Wi i).coeff j).natDegree + kF * j ≤ Di i)
    (k : ℕ → ℕ) (hk : ∀ i ∈ s, |c i| ≤ k i) :
    S.PoleBoundInf K z (DW + 1 - Q.natDegree + ∑ i ∈ s, k i * (Du i + Di i)) := by
  intro N hN r hsplit kk
  have hN' := Nat.pos_of_ne_zero hN
  set φ := S.embG (infSub N) (infSub_injective N hN') (r kk) (S.root_of_split _ r hsplit kk)
    with hφ
  have hord : ∀ i ∈ s, |((φ (u i)).order : ℚ)| ≤ (N * Du i + N * Di i : ℕ) := by
    intro i hi
    have h1 := S.lowerBd_inf N hN' kF hkF (r kk) (S.root_of_split _ r hsplit kk) (u i) (Wu i)
      (Qu i) (hQu i hi) (hru i hi) (Du i) (hDu i hi)
    have h2 := S.lowerBd_inf N hN' kF hkF (r kk) (S.root_of_split _ r hsplit kk) (u i)⁻¹ (Wi i)
      (Qi i) (hQi i hi) (by rw [IntermediateField.coe_inv]; exact hri i hi) (Di i) (hDi i hi)
    rw [map_inv₀] at h2
    refine abs_order_le ((map_ne_zero φ).mpr (hu i hi)) (h1.mono ?_) (h2.mono ?_)
    · have : (0 : ℤ) ≤ ((N * (Qu i).natDegree : ℕ) : ℤ) := by positivity
      omega
    · have : (0 : ℤ) ≤ ((N * (Qi i).natDegree : ℕ) : ℤ) := by positivity
      omega
  set B : ℕ := ∑ i ∈ s, k i * (N * Du i + N * Di i) with hB
  have hBq : ∑ i ∈ s, |c i| * |((φ (u i)).order : ℚ)| ≤ B := by
    rw [hB]; push_cast
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have := hord i hi
    push_cast at this
    exact mul_le_mul (hk i hi) this (abs_nonneg _) (by positivity)
  have hwb := S.lowerBd_inf N hN' kF hkF (r kk) (S.root_of_split _ r hsplit kk) w W Q hQ hw DW hDW
  have hD := lowerBd_single (-(N : ℤ) - 1) (-(N : K))
  rw [← SuperData.derivation_infX N] at hD
  have := S.rde_branch_log hC hx _ (hX_inf N hN') (infSub N) (infSub_injective N hN')
    (fun P ↦ by rw [SuperData.infSub_eq_subst]) (r kk) (S.root_of_split _ r hsplit kk) z h w
    s c u hu hE _ (hwb.mul hD) B hBq
  refine this.mono ?_
  have e : (B : ℤ) = (N : ℤ) * ((∑ i ∈ s, k i * (Du i + Di i) : ℕ) : ℤ) := by
    rw [hB]; push_cast; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_; ring
  have h0 : (0 : ℤ) ≤ (N : ℤ) := by positivity
  have hS0 : (0 : ℤ) ≤ ((∑ i ∈ s, k i * (Du i + Di i) : ℕ) : ℤ) := by positivity
  have hNS : (0 : ℤ) ≤ (N : ℤ) * ((∑ i ∈ s, k i * (Du i + Di i) : ℕ) : ℤ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  push_cast at hNS
  refine le_min (le_min ?_ ?_) ?_
  · have : (0 : ℤ) ≤ ((DW + 1 - Q.natDegree : ℕ) : ℤ) := by positivity
    push_cast [Nat.cast_add] at *
    nlinarith
  · rcases le_total (DW + 1) Q.natDegree with hle | hle
    · rw [Nat.sub_eq_zero_of_le hle]
      push_cast
      nlinarith
    · push_cast [Nat.cast_sub hle]
      nlinarith
  · rw [e]; push_cast
    have : (0 : ℤ) ≤ ((DW + 1 - Q.natDegree : ℕ) : ℤ) := by positivity
    nlinarith

/-- **The ansatz with a logarithmic part.** -/
theorem rdeL_ansatz (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (z h w : C⟮S.x⟯⟮S.y⟯)
    (s : Finset ℕ) (c : ℕ → ℚ) (u : ℕ → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i ∈ s, u i ≠ 0)
    (hE : (z : L)′ + ((h : L)′ + ∑ i ∈ s, (c i : L) * logDeriv (u i : L)) * z = w)
    (kF : ℕ) (hkF : ∀ i, (S.F.coeff i).natDegree ≤ kF)
    (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0) (hw : (w : L) * aeval S.x Q = S.evXY W) (DW : ℕ)
    (hDW : ∀ i, W.coeff i ≠ 0 → (W.coeff i).natDegree + kF * i ≤ DW)
    (Wu Wi : ℕ → C[X][X]) (Qu Qi : ℕ → C[X]) (hQu : ∀ i ∈ s, Qu i ≠ 0) (hQi : ∀ i ∈ s, Qi i ≠ 0)
    (hru : ∀ i ∈ s, (u i : L) * aeval S.x (Qu i) = S.evXY (Wu i))
    (hri : ∀ i ∈ s, (u i : L)⁻¹ * aeval S.x (Qi i) = S.evXY (Wi i))
    (Du Di : ℕ → ℕ)
    (hDu : ∀ i ∈ s, ∀ j, (Wu i).coeff j ≠ 0 → ((Wu i).coeff j).natDegree + kF * j ≤ Du i)
    (hDi : ∀ i ∈ s, ∀ j, (Wi i).coeff j ≠ 0 → ((Wi i).coeff j).natDegree + kF * j ≤ Di i)
    (k : ℕ → ℕ) (hk : ∀ i ∈ s, |c i| ≤ k i) :
    ∃ Wz : C[X][X], Wz.natDegree < S.F.natDegree ∧
      (∀ j, (Wz.coeff j).natDegree ≤ (Q * ∏ i ∈ s, (Qu i * Qi i) ^ k i).natDegree +
        (DW + 1 - Q.natDegree + ∑ i ∈ s, k i * (Du i + Di i)) +
        ((S.F.natDegree - 1) * (S.F.natDegree - 1) + (S.F.natDegree - 1)) * S.degB) ∧
      (z : L) * aeval S.x (S.discR * (Q * ∏ i ∈ s, (Qu i * Qi i) ^ k i)) = S.evXY Wz :=
  S.ansatz (K := AlgebraicClosure C) z _ (mul_ne_zero hQ (Finset.prod_ne_zero_iff.mpr
      fun i hi ↦ pow_ne_zero _ (mul_ne_zero (hQu i hi) (hQi i hi)))) _
    (S.rdeL_poleBoundFin hC hx z h w s c u hu hE W Q hQ hw Wu Wi Qu Qi hQu hQi hru hri k hk)
    (S.rdeL_poleBoundInf hC hx z h w s c u hu hE kF hkF W Q hQ hw DW hDW Wu Wi Qu Qi hQu hQi hru
      hri Du Di hDu hDi k hk)

end CurveData

end Bounds

end Curves
