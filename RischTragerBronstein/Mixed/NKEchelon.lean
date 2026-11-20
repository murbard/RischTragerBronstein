import RischTragerBronstein.Mixed.NKInfStruct
import RischTragerBronstein.Curves.IntBasisInf

/-!
# Echelon integral bases at a single place at infinity

For a curve of weighted shape (a single place at infinity) the orders above infinity are the same
along every branch up to the factor `N/n`: `n · ord z = −N v(z)` (`exists_vInf`). So `InfOrd`
is read off one fixed branch (`infOrd_iff_ord`). Two elements of the same order have proportional
leading coefficients with a ratio in `C` (`exists_cancel`), so a reduced integral basis can be
transformed, by `wᵢ ↦ wᵢ − κ x^{rᵢ − rⱼ} wⱼ` (`rᵢ ≥ rⱼ`), into one whose rescaled elements
`x^{−rᵢ} wᵢ` have pairwise distinct orders (`exists_echelon`), and then scaled to leading
coefficients `γ^{j₀}` (`exists_echelon_normed`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

lemma order_ge_of_lowerBd {K : Type*} [Field K] {z : LaurentSeries K} (hz : z ≠ 0) {m : ℤ}
    (h : LowerBd z m) : m ≤ z.order := by
  by_contra hlt
  push Not at hlt
  exact (HahnSeries.coeff_order_eq_zero.not.mpr hz) (h _ hlt)

lemma lowerBd_of_order_ge {K : Type*} [Field K] {z : LaurentSeries K} {m : ℤ}
    (h : m ≤ z.order) : LowerBd z m := fun k hk ↦
  HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk h)

namespace CurveData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K]

variable (S : CurveData C L)

section Basic

/-- The order of `z` along a fixed branch above infinity. -/
noncomputable def ordR (N : ℕ) (hN : 0 < N) (ρ : LaurentSeries K)
    (hρ : (S.F.map (infSub N)).eval ρ = 0) (z : C⟮S.x⟯⟮S.y⟯) : ℤ :=
  (S.embG (infSub N) (infSub_injective N hN) ρ hρ z).order

/-- The rescaled element `x^{−rⱼ} wⱼ`. -/
noncomputable def wTil {m : ℕ} (w : Fin m → C⟮S.x⟯⟮S.y⟯) (r : Fin m → ℕ) (j : Fin m) :
    C⟮S.x⟯⟮S.y⟯ :=
  (S.polyE (X ^ r j))⁻¹ * w j

lemma infOrd_wTil {m : ℕ} (w : Fin m → C⟮S.x⟯⟮S.y⟯) (r : Fin m → ℕ) (j : Fin m)
    (h : S.InfOrd K (w j) (r j)) : S.InfOrd K (S.wTil w r j) 0 := by
  have := InfOrd.mul S (S.infOrd_inv_poly (K := K) (X ^ r j) (pow_ne_zero _ X_ne_zero)) h
  rw [natDegree_X_pow] at this
  exact InfOrd.mono S this (by omega)

lemma wTil_ne_zero {m : ℕ} (w : Fin m → C⟮S.x⟯⟮S.y⟯) (r : Fin m → ℕ) (j : Fin m) (h : w j ≠ 0) :
    S.wTil w r j ≠ 0 :=
  mul_ne_zero (inv_ne_zero (S.polyE_ne_zero _ (pow_ne_zero _ X_ne_zero))) h

end Basic

variable (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
  (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = d)
  (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < d * (n - i))
  (hcop : Nat.Coprime n d)
include hn hn0 ha0 hd hw hcop

/-- **The order above infinity is branch independent**: `n · ord z = −N v(z)`. -/
lemma exists_vInf (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0) :
    ∃ v : ℤ, ∀ (N : ℕ) (hN : 0 < N) (r : LaurentSeries K) (hr : (S.F.map (infSub N)).eval r = 0),
      S.embG (infSub N) (infSub_injective N hN) r hr z ≠ 0 ∧
        (n : ℤ) * (S.embG (infSub N) (infSub_injective N hN) r hr z).order = -((N : ℤ) * v) := by
  have hF1 : S.F ≠ 1 := fun h ↦ by rw [h, natDegree_one] at hn; omega
  obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt z hF1
  rw [hn] at hWn
  have hW0 : W ≠ 0 := by
    intro h0
    rw [h0, evXY, Polynomial.map_zero, eval_zero] at hWQ
    have hx0 : aeval S.x Q ≠ 0 := fun h ↦ hQ ((transcendental_iff.mp S.htr) Q h)
    exact hz (Subtype.ext (by simpa [hx0] using hWQ))
  refine ⟨(wtW n d W : ℤ) - n * Q.natDegree, fun N hN r hr ↦ ?_⟩
  obtain ⟨h1, h2, -⟩ := S.embG_lead_inf n d hn hn0 ha0 hd hw hcop N hN r hr z W Q hQ hWQ hW0 hWn
  exact ⟨h1, h2⟩

/-- **`InfOrd` along one branch.** -/
lemma infOrd_iff_ord (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K)
    (hr : r ∈ l) (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0) (k : ℤ) :
    S.InfOrd K z k ↔ -(k * N) ≤ (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
      (S.root_of_mem hl hr) z).order := by
  obtain ⟨v, hv⟩ := S.exists_vInf (K := K) n d hn hn0 ha0 hd hw hcop z hz
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  obtain ⟨h0, ho⟩ := hv N (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr)
  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  constructor
  · intro h
    exact order_ge_of_lowerBd h0 (h N hN l hl r hr)
  · intro h N' hN' l' hl' r' hr'
    obtain ⟨h0', ho'⟩ := hv N' (Nat.pos_of_ne_zero hN') r' (S.root_of_mem hl' hr')
    have hN'pos : (0 : ℤ) < N' := by exact_mod_cast Nat.pos_of_ne_zero hN'
    refine lowerBd_of_order_ge ?_
    have hvk : v ≤ n * k := by nlinarith
    nlinarith

omit [CharZero C] [CharZero L] [CharZero K] in
/-- The index `j₀` is determined by the weight modulo `n`. -/
lemma j0_unique (j1 j2 a1 a2 b1 b2 : ℕ) (hj1 : j1 < n) (hj2 : j2 < n)
    (h : (n * a1 + j1 * d : ℤ) - n * b1 = (n * a2 + j2 * d : ℤ) - n * b2) : j1 = j2 := by
  have hdvd : (n : ℤ) ∣ ((j1 : ℤ) - j2) * d :=
    ⟨(a2 : ℤ) - b2 - a1 + b1, by linear_combination h⟩
  have hcopZ : IsCoprime (n : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have h2 : (n : ℤ) ∣ (j1 : ℤ) - j2 := hcopZ.dvd_of_dvd_mul_right hdvd
  have h3 : (j1 : ℤ) - j2 = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h2 ?_
    rw [abs_lt]; constructor <;> omega
  omega

/-- **Same order, proportional leading terms**: if `z₁`, `z₂` have the same order along a branch
above infinity, then `z₁ − κ z₂` has a larger order (or vanishes) for some `κ ∈ C`, `κ ≠ 0`. -/
lemma exists_cancel (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0) (z1 z2 : C⟮S.x⟯⟮S.y⟯) (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0)
    (heq : (S.embG (infSub N) (infSub_injective N hN) r hr z1).order =
      (S.embG (infSub N) (infSub_injective N hN) r hr z2).order) :
    ∃ κ : C, κ ≠ 0 ∧ LowerBd (S.embG (infSub N) (infSub_injective N hN) r hr
      (z1 - S.polyE (Polynomial.C κ) * z2))
      ((S.embG (infSub N) (infSub_injective N hN) r hr z1).order + 1) := by
  have hF1 : S.F ≠ 1 := fun h ↦ by rw [h, natDegree_one] at hn; omega
  have hrep : ∀ z : C⟮S.x⟯⟮S.y⟯, z ≠ 0 → ∃ (W : C[X][X]) (Q : C[X]), Q ≠ 0 ∧
      (z : L) * aeval S.x Q = S.evXY W ∧ W ≠ 0 ∧ W.natDegree < n := by
    intro z hz
    obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt z hF1
    rw [hn] at hWn
    refine ⟨W, Q, hQ, hWQ, ?_, hWn⟩
    intro h0
    rw [h0, evXY, Polynomial.map_zero, eval_zero] at hWQ
    have hx0 : aeval S.x Q ≠ 0 := fun h ↦ hQ ((transcendental_iff.mp S.htr) Q h)
    exact hz (Subtype.ext (by simpa [hx0] using hWQ))
  obtain ⟨W1, Q1, hQ1, hWQ1, hW01, hWn1⟩ := hrep z1 hz1
  obtain ⟨W2, Q2, hQ2, hWQ2, hW02, hWn2⟩ := hrep z2 hz2
  obtain ⟨hE1, ho1, j1, hj1n, hj1, hwt1, hlc1⟩ :=
    S.embG_lead_inf n d hn hn0 ha0 hd hw hcop N hN r hr z1 W1 Q1 hQ1 hWQ1 hW01 hWn1
  obtain ⟨hE2, ho2, j2, hj2n, hj2, hwt2, hlc2⟩ :=
    S.embG_lead_inf n d hn hn0 ha0 hd hw hcop N hN r hr z2 W2 Q2 hQ2 hWQ2 hW02 hWn2
  set E1 := S.embG (infSub N) (infSub_injective N hN) r hr z1 with hE1d
  set E2 := S.embG (infSub N) (infSub_injective N hN) r hr z2 with hE2d
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  have hv : ((wtW n d W1 : ℤ) - n * Q1.natDegree) = (wtW n d W2 : ℤ) - n * Q2.natDegree := by
    rw [heq] at ho1
    have : (N : ℤ) * ((wtW n d W1 : ℤ) - n * Q1.natDegree) =
      N * ((wtW n d W2 : ℤ) - n * Q2.natDegree) := by linarith
    exact mul_left_cancel₀ hNpos.ne' this
  have hj12 : j1 = j2 := by
    refine S.j0_unique n d hn hn0 ha0 hd hw hcop j1 j2 (W1.coeff j1).natDegree (W2.coeff j2).natDegree
      Q1.natDegree Q2.natDegree hj1n hj2n ?_
    rw [hwt1, hwt2] at hv; push_cast at hv ⊢; exact hv
  subst hj12
  set β1 := (W1.coeff j1).leadingCoeff / Q1.leadingCoeff with hβ1
  set β2 := (W2.coeff j1).leadingCoeff / Q2.leadingCoeff with hβ2
  have hβ10 : β1 ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hj1) (leadingCoeff_ne_zero.mpr hQ1)
  have hβ20 : β2 ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hj2) (leadingCoeff_ne_zero.mpr hQ2)
  refine ⟨β1 / β2, div_ne_zero hβ10 hβ20, fun k hk ↦ ?_⟩
  rw [map_sub, map_mul, S.embG_polyX, SuperData.infSub_C, HahnSeries.coeff_sub,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  rcases lt_or_eq_of_le (Int.lt_add_one_iff.mp hk) with hk' | hk'
  · rw [HahnSeries.coeff_eq_zero_of_lt_order hk',
      HahnSeries.coeff_eq_zero_of_lt_order (heq ▸ hk'), mul_zero, sub_zero]
  · rw [hk', ← HahnSeries.leadingCoeff_eq, heq, ← HahnSeries.leadingCoeff_eq, hlc1, hlc2,
      ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hβ20, sub_self]

/-- **The window**: for an integral basis normal at infinity, `0 ≤ ord (x^{−rⱼ} wⱼ) < N`. -/
lemma ordR_wTil_window (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (ρ : LaurentSeries K)
    (hρl : ρ ∈ l) {m : ℕ} (w : Fin m → C⟮S.x⟯⟮S.y⟯) (r : Fin m → ℕ) (hw0 : ∀ j, w j ≠ 0)
    (hr : ∀ j, S.InfOrd K (w j) (r j)) (hred : S.Reduced K w r) (j : Fin m) :
    0 ≤ S.ordR N (Nat.pos_of_ne_zero hN) ρ (S.root_of_mem hl hρl) (S.wTil w r j) ∧
      S.ordR N (Nat.pos_of_ne_zero hN) ρ (S.root_of_mem hl hρl) (S.wTil w r j) < N := by
  classical
  have hz := S.wTil_ne_zero w r j (hw0 j)
  have hiff := fun k ↦ S.infOrd_iff_ord n d hn hn0 ha0 hd hw hcop N hN l hl ρ hρl (S.wTil w r j) hz k
  constructor
  · have := (hiff 0).mp (S.infOrd_wTil w r j (hr j))
    simpa [ordR] using this
  · by_contra hge
    push Not at hge
    have h1 : S.InfOrd K (S.wTil w r j) (-1) := (hiff (-1)).mpr (by simpa [ordR] using hge)
    have := hred (fun i ↦ if i = j then 1 else 0) (by
      have e : ∑ i, S.polyE (Polynomial.C (if i = j then (1 : C) else 0)) *
          ((S.polyE (X ^ r i))⁻¹ * w i) = S.wTil w r j := by
        rw [Finset.sum_eq_single j]
        · simp [wTil, S.polyE_one]
        · intro i _ hij; simp [hij, S.polyE_zero']
        · simp
      rw [e]; exact h1) j
    simp at this

/-- **The echelon descent**: a reduced integral basis can be transformed into one whose rescaled
elements have pairwise distinct orders along the branch. -/
theorem exists_echelon (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (ρ : LaurentSeries K)
    (hρl : ρ ∈ l) [IsAlgClosed K] {m' : ℕ} :
    ∀ (M : ℕ) (w : Fin m' → C⟮S.x⟯⟮S.y⟯) (r : Fin m' → ℕ), S.IBasis K w →
      (∀ j, S.InfOrd K (w j) (r j)) → S.Reduced K w r →
      ∑ j, ((N : ℤ) - S.ordR N (Nat.pos_of_ne_zero hN) ρ (S.root_of_mem hl hρl)
        (S.wTil w r j)).toNat = M →
      ∃ (w' : Fin m' → C⟮S.x⟯⟮S.y⟯) (r' : Fin m' → ℕ), S.IBasis K w' ∧
        (∀ j, S.InfOrd K (w' j) (r' j)) ∧ S.Reduced K w' r' ∧
        ∀ i j, S.ordR N (Nat.pos_of_ne_zero hN) ρ (S.root_of_mem hl hρl) (S.wTil w' r' i) =
          S.ordR N (Nat.pos_of_ne_zero hN) ρ (S.root_of_mem hl hρl) (S.wTil w' r' j) → i = j := by
  classical
  have hN0 := Nat.pos_of_ne_zero hN
  set hρ := S.root_of_mem hl hρl
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro w r hwB hr hred hM
  by_cases hdist : ∀ i j, S.ordR N hN0 ρ hρ (S.wTil w r i) = S.ordR N hN0 ρ hρ (S.wTil w r j) → i = j
  · exact ⟨w, r, hwB, hr, hred, hdist⟩
  -- one cancellation step, for `rⱼ ≤ rᵢ`
  have key : ∀ i j, S.ordR N hN0 ρ hρ (S.wTil w r i) = S.ordR N hN0 ρ hρ (S.wTil w r j) → i ≠ j →
      r j ≤ r i → ∃ (w' : Fin m' → C⟮S.x⟯⟮S.y⟯) (r' : Fin m' → ℕ), S.IBasis K w' ∧
        (∀ j, S.InfOrd K (w' j) (r' j)) ∧ S.Reduced K w' r' ∧
        ∀ i j, S.ordR N hN0 ρ hρ (S.wTil w' r' i) = S.ordR N hN0 ρ hρ (S.wTil w' r' j) → i = j := by
    intro i j hij hne hle
    have hw0 := IBasis.ne_zero S hwB
    obtain ⟨κ, hκ0, hLB⟩ := S.exists_cancel n d hn hn0 ha0 hd hw hcop N hN0 ρ hρ
      (S.wTil w r i) (S.wTil w r j) (S.wTil_ne_zero w r i (hw0 i)) (S.wTil_ne_zero w r j (hw0 j)) hij
    set a : Fin m' → C[X] := fun k ↦ (if k = i then 1 else 0) -
      (if k = j then Polynomial.C κ * X ^ (r i - r j) else 0) with ha
    have haI : a i = Polynomial.C 1 := by simp [ha, hne]
    have hv := IBasis.update S hwB a i 1 one_ne_zero haI
    set w' := Function.update w i (∑ k, S.polyE (a k) * w k) with hw'
    have hsum : ∑ k, S.polyE (a k) * w k =
        w i - S.polyE (Polynomial.C κ * X ^ (r i - r j)) * w j := by
      simp only [ha, S.polyE_sub, sub_mul, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_eq_single i (fun k _ hk ↦ by simp [hk, S.polyE_zero'])
          (fun h ↦ absurd (Finset.mem_univ i) h)]
        simp [S.polyE_one]
      · rw [Finset.sum_eq_single j (fun k _ hk ↦ by simp [hk, S.polyE_zero'])
          (fun h ↦ absurd (Finset.mem_univ j) h)]
        simp
    have hXi : S.polyE (X ^ r i) = S.polyE (X ^ (r i - r j)) * S.polyE (X ^ r j) := by
      rw [← S.polyE_mul, ← pow_add, Nat.sub_add_cancel hle]
    have hXj0 : S.polyE (X ^ r j) ≠ 0 := S.polyE_ne_zero _ (pow_ne_zero _ X_ne_zero)
    have hXd0 : S.polyE (X ^ (r i - r j)) ≠ 0 := S.polyE_ne_zero _ (pow_ne_zero _ X_ne_zero)
    have hwti : S.wTil w' r i = S.wTil w r i - S.polyE (Polynomial.C κ) * S.wTil w r j := by
      simp only [wTil, hw', Function.update_self, hsum, S.polyE_mul, hXi]
      field_simp
    have hwtk : ∀ k, k ≠ i → S.wTil w' r k = S.wTil w r k := fun k hk ↦ by
      simp only [wTil, hw', Function.update_of_ne hk]
    -- the new family is normal at infinity
    have hr' : ∀ k, S.InfOrd K (w' k) (r k) := by
      intro k
      by_cases hk : k = i
      · subst hk
        have h0 : S.InfOrd K (S.wTil w' r k) 0 := by
          rw [hwti]
          have hκ : S.InfOrd K (S.polyE (Polynomial.C κ)) 0 := by
            have := S.infOrd_poly (K := K) (Polynomial.C κ)
            rwa [natDegree_C, Nat.cast_zero] at this
          have h2 := InfOrd.mul S hκ (S.infOrd_wTil w r j (hr j))
          rw [add_zero] at h2
          exact InfOrd.sub S (S.infOrd_wTil w r k (hr k)) h2
        have hXk0 : S.polyE (X ^ r k) ≠ 0 := S.polyE_ne_zero _ (pow_ne_zero _ X_ne_zero)
        have e : w' k = S.polyE (X ^ r k) * S.wTil w' r k := by
          rw [wTil, ← mul_assoc, mul_inv_cancel₀ hXk0, one_mul]
        rw [e]
        have := InfOrd.mul S (S.infOrd_poly (K := K) (X ^ r k)) h0
        rw [natDegree_X_pow, add_zero] at this
        exact this
      · simp only [hw', Function.update_of_ne hk]; exact hr k
    -- and reduced
    have hred' : S.Reduced K w' r := by
      intro c hc
      set c'' : Fin m' → C := fun k ↦ if k = j then c j - c i * κ else c k with hc''
      have heq : ∑ k, S.polyE (Polynomial.C (c k)) * ((S.polyE (X ^ r k))⁻¹ * w' k) =
          ∑ k, S.polyE (Polynomial.C (c'' k)) * ((S.polyE (X ^ r k))⁻¹ * w k) := by
        have h1 : ∀ k, (S.polyE (X ^ r k))⁻¹ * w' k = S.wTil w' r k := fun k ↦ rfl
        have h2 : ∀ k, (S.polyE (X ^ r k))⁻¹ * w k = S.wTil w r k := fun k ↦ rfl
        simp only [h1, h2]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hwti]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ j⟩),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ j⟩),
          hwtk j (Ne.symm hne)]
        have hrest : ∑ k ∈ (Finset.univ.erase i).erase j,
            S.polyE (Polynomial.C (c k)) * S.wTil w' r k =
            ∑ k ∈ (Finset.univ.erase i).erase j, S.polyE (Polynomial.C (c'' k)) * S.wTil w r k :=
          Finset.sum_congr rfl fun k hk ↦ by
            have hkj := Finset.ne_of_mem_erase hk
            have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
            rw [hwtk k hki, hc'']; simp [hkj]
        rw [hrest]
        simp only [hc'', hne, ite_true, ite_false]
        simp only [Polynomial.C_sub, Polynomial.C_mul, S.polyE_sub, S.polyE_mul]
        ring
      rw [heq] at hc
      have h0 := hred c'' hc
      have hci : c i = 0 := by have := h0 i; simpa [hc'', hne] using this
      intro k
      by_cases hk : k = j
      · subst hk; have := h0 k; simpa [hc'', hci] using this
      · have := h0 k; simpa [hc'', hk] using this
    -- the measure decreases
    have hwin := S.ordR_wTil_window n d hn hn0 ha0 hd hw hcop N hN l hl ρ hρl w r hw0 hr hred
    have hwin' := S.ordR_wTil_window n d hn hn0 ha0 hd hw hcop N hN l hl ρ hρl w' r
      (IBasis.ne_zero S hv) hr' hred'
    have hinc : S.ordR N hN0 ρ hρ (S.wTil w r i) < S.ordR N hN0 ρ hρ (S.wTil w' r i) := by
      have hne0 : S.wTil w' r i ≠ 0 := S.wTil_ne_zero w' r i (IBasis.ne_zero S hv i)
      rw [hwti] at hne0 ⊢
      have := order_ge_of_lowerBd ((map_ne_zero_iff _ (S.embG _ _ ρ hρ).injective).mpr hne0) hLB
      simp only [ordR]; omega
    refine ih _ ?_ w' r hv hr' hred' rfl
    rw [← hM]
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hk : k = i
      · subst hk
        have := hwin k; have := hwin' k; omega
      · rw [hwtk k hk]
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      have := hwin i; have := hwin' i; omega
  push Not at hdist
  obtain ⟨i, j, hij, hne⟩ := hdist
  rcases le_total (r j) (r i) with h | h
  · exact key i j hij hne h
  · exact key j i hij.symm (Ne.symm hne) h

end CurveData

end Curves
