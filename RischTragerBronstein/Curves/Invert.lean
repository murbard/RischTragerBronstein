import RischTragerBronstein.Curves.Integral

/-!
# The inverted chart `x' = 1/(x − b)`

For `S : CurveData C L`, `b ∈ C` and `k ≥ deg aᵢ` (the coefficients of `F`), `S.inv b k` is the
curve `x' = 1/(x − b)`, `y' = y x'ᵏ`, with
`F'(u, W) = uᵏⁿ F(b + 1/u, W/uᵏ) = ∑ᵢ rev_{k(n−i)}(aᵢ(b + ·))(u) Wⁱ` (monic of the same degree).
It generates the same field (`mem_inv_iff`). The branches of `S.inv b k` above `u = 0` are the
branches of `S` above `x = ∞` (for `b = 0`) or above `x = b`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential

section Inv

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- The coefficients of the inverted equation. -/
noncomputable def invF (F : C[X][X]) (b : C) (k : ℕ) : C[X][X] :=
  ∑ i ∈ Finset.range (F.natDegree + 1),
    Polynomial.C (reflect (k * (F.natDegree - i)) (taylor b (F.coeff i))) * X ^ i

lemma invF_coeff (F : C[X][X]) (b : C) (k i : ℕ) :
    (invF F b k).coeff i =
      if i ≤ F.natDegree then reflect (k * (F.natDegree - i)) (taylor b (F.coeff i)) else 0 := by
  classical
  simp only [invF, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]

lemma invF_coeff_top {F : C[X][X]} (hF : F.Monic) (b : C) (k : ℕ) :
    (invF F b k).coeff F.natDegree = 1 := by
  rw [invF_coeff, if_pos le_rfl, Nat.sub_self, mul_zero, hF.coeff_natDegree, taylor_one,
    map_one, reflect_one, pow_zero]

lemma invF_natDegree_le (F : C[X][X]) (b : C) (k : ℕ) :
    (invF F b k).natDegree ≤ F.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
    rw [invF_coeff, if_neg (by exact_mod_cast not_le.mpr hi)]

lemma invF_monic {F : C[X][X]} (hF : F.Monic) (b : C) (k : ℕ) : (invF F b k).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one _ (invF_natDegree_le F b k) (invF_coeff_top hF b k)

lemma invF_natDegree {F : C[X][X]} (hF : F.Monic) (b : C) (k : ℕ) :
    (invF F b k).natDegree = F.natDegree :=
  natDegree_eq_of_le_of_coeff_ne_zero (invF_natDegree_le F b k)
    (by rw [invF_coeff_top hF]; exact one_ne_zero)

end Inv

section InvCurve

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- `x − b`. -/
noncomputable def xb (b : C) : L := S.x - algebraMap C L b

lemma aeval_taylor (b : C) (P : C[X]) : aeval (S.xb b) (taylor b P) = aeval S.x P := by
  rw [taylor_apply, aeval_comp, map_add, aeval_X, aeval_C, xb, sub_add_cancel]

lemma xb_transcendental (b : C) : Transcendental C (S.xb b) := by
  rintro ⟨p, hp, h⟩
  apply S.htr
  refine ⟨taylor (-b) p, (taylor_eq_zero (-b) p).not.mpr hp, ?_⟩
  rw [taylor_apply, aeval_comp, map_add, aeval_X, aeval_C, map_neg, ← sub_eq_add_neg]
  exact h

lemma xb_ne_zero (b : C) : S.xb b ≠ 0 := fun h ↦
  S.xb_transcendental b ⟨X, X_ne_zero, by rw [aeval_X, h]⟩

/-- `rev_M(P(b + ·))(1/(x − b)) · (x − b)ᴹ = P(x)`. -/
lemma aeval_reflect_taylor (b : C) (P : C[X]) (M : ℕ) (hM : P.natDegree ≤ M) :
    aeval (S.xb b)⁻¹ (reflect M (taylor b P)) * S.xb b ^ M = aeval S.x P := by
  letI : Invertible (S.xb b) := invertibleOfNonzero (S.xb_ne_zero b)
  have h := eval₂_reflect_mul_pow (algebraMap C L) (S.xb b) M (taylor b P)
    (by rwa [natDegree_taylor])
  rw [invOf_eq_inv] at h
  rw [aeval_def, h, ← aeval_def, S.aeval_taylor]

/-- **The change of chart on polynomial expressions.** -/
lemma eval_transform (b : C) (k m E : ℕ) (h : ℕ → C[X]) (e : ℕ → ℕ)
    (he : ∀ i ≤ m, (h i).natDegree ≤ e i) (hE : ∀ i ≤ m, e i + k * i ≤ E) :
    (∑ i ∈ Finset.range (m + 1), aeval (S.xb b)⁻¹ (reflect (e i) (taylor b (h i))) *
      (S.y * (S.xb b)⁻¹ ^ k) ^ i) * S.xb b ^ E =
      ∑ i ∈ Finset.range (m + 1), aeval S.x (h i) * S.xb b ^ (E - e i - k * i) * S.y ^ i := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hx : (S.xb b)⁻¹ * S.xb b = 1 := inv_mul_cancel₀ (S.xb_ne_zero b)
  have hE' : E = e i + k * i + (E - e i - k * i) := by have := hE i hi'; omega
  conv_lhs => rw [hE', pow_add, pow_add]
  calc aeval (S.xb b)⁻¹ (reflect (e i) (taylor b (h i))) * (S.y * (S.xb b)⁻¹ ^ k) ^ i *
        (S.xb b ^ e i * S.xb b ^ (k * i) * S.xb b ^ (E - e i - k * i))
      = (aeval (S.xb b)⁻¹ (reflect (e i) (taylor b (h i))) * S.xb b ^ e i) *
          S.xb b ^ (E - e i - k * i) * S.y ^ i * ((S.xb b)⁻¹ * S.xb b) ^ (k * i) := by
        rw [mul_pow, ← pow_mul, mul_pow]; ring
    _ = _ := by rw [S.aeval_reflect_taylor b _ _ (he i hi'), hx, one_pow, mul_one]

/-- **The inverted chart** `x' = 1/(x − b)`, `y' = y x'ᵏ`. -/
noncomputable def inv (b : C) (k : ℕ) (hk : ∀ i, (S.F.coeff i).natDegree ≤ k) : CurveData C L where
  x := (S.xb b)⁻¹
  y := S.y * (S.xb b)⁻¹ ^ k
  F := invF S.F b k
  htr := by
    intro h
    exact S.xb_transcendental b (IsAlgebraic.inv_iff.mp h)
  monic := invF_monic S.monic b k
  irr := by
    classical
    intro G hG hG0
    set m := G.natDegree
    set D := ∑ i ∈ Finset.range (m + 1), (G.coeff i).natDegree
    have hD : ∀ i ≤ m, (G.coeff i).natDegree ≤ D := fun i hi ↦
      Finset.single_le_sum (f := fun i ↦ (G.coeff i).natDegree) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    set h : ℕ → C[X] := fun i ↦ (reflect D (G.coeff i)).comp (X - Polynomial.C b)
    have hth : ∀ i, taylor b (h i) = reflect D (G.coeff i) := fun i ↦ by
      simp only [h, taylor_apply, comp_assoc, sub_comp, X_comp, C_comp, add_sub_cancel_right,
        comp_X]
    have hhd : ∀ i ≤ m, (h i).natDegree ≤ D := fun i hi ↦ by
      rw [← natDegree_taylor (h i) b, hth]
      exact natDegree_reflect_le.trans (max_le le_rfl (hD i hi))
    have hmn : m < S.F.natDegree := by rw [invF_natDegree S.monic] at hG; exact hG
    have key := S.eval_transform b k m (D + k * m) h (fun _ ↦ D) hhd
      (fun i hi ↦ by have := Nat.mul_le_mul_left k hi; omega)
    have hlhs : (∑ i ∈ Finset.range (m + 1), aeval (S.xb b)⁻¹ (reflect D (taylor b (h i))) *
        (S.y * (S.xb b)⁻¹ ^ k) ^ i) = 0 := by
      rw [← hG0, eval_eq_sum_range' (n := m + 1) (natDegree_map_le.trans_lt (Nat.lt_succ_self m))]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hth, reflect_reflect, coeff_map]
      rfl
    rw [hlhs, zero_mul] at key
    set G' : C[X][X] := ∑ i ∈ Finset.range (m + 1),
      Polynomial.C (h i * (X - Polynomial.C b) ^ (D + k * m - D - k * i)) * X ^ i with hG'
    have hG'c : ∀ i, G'.coeff i = if i ≤ m then
        h i * (X - Polynomial.C b) ^ (D + k * m - D - k * i) else 0 := by
      intro i
      simp only [hG', finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]
    have hG'deg : G'.natDegree < S.F.natDegree :=
      lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
        rw [hG'c, if_neg (by exact_mod_cast not_le.mpr hi)]) hmn
    have hG'0 : (G'.map (aeval S.x).toRingHom).eval S.y = 0 := by
      rw [hG', Polynomial.map_sum, eval_finsetSum]
      refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) key.symm
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul,
        eval_C, eval_pow, eval_X]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow, map_sub, aeval_X,
        aeval_C]
      rfl
    have hz := S.irr G' hG'deg hG'0
    refine Polynomial.ext fun i ↦ ?_
    rw [Polynomial.coeff_zero]
    by_cases hi : i ≤ m
    · have h1 := congrArg (fun P ↦ P.coeff i) hz
      simp only [hG'c, if_pos hi, Polynomial.coeff_zero] at h1
      have h2 : h i = 0 := (mul_eq_zero.mp h1).resolve_right
        (pow_ne_zero _ (X_sub_C_ne_zero b))
      rw [← reflect_reflect (N := D) (p := G.coeff i), ← hth, h2, map_zero, reflect_zero]
    · exact coeff_eq_zero_of_natDegree_lt (not_le.mp hi)
  root := by
    have hdeg : ∀ i ≤ S.F.natDegree, (S.F.coeff i).natDegree ≤ k * (S.F.natDegree - i) := by
      intro i hi
      rcases lt_or_eq_of_le hi with h | h
      · exact (hk i).trans (Nat.le_mul_of_pos_right k (by omega))
      · rw [h, S.monic.coeff_natDegree, natDegree_one]; exact Nat.zero_le _
    have key := S.eval_transform b k S.F.natDegree (k * S.F.natDegree) (fun i ↦ S.F.coeff i)
      (fun i ↦ k * (S.F.natDegree - i)) hdeg (fun i hi ↦ by
        rw [← Nat.mul_add, Nat.sub_add_cancel hi])
    have hr : (∑ i ∈ Finset.range (S.F.natDegree + 1), aeval S.x (S.F.coeff i) *
        S.xb b ^ (k * S.F.natDegree - k * (S.F.natDegree - i) - k * i) * S.y ^ i) = 0 := by
      rw [← S.root, eval_eq_sum_range' (n := S.F.natDegree + 1)
        (natDegree_map_le.trans_lt (Nat.lt_succ_self _))]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' : i ≤ S.F.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have : k * S.F.natDegree - k * (S.F.natDegree - i) - k * i = 0 := by
        rw [← Nat.mul_sub, ← Nat.mul_sub, Nat.sub_sub_self hi', Nat.sub_self, mul_zero]
      rw [this, pow_zero, mul_one, coeff_map]
      rfl
    rw [hr] at key
    have hne : S.xb b ^ (k * S.F.natDegree) ≠ 0 := pow_ne_zero _ (S.xb_ne_zero b)
    have h0 := (mul_eq_zero.mp key).resolve_right hne
    rw [← h0, eval_eq_sum_range' (n := S.F.natDegree + 1)
      (natDegree_map_le.trans_lt (Nat.lt_succ_of_le (invF_natDegree_le _ b k)))]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ S.F.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [coeff_map, invF_coeff, if_pos hi']
    rfl

end CurveData

end InvCurve

end Curves
