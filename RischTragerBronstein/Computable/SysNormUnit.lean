import RischTragerBronstein.Computable.SysNorm

/-!
# The norm of a unit modulo `q` is non-zero

The multiplication matrices on `K[t]/(q)` (`q` monic) are multiplicative (`multMat_mul`), equal
for congruent polynomials (`multMat_congr`) and the identity for `1` (`multMat_one`); hence
**`det (multMat q P) ≠ 0` when `P` is coprime to `q`** (`det_multMat_ne_zero`).
-/

open Polynomial

namespace Tower.Sys

variable {K : Type*} [Field K]

lemma modByMonic_congr {q p₁ p₂ : K[X]} (hq : q.Monic) (h : q ∣ p₁ - p₂) :
    p₁ %ₘ q = p₂ %ₘ q := by
  have e : (p₁ - p₂) %ₘ q = 0 := (modByMonic_eq_zero_iff_dvd hq).mpr h
  have := (modByMonicHom q).map_sub p₁ p₂
  simp only [modByMonicHom_apply] at this
  rw [this] at e
  exact sub_eq_zero.mp e

/-- The polynomial with coefficient vector `v`. -/
noncomputable def ofVec (q : K[X]) (v : Fin q.natDegree → K) : K[X] :=
  ∑ i : Fin q.natDegree, C (v i) * X ^ (i : ℕ)

lemma coeff_ofVec (q : K[X]) (v : Fin q.natDegree → K) (k : ℕ) :
    (ofVec q v).coeff k = if h : k < q.natDegree then v ⟨k, h⟩ else 0 := by
  simp only [ofVec, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k, h⟩ (fun b _ hb ↦ by
      rw [if_neg (fun e ↦ hb (Fin.ext e.symm)), mul_zero]) (by simp)]
    simp
  · exact Finset.sum_eq_zero fun b _ ↦ by rw [if_neg (by omega), mul_zero]

lemma natDegree_ofVec_lt (q : K[X]) (hq : 0 < q.natDegree) (v : Fin q.natDegree → K) :
    (ofVec q v).natDegree < q.natDegree := by
  rw [Nat.lt_iff_le_pred hq, natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_ofVec, dif_neg (by
    have : q.natDegree - 1 < k := by exact_mod_cast hk
    omega)]

lemma coeffVec_ofVec (q : K[X]) (v : Fin q.natDegree → K) : coeffVec q (ofVec q v) = v := by
  funext i
  simp only [coeffVec, coeff_ofVec, dif_pos i.2]

/-- Multiplication matrices are multiplicative modulo a monic `q`. -/
lemma multMat_mul (q P Q : K[X]) (hq : q.Monic) :
    multMat q (P * Q) = multMat q P * multMat q Q := by
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hpos
  · ext i; exact absurd i.2 (by omega)
  refine Matrix.ext fun i j ↦ ?_
  have key : ∀ v, (multMat q (P * Q)).mulVec v = (multMat q P * multMat q Q).mulVec v := by
    intro v
    rw [← Matrix.mulVec_mulVec, ← coeffVec_ofVec q v,
      multMat_mulVec _ _ _ (natDegree_ofVec_lt q hpos v),
      multMat_mulVec _ _ _ (natDegree_ofVec_lt q hpos v),
      multMat_mulVec _ _ _ (natDegree_modByMonic_lt _ hq (by
        intro h; rw [h] at hpos; simp at hpos))]
    congr 1
    refine modByMonic_congr hq ?_
    have := dvd_modByMonic_sub (Q * ofVec q v) q
    have e : P * Q * ofVec q v - P * ((Q * ofVec q v) %ₘ q) =
        -(P * ((Q * ofVec q v) %ₘ q - Q * ofVec q v)) := by ring
    rw [e]
    exact (dvd_neg).mpr (dvd_mul_of_dvd_right this P)
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

/-- Congruent polynomials have the same multiplication matrix. -/
lemma multMat_congr (q P P' : K[X]) (hq : q.Monic) (h : q ∣ P - P') :
    multMat q P = multMat q P' := by
  ext i j
  simp only [multMat, Matrix.of_apply]
  rw [modByMonic_congr (p₂ := P' * X ^ (j : ℕ)) hq ?_]
  rw [← sub_mul]
  exact dvd_mul_of_dvd_left h _

lemma multMat_one (q : K[X]) (hq : q.Monic) : multMat q 1 = 1 := by
  ext i j
  simp only [multMat, Matrix.of_apply, one_mul]
  rw [modByMonic_eq_self_iff hq |>.mpr (by
    rw [degree_X_pow]
    rw [degree_eq_natDegree hq.ne_zero]; exact_mod_cast j.2)]
  rw [coeff_X_pow, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (fun e ↦ h (Fin.ext e)), if_neg h]

/-- **The norm of a unit modulo `q` is non-zero.** -/
theorem det_multMat_ne_zero (q P : K[X]) (hq : q.Monic) (hcop : IsCoprime P q) :
    (multMat q P).det ≠ 0 := by
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : multMat q (u * P) = 1 := by
    rw [multMat_congr q (u * P) 1 hq ⟨-v, by linear_combination huv⟩, multMat_one q hq]
  have h2 := congrArg Matrix.det h1
  rw [multMat_mul q u P hq, Matrix.det_mul, Matrix.det_one] at h2
  exact right_ne_zero_of_mul_eq_one h2

end Tower.Sys
