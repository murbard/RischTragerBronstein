import RischTragerBronstein.Curves.Reparam

/-!
# Quantitative Hensel lemma over `K⟦T⟧`

`hensel_quant`: if `Tᴬ ∣ H(y₀)` and `H′(y₀) = Tᴮ u` with `u` a unit and `2B < A`, then `H` has a
root `y` with `T^{A−B} ∣ y − y₀` (Newton's method, via `hensel_simple` applied to
`G(Z) = H(y₀ + H′(y₀) Z) / H′(y₀)²`).

`split_of_approx`: `n` such approximate roots of a monic `H` of degree `n`, pairwise closer to
their true roots than to each other, give the full splitting `H = ∏ (Y − yₖ)`.
-/

open Polynomial

namespace Curves

section HQ

variable {K : Type*} [Field K]

theorem hensel_quant (H : Polynomial (PowerSeries K)) (y₀ : PowerSeries K) (A B : ℕ) (u : PowerSeries K)
    (hA : (PowerSeries.X : PowerSeries K) ^ A ∣ H.eval y₀)
    (hB : (derivative H).eval y₀ = PowerSeries.X ^ B * u)
    (hu : PowerSeries.constantCoeff u ≠ 0) (hAB : 2 * B < A) :
    ∃ y : PowerSeries K, H.eval y = 0 ∧ (PowerSeries.X : PowerSeries K) ^ (A - B) ∣ y - y₀ := by
  classical
  set d := (derivative H).eval y₀ with hd
  set T := taylor y₀ H with hT
  set R := divX (divX T) with hR
  have hT0 : T.coeff 0 = H.eval y₀ := taylor_coeff_zero _ _
  have hT1 : T.coeff 1 = d := taylor_coeff_one _ _
  -- `T = c₀ + c₁ Z + Z² R`
  have hTexp : T = Polynomial.C (H.eval y₀) + Polynomial.C d * Polynomial.X +
      Polynomial.X ^ 2 * R := by
    have h1 := X_mul_divX_add T
    have h2 := X_mul_divX_add (divX T)
    rw [coeff_divX, zero_add, hT1] at h2
    rw [hT0] at h1
    rw [← h1, ← h2, hR]; ring
  -- `e₀ = H(y₀)/d²`
  obtain ⟨q, hq⟩ := hA
  have hu' : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; exact hu.isUnit
  obtain ⟨ui, hui⟩ := hu'.exists_right_inv
  set e₀ := PowerSeries.X ^ (A - 2 * B) * q * ui ^ 2 with he₀
  have hde : d ^ 2 * e₀ = H.eval y₀ := by
    rw [hq, hB, he₀]
    have : A = 2 * B + (A - 2 * B) := by omega
    conv_rhs => rw [this, pow_add]
    calc (PowerSeries.X ^ B * u) ^ 2 * (PowerSeries.X ^ (A - 2 * B) * q * ui ^ 2)
        = PowerSeries.X ^ (2 * B) * PowerSeries.X ^ (A - 2 * B) * q * (u * ui) ^ 2 := by ring
      _ = _ := by rw [hui]; ring
  set G : Polynomial (PowerSeries K) := Polynomial.C e₀ + Polynomial.X +
    Polynomial.X ^ 2 * R.comp (Polynomial.C d * Polynomial.X) with hG
  have hGeval : ∀ Z, d ^ 2 * G.eval Z = H.eval (y₀ + d * Z) := by
    intro Z
    rw [add_comm y₀, ← taylor_eval, ← hT, hTexp, hG]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_comp]
    rw [← hde]; ring
  have hG0 : PowerSeries.constantCoeff (G.eval 0) = 0 := by
    rw [hG]
    simp only [eval_add, eval_C, eval_X, eval_mul, eval_pow, add_zero, zero_pow two_ne_zero,
      zero_mul, he₀, map_mul, map_pow, PowerSeries.constantCoeff_X]
    rw [zero_pow (by omega), zero_mul, zero_mul]
  have hG1 : PowerSeries.constantCoeff ((derivative G).eval 0) ≠ 0 := by
    rw [hG]
    simp only [derivative_add, Polynomial.derivative_C, Polynomial.derivative_X, derivative_mul,
      derivative_X_pow, eval_add, eval_mul, eval_C, eval_X, eval_pow, zero_add, eval_natCast,
      map_add]
    simp
  obtain ⟨Z₀, hZ₀, hZ₀c⟩ := Puiseux.hensel_simple G 0 hG0 hG1
  rw [map_zero] at hZ₀c
  refine ⟨y₀ + d * Z₀, by rw [← hGeval, hZ₀, mul_zero], ?_⟩
  rw [add_sub_cancel_left]
  -- `T^{A−2B} ∣ Z₀`
  have hZ : ∀ s, s ≤ A - 2 * B → (PowerSeries.X : PowerSeries K) ^ s ∣ Z₀ := by
    intro s
    induction s with
    | zero => intro _; exact one_dvd _
    | succ s ih =>
      intro hs
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · rw [pow_one, PowerSeries.X_dvd_iff]; exact hZ₀c
      have h1 := ih (by omega)
      have hZeq : Z₀ = -e₀ - Z₀ ^ 2 * (R.comp (Polynomial.C d * Polynomial.X)).eval Z₀ := by
        have := hZ₀
        rw [hG] at this
        simp only [eval_add, eval_C, eval_X, eval_mul, eval_pow] at this
        linear_combination this
      rw [hZeq]
      refine dvd_sub (dvd_neg.mpr ?_) (Dvd.dvd.mul_right ?_ _)
      · rw [he₀]
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow _ hs) _) _
      · exact (pow_dvd_pow PowerSeries.X (by omega : s + 1 ≤ 2 * s)).trans
          (by rw [pow_mul']; exact pow_dvd_pow_of_dvd h1 2)
  obtain ⟨w, hw⟩ := hZ (A - 2 * B) le_rfl
  refine ⟨u * w, ?_⟩
  rw [hB, hw]
  have : A - B = B + (A - 2 * B) := by omega
  rw [this, pow_add]; ring

/-- A monic polynomial over a field with `natDegree` many distinct roots is their product. -/
lemma eq_prod_of_distinct_roots {L : Type*} [Field L] [DecidableEq L] (p : L[X]) (hp : p.Monic)
    {n : ℕ} (hn : p.natDegree = n) (r : Fin n → L) (hr : Function.Injective r)
    (hroot : ∀ k, p.eval (r k) = 0) : p = ∏ k, (X - Polynomial.C (r k)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  set S : Multiset L := Finset.univ.val.map r with hS
  have hSnd : S.Nodup := (Finset.univ.nodup).map hr
  have hle : S ≤ p.roots := (Multiset.le_iff_subset hSnd).mpr fun z hz ↦ by
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hz
    exact (mem_roots hp0).mpr (hroot k)
  have hcard : Multiset.card S = n := by rw [hS, Multiset.card_map, Finset.card_val,
    Finset.card_univ, Fintype.card_fin]
  have heq : S = p.roots := Multiset.eq_of_le_of_card_le hle (by
    rw [hcard, ← hn]; exact card_roots' p)
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp (by rw [← heq, hcard, hn])
  rw [← h, ← heq, hS, Multiset.map_map]
  rfl

/-- **Splitting from certified approximate roots.** -/
theorem split_of_approx (H : Polynomial (PowerSeries K)) (hH : H.Monic) {n : ℕ}
    (hn : H.natDegree = n) (y₀ : Fin n → PowerSeries K) (A B : Fin n → ℕ)
    (u : Fin n → PowerSeries K) (hA : ∀ k, (PowerSeries.X : PowerSeries K) ^ A k ∣ H.eval (y₀ k))
    (hB : ∀ k, (derivative H).eval (y₀ k) = PowerSeries.X ^ B k * u k)
    (hu : ∀ k, PowerSeries.constantCoeff (u k) ≠ 0) (hAB : ∀ k, 2 * B k < A k)
    (hsep : ∀ k l, k ≠ l →
      ¬ (PowerSeries.X : PowerSeries K) ^ min (A k - B k) (A l - B l) ∣ y₀ k - y₀ l) :
    ∃ y : Fin n → PowerSeries K, (∀ k, (PowerSeries.X : PowerSeries K) ^ (A k - B k) ∣ y k - y₀ k) ∧
      Function.Injective y ∧ H.map (HahnSeries.ofPowerSeries ℤ K) =
        ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ K (y k))) := by
  classical
  choose y hy hyd using fun k ↦ hensel_quant H (y₀ k) (A k) (B k) (u k) (hA k) (hB k) (hu k)
    (hAB k)
  have hinj : Function.Injective fun k ↦ HahnSeries.ofPowerSeries ℤ K (y k) := by
    intro k l hkl
    by_contra hne
    have hyy : y k = y l := HahnSeries.ofPowerSeries_injective hkl
    apply hsep k l hne
    have h1 := (pow_dvd_pow PowerSeries.X (min_le_left (A k - B k) (A l - B l))).trans (hyd k)
    have h2 := (pow_dvd_pow PowerSeries.X (min_le_right (A k - B k) (A l - B l))).trans (hyd l)
    have := dvd_sub h2 h1
    rw [hyy] at this
    have e : y l - y₀ l - (y l - y₀ k) = y₀ k - y₀ l := by ring
    rwa [e] at this
  refine ⟨y, hyd, fun k l h ↦ hinj (by simp only [h]), ?_⟩
  refine eq_prod_of_distinct_roots _ (hH.map _) (by rw [hH.natDegree_map, hn]) _ hinj fun k ↦ ?_
  rw [eval_map, eval₂_at_apply, hy k, map_zero]

end HQ

end Curves
