import RischTragerBronstein.Curves.HenselQ
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Hensel's lemma over `O⟦T⟧` for a commutative ring `O`

`hensel_simpleR` and `hensel_quantR` are the ring versions of `Puiseux.hensel_simple` and
`hensel_quant` (non-vanishing constant coefficients become units); `O⟦T⟧` is `T`-adically complete,
hence Henselian. `hensel_unique` is the uniqueness of the Newton root over a field.
-/

open Polynomial PowerSeries

namespace Curves

section HR

variable {O : Type*} [CommRing O] [Nontrivial O]

lemma mem_span_X_iffR (f : O⟦X⟧) : f ∈ Ideal.span {(X : O⟦X⟧)} ↔ PowerSeries.constantCoeff f = 0 := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

/-- **Hensel's lemma for non-monic polynomials over `O⟦X⟧`.** -/
theorem hensel_simpleR (f : Polynomial O⟦X⟧) (a₀ : O⟦X⟧)
    (h₁ : PowerSeries.constantCoeff (f.eval a₀) = 0) (h₂ : IsUnit (PowerSeries.constantCoeff (f.derivative.eval a₀))) :
    ∃ a : O⟦X⟧, f.eval a = 0 ∧ PowerSeries.constantCoeff a = PowerSeries.constantCoeff a₀ := by
  classical
  set g := Polynomial.taylor a₀ f with hg
  set u := g.coeff 0 with hu
  set v := g.coeff 1 with hv
  have hu0 : PowerSeries.constantCoeff u = 0 := by rw [hu, hg, Polynomial.taylor_coeff_zero]; exact h₁
  have hv0 : IsUnit (PowerSeries.constantCoeff v) := by rw [hv, hg, Polynomial.taylor_coeff_one]; exact h₂
  by_cases hu' : u = 0
  · refine ⟨a₀, ?_, rfl⟩
    rw [← Polynomial.taylor_coeff_zero]; exact hu'
  set N := g.natDegree with hN
  have hN1 : 1 ≤ N := by
    by_contra h
    have : g.coeff 1 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    apply not_isUnit_zero (M₀ := O)
    rw [← map_zero (PowerSeries.constantCoeff (R := O)), ← this]; exact hv0
  set Q : Polynomial O⟦X⟧ := ∑ i ∈ Finset.range (N + 1),
    Polynomial.C (if i = 0 then 1 else g.coeff i * u ^ (i - 1)) * Polynomial.X ^ i with hQ
  have hQcoeff : ∀ i, Q.coeff i = if i ≤ N then (if i = 0 then 1 else g.coeff i * u ^ (i - 1))
      else 0 := by
    intro i
    rw [hQ, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]
  have hgQ : ∀ w, g.eval (u * w) = u * Q.eval w := by
    intro w
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range' (n := N + 1)]
    · rw [Finset.mul_sum, Finset.sum_range_succ', Finset.sum_range_succ' (fun i ↦ u * _)]
      congr 1
      · refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [hQcoeff, if_pos (by rw [Finset.mem_range] at hi; omega), if_neg (by omega)]
        simp only [Nat.add_sub_cancel]
        ring
      · rw [hQcoeff, if_pos (by omega), if_pos rfl, ← hu]; ring
    · refine lt_of_le_of_lt (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_)
        (Nat.lt_succ_self N)
      rw [hQcoeff, if_neg (by exact_mod_cast not_le.mpr hi)]
  have hQdeg : Q.natDegree ≤ N := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
    rw [hQcoeff, if_neg (by exact_mod_cast not_le.mpr hi)]
  set v₀ := PowerSeries.constantCoeff v with hv₀
  have hredQ : Q.map (PowerSeries.constantCoeff (R := O)) =
      Polynomial.C v₀ * Polynomial.X ^ 1 + Polynomial.C 1 * Polynomial.X ^ 0 := by
    ext i
    rw [Polynomial.coeff_map, hQcoeff]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · simp
      · simp [if_pos hN1, hv₀, hv]
    · split_ifs <;> first | omega | simp [map_mul, map_pow, hu0, zero_pow (by omega : i - 1 ≠ 0)]
  set R := Polynomial.reflect N Q with hR
  have hRmon : R.Monic := by
    refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one N
      (le_trans Polynomial.natDegree_reflect_le (max_le le_rfl hQdeg)) ?_
    rw [hR, Polynomial.coeff_reflect, Polynomial.revAt_le le_rfl, Nat.sub_self, hQcoeff,
      if_pos (Nat.zero_le _), if_pos rfl]
  have hredR : R.map (PowerSeries.constantCoeff (R := O)) =
      Polynomial.X ^ (N - 1) * (Polynomial.X + Polynomial.C v₀) := by
    rw [hR, ← Polynomial.reflect_map, hredQ, Polynomial.reflect_add,
      Polynomial.reflect_C_mul_X_pow, Polynomial.reflect_C_mul_X_pow,
      Polynomial.revAt_le hN1, Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero]
    have hXN : (Polynomial.X : Polynomial O) ^ N = Polynomial.X ^ (N - 1) * Polynomial.X := by
      rw [← pow_succ, Nat.sub_add_cancel hN1]
    simp only [map_one, one_mul, hXN]
    ring
  have hcc : ∀ (P : Polynomial O⟦X⟧) (t : O⟦X⟧),
      PowerSeries.constantCoeff (P.eval t) = (P.map (PowerSeries.constantCoeff (R := O))).eval (PowerSeries.constantCoeff t) := by
    intro P t
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  set a0 : O⟦X⟧ := PowerSeries.C (-v₀) with ha0
  have hH1 : R.eval a0 ∈ Ideal.span {(X : O⟦X⟧)} := by
    rw [mem_span_X_iffR, hcc, hredR, ha0, PowerSeries.constantCoeff_C]
    simp
  have hH2 : IsUnit (Ideal.Quotient.mk (Ideal.span {(X : O⟦X⟧)}) (R.derivative.eval a0)) := by
    refine IsUnit.map _ ?_
    rw [PowerSeries.isUnit_iff_constantCoeff, hcc, ← Polynomial.derivative_map, hredR, ha0,
      PowerSeries.constantCoeff_C]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_X,
      Polynomial.derivative_C, add_zero, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_one, neg_add_cancel,
      mul_zero, zero_add, mul_one]
    exact (hv0.neg).pow _
  obtain ⟨t, ht, hta⟩ := HenselianRing.is_henselian R hRmon a0 hH1 hH2
  have ht0 : PowerSeries.constantCoeff t = -v₀ := by
    rw [mem_span_X_iffR, map_sub, sub_eq_zero, ha0, PowerSeries.constantCoeff_C] at hta; exact hta
  have htu : IsUnit t := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ht0]; exact hv0.neg
  let _ : Invertible t := htu.invertible
  set w := ⅟t with hw
  let _ : Invertible w := invertibleInvOf
  have hQw : Q.eval w = 0 := by
    have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id _) w N Q hQdeg
    have hinv : (⅟w : O⟦X⟧) = t := invOf_invOf t
    rw [hinv, ← hR] at h
    rw [Polynomial.eval, ← h, ← Polynomial.eval]
    rw [Polynomial.IsRoot.def] at ht
    rw [ht, zero_mul]
  refine ⟨u * w + a₀, ?_, ?_⟩
  · rw [← Polynomial.taylor_eval, ← hg, hgQ, hQw, mul_zero]
  · rw [map_add, map_mul, hu0, zero_mul, zero_add]

/-- **Quantitative Hensel over `O⟦T⟧`.** -/
theorem hensel_quantR (H : Polynomial (PowerSeries O)) (y₀ : PowerSeries O) (A B : ℕ)
    (u : PowerSeries O)
    (hA : (PowerSeries.X : PowerSeries O) ^ A ∣ H.eval y₀)
    (hB : (derivative H).eval y₀ = PowerSeries.X ^ B * u)
    (hu : IsUnit (PowerSeries.constantCoeff u)) (hAB : 2 * B < A) :
    ∃ y : PowerSeries O, H.eval y = 0 ∧ (PowerSeries.X : PowerSeries O) ^ (A - B) ∣ y - y₀ := by
  classical
  set d := (derivative H).eval y₀ with hd
  set T := taylor y₀ H with hT
  set R := divX (divX T) with hR
  have hT0 : T.coeff 0 = H.eval y₀ := taylor_coeff_zero _ _
  have hT1 : T.coeff 1 = d := taylor_coeff_one _ _
  have hTexp : T = Polynomial.C (H.eval y₀) + Polynomial.C d * Polynomial.X +
      Polynomial.X ^ 2 * R := by
    have h1 := X_mul_divX_add T
    have h2 := X_mul_divX_add (divX T)
    rw [coeff_divX, zero_add, hT1] at h2
    rw [hT0] at h1
    rw [← h1, ← h2, hR]; ring
  obtain ⟨q, hq⟩ := hA
  have hu' : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; exact hu
  obtain ⟨ui, hui⟩ := hu'.exists_right_inv
  set e₀ := PowerSeries.X ^ (A - 2 * B) * q * ui ^ 2 with he₀
  have hde : d ^ 2 * e₀ = H.eval y₀ := by
    rw [hq, hB, he₀]
    have : A = 2 * B + (A - 2 * B) := by omega
    conv_rhs => rw [this, pow_add]
    calc (PowerSeries.X ^ B * u) ^ 2 * (PowerSeries.X ^ (A - 2 * B) * q * ui ^ 2)
        = PowerSeries.X ^ (2 * B) * PowerSeries.X ^ (A - 2 * B) * q * (u * ui) ^ 2 := by ring
      _ = _ := by rw [hui]; ring
  set G : Polynomial (PowerSeries O) := Polynomial.C e₀ + Polynomial.X +
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
  have hG1 : IsUnit (PowerSeries.constantCoeff ((derivative G).eval 0)) := by
    rw [hG]
    simp only [derivative_add, Polynomial.derivative_C, Polynomial.derivative_X, derivative_mul,
      derivative_X_pow, eval_add, eval_mul, eval_C, eval_X, eval_pow, zero_add, eval_natCast,
      map_add]
    simp
  obtain ⟨Z₀, hZ₀, hZ₀c⟩ := hensel_simpleR G 0 hG0 hG1
  rw [map_zero] at hZ₀c
  refine ⟨y₀ + d * Z₀, by rw [← hGeval, hZ₀, mul_zero], ?_⟩
  rw [add_sub_cancel_left]
  have hZ : ∀ s, s ≤ A - 2 * B → (PowerSeries.X : PowerSeries O) ^ s ∣ Z₀ := by
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

end HR

section Uniq

variable {K : Type*} [Field K]

/-- **Uniqueness of the Newton root.** -/
theorem hensel_unique (H : Polynomial (PowerSeries K)) (y₀ y y' : PowerSeries K) (A B : ℕ)
    (u : PowerSeries K) (hB : (derivative H).eval y₀ = PowerSeries.X ^ B * u)
    (hu : PowerSeries.constantCoeff u ≠ 0) (hAB : 2 * B < A)
    (hy : H.eval y = 0) (hy' : H.eval y' = 0)
    (hd : (PowerSeries.X : PowerSeries K) ^ (A - B) ∣ y - y₀)
    (hd' : (PowerSeries.X : PowerSeries K) ^ (A - B) ∣ y' - y₀) : y = y' := by
  by_contra hne
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion H y' (y - y')
  rw [add_sub_cancel, hy, hy', zero_add] at hk
  have hdne : y - y' ≠ 0 := sub_ne_zero.mpr hne
  have h0 : (derivative H).eval y' + k * (y - y') = 0 := by
    have : (y - y') * ((derivative H).eval y' + k * (y - y')) = 0 := by
      linear_combination -hk
    exact (mul_eq_zero.mp this).resolve_left hdne
  have hyy : (PowerSeries.X : PowerSeries K) ^ (A - B) ∣ y - y' := by
    have := dvd_sub hd hd'
    rwa [sub_sub_sub_cancel_right] at this
  have hder : (PowerSeries.X : PowerSeries K) ^ (A - B) ∣ (derivative H).eval y' -
      (derivative H).eval y₀ := hd'.trans (sub_dvd_eval_sub _ _ _)
  have h1 : (PowerSeries.X : PowerSeries K) ^ (A - B) ∣ PowerSeries.X ^ B * u := by
    rw [← hB]
    have : (derivative H).eval y₀ = -((derivative H).eval y' - (derivative H).eval y₀) -
        k * (y - y') := by linear_combination h0
    rw [this]
    exact dvd_sub (dvd_neg.mpr hder) (Dvd.dvd.mul_left hyy _)
  have h2 : (PowerSeries.X : PowerSeries K) ^ B * PowerSeries.X ∣ PowerSeries.X ^ B * u :=
    (by rw [← pow_succ]; exact pow_dvd_pow _ (by omega) : _ ∣ PowerSeries.X ^ (A - B)).trans h1
  have h3 := (mul_dvd_mul_iff_left (pow_ne_zero B PowerSeries.X_ne_zero)).mp h2
  exact hu (PowerSeries.X_dvd_iff.mp h3)

end Uniq

end Curves
