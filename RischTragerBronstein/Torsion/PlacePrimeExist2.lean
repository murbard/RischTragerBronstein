import RischTragerBronstein.Torsion.PlacePrimeExist1

/-!
# Place data modulo large primes (2): the checks without the multiplier transfer to refinements

* `getD_compC_shiftC`, **`muD_mul`**: the order of `D(α + Tᴺ)` is `N` times the
  order of `D(α + T)`;
* `bivEval_agree`: evaluations agree below `m` along approximations agreeing below `m`;
* **`primePre_refine`**: the checks of `PlaceCert.primePre` (all but the multiplier) pass for a
  refinement `D'` of a place certificate `D` (same fibres, places and roots; approximations
  extended) as soon as they pass for `D` and the new coefficients are integral.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Orders

variable {F : Type*} [Field F] [DecidableEq F]

lemma getD_compC_shiftC (Dc : CPoly F) (a : F) {N : ℕ} (hN : 0 < N) (i : ℕ) :
    (compC Dc (shiftC a N)).getD i 0 =
      if N ∣ i then (compC Dc (shiftC a 1)).getD (i / N) 0 else 0 := by
  rw [← coeff_toPoly, ← coeff_toPoly, toPoly_compC, toPoly_shiftC, toPoly_compC, toPoly_shiftC]
  have e : (toPoly Dc).comp (Polynomial.C a + X ^ N) =
      expand F N ((toPoly Dc).comp (Polynomial.C a + X ^ 1)) := by
    rw [expand_eq_comp_X_pow, Polynomial.comp_assoc]
    simp
  rw [e, coeff_expand hN]

/-- **The order of `D(α + Tᴺ)`.** -/
lemma muD_mul (Dc : CPoly F) (a : F) {N : ℕ} (hN : 0 < N)
    (h : muD Dc a 1 < (compC Dc (shiftC a 1)).length) :
    muD Dc a N = N * muD Dc a 1 ∧ muD Dc a N < (compC Dc (shiftC a N)).length := by
  have hne : (compC Dc (shiftC a 1)).getD (muD Dc a 1) 0 ≠ 0 := getD_ordC _ h
  have hN' : (compC Dc (shiftC a N)).getD (N * muD Dc a 1) 0 ≠ 0 := by
    rw [getD_compC_shiftC Dc a hN, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hN]
    exact hne
  have heq : muD Dc a N = N * muD Dc a 1 := by
    refine ordC_eq_of (fun i hi ↦ ?_) hN'
    rw [getD_compC_shiftC Dc a hN]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left _ hN]
      exact getD_lt_ordC _ q (by
        by_contra hq; push Not at hq
        exact absurd hi (not_lt.mpr (Nat.mul_le_mul_left _ hq)))
    · rfl
  refine ⟨heq, ?_⟩
  rw [heq]
  by_contra hl
  exact hN' (List.getD_eq_default _ _ (by omega))

end Orders

section Agree

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Evaluations along approximations agreeing below `m` agree below `m`.** -/
lemma bivEval_agree (s : CPoly F) {Y Y' : CPoly F} {m : ℕ}
    (h : (X : F[X]) ^ m ∣ toPoly Y - toPoly Y') : ∀ W : BPoly F,
    (X : F[X]) ^ m ∣ toPoly (bivEval W s Y) - toPoly (bivEval W s Y')
  | [] => by simp [bivEval]
  | c :: W => by
    have ih := bivEval_agree s h W
    have e : ∀ Z : CPoly F, bivEval (c :: W) s Z = add (compC c s) (mul Z (bivEval W s Z)) :=
      fun _ ↦ rfl
    rw [e, e, toPoly_add, toPoly_add, toPoly_mul, toPoly_mul]
    have : toPoly (compC c s) + toPoly Y * toPoly (bivEval W s Y) -
        (toPoly (compC c s) + toPoly Y' * toPoly (bivEval W s Y')) =
        (toPoly Y - toPoly Y') * toPoly (bivEval W s Y) +
          toPoly Y' * (toPoly (bivEval W s Y) - toPoly (bivEval W s Y')) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right ih _)

lemma X_pow_dvd_of_prefix {Y Y' : CPoly F} (h : Y <+: Y') :
    (X : F[X]) ^ Y.length ∣ toPoly Y - toPoly Y' := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub, coeff_toPoly, coeff_toPoly, getD_of_prefix h hd, sub_self]

lemma getD_eq_of_dvd {P P' : CPoly F} {m : ℕ} (h : (X : F[X]) ^ m ∣ toPoly P - toPoly P') {i : ℕ}
    (hi : i < m) : P.getD i 0 = P'.getD i 0 := by
  have := (Polynomial.X_pow_dvd_iff.mp h) i hi
  rwa [Polynomial.coeff_sub, coeff_toPoly, coeff_toPoly, sub_eq_zero] at this

end Agree

section Refine

variable {K : Type*} [Field K] [DecidableEq K] {p : ℕ} [Fact p.Prime] (R : RedFns p K)

/-- **The checks without the multiplier pass for refinements.** -/
theorem primePre_refine {Fc : BPoly K} {n : ℕ} {Dc : CPoly K} {xs : List (ZMod p)}
    {D D' : PlaceCert K} (hD : D.Facts Fc n)
    (hfib : D'.fib = D.fib) (hrt : D'.rt = D.rt) (hpl : D'.pl.length = D.pl.length)
    (hπ : ∀ π < D.pl.length, D'.pj π = D.pj π ∧ D'.pe π = D.pe π ∧ D.pp π ≤ D'.pp π ∧
      D.py π <+: D'.py π)
    (hlen : ∀ π < D.pl.length, D.pp π ≤ (D.py π).length)
    (htp : ∀ j < D.fib.length, D.tp.getD j 0 ≤ D'.tp.getD j 0)
    (hok' : ∀ π < D'.pl.length, ∀ c ∈ D'.py π, R.ok c = true)
    (h : D.primePre R Fc n Dc xs = true) : D'.primePre R Fc n Dc xs = true := by
  have hfα : ∀ j, D'.fα j = D.fα j := fun j ↦ by simp only [PlaceCert.fα, hfib]
  have hrζ : ∀ j k, D'.rζ j k = D.rζ j k := fun j k ↦ by simp only [PlaceCert.rζ, hrt]
  have hrs : ∀ j k, D'.rs j k = D.rs j k := fun j k ↦ by simp only [PlaceCert.rs, hrt]
  have hrπ : ∀ j k, D'.rπ j k = D.rπ j k := fun j k ↦ by simp only [PlaceCert.rπ, hrt]
  have hαs : D'.αs = D.αs := by simp only [PlaceCert.αs, hfib]
  have hαsr : (D'.map R.red).αs = (D.map R.red).αs := by
    simp only [PlaceCert.αs, PlaceCert.map, hfib]
  have hsep0 : (D.map R.red).sepCheckP n = true := by
    simp only [PlaceCert.primePre, Bool.and_eq_true] at h
    exact h.2
  simp only [PlaceCert.primePre, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨okα, -⟩, okζ⟩, hnd⟩, hpt⟩, hunit⟩, -⟩ := h
  refine ⟨⟨⟨⟨⟨⟨by rw [hαs]; exact okα, fun π hπ' c hc ↦ hok' π hπ' c hc⟩, ?_⟩, by rw [hαsr]; exact hnd⟩,
    ?_⟩, ?_⟩, ?_⟩
  · intro j hj k hk
    rw [hrζ]; exact okζ j (by rw [← hfib]; exact hj) k hk
  · intro j hj
    rw [hfα]; exact hpt j (by rw [← hfib]; exact hj)
  · intro π hπ'
    rw [hpl] at hπ'
    obtain ⟨hpj, hpe, -, hpre⟩ := hπ π hπ'
    rw [hpj, hpe, hfα]
    set a := D.fα (D.pj π)
    set e := D.pe π
    have hrc := (hD.pl π hπ').2.2
    obtain ⟨hB1, hB2, -⟩ := rootCheck_spec hrc
    set B := ordC (bivEval (derivYB Fc) (shiftC a e) (D.py π)) with hBdef
    have hBm : B < (D.py π).length := lt_of_lt_of_le hB1 (hlen π hπ')
    have h0 := bivEval_agree (shiftC a e) (X_pow_dvd_of_prefix hpre) (derivYB Fc)
    have hord : ordC (bivEval (derivYB Fc) (shiftC a e) (D'.py π)) = B := by
      refine ordC_eq_of (fun i hi ↦ ?_) ?_
      · rw [← getD_eq_of_dvd h0 (by omega)]; exact getD_lt_ordC _ i hi
      · rw [← getD_eq_of_dvd h0 hBm]; exact getD_ordC _ hB2
    rw [hord]
    have hpre' : (D.py π).map R.red <+: (D'.py π).map R.red := hpre.map _
    have h1 := bivEval_agree (shiftC (R.red a) e) (X_pow_dvd_of_prefix hpre') (derivYB (redBL R Fc))
    rw [← getD_eq_of_dvd h1 (by rw [List.length_map]; exact hBm)]
    exact hunit π hπ'
  · simp only [PlaceCert.sepCheckP, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      decide_eq_true_eq, List.any_eq_true]
    intro j hj k hk l hl
    rw [PlaceCert.map_fib_length, hfib] at hj
    by_cases hkl : k = l
    · exact Or.inl hkl
    right
    obtain ⟨i, hi, hne⟩ := PlaceCert.sepCheckP_spec _ hsep0 j (by rw [PlaceCert.map_fib_length]; exact hj)
      k l hk hl hkl
    rw [PlaceCert.map_tp] at hi
    refine ⟨i, by rw [PlaceCert.map_tp]; exact lt_of_lt_of_le hi (htp j hj), ?_⟩
    have hrtl : j < D.rt.length := by rw [hD.rtl]; exact hj
    obtain ⟨hlen', hrts⟩ := hD.rt j hj
    have key : ∀ k < n, ((D'.map R.red).apx j k).getD i 0 = ((D.map R.red).apx j k).getD i 0 := by
      intro k hk
      obtain ⟨hπk, -, hs, -, -, htpk⟩ := hrts k hk
      have hk' : k < (D.rt.getD j []).length := by rw [hlen']; exact hk
      rw [PlaceCert.map_apx D' R.red j k (by rw [hrt]; exact hrtl) (by rw [hrt]; exact hk')
          (by rw [hrπ, hpl]; exact hπk),
        PlaceCert.map_apx D R.red j k hrtl hk' hπk, hrζ, hrs, hrπ,
        getD_conjC _ hs, getD_conjC _ hs]
      split_ifs with hd
      · congr 1
        obtain ⟨-, -, -, hpre⟩ := hπ _ hπk
        have hlt : i / D.rs j k < (D.py (D.rπ j k)).length := by
          have := hlen _ hπk
          have h2 : i < D.rs j k * D.pp (D.rπ j k) := lt_of_lt_of_le hi htpk
          have h3 : i / D.rs j k < D.pp (D.rπ j k) := (Nat.div_lt_iff_lt_mul hs).mpr (by
            rw [mul_comm]; exact h2)
          omega
        exact getD_of_prefix (hpre.map _) (by rw [List.length_map]; exact hlt)
      · rfl
    rw [key k hk, key l hl]
    exact hne

end Refine

end Curves
