import RischTragerBronstein.Algebraic.SupMobComplete
import RischTragerBronstein.Algebraic.SupCover

/-!
# The superelliptic dispatcher answers

`superDecideSup_eventually`: for every squarefree `f ∈ ℚ[x]` of positive degree, every `n ≥ 1` and
`D ≠ 0`, `superDecideSup f n A D B fuel` answers for all large `fuel`, whenever the torsion oracle
answers (the only remaining hypothesis). The cover case uses `coverC_spec` (the chosen `c` is not
a root of `f`) and `squarefree_comp_shiftPow` (`f(c + Xᵏ)` is squarefree then).
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac NFC

namespace Sup

lemma coverC_spec (f : CPoly ℚ) (hf0 : toPoly f ≠ 0) : (toPoly f).eval (coverC f) ≠ 0 := by
  classical
  unfold coverC
  cases hfind : ((List.range (f.length + 1)).map fun i : ℕ ↦ (i : ℚ)).find?
      (fun c ↦ decide (evalC f c ≠ 0)) with
  | some c =>
    have := List.find?_some hfind
    simp only [decide_eq_true_eq] at this
    rw [Option.getD_some, ← evalC_eq]; exact this
  | none =>
    exfalso
    have hall := List.find?_eq_none.mp hfind
    have hroots : ∀ a ∈ (List.range (f.length + 1)).map (fun i : ℕ ↦ (i : ℚ)),
        (toPoly f).eval a = 0 := fun a ha ↦ by
      have := hall a ha
      simp only [decide_eq_true_eq, not_not] at this
      rw [← evalC_eq]; exact this
    have hnd : ((List.range (f.length + 1)).map fun i : ℕ ↦ (i : ℚ)).Nodup :=
      List.nodup_range.map fun i j h ↦ by exact_mod_cast h
    have := length_le_natDegree hf0 hnd hroots
    simp only [List.length_map, List.length_range] at this
    have := natDegree_toPoly_le' f
    omega

/-- `f(c + Xᵏ)` is squarefree when `f` is and `f(c) ≠ 0`. -/
lemma squarefree_comp_shiftPow {p : ℚ[X]} (hsq : Squarefree p) {c : ℚ} (hc : p.eval c ≠ 0)
    {k : ℕ} (hk : 0 < k) : Squarefree (p.comp (C c + X ^ k)) := by
  apply Polynomial.Separable.squarefree
  have hsep : IsCoprime p (derivative p) := PerfectField.separable_iff_squarefree.mpr hsq
  have h1 : IsCoprime (p.comp (C c + X ^ k)) ((derivative p).comp (C c + X ^ k)) := by
    simpa using hsep.map (Polynomial.compRingHom (C c + X ^ k))
  have hX : IsCoprime (p.comp (C c + X ^ k)) X := by
    refine (irreducible_X.coprime_iff_not_dvd.mpr ?_).symm
    rw [X_dvd_iff, coeff_zero_eq_eval_zero, eval_comp]
    simpa [zero_pow hk.ne'] using hc
  have hCk : IsCoprime (p.comp (C c + X ^ k)) (C (k : ℚ)) :=
    IsCoprime.of_isCoprime_of_dvd_right isCoprime_one_right
      (isUnit_C.mpr (IsUnit.mk0 _ (by exact_mod_cast hk.ne'))).dvd
  show IsCoprime _ _
  rw [derivative_comp, derivative_add, derivative_C, zero_add, derivative_X_pow]
  exact (hCk.mul_right hX.pow_right).mul_right h1

lemma toPoly_shiftPow_ne {p : CPoly ℚ} (hp : toPoly p ≠ 0) (c : ℚ) {k : ℕ} (hk : 0 < k) :
    toPoly (compShiftPow p c k) ≠ 0 := by
  rw [toPoly_compShiftPow]
  intro h0
  rcases comp_eq_zero_iff.mp h0 with h | ⟨-, h⟩
  · exact hp h
  · have := congrArg natDegree h
    rw [natDegree_C_add, natDegree_X_pow, natDegree_C] at this
    omega

lemma natDegree_shiftPow (p : CPoly ℚ) (c : ℚ) {k : ℕ} (hk : 0 < k) :
    (toPoly (compShiftPow p c k)).natDegree = (toPoly p).natDegree * k := by
  rw [toPoly_compShiftPow, natDegree_comp, natDegree_C_add, natDegree_X_pow]

lemma shiftPow_length {p : CPoly ℚ} (hp : toPoly p ≠ 0) (c : ℚ) {k : ℕ} (hk : 0 < k) :
    (toPoly (compShiftPow p c k)).natDegree = (compShiftPow p c k).length - 1 := by
  have h0 := toPoly_shiftPow_ne hp c hk
  have hne : compShiftPow p c k ≠ [] := fun h ↦ h0 (by rw [h]; rfl)
  have htr : trim (compShiftPow0 p c k) ≠ [] := hne
  have := length_trim htr
  unfold compShiftPow
  rw [toPoly_trim, this]; omega

/-- **The cover case answers** whenever the torsion oracle does. -/
theorem superDecideCover_ne_none_of (f : CPoly ℚ) {n : ℕ} (hn2 : 2 ≤ n)
    (hsq : Squarefree (toPoly f)) (hfd : (toPoly f).natDegree = f.length - 1)
    (hpd : 0 < f.length - 1) (A : List (CPoly ℚ)) (D : CPoly ℚ) (hD : toPoly D ≠ 0) (B fuel : ℕ)
    (hfn : n < fuel)
    (hff : (toPoly (compShiftPow f (coverC f) (coverK f n))).natDegree < fuel)
    (hfS : (toPoly (nbPartK (compShiftPow f (coverC f) (coverK f n))
      (compShiftPow D (coverC f) (coverK f n)))).natDegree < fuel)
    (hans : ∀ (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (P : CPoly (NF M)), TorsAnswers P n
      (torsOracle (nfRedAt (M := M) (M.map Rat.num)) (primesBelow B) B P n)) :
    superDecideCover f n A D B fuel ≠ none := by
  have hn : 0 < n := by omega
  set k := coverK f n with hkdef
  set c := coverC f with hcdef
  have hk : 0 < k := Nat.div_pos (Nat.gcd_le_left _ hn) (Nat.gcd_pos_of_pos_left _ hn)
  have hc : (toPoly f).eval c ≠ 0 := coverC_spec f hsq.ne_zero
  have hsqg : Squarefree (toPoly (compShiftPow f c k)) := by
    rw [toPoly_compShiftPow]; exact squarefree_comp_shiftPow hsq hc hk
  have hdeg : (toPoly (compShiftPow f c k)).natDegree = (f.length - 1) * k := by
    rw [natDegree_shiftPow f c hk, hfd]
  have hnd : n ∣ (toPoly (compShiftPow f c k)).natDegree := by
    rw [hdeg, hkdef, coverK]
    have hg : Nat.gcd n (f.length - 1) ∣ f.length - 1 := Nat.gcd_dvd_right _ _
    have hgn : Nat.gcd n (f.length - 1) ∣ n := Nat.gcd_dvd_left _ _
    have hgpos : 0 < Nat.gcd n (f.length - 1) := Nat.gcd_pos_of_pos_left _ hn
    rw [← Nat.mul_div_assoc _ hgn]
    set g := Nat.gcd n (f.length - 1)
    obtain ⟨d', hd'⟩ := hg
    rw [hd', Nat.mul_assoc, Nat.mul_div_cancel_left _ hgpos]
    exact dvd_mul_left _ _
  have hd1 : 1 ≤ (toPoly (compShiftPow f c k)).natDegree := by
    rw [hdeg]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hk.ne')
  unfold superDecideCover
  exact superDecideMobQ_ne_none_of (compShiftPow f c k) hn2 hsqg
    (shiftPow_length hsq.ne_zero c hk) hd1 hnd _ _ (toPoly_shiftPow_ne hD c hk) B fuel hfn hff hfS
    hans

/-- **The superelliptic procedure answers**: for `f ∈ ℚ[x]` squarefree of positive degree, any
`n ≥ 1` and `D ≠ 0`, `superDecideSup` answers for all large `fuel`, whenever the torsion oracle
answers. -/
theorem superDecideSup_eventually (f : CPoly ℚ) {n : ℕ} (hn : 0 < n)
    (hsq : Squarefree (toPoly f)) (hfd : (toPoly f).natDegree = f.length - 1)
    (hpd : 0 < f.length - 1) (A : List (CPoly ℚ)) (D : CPoly ℚ) (hD : toPoly D ≠ 0) (B : ℕ)
    (hans : ∀ (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (P : CPoly (NF M)), TorsAnswers P n
      (torsOracle (nfRedAt (M := M) (M.map Rat.num)) (primesBelow B) B P n)) :
    ∃ F0, ∀ fuel, F0 ≤ fuel → superDecideSup f n A D B fuel ≠ none := by
  refine ⟨n + (toPoly f).natDegree + (toPoly (nbPartK f D)).natDegree +
    (toPoly (compShiftPow f (coverC f) (coverK f n))).natDegree +
    (toPoly (nbPartK (compShiftPow f (coverC f) (coverK f n))
      (compShiftPow D (coverC f) (coverK f n)))).natDegree + 1, fun fuel hF ↦ ?_⟩
  unfold superDecideSup
  split_ifs with hcop hdiv
  · exact superDecideQ_ne_none_of f hn hsq hfd hpd hcop A D hD B fuel (by omega) (by omega)
      fun M _ ↦ hans M _
  · have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · exfalso; apply hcop; interval_cases n; exact Nat.coprime_one_left _
      · exact h
    exact superDecideMobQ_ne_none_of f hn2 hsq hfd (by omega)
      (by rw [hfd]; exact Nat.dvd_of_mod_eq_zero hdiv) A D hD B fuel (by omega) (by omega)
      (by omega) hans
  · have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · exfalso; apply hcop; interval_cases n; exact Nat.coprime_one_left _
      · exact h
    exact superDecideCover_ne_none_of f hn2 hsq hfd hpd A D hD B fuel (by omega) (by omega)
      (by omega) hans

end Sup
