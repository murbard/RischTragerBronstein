import RischTragerBronstein.Algebraic.HypCert
import RischTragerBronstein.Algebraic.EllGenComplete

/-!
# Completeness of `hypCertDecide` for poles at branch points

For `y² = p(x)` (`p ∈ ℚ[x]` squarefree of odd degree, any genus) and `∫ A(x)/(D(x) y) dx` with `D`
split over `ℚ` and every root of `D` a root of `p`, the Hermite decomposition has no logarithmic
part (`hermite_poly` with no poles off the branch points), fits the solver's budget
(`hermite_deg_bound`), and the solver's output always passes the kernel check: `hypCertDecide`
answers, and the answer is the truth (`hypCertDecide_decides`).
-/

open Polynomial

namespace EllAlgo

open CPoly

lemma lcomb_hypCols (p A D : CPoly ℚ) (dW nB : ℕ) (w : List ℚ) :
    lcomb w (hypCols p A D dW nB) =
      C (w.getD 0 0) * (2 * (toPoly A * toPoly D)) +
      ∑ i ∈ Finset.range (dW + 1), C (w.getD (1 + i) 0) * LD (toPoly p) (toPoly D) (X ^ i) +
      ∑ j ∈ Finset.range nB, C (w.getD (1 + (dW + 1) + j) 0) *
        (2 * X ^ j * (toPoly D * toPoly D)) := by
  have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
    rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
  unfold hypCols
  rw [lcomb_append', lcomb_cons']
  simp only [List.length_cons, List.length_map, List.length_range]
  rw [lcomb_range', lcomb_range']
  simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, toPoly_monomial, h2, map_one,
    one_mul]
  have g0 : (w.take (dW + 1 + 1)).getD 0 0 = w.getD 0 0 := getD_take (by omega)
  rw [g0]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    have : ((w.take (dW + 1 + 1)).tail).getD i 0 = w.getD (1 + i) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_tail, ← List.getD_eq_getElem?_getD,
        getD_take (by omega), add_comm]
    rw [this, LD]
    ring
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    have : (w.drop (dW + 1 + 1)).getD j 0 = w.getD (1 + (dW + 1) + j) 0 := by
      rw [getD_drop]; congr 1; omega
    rw [this, mul_assoc 2]

/-- **The solver finds any residue-free Hermite decomposition** (no condition on `D`): if
`A / (D y) = (W/D · y)′ + B₀ / y` for some polynomials `W`, `B₀` (`deg B₀ ≤ deg p − 2`), the
solver succeeds. -/
theorem hypCertSolve_ne_none_of_decomp (p A D : CPoly ℚ) (hsq : Squarefree (toPoly p))
    (hp1 : 1 ≤ (toPoly p).natDegree) (hD : toPoly D ≠ 0) (W B₀ : ℚ[X])
    (hB : B₀ = 0 ∨ B₀.natDegree + 2 ≤ (toPoly p).natDegree)
    (hid : 2 * toPoly A * toPoly D = LD (toPoly p) (toPoly D) W + 2 * toPoly D ^ 2 * B₀) :
    hypCertSolve p A D ≠ none := by
  classical
  set n := (trim p).length - 1 with hn
  set nB := n - 1 with hnB
  set dW := A.length + D.length with hdW
  have hWd := hermite_deg_bound (toPoly p) hp1 (toPoly A) (toPoly D) W B₀ ∅ (fun _ ↦ 0) hD hB
    (by simp only [Finset.prod_empty, mul_one, one_mul, Finset.sum_empty, mul_zero, add_zero]
        exact hid)
  have hAd := natDegree_toPoly_le_length A
  have hDd := natDegree_toPoly_le_length D
  have hWn : W = 0 ∨ W.natDegree < dW + 1 := Or.inr (by
    have := max_le_max hAd hDd
    have : max A.length D.length ≤ dW := max_le (by omega) (by omega)
    omega)
  have hp0 : toPoly p ≠ 0 := hsq.ne_zero
  have htp : (trim p).length = (toPoly p).natDegree + 1 :=
    length_trim (fun h ↦ hp0 ((trim_eq_nil_iff p).mp h))
  have hBn : B₀ = 0 ∨ B₀.natDegree < nB := by
    rcases hB with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  set N := 1 + (dW + 1) + nB
  set g : ℕ → ℚ := fun k ↦ if k = 0 then 1 else if k < dW + 2 then -W.coeff (k - 1)
    else -B₀.coeff (k - (dW + 2))
  set w := (List.range N).map g
  have hwl : w.length = (hypCols p A D dW nB).length := by
    simp [w, N, hypCols]; omega
  have hrel : lcomb w (hypCols p A D dW nB) = 0 := by
    rw [lcomb_hypCols, getD_map_range g (by omega)]
    have s1 : ∑ i ∈ Finset.range (dW + 1), C (w.getD (1 + i) 0) *
        LD (toPoly p) (toPoly D) (X ^ i) = -LD (toPoly p) (toPoly D) W := by
      conv_rhs => rw [← sum_range_coeff W _ hWn, LD_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [Finset.mem_range] at hi
      rw [getD_map_range g (by omega)]
      simp only [g, if_neg (show 1 + i ≠ 0 by omega), if_pos (show 1 + i < dW + 2 by omega),
        show 1 + i - 1 = i by omega, map_neg]
      ring
    have s2 : ∑ j ∈ Finset.range nB, C (w.getD (1 + (dW + 1) + j) 0) *
        (2 * X ^ j * (toPoly D * toPoly D)) = -(2 * toPoly D ^ 2 * B₀) := by
      conv_rhs => rw [← sum_range_coeff B₀ _ hBn, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [Finset.mem_range] at hj
      rw [getD_map_range g (by omega)]
      simp only [g, if_neg (show 1 + (dW + 1) + j ≠ 0 by omega),
        if_neg (show ¬ 1 + (dW + 1) + j < dW + 2 by omega),
        show 1 + (dW + 1) + j - (dW + 2) = j by omega, map_neg]
      ring
    rw [s1, s2]
    simp only [g, if_pos rfl, map_one, one_mul]
    linear_combination hid
  have hhead : w.getD 0 0 ≠ 0 := by
    rw [getD_map_range g (by omega)]; simp [g]
  obtain ⟨u, hu, hu0⟩ := exists_head_basis _ w hwl hrel hhead
  have hsome : ((nullBasis (hypCols p A D dW nB)).find? fun u ↦ u.getD 0 0 ≠ 0).isSome := by
    rw [List.find?_isSome]; exact ⟨u, hu, by simpa using hu0⟩
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp hsome
  unfold hypCertSolve
  dsimp only
  rw [← hn, ← hnB, ← hdW, hu']
  simp

/-- **The solver always finds the decomposition** when all poles are branch points. -/
theorem hypCertSolve_ne_none (p A D : CPoly ℚ) (hsq : Squarefree (toPoly p))
    (hp1 : 1 ≤ (toPoly p).natDegree) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (hbr : ∀ α : ℚ, (toPoly D).eval α = 0 → (toPoly p).eval α = 0) :
    hypCertSolve p A D ≠ none := by
  classical
  obtain ⟨W, B₀, T, c, hT, hB, hid⟩ := hermite_poly (toPoly p) hsq hp1 (toPoly A) (toPoly D) hD hsplit
  have hT0 : T = ∅ := Finset.eq_empty_of_forall_notMem fun α hα ↦
    (hT α hα).2 (hbr α (hT α hα).1)
  subst hT0
  simp only [Finset.prod_empty, mul_one, one_mul, Finset.sum_empty, mul_zero, add_zero] at hid
  exact hypCertSolve_ne_none_of_decomp p A D hsq hp1 hD W B₀ hB hid

/-- **The solver's output passes the kernel check.** -/
lemma hypCertCheck_of_solve (p A D W V B0 : CPoly ℚ) (hD : toPoly D ≠ 0)
    (hp1 : 1 ≤ (toPoly p).natDegree) (h : hypCertSolve p A D = some (W, V, B0)) :
    hypCertCheck p A D W V B0 = true := by
  have hp0 : toPoly p ≠ 0 := fun h ↦ by rw [h] at hp1; simp at hp1
  have htp : (trim p).length = (toPoly p).natDegree + 1 :=
    length_trim (fun h ↦ hp0 ((trim_eq_nil_iff p).mp h))
  unfold hypCertSolve at h
  dsimp only at h
  split at h
  · rename_i u hu
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hW, hV, hB⟩ := h
    subst hW hV hB
    have hmem := List.mem_of_find?_eq_some hu
    have hu0 : u.getD 0 0 ≠ 0 := by simpa using List.find?_some hu
    have hrel := nullBasis_sound _ u hmem
    rw [lcomb_hypCols] at hrel
    set dW := A.length + D.length
    set nB := (trim p).length - 1 - 1
    set u0 := u.getD 0 0
    set co : ℕ → ℚ := fun k ↦ -u.getD k 0 / u0
    have key' : ∀ k, C u0 * C (co k) = -C (u.getD k 0) := fun k ↦ by
      rw [← C_mul, ← C_neg]; congr 1; simp only [co]; field_simp
    set Dp := toPoly D
    have S1 : ∑ i ∈ Finset.range (dW + 1), C (u.getD (1 + i) 0) * LD (toPoly p) Dp (X ^ i) =
        -(C u0 * LD (toPoly p) Dp (toPoly ((List.range (dW + 1)).map fun i ↦ co (i + 1)))) := by
      rw [toPoly_map_range', LD_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [add_comm 1 i]
      linear_combination (LD (toPoly p) Dp (X ^ i)) * key' (i + 1)
    have S2 : ∑ j ∈ Finset.range nB, C (u.getD (1 + (dW + 1) + j) 0) *
        (2 * X ^ j * (Dp * Dp)) = -(C u0 * (2 * Dp ^ 2 *
          toPoly ((List.range nB).map fun j ↦ co (dW + 2 + j)))) := by
      rw [toPoly_map_range', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [show 1 + (dW + 1) + j = dW + 2 + j by omega]
      linear_combination (2 * X ^ j * (Dp * Dp)) * key' (dW + 2 + j)
    rw [S1, S2] at hrel
    have hu0' : C u0 ≠ 0 := by rwa [Ne, C_eq_zero]
    have hz : C u0 * (2 * toPoly A * Dp - (LD (toPoly p) Dp
        (toPoly ((List.range (dW + 1)).map fun i ↦ co (i + 1))) +
        2 * Dp ^ 2 * toPoly ((List.range nB).map fun j ↦ co (dW + 2 + j)))) = 0 := by
      linear_combination hrel
    have hid := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hu0')
    unfold hypCertCheck
    simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, isZero_iff,
      decide_eq_true_eq]
    refine ⟨⟨⟨hD, hD⟩, by simp only [List.length_map, List.length_range, nB]; omega⟩,
      (beq_iff _ _).mpr ?_⟩
    have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
      rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
    simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, h2]
    simp only [LD] at hid
    linear_combination Dp * hid
  · exact absurd h (by simp)

/-- **Completeness of `hypCertDecide`** (poles only at branch points, split denominator). -/
theorem hypCertDecide_ne_none (p A D : CPoly ℚ) (hsq : Squarefree (toPoly p))
    (hp1 : 1 ≤ (toPoly p).natDegree) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (hbr : ∀ α : ℚ, (toPoly D).eval α = 0 → (toPoly p).eval α = 0) :
    hypCertDecide p A D ≠ none := by
  obtain ⟨⟨W, V, B0⟩, h⟩ := Option.ne_none_iff_exists'.mp
    (hypCertSolve_ne_none p A D hsq hp1 hD hsplit hbr)
  unfold hypCertDecide
  rw [h]
  dsimp only
  rw [if_pos (hypCertCheck_of_solve p A D W V B0 hD hp1 h)]
  simp

/-- **Completeness of `hypCertDecide` on its domain**: whenever a residue-free Hermite
decomposition exists (any `D`), it answers. -/
theorem hypCertDecide_ne_none_of_decomp (p A D : CPoly ℚ) (hsq : Squarefree (toPoly p))
    (hp1 : 1 ≤ (toPoly p).natDegree) (hD : toPoly D ≠ 0) (W B₀ : ℚ[X])
    (hB : B₀ = 0 ∨ B₀.natDegree + 2 ≤ (toPoly p).natDegree)
    (hid : 2 * toPoly A * toPoly D = LD (toPoly p) (toPoly D) W + 2 * toPoly D ^ 2 * B₀) :
    hypCertDecide p A D ≠ none := by
  obtain ⟨⟨W', V, B0⟩, h⟩ := Option.ne_none_iff_exists'.mp
    (hypCertSolve_ne_none_of_decomp p A D hsq hp1 hD W B₀ hB hid)
  unfold hypCertDecide
  rw [h]
  dsimp only
  rw [if_pos (hypCertCheck_of_solve p A D W' V B0 hD hp1 h)]
  simp

section Decision

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem for hyperelliptic integrals with poles at branch points**:
`y² = p(x)`, `p` squarefree of odd degree (any genus), `D` split over `ℚ` with all its roots among
those of `p`: `hypCertDecide` answers `some b`, and `b = true` iff `∫ A/(D y)` is elementary. -/
theorem hypCertDecide_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (p : CPoly ℚ) (hsq : Squarefree (toPoly p)) (hodd : Odd (toPoly p).natDegree)
    (hy : y ^ 2 = aeval x (toPoly p)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (hbr : ∀ α : ℚ, (toPoly D).eval α = 0 → (toPoly p).eval α = 0) :
    ∃ ans : Bool, hypCertDecide p A D = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  have hp1 : 1 ≤ (toPoly p).natDegree := by obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp
    (hypCertDecide_ne_none p A D hsq hp1 hD hsplit hbr)
  refine ⟨ans, hans, ?_⟩
  obtain ⟨W, V, B0, hD', hV, hid, hdeg, hb⟩ := hypCertDecide_spec _ _ _ _ hans
  rw [hb, hyp_decides_cert hC hCall x y hx p hsq hodd hy hgen _ _ _ _ _ hD' hV hid hdeg]

/-- **The decision theorem for hyperelliptic integrals without logarithmic part**: `y² = p(x)`,
`p` squarefree of odd degree (any genus), any `D ≠ 0`; if `A / (D y) = (W/D · y)′ + B₀ / y` for
some polynomials (`deg B₀ ≤ deg p − 2`), then `hypCertDecide` answers `some b`, and `b = true`
iff `∫ A/(D y)` is elementary. -/
theorem hypCertDecide_decides_of_decomp (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (p : CPoly ℚ) (hsq : Squarefree (toPoly p)) (hodd : Odd (toPoly p).natDegree)
    (hy : y ^ 2 = aeval x (toPoly p)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (W B₀ : ℚ[X])
    (hB : B₀ = 0 ∨ B₀.natDegree + 2 ≤ (toPoly p).natDegree)
    (hid : 2 * toPoly A * toPoly D = LD (toPoly p) (toPoly D) W + 2 * toPoly D ^ 2 * B₀) :
    ∃ ans : Bool, hypCertDecide p A D = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  have hp1 : 1 ≤ (toPoly p).natDegree := by obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp
    (hypCertDecide_ne_none_of_decomp p A D hsq hp1 hD W B₀ hB hid)
  refine ⟨ans, hans, ?_⟩
  obtain ⟨W', V, B0, hD', hV, hid', hdeg, hb⟩ := hypCertDecide_spec _ _ _ _ hans
  rw [hb, hyp_decides_cert hC hCall x y hx p hsq hodd hy hgen _ _ _ _ _ hD' hV hid' hdeg]

end Decision

end EllAlgo
