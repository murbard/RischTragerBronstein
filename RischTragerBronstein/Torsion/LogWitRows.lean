import RischTragerBronstein.Torsion.LinDescent
import RischTragerBronstein.Curves.CertBranch

/-!
# Expansions along a branch are linear in the coefficients

For a branch `x = a + Tᴺ`, `y = ρ(T)` with `ρ ∈ F⟦T⟧` and a polynomial `W = ∑ c_{ie} xᵉ yⁱ`
(`i < n`, `e ≤ E`) with coefficients in an extension `ψ : F → K`, the expansion
`W(a + Tᴺ, ρ)` is `∑ c_{ie} ψ(σ_{ie})` with `σ_{ie} = (a + Tᴺ)ᵉ ρⁱ ∈ F⟦T⟧`
(**`expansion_eq_sum`**). Its first coefficients are therefore linear forms with coefficients in `F`
(`rowsAt`), the input of the linear descent.
-/

open Polynomial

namespace Curves

open CPoly

section Rows

variable {F : Type*} [Field F] {K : Type*} [Field K] (ψ : F →+* K)

/-- The substitution `P ↦ P(a + Tᴺ)` into `K⟦T⟧`. -/
noncomputable def subK (a : K) (N : ℕ) : K[X] →+* PowerSeries K :=
  (Polynomial.coeToPowerSeries.ringHom (R := K)).comp (compRingHom (Polynomial.C a + X ^ N))

/-- The monomial expansion `(a + Tᴺ)ᵉ ρⁱ` over `F`. -/
noncomputable def sigmaF (a : F) (N : ℕ) (ρ : PowerSeries F) (i e : ℕ) : PowerSeries F :=
  subK a N (X ^ e) * ρ ^ i

lemma map_subK (a : F) (N : ℕ) (P : F[X]) :
    PowerSeries.map ψ (subK a N P) = subK (ψ a) N (P.map ψ) := by
  simp only [subK, RingHom.coe_comp, Function.comp_apply, coe_compRingHom,
    Polynomial.coeToPowerSeries.ringHom_apply]
  rw [← Polynomial.polynomial_map_coe, Polynomial.map_comp]
  simp

/-- `∑_{b < n m} f (b / m) (b % m) = ∑_{i < n} ∑_{e < m} f i e`. -/
lemma sum_range_mul_div_mod {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) (m : ℕ) (hm : 0 < m) :
    ∀ n, ∑ b ∈ Finset.range (n * m), f (b / m) (b % m) =
      ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range m, f i e
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul_div_mod f m hm n,
      Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun e he ↦ ?_
    have he' := Finset.mem_range.mp he
    have h1 : (n * m + e) / m = n := by
      rw [add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt he', zero_add]
    have h2 : (n * m + e) % m = e := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he']
    rw [h1, h2]

lemma subK_eq_sum (c : K) (N E : ℕ) (q : K[X]) (hq : q.natDegree ≤ E) :
    subK c N q = ∑ e ∈ Finset.range (E + 1), PowerSeries.C (q.coeff e) * subK c N (X ^ e) := by
  conv_lhs => rw [as_sum_range' q (E + 1) (Nat.lt_succ_of_le hq)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
  congr 1
  simp [subK]

/-- **The expansion along a branch is a linear combination of monomial expansions.** -/
theorem expansion_eq_sum (a : F) (N : ℕ) (ρ : PowerSeries F) (W : K[X][X]) (n E : ℕ)
    (hdeg : W.natDegree < n) (hE : ∀ i, (W.coeff i).natDegree ≤ E) :
    (W.map (subK (ψ a) N)).eval (PowerSeries.map ψ ρ) =
      ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range (E + 1),
        PowerSeries.C ((W.coeff i).coeff e) * PowerSeries.map ψ (sigmaF a N ρ i e) := by
  rw [eval_eq_sum_range' (lt_of_le_of_lt natDegree_map_le hdeg)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_map, subK_eq_sum (ψ a) N E _ (hE i), Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [sigmaF, map_mul, map_subK, Polynomial.map_pow, Polynomial.map_X, map_pow (PowerSeries.map ψ)]
  ring

/-- The rows: the first `t` coefficients of the monomial expansions. -/
noncomputable def rowsAt (a : F) (N : ℕ) (ρ : PowerSeries F) (n E t : ℕ) : List (List F) :=
  (List.range t).map fun s ↦ (List.range (n * (E + 1))).map fun b ↦
    PowerSeries.coeff s (sigmaF a N ρ (b / (E + 1)) (b % (E + 1)))

/-- The coefficient vector of `W`. -/
noncomputable def coeffVec {R : Type*} [Semiring R] (W : R[X][X]) (E : ℕ) (b : ℕ) : R :=
  (W.coeff (b / (E + 1))).coeff (b % (E + 1))

/-- **A row applied to the coefficients of `W` is a coefficient of the expansion.** -/
theorem row_apply (a : F) (N : ℕ) (ρ : PowerSeries F) (W : K[X][X]) (n E t : ℕ)
    (hdeg : W.natDegree < n) (hE : ∀ i, (W.coeff i).natDegree ≤ E) (row : List F)
    (hrow : row ∈ rowsAt a N ρ n E t) :
    ∃ s < t, ∑ b ∈ Finset.range (n * (E + 1)), coeffVec W E b * ψ (row.getD b 0) =
      PowerSeries.coeff s ((W.map (subK (ψ a) N)).eval (PowerSeries.map ψ ρ)) := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hrow
  refine ⟨s, List.mem_range.mp hs, ?_⟩
  rw [expansion_eq_sum ψ a N ρ W n E hdeg hE]
  simp only [map_sum]
  rw [← sum_range_mul_div_mod (fun i e ↦ PowerSeries.coeff s (PowerSeries.C ((W.coeff i).coeff e) *
    PowerSeries.map ψ (sigmaF a N ρ i e))) (E + 1) (Nat.succ_pos E) n]
  · refine Finset.sum_congr rfl fun b hb ↦ ?_
    rw [List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.mp hb), List.getElem_map,
      List.getElem_range, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, coeffVec]

/-- The combination `∑_{i<n, e≤E} c_{ie} σ(i, e)`. -/
noncomputable def combS {R : Type*} [CommRing R] (σ : ℕ → ℕ → PowerSeries R) (n E : ℕ)
    (c : ℕ → ℕ → R) : PowerSeries R :=
  ∑ i ∈ Finset.range n, ∑ e ∈ Finset.range (E + 1), PowerSeries.C (c i e) * σ i e

/-- A combination applied to a row of expansions. -/
lemma apply_row {R : Type*} [CommRing R] (φ : F →+* R) (n E : ℕ)
    (β : (ℕ → ℕ → PowerSeries F) × ℕ) (s : ℕ) (x : ℕ → ℕ → R) :
    ∑ b ∈ Finset.range (n * (E + 1)), x (b / (E + 1)) (b % (E + 1)) *
      φ (((List.range (n * (E + 1))).map fun b ↦
        PowerSeries.coeff s (β.1 (b / (E + 1)) (b % (E + 1)))).getD b 0) =
      PowerSeries.coeff s (combS (fun i e ↦ PowerSeries.map φ (β.1 i e)) n E x) := by
  rw [combS]
  simp only [map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  rw [← sum_range_mul_div_mod (fun i e ↦ x i e * φ (PowerSeries.coeff s (β.1 i e))) (E + 1)
    (Nat.succ_pos E) n]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.mp hb), List.getElem_map,
    List.getElem_range]

/-- **Descent of combinations with prescribed vanishing orders**: a non-zero combination over `K`
of families defined over `F`, whose first coefficients vanish along every branch, gives one over
`F`. -/
theorem descend_comb (branches : List ((ℕ → ℕ → PowerSeries F) × ℕ)) (n E : ℕ)
    (c : ℕ → ℕ → K) (hc : ∃ i < n, ∃ e < E + 1, c i e ≠ 0)
    (h : ∀ β ∈ branches, ∀ s < β.2,
      PowerSeries.coeff s (combS (fun i e ↦ PowerSeries.map ψ (β.1 i e)) n E c) = 0) :
    ∃ d : ℕ → ℕ → F, (∃ i < n, ∃ e < E + 1, d i e ≠ 0) ∧
      ∀ β ∈ branches, ∀ s < β.2, PowerSeries.coeff s (combS β.1 n E d) = 0 := by
  classical
  set nb := n * (E + 1) with hnb
  set rows : List (List F) := branches.flatMap fun β ↦ (List.range β.2).map fun s ↦
    (List.range nb).map fun b ↦ PowerSeries.coeff s (β.1 (b / (E + 1)) (b % (E + 1))) with hrows
  have hmem : ∀ row ∈ rows, ∃ β ∈ branches, ∃ s < β.2, row = (List.range nb).map fun b ↦
      PowerSeries.coeff s (β.1 (b / (E + 1)) (b % (E + 1))) := fun row hrow ↦ by
    obtain ⟨β, hβ, hr⟩ := List.mem_flatMap.mp hrow
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact ⟨β, hβ, s, List.mem_range.mp hs, rfl⟩
  have hidx : ∀ i e, e < E + 1 → (i * (E + 1) + e) / (E + 1) = i ∧ (i * (E + 1) + e) % (E + 1) = e :=
    fun i e he ↦ ⟨by rw [add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos E), Nat.div_eq_of_lt he,
      zero_add], by rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]⟩
  obtain ⟨i0, hi0, e0, he0, hc0⟩ := hc
  obtain ⟨d, ⟨b, hb, hdb⟩, hd⟩ := exists_kernel_of_ext ψ rows nb
    (fun b ↦ c (b / (E + 1)) (b % (E + 1)))
    ⟨i0 * (E + 1) + e0, by rw [hnb]; nlinarith, by
      show c ((i0 * (E + 1) + e0) / (E + 1)) ((i0 * (E + 1) + e0) % (E + 1)) ≠ 0
      rwa [(hidx i0 e0 he0).1, (hidx i0 e0 he0).2]⟩
    (fun row hrow ↦ by
      obtain ⟨β, hβ, s, hs, rfl⟩ := hmem row hrow
      rw [apply_row ψ n E β s c]; exact h β hβ s hs)
  refine ⟨fun i e ↦ d (i * (E + 1) + e), ⟨b / (E + 1), ?_, b % (E + 1), Nat.mod_lt _ (Nat.succ_pos E), ?_⟩,
    fun β hβ s hs ↦ ?_⟩
  · rw [hnb, mul_comm] at hb; exact Nat.div_lt_of_lt_mul hb
  · show d (b / (E + 1) * (E + 1) + b % (E + 1)) ≠ 0
    rwa [Nat.div_add_mod' b (E + 1)]
  · have := hd ((List.range nb).map fun b ↦ PowerSeries.coeff s (β.1 (b / (E + 1)) (b % (E + 1))))
      (List.mem_flatMap.mpr ⟨β, hβ, List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩⟩)
    have e2 := apply_row (RingHom.id F) n E β s (fun i e ↦ d (i * (E + 1) + e))
    simp only [RingHom.id_apply, Nat.div_add_mod'] at e2
    rw [← this, e2]
    simp [PowerSeries.map_id]

end Rows

end Curves
