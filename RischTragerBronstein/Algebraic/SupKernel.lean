import RischTragerBronstein.Algebraic.SuperJets
import RischTragerBronstein.Jacobian.KernelTorsion
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Jets over a ring on `yⁿ = f(x)`: all the points above an abscissa

Over an integral domain `R` containing a primitive `n`-th root of unity `ζ`, with `n` a unit, the
points above `x₀` (with `f(x₀) = Y₀ⁿ`, `Y₀` a unit) are `(x₀, ζᵏ Y₀)`, `k < n`.

* `dvd_of_vanish_all`: if `W = ∑ Wⱼ yʲ` (`j < n`) vanishes to order `ℓ` at all of them, then
  `(x − x₀)ˡ ∣ Wⱼ` for every `j` (discrete Fourier inversion over `ζ`).
-/

open Polynomial

namespace Sup

section Ring

variable {R : Type*} [CommRing R] [IsDomain R]

/-- `∑_{k < n} (ζᵐ)ᵏ` is `n` or `0`. -/
lemma root_geom_sum {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) (m : ℕ) :
    ∑ k ∈ Finset.range n, (ζ ^ m) ^ k = if n ∣ m then (n : R) else 0 := by
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    simp only [pow_mul, hζ.pow_eq_one, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  · have hne : ζ ^ m ≠ 1 := fun h1 ↦ h (hζ.dvd_of_pow_eq_one m h1)
    have hg := mul_geom_sum (ζ ^ m) n
    have h1 : (ζ ^ m) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [h1, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr hne)

lemma branch_mul_root {f : R[X]} {n : ℕ} {x₀ Y₀ ζ : R} {ℓ : ℕ} {V : R[X]} (hζ : ζ ^ n = 1)
    (hV : IsBranchN f n x₀ Y₀ ℓ V) (k : ℕ) :
    IsBranchN f n x₀ (ζ ^ k * Y₀) ℓ (C (ζ ^ k) * V) := by
  refine ⟨by rw [coeff_C_mul, hV.1], ?_⟩
  rw [mul_pow, ← C_pow, ← pow_mul, mul_comm k, pow_mul, hζ, one_pow, C_1, one_mul]
  exact hV.2

lemma jetN_C_mul_branch (W : R[X][X]) (x₀ c : R) (V : R[X]) (N : ℕ) (hN : W.natDegree < N) :
    jetN W x₀ (C c * V) = ∑ j ∈ Finset.range N, C (c ^ j) * ((W.coeff j).comp (X + C x₀) * V ^ j) := by
  rw [jetN, eval_eq_sum_range' (n := N) (lt_of_le_of_lt natDegree_map_le hN)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [coeff_map, coe_compRingHom, mul_pow, ← C_pow]
  ring

/-- **Vanishing at every point above `x₀`.** -/
theorem dvd_of_vanish_all {f : R[X]} {n : ℕ} (hn : 0 < n) {ζ : R} (hζ : IsPrimitiveRoot ζ n)
    (hnu : IsUnit (n : R)) {x₀ Y₀ : R} (hY : IsUnit Y₀) {ℓ : ℕ} {W : R[X][X]}
    (hW : W.natDegree < n)
    (h : ∀ k < n, VanishAtN f n W x₀ (ζ ^ k * Y₀) ℓ) :
    ∀ j, (X - C x₀) ^ ℓ ∣ W.coeff j := by
  classical
  obtain ⟨V, hV, -⟩ := h 0 hn
  rw [pow_zero, one_mul] at hV
  have hunit : ∀ k, IsUnit ((n : R) * (ζ ^ k * Y₀) ^ (n - 1)) := fun k ↦
    hnu.mul (((hζ.isUnit hn.ne').pow k).mul hY |>.pow _)
  -- every jet along `ζᵏ V` vanishes
  have hjk : ∀ k < n, X ^ ℓ ∣ jetN W x₀ (C (ζ ^ k) * V) := by
    intro k hk
    obtain ⟨Vk, hVk, hdv⟩ := h k hk
    have hcong := branchN_unique hn (hunit k) (branch_mul_root hζ.pow_eq_one hV k) hVk
    have := dvd_add (jetN_congr W x₀ hcong) hdv
    rwa [sub_add_cancel] at this
  intro j
  by_cases hj : n ≤ j
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact dvd_zero _
  push_neg at hj
  -- Fourier inversion
  set A : ℕ → R[X] := fun i ↦ (W.coeff i).comp (X + C x₀) * V ^ i
  have hsum : ∑ k ∈ Finset.range n, C ((ζ ^ k) ^ (n - j)) * jetN W x₀ (C (ζ ^ k) * V) =
      C (n : R) * A j := by
    have hterm : ∀ k i, C ((ζ ^ k) ^ (n - j)) * (C ((ζ ^ k) ^ i) * A i) =
        C ((ζ ^ (n - j + i)) ^ k) * A i := fun k i ↦ by
      rw [← mul_assoc, ← map_mul, ← pow_add, ← pow_mul, ← pow_mul, mul_comm k]
    simp_rw [jetN_C_mul_branch W x₀ _ V n hW, Finset.mul_sum]
    simp_rw [show ∀ k i, C ((ζ ^ k) ^ (n - j)) * (C ((ζ ^ k) ^ i) *
      ((W.coeff i).comp (X + C x₀) * V ^ i)) = C ((ζ ^ (n - j + i)) ^ k) * A i from hterm]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum, root_geom_sum hζ]
    rw [Finset.sum_eq_single j]
    · rw [if_pos ⟨1, by omega⟩]
    · intro i hi hij
      rw [if_neg, map_zero, zero_mul]
      rintro ⟨c, hc⟩
      have hi' := Finset.mem_range.mp hi
      rcases c with _ | _ | c
      · omega
      · omega
      · have : n * (c + 1 + 1) ≥ 2 * n := by nlinarith
        omega
    · intro hjn; exact absurd (Finset.mem_range.mpr hj) hjn
  have hdA : X ^ ℓ ∣ C (n : R) * A j := by
    rw [← hsum]
    exact Finset.dvd_sum fun k hk ↦ Dvd.dvd.mul_left (hjk k (Finset.mem_range.mp hk)) _
  -- cancel the unit `n Vʲ`
  have hc : IsUnit ((C (n : R) * V ^ j).coeff 0) := by
    rw [coeff_C_mul, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, hV.1]
    exact hnu.mul (hY.pow j)
  have h1 : X ^ ℓ ∣ (C (n : R) * V ^ j) * (W.coeff j).comp (X + C x₀) := by
    have e : C (n : R) * A j = (C (n : R) * V ^ j) * (W.coeff j).comp (X + C x₀) := by
      simp only [A]; ring
    rwa [← e]
  exact Jac.dvd_of_comp (Jac.X_pow_dvd_of_mul hc h1)

end Ring

/-- The value `∑ Vⱼ(a) bʲ` of `V` at the point `(a, b)`. -/
noncomputable def evalW {R : Type*} [CommRing R] (V : R[X][X]) (a b : R) : R :=
  (V.map (evalRingHom a)).eval b

lemma jetN_coeff_zero {R : Type*} [CommRing R] (V : R[X][X]) (a : R) (B : R[X]) :
    (jetN V a B).coeff 0 = evalW V a (B.coeff 0) := by
  induction V using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [jetN_add, coeff_add, hP, hQ]
    simp [evalW, Polynomial.map_add]
  | monomial i P =>
    simp only [jetN, evalW, Polynomial.map_monomial, eval_monomial, coe_compRingHom,
      coe_evalRingHom, coeff_zero_eq_eval_zero]
    rw [eval_mul, eval_pow, eval_comp, eval_add, eval_X, eval_C, zero_add]

section Field

variable {k : Type*} [Field k]

/-- **Over the residue field**: a function of bounded pole order vanishing to order `ℓ` at all the
points above `g'` distinct abscissae is `c ∏ (x − xᵢ)ˡ`. -/
theorem structure_mod_N {f : k[X]} {n d g' ℓ : ℕ} (hn : 0 < n) (hd : 0 < d) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) (hnu : (n : k) ≠ 0) {x y : Fin g' → k}
    (hx : Function.Injective x) (hy : ∀ i, y i ≠ 0) {W : k[X][X]} (hW : W.natDegree < n)
    (hbd : ∀ j, W.coeff j ≠ 0 → n * (W.coeff j).natDegree + d * j ≤ ℓ * n * g')
    (hv : ∀ i, ∀ k < n, VanishAtN f n W (x i) (ζ ^ k * y i) ℓ) :
    (∀ j, 1 ≤ j → W.coeff j = 0) ∧ ∃ c, W.coeff 0 = C c * (∏ i, (X - C (x i))) ^ ℓ := by
  have hdv : ∀ j i, (X - C (x i)) ^ ℓ ∣ W.coeff j := fun j i ↦
    dvd_of_vanish_all hn hζ (Ne.isUnit hnu) (Ne.isUnit (hy i)) hW (hv i) j
  have hU := fun j ↦ Jac.prod_pow_dvd hx ℓ (hdv j)
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · by_contra h0
    have h1 := natDegree_le_of_dvd (hU j) h0
    rw [Jac.natDegree_prod_pow] at h1
    have h2 := hbd j h0
    have : n * (g' * ℓ) ≤ n * (W.coeff j).natDegree := Nat.mul_le_mul_left n h1
    have : 0 < d * j := Nat.mul_pos hd hj
    nlinarith
  · obtain ⟨q, hq⟩ := hU 0
    by_cases hq0 : q = 0
    · exact ⟨0, by rw [hq, hq0]; simp⟩
    have hU0 : (∏ i, (X - C (x i))) ^ ℓ ≠ 0 :=
      ((monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)).pow _).ne_zero
    have hW0 : W.coeff 0 ≠ 0 := by rw [hq]; exact mul_ne_zero hU0 hq0
    have hdeg : q.natDegree = 0 := by
      have := congrArg natDegree hq
      rw [natDegree_mul hU0 hq0, Jac.natDegree_prod_pow] at this
      have h2 := hbd 0 hW0
      rw [this] at h2
      have : n * (g' * ℓ + q.natDegree) ≤ ℓ * n * g' := by simpa using h2
      nlinarith
    refine ⟨q.coeff 0, ?_⟩
    rw [hq, mul_comm]; congr 1; exact eq_C_of_natDegree_eq_zero hdeg

end Field

lemma jetN_C_poly_mul {R : Type*} [CommRing R] (P : R[X]) (U : R[X][X]) (a : R) (B : R[X]) :
    jetN (Polynomial.C P * U) a B = P.comp (X + C a) * jetN U a B := by
  simp [jetN, Polynomial.map_mul]

lemma u_comp_self {R : Type*} [CommRing R] {g' : ℕ} (x : Fin g' → R) (i : Fin g') :
    (∏ j, (X - C (x j))).comp (X + C (x i)) =
      X * ∏ j ∈ Finset.univ.erase i, (X + C (x i - x j)) := by
  classical
  rw [prod_comp, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [sub_comp, X_comp, C_comp]
  congr 1
  · rw [add_sub_cancel_right]
  · exact Finset.prod_congr rfl fun j _ ↦ by rw [add_sub_assoc, ← C_sub]

lemma coeff_zero_prod_erase {R : Type*} [CommRing R] {g' : ℕ} (x : Fin g' → R) (i : Fin g') :
    (∏ j ∈ Finset.univ.erase i, (X + C (x i - x j))).coeff 0 =
      ∏ j ∈ Finset.univ.erase i, (x i - x j) := by
  rw [coeff_zero_eq_eval_zero, eval_prod]
  simp

section Tangent

variable {k : Type*} [Field k]

/-- **The tangent step over the residue field**: under the non-speciality hypothesis `hNS`, the
first-order terms `λᵢ` of a function vanishing to order `m + 1` at the conjugate points and to
order `m` at `(xᵢ, yᵢ)` all vanish. -/
theorem tangent_N {f : k[X]} {n d g' m : ℕ} (hn : 0 < n) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (hnu : (n : k) ≠ 0) {x y : Fin g' → k} (hx : Function.Injective x) (hy : ∀ i, y i ≠ 0)
    {W : k[X][X]} (hW : W.natDegree < n)
    (hbd : ∀ j, W.coeff j ≠ 0 → n * (W.coeff j).natDegree + d * j ≤ (m + 1) * n * g')
    (V : Fin g' → k[X]) (hV : ∀ i, IsBranchN f n (x i) (y i) (m + 1) (V i)) (lam : Fin g' → k)
    (h0 : ∀ i, X ^ (m + 1) ∣ jetN W (x i) (V i) - C (lam i) * X ^ m)
    (hk : ∀ i, ∀ k, 1 ≤ k → k < n → X ^ (m + 1) ∣ jetN W (x i) (C (ζ ^ k) * V i))
    (hNS : ∀ U : k[X][X], U.natDegree < n →
      (∀ j, U.coeff j ≠ 0 → n * (U.coeff j).natDegree + d * j ≤ n * g') →
      (∀ i k, 1 ≤ k → k < n → evalW U (x i) (ζ ^ k * y i) = 0) → ∀ i, evalW U (x i) (y i) = 0) :
    ∀ i, lam i = 0 := by
  classical
  set u : k[X] := ∏ j, (X - C (x j))
  have hXm : (X : k[X]) ^ m ∣ X ^ (m + 1) := pow_dvd_pow X (Nat.le_succ m)
  -- all jets vanish to order `m`
  have hvm : ∀ i, ∀ kk < n, VanishAtN f n W (x i) (ζ ^ kk * y i) m := by
    intro i kk hkk
    rcases Nat.eq_zero_or_pos kk with rfl | hkk0
    · refine ⟨V i, ⟨by rw [pow_zero, one_mul]; exact (hV i).1, hXm.trans (hV i).2⟩, ?_⟩
      have := dvd_add (hXm.trans (h0 i)) (dvd_mul_left (X ^ m) (C (lam i)))
      rwa [sub_add_cancel] at this
    · have hb := branch_mul_root hζ.pow_eq_one (hV i) kk
      exact ⟨C (ζ ^ kk) * V i, ⟨hb.1, hXm.trans hb.2⟩, hXm.trans (hk i kk hkk0 hkk)⟩
  have hdv : ∀ j i, (X - C (x i)) ^ m ∣ W.coeff j := fun j i ↦
    dvd_of_vanish_all hn hζ (Ne.isUnit hnu) (Ne.isUnit (hy i)) hW (hvm i) j
  have hU : ∀ j, u ^ m ∣ W.coeff j := fun j ↦ Jac.prod_pow_dvd hx m (hdv j)
  choose q hq using hU
  set U : k[X][X] := ∑ j ∈ Finset.range n, Polynomial.monomial j (q j)
  have hUc : ∀ j, U.coeff j = if j < n then q j else 0 := fun j ↦ by
    simp only [U, finsetSum_coeff, coeff_monomial]
    split_ifs with hj
    · rw [Finset.sum_eq_single j (fun b _ hb ↦ by rw [if_neg hb]) (fun h ↦ absurd
        (Finset.mem_range.mpr hj) h), if_pos rfl]
    · exact Finset.sum_eq_zero fun b hb ↦ by
        rw [if_neg (fun h ↦ hj (by rw [← h]; exact Finset.mem_range.mp hb))]
  have hu0 : u ^ m ≠ 0 := ((monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)).pow _).ne_zero
  have hWU : W = Polynomial.C (u ^ m) * U := by
    ext1 j
    rw [coeff_C_mul, hUc]
    split_ifs with hj
    · exact hq j
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  have hUn : U.natDegree < n := by
    by_cases hU0 : U = 0
    · rw [hU0, natDegree_zero]; exact hn
    rw [natDegree_lt_iff_degree_lt hU0, degree_lt_iff_coeff_zero]
    intro j hj; rw [hUc, if_neg (by omega)]
  have hUbd : ∀ j, U.coeff j ≠ 0 → n * (U.coeff j).natDegree + d * j ≤ n * g' := by
    intro j hj
    have hWj : W.coeff j ≠ 0 := by rw [hWU, coeff_C_mul]; exact mul_ne_zero hu0 hj
    have h1 := hbd j hWj
    rw [hWU, coeff_C_mul, natDegree_mul hu0 hj, Jac.natDegree_prod_pow] at h1
    nlinarith
  -- jets of `W` through those of `U`
  set G : Fin g' → k[X] := fun i ↦ ∏ j ∈ Finset.univ.erase i, (X + C (x i - x j))
  have hG0 : ∀ i, IsUnit ((G i ^ m).coeff 0) := fun i ↦ by
    rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, coeff_zero_prod_erase]
    refine Ne.isUnit (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_))
    exact sub_ne_zero.mpr fun h ↦ (Finset.ne_of_mem_erase hj) (hx h).symm
  have hjet : ∀ i B, jetN W (x i) B = X ^ m * (G i ^ m * jetN U (x i) B) := fun i B ↦ by
    rw [hWU, jetN_C_poly_mul, pow_comp, u_comp_self]
    simp only [G]; ring
  have hcancel : ∀ (P : k[X]), X ^ (m + 1) ∣ X ^ m * P → X ∣ P := fun P h ↦ by
    rw [pow_succ] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero m X_ne_zero)).mp h
  -- `U` vanishes at the conjugate points, hence at `(xᵢ, yᵢ)`
  have hconj : ∀ i kk, 1 ≤ kk → kk < n → evalW U (x i) (ζ ^ kk * y i) = 0 := by
    intro i kk hkk hkn
    have h1 := hcancel _ (by rw [← hjet]; exact hk i kk hkk hkn)
    have h2 := Jac.X_pow_dvd_of_mul (hG0 i) (by rwa [pow_one])
    rw [pow_one, X_dvd_iff, jetN_coeff_zero, coeff_C_mul, (hV i).1] at h2
    exact h2
  have hval := hNS U hUn hUbd hconj
  intro i
  have h1 := hcancel _ (by
    have := h0 i
    rw [hjet] at this
    rwa [show X ^ m * (G i ^ m * jetN U (x i) (V i)) - C (lam i) * X ^ m =
      X ^ m * (G i ^ m * jetN U (x i) (V i) - C (lam i)) by ring] at this)
  rw [X_dvd_iff, coeff_sub, coeff_C_zero, mul_coeff_zero, jetN_coeff_zero, (hV i).1, hval i,
    mul_zero, zero_sub, neg_eq_zero] at h1
  exact h1

end Tangent

lemma jetN_const {R : Type*} [CommRing R] (P : R[X]) (z : R) (V : R[X]) :
    jetN (Polynomial.C P) z V = P.comp (X + C z) := by
  simp [jetN]

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

local notation "ρ" => IsLocalRing.residue O

/-- A bivariate polynomial whose reduction vanishes is `ϖ` times another one, with the same
degrees. -/
lemma bivar_div {ϖ : O} (hϖ : Irreducible ϖ) (W : O[X][X]) (h : W.map (mapRingHom ρ) = 0) :
    ∃ W' : O[X][X], W = Polynomial.C (C ϖ) * W' ∧ ∀ j, W'.coeff j = 0 ∨
      (W'.coeff j).natDegree = (W.coeff j).natDegree := by
  classical
  have hd : ∀ j, C ϖ ∣ W.coeff j := fun j ↦ by
    rw [Jac.C_dvd_iff_map hϖ]
    have := congrArg (fun P ↦ P.coeff j) h
    simpa [coeff_map] using this
  choose q hq using hd
  refine ⟨∑ j ∈ Finset.range (W.natDegree + 1), Polynomial.monomial j (q j), ?_, fun j ↦ ?_⟩
  · ext1 j
    rw [coeff_C_mul, finsetSum_coeff]
    by_cases hj : j < W.natDegree + 1
    · rw [Finset.sum_eq_single j (fun b _ hb ↦ by rw [coeff_monomial, if_neg hb])
        (fun h ↦ absurd (Finset.mem_range.mpr hj) h), coeff_monomial, if_pos rfl, hq j]
    · rw [Finset.sum_eq_zero fun b hb ↦ by
          rw [coeff_monomial, if_neg (fun h ↦ hj (by rw [← h]; exact Finset.mem_range.mp hb))], mul_zero,
        coeff_eq_zero_of_natDegree_lt (by omega)]
  · rw [finsetSum_coeff]
    by_cases hj : j < W.natDegree + 1
    · rw [Finset.sum_eq_single j (fun b _ hb ↦ by rw [coeff_monomial, if_neg hb])
        (fun h ↦ absurd (Finset.mem_range.mpr hj) h), coeff_monomial, if_pos rfl]
      by_cases hq0 : q j = 0
      · exact Or.inl hq0
      · right; rw [hq j, natDegree_C_mul hϖ.ne_zero]
    · left
      exact Finset.sum_eq_zero fun b hb ↦ by
        rw [coeff_monomial, if_neg (fun h ↦ hj (by rw [← h]; exact Finset.mem_range.mp hb))]

lemma IsBranchN.mapR {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {f : R[X]} {n : ℕ}
    {α β : R} {ℓ : ℕ} {V : R[X]} (h : IsBranchN f n α β ℓ V) :
    IsBranchN (f.map φ) n (φ α) (φ β) ℓ (V.map φ) := by
  refine ⟨by rw [coeff_map, h.1], ?_⟩
  obtain ⟨G, hG⟩ := h.2
  refine ⟨G.map φ, ?_⟩
  have := congrArg (Polynomial.map φ) hG
  simpa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_comp] using this

/-- **The kernel of reduction has no prime-to-`p` torsion** (superelliptic curves). The points
`Pᵢ = (xᵢ, yᵢ)` (distinct abscissae modulo `ϖ`, `yᵢ` units) form a non-special divisor modulo `ϖ`
(`hNS`); `Qᵢ = (xᵢ + tᵢ, Yᵢ)` reduce to `Pᵢ`; `ψ` (pole order `≤ ℓ n g'`) vanishes to order
`ℓ = m + 1` (a unit) at every `Qᵢ` and every conjugate `(xᵢ, ζᵏ yᵢ)`, `k ≠ 0`: it witnesses that
`ℓ (∑ Qᵢ − ∑ Pᵢ)` is principal. Then `Qᵢ = Pᵢ`. -/
theorem kernel_no_torsion_N {ϖ : O} (hϖ : Irreducible ϖ) {n d g' m : ℕ} (hn : 0 < n)
    (hd : 0 < d) {ζ : O} (hζ : IsPrimitiveRoot ζ n) (hζk : IsPrimitiveRoot (ρ ζ) n)
    (hnu : IsUnit (n : O)) (hℓ : IsUnit ((m + 1 : ℕ) : O)) (f : O[X])
    (x y t Y : Fin g' → O) (hyu : ∀ i, IsUnit (y i)) (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (ht : ∀ i, ϖ ∣ t i) (hYy : ∀ i, ϖ ∣ Y i - y i)
    (ψ : O[X][X]) (hψn : ψ.natDegree < n) (hprim : ¬ ∀ j, C ϖ ∣ ψ.coeff j)
    (hbd : ∀ j, ψ.coeff j ≠ 0 → n * (ψ.coeff j).natDegree + d * j ≤ (m + 1) * n * g')
    (hQ : ∀ i, VanishAtN f n ψ (x i + t i) (Y i) (m + 1))
    (hS : ∀ i, ∀ k, 1 ≤ k → k < n → VanishAtN f n ψ (x i) (ζ ^ k * y i) (m + 1))
    (hNS : ∀ U : (IsLocalRing.ResidueField O)[X][X], U.natDegree < n →
      (∀ j, U.coeff j ≠ 0 → n * (U.coeff j).natDegree + d * j ≤ n * g') →
      (∀ i k, 1 ≤ k → k < n → evalW U (ρ (x i)) (ρ ζ ^ k * ρ (y i)) = 0) →
      ∀ i, evalW U (ρ (x i)) (ρ (y i)) = 0) :
    ∀ i, t i = 0 := by
  classical
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  by_contra hne
  push_neg at hne
  obtain ⟨j0, hj0⟩ := hne
  have hex : ∃ N, ¬ ∀ i, ϖ ^ (N + 1) ∣ t i := by
    obtain ⟨N, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hj0 hϖ
    refine ⟨N, fun h ↦ ?_⟩
    have h1 := h j0
    rw [hv, pow_succ, mul_comm (ϖ ^ N)] at h1
    have h3 : ϖ ∣ (v : O) := (mul_dvd_mul_iff_right (pow_ne_zero N hϖ0)).mp h1
    exact hϖ.not_isUnit (isUnit_of_dvd_unit h3 v.isUnit)
  set N := Nat.find hex with hNdef
  have hN1 : ¬ ∀ i, ϖ ^ (N + 1) ∣ t i := Nat.find_spec hex
  have hN : ∀ i, ϖ ^ N ∣ t i := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · intro i; rw [h0, pow_zero]; exact one_dvd _
    · have := Nat.find_min hex (show N - 1 < N by omega)
      push_neg at this
      rwa [Nat.sub_add_cancel hpos] at this
  have hN0 : 1 ≤ N := by
    by_contra h0
    push_neg at h0
    apply hN1
    rw [Nat.lt_one_iff.mp h0, zero_add, pow_one]; exact ht
  choose τ hτ using hN
  choose VQ hVQ hjQ using hQ
  set u : O[X] := ∏ j, (X - C (x j))
  have hmap_u : u.map ρ = ∏ j, (X - C (ρ (x j))) := by simp [u, Polynomial.map_prod]
  have hxk : Function.Injective fun i ↦ ρ (x i) := by
    intro i j hij
    by_contra hne
    have := (hx i j hne).map ρ
    rw [map_sub, show ρ (x i) = ρ (x j) from hij, sub_self] at this
    exact not_isUnit_zero this
  have hρt : ∀ i, ρ (t i) = 0 := fun i ↦ (Jac.res_eq_zero_iff hϖ _).mpr (ht i)
  have hρY : ∀ i, ρ (Y i) = ρ (y i) := fun i ↦ by
    rw [← sub_eq_zero, ← map_sub]; exact (Jac.res_eq_zero_iff hϖ _).mpr (hYy i)
  have hyk : ∀ i, ρ (y i) ≠ 0 := fun i ↦ ((hyu i).map ρ).ne_zero
  have hnk : ((n : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    have := (hnu.map ρ).ne_zero; rwa [map_natCast] at this
  have hU0 : ∀ i, X ^ (m + 1) ∣ (u ^ (m + 1)).comp (X + C (x i)) := fun i ↦ by
    obtain ⟨R₁, R₂, h⟩ := Jac.u_pow_comp x i 0 m
    rw [add_zero] at h
    rw [h]; simp
  have hsplit : ∀ (c : O) (α : O[X][X]) (r : ℕ) (z : O) (V : O[X]),
      jetN (Polynomial.C (C c * u ^ (m + 1)) + Polynomial.C (C (ϖ ^ r)) * α) z V =
        C c * (u ^ (m + 1)).comp (X + C z) + C (ϖ ^ r) * jetN α z V := by
    intro c α r z V
    rw [jetN_add, jetN_const, jetN_C_mul, mul_comp, C_comp]
  have hdegU : (u ^ (m + 1)).natDegree = g' * (m + 1) := by
    rw [(monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)).natDegree_pow,
      natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)]
    simp [mul_comm]
  have hmapmul : ∀ (A : O[X][X]), A.natDegree < n →
      (A.map (mapRingHom ρ)).natDegree < n := fun A hA ↦ lt_of_le_of_lt natDegree_map_le hA
  -- the reduced layer vanishes at the conjugate points
  have hconjL : ∀ (c : O) (α : O[X][X]) (r : ℕ),
      ψ = Polynomial.C (C c * u ^ (m + 1)) + Polynomial.C (C (ϖ ^ r)) * α →
      ∀ i k, 1 ≤ k → k < n → ∃ Wk : O[X],
        IsBranchN f n (x i) (ζ ^ k * y i) (m + 1) Wk ∧
        X ^ (m + 1) ∣ jetN (α.map (mapRingHom ρ)) (ρ (x i)) (Wk.map ρ) := by
    intro c α r hae i k hk1 hkn
    obtain ⟨Wk, hWk, hj⟩ := hS i k hk1 hkn
    rw [hae, hsplit] at hj
    have hj2 := Jac.X_pow_dvd_of_C_mul (pow_ne_zero r hϖ0)
      ((dvd_add_right (Dvd.dvd.mul_left (hU0 i) _)).mp hj)
    refine ⟨Wk, hWk, ?_⟩
    rw [← jetN_map]
    simpa using Polynomial.map_dvd ρ hj2
  -- peeling off the layers
  have layers : ∀ r ≤ N, ∃ (c : O) (α : O[X][X]),
      ψ = Polynomial.C (C c * u ^ (m + 1)) + Polynomial.C (C (ϖ ^ r)) * α ∧ α.natDegree < n ∧
      ∀ j, α.coeff j ≠ 0 → n * (α.coeff j).natDegree + d * j ≤ (m + 1) * n * g' := by
    intro r
    induction r with
    | zero => intro _; exact ⟨0, ψ, by simp, hψn, hbd⟩
    | succ r ih =>
      intro hr
      obtain ⟨c, α, hae, hαn, hαbd⟩ := ih (by omega)
      -- vanishing of the reduced layer at every point above `xᵢ`
      have hv : ∀ i, ∀ k < n, VanishAtN (f.map ρ) n (α.map (mapRingHom ρ)) (ρ (x i))
          (ρ ζ ^ k * ρ (y i)) (m + 1) := by
        intro i k hk
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · rw [pow_zero, one_mul]
          have hV := hVQ i
          have hj := hjQ i
          set V := VQ i
          obtain ⟨R₁, R₂, hUi⟩ := Jac.u_pow_comp x i (t i) m
          rw [hae, hsplit, hUi, hτ i] at hj
          have e : C c * (X ^ (m + 1) * R₁ + C ((m + 1 : O) * (ϖ ^ N * τ i) *
              (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1)) * X ^ m +
              C ((ϖ ^ N * τ i) ^ 2) * R₂) + C (ϖ ^ r) * jetN α (x i + ϖ ^ N * τ i) V =
              X ^ (m + 1) * (C c * R₁) + C (ϖ ^ r) * (jetN α (x i + ϖ ^ N * τ i) V +
                C (ϖ ^ (N - r)) * (C (c * ((m + 1 : O) * τ i *
                  (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1))) * X ^ m +
                  C (c * ϖ ^ N * τ i ^ 2) * R₂)) := by
            have hpow : (ϖ : O) ^ N = ϖ ^ r * ϖ ^ (N - r) := by
              rw [← pow_add]; congr 1; omega
            rw [hpow]; simp only [map_mul, map_pow, map_add]; ring
          rw [e] at hj
          have hj2 := Jac.X_pow_dvd_of_C_mul (pow_ne_zero r hϖ0)
            ((dvd_add_right (dvd_mul_right _ _)).mp hj)
          have hj3 := Polynomial.map_dvd ρ hj2
          have hz : ρ (ϖ ^ (N - r)) = 0 := by
            rw [Jac.res_eq_zero_iff hϖ]; exact dvd_pow_self ϖ (by omega)
          simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hz, map_zero, zero_mul,
            add_zero, Polynomial.map_pow, Polynomial.map_X] at hj3
          have hzN : ρ (ϖ ^ N) = 0 := by
            rw [Jac.res_eq_zero_iff hϖ]; exact dvd_pow_self ϖ (by omega)
          rw [jetN_map, map_add, map_mul, hzN, zero_mul, add_zero] at hj3
          refine ⟨V.map ρ, ?_, hj3⟩
          have hb := hV.mapR ρ
          rwa [map_add, hρt i, add_zero, hρY] at hb
        · obtain ⟨Wk, hWk, hj⟩ := hconjL c α r hae i k hk0 hk
          refine ⟨Wk.map ρ, ?_, hj⟩
          have := hWk.mapR ρ
          rwa [map_mul, map_pow] at this
      have hbdk : ∀ j, (α.map (mapRingHom ρ)).coeff j ≠ 0 →
          n * ((α.map (mapRingHom ρ)).coeff j).natDegree + d * j ≤ (m + 1) * n * g' := by
        intro j hj
        have hαj : α.coeff j ≠ 0 := fun h0 ↦ hj (by simp [coeff_map, h0])
        have h1 := hαbd j hαj
        have h2 : ((α.map (mapRingHom ρ)).coeff j).natDegree ≤ (α.coeff j).natDegree := by
          rw [coeff_map]; exact natDegree_map_le
        nlinarith
      obtain ⟨hj1, c', hc'⟩ := structure_mod_N hn hd hζk hnk hxk hyk (hmapmul α hαn) hbdk hv
      obtain ⟨c'', hc''⟩ := IsLocalRing.residue_surjective c'
      have hred : (α - Polynomial.C (C c'' * u ^ (m + 1))).map (mapRingHom ρ) = 0 := by
        ext1 j
        rw [Polynomial.map_sub, coeff_sub, coeff_map, coeff_map, coeff_C, Polynomial.coeff_zero]
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [if_pos rfl]
          have := hc'
          rw [coeff_map] at this
          rw [this]
          simp [Polynomial.map_mul, hmap_u, hc'']
        · rw [if_neg (by omega), map_zero, sub_zero]
          have := hj1 j hj
          rwa [coeff_map] at this
      obtain ⟨α', hα'e, hα'd⟩ := bivar_div hϖ _ hred
      refine ⟨c + ϖ ^ r * c'', α', ?_, ?_, fun j hj ↦ ?_⟩
      · rw [hae, show α = Polynomial.C (C c'' * u ^ (m + 1)) + Polynomial.C (C ϖ) * α' by
          rw [← hα'e]; ring]
        simp only [map_add, map_mul, map_pow]; ring
      · by_contra hge
        push_neg at hge
        have h1 := congrArg (fun P ↦ P.coeff α'.natDegree) hα'e
        simp only [coeff_sub, coeff_C, coeff_C_mul] at h1
        rw [if_neg (by omega), sub_zero, coeff_eq_zero_of_natDegree_lt (by omega)] at h1
        have hlead : α'.coeff α'.natDegree ≠ 0 := by
          intro h0
          have : α' = 0 := by rw [← leadingCoeff_eq_zero]; exact h0
          rw [this, natDegree_zero] at hge
          omega
        exact hlead ((mul_eq_zero.mp h1.symm).resolve_left (C_ne_zero.mpr hϖ0))
      · rcases hα'd j with h0 | h0
        · exact absurd h0 hj
        rw [h0]
        rcases Nat.eq_zero_or_pos j with rfl | hjp
        · simp only [coeff_sub, coeff_C_zero, mul_zero, add_zero]
          have h1 : (α.coeff 0 - C c'' * u ^ (m + 1)).natDegree ≤
              max (α.coeff 0).natDegree (g' * (m + 1)) :=
            (natDegree_sub_le _ _).trans (max_le_max le_rfl
              ((natDegree_C_mul_le _ _).trans hdegU.le))
          have h2 : n * max (α.coeff 0).natDegree (g' * (m + 1)) ≤ (m + 1) * n * g' := by
            rcases le_total (α.coeff 0).natDegree (g' * (m + 1)) with h | h
            · rw [max_eq_right h]; nlinarith
            · rw [max_eq_left h]
              by_cases hα0 : α.coeff 0 = 0
              · rw [hα0, natDegree_zero] at h ⊢
                nlinarith
              · have := hαbd 0 hα0
                rw [mul_zero, add_zero] at this
                exact this
          exact (Nat.mul_le_mul_left n h1).trans h2
        · rw [coeff_sub, coeff_C, if_neg (by omega), sub_zero]
          have hαj : α.coeff j ≠ 0 := by
            intro h0'
            have h1 := congrArg (fun P ↦ P.coeff j) hα'e
            simp only [coeff_sub, coeff_C, if_neg (show j ≠ 0 by omega), sub_zero, h0',
              coeff_C_mul] at h1
            exact hj ((mul_eq_zero.mp h1.symm).resolve_left (C_ne_zero.mpr hϖ0))
          exact hαbd j hαj
  obtain ⟨c, α, hae, hαn, hαbd⟩ := layers N le_rfl
  -- `c` is a unit
  have hc : ρ c ≠ 0 := by
    intro hc0
    apply hprim
    intro j
    rw [hae, coeff_add, coeff_C, coeff_C_mul]
    refine dvd_add ?_ ((_root_.map_dvd C (dvd_pow_self ϖ (by omega))).mul_right _)
    split_ifs
    · exact (_root_.map_dvd C ((Jac.res_eq_zero_iff hϖ _).mp hc0)).mul_right _
    · exact dvd_zero _
  -- the tangent equations over the residue field
  set Vb : Fin g' → (IsLocalRing.ResidueField O)[X] := fun i ↦ (VQ i).map ρ
  have hVb : ∀ i, IsBranchN (f.map ρ) n (ρ (x i)) (ρ (y i)) (m + 1) (Vb i) := fun i ↦ by
    have hb := (hVQ i).mapR ρ
    rwa [map_add, hρt i, add_zero, hρY] at hb
  set κ : Fin g' → O := fun i ↦ c * ((m + 1 : O) * τ i *
    (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1))
  have h0 : ∀ i, X ^ (m + 1) ∣ jetN (α.map (mapRingHom ρ)) (ρ (x i)) (Vb i) -
      C (ρ (-κ i)) * X ^ m := by
    intro i
    have hj := hjQ i
    obtain ⟨R₁, R₂, hUi⟩ := Jac.u_pow_comp x i (t i) m
    rw [hae, hsplit, hUi, hτ i] at hj
    have e : C c * (X ^ (m + 1) * R₁ + C ((m + 1 : O) * (ϖ ^ N * τ i) *
        (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1)) * X ^ m +
        C ((ϖ ^ N * τ i) ^ 2) * R₂) + C (ϖ ^ N) * jetN α (x i + ϖ ^ N * τ i) (VQ i) =
        X ^ (m + 1) * (C c * R₁) + C (ϖ ^ N) * (jetN α (x i + ϖ ^ N * τ i) (VQ i) -
          C (-κ i) * X ^ m + C (c * ϖ ^ N * τ i ^ 2) * R₂) := by
      simp only [κ, map_mul, map_pow, map_add, map_neg]; ring
    rw [e] at hj
    have hj2 := Jac.X_pow_dvd_of_C_mul (pow_ne_zero N hϖ0)
      ((dvd_add_right (dvd_mul_right _ _)).mp hj)
    have hj3 := Polynomial.map_dvd ρ hj2
    have hz : ρ (ϖ ^ N) = 0 := by rw [Jac.res_eq_zero_iff hϖ]; exact dvd_pow_self ϖ (by omega)
    have hz2 : ρ (c * ϖ ^ N * τ i ^ 2) = 0 := by rw [map_mul, map_mul, hz, mul_zero, zero_mul]
    rw [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, map_C,
      map_C, hz2, map_zero, zero_mul, add_zero, Polynomial.map_pow, Polynomial.map_X, jetN_map,
      map_add, map_mul, hz, zero_mul, add_zero, Polynomial.map_pow, Polynomial.map_X] at hj3
    exact hj3
  have hk : ∀ i, ∀ k, 1 ≤ k → k < n →
      X ^ (m + 1) ∣ jetN (α.map (mapRingHom ρ)) (ρ (x i)) (C (ρ ζ ^ k) * Vb i) := by
    intro i k hk1 hkn
    obtain ⟨Wk, hWk, hj⟩ := hconjL c α N hae i k hk1 hkn
    have hWkb := hWk.mapR ρ
    rw [map_mul, map_pow] at hWkb
    have hunit : IsUnit ((n : IsLocalRing.ResidueField O) * (ρ ζ ^ k * ρ (y i)) ^ (n - 1)) :=
      Ne.isUnit (mul_ne_zero hnk (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _
        (hζk.ne_zero hn.ne')) (hyk i))))
    have hcong := branchN_unique hn hunit (branch_mul_root hζk.pow_eq_one (hVb i) k) hWkb
    have := dvd_add (jetN_congr (α.map (mapRingHom ρ)) (ρ (x i)) hcong) hj
    rwa [sub_add_cancel] at this
  have hαbdk : ∀ j, (α.map (mapRingHom ρ)).coeff j ≠ 0 →
      n * ((α.map (mapRingHom ρ)).coeff j).natDegree + d * j ≤ (m + 1) * n * g' := by
    intro j hj
    have hαj : α.coeff j ≠ 0 := fun h0 ↦ hj (by simp [coeff_map, h0])
    have h1 := hαbd j hαj
    have h2 : ((α.map (mapRingHom ρ)).coeff j).natDegree ≤ (α.coeff j).natDegree := by
      rw [coeff_map]; exact natDegree_map_le
    nlinarith
  have hlam := tangent_N hn hζk hnk hxk hyk (hmapmul α hαn) hαbdk Vb hVb (fun i ↦ ρ (-κ i)) h0 hk
    hNS
  apply hN1
  intro i
  have h1 := hlam i
  rw [map_neg, neg_eq_zero] at h1
  have hℓk : ρ ((m + 1 : ℕ) : O) ≠ 0 := (hℓ.map ρ).ne_zero
  have hck : ρ (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1) ≠ 0 := by
    refine pow_ne_zero _ (IsUnit.ne_zero ?_)
    refine IsUnit.map ρ ?_
    exact (IsUnit.prod_iff.mpr fun j hj ↦ hx i j (Finset.ne_of_mem_erase hj).symm)
  push_cast at hℓk
  simp only [κ, map_mul, map_pow] at h1
  have hτ0 : ρ (τ i) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hc
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hℓk
        · exact h
      · exact absurd h (by rw [← map_pow]; exact hck)
  rw [hτ i, pow_succ]
  exact mul_dvd_mul_left _ ((Jac.res_eq_zero_iff hϖ _).mp hτ0)

end Main

end Sup
