import RischTragerBronstein.Algebraic.SupCheck
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Lagrange

/-!
# Non-special base points exist

The torsion test needs a *non-speciality certificate*: base points `Pᵢ = (xᵢ, yᵢ)` on `yⁿ = f(x)`
and coefficients `λ` expressing, on the space `V` of functions `xᵃ yʲ` of weight
`n a + d j ≤ n g`, the evaluation at `Pᵢ` through the evaluations at the conjugate points
`Q_{i',k} = (x_{i'}, ζᵏ y_{i'})`, `k ≥ 1`. This file proves that such certificates exist.

* `dft_const`: vanishing on the `n − 1` non-trivial conjugates forces `u_j(x) yʲ` to be
  constant in `j`.
-/

open Polynomial

namespace Sup

section DFT

variable {F : Type*} [Field F]

/-- Orthogonality of the powers of a primitive root. -/
lemma sum_root_pow {ζ : F} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (m : ℕ) :
    ∑ k ∈ Finset.range n, ζ ^ (k * m) = if n ∣ m then (n : F) else 0 := by
  split_ifs with hm
  · obtain ⟨t, rfl⟩ := hm
    have : ∀ k, ζ ^ (k * (n * t)) = 1 := fun k ↦ by
      rw [show k * (n * t) = n * (k * t) by ring, pow_mul, hζ.pow_eq_one, one_pow]
    simp [this]
  · have h1 : ζ ^ m ≠ 1 := fun h ↦ hm ((hζ.pow_eq_one_iff_dvd m).mp h)
    have h2 : (ζ ^ m) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have := geom_sum_eq h1 n
    rw [h2, sub_self, zero_div] at this
    simpa [← pow_mul, mul_comm] using this

/-- **Discrete Fourier inversion**: if `∑ⱼ vⱼ ζ^{kj} = 0` for `1 ≤ k < n`, all `vⱼ` agree. -/
lemma dft_const {ζ : F} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (v : ℕ → F)
    (h : ∀ k, 1 ≤ k → k < n → ∑ j ∈ Finset.range n, v j * ζ ^ (k * j) = 0) :
    ∀ j < n, v j = v 0 := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · intro j hj; omega
  haveI : NeZero n := ⟨hn.ne'⟩
  have hn0 : NeZero (n : F) := hζ.neZero'
  -- `n vⱼ₀ = ∑ⱼ vⱼ` for every `j₀`
  have key : ∀ j0 < n, (n : F) * v j0 = ∑ j ∈ Finset.range n, v j := by
    intro j0 hj0
    have hT : ∑ k ∈ Finset.range n, (∑ j ∈ Finset.range n, v j * ζ ^ (k * j)) *
        ζ ^ (k * (n - j0)) = ∑ j ∈ Finset.range n, v j := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        rw [h k (Nat.one_le_iff_ne_zero.mpr hk0) (Finset.mem_range.mp hk), zero_mul]
      · intro h0; exact absurd (Finset.mem_range.mpr hn) h0
    rw [← hT]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have hin : ∀ j ∈ Finset.range n, ∑ k ∈ Finset.range n, v j * ζ ^ (k * j) * ζ ^ (k * (n - j0)) =
        v j * ∑ k ∈ Finset.range n, ζ ^ (k * (j + (n - j0))) := by
      intro j _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [mul_assoc, ← pow_add, mul_add]
    rw [Finset.sum_congr rfl hin, Finset.sum_eq_single j0]
    · rw [sum_root_pow hζ, if_pos (by rw [show j0 + (n - j0) = n by omega])]; ring
    · intro j hj hjj0
      rw [sum_root_pow hζ, if_neg, mul_zero]
      intro hd
      have hj' := Finset.mem_range.mp hj
      obtain ⟨t, ht⟩ := hd
      rcases t with _ | _ | t
      · omega
      · omega
      · have : n * (t + 1 + 1) ≥ 2 * n := by nlinarith
        omega
    · intro h0; exact absurd (Finset.mem_range.mpr hj0) h0
  intro j hj
  have e1 := key j hj
  have e2 := key 0 hn
  rw [← e2] at e1
  exact mul_left_cancel₀ hn0.out e1

end DFT

section Core

variable {F : Type*} [Field F]

/-- `U` as a polynomial in `y` of degree `< n`. -/
lemma evalW_eq_sum_j (U : F[X][X]) {n d M : ℕ}
    (hU : ∀ j a, (U.coeff j).coeff a ≠ 0 → j < n ∧ n * a + d * j ≤ M) (a b : F) :
    evalW U a b = ∑ j ∈ Finset.range n, (U.coeff j).eval a * b ^ j := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    have : U = 0 := by
      ext j a'
      by_contra h
      exact absurd (hU j a' h).1 (Nat.not_lt_zero _)
    subst this; simp [evalW]
  have hUn : (U.map (evalRingHom a)).natDegree < n := by
    refine lt_of_le_of_lt natDegree_map_le ?_
    by_contra h
    push_neg at h
    by_cases hU0 : U = 0
    · subst hU0; simp at h; omega
    have hc := leadingCoeff_ne_zero.mpr hU0
    obtain ⟨a', ha'⟩ : ∃ a', (U.coeff U.natDegree).coeff a' ≠ 0 := by
      by_contra h1; push_neg at h1; exact hc (Polynomial.ext h1)
    have := (hU _ a' ha').1
    omega
  rw [evalW, eval_eq_sum_range' hUn]
  simp [coeff_map]

/-- The monomials `xˢ y⁻ʲ` with `1 ≤ j < n`, `n (s + 1) < d j` (the holomorphic differentials
`xˢ dx / yʲ`). -/
def IsHol (n d : ℕ) (sj : ℕ × ℕ) : Prop := 1 ≤ sj.2 ∧ sj.2 < n ∧ n * (sj.1 + 1) < d * sj.2

set_option maxHeartbeats 1600000 in
/-- **Non-special points give the vanishing implication**: if the matrix `xᵢ^{sₖ} yᵢ^{-jₖ}` of `g`
holomorphic monomials is invertible, every `U` of weight `≤ n g` vanishing at all conjugates
`(xᵢ, ζᵏ yᵢ)`, `k ≥ 1`, vanishes at every `(xᵢ, yᵢ)`. -/
theorem cert_implication {g n d : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ n) (x y : Fin g → F)
    (hx : Function.Injective x) (hy : ∀ i, y i ≠ 0) (sj : Fin g → ℕ × ℕ)
    (hsj : ∀ k, IsHol n d (sj k))
    (hdet : (Matrix.of fun i k ↦ x i ^ (sj k).1 * (y i ^ (sj k).2)⁻¹).det ≠ 0)
    (U : F[X][X]) (hU : ∀ j a, (U.coeff j).coeff a ≠ 0 → j < n ∧ n * a + d * j ≤ n * g)
    (hv : ∀ i k, 1 ≤ k → k < n → evalW U (x i) (ζ ^ k * y i) = 0) :
    ∀ i, evalW U (x i) (y i) = 0 := by
  classical
  -- DFT on each fiber
  have hconst : ∀ i, ∀ j < n, (U.coeff j).eval (x i) * y i ^ j = (U.coeff 0).eval (x i) := by
    intro i
    have := dft_const hζ (fun j ↦ (U.coeff j).eval (x i) * y i ^ j) (fun k hk1 hkn ↦ by
      have h := hv i k hk1 hkn
      rw [evalW_eq_sum_j U hU] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_pow, ← pow_mul]; ring)
    intro j hj
    simpa using this j hj
  set c : Fin g → F := fun i ↦ (U.coeff 0).eval (x i) with hc
  -- the Lagrange relations
  set D : Fin g → F := fun i ↦ ∏ l ∈ Finset.univ.erase i, (x i - x l) with hD
  have hD0 : ∀ i, D i ≠ 0 := fun i ↦ Finset.prod_ne_zero_iff.mpr fun l hl ↦
    sub_ne_zero.mpr fun h ↦ (Finset.mem_erase.mp hl).1 (hx h).symm
  have hrel : ∀ k, ∑ i, c i / D i * (x i ^ (sj k).1 * (y i ^ (sj k).2)⁻¹) = 0 := by
    intro k
    obtain ⟨hj1, hjn, hjd⟩ := hsj k
    set s := (sj k).1
    set j := (sj k).2
    have hdeg : (U.coeff j * X ^ s).degree < ((Finset.univ : Finset (Fin g)).card : WithBot ℕ) := by
      by_cases hU0 : U.coeff j = 0
      · rw [hU0, zero_mul, degree_zero]; exact WithBot.bot_lt_coe _
      rw [Finset.card_univ, Fintype.card_fin]
      have hlc := leadingCoeff_ne_zero.mpr hU0
      have hb := (hU j _ hlc).2
      rw [degree_mul, degree_X_pow, degree_eq_natDegree hU0]
      norm_cast
      have : n * ((U.coeff j).natDegree + s + 1) < n * g := by nlinarith
      have := lt_of_mul_lt_mul_left this (Nat.zero_le n)
      omega
    have hcoef : (U.coeff j * X ^ s).coeff ((Finset.univ : Finset (Fin g)).card - 1) = 0 := by
      by_cases hU0 : U.coeff j = 0
      · rw [hU0, zero_mul, coeff_zero]
      apply coeff_eq_zero_of_natDegree_lt
      rw [Finset.card_univ, Fintype.card_fin]
      have hlc := leadingCoeff_ne_zero.mpr hU0
      have hb := (hU j _ hlc).2
      rw [natDegree_mul hU0 (pow_ne_zero _ X_ne_zero), natDegree_X_pow]
      have : n * ((U.coeff j).natDegree + s + 1) < n * g := by nlinarith
      have := lt_of_mul_lt_mul_left this (Nat.zero_le n)
      omega
    have hsum := Lagrange.coeff_eq_sum (s := Finset.univ) (v := x) (fun a _ b _ h ↦ hx h) hdeg
    rw [hcoef] at hsum
    rw [hsum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hci := hconst i j hjn
    rw [eval_mul, eval_pow, eval_X]
    have hyj : y i ^ j ≠ 0 := pow_ne_zero _ (hy i)
    rw [show (U.coeff j).eval (x i) = c i * (y i ^ j)⁻¹ by
      rw [hc]; simp only; rw [← hci]; field_simp]
    simp only [hD]
    field_simp
  -- invertibility of the matrix kills `c / D`
  have hw : (fun i ↦ c i / D i) = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    funext k
    rw [Matrix.vecMul, dotProduct]
    simpa using hrel k
  intro i
  have hci : c i = 0 := by
    have := congrFun hw i
    simp only [Pi.zero_apply, div_eq_zero_iff] at this
    rcases this with h | h
    · exact h
    · exact absurd h (hD0 i)
  rw [evalW_eq_sum_j U hU, Finset.sum_congr rfl fun j hj ↦ hconst i j (Finset.mem_range.mp hj)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [show (U.coeff 0).eval (x i) = c i from rfl, hci, mul_zero]

end Core

section Dual

variable {F : Type*} [Field F]

open Classical in
/-- **The certificate exists** for points with an invertible holomorphic matrix: the evaluation
at `Pᵢ` on the weight-`≤ n g` space is a combination of the evaluations at the conjugates. -/
theorem exists_lam {g n d : ℕ} (hn : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n) (x y : Fin g → F)
    (hx : Function.Injective x) (hy : ∀ i, y i ≠ 0) (sj : Fin g → ℕ × ℕ)
    (hsj : ∀ k, IsHol n d (sj k))
    (hdet : (Matrix.of fun i k ↦ x i ^ (sj k).1 * (y i ^ (sj k).2)⁻¹).det ≠ 0) :
    ∃ lam : Fin g → Fin g → ℕ → F, ∀ i, ∀ ai ∈ basisN n d (n * g),
      x i ^ ai.1 * y i ^ ai.2 =
        ∑ i', ∑ k ∈ Finset.Ico 1 n, lam i i' k * (x i' ^ ai.1 * (ζ ^ k * y i') ^ ai.2) := by
  set B := (basisN n d (n * g)).toFinset with hB
  -- evaluation functionals on coefficient vectors
  let L : F → F → ((↥B) → F) →ₗ[F] F := fun a b ↦
    ∑ ai : B, (a ^ ai.1.1 * b ^ ai.1.2) • LinearMap.proj ai
  have hL : ∀ a b (u : (↥B) → F), L a b u = ∑ ai : B, (a ^ ai.1.1 * b ^ ai.1.2) * u ai :=
    fun a b u ↦ by simp [L, LinearMap.sum_apply]
  -- the polynomial of a coefficient vector
  let poly : ((↥B) → F) → F[X][X] := fun u ↦
    ∑ ai : B, Polynomial.monomial ai.1.2 (Polynomial.monomial ai.1.1 (u ai))
  have hcoef : ∀ u j a, ((poly u).coeff j).coeff a =
      if h : (a, j) ∈ B then u ⟨(a, j), h⟩ else 0 := by
    intro u j a
    have hterm : ∀ b : B, ((Polynomial.monomial b.1.2 (Polynomial.monomial b.1.1 (u b))).coeff
        j).coeff a = if b.1 = (a, j) then u b else 0 := by
      intro b
      simp only [coeff_monomial]
      by_cases h2 : b.1.2 = j <;> by_cases h1 : b.1.1 = a <;>
        simp [h1, h2, Prod.ext_iff, coeff_monomial]
    simp only [poly, finsetSum_coeff]
    rw [Finset.sum_congr rfl fun b _ ↦ hterm b]
    split_ifs with h
    · rw [Fintype.sum_eq_single ⟨(a, j), h⟩]
      · simp
      · intro b hb
        rw [if_neg]
        intro h'
        exact hb (Subtype.ext h')
    · refine Finset.sum_eq_zero fun b _ ↦ ?_
      rw [if_neg]
      intro h'
      exact h (h' ▸ b.2)
  have hsupp : ∀ u j a, ((poly u).coeff j).coeff a ≠ 0 → j < n ∧ n * a + d * j ≤ n * g := by
    intro u j a h
    rw [hcoef] at h
    split_ifs at h with hm
    · exact (mem_basisN n d (n * g) a j hn).mp (List.mem_toFinset.mp hm)
    · exact absurd rfl h
  have hev : ∀ u a b, evalW (poly u) a b = L a b u := by
    intro u a b
    rw [evalW_eq_sum_basis (poly u) hn (hsupp u) a b, hL, ← hB,
      ← Finset.sum_coe_sort B]
    refine Finset.sum_congr rfl fun ai _ ↦ ?_
    rw [hcoef, dif_pos (by simpa using ai.2)]
    ring
  have hL1 : ∀ a b (ai : B), L a b (Pi.single ai 1) = a ^ ai.1.1 * b ^ ai.1.2 := by
    intro a b ai
    rw [hL, Finset.sum_eq_single ai]
    · simp
    · intro b' _ hb'; simp [Pi.single_apply, hb']
    · simp
  have hspan : ∀ i, ∃ c : Fin g × Fin (n - 1) → F,
      ∑ q, c q • L (x q.1) (ζ ^ (q.2.1 + 1) * y q.1) = L (x i) (y i) := by
    intro i
    have hker : ⨅ q : Fin g × Fin (n - 1), LinearMap.ker (L (x q.1) (ζ ^ (q.2.1 + 1) * y q.1)) ≤
        LinearMap.ker (L (x i) (y i)) := by
      intro u hu
      rw [Submodule.mem_iInf] at hu
      rw [LinearMap.mem_ker, ← hev]
      refine cert_implication hζ x y hx hy sj hsj hdet (poly u) (hsupp u) (fun i' k hk1 hkn ↦ ?_) i
      have := hu (i', ⟨k - 1, by omega⟩)
      rw [LinearMap.mem_ker, ← hev] at this
      rwa [show k - 1 + 1 = k by omega] at this
    exact (Submodule.mem_span_range_iff_exists_fun F).mp (mem_span_of_iInf_ker_le_ker hker)
  choose c hc using hspan
  refine ⟨fun i i' k ↦ if h : 1 ≤ k ∧ k < n then c i (i', ⟨k - 1, by omega⟩) else 0, ?_⟩
  intro i ai hai
  have hai' : ai ∈ B := List.mem_toFinset.mpr hai
  have h1 := congrArg (fun φ ↦ φ (Pi.single (⟨ai, hai'⟩ : B) 1)) (hc i)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, hL1, smul_eq_mul] at h1
  rw [← h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i' _ ↦ ?_
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk := k.2
  beta_reduce
  rw [dif_pos ⟨by omega, by omega⟩]
  have hfin : (⟨1 + ↑k - 1, by omega⟩ : Fin (n - 1)) = k := Fin.ext (by simp)
  rw [hfin, add_comm (1 : ℕ) ↑k]

end Dual

section Choose

variable {F : Type*} [Field F]

/-- **Full Fourier inversion**: `∑ⱼ wⱼ ηᵏʲ = 0` for all `k < n` forces `w = 0`. -/
lemma dft_zero {η : F} {n : ℕ} (hη : IsPrimitiveRoot η n) (w : ℕ → F)
    (h : ∀ k < n, ∑ j ∈ Finset.range n, w j * η ^ (k * j) = 0) : ∀ j < n, w j = 0 := by
  have hc := dft_const hη w fun k _ hk ↦ h k hk
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · intro j hj; omega
  haveI : NeZero n := ⟨hn.ne'⟩
  have hn0 : (n : F) ≠ 0 := hη.neZero'.out
  have h0 := h 0 hn
  simp only [zero_mul, pow_zero, mul_one] at h0
  rw [Finset.sum_congr rfl fun j hj ↦ hc j (Finset.mem_range.mp hj)] at h0
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
  have hw0 : w 0 = 0 := (mul_eq_zero.mp h0).resolve_left hn0
  intro j hj
  rw [hc j hj, hw0]

open Classical in
/-- **A non-vanishing conjugate point exists** for a non-zero combination of holomorphic
monomials, among enough candidate `x`. -/
theorem exists_good_point {n d g : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ n) (sj : Fin g → ℕ × ℕ)
    (hinj : Function.Injective sj) (hsj : ∀ l, IsHol n d (sj l)) (c : Fin g → F) (hc : c ≠ 0)
    (Xs used : Finset F) (y : F → F) (hy : ∀ x ∈ Xs, y x ≠ 0) (hX : used.card + d < Xs.card) :
    ∃ x ∈ Xs, x ∉ used ∧ ∃ k < n,
      ∑ l, c l * (x ^ (sj l).1 * ((ζ ^ k * y x) ^ (sj l).2)⁻¹) ≠ 0 := by
  obtain ⟨l0, hl0⟩ : ∃ l0, c l0 ≠ 0 := by
    by_contra h; push_neg at h; exact hc (funext h)
  set js := (sj l0).2 with hjs
  -- the coefficient polynomial of `y^{-js}`
  set p : F[X] := ∑ l ∈ Finset.univ.filter (fun l ↦ (sj l).2 = js), C (c l) * X ^ (sj l).1 with hp
  have hpcoef : p.coeff (sj l0).1 = c l0 := by
    rw [hp, finsetSum_coeff, Finset.sum_eq_single l0]
    · simp
    · intro l hl hll0
      rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
      intro h
      apply hll0
      apply hinj
      ext
      · exact h.symm
      · exact (Finset.mem_filter.mp hl).2
    · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ l0, hjs.symm⟩) h
  have hp0 : p ≠ 0 := fun h ↦ hl0 (by rw [← hpcoef, h, coeff_zero])
  have hpdeg : p.natDegree < d := by
    rw [hp]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := d - 1) fun l _ ↦ ?_) ?_
    · refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_X_pow]
      obtain ⟨h1, h2, h3⟩ := hsj l
      have : n * ((sj l).1 + 1) < d * n := lt_of_lt_of_le h3 (Nat.mul_le_mul_left _ h2.le)
      rw [mul_comm d n] at this
      have := lt_of_mul_lt_mul_left this (Nat.zero_le n)
      omega
    · have := (hsj l0).2.2
      have : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · rw [h, zero_mul] at this; omega
        · exact h
      omega
  -- a candidate avoiding `used` and the roots of `p`
  have hcard : (used ∪ p.roots.toFinset).card < Xs.card := by
    refine lt_of_le_of_lt (Finset.card_union_le _ _) ?_
    have : p.roots.toFinset.card ≤ p.natDegree :=
      (Multiset.toFinset_card_le _).trans (card_roots' p)
    omega
  obtain ⟨x0, hx0X, hx0⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_union, not_or, Multiset.mem_toFinset] at hx0
  obtain ⟨hx0u, hx0r⟩ := hx0
  have hpx0 : p.eval x0 ≠ 0 := fun h ↦ hx0r ((mem_roots hp0).mpr h)
  refine ⟨x0, hx0X, hx0u, ?_⟩
  by_contra hall
  push_neg at hall
  -- all conjugate values vanish: invert
  set η := ζ⁻¹ with hη
  have hηp : IsPrimitiveRoot η n := hζ.inv
  set w : ℕ → F := fun j ↦ ∑ l ∈ Finset.univ.filter (fun l ↦ (sj l).2 = j),
    c l * x0 ^ (sj l).1 * (y x0 ^ j)⁻¹ with hw
  have hyx := hy x0 hx0X
  have hsum : ∀ k < n, ∑ j ∈ Finset.range n, w j * η ^ (k * j) = 0 := by
    intro k hk
    rw [← hall k hk]
    simp only [hw, Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun l ↦ (sj l).2) (t := Finset.range n)
      (fun l _ ↦ Finset.mem_range.mpr (hsj l).2.1)]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l hl ↦ ?_
    rw [(Finset.mem_filter.mp hl).2, hη, mul_pow, inv_pow, ← pow_mul, mul_inv, ← inv_pow]
    ring
  have hwj := dft_zero hηp w hsum js (hsj l0).2.1
  apply hpx0
  have : w js = p.eval x0 * (y x0 ^ js)⁻¹ := by
    simp only [hw, hp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Finset.sum_mul]
  rw [this] at hwj
  exact (mul_eq_zero.mp hwj).resolve_right (inv_ne_zero (pow_ne_zero _ hyx))

end Choose

section Points

variable {F : Type*} [Field F]

open Classical in
/-- **Non-special base points exist**: among more than `g + d` candidate `x` (each with a
non-zero `n`-th root `y x` of `f(x)`), there are `g` points with distinct `x` (on suitable
conjugates `ζᵏ y`) whose matrix of `g` distinct holomorphic monomials is invertible. -/
theorem exists_nonspecial {n d g : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ n) (sj : Fin g → ℕ × ℕ)
    (hinj : Function.Injective sj) (hsj : ∀ l, IsHol n d (sj l)) (Xs : Finset F) (y : F → F)
    (hy : ∀ x ∈ Xs, y x ≠ 0) (hX : g + d < Xs.card) :
    ∃ (xs : Fin g → F) (ks : Fin g → ℕ), Function.Injective xs ∧ (∀ i, xs i ∈ Xs) ∧
      (∀ i, ks i < n) ∧
      (Matrix.of fun i l ↦ xs i ^ (sj l).1 * ((ζ ^ ks i * y (xs i)) ^ (sj l).2)⁻¹).det ≠ 0 := by
  set row : F → ℕ → Fin g → F := fun x k l ↦ x ^ (sj l).1 * ((ζ ^ k * y x) ^ (sj l).2)⁻¹ with hrow
  have key : ∀ t ≤ g, ∃ (xs : Fin t → F) (ks : Fin t → ℕ), Function.Injective xs ∧
      (∀ i, xs i ∈ Xs) ∧ (∀ i, ks i < n) ∧ LinearIndependent F fun i ↦ row (xs i) (ks i) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨Fin.elim0, Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0,
        fun i ↦ i.elim0, linearIndependent_empty_type⟩
    | succ t ih =>
      intro ht
      obtain ⟨xs, ks, hxi, hxX, hkn, hli⟩ := ih (by omega)
      -- a non-zero vector orthogonal to the rows
      let A : (Fin g → F) →ₗ[F] (Fin t → F) :=
        { toFun := fun c i ↦ ∑ l, row (xs i) (ks i) l * c l
          map_add' := fun a b ↦ by funext i; simp [mul_add, Finset.sum_add_distrib]
          map_smul' := fun r a ↦ by
            funext i
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ ↦ by ring }
      have hker : LinearMap.ker A ≠ ⊥ :=
        LinearMap.ker_ne_bot_of_finrank_lt (by simp; omega)
      obtain ⟨c, hcA, hc0⟩ := (Submodule.ne_bot_iff _).mp hker
      rw [LinearMap.mem_ker] at hcA
      have hcA' : ∀ i, ∑ l, row (xs i) (ks i) l * c l = 0 := fun i ↦ congrFun hcA i
      have hused : (Finset.univ.image xs).card + d < Xs.card := by
        have := Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := xs)
        simp at this
        omega
      obtain ⟨x0, hx0X, hx0u, k, hk, hval⟩ := exists_good_point hζ sj hinj hsj c hc0 Xs
        (Finset.univ.image xs) y hy hused
      have hx0 : ∀ i, xs i ≠ x0 := fun i h ↦ hx0u (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
      refine ⟨Fin.snoc (α := fun _ ↦ F) xs x0, Fin.snoc (α := fun _ ↦ ℕ) ks k, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => rfl
          | cast j =>
            simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
            exact absurd hij.symm (hx0 j)
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
            exact absurd hij (hx0 i)
          | cast j =>
            simp only [Fin.snoc_castSucc] at hij
            rw [hxi hij]
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hx0X
        | cast i => simpa using hxX i
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hk
        | cast i => simpa using hkn i
      · have hfun : (fun i ↦ row (Fin.snoc (α := fun _ ↦ F) xs x0 i)
            (Fin.snoc (α := fun _ ↦ ℕ) ks k i)) =
            Fin.snoc (fun i ↦ row (xs i) (ks i)) (row x0 k) := by
          funext i
          induction i using Fin.lastCases with
          | last => simp
          | cast i => simp
        rw [hfun, linearIndependent_finSnoc]
        refine ⟨hli, fun hmem ↦ hval ?_⟩
        -- the functional `v ↦ ∑ v_l c_l` kills the span of the rows
        let φ : (Fin g → F) →ₗ[F] F :=
          { toFun := fun v ↦ ∑ l, v l * c l
            map_add' := fun a b ↦ by simp [add_mul, Finset.sum_add_distrib]
            map_smul' := fun r a ↦ by
              simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ ↦ by ring }
        have hspan : Submodule.span F (Set.range fun i ↦ row (xs i) (ks i)) ≤ LinearMap.ker φ := by
          rw [Submodule.span_le]
          rintro v ⟨i, rfl⟩
          exact hcA' i
        have := hspan hmem
        rw [LinearMap.mem_ker] at this
        rw [← this]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        simp only [φ, hrow, LinearMap.coe_mk, AddHom.coe_mk]
        ring
  obtain ⟨xs, ks, hxi, hxX, hkn, hli⟩ := key g le_rfl
  refine ⟨xs, ks, hxi, hxX, hkn, ?_⟩
  have hunit : IsUnit (Matrix.of fun i l ↦ xs i ^ (sj l).1 * ((ζ ^ ks i * y (xs i)) ^ (sj l).2)⁻¹) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hli
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero

end Points

section Count

lemma pred_div {A n : ℕ} (hn : 0 < n) (hA : A % n ≠ 0) : (A - 1) / n = A / n := by
  have h := Nat.div_add_mod A n
  have hlt := Nat.mod_lt A hn
  have e : A - 1 = n * (A / n) + (A % n - 1) := by omega
  rw [e, Nat.mul_add_div hn, Nat.div_eq_of_lt (show A % n - 1 < n by omega), add_zero]

/-- One pair `j, n − j`: `⌊(dj − 1)/n⌋ + ⌊(d(n − j) − 1)/n⌋ = d − 1` for coprime `n, d`. -/
lemma pair_sum {n d j : ℕ} (hcop : Nat.Coprime n d) (hj1 : 1 ≤ j) (hjn : j < n) :
    (d * j - 1) / n + (d * (n - j) - 1) / n = d - 1 := by
  have hn : 0 < n := by omega
  have hndv : ∀ m, 0 < m → m < n → d * m % n ≠ 0 := by
    intro m hm0 hmn h
    have := Nat.Coprime.dvd_of_dvd_mul_left hcop (Nat.dvd_of_mod_eq_zero h)
    have := Nat.le_of_dvd hm0 this
    omega
  have hA := hndv j (by omega) hjn
  have hB := hndv (n - j) (by omega) (by omega)
  rw [pred_div hn hA, pred_div hn hB]
  have hsum : d * j + d * (n - j) = d * n := by rw [← Nat.mul_add]; congr 1; omega
  have hadd := Nat.add_div (a := d * j) (b := d * (n - j)) hn
  rw [hsum, Nat.mul_div_cancel _ hn] at hadd
  have hS : d * j % n + d * (n - j) % n = n := by
    have h0 : (d * j % n + d * (n - j) % n) % n = 0 := by
      rw [← Nat.add_mod, hsum, Nat.mul_mod_left]
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h0
    have h1 := Nat.mod_lt (d * j) hn
    have h2 := Nat.mod_lt (d * (n - j)) hn
    have h3 : 0 < d * j % n := Nat.pos_of_ne_zero hA
    rcases t with _ | _ | t
    · omega
    · omega
    · have : n * (t + 1 + 1) ≥ 2 * n := by nlinarith
      omega
  rw [if_pos (by omega)] at hadd
  generalize d * j / n = a at hadd ⊢
  generalize d * (n - j) / n = b at hadd ⊢
  omega

/-- **The number of holomorphic monomials**: `2 ∑_{1 ≤ j < n} ⌊(dj − 1)/n⌋ = (n − 1)(d − 1)` for
coprime `n, d`. -/
lemma two_sum_hol {n d : ℕ} (hcop : Nat.Coprime n d) :
    2 * ∑ j ∈ Finset.Ico 1 n, (d * j - 1) / n = (n - 1) * (d - 1) := by
  have hrefl : ∑ j ∈ Finset.Ico 1 n, (d * j - 1) / n =
      ∑ j ∈ Finset.Ico 1 n, (d * (n - j) - 1) / n := by
    refine Finset.sum_nbij' (fun j ↦ n - j) (fun j ↦ n - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp at hj ⊢; omega
    · intro j hj; simp at hj ⊢; omega
    · intro j hj; simp at hj; omega
    · intro j hj; simp at hj; omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      rw [show n - (n - j) = j by omega]
  rw [two_mul]
  nth_rewrite 2 [hrefl]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun j hj ↦ pair_sum hcop
    (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2]
  simp

open Classical in
/-- **Enough holomorphic monomials**: for coprime `n, d`, there are `g = ((n−1)(d−1)+1)/2`
distinct ones. -/
theorem exists_hol {n d : ℕ} (hcop : Nat.Coprime n d) :
    ∃ sj : Fin (((n - 1) * (d - 1) + 1) / 2) → ℕ × ℕ, Function.Injective sj ∧
      ∀ l, IsHol n d (sj l) := by
  set H : Finset (ℕ × ℕ) := (Finset.Ico 1 n).biUnion fun j ↦
    (Finset.range ((d * j - 1) / n)).image fun s ↦ (s, j) with hH
  have hHol : ∀ p ∈ H, IsHol n d p := by
    intro p hp
    obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hj1, hjn⟩ := Finset.mem_Ico.mp hj
    refine ⟨hj1, hjn, ?_⟩
    have hs' := Finset.mem_range.mp hs
    show n * (s + 1) < d * j
    have h1 : n * (s + 1) ≤ n * ((d * j - 1) / n) := Nat.mul_le_mul_left n hs'
    have h2 : n * ((d * j - 1) / n) ≤ d * j - 1 := by
      rw [mul_comm]; exact Nat.div_mul_le_self _ _
    have h3 : 1 ≤ d * j := by
      rcases Nat.eq_zero_or_pos (d * j) with h | h
      · rw [h, Nat.zero_sub, Nat.zero_div] at hs'; omega
      · exact h
    omega
  have hcard : H.card = ∑ j ∈ Finset.Ico 1 n, (d * j - 1) / n := by
    rw [hH, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.card_image_of_injective _ (fun a b h ↦ (Prod.mk.inj h).1), Finset.card_range]
    · intro j _ j' _ hjj'
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp hp'
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨_, _, h⟩ := Finset.mem_image.mp hp'
      exact hjj' (Prod.mk.inj h).2.symm
  have htwo := two_sum_hol hcop
  have hev : 2 ∣ (n - 1) * (d - 1) := ⟨_, htwo.symm⟩
  have hle : ((n - 1) * (d - 1) + 1) / 2 ≤ H.card := by
    rw [hcard]; omega
  refine ⟨fun l ↦ (H.equivFin.symm (Fin.castLE hle l)).1, ?_, fun l ↦ hHol _ (Subtype.prop _)⟩
  intro a b hab
  have := Subtype.ext hab
  have := H.equivFin.symm.injective this
  exact Fin.castLE_injective hle this

end Count

end Sup
