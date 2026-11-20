import RischTragerBronstein.Mixed.NKSplitGauge
import RischTragerBronstein.Mixed.NKRamUnits

/-!
# Expansions at ramified places at infinity

For a single slope `s'/e` at infinity, the monomials `μⱼ = θʲ/x^{gⱼ}` with `gⱼ = ⌈j s'/e⌉` have
order `levⱼ/e` (`levⱼ = e gⱼ − j s' < e`) at every place at infinity. Along a branch system
`x = T^{-N}`, `N = N' e`, with `σ = N' s'`:
`μⱼ = (ρ T^σ)ʲ T^{N' levⱼ}` (`embG_expandG`, `expand_ram`), and the coefficients `Bⱼ = Wⱼ x^{gⱼ}/Q`
of a function `z Q = ∑ Wⱼ θʲ` without pole above infinity are bounded (`bounded_ram`: the matrix
`(ρ T^σ)ʲ` over the `n` roots is a Vandermonde matrix in their distinct leading values).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

/-- `gⱼ = ⌈j s'/e⌉`. -/
def gR (e sR j : ℕ) : ℕ := (j * sR + e - 1) / e

/-- The level `e gⱼ − j s'` of `θʲ/x^{gⱼ}`. -/
def levR (e sR j : ℕ) : ℕ := e * gR e sR j - j * sR

lemma gR_spec (e sR j : ℕ) (he : 0 < e) :
    e * gR e sR j = j * sR + levR e sR j ∧ levR e sR j < e := by
  have h1 : (j * sR + e - 1) / e * e ≤ j * sR + e - 1 := Nat.div_mul_le_self _ _
  have h2 : j * sR + e - 1 < (j * sR + e - 1) / e * e + e := Nat.lt_div_mul_add he
  unfold levR gR
  rw [Nat.mul_comm e ((j * sR + e - 1) / e)]
  constructor <;> omega

namespace CurveData

section Expand

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

variable (S : CurveData C L)

/-- **Expansion along a branch above infinity with any exponents `gⱼ`**: if `z Q(x) = ∑ Wⱼ(x) yʲ`
then `z = ∑ⱼ (Wⱼ x^{gⱼ})(T^{-N}) / Q(T^{-N}) · rʲ T^{N gⱼ}`. -/
lemma embG_expandG (N : ℕ) (hN : 0 < N) (g : ℕ → ℕ) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0) (z : C⟮S.x⟯⟮S.y⟯) (W : C[X][X]) (Q : C[X])
    (hQ : Q ≠ 0) (hWQ : (z : L) * aeval S.x Q = S.evXY W) (hWn : W.natDegree < S.F.natDegree) :
    S.embG (infSub N) (infSub_injective N hN) r hr z =
      ∑ j ∈ Finset.range S.F.natDegree, infSub (K := K) N (W.coeff j * X ^ g j) *
        (infSub (K := K) N Q)⁻¹ * (r ^ j * single ((N * g j : ℕ) : ℤ) 1) := by
  have hQ' := infSub_ne_zero (K := K) N hN Q hQ
  have e := congrArg (S.embG (infSub N) (infSub_injective N hN) r hr)
    (show z * ⟨aeval S.x Q, S.aeval_mem Q⟩ = ⟨S.evXY W, S.evXY_mem W⟩ from Subtype.ext hWQ)
  rw [map_mul, S.embG_polyX, S.embG_wE_eq (RingHom.id C) W,
    eval_eq_sum_range' (by rw [natDegree_map_eq_of_injective (infSub_injective N hN)]; exact hWn)]
    at e
  have e2 : S.embG (infSub N) (infSub_injective N hN) r hr z =
      (∑ j ∈ Finset.range S.F.natDegree, (W.map (infSub N)).coeff j * r ^ j) *
        (infSub (K := K) N Q)⁻¹ := by
    rw [← e, mul_assoc, mul_inv_cancel₀ hQ', mul_one]
  rw [e2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have key : (single (-(N : ℤ)) (1 : K)) ^ (g j) * single ((N * g j : ℕ) : ℤ) (1 : K) = 1 := by
    rw [single_pow, one_pow, single_mul_single, mul_one]
    convert HahnSeries.single_zero_one using 2
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [coeff_map, map_mul, map_pow, infSub_X_K]
  linear_combination (-(infSub (K := K) N (W.coeff j) * r ^ j * (infSub (K := K) N Q)⁻¹)) * key

/-- **The expansion in the monomials of a slope `s'/e`** (`N = N' e`, `σ = N' s'`). -/
lemma expand_ram (e sR N' : ℕ) (he : 0 < e) (hN' : 0 < N') (r : LaurentSeries K)
    (hr : (S.F.map (infSub (N' * e))).eval r = 0) (z : C⟮S.x⟯⟮S.y⟯) (W : C[X][X]) (Q : C[X])
    (hQ : Q ≠ 0) (hWQ : (z : L) * aeval S.x Q = S.evXY W) (hWn : W.natDegree < S.F.natDegree) :
    S.embG (infSub (N' * e)) (infSub_injective (N' * e) (Nat.mul_pos hN' he)) r hr z =
      ∑ j ∈ Finset.range S.F.natDegree,
        (infSub (K := K) (N' * e) (W.coeff j * X ^ gR e sR j) * (infSub (K := K) (N' * e) Q)⁻¹ *
          single ((N' * levR e sR j : ℕ) : ℤ) 1) * (r * single ((N' * sR : ℕ) : ℤ) 1) ^ j := by
  rw [S.embG_expandG (N' * e) (Nat.mul_pos hN' he) (gR e sR) r hr z W Q hQ hWQ hWn]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h := (gR_spec e sR j he).1
  have hexp : (((N' * e * gR e sR j : ℕ)) : ℤ) = ((N' * levR e sR j : ℕ) : ℤ) + j * ((N' * sR : ℕ) : ℤ) := by
    have : N' * e * gR e sR j = N' * levR e sR j + j * (N' * sR) := by
      rw [mul_assoc, h]; ring
    rw [this]; push_cast; ring
  rw [hexp, mul_pow, single_pow, one_pow, nsmul_eq_mul]
  rw [show (single (((N' * levR e sR j : ℕ) : ℤ) + j * ((N' * sR : ℕ) : ℤ)) (1 : K)) =
    single ((N' * levR e sR j : ℕ) : ℤ) 1 * single ((j : ℤ) * ((N' * sR : ℕ) : ℤ)) 1 by
    rw [single_mul_single, one_mul]]
  ring

/-- **The coefficients of a function without pole above infinity are bounded** (single slope
`s'/e`, distinct leading values of the `n` roots). -/
theorem bounded_ram (e sR N' : ℕ) (he : 0 < e) (hN' : 0 < N') (l : List (LaurentSeries K))
    (hl : S.F.map (infSub (N' * e)) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (hLB : ∀ r ∈ l, LowerBd (r * single ((N' * sR : ℕ) : ℤ) 1) 0)
    (hnd : (l.map fun r ↦ (r * single ((N' * sR : ℕ) : ℤ) 1).coeff 0).Nodup)
    (z : C⟮S.x⟯⟮S.y⟯) (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0)
    (hWQ : (z : L) * aeval S.x Q = S.evXY W) (hWn : W.natDegree < S.F.natDegree)
    (hz : ∀ r (hr : r ∈ l), LowerBd (S.embG (infSub (N' * e))
      (infSub_injective (N' * e) (Nat.mul_pos hN' he)) r (S.root_of_mem hl hr) z) 0) :
    ∀ j < S.F.natDegree, (W.coeff j * X ^ gR e sR j).natDegree ≤ Q.natDegree := by
  classical
  set n := S.F.natDegree with hn
  have hNe := Nat.mul_pos hN' he
  have hlenl : l.length = n := S.length_of_split hl
  set ρ : Fin n → LaurentSeries K := fun p ↦ l.get ⟨p, by rw [hlenl]; exact p.2⟩ with hρ
  have hρl : ∀ p, ρ p ∈ l := fun p ↦ List.get_mem _ _
  set b : LaurentSeries K := single ((N' * sR : ℕ) : ℤ) 1 with hb
  set M : Matrix (Fin n) (Fin n) (LaurentSeries K) := Matrix.of fun j p ↦ (ρ p * b) ^ (j : ℕ) with hM
  have hMLB : ∀ j p, LowerBd (M j p) 0 := fun j p ↦ lowerBd_pow0 (hLB _ (hρl p)) _
  have hdet : (M.det).coeff 0 ≠ 0 := by
    rw [coeff_zero_det_of_lowerBd M hMLB]
    have e1 : (M.map fun z ↦ z.coeff 0) =
        (Matrix.vandermonde fun p ↦ (ρ p * b).coeff 0).transpose := by
      ext j p
      simp only [hM, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
        Matrix.vandermonde]
      rw [coeff_zero_pow_of_lowerBd (hLB _ (hρl p))]
    rw [e1, Matrix.det_transpose]
    refine Matrix.det_vandermonde_ne_zero_iff.mpr fun p q hpq ↦ ?_
    have h1 := List.inj_on_of_nodup_map hnd (hρl p) (hρl q) hpq
    have := (List.Nodup.get_inj_iff (List.Nodup.of_map _ hnd)).mp h1
    exact Fin.ext (by simpa using congrArg Fin.val this)
  set x : Fin n → LaurentSeries K := fun j ↦ infSub (K := K) (N' * e) (W.coeff j * X ^ gR e sR j) *
    (infSub (K := K) (N' * e) Q)⁻¹ * single ((N' * levR e sR j : ℕ) : ℤ) 1 with hx
  have hxLB : ∀ j, LowerBd (x j) 0 := lowerBd_of_vecMul M hMLB hdet x fun p ↦ by
    have h1 := S.expand_ram e sR N' he hN' (ρ p) (S.root_of_mem hl (hρl p)) z W Q hQ hWQ hWn
    have h2 := hz (ρ p) (hρl p)
    rw [h1] at h2
    have e3 : (∑ j : Fin n, x j * M j p) = ∑ j ∈ Finset.range n,
        (infSub (K := K) (N' * e) (W.coeff j * X ^ gR e sR j) * (infSub (K := K) (N' * e) Q)⁻¹ *
          single ((N' * levR e sR j : ℕ) : ℤ) 1) * (ρ p * single ((N' * sR : ℕ) : ℤ) 1) ^ j := by
      rw [Finset.sum_range]; rfl
    rw [e3]; exact h2
  intro j hj
  set P := W.coeff j * X ^ gR e sR j with hP
  by_cases hP0 : P = 0
  · rw [hP0, natDegree_zero]; exact Nat.zero_le _
  have hLBj := hxLB ⟨j, hj⟩
  simp only [hx] at hLBj
  have hP' := infSub_ne_zero (K := K) (N' * e) hNe P hP0
  have hQ' := infSub_ne_zero (K := K) (N' * e) hNe Q hQ
  have ho := order_nonneg_of_lowerBd_nk _ hLBj
  rw [HahnSeries.order_mul (mul_ne_zero hP' (inv_ne_zero hQ')) (by simp),
    HahnSeries.order_mul hP' (inv_ne_zero hQ'), order_inv_nk _ hQ', order_infSub _ hNe P hP0,
    order_infSub _ hNe Q hQ, HahnSeries.order_single (one_ne_zero)] at ho
  have hlev := (gR_spec e sR j he).2
  have hNe' : (0 : ℤ) < N' * e := by exact_mod_cast hNe
  by_contra hcon
  push Not at hcon
  have h3 : ((N' * levR e sR j : ℕ) : ℤ) < N' * e := by
    have : N' * levR e sR j < N' * e := Nat.mul_lt_mul_of_pos_left hlev hN'
    exact_mod_cast this
  have h4 : ((N' * e : ℕ) : ℤ) * (Q.natDegree + 1) ≤ (N' * e : ℕ) * P.natDegree := by
    have : Q.natDegree + 1 ≤ P.natDegree := hcon
    exact_mod_cast Nat.mul_le_mul_left _ this
  push_cast at ho h3 h4
  nlinarith

end Expand

end CurveData

end Curves
