import RischTragerBronstein.Curves.IntBasisInf
import RischTragerBronstein.Curves.LScale
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Residue matrices of logarithmic derivations on integral bases

Along a branch `x = Tᴺ` (resp. `x = T^{−N}`), `x d/dx` is `(1/N) T d/dT` (resp. `−(1/N) T d/dT`),
which multiplies `Tʲ` by `j/N` (resp. `−j/N`). By the Puiseux support lemma (`branch_support`)
the exponents `j/N` of an expansion lie in `(1/n!) ℤ`, so `∏_{k<n!} (x d/dx − k/n!)` maps
expansions without pole to expansions divisible by `x`. On an integral basis this says that the
residue matrix of the logarithmic derivation at `x = 0` (resp. at infinity, on a reduced basis)
is annihilated by `∏_{k<n!} (X − k/n!)` (resp. `∏_{k<n!} (X + k/n!)`): it is diagonalizable with
rational eigenvalues.

This file: the series part (`opL_lowerBd`).
-/

open Polynomial HahnSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential LaurentSeries

section Series

variable {K : Type*} [Field K]

/-- `c T d/dT`. -/
noncomputable def thetaS (c : K) (u : LaurentSeries K) : LaurentSeries K :=
  single 1 c * LaurentSeries.derivative K u

lemma thetaS_coeff (c : K) (u : LaurentSeries K) (j : ℤ) :
    (thetaS c u).coeff j = c * j * u.coeff j := by
  rw [thetaS, HahnSeries.coeff_single_mul, LaurentSeries.derivative_coeff, sub_add_cancel]
  ring

lemma thetaS_sub (c : K) (u v : LaurentSeries K) : thetaS c (u - v) = thetaS c u - thetaS c v := by
  rw [thetaS, thetaS, thetaS, map_sub, mul_sub]

lemma LowerBd.thetaS {u : LaurentSeries K} {m : ℤ} (hu : LowerBd u m) (c : K) :
    LowerBd (Curves.thetaS c u) m := fun k hk ↦ by rw [thetaS_coeff, hu k hk, mul_zero]

/-- `∏ (Φ − μ)` applied to `u`. -/
noncomputable def opL (Φ : LaurentSeries K → LaurentSeries K) : List K → LaurentSeries K → LaurentSeries K
  | [], u => u
  | μ :: μs, u => Φ (opL Φ μs u) - HahnSeries.C μ * opL Φ μs u

lemma C_mul_coeff (μ : K) (u : LaurentSeries K) (j : ℤ) :
    (HahnSeries.C μ * u).coeff j = μ * u.coeff j := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero]

lemma LowerBd.C_mul {u : LaurentSeries K} {m : ℤ} (hu : LowerBd u m) (μ : K) :
    LowerBd (HahnSeries.C μ * u) m := fun k hk ↦ by rw [C_mul_coeff, hu k hk, mul_zero]

/-- The constant-coefficient operator `s c T d/dT` acts diagonally. -/
lemma opL_const_coeff (s c : K) (μs : List K) (u : LaurentSeries K) (j : ℤ) :
    (opL (fun v ↦ HahnSeries.C s * thetaS c v) μs u).coeff j =
      (μs.map fun μ ↦ s * c * j - μ).prod * u.coeff j := by
  induction μs with
  | nil => simp [opL]
  | cons μ μs ih =>
    simp only [opL, HahnSeries.coeff_sub, C_mul_coeff, thetaS_coeff, ih, List.map_cons, List.prod_cons]
    ring

/-- **Approximation**: if `h ≡ s` modulo `T^N`, then `∏ (h θ − μ)` and `∏ (s θ − μ)` agree modulo
`T^N` on series without pole. -/
lemma opL_approx (h : LaurentSeries K) (s c : K) (N : ℤ) (hN : 0 ≤ N)
    (hh : LowerBd (h - HahnSeries.C s) N) (μs : List K) (u : LaurentSeries K) (hu : LowerBd u 0) :
    LowerBd (opL (fun v ↦ h * thetaS c v) μs u - opL (fun v ↦ HahnSeries.C s * thetaS c v) μs u) N ∧
      LowerBd (opL (fun v ↦ h * thetaS c v) μs u) 0 ∧
      LowerBd (opL (fun v ↦ HahnSeries.C s * thetaS c v) μs u) 0 := by
  have hh0 : LowerBd h 0 := by
    have := (hh.mono hN).add (lowerBd_C s)
    rwa [sub_add_cancel] at this
  induction μs with
  | nil => simp only [opL, sub_self]; exact ⟨lowerBd_zero N, hu, hu⟩
  | cons μ μs ih =>
    obtain ⟨hd, ha, hb⟩ := ih
    set a := opL (fun v ↦ h * thetaS c v) μs u
    set b := opL (fun v ↦ HahnSeries.C s * thetaS c v) μs u
    simp only [opL]
    refine ⟨?_, ?_, ?_⟩
    · have e : h * thetaS c a - HahnSeries.C μ * a - (HahnSeries.C s * thetaS c b - HahnSeries.C μ * b) =
          h * thetaS c (a - b) + (h - HahnSeries.C s) * thetaS c b - HahnSeries.C μ * (a - b) := by
        rw [thetaS_sub]; ring
      rw [e]
      have h1 := hh0.mul (hd.thetaS c)
      have h2 := hh.mul (hb.thetaS c)
      rw [zero_add] at h1
      rw [add_zero] at h2
      exact (h1.add h2).sub (hd.C_mul μ)
    · have := (hh0.mul (ha.thetaS c)).sub (ha.C_mul μ)
      rwa [add_zero] at this
    · have := ((lowerBd_C s).mul (hb.thetaS c)).sub (hb.C_mul μ)
      rwa [add_zero] at this

/-- **`∏ (h θ − μ)` divides by `T^N`** when every exponent `0 ≤ j < N` of `u` is killed by the
diagonal operator. -/
lemma opL_lowerBd (h : LaurentSeries K) (s c : K) (N : ℤ) (hN : 0 ≤ N)
    (hh : LowerBd (h - HahnSeries.C s) N) (μs : List K) (u : LaurentSeries K) (hu : LowerBd u 0)
    (hvan : ∀ j : ℤ, 0 ≤ j → j < N → u.coeff j ≠ 0 → (μs.map fun μ ↦ s * c * j - μ).prod = 0) :
    LowerBd (opL (fun v ↦ h * thetaS c v) μs u) N := by
  obtain ⟨hd, -, -⟩ := opL_approx h s c N hN hh μs u hu
  have hc : LowerBd (opL (fun v ↦ HahnSeries.C s * thetaS c v) μs u) N := by
    intro j hj
    rw [opL_const_coeff]
    by_cases hj0 : j < 0
    · rw [hu j hj0, mul_zero]
    by_cases hu0 : u.coeff j = 0
    · rw [hu0, mul_zero]
    · rw [hvan j (by omega) hj hu0, zero_mul]
  have := hd.add hc
  rwa [sub_add_cancel] at this

end Series

section Coord

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

/-- The coordinates of `S₀ d/dx` on `∑ aⱼ wⱼ`, for `S₀ wᵢ′ = ∑ Pᵢⱼ wⱼ`. -/
noncomputable def dC {n : ℕ} (S0 : C[X]) (P : Fin n → Fin n → C[X]) (a : Fin n → C[X]) :
    Fin n → C[X] :=
  fun j ↦ S0 * derivative (a j) + ∑ i, a i * P i j

/-- The coordinates of `∏ (S₀ d/dx − μ)`. -/
noncomputable def opC {n : ℕ} (S0 : C[X]) (P : Fin n → Fin n → C[X]) :
    List C → (Fin n → C[X]) → Fin n → C[X]
  | [], a => a
  | μ :: μs, a => fun j ↦ dC S0 P (opC S0 P μs a) j - Polynomial.C μ * opC S0 P μs a j

namespace CurveData

variable (S : CurveData C L) (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)

/-- `S₀ d/dx` on the function field. -/
noncomputable def dS (S0 : C[X]) (z : C⟮S.x⟯⟮S.y⟯) : C⟮S.x⟯⟮S.y⟯ :=
  S.polyE S0 * ⟨(z : L)′, S.derivClosedXY hC hx z z.2⟩

/-- `∏ (S₀ d/dx − μ)` on the function field. -/
noncomputable def opZ (S0 : C[X]) : List C → C⟮S.x⟯⟮S.y⟯ → C⟮S.x⟯⟮S.y⟯
  | [], z => z
  | μ :: μs, z => S.dS hC hx S0 (opZ S0 μs z) - S.polyE (Polynomial.C μ) * opZ S0 μs z

lemma dS_sum {n : ℕ} (S0 : C[X]) (P : Fin n → Fin n → C[X]) (w : Fin n → C⟮S.x⟯⟮S.y⟯)
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXY hC hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE S0 =
      ∑ j, S.polyE (P i j) * w j) (a : Fin n → C[X]) :
    S.dS hC hx S0 (∑ j, S.polyE (a j) * w j) = ∑ j, S.polyE (dC S0 P a j) * w j := by
  apply Subtype.ext
  have hP' : ∀ i, ((w i : L))′ * aeval S.x S0 = ∑ j, aeval S.x (P i j) * (w j : L) := fun i ↦ by
    have := congrArg (fun t : C⟮S.x⟯⟮S.y⟯ ↦ (t : L)) (hP i)
    simpa only [MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum] using this
  simp only [dS, dC, MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum, map_add, map_mul,
    map_sum, add_mul, Finset.sum_add_distrib]
  simp only [Derivation.leibniz, smul_eq_mul, Differential.deriv_aeval_x S.x hC hx, Finset.mul_sum,
    mul_add, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun j _ ↦ by ring
  · have e : ∀ j, aeval S.x S0 * (aeval S.x (a j) * ((w j : L))′) =
        aeval S.x (a j) * ∑ k, aeval S.x (P j k) * (w k : L) := fun j ↦ by
      rw [← hP' j]; ring
    simp only [e, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring

lemma opZ_sum {n : ℕ} (S0 : C[X]) (P : Fin n → Fin n → C[X]) (w : Fin n → C⟮S.x⟯⟮S.y⟯)
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXY hC hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE S0 =
      ∑ j, S.polyE (P i j) * w j) (μs : List C) (a : Fin n → C[X]) :
    S.opZ hC hx S0 μs (∑ j, S.polyE (a j) * w j) = ∑ j, S.polyE (opC S0 P μs a j) * w j := by
  induction μs with
  | nil => rfl
  | cons μ μs ih =>
    rw [opZ, ih, S.dS_sum hC hx S0 P w hP, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [opC, S.polyE_sub, S.polyE_mul]
    ring

end CurveData

/-- At `x = 0` (with `S₀(0) = 0`) the coordinates of `∏ (S₀ d/dx − μ)` are `a(0) ∏ (P(0) − μ)`. -/
lemma opC_eval_zero {n : ℕ} (S0 : C[X]) (hS0 : S0.eval 0 = 0) (P : Fin n → Fin n → C[X])
    (μs : List C) (a : Fin n → C[X]) :
    (fun j ↦ (opC S0 P μs a j).eval 0) = Matrix.vecMul (fun j ↦ (a j).eval 0)
      (μs.foldr (fun μ M ↦ M * (Matrix.of (fun i j ↦ (P i j).eval 0) - μ • 1)) 1) := by
  induction μs with
  | nil => funext j; simp [opC]
  | cons μ μs ih =>
    funext j
    simp only [opC, dC, eval_sub, eval_add, eval_mul, hS0, zero_mul, zero_add, eval_finsetSum,
      eval_C, List.foldr_cons]
    rw [← Matrix.vecMul_vecMul, ← ih]
    simp only [Matrix.vecMul, dotProduct, Matrix.sub_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring

end Coord

section Zero

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L) (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)

lemma regularFinite_span {n : ℕ} {w : Fin n → C⟮S.x⟯⟮S.y⟯} (hw : ∀ j, S.RegularFinite K (w j))
    (a : Fin n → C[X]) : S.RegularFinite K (∑ j, S.polyE (a j) * w j) :=
  S.regularFinite_sum _ _ fun j _ ↦ S.regularFinite_polyE_mul _ (hw j)

/-- Along `x = Tᴺ`, `S₀ d/dx = S₁(Tᴺ) (1/N) T d/dT` for `S₀ = x S₁`. -/
lemma embG_dS_zero (N : ℕ) (hN : 0 < N) (S0 S1 : C[X]) (hS : S0 = X * S1) (r : LaurentSeries K)
    (hY : (S.F.map (branchSub N 0)).eval r = 0) (v : C⟮S.x⟯⟮S.y⟯) :
    S.embG (branchSub N 0) (branchSub_injective N hN 0) r hY (S.dS hC hx S0 v) =
      branchSub N 0 S1 * thetaS (N : K)⁻¹
        (S.embG (branchSub N 0) (branchSub_injective N hN 0) r hY v) := by
  have hd := S.embG_derivG (HahnSeries.C (0 : K) + single (N : ℤ) (1 : K))
    (derivation_branchX_ne N hN 0) (branchSub N 0) (branchSub_injective N hN 0)
    (fun P ↦ by rw [SuperData.branchSub_eq_subst]) hC hx r hY (v : L) v.2
  simp only [Subtype.coe_eta] at hd
  rw [dS, map_mul, S.embG_polyX, hd]
  show branchSub N 0 S0 * ((LaurentSeries.derivation (HahnSeries.C (0 : K) +
    single (N : ℤ) (1 : K)))⁻¹ * LaurentSeries.derivation _) = _
  rw [SuperData.derivation_branchX N hN 0, LaurentSeries.derivation_apply, hS, map_mul, bs_X,
    map_zero, zero_add, thetaS, HahnSeries.inv_single]
  have e : single (N : ℤ) (1 : K) * single (-((N : ℤ) - 1)) (N : K)⁻¹ = single 1 (N : K)⁻¹ := by
    rw [HahnSeries.single_mul_single, one_mul, show (N : ℤ) + -((N : ℤ) - 1) = 1 by ring]
  rw [← e]
  ring_nf

lemma embG_opZ_zero (N : ℕ) (hN : 0 < N) (S0 S1 : C[X]) (hS : S0 = X * S1) (r : LaurentSeries K)
    (hY : (S.F.map (branchSub N 0)).eval r = 0) (μs : List C) (v : C⟮S.x⟯⟮S.y⟯) :
    S.embG (branchSub N 0) (branchSub_injective N hN 0) r hY (S.opZ hC hx S0 μs v) =
      opL (fun u ↦ branchSub N 0 S1 * thetaS (N : K)⁻¹ u) (μs.map (algebraMap C K))
        (S.embG (branchSub N 0) (branchSub_injective N hN 0) r hY v) := by
  induction μs with
  | nil => rfl
  | cons μ μs ih =>
    rw [opZ, map_sub, S.embG_dS_zero hC hx N hN S0 S1 hS r hY, map_mul, S.embG_polyX, ih, bs_C,
      List.map_cons, opL]

lemma lowerBd_branchSub_sub (N : ℕ) (S1 : C[X]) :
    LowerBd (branchSub (K := K) N 0 S1 - HahnSeries.C (algebraMap C K (S1.eval 0))) N := by
  obtain ⟨Q, hQ⟩ : X ∣ S1 - Polynomial.C (S1.eval 0) := by
    rw [X_dvd_iff, Polynomial.coeff_sub, coeff_C_zero, coeff_zero_eq_eval_zero, sub_self]
  have e : branchSub (K := K) N 0 S1 - HahnSeries.C (algebraMap C K (S1.eval 0)) =
      single (N : ℤ) 1 * branchSub N 0 Q := by
    rw [← bs_C, ← map_sub, hQ, map_mul, bs_X, map_zero, zero_add]
  rw [e]
  have := (lowerBd_single (N : ℤ) (1 : K)).mul (lowerBd_branchSub_nonneg (C := C) N (0 : K) Q)
  rwa [add_zero] at this

end CurveData

/-- **Matching exponents**: if `N ∣ d j` with `1 ≤ d ≤ n` and `0 ≤ j < N`, then `j/N = k/n!` for some
`k < n!`. -/
lemma exists_k (n N : ℕ) (hN : 0 < N) (d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n) (j : ℤ)
    (hj0 : 0 ≤ j) (hjN : j < N) (hdiv : (N : ℤ) ∣ d * j) :
    ∃ k : ℕ, k < n.factorial ∧ j * n.factorial = N * k := by
  obtain ⟨m, hm⟩ := hdiv
  obtain ⟨e, he⟩ := Nat.dvd_factorial hd1 hdn
  have hm0 : 0 ≤ m := by
    by_contra h
    have : (N : ℤ) * m < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hN) (by omega)
    have : (0 : ℤ) ≤ d * j := mul_nonneg (by positivity) hj0
    omega
  set k := m.toNat * e with hk
  have hjk : j * n.factorial = N * k := by
    rw [he, hk]; push_cast; rw [Int.toNat_of_nonneg hm0]
    linear_combination (e : ℤ) * hm
  refine ⟨k, ?_, hjk⟩
  have hf : (0 : ℤ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have : (N : ℤ) * k < N * n.factorial := by
    rw [← hjk]; exact mul_lt_mul_of_pos_right hjN hf
  exact_mod_cast lt_of_mul_lt_mul_left this (by positivity)

/-- **The exponents are killed** at `x = 0`. -/
lemma prod_vanish (n N : ℕ) (hN : 0 < N) (d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n) (s : K) (j : ℤ)
    (hj0 : 0 ≤ j) (hjN : j < N) (hdiv : (N : ℤ) ∣ d * j) :
    ((((List.range n.factorial).map fun k : ℕ ↦ s * (k : K) / n.factorial)).map
      fun μ ↦ s * (N : K)⁻¹ * j - μ).prod = 0 := by
  obtain ⟨k, hkN, hjk⟩ := exists_k n N hN d hd1 hdn j hj0 hjN hdiv
  apply List.prod_eq_zero
  refine List.mem_map.mpr ⟨s * (k : K) / n.factorial, List.mem_map.mpr ⟨k, List.mem_range.mpr hkN,
    rfl⟩, ?_⟩
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hfK : (n.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hjkK : (j : K) * n.factorial = N * k := by exact_mod_cast hjk
  field_simp
  linear_combination s * hjkK

/-- **The exponents are killed** at infinity (`x d/dx = −(1/N) T d/dT`). -/
lemma prod_vanish_inf (n N : ℕ) (hN : 0 < N) (d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n) (j : ℤ)
    (hj0 : 0 ≤ j) (hjN : j < N) (hdiv : (N : ℤ) ∣ d * j) :
    ((((List.range n.factorial).map fun k : ℕ ↦ -((k : K) / n.factorial))).map
      fun μ ↦ 1 * (-(N : K)⁻¹) * j - μ).prod = 0 := by
  obtain ⟨k, hkN, hjk⟩ := exists_k n N hN d hd1 hdn j hj0 hjN hdiv
  apply List.prod_eq_zero
  refine List.mem_map.mpr ⟨-((k : K) / n.factorial), List.mem_map.mpr ⟨k, List.mem_range.mpr hkN,
    rfl⟩, ?_⟩
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hfK : (n.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hjkK : (j : K) * n.factorial = N * k := by exact_mod_cast hjk
  field_simp
  linear_combination -hjkK

namespace CurveData

variable (S : CurveData C L) (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)

/-- **The residue matrix at `x = 0`**: for an integral basis with `S₀ wᵢ′ = ∑ Pᵢⱼ wⱼ` and
`S₀ = x S₁`, `∏_{k<n!} (P(0) − S₁(0) k/n!) = 0`. -/
theorem resid0_ann (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (hw : S.IBasis K w) (S0 S1 : C[X])
    (hS : S0 = X * S1) (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXY hC hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE S0 =
      ∑ j, S.polyE (P i j) * w j) :
    ((List.range S.F.natDegree.factorial).map fun k : ℕ ↦
        S1.eval 0 * (k : C) / S.F.natDegree.factorial).foldr
      (fun μ M ↦ M * (Matrix.of (fun i j ↦ (P i j).eval 0) - μ • 1)) 1 = 0 := by
  classical
  set μs := (List.range S.F.natDegree.factorial).map fun k : ℕ ↦ S1.eval 0 * (k : C) / S.F.natDegree.factorial with hμs
  have hvec : ∀ c : Fin S.F.natDegree → C, Matrix.vecMul c
      (μs.foldr (fun μ M ↦ M * (Matrix.of (fun i j ↦ (P i j).eval 0) - μ • 1)) 1) = 0 := by
    intro c
    set a : Fin S.F.natDegree → C[X] := fun j ↦ Polynomial.C (c j) with ha
    set z := ∑ j, S.polyE (a j) * w j with hz
    set G := S.opZ hC hx S0 μs z with hG
    have hGs : G = ∑ j, S.polyE (opC S0 P μs a j) * w j := S.opZ_sum hC hx S0 P w hP μs a
    have hreg : S.RegularFinite K ((S.polyE X)⁻¹ * G) := by
      intro a' N hN l hl r hr
      have hN0 : 0 < N := Nat.pos_of_ne_zero hN
      rw [map_mul, map_inv₀, S.embG_polyX, bs_X]
      by_cases ha' : a' = 0
      · subst ha'
        rw [map_zero, zero_add, HahnSeries.inv_single, inv_one, hG,
          S.embG_opZ_zero hC hx N hN0 S0 S1 hS r _ μs z]
        refine order_nonneg_of_lowerBd _ ?_
        have hu := lowerBd_of_order_nonneg (S.regularFinite_span (K := K) hw.1 a 0 N hN l hl r hr)
        have : NeZero (N : K) := ⟨by exact_mod_cast hN⟩
        obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K N
        have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
        obtain ⟨d, hd1, hdn, hsupp⟩ := S.branch_support (branchSub N 0) (branchSub_injective N hN0 0)
          hζ hζ0 (fun ξ hξ h ↦ lscale_comp_branchSub hξ N h) hl hr
        have hμK : μs.map (algebraMap C K) = (List.range S.F.natDegree.factorial).map fun k : ℕ ↦
            algebraMap C K (S1.eval 0) * (k : K) / S.F.natDegree.factorial := by
          rw [hμs, List.map_map]
          refine List.map_congr_left fun k _ ↦ ?_
          simp only [Function.comp_apply, map_div₀, map_mul, map_natCast]
        have hL := opL_lowerBd (branchSub N 0 S1) (algebraMap C K (S1.eval 0)) (N : K)⁻¹ N
          (by positivity) (lowerBd_branchSub_sub N S1) (μs.map (algebraMap C K)) _ hu
          (fun j hj0 hjN hne ↦ by
            rw [hμK]
            refine prod_vanish S.F.natDegree N hN0 d hd1 hdn _ j hj0 hjN ?_
            by_contra hnd
            exact hne (hsupp z j hnd))
        have := (lowerBd_single (-(N : ℤ)) (1 : K)).mul hL
        rwa [neg_add_cancel] at this
      · have hGreg : S.RegularFinite K G := by rw [hGs]; exact S.regularFinite_span hw.1 _
        have hB : HahnSeries.C a' + single (N : ℤ) (1 : K) ≠ 0 := by
          intro h0
          have := congrArg (fun u : LaurentSeries K ↦ u.coeff 0) h0
          simp only [HahnSeries.coeff_add, HahnSeries.C_apply, HahnSeries.coeff_single_same,
            HahnSeries.coeff_zero] at this
          rw [HahnSeries.coeff_single_of_ne (by exact_mod_cast hN0.ne), add_zero] at this
          exact ha' this
        have hord : (HahnSeries.C a' + single (N : ℤ) (1 : K)).order = 0 := by
          apply le_antisymm
          · apply HahnSeries.order_le_of_coeff_ne_zero
            simp only [HahnSeries.coeff_add, HahnSeries.C_apply, HahnSeries.coeff_single_same]
            rw [HahnSeries.coeff_single_of_ne (by exact_mod_cast hN0.ne), add_zero]
            exact ha'
          · exact order_nonneg_of_lowerBd _ ((lowerBd_C a').add
              ((lowerBd_single (N : ℤ) (1 : K)).mono (by positivity)))
        have hinv := lowerBd_inv _ hB
        rw [hord, neg_zero] at hinv
        have := hinv.mul (lowerBd_of_order_nonneg (hGreg a' N hN l hl r hr))
        rw [add_zero] at this
        exact order_nonneg_of_lowerBd _ this
    obtain ⟨b, hb⟩ := hw.2.1 _ hreg
    have hX0 : S.polyE X ≠ 0 := S.polyE_ne_zero X X_ne_zero
    have hGb : G = ∑ j, S.polyE (X * b j) * w j := by
      calc G = S.polyE X * ((S.polyE X)⁻¹ * G) := by rw [← mul_assoc, mul_inv_cancel₀ hX0, one_mul]
        _ = ∑ j, S.polyE (X * b j) * w j := by
          rw [hb, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by rw [S.polyE_mul]; ring
    have huniq := hw.2.2 (fun j ↦ opC S0 P μs a j - X * b j) (by
      simp only [S.polyE_sub, sub_mul, Finset.sum_sub_distrib]
      rw [← hGs, ← hGb, sub_self])
    have hev := opC_eval_zero S0 (by rw [hS]; simp) P μs a
    have h0 : (fun j ↦ (opC S0 P μs a j).eval 0) = 0 := funext fun j ↦ by
      rw [sub_eq_zero.mp (huniq j)]; simp
    have hc : (fun j ↦ (a j).eval 0) = c := funext fun j ↦ eval_C
    rw [h0, hc] at hev
    exact hev.symm
  ext i j
  have := congrFun (hvec (Pi.single i 1)) j
  simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using this

end CurveData

end Zero

/-- The numerators `x^{rⱼ+1} Pᵢⱼ − δᵢⱼ rᵢ x^{rᵢ} S₀` of the rescaled matrix. -/
noncomputable def pqF {C : Type*} [Field C] {n : ℕ} (r : Fin n → ℕ) (P : Fin n → Fin n → C[X])
    (S0 : C[X]) (i j : Fin n) : C[X] :=
  X ^ (r j + 1) * P i j - (if i = j then Polynomial.C (r i : C) * X ^ r i * S0 else 0)

/-- The denominators `x^{rᵢ} S₀` of the rescaled matrix. -/
noncomputable def qF {C : Type*} [Field C] {n : ℕ} (r : Fin n → ℕ) (S0 : C[X]) (i : Fin n) : C[X] :=
  X ^ r i * S0

/-- **The residue matrix at infinity** `Λ∞ᵢⱼ = lim x M̃ᵢⱼ`. -/
noncomputable def lamInf {C : Type*} [Field C] {n : ℕ} (r : Fin n → ℕ) (P : Fin n → Fin n → C[X])
    (S0 : C[X]) : Matrix (Fin n) (Fin n) C :=
  Matrix.of fun i j ↦ (pqF r P S0 i j).coeff (qF r S0 i).natDegree / (qF r S0 i).leadingCoeff

section Inf

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L) (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)

/-- `x d/dx` on the function field. -/
noncomputable def dX (z : C⟮S.x⟯⟮S.y⟯) : C⟮S.x⟯⟮S.y⟯ :=
  S.polyE X * ⟨(z : L)′, S.derivClosedXY hC hx z z.2⟩

/-- `∏ (x d/dx − μ)` on the function field. -/
noncomputable def opX : List C → C⟮S.x⟯⟮S.y⟯ → C⟮S.x⟯⟮S.y⟯
  | [], z => z
  | μ :: μs, z => S.dX hC hx (opX μs z) - S.polyE (Polynomial.C μ) * opX μs z

lemma dX_sub (z z' : C⟮S.x⟯⟮S.y⟯) : S.dX hC hx (z - z') = S.dX hC hx z - S.dX hC hx z' := by
  apply Subtype.ext
  simp only [dX, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, map_sub, mul_sub]

lemma dX_const_sum {n : ℕ} (e : Fin n → C) (v : Fin n → C⟮S.x⟯⟮S.y⟯) :
    S.dX hC hx (∑ j, S.polyE (Polynomial.C (e j)) * v j) =
      ∑ j, S.polyE (Polynomial.C (e j)) * S.dX hC hx (v j) := by
  apply Subtype.ext
  simp only [dX, MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum, map_sum, Finset.mul_sum,
    Derivation.leibniz, smul_eq_mul, Differential.deriv_aeval_x S.x hC hx, derivative_C, map_zero,
    mul_zero, add_zero]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **`x d/dx` on the rescaled basis** `w̃ᵢ = x^{−rᵢ} wᵢ`. -/
lemma dX_wt {n : ℕ} (w : Fin n → C⟮S.x⟯⟮S.y⟯) (r : Fin n → ℕ) (S0 : C[X]) (hS00 : S0 ≠ 0)
    (P : Fin n → Fin n → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXY hC hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE S0 =
      ∑ j, S.polyE (P i j) * w j) (i : Fin n) :
    S.dX hC hx ((S.polyE (X ^ r i))⁻¹ * w i) = ∑ j, S.polyE (pqF r P S0 i j) *
        (S.polyE (qF r S0 i))⁻¹ * ((S.polyE (X ^ r j))⁻¹ * w j) := by
  set p : Fin n → C[X] := fun j ↦ X ^ (r j + 1) * P i j -
    (if i = j then Polynomial.C (r i : C) * X ^ r i * S0 else 0) with hp
  show _ = ∑ j, S.polyE (p j) * (S.polyE (X ^ r i * S0))⁻¹ * ((S.polyE (X ^ r j))⁻¹ * w j)
  apply Subtype.ext
  have hx0 : S.x ≠ 0 := S.htr.ne_zero
  have hS0L : aeval S.x S0 ≠ 0 := fun h0 ↦ hS00 (transcendental_iff_injective.mp S.htr
    (by rw [h0, map_zero]))
  have hPi := congrArg (fun t : C⟮S.x⟯⟮S.y⟯ ↦ (t : L)) (hP i)
  simp only [MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum] at hPi
  have hwd : ((w i : L))′ = (∑ j, aeval S.x (P i j) * (w j : L)) / aeval S.x S0 := by
    rw [eq_div_iff hS0L]; exact hPi
  have hpow : ((S.x ^ r i))′ * S.x = (r i : L) * S.x ^ r i := by
    rw [Derivation.leibniz_pow, hx, smul_eq_mul, mul_one, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (r i) with h0 | hpos
    · rw [h0]; simp
    · rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hpos]
  have hcp : ∀ q : C[X], ((S.polyE q : C⟮S.x⟯⟮S.y⟯) : L) = aeval S.x q := fun _ ↦ rfl
  simp only [dX, MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_inv]
  simp only [map_pow, aeval_X]
  rw [Derivation.leibniz, Derivation.leibniz_inv, hwd, smul_eq_mul, smul_eq_mul]
  have hxr : S.x ^ r i ≠ 0 := pow_ne_zero _ hx0
  have hsum : ∀ j, aeval S.x (p j) * (aeval S.x (X ^ r i * S0 : C[X]))⁻¹ *
      ((S.x ^ r j)⁻¹ * (w j : L)) =
      S.x * (S.x ^ r i)⁻¹ * (aeval S.x (P i j) * (w j : L)) / aeval S.x S0 -
        if i = j then (r i : L) * (S.x ^ r i)⁻¹ * (w i : L) else 0 := by
    intro j
    simp only [hp, map_sub, map_mul, map_pow, aeval_X]
    split_ifs with hij
    · subst hij
      simp only [map_mul, map_pow, aeval_X, map_natCast]
      field_simp
      ring
    · simp only [map_zero, sub_zero]
      field_simp
      ring
  rw [Finset.sum_congr rfl fun j _ ↦ hsum j, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ i), ← Finset.sum_div, ← Finset.mul_sum]
  have e2 : S.x * ((w i : L) * (-(S.x ^ r i)⁻¹ ^ 2 • (S.x ^ r i)′)) =
      -((r i : L) * (S.x ^ r i)⁻¹ * (w i : L)) := by
    rw [smul_eq_mul]
    have : (S.x ^ r i)′ = (r i : L) * S.x ^ r i / S.x := by rw [eq_div_iff hx0, hpow]
    rw [this]
    field_simp
  rw [mul_add, e2]
  field_simp
  ring

/-- A polynomial below `q` minus its limit. -/
lemma natDegree_sub_lim (p q : C[X]) (hq : q ≠ 0) (hpq : p.natDegree ≤ q.natDegree) :
    p - Polynomial.C (p.coeff q.natDegree / q.leadingCoeff) * q = 0 ∨
      (p - Polynomial.C (p.coeff q.natDegree / q.leadingCoeff) * q).natDegree < q.natDegree := by
  by_cases h0 : p - Polynomial.C (p.coeff q.natDegree / q.leadingCoeff) * q = 0
  · exact Or.inl h0
  right
  rw [Polynomial.natDegree_lt_iff_degree_lt h0, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  have hm' : q.natDegree ≤ m := by exact_mod_cast hm
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rcases hm'.lt_or_eq with hlt | heq
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hpq.trans_lt hlt),
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero, sub_zero]
  · subst heq
    have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
    rw [← Polynomial.leadingCoeff]
    field_simp
    ring

/-- A fraction vanishing at infinity. -/
lemma infOrd_frac_lt (p q : C[X]) (hq : q ≠ 0) (h : p = 0 ∨ p.natDegree < q.natDegree) :
    S.InfOrd K (S.polyE p * (S.polyE q)⁻¹) (-1) := by
  rcases h with h | h
  · subst h
    have : S.polyE (0 : C[X]) = 0 := S.polyE_zero'
    rw [this, zero_mul]; exact S.infOrd_zero (-1)
  · exact InfOrd.mono S (S.infOrd_frac (K := K) p q hq) (by omega)

lemma polyE_C_sum {n : ℕ} (e : Fin n → C) (Λ : Fin n → C) :
    S.polyE (Polynomial.C (∑ j, e j * Λ j)) =
      ∑ j, S.polyE (Polynomial.C (e j)) * S.polyE (Polynomial.C (Λ j)) := by
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, aeval_C, map_sum, map_mul]

lemma infOrd_polyE_C (c : C) : S.InfOrd K (S.polyE (Polynomial.C c)) 0 := by
  have := S.infOrd_poly (K := K) (Polynomial.C c)
  rwa [natDegree_C, Nat.cast_zero] at this

/-- A fraction minus its limit vanishes at infinity. -/
lemma frac_sub_lim (p q : C[X]) (hq : q ≠ 0) (hpq : p.natDegree ≤ q.natDegree) :
    S.InfOrd K (S.polyE p * (S.polyE q)⁻¹ -
      S.polyE (Polynomial.C (p.coeff q.natDegree / q.leadingCoeff))) (-1) := by
  have hQ := S.polyE_ne_zero q hq
  have e : S.polyE p * (S.polyE q)⁻¹ - S.polyE (Polynomial.C (p.coeff q.natDegree / q.leadingCoeff)) =
      S.polyE (p - Polynomial.C (p.coeff q.natDegree / q.leadingCoeff) * q) * (S.polyE q)⁻¹ := by
    rw [S.polyE_sub, S.polyE_mul]; field_simp
  rw [e]
  exact S.infOrd_frac_lt _ _ hq (natDegree_sub_lim p q hq hpq)

/-- **`x d/dx ≡ Λ∞` modulo `x^{−1}`** on constant combinations of the rescaled basis. -/
lemma dX_near {n : ℕ} (w : Fin n → C⟮S.x⟯⟮S.y⟯) (r : Fin n → ℕ)
    (hr : ∀ j, S.InfOrd K (w j) (r j)) (S0 : C[X]) (hS00 : S0 ≠ 0)
    (P : Fin n → Fin n → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXY hC hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE S0 =
      ∑ j, S.polyE (P i j) * w j)
    (hdeg : ∀ i j, (pqF r P S0 i j).natDegree ≤ r i + S0.natDegree) (e : Fin n → C) :
    S.InfOrd K (S.dX hC hx (∑ j, S.polyE (Polynomial.C (e j)) * ((S.polyE (X ^ r j))⁻¹ * w j)) -
      ∑ k, S.polyE (Polynomial.C (Matrix.vecMul e (lamInf r P S0) k)) *
        ((S.polyE (X ^ r k))⁻¹ * w k)) (-1) := by
  have hq0 : ∀ i, qF r S0 i ≠ 0 := fun i ↦ mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
  have hqdeg : ∀ i, (qF r S0 i).natDegree = r i + S0.natDegree := fun i ↦ by
    rw [qF, natDegree_mul (pow_ne_zero _ X_ne_zero) hS00, natDegree_X_pow]
  have hwt0 : ∀ j, S.InfOrd K ((S.polyE (X ^ r j))⁻¹ * w j) 0 := fun j ↦ by
    have := InfOrd.mul S (S.infOrd_inv_poly (K := K) (X ^ r j) (pow_ne_zero _ X_ne_zero)) (hr j)
    rw [natDegree_X_pow] at this
    exact InfOrd.mono S this (by omega)
  have e1 : S.dX hC hx (∑ j, S.polyE (Polynomial.C (e j)) * ((S.polyE (X ^ r j))⁻¹ * w j)) -
      ∑ k, S.polyE (Polynomial.C (Matrix.vecMul e (lamInf r P S0) k)) *
        ((S.polyE (X ^ r k))⁻¹ * w k) =
      ∑ j, ∑ k, S.polyE (Polynomial.C (e j)) * ((S.polyE (pqF r P S0 j k) *
        (S.polyE (qF r S0 j))⁻¹ - S.polyE (Polynomial.C (lamInf r P S0 j k))) *
          ((S.polyE (X ^ r k))⁻¹ * w k)) := by
    rw [S.dX_const_sum hC hx]
    simp only [S.dX_wt hC hx w r S0 hS00 P hP]
    simp only [Matrix.vecMul, dotProduct, S.polyE_C_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun k j ↦ S.polyE (Polynomial.C (e j)) *
      S.polyE (Polynomial.C (lamInf r P S0 j k)) * ((S.polyE (X ^ r k))⁻¹ * w k)),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [e1]
  refine InfOrd.sum S _ _ fun j _ ↦ InfOrd.sum S _ _ fun k _ ↦ ?_
  have h1 := S.frac_sub_lim (K := K) (pqF r P S0 j k) (qF r S0 j) (hq0 j) (by rw [hqdeg]; exact hdeg j k)
  have := InfOrd.mul S (S.infOrd_polyE_C (K := K) (e j)) (InfOrd.mul S h1 (hwt0 k))
  simpa [lamInf] using this

/-- **Iterates modulo `x^{−1}`**: `∏ (x d/dx − μ) ∑ cⱼ w̃ⱼ ≡ ∑ (c ∏ (Λ∞ − μ))ₖ w̃ₖ`. -/
lemma opX_near {n : ℕ} (w : Fin n → C⟮S.x⟯⟮S.y⟯) (r : Fin n → ℕ)
    (hr : ∀ j, S.InfOrd K (w j) (r j)) (S0 : C[X]) (hS00 : S0 ≠ 0)
    (P : Fin n → Fin n → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXY hC hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE S0 =
      ∑ j, S.polyE (P i j) * w j)
    (hdeg : ∀ i j, (pqF r P S0 i j).natDegree ≤ r i + S0.natDegree) (μs : List C) (c : Fin n → C) :
    S.InfOrd K (S.opX hC hx μs (∑ j, S.polyE (Polynomial.C (c j)) * ((S.polyE (X ^ r j))⁻¹ * w j)) -
      ∑ k, S.polyE (Polynomial.C (Matrix.vecMul c
        (μs.foldr (fun μ M ↦ M * (lamInf r P S0 - μ • 1)) 1) k)) *
        ((S.polyE (X ^ r k))⁻¹ * w k)) (-1) := by
  induction μs with
  | nil =>
    simp only [opX, List.foldr_nil, Matrix.vecMul_one, sub_self]
    exact S.infOrd_zero (-1)
  | cons μ μs ih =>
    set g := S.opX hC hx μs (∑ j, S.polyE (Polynomial.C (c j)) * ((S.polyE (X ^ r j))⁻¹ * w j))
    set e := Matrix.vecMul c (μs.foldr (fun μ M ↦ M * (lamInf r P S0 - μ • 1)) 1) with he
    set E := ∑ k, S.polyE (Polynomial.C (e k)) * ((S.polyE (X ^ r k))⁻¹ * w k) with hE
    have hvec : Matrix.vecMul c ((μ :: μs).foldr (fun μ M ↦ M * (lamInf r P S0 - μ • 1)) 1) =
        fun k ↦ Matrix.vecMul e (lamInf r P S0) k - μ * e k := by
      rw [List.foldr_cons, ← Matrix.vecMul_vecMul, ← he, Matrix.vecMul_sub]
      funext k
      simp [Matrix.vecMul_smul, Matrix.vecMul_one]
    have hsum : ∑ k, S.polyE (Polynomial.C (Matrix.vecMul e (lamInf r P S0) k - μ * e k)) *
        ((S.polyE (X ^ r k))⁻¹ * w k) =
        ∑ k, S.polyE (Polynomial.C (Matrix.vecMul e (lamInf r P S0) k)) *
          ((S.polyE (X ^ r k))⁻¹ * w k) - S.polyE (Polynomial.C μ) * E := by
      rw [hE, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Polynomial.C_sub, S.polyE_sub, Polynomial.C_mul, S.polyE_mul]
      ring
    have e2 : S.opX hC hx (μ :: μs) (∑ j, S.polyE (Polynomial.C (c j)) *
        ((S.polyE (X ^ r j))⁻¹ * w j)) - ∑ k, S.polyE (Polynomial.C (Matrix.vecMul c
          ((μ :: μs).foldr (fun μ M ↦ M * (lamInf r P S0 - μ • 1)) 1) k)) *
          ((S.polyE (X ^ r k))⁻¹ * w k) =
        S.dX hC hx (g - E) - S.polyE (Polynomial.C μ) * (g - E) +
          (S.dX hC hx E - ∑ k, S.polyE (Polynomial.C (Matrix.vecMul e (lamInf r P S0) k)) *
            ((S.polyE (X ^ r k))⁻¹ * w k)) := by
      rw [hvec, hsum, S.dX_sub hC hx]
      simp only [opX]
      ring
    rw [e2]
    have h1 : S.InfOrd K (S.dX hC hx (g - E)) (-1) := S.infOrd_x_deriv hC hx _ (-1) ih
    have h2 := InfOrd.mul S (S.infOrd_polyE_C (K := K) μ) ih
    rw [zero_add] at h2
    exact InfOrd.add S (InfOrd.sub S h1 h2) (S.dX_near hC hx w r hr S0 hS00 P hP hdeg e)

lemma embG_dX_inf (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hY : (S.F.map (infSub N)).eval r = 0) (v : C⟮S.x⟯⟮S.y⟯) :
    S.embG (infSub N) (infSub_injective N hN) r hY (S.dX hC hx v) =
      HahnSeries.C 1 * thetaS (-(N : K)⁻¹) (S.embG (infSub N) (infSub_injective N hN) r hY v) := by
  have hd := S.embG_derivG (single (-(N : ℤ)) (1 : K)) (derivation_infX_ne N hN)
    (infSub N) (infSub_injective N hN) (fun P ↦ by rw [SuperData.infSub_eq_subst]) hC hx r hY
    (v : L) v.2
  simp only [Subtype.coe_eta] at hd
  rw [dX, map_mul, S.embG_polyX, hd, HahnSeries.C_one, one_mul]
  show infSub N X * ((LaurentSeries.derivation (single (-(N : ℤ)) (1 : K)))⁻¹ *
    LaurentSeries.derivation _) = _
  rw [SuperData.derivation_infX N, LaurentSeries.derivation_apply, is_X, thetaS,
    HahnSeries.inv_single, ← mul_assoc, HahnSeries.single_mul_single, one_mul,
    show -(N : ℤ) + -(-(N : ℤ) - 1) = 1 by ring, inv_neg]

lemma embG_opX_inf (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hY : (S.F.map (infSub N)).eval r = 0) (μs : List C) (v : C⟮S.x⟯⟮S.y⟯) :
    S.embG (infSub N) (infSub_injective N hN) r hY (S.opX hC hx μs v) =
      opL (fun u ↦ HahnSeries.C 1 * thetaS (-(N : K)⁻¹) u) (μs.map (algebraMap C K))
        (S.embG (infSub N) (infSub_injective N hN) r hY v) := by
  induction μs with
  | nil => rfl
  | cons μ μs ih =>
    rw [opX, map_sub, S.embG_dX_inf hC hx N hN r hY, map_mul, S.embG_polyX, ih, is_C,
      List.map_cons, opL]

/-- **Far from the residues**: `∏_{k<n!} (x d/dx + k/n!)` maps elements without pole above
infinity to elements vanishing there. -/
lemma opX_far (f : C⟮S.x⟯⟮S.y⟯) (hf : S.InfOrd K f 0) :
    S.InfOrd K (S.opX hC hx ((List.range S.F.natDegree.factorial).map fun k : ℕ ↦
      -((k : C) / S.F.natDegree.factorial)) f) (-1) := by
  intro N hN l hl r hr
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  rw [S.embG_opX_inf hC hx N hN0 r _ ((List.range S.F.natDegree.factorial).map fun k : ℕ ↦
      -((k : C) / S.F.natDegree.factorial)) f]
  have hu := hf N hN l hl r hr
  rw [zero_mul, neg_zero] at hu
  have : NeZero (N : K) := ⟨by exact_mod_cast hN⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  obtain ⟨d, hd1, hdn, hsupp⟩ := S.branch_support (infSub N) (infSub_injective N hN0)
    hζ hζ0 (fun ξ hξ h ↦ lscale_comp_infSub hξ N h) hl hr
  have hμK : ((List.range S.F.natDegree.factorial).map fun k : ℕ ↦
      -((k : C) / S.F.natDegree.factorial)).map (algebraMap C K) =
      (List.range S.F.natDegree.factorial).map fun k : ℕ ↦
        -((k : K) / S.F.natDegree.factorial) := by
    rw [List.map_map]
    refine List.map_congr_left fun k _ ↦ ?_
    simp only [Function.comp_apply, map_neg, map_div₀, map_natCast]
  have hL := opL_lowerBd (HahnSeries.C 1) 1 (-(N : K)⁻¹) N (by positivity)
    (by rw [sub_self]; exact lowerBd_zero _) (((List.range S.F.natDegree.factorial).map
      fun k : ℕ ↦ -((k : C) / S.F.natDegree.factorial)).map (algebraMap C K)) _ hu
    (fun j hj0 hjN hne ↦ by
      rw [hμK]
      refine prod_vanish_inf S.F.natDegree N hN0 d hd1 hdn j hj0 hjN ?_
      by_contra hnd
      exact hne (hsupp f j hnd))
  refine hL.mono (le_of_eq ?_)
  ring

/-- **The residue matrix at infinity** of a reduced basis: `∏_{k<n!} (Λ∞ + k/n!) = 0`. -/
theorem resInf_ann (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ)
    (hr : ∀ j, S.InfOrd K (w j) (r j)) (hred : S.Reduced K w r) (S0 : C[X]) (hS00 : S0 ≠ 0)
    (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXY hC hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE S0 =
      ∑ j, S.polyE (P i j) * w j)
    (hdeg : ∀ i j, (pqF r P S0 i j).natDegree ≤ r i + S0.natDegree) :
    ((List.range S.F.natDegree.factorial).map fun k : ℕ ↦
        -((k : C) / S.F.natDegree.factorial)).foldr
      (fun μ M ↦ M * (lamInf r P S0 - μ • 1)) 1 = 0 := by
  classical
  have hvec : ∀ c : Fin S.F.natDegree → C, Matrix.vecMul c (((List.range S.F.natDegree.factorial).map
      fun k : ℕ ↦ -((k : C) / S.F.natDegree.factorial)).foldr
        (fun μ M ↦ M * (lamInf r P S0 - μ • 1)) 1) = 0 := by
    intro c
    set f := ∑ j, S.polyE (Polynomial.C (c j)) * ((S.polyE (X ^ r j))⁻¹ * w j) with hf
    have hf0 : S.InfOrd K f 0 := by
      refine InfOrd.sum S _ _ fun j _ ↦ ?_
      have := InfOrd.mul S (S.infOrd_inv_poly (K := K) (X ^ r j) (pow_ne_zero _ X_ne_zero)) (hr j)
      rw [natDegree_X_pow] at this
      have h3 : S.InfOrd K ((S.polyE (X ^ r j))⁻¹ * w j) 0 := InfOrd.mono S this (by omega)
      have h2 := InfOrd.mul S (S.infOrd_polyE_C (K := K) (c j)) h3
      simpa using h2
    have h1 := S.opX_near hC hx w r hr S0 hS00 P hP hdeg ((List.range S.F.natDegree.factorial).map
      fun k : ℕ ↦ -((k : C) / S.F.natDegree.factorial)) c
    have h2 := S.opX_far hC hx f hf0
    have h3 := InfOrd.sub S h2 h1
    rw [sub_sub_cancel] at h3
    funext k
    exact hred _ h3 k
  ext i j
  have := congrFun (hvec (Pi.single i 1)) j
  simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using this

end CurveData

end Inf

end Curves
