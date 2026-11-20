import RischTragerBronstein.Mixed.NKExpCurve
import RischTragerBronstein.Mixed.NKExp0Lead
import RischTragerBronstein.Mixed.NKLogDecide

/-!
# The gauge at `x = 0` for a single place above `0` (exponential level)

`S : CurveData C L` with `x′ = b x` and a single, totally ramified place above `x = 0`
(`ord₀ a₀ = d`, `gcd(n, d) = 1`, `n ord₀ aᵢ > d (n − i)`). For an integral basis `w` with
derivation matrix `M = P/S₀` regular at `0` (`S₀(0) ≠ 0`), the elements `ēⱼ = yʲ / x^{⌊jd/n⌋}`
(`j < n`) are integral, of orders `(jd mod n)/n` above `0`. Their coordinates at `x = 0` form an
invertible matrix `U`, and the derivation of the residue algebra `O₀/x` in the basis `ē` is
`Λ = (U′ + U M(0)) U⁻¹`, triangular for the orders with diagonal
`((jd mod n)/n) b + j c′/(n c)`, `c = tc(a₀)` (`exists_gauge0`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Speed0

variable {C K : Type*} [Field C] [CharZero C] [Field K] [CharZero K] [Algebra C K] [Differential C]
  [Differential K]

/-- **Along a branch above `0`** (exponential level): `(z′)ₖ = zₖ′ + (k a′/N) zₖ`. -/
lemma coeff_dS_zeroSpeedE (b : C) (N : ℕ) (E : LaurentSeries K) (k : ℤ) :
    (dS (zeroSpeedE (K := K) b N) E).coeff k =
      (E.coeff k)′ + algebraMap C K b * (k / N) * E.coeff k := by
  rw [dS_apply, HahnSeries.coeff_add, coeff_coefDeriv, zeroSpeedE]
  have e := HahnSeries.coeff_single_mul_add (r := (algebraMap C K b) / N) (b := (1 : ℤ))
    (a := k - 1) (x := derivative K E)
  rw [sub_add_cancel] at e
  rw [e, derivative_coeff, sub_add_cancel]
  push_cast
  ring

end Speed0

section Sub0

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

lemma branchSub_zero_X' (N : ℕ) : branchSub (C := C) (K := K) N 0 X = single (N : ℤ) 1 := by
  rw [branchSub_apply, Polynomial.map_X, X_comp, map_zero, zero_add, Polynomial.coe_pow,
    Polynomial.coe_X, ← ofPowerSeries_X_pow]

lemma branchSub_C'' (N : ℕ) (e : K) (c : C) :
    branchSub (C := C) (K := K) N e (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := by
  rw [branchSub_apply, Polynomial.map_C, C_comp, Polynomial.coe_C, ofPowerSeries_C]

lemma lowerBd_bsub (N : ℕ) (hN : 0 < N) (e : K) (P : C[X]) : LowerBd (branchSub N e P) 0 := by
  by_cases hP : P = 0
  · rw [hP, map_zero]; exact lowerBd_zero 0
  · refine lowerBd_of_order_nk ?_
    rw [order_branchSub N hN e P hP]; positivity

/-- Polynomials vanishing at `0` have order `≥ N` along `x = Tᴺ`. -/
lemma lowerBd_branchSub_zero (N : ℕ) (hN : 0 < N) (P : C[X]) (hP : P.coeff 0 = 0) :
    LowerBd (branchSub (K := K) N 0 P) N := by
  obtain ⟨Q, rfl⟩ := Polynomial.X_dvd_iff.mpr hP
  rw [map_mul, branchSub_zero_X']
  have := (lowerBd_single (N : ℤ) (1 : K)).mul (lowerBd_bsub N hN 0 Q)
  simpa using this

lemma lowerBd_pow0 {z : LaurentSeries K} (hz : LowerBd z 0) (j : ℕ) : LowerBd (z ^ j) 0 := by
  induction j with
  | zero => rw [pow_zero, ← HahnSeries.single_zero_one]; exact lowerBd_single 0 1
  | succ k ih => rw [pow_succ]; simpa using ih.mul hz

/-- Inverting a series of order `0`. -/
lemma lowerBd_inv_of_order_zero {z : LaurentSeries K} (hz : z ≠ 0) (ho : z.order = 0) :
    LowerBd z⁻¹ 0 := by
  refine lowerBd_of_order_nk ?_
  have h1 : (z * z⁻¹).order = 0 := by rw [mul_inv_cancel₀ hz, HahnSeries.order_one]
  rw [HahnSeries.order_mul hz (inv_ne_zero hz), ho, zero_add] at h1
  rw [h1]

end Sub0

namespace CurveData

section Gauge0

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

/-- The elements `yʲ / x^{⌊jd/n⌋}`. -/
noncomputable def eZ (n d j : ℕ) : C⟮S.x⟯⟮S.y⟯ :=
  (S.polyE (X ^ (j * d / n)))⁻¹ * (AdjoinSimple.gen C⟮S.x⟯ S.y) ^ j

lemma embG_eZ (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (r : LaurentSeries K)
    (hr : (S.F.map g).eval r = 0) (n d j : ℕ) :
    S.embG g hg r hr (S.eZ n d j) = (g (X ^ (j * d / n)))⁻¹ * r ^ j := by
  rw [eZ, map_mul, map_inv₀, map_pow, S.embG_gen]
  congr 2
  exact S.embG_polyX g hg r hr _ _

/-- **`yʲ / x^{⌊jd/n⌋}` is integral** (a single place above `0`). -/
lemma regularFinite_eZ (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natTrailingDegree = d)
    (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ d * (n - i) < n * (S.F.coeff i).natTrailingDegree)
    (j : ℕ) : S.RegularFinite K (S.eZ n d j) := by
  intro α N hN l hl r hr
  have hN0 := Nat.pos_of_ne_zero hN
  have hroot := S.root_of_mem hl hr
  rw [S.embG_eZ]
  by_cases hα : α = 0
  · subst hα
    obtain ⟨hr0, hro⟩ := root_order_zero S.F S.monic n d N hn hn0 hN0 ha0 hd hw r hroot
    rw [map_pow, branchSub_zero_X', single_pow, inv_single, one_pow, inv_one,
      HahnSeries.order_mul (single_ne_zero one_ne_zero) (pow_ne_zero _ hr0), order_single one_ne_zero,
      HahnSeries.order_pow, nsmul_eq_mul]
    have hdiv := Nat.div_mul_le_self (j * d) n
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
    have h1 : ((j * d / n : ℕ) : ℤ) * n ≤ (j : ℤ) * d := by exact_mod_cast hdiv
    have h2 : (n : ℤ) * (-((j * d / n : ℕ) • (N : ℤ)) + j * r.order) =
        (N : ℤ) * ((j : ℤ) * d - ((j * d / n : ℕ) : ℤ) * n) := by
      rw [nsmul_eq_mul]; push_cast; linear_combination (j : ℤ) * hro
    have h3 : 0 ≤ (n : ℤ) * (-((j * d / n : ℕ) • (N : ℤ)) + j * r.order) := by
      rw [h2]; exact mul_nonneg (by positivity) (by linarith)
    by_contra hneg
    push Not at hneg
    simp only [nsmul_eq_mul] at hneg h3
    nlinarith
  · have hX : (branchSub (K := K) N α ((X : C[X]) ^ (j * d / n))).order = 0 := by
      rw [order_branchSub N hN0 α _ (pow_ne_zero _ (X_ne_zero (R := C)))]
      rw [rootMultiplicity_eq_zero (by simp [hα]), mul_zero, Nat.cast_zero]
    have hX0 : branchSub (K := K) N α ((X : C[X]) ^ (j * d / n)) ≠ 0 :=
      (map_ne_zero_iff _ (branchSub_injective N hN0 α)).mpr (pow_ne_zero _ X_ne_zero)
    have hY : LowerBd r 0 := lowerBd_root _ (S.monic.map _)
      (fun i ↦ by rw [coeff_map]; exact lowerBd_bsub N hN0 α _) r hroot
    refine order_nonneg_of_lowerBd_nk _ ?_
    have := (lowerBd_inv_of_order_zero hX0 hX).mul (lowerBd_pow0 hY j)
    simpa using this

variable (b : C) (hx : S.x′ = aeval S.x (Polynomial.C b * X))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **The gauge at `x = 0`**: for an integral basis `w` with derivation matrix `P/S₀`, `S₀(0) ≠ 0`,
the coordinates `U` at `0` of `ēᵢ = yⁱ/x^{⌊id/n⌋}` are invertible and
`Λ = (U′ + U M(0)) U⁻¹` is triangular for the orders `id mod n` with diagonal
`((id mod n)/n) b + i c′/(n c)`, `c = tc(a₀)`. -/
theorem exists_gauge0 (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natTrailingDegree = d)
    (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ d * (n - i) < n * (S.F.coeff i).natTrailingDegree)
    (hcop : Nat.Coprime n d)
    (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (hwB : S.IBasis K w) (S0 : C[X]) (hS0 : S0.coeff 0 ≠ 0)
    (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
        S.polyE S0 = ∑ j, S.polyE (P i j) * w j) :
    ∃ (U Ui Lam : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C),
      U * Ui = 1 ∧ Ui * U = 1 ∧
      Lam = (U.map (fun z ↦ z′) + U * Matrix.of (fun i j ↦ (P i j).coeff 0 / S0.coeff 0)) * Ui ∧
      (∀ i j, Lam i j ≠ 0 → (i : ℕ) * d % n ≤ (j : ℕ) * d % n) ∧
      (∀ i, Lam i i = (((i : ℕ) * d % n : ℕ) : C) / n * b +
        ((i : ℕ) : C) * ((S.F.coeff 0).trailingCoeff′ / (n * (S.F.coeff 0).trailingCoeff))) := by
  classical
  -- a branch above `0`
  obtain ⟨N, hN, l0, hlen, hl0⟩ := S.hasBranches (K := K) 0
  have hN0 := Nat.pos_of_ne_zero hN
  set l := l0.map (ofPowerSeries ℤ K) with hldef
  have hl : S.F.map (branchSub N (0 : K)) = (l.map fun r ↦ X - Polynomial.C r).prod := by
    rw [hl0, hldef, List.map_map]; rfl
  have hlne : l ≠ [] := by
    intro h
    rw [hldef, List.map_eq_nil_iff] at h
    rw [h, List.length_nil, hn] at hlen; omega
  obtain ⟨ρ, hρl⟩ := List.exists_mem_of_ne_nil l hlne
  have hρ := S.root_of_mem hl hρl
  obtain ⟨hρ0, hρo⟩ := root_order_zero S.F S.monic n d N hn hn0 hN0 ha0 hd hw ρ hρ
  have hγ := root_lead_zero (K := K) S.F S.monic n d N hn hn0 hN0 ha0 hd hw ρ hρ
  set φ := S.embG (branchSub N 0) (branchSub_injective N hN0 0) ρ hρ with hφ
  set e : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯ := fun i ↦ S.eZ n d i with he
  set E : Fin S.F.natDegree → LaurentSeries K := fun i ↦ φ (e i) with hE
  have hEf : ∀ i, E i = single (-((((i : ℕ) * d / n : ℕ) : ℤ) * N)) 1 * ρ ^ (i : ℕ) := fun i ↦ by
    simp only [hE, he, hφ]
    rw [S.embG_eZ, map_pow, branchSub_zero_X', single_pow, one_pow, inv_single, inv_one,
      nsmul_eq_mul]
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN0
  -- orders and leading coefficients
  have hE0 : ∀ i, E i ≠ 0 := fun i ↦ by
    rw [hEf]; exact mul_ne_zero (single_ne_zero one_ne_zero) (pow_ne_zero _ hρ0)
  set o : Fin S.F.natDegree → ℤ := fun i ↦ (E i).order with ho
  have hno : ∀ i, (n : ℤ) * o i = N * (((i : ℕ) * d % n : ℕ) : ℤ) := fun i ↦ by
    simp only [ho]
    rw [hEf, HahnSeries.order_mul (single_ne_zero one_ne_zero) (pow_ne_zero _ hρ0),
      order_single one_ne_zero, HahnSeries.order_pow, nsmul_eq_mul]
    have h' : ((n * ((i : ℕ) * d / n) + (i : ℕ) * d % n : ℕ) : ℤ) = (((i : ℕ) * d : ℕ) : ℤ) := by
      rw [Nat.div_add_mod]
    push_cast at h' ⊢
    linear_combination ((i : ℕ) : ℤ) * hρo - (N : ℤ) * h'
  have hrem : ∀ i : Fin S.F.natDegree, (((i : ℕ) * d % n : ℕ) : ℤ) < n := fun i ↦ by
    exact_mod_cast Nat.mod_lt _ hn0
  have ho0 : ∀ i, 0 ≤ o i := fun i ↦ by
    have := hno i
    have h2 : (0 : ℤ) ≤ (N : ℤ) * (((i : ℕ) * d % n : ℕ) : ℤ) := by positivity
    nlinarith
  have hoN : ∀ i, o i < N := fun i ↦ by
    have := hno i; have := hrem i; nlinarith
  have hreminj : ∀ i j : Fin S.F.natDegree, (i : ℕ) * d % n = (j : ℕ) * d % n → i = j := by
    intro i j hij
    have h := Nat.ModEq.cancel_right_of_coprime hcop (hij : (i : ℕ) * d ≡ (j : ℕ) * d [MOD n])
    have hi : (i : ℕ) < n := hn ▸ i.2
    have hj : (j : ℕ) < n := hn ▸ j.2
    unfold Nat.ModEq at h
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
    exact Fin.ext h
  have hoinj : ∀ i j, o i = o j → i = j := fun i j hij ↦ by
    refine hreminj i j ?_
    have h1 := hno i; have h2 := hno j
    rw [hij] at h1
    have : (N : ℤ) * (((i : ℕ) * d % n : ℕ) : ℤ) = N * (((j : ℕ) * d % n : ℕ) : ℤ) := by linarith
    exact_mod_cast mul_left_cancel₀ hNpos.ne' this
  have hlc : ∀ i, (E i).coeff (o i) = ρ.leadingCoeff ^ (i : ℕ) := fun i ↦ by
    simp only [ho]
    rw [← HahnSeries.leadingCoeff_eq, hEf, HahnSeries.leadingCoeff_mul, leadingCoeff_of_single,
      leadingCoeff_pow_hahn, one_mul]
  have hγ0 : ρ.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hρ0
  have hbelow : ∀ i k, k < o i → (E i).coeff k = 0 := fun i k hk ↦
    HahnSeries.coeff_eq_zero_of_lt_order hk
  -- the coordinates
  have hreg : ∀ i, S.RegularFinite K (e i) := fun i ↦ S.regularFinite_eZ n d hn hn0 ha0 hd hw i
  choose p hp using fun i ↦ hwB.2.1 (e i) (hreg i)
  have hpL : ∀ i, (e i : L) = ∑ k, aeval S.x (p i k) * (w k : L) := fun i ↦ by
    have := congrArg Subtype.val (hp i)
    simpa [CurveData.polyE] using this
  have hPL : ∀ k, (w k : L)′ * aeval S.x S0 = ∑ j, aeval S.x (P k j) * (w j : L) := fun k ↦ by
    have := congrArg Subtype.val (hP k)
    simpa [CurveData.polyE] using this
  set U : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C := Matrix.of fun i k ↦ (p i k).coeff 0
    with hU
  have hwreg : ∀ k, LowerBd (φ (w k)) 0 := fun k ↦
    lowerBd_of_order_nk (hwB.1 k 0 N hN l hl ρ hρl)
  have hcomb : ∀ c : Fin S.F.natDegree → C[X], (∀ k, (c k).coeff 0 = 0) →
      LowerBd (φ (∑ k, S.polyE (c k) * w k)) N := fun c hc ↦ by
    rw [map_sum]
    refine lowerBd_sum _ _ fun k _ ↦ ?_
    rw [map_mul, show φ (S.polyE (c k)) = branchSub N 0 (c k) from S.embG_polyX _ _ _ _ _ _]
    simpa using (lowerBd_branchSub_zero N hN0 (c k) (hc k)).mul (hwreg k)
  have hφC : ∀ c : C, φ (S.polyE (Polynomial.C c)) = HahnSeries.C (algebraMap C K c) := fun c ↦ by
    rw [show φ (S.polyE (Polynomial.C c)) = branchSub N 0 (Polynomial.C c) from
      S.embG_polyX _ _ _ _ _ _, branchSub_C'']
  -- `U` is invertible
  have hUind : ∀ v : Fin S.F.natDegree → C, Matrix.vecMul v U = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
      by_contra h; push Not at h; exact hv0 (funext h)
    set J := Finset.univ.filter fun i ↦ v i ≠ 0 with hJ
    obtain ⟨i1, hi1J, hi1min⟩ := J.exists_min_image o ⟨i0, by simp [hJ, hi0]⟩
    have hi1 : v i1 ≠ 0 := (Finset.mem_filter.mp hi1J).2
    have hz := hcomb (fun k ↦ ∑ i, Polynomial.C (v i) * p i k) fun k ↦ by
      rw [finset_sum_coeff]
      have := congrFun hv k
      simp only [Matrix.vecMul, dotProduct, hU, Matrix.of_apply, Pi.zero_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [Polynomial.coeff_C_mul]
    have heq : (∑ k, S.polyE (∑ i, Polynomial.C (v i) * p i k) * w k) =
        ∑ i, S.polyE (Polynomial.C (v i)) * e i := by
      apply Subtype.ext
      simp only [CurveData.polyE, IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum,
        map_mul, hpL, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [heq, map_sum] at hz
    have hc := hz (o i1) (hoN i1)
    rw [HahnSeries.coeff_sum, Finset.sum_eq_single i1] at hc
    · rw [map_mul, hφC, LaurentSeries.coeff_C_mul] at hc
      exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap C K).injective).mpr hi1)
        (by rw [show φ (e i1) = E i1 from rfl, hlc]; exact pow_ne_zero _ hγ0) hc
    · intro i _ hii1
      rw [map_mul, hφC, LaurentSeries.coeff_C_mul]
      by_cases hvi : v i = 0
      · rw [hvi, map_zero, zero_mul]
      · have h3 : o i1 ≤ o i := hi1min i (by simp [hJ, hvi])
        have h4 : o i1 < o i := lt_of_le_of_ne h3 fun h5 ↦ hii1 (hoinj _ _ h5).symm
        rw [show φ (e i) = E i from rfl, hbelow i _ h4, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i1) h
  have hdet : U.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    exact hv0 (hUind v hv)
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet
  set M0 : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C :=
    Matrix.of (fun i j ↦ (P i j).coeff 0 / S0.coeff 0) with hM0
  set Lam := (U.map (fun z ↦ z′) + U * M0) * U⁻¹ with hLam
  have hLU : Lam * U = U.map (fun z ↦ z′) + U * M0 := by
    rw [hLam, Matrix.mul_assoc, Matrix.nonsing_inv_mul U hUu, Matrix.mul_one]
  -- the residual polynomials
  set D : Fin S.F.natDegree → Fin S.F.natDegree → C[X] := fun i k ↦
    S0 * (mapCoeffs (p i k) + Polynomial.C b * X * derivative (p i k)) + ∑ l, p i l * P l k -
      ∑ l, Polynomial.C (Lam i l) * S0 * p l k with hD
  have hD0 : ∀ i k, (D i k).coeff 0 = 0 := by
    intro i k
    have h := congrFun (congrFun hLU i) k
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, hU, hM0, Matrix.of_apply] at h
    simp only [hD, Polynomial.coeff_sub, Polynomial.coeff_add, mul_coeff_zero, finsetSum_coeff,
      coeff_mapCoeffs,
      coeff_C_zero, coeff_X_zero, mul_zero, zero_mul, add_zero]
    have e1 : ∑ l, Lam i l * S0.coeff 0 * (p l k).coeff 0 =
        S0.coeff 0 * ∑ l, Lam i l * (p l k).coeff 0 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ ↦ by ring
    rw [e1, h, mul_add, Finset.mul_sum]
    have e2 : ∀ l, S0.coeff 0 * ((p i l).coeff 0 * ((P l k).coeff 0 / S0.coeff 0)) =
        (p i l).coeff 0 * (P l k).coeff 0 := fun l ↦ by field_simp
    simp only [e2]
    ring
  have hDL : ∀ i, ((e i : L)′ - ∑ l, algebraMap C L (Lam i l) * (e l : L)) * aeval S.x S0 =
      ∑ k, aeval S.x (D i k) * (w k : L) := by
    intro i
    have h1 : (e i : L)′ * aeval S.x S0 = ∑ k, aeval S.x (S0 * (mapCoeffs (p i k) +
        Polynomial.C b * X * derivative (p i k))) * (w k : L) +
        ∑ k, aeval S.x (∑ l, p i l * P l k) * (w k : L) := by
      rw [hpL i, map_sum, Finset.sum_mul]
      have e1 : ∀ k, (aeval S.x (p i k) * (w k : L))′ * aeval S.x S0 =
          aeval S.x (S0 * (mapCoeffs (p i k) + Polynomial.C b * X * derivative (p i k))) * (w k : L) +
          aeval S.x (p i k) * ∑ j, aeval S.x (P k j) * (w j : L) := fun k ↦ by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, deriv_aeval_eq, hx, ← hPL k]
        simp only [map_mul, map_add, aeval_C, aeval_X]
        ring
      rw [Finset.sum_congr rfl fun k _ ↦ e1 k, Finset.sum_add_distrib]
      congr 1
      simp only [Finset.mul_sum, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_mul]; ring
    have h2 : (∑ l, algebraMap C L (Lam i l) * (e l : L)) * aeval S.x S0 =
        ∑ k, aeval S.x (∑ l, Polynomial.C (Lam i l) * S0 * p l k) * (w k : L) := by
      simp only [hpL, Finset.mul_sum, Finset.sum_mul, map_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
      simp only [map_mul, aeval_C]; ring
    rw [sub_mul, h1, h2, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [hD, map_sub, map_add]
    ring
  -- the key identity along the branch
  have hS0ne : S0 ≠ 0 := by rintro rfl; exact hS0 (coeff_zero 0)
  have hS0b : branchSub (K := K) N 0 S0 ≠ 0 := branchSub_zero_ne_zero N hN0 S0 hS0ne
  have hS0o : (branchSub (K := K) N 0 S0).order = 0 := by
    rw [order_branchSub_zero N hN0 S0 hS0ne, natTrailingDegree_eq_zero.mpr (Or.inr hS0)]
    simp
  have hkey : ∀ i, ∀ k : ℤ, 0 ≤ k → k < N →
      ((E i).coeff k)′ + algebraMap C K b * (k / N) * (E i).coeff k =
        ∑ j, algebraMap C K (Lam i j) * (E j).coeff k := by
    intro i k hk0 hkN
    have hmem := S.derivClosedXYW' (Polynomial.C b * X) hx (e i) (e i).2
    set R : C⟮S.x⟯⟮S.y⟯ := ⟨(e i : L)′, hmem⟩ - ∑ l, S.polyE (Polynomial.C (Lam i l)) * e l with hR
    have hRe : R * S.polyE S0 = ∑ k, S.polyE (D i k) * w k := by
      apply Subtype.ext
      simp only [hR, CurveData.polyE, MulMemClass.coe_mul, AddSubgroupClass.coe_sub,
        AddSubmonoidClass.coe_finsetSum, aeval_C]
      exact hDL i
    have hRb : LowerBd (φ R) N := by
      have h1 := hcomb (D i) (hD0 i)
      rw [← hRe, map_mul, show φ (S.polyE S0) = branchSub N 0 S0 from S.embG_polyX _ _ _ _ _ _]
        at h1
      have e : φ R = φ R * branchSub (K := K) N 0 S0 * (branchSub (K := K) N 0 S0)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hS0b, mul_one]
      rw [e]
      simpa using h1.mul (lowerBd_inv_of_order_zero hS0b hS0o)
    have hd := S.embG_dSW' (Polynomial.C b * X) hx hK (zeroSpeedE b N)
      (HahnSeries.C 0 + single (N : ℤ) 1) (dS_zeroSpeedE b N hN0) (branchSub N 0)
      (branchSub_injective N hN0 0) (fun P ↦ by rw [SuperData.branchSub_eq_subst])
      ρ hρ (e i : L) (e i).2
    simp only [Subtype.coe_eta] at hd
    have hφR : φ R = dS (zeroSpeedE b N) (E i) - ∑ l, HahnSeries.C (algebraMap C K (Lam i l)) * E l := by
      rw [hR, map_sub, map_sum]
      simp only [map_mul, hφC]
      rw [show φ ⟨(e i : L)′, hmem⟩ = dS (zeroSpeedE b N) (E i) from hd]
    have hc := hRb k hkN
    rw [hφR, HahnSeries.coeff_sub, coeff_dS_zeroSpeedE, HahnSeries.coeff_sum, sub_eq_zero] at hc
    rw [hc]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [LaurentSeries.coeff_C_mul]
  -- triangularity
  have hlcn : ∀ i, (E i).coeff (o i) ≠ 0 := fun i ↦ by rw [hlc]; exact pow_ne_zero _ hγ0
  have htri : ∀ i j, Lam i j ≠ 0 → o i ≤ o j := by
    intro i j hij
    by_contra hcon
    have hlt : o j < o i := by push Not at hcon; exact hcon
    set J := Finset.univ.filter fun j ↦ Lam i j ≠ 0 with hJ
    have hJne : J.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
    obtain ⟨j1, hj1J, hj1min⟩ := J.exists_min_image o hJne
    have hj1 : Lam i j1 ≠ 0 := (Finset.mem_filter.mp hj1J).2
    have hle : o j1 ≤ o j := hj1min j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
    have h := hkey i (o j1) (ho0 j1) (hoN j1)
    rw [hbelow i (o j1) (by omega), Derivation.map_zero (Differential.deriv (R := K)), mul_zero,
      add_zero, Finset.sum_eq_single j1] at h
    · exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap C K).injective).mpr hj1) (hlcn j1) h.symm
    · intro j2 _ hj2
      by_cases h2 : Lam i j2 = 0
      · rw [h2, map_zero, zero_mul]
      · have h3 : o j1 ≤ o j2 := hj1min j2 (by simp [hJ, h2])
        have h4 : o j1 < o j2 := lt_of_le_of_ne h3 fun h5 ↦ hj2 (hoinj _ _ h5).symm
        rw [hbelow j2 _ h4, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j1) h
  refine ⟨U, U⁻¹, Lam, Matrix.mul_nonsing_inv U hUu, Matrix.nonsing_inv_mul U hUu, rfl,
    fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · have h := htri i j hij
    have h1 := hno i; have h2 := hno j
    have : (N : ℤ) * (((i : ℕ) * d % n : ℕ) : ℤ) ≤ N * (((j : ℕ) * d % n : ℕ) : ℤ) := by nlinarith
    exact_mod_cast le_of_mul_le_mul_left this hNpos
  · -- the diagonal
    set c : C := (S.F.coeff 0).trailingCoeff with hc
    have hc0 : c ≠ 0 := trailingCoeff_nonzero_iff_nonzero.mpr ha0
    obtain ⟨q, hq⟩ : ∃ q : ℕ, (i : ℕ) * d % n = q := ⟨_, rfl⟩
    have hnoi := hno i
    rw [hq] at hnoi ⊢
    have h := hkey i (o i) (ho0 i) (hoN i)
    rw [Finset.sum_eq_single i] at h
    · rw [hlc, deriv_root_lead_gen (C := C) hK n hn0 ρ.leadingCoeff c hc0 hγ (i : ℕ)] at h
      have hpow : ρ.leadingCoeff ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hγ0
      have hov : ((o i : ℤ) : K) / N = ((q : ℕ) : K) / n := by
        have := hnoi
        have hnK : (n : K) ≠ 0 := by exact_mod_cast hn0.ne'
        have hNK : (N : K) ≠ 0 := by exact_mod_cast hN0.ne'
        rw [div_eq_div_iff hNK hnK]
        have e2 := congrArg (fun z : ℤ ↦ (z : K)) this
        push_cast at e2
        linear_combination e2
      apply (algebraMap C K).injective
      have h' : algebraMap C K (Lam i i) * ρ.leadingCoeff ^ (i : ℕ) =
          algebraMap C K (((q : ℕ) : C) / n * b +
            ((i : ℕ) : C) * (c′ / (n * c))) * ρ.leadingCoeff ^ (i : ℕ) := by
        rw [← h]
        simp only [map_add, map_div₀, map_mul, map_natCast]
        rw [show (((o i : ℤ) : K) / N) = ((q : ℕ) : K) / n from hov]
        push_cast
        ring
      exact mul_right_cancel₀ hpow h'
    · intro j _ hji
      by_cases h2 : Lam i j = 0
      · rw [h2, map_zero, zero_mul]
      · have h3 := htri i j h2
        have h4 : o i < o j := lt_of_le_of_ne h3 fun h5 ↦ hji (hoinj _ _ h5).symm
        rw [hbelow j _ h4, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

end Gauge0

end CurveData

end Curves
