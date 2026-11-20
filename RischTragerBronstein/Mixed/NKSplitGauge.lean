import RischTragerBronstein.Mixed.NKSplitInf
import RischTragerBronstein.Mixed.NKBasisExists
import RischTragerBronstein.Mixed.NKExp0Gauge

/-!
# Curves split at infinity: the gauge of the limit matrix

For a curve with `n` places at infinity whose leading polynomial `L` has distinct roots
`γ₁, …, γₙ ∈ C`, and an integral basis `w` normal at infinity (shifts `r`): the values at the
places at infinity of the rescaled basis `w̃ᵢ = x^{−rᵢ} wᵢ` form an invertible matrix
`A ∈ GLₙ(C)` with `A′ = Λ A`, `Λ` the limit at infinity of the rescaled derivation matrix
(`split_gauge`). So `Λ` is gauge-trivial over `C`: `Aᵀ Λᵀ = (Aᵀ)′`.

The values are computed through the powers of `u = y/xˢ`, whose branches have constant terms
`γₖ` (Vandermonde), so that the coordinates `w̃ᵢ = ∑ βᵢⱼ uʲ` have no pole at infinity
(`lowerBd_of_vecMul`) and `A = β(∞) V`.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Mat

variable {K : Type*} [Field K]

/-- **Solving with a power-series matrix**: if `M` has entries without pole and `det M` has a
non-zero constant term, a row vector `x` with `x M` without pole has no pole. -/
lemma lowerBd_of_vecMul {n : ℕ} (M : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (hM : ∀ i j, LowerBd (M i j) 0) (hdet : (M.det).coeff 0 ≠ 0) (x : Fin n → LaurentSeries K)
    (hx : ∀ m, LowerBd (∑ j, x j * M j m) 0) : ∀ j, LowerBd (x j) 0 := by
  classical
  set M' : Matrix (Fin n) (Fin n) (PowerSeries K) := M.map toPS with hM'
  have hMM : M = M'.map (ofPowerSeries ℤ K) := by
    ext i j; simp [hM', ofPS_toPS (hM i j)]
  have hdetM : M.det = ofPowerSeries ℤ K M'.det := by
    rw [hMM]; exact (RingHom.map_det _ _).symm
  have hadj : M.adjugate = M'.adjugate.map (ofPowerSeries ℤ K) := by
    rw [hMM]; exact (RingHom.map_adjugate _ _).symm
  have hLB : ∀ z : PowerSeries K, LowerBd (ofPowerSeries ℤ K z) 0 := fun z k hk ↦ by
    rw [LaurentSeries.coeff_ofPS, if_neg (by omega)]
  have hD0 : M.det ≠ 0 := fun h ↦ hdet (by rw [h, HahnSeries.coeff_zero])
  have hDo : M.det.order = 0 := by
    have h1 : 0 ≤ M.det.order := by rw [hdetM]; exact order_nonneg_of_lowerBd_nk _ (hLB _)
    by_contra hne
    have : 0 < M.det.order := lt_of_le_of_ne h1 (Ne.symm hne)
    exact hdet (HahnSeries.coeff_eq_zero_of_lt_order this)
  have hDi : LowerBd (M.det)⁻¹ 0 := lowerBd_inv_of_order_zero hD0 hDo
  have hinv : M⁻¹ = (M.det)⁻¹ • M.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have hx' : x = Matrix.vecMul (Matrix.vecMul x M) M⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hD0),
      Matrix.vecMul_one]
  intro j
  rw [hx']
  simp only [Matrix.vecMul, dotProduct, hinv, Matrix.smul_apply, smul_eq_mul, hadj,
    Matrix.map_apply]
  refine lowerBd_sum _ _ fun m _ ↦ ?_
  have := (hx m).mul (hDi.mul (hLB (M'.adjugate m j)))
  simpa using this

lemma coeff_zero_mul_of_lowerBd {a b : LaurentSeries K} (ha : LowerBd a 0) (hb : LowerBd b 0) :
    (a * b).coeff 0 = a.coeff 0 * b.coeff 0 := by
  rw [← ofPS_toPS ha, ← ofPS_toPS hb, ← map_mul, LaurentSeries.coeff_ofPS, if_pos le_rfl,
    LaurentSeries.coeff_ofPS, if_pos le_rfl, LaurentSeries.coeff_ofPS, if_pos le_rfl]
  simp only [Int.toNat_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]

lemma coeff_zero_pow_of_lowerBd {a : LaurentSeries K} (ha : LowerBd a 0) (j : ℕ) :
    (a ^ j).coeff 0 = a.coeff 0 ^ j := by
  rw [← ofPS_toPS ha, ← map_pow, LaurentSeries.coeff_ofPS, if_pos le_rfl,
    LaurentSeries.coeff_ofPS, if_pos le_rfl]
  simp only [Int.toNat_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]

/-- The determinant of a matrix of series without pole has constant term the determinant of the
constant terms. -/
lemma coeff_zero_det_of_lowerBd {n : ℕ} (M : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (hM : ∀ i j, LowerBd (M i j) 0) :
    (M.det).coeff 0 = (M.map fun z ↦ z.coeff 0).det := by
  set M' : Matrix (Fin n) (Fin n) (PowerSeries K) := M.map toPS with hM'
  have hMM : M = M'.map (ofPowerSeries ℤ K) := by
    ext i j; simp [hM', ofPS_toPS (hM i j)]
  have h1 : M.det = ofPowerSeries ℤ K M'.det := by
    rw [hMM]; exact (RingHom.map_det _ _).symm
  rw [h1, LaurentSeries.coeff_ofPS, if_pos le_rfl, Int.toNat_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, RingHom.map_det]
  congr 1

end Mat

section RatInf

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- A quotient `p(T^{-N})/q(T^{-N})` without pole has `deg p ≤ deg q`. -/
lemma natDegree_le_of_lowerBd_div (N : ℕ) (hN : 0 < N) (p q : C[X]) (hq : q ≠ 0)
    (h : LowerBd (infSub (K := K) N p * (infSub (K := K) N q)⁻¹) 0) :
    p.natDegree ≤ q.natDegree := by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero]; exact Nat.zero_le _
  have hp' := infSub_ne_zero (K := K) N hN p hp
  have hq' := infSub_ne_zero (K := K) N hN q hq
  have ho := order_nonneg_of_lowerBd_nk _ h
  rw [HahnSeries.order_mul hp' (inv_ne_zero hq'), order_inv_nk _ hq', order_infSub N hN p hp,
    order_infSub N hN q hq] at ho
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  have : (N : ℤ) * p.natDegree ≤ N * q.natDegree := by push_cast at ho; linarith
  exact_mod_cast le_of_mul_le_mul_left this hNpos

end RatInf

end Curves

namespace Curves

open Differential

namespace CurveData

section SplitGauge

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

/-- **The expansion of a function along a branch above infinity** in the powers of the scaled
root `Z = r T^{N s}`: if `z Q(x) = ∑_{j<n} Wⱼ(x) yʲ` then
`z = ∑ⱼ (Wⱼ xˢʲ)(T^{-N}) / Q(T^{-N}) · Zʲ`. -/
lemma embG_expand (N s : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0) (z : C⟮S.x⟯⟮S.y⟯) (W : C[X][X]) (Q : C[X])
    (hQ : Q ≠ 0) (hWQ : (z : L) * aeval S.x Q = S.evXY W) (hWn : W.natDegree < S.F.natDegree) :
    S.embG (infSub N) (infSub_injective N hN) r hr z =
      ∑ j ∈ Finset.range S.F.natDegree, infSub (K := K) N (W.coeff j * X ^ (s * j)) *
        (infSub (K := K) N Q)⁻¹ * (r * single ((N * s : ℕ) : ℤ) 1) ^ j := by
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
  have key : (single (-(N : ℤ)) (1 : K)) ^ (s * j) * (single ((N * s : ℕ) : ℤ) (1 : K)) ^ j = 1 := by
    rw [single_pow, single_pow, one_pow, one_pow, single_mul_single, mul_one]
    convert HahnSeries.single_zero_one using 2
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [coeff_map, map_mul, map_pow, infSub_X_K, mul_pow]
  linear_combination (-(infSub (K := K) N (W.coeff j) * r ^ j * (infSub (K := K) N Q)⁻¹)) * key

set_option maxHeartbeats 4000000 in
/-- **The gauge at infinity of a curve split at infinity**: the values `A` at the places at
infinity of the rescaled basis form an invertible matrix with `A′ = Λ A`. -/
theorem split_gauge (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′) (s : ℕ)
    (hdegF : ∀ i < S.F.natDegree, (S.F.coeff i).natDegree ≤ s * (S.F.natDegree - i))
    (γ : Fin S.F.natDegree → C) (hγ : Function.Injective γ)
    (hL : leadPoly s S.F = ∏ k, (X - Polynomial.C (γ k)))
    (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ)
    (hrw : ∀ j, S.InfOrd K (w j) (r j)) (hred : S.Reduced K w r) (S0 : C[X]) (hS00 : S0 ≠ 0)
    (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C η) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
      S.polyE S0 = ∑ j, S.polyE (P i j) * w j)
    (hdeg : ∀ i j, (pqV η r P S0 i j).natDegree ≤ (X ^ (r i + 1) * S0).natDegree) :
    ∃ A : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C, A.det ≠ 0 ∧
      ∀ i m, (A i m)′ = ∑ j, (pqV η r P S0 i j).coeff (X ^ (r i + 1) * S0).natDegree /
        (X ^ (r i + 1) * S0).leadingCoeff * A j m := by
  classical
  -- a branch system above infinity and the branches of the `γₖ`
  obtain ⟨N, hN, l, -, hl⟩ := S.hasBranchesInf (K := K)
  have hN0 := Nat.pos_of_ne_zero hN
  set b : LaurentSeries K := single ((N * s : ℕ) : ℤ) 1 with hb
  obtain ⟨hZ, hprod⟩ := leadPoly_eq_prod N s hN0 S.F S.monic hdegF l hl
  have hex : ∀ k, ∃ ρ ∈ l, (ρ * b).coeff 0 = algebraMap C K (γ k) := by
    intro k
    have h := congrArg (Polynomial.eval (algebraMap C K (γ k))) hprod
    rw [hL, Polynomial.map_prod, eval_prod,
      Finset.prod_eq_zero (Finset.mem_univ k) (by simp), eval_list_prod, List.map_map] at h
    obtain ⟨v, hv, hv0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h.symm)
    refine ⟨v, hv, ?_⟩
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at hv0
    exact (sub_eq_zero.mp hv0).symm
  choose ρ hρl hργ using hex
  have hρr : ∀ k, (S.F.map (infSub N)).eval (ρ k) = 0 := fun k ↦ S.root_of_mem hl (hρl k)
  -- the coordinates of the rescaled basis in the powers of `u = y/xˢ`
  have hF1 : S.F ≠ 1 := fun h ↦ S.natDegree_F_ne_zero (by rw [h, natDegree_one])
  choose Wr Qr hQr hWQr hWnr using fun i ↦ S.exists_repr_lt (S.wTil w r i) hF1
  set pc : Fin S.F.natDegree → Fin S.F.natDegree → C[X] := fun i j ↦
    (Wr i).coeff (j : ℕ) * X ^ (s * (j : ℕ)) with hpc
  -- expansions along any root above infinity
  have hexpand : ∀ (N' : ℕ) (hN' : 0 < N') (r' : LaurentSeries K)
      (hr' : (S.F.map (infSub N')).eval r' = 0) (i : Fin S.F.natDegree),
      S.embG (infSub N') (infSub_injective N' hN') r' hr' (S.wTil w r i) =
        ∑ j : Fin S.F.natDegree, infSub (K := K) N' (pc i j) * (infSub (K := K) N' (Qr i))⁻¹ *
          (r' * single ((N' * s : ℕ) : ℤ) 1) ^ (j : ℕ) := fun N' hN' r' hr' i ↦ by
    rw [S.embG_expand N' s hN' r' hr' _ (Wr i) (Qr i) (hQr i) (hWQr i) (hWnr i)]
    exact (Fin.sum_univ_eq_sum_range (fun j ↦ infSub (K := K) N' ((Wr i).coeff j * X ^ (s * j)) *
      (infSub (K := K) N' (Qr i))⁻¹ * (r' * single ((N' * s : ℕ) : ℤ) 1) ^ j) _).symm
  set φ : Fin S.F.natDegree → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K) := fun m ↦
    S.embG (infSub N) (infSub_injective N hN0) (ρ m) (hρr m) with hφ
  set M : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) (LaurentSeries K) :=
    Matrix.of fun j m ↦ (ρ m * b) ^ (j : ℕ) with hM
  set xq : Fin S.F.natDegree → Fin S.F.natDegree → LaurentSeries K := fun i j ↦
    infSub (K := K) N (pc i j) * (infSub (K := K) N (Qr i))⁻¹ with hxq
  have hMLB : ∀ j m, LowerBd (M j m) 0 := fun j m ↦ lowerBd_pow0 (hZ _ (hρl m)) _
  have hWLB : ∀ i m, LowerBd (φ m (S.wTil w r i)) 0 := fun i m ↦ by
    have := S.infOrd_wTil w r i (hrw i) N hN l hl (ρ m) (hρl m)
    simpa using this
  have hdet : (M.det).coeff 0 ≠ 0 := by
    rw [coeff_zero_det_of_lowerBd M hMLB]
    have e : (M.map fun z ↦ z.coeff 0) =
        (Matrix.vandermonde fun m ↦ algebraMap C K (γ m)).transpose := by
      ext j m
      simp only [hM, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
        Matrix.vandermonde]
      rw [coeff_zero_pow_of_lowerBd (hZ _ (hρl m)), hργ]
    rw [e, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr ((algebraMap C K).injective.comp hγ)
  have hxLB : ∀ i j, LowerBd (xq i j) 0 := fun i ↦ lowerBd_of_vecMul M hMLB hdet (xq i)
    fun m ↦ by
      have := hexpand N hN0 (ρ m) (hρr m) i
      have h2 := hWLB i m
      rw [show φ m (S.wTil w r i) = _ from this] at h2
      exact h2
  have hpq : ∀ i j, (pc i j).natDegree ≤ (Qr i).natDegree := fun i j ↦
    natDegree_le_of_lowerBd_div N hN0 _ _ (hQr i) (hxLB i j)
  set B : Fin S.F.natDegree → Fin S.F.natDegree → C := fun i j ↦
    (pc i j).coeff (Qr i).natDegree / (Qr i).leadingCoeff with hB
  set A : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C :=
    Matrix.of fun i m ↦ ∑ j, B i j * γ m ^ (j : ℕ) with hA
  have hxq0 : ∀ i j, (xq i j).coeff 0 = algebraMap C K (B i j) := fun i j ↦ by
    have h := lowerBd_infSub_div (K := K) N hN0 (pc i j) (Qr i) (hQr i) (hpq i j) 0
      (by exact_mod_cast hN0)
    rw [HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_eq_zero] at h
    exact h
  have hT0 : ∀ i m, (φ m (S.wTil w r i)).coeff 0 = algebraMap C K (A i m) := fun i m ↦ by
    rw [show φ m (S.wTil w r i) = _ from hexpand N hN0 (ρ m) (hρr m) i, HahnSeries.coeff_sum]
    simp only [hA, Matrix.of_apply, map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [coeff_zero_mul_of_lowerBd (hxLB i j) (lowerBd_pow0 (hZ _ (hρl m)) _),
      coeff_zero_pow_of_lowerBd (hZ _ (hρl m)), hργ]
    exact congrArg (· * _) (hxq0 i j)
  -- `A` is invertible (normality at infinity)
  have hA0 : A.det ≠ 0 := by
    intro hdet0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet0
    set Vt : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C :=
      (Matrix.vandermonde γ).transpose with hVt
    have hAB : A = (Matrix.of B) * Vt := by
      ext i m
      simp [hA, hVt, Matrix.mul_apply, Matrix.vandermonde]
    have hVt0 : Vt.det ≠ 0 := by
      rw [hVt, Matrix.det_transpose]; exact Matrix.det_vandermonde_ne_zero_iff.mpr hγ
    have hvB : Matrix.vecMul v (Matrix.of B) = 0 := by
      by_contra hne
      apply hVt0
      refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, ?_⟩
      rw [Matrix.vecMul_vecMul, ← hAB, hv]
    apply hv0
    funext i
    refine hred v ?_ i
    intro N' hN' l' hl' r' hr'
    have hN'0 := Nat.pos_of_ne_zero hN'
    obtain ⟨hZ', -⟩ := leadPoly_eq_prod N' s hN'0 S.F S.monic hdegF l' hl'
    have hz : (∑ j, S.polyE (Polynomial.C (v j)) * ((S.polyE (X ^ r j))⁻¹ * w j)) =
        ∑ j, S.polyE (Polynomial.C (v j)) * S.wTil w r j := rfl
    rw [hz, map_sum]
    simp only [map_mul, S.embG_polyX, infSub_C, hexpand N' hN'0 r' (S.root_of_mem hl' hr')]
    -- regroup by powers of `u`
    have e : ∑ i : Fin S.F.natDegree, HahnSeries.C (algebraMap C K (v i)) *
        ∑ j : Fin S.F.natDegree, infSub (K := K) N' (pc i j) * (infSub (K := K) N' (Qr i))⁻¹ *
          (r' * single ((N' * s : ℕ) : ℤ) 1) ^ (j : ℕ) =
        ∑ j : Fin S.F.natDegree, (∑ i : Fin S.F.natDegree, HahnSeries.C (algebraMap C K (v i)) *
          (infSub (K := K) N' (pc i j) * (infSub (K := K) N' (Qr i))⁻¹ -
            HahnSeries.C (algebraMap C K (B i j)))) *
          (r' * single ((N' * s : ℕ) : ℤ) 1) ^ (j : ℕ) := by
      have hsum : ∀ j : Fin S.F.natDegree, (∑ i : Fin S.F.natDegree,
          HahnSeries.C (algebraMap C K (v i)) * HahnSeries.C (algebraMap C K (B i j)) :
            LaurentSeries K) = 0 := by
        intro j
        have h0 : ∑ i, v i * B i j = 0 := by
          have := congrFun hvB j
          simpa [Matrix.vecMul, dotProduct] using this
        calc (∑ i : Fin S.F.natDegree, HahnSeries.C (algebraMap C K (v i)) *
              HahnSeries.C (algebraMap C K (B i j)) : LaurentSeries K)
            = HahnSeries.C (algebraMap C K (∑ i, v i * B i j)) := by
              simp only [map_sum, map_mul]
          _ = 0 := by rw [h0, map_zero, map_zero]
      calc ∑ i : Fin S.F.natDegree, HahnSeries.C (algebraMap C K (v i)) *
            ∑ j : Fin S.F.natDegree, infSub (K := K) N' (pc i j) *
              (infSub (K := K) N' (Qr i))⁻¹ * (r' * single ((N' * s : ℕ) : ℤ) 1) ^ (j : ℕ)
          = ∑ j : Fin S.F.natDegree, (∑ i : Fin S.F.natDegree,
              HahnSeries.C (algebraMap C K (v i)) * (infSub (K := K) N' (pc i j) *
                (infSub (K := K) N' (Qr i))⁻¹)) * (r' * single ((N' * s : ℕ) : ℤ) 1) ^ (j : ℕ) := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ ↦ by ring
        _ = _ := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            congr 1
            rw [← sub_zero (∑ i : Fin S.F.natDegree, HahnSeries.C (algebraMap C K (v i)) *
              (infSub (K := K) N' (pc i j) * (infSub (K := K) N' (Qr i))⁻¹)), ← hsum j,
              ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [e]
    refine lowerBd_sum _ _ fun j _ ↦ ?_
    have h1 : LowerBd (∑ i : Fin S.F.natDegree, HahnSeries.C (algebraMap C K (v i)) *
        (infSub (K := K) N' (pc i j) * (infSub (K := K) N' (Qr i))⁻¹ -
          HahnSeries.C (algebraMap C K (B i j)))) N' :=
      lowerBd_sum _ _ fun i _ ↦
        ((lowerBd_C _).mul
          (lowerBd_infSub_div (K := K) N' hN'0 (pc i j) (Qr i) (hQr i) (hpq i j))).mono
          (by simp)
    exact (h1.mul (lowerBd_pow0 (hZ' r' hr') (j : ℕ))).mono (by simp)
  -- the derivative: `A′ = Λ A`
  refine ⟨A, hA0, fun i m ↦ ?_⟩
  apply (algebraMap C K).injective
  set q : C[X] := X ^ (r i + 1) * S0 with hq
  have hq0 : q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
  have hqK := infSub_ne_zero (K := K) N hN0 q hq0
  have hmem := S.derivClosedXYW' (Polynomial.C η) hx (S.wTil w r i) (S.wTil w r i).2
  -- the derivative of `w̃ᵢ` along the branch
  have hdw := S.deriv_wTil η hx w r S0 P hP i
  have hid : (⟨(S.wTil w r i : L)′, hmem⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE q =
      ∑ j, S.polyE (pqV η r P S0 i j) * S.wTil w r j := Subtype.ext (by
    push_cast
    exact hdw)
  have hemb := congrArg (φ m) hid
  rw [map_mul, map_sum] at hemb
  simp only [map_mul] at hemb
  rw [show φ m (S.polyE q) = infSub N q from S.embG_polyX _ _ _ _ _ _] at hemb
  have hpoly : ∀ j, φ m (S.polyE (pqV η r P S0 i j)) = infSub N (pqV η r P S0 i j) := fun j ↦
    S.embG_polyX _ _ _ _ _ _
  simp only [hpoly] at hemb
  have hder : φ m ⟨(S.wTil w r i : L)′, hmem⟩ =
      ∑ j, (infSub (K := K) N (pqV η r P S0 i j) * (infSub (K := K) N q)⁻¹) *
        φ m (S.wTil w r j) := by
    have : φ m ⟨(S.wTil w r i : L)′, hmem⟩ =
        (∑ j, infSub (K := K) N (pqV η r P S0 i j) * φ m (S.wTil w r j)) *
          (infSub (K := K) N q)⁻¹ := by
      rw [← hemb, mul_assoc, mul_inv_cancel₀ hqK, mul_one]
    rw [this, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hL := S.coeff_embG_deriv_inf η hx hK N hN0 (ρ m) (hρr m) (S.wTil w r i) (hWLB i m) 0
    (by exact_mod_cast hN0)
  rw [← hK, ← hT0 i m, ← hL]
  change (φ m ⟨(S.wTil w r i : L)′, hmem⟩).coeff 0 = _
  rw [hder, HahnSeries.coeff_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hlim := lowerBd_infSub_div (K := K) N hN0 (pqV η r P S0 i j) q hq0 (hdeg i j)
  have hLB : LowerBd (infSub (K := K) N (pqV η r P S0 i j) * (infSub (K := K) N q)⁻¹) 0 := by
    have h2 := (hlim.mono (show (0 : ℤ) ≤ N by positivity)).add
      (lowerBd_C (algebraMap C K ((pqV η r P S0 i j).coeff q.natDegree / q.leadingCoeff)))
    rwa [sub_add_cancel] at h2
  rw [coeff_zero_mul_of_lowerBd hLB (hWLB j m), hT0 j m, RingHom.map_mul (algebraMap C K)]
  congr 1
  have h0 := hlim 0 (by exact_mod_cast hN0)
  rw [HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_eq_zero] at h0
  exact h0

/-- **Integral bases normal at infinity with the derivation matrix of a curve with any
coefficients** (no condition at infinity). -/
theorem exists_nkBasisG (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′) :
    ∃ (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ) (S0 : C[X])
      (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X]),
      S.IBasis K w ∧ (∀ j, S.InfOrd K (w j) (r j)) ∧ S.Reduced K w r ∧
      (∀ c : Fin S.F.natDegree → C⟮S.x⟯,
        ∑ j, algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (c j) * w j = 0 → ∀ j, c j = 0) ∧
      S0 ≠ 0 ∧ Squarefree S0 ∧
      (∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C η) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
        S.polyE S0 = ∑ j, S.polyE (P i j) * w j) ∧
      (∀ i j, (pqV η r P S0 i j).natDegree ≤ (X ^ (r i + 1) * S0).natDegree) := by
  classical
  obtain ⟨w0, hw0⟩ := S.exists_IBasis K
  obtain ⟨w, r, hwB, hrw, hredw⟩ := S.exists_reduced K w0 hw0
  -- `S₀ wᵢ′` is a polynomial combination
  have hderiv : ∀ i, ∃ (Wd : C[X][X]) (Qd : C[X]), Qd ≠ 0 ∧
      ((w i : L))′ * aeval S.x Qd = S.evXY Wd := fun i ↦
    S.exists_repr ⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C η) hx _ (w i).2⟩
  choose Wd Qd hQd hWQd using hderiv
  set S0 := UniqueFactorizationMonoid.radical (∏ i, Qd i) with hS0
  have hQprod : ∏ i, Qd i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hQd i
  have hS00 : S0 ≠ 0 := radical_ne_zero' _
  have hcoord : ∀ i, ∃ c : Fin S.F.natDegree → C[X],
      (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C η) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
        S.polyE S0 = ∑ j, S.polyE (c j) * w j := by
    intro i
    have hreg := S.regularFinite_rad_derivW (K := K) (Polynomial.C η) hx hK (w i) (hwB.1 i) (Wd i)
      (Qd i) (hQd i) (hWQd i)
    obtain ⟨T, hT⟩ : UniqueFactorizationMonoid.radical (Qd i) ∣ S0 :=
      UniqueFactorizationMonoid.radical_dvd_radical (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
        hQprod
    have hreg2 := S.regularFinite_polyE_mul (K := K) T hreg
    obtain ⟨c, hc⟩ := hwB.2.1 _ hreg2
    refine ⟨c, ?_⟩
    rw [← hc, hT, S.polyE_mul]
    ring
  choose P hP using hcoord
  -- normality at infinity: the rescaled matrix is bounded
  have hdeg : ∀ i j, (pqV η r P S0 i j).natDegree ≤ (X ^ (r i + 1) * S0).natDegree := by
    intro i
    have hwt0 : S.InfOrd K (S.wTil w r i) 0 := S.infOrd_wTil w r i (hrw i)
    have hu := S.infOrd_derivW η hx hK (S.wTil w r i) 0 hwt0
    have hq : (X ^ (r i + 1) * S0 : C[X]) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
    have hid := S.deriv_wTil η hx w r S0 P hP i
    refine S.reduced_normal (K := K) w r hrw hredw _ hu (fun j ↦ pqV η r P S0 i j)
      (X ^ (r i + 1) * S0) hq ?_
    have hqL : aeval S.x (X ^ (r i + 1) * S0) ≠ 0 := fun h ↦ hq ((transcendental_iff.mp S.htr) _ h)
    apply Subtype.ext
    have e : ((∑ j, S.polyE (pqV η r P S0 i j) * (S.polyE (X ^ (r i + 1) * S0))⁻¹ *
        ((S.polyE (X ^ r j))⁻¹ * w j) : C⟮S.x⟯⟮S.y⟯) : L) =
        (∑ j, aeval S.x (pqV η r P S0 i j) * (S.wTil w r j : L)) / aeval S.x (X ^ (r i + 1) * S0) := by
      rw [Finset.sum_div]
      push_cast
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [polyE, wTil]
      push_cast
      ring
    rw [e, eq_div_iff hqL]
    exact hid
  refine ⟨w, r, S0, P, hwB, hrw, hredw, ?_, hS00,
    UniqueFactorizationMonoid.squarefree_radical, hP, hdeg⟩
  · -- independence over `C(x)`: clear denominators
    intro c hc
    letI := algebraAdjoinSimple (F := C) S.x
    haveI := isFractionRing_adjoin_simple S.x S.htr
    have hpoly : ∀ p : C[X], S.polyE p =
        algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (algebraMap C[X] C⟮S.x⟯ p) := fun p ↦ Subtype.ext (by
      show aeval S.x p = ((algebraMap C[X] C⟮S.x⟯ p : C⟮S.x⟯) : L)
      rw [algebraMap_adjoinSimple])
    obtain ⟨⟨dd, hdd⟩, hdc⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors C[X]) (Finset.univ.image c)
    choose p hp using fun j ↦ hdc (c j) (Finset.mem_image_of_mem c (Finset.mem_univ j))
    have hd0 : dd ≠ 0 := nonZeroDivisors.ne_zero hdd
    have h0 := hwB.2.2 p (by
      have : ∑ j, S.polyE (p j) * w j =
          algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (algebraMap C[X] C⟮S.x⟯ dd) *
            ∑ j, algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (c j) * w j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hpoly, hp j, Algebra.smul_def, map_mul]
        ring
      rw [this, hc, mul_zero])
    intro j
    have := hp j
    rw [h0 j, map_zero, Algebra.smul_def] at this
    have hdne : algebraMap C[X] C⟮S.x⟯ dd ≠ 0 := fun h ↦ hd0 (IsFractionRing.injective C[X] C⟮S.x⟯
      (by rw [h, map_zero]))
    exact (mul_eq_zero.mp this.symm).resolve_left hdne

end SplitGauge

end CurveData

end Curves
