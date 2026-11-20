import RischTragerBronstein.Mixed.NKSplitGauge
import RischTragerBronstein.Mixed.NKExpCurve

/-!
# Curves split at infinity over an exponential level: the gauge of the limit matrix

`split_gaugeE`, `exists_nkBasisEG`: `split_gauge`, `exists_nkBasisG` for `x′ = a′ x`. Above
infinity the derivation acts on the coefficient of `T⁰` as the coefficient derivation
(`coeff_dS_infSpeedE`), so the values `A` at the places at infinity of the rescaled basis
satisfy `A′ = Λ A` as at a logarithmic level. The basis has `S₀(0) ≠ 0` (derivatives have no
pole above `x = 0`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

namespace CurveData

section SplitGaugeE

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

/-- **The limit matrix at infinity is gauge-trivial** (curves split at infinity, exponential
level). -/
theorem split_gaugeE (b : C) (hx : S.x′ = aeval S.x (Polynomial.C b * X))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′) (s : ℕ)
    (hdegF : ∀ i < S.F.natDegree, (S.F.coeff i).natDegree ≤ s * (S.F.natDegree - i))
    (γ : Fin S.F.natDegree → C) (hγ : Function.Injective γ)
    (hL : leadPoly s S.F = ∏ k, (X - Polynomial.C (γ k)))
    (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ)
    (hrw : ∀ j, S.InfOrd K (w j) (r j)) (hred : S.Reduced K w r) (S0 : C[X]) (hS00 : S0 ≠ 0)
    (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
      S.polyE S0 = ∑ j, S.polyE (P i j) * w j)
    (hdeg : ∀ i j, (pqE b r P S0 i j).natDegree ≤ (X ^ r i * S0).natDegree) :
    ∃ A : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C, A.det ≠ 0 ∧
      ∀ i m, (A i m)′ = ∑ j, (pqE b r P S0 i j).coeff (X ^ r i * S0).natDegree /
        (X ^ r i * S0).leadingCoeff * A j m := by
  classical
  -- a branch system above infinity and the branches of the `γₖ`
  obtain ⟨N, hN, l, -, hl⟩ := S.hasBranchesInf (K := K)
  have hN0 := Nat.pos_of_ne_zero hN
  set bT : LaurentSeries K := single ((N * s : ℕ) : ℤ) 1 with hbT
  obtain ⟨hZ, hprod⟩ := leadPoly_eq_prod N s hN0 S.F S.monic hdegF l hl
  have hex : ∀ k, ∃ ρ ∈ l, (ρ * bT).coeff 0 = algebraMap C K (γ k) := by
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
    Matrix.of fun j m ↦ (ρ m * bT) ^ (j : ℕ) with hM
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
  set q : C[X] := X ^ r i * S0 with hq
  have hq0 : q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
  have hqK := infSub_ne_zero (K := K) N hN0 q hq0
  have hmem := S.derivClosedXYW' (Polynomial.C b * X) hx (S.wTil w r i) (S.wTil w r i).2
  -- the derivative of `w̃ᵢ` along the branch
  have hdw := S.deriv_wTilE b hx w r S0 P hP i
  have hid : (⟨(S.wTil w r i : L)′, hmem⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE q =
      ∑ j, S.polyE (pqE b r P S0 i j) * S.wTil w r j := Subtype.ext (by
    push_cast
    exact hdw)
  have hemb := congrArg (φ m) hid
  rw [map_mul, map_sum] at hemb
  simp only [map_mul] at hemb
  rw [show φ m (S.polyE q) = infSub N q from S.embG_polyX _ _ _ _ _ _] at hemb
  have hpoly : ∀ j, φ m (S.polyE (pqE b r P S0 i j)) = infSub N (pqE b r P S0 i j) := fun j ↦
    S.embG_polyX _ _ _ _ _ _
  simp only [hpoly] at hemb
  have hder : φ m ⟨(S.wTil w r i : L)′, hmem⟩ =
      ∑ j, (infSub (K := K) N (pqE b r P S0 i j) * (infSub (K := K) N q)⁻¹) *
        φ m (S.wTil w r j) := by
    have : φ m ⟨(S.wTil w r i : L)′, hmem⟩ =
        (∑ j, infSub (K := K) N (pqE b r P S0 i j) * φ m (S.wTil w r j)) *
          (infSub (K := K) N q)⁻¹ := by
      rw [← hemb, mul_assoc, mul_inv_cancel₀ hqK, mul_one]
    rw [this, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hL : (φ m ⟨(S.wTil w r i : L)′, hmem⟩).coeff 0 = ((φ m (S.wTil w r i)).coeff 0)′ := by
    change (S.embG (infSub N) (infSub_injective N hN0) (ρ m) (hρr m)
      ⟨(S.wTil w r i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (S.wTil w r i).2⟩).coeff 0 = _
    rw [S.embG_deriv_infE b hx hK N hN0 (ρ m) (hρr m) (S.wTil w r i), coeff_dS_infSpeedE]
    simp only [Int.cast_zero, zero_div, mul_zero, zero_mul, sub_zero]
    rfl
  rw [← hK, ← hT0 i m, ← hL]
  change (φ m ⟨(S.wTil w r i : L)′, hmem⟩).coeff 0 = _
  rw [hder, HahnSeries.coeff_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hlim := lowerBd_infSub_div (K := K) N hN0 (pqE b r P S0 i j) q hq0 (hdeg i j)
  have hLB : LowerBd (infSub (K := K) N (pqE b r P S0 i j) * (infSub (K := K) N q)⁻¹) 0 := by
    have h2 := (hlim.mono (show (0 : ℤ) ≤ N by positivity)).add
      (lowerBd_C (algebraMap C K ((pqE b r P S0 i j).coeff q.natDegree / q.leadingCoeff)))
    rwa [sub_add_cancel] at h2
  rw [coeff_zero_mul_of_lowerBd hLB (hWLB j m), hT0 j m, RingHom.map_mul (algebraMap C K)]
  congr 1
  have h0 := hlim 0 (by exact_mod_cast hN0)
  rw [HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_eq_zero] at h0
  exact h0

/-- **Integral bases normal at infinity with the derivation matrix of a curve with any
coefficients over an exponential level** (no condition at infinity; `S₀(0) ≠ 0`). -/
theorem exists_nkBasisEG (b : C) (hx : S.x′ = aeval S.x (Polynomial.C b * X))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′) :
    ∃ (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ) (S0 : C[X])
      (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X]),
      S.IBasis K w ∧ (∀ j, S.InfOrd K (w j) (r j)) ∧ S.Reduced K w r ∧
      (∀ c : Fin S.F.natDegree → C⟮S.x⟯,
        ∑ j, algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (c j) * w j = 0 → ∀ j, c j = 0) ∧
      S0 ≠ 0 ∧ Squarefree S0 ∧ S0.coeff 0 ≠ 0 ∧
      (∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
        S.polyE S0 = ∑ j, S.polyE (P i j) * w j) ∧
      (∀ i j, (pqE b r P S0 i j).natDegree ≤ (X ^ r i * S0).natDegree) := by
  classical
  obtain ⟨w0, hw0⟩ := S.exists_IBasis K
  obtain ⟨w, r, hwB, hrw, hredw⟩ := S.exists_reduced K w0 hw0
  -- `S₀ wᵢ′` is a polynomial combination
  have hderiv : ∀ i, ∃ (Wd : C[X][X]) (Qd : C[X]), Qd ≠ 0 ∧
      ((w i : L))′ * aeval S.x Qd = S.evXY Wd := fun i ↦
    S.exists_repr ⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩
  choose Wd Qd hQd hWQd using hderiv
  set R := UniqueFactorizationMonoid.radical (∏ i, Qd i) with hRdef
  have hQprod : ∏ i, Qd i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hQd i
  have hR0 : R ≠ 0 := radical_ne_zero' _
  have hRsq : Squarefree R := UniqueFactorizationMonoid.squarefree_radical
  obtain ⟨S0, hRS, hS0X⟩ : ∃ S0 : C[X], (R = X * S0 ∨ R = S0) ∧ ¬ X ∣ S0 := by
    by_cases hX : X ∣ R
    · obtain ⟨S0, hS0⟩ := hX
      refine ⟨S0, Or.inl hS0, fun hX2 ↦ ?_⟩
      obtain ⟨T0, hT0⟩ := hX2
      have := hRsq X ⟨T0, by rw [hS0, hT0]; ring⟩
      exact not_isUnit_X this
    · exact ⟨R, Or.inr rfl, hX⟩
  have hS00 : S0 ≠ 0 := by
    rintro rfl; rcases hRS with h | h <;> simp [h] at hR0
  have hsq0 : Squarefree S0 := by
    rcases hRS with h | h
    · rw [h] at hRsq; exact hRsq.of_mul_right
    · rw [← h]; exact hRsq
  have hcoord : ∀ i, ∃ c : Fin S.F.natDegree → C[X],
      (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
        S.polyE S0 = ∑ j, S.polyE (c j) * w j := by
    intro i
    have hreg := S.regularFinite_rad_derivW (K := K) (Polynomial.C b * X) hx hK (w i) (hwB.1 i) (Wd i)
      (Qd i) (hQd i) (hWQd i)
    obtain ⟨T, hT⟩ : UniqueFactorizationMonoid.radical (Qd i) ∣ R :=
      UniqueFactorizationMonoid.radical_dvd_radical (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
        hQprod
    have hreg2 := S.regularFinite_polyE_mul (K := K) T hreg
    have hreg3 : S.RegularFinite K (S.polyE R *
        ⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩) := by
      convert hreg2 using 1
      rw [hT, S.polyE_mul]; ring
    have hreg4 : S.RegularFinite K (S.polyE S0 *
        ⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩) := by
      rcases hRS with h | h
      · exact S.regularFinite_dropX b hx hK (w i) (hwB.1 i) R S0 h hreg3
      · rw [← h]; exact hreg3
    obtain ⟨c, hc⟩ := hwB.2.1 _ hreg4
    exact ⟨c, by rw [← hc]; ring⟩
  choose P hP using hcoord
  -- normality at infinity: the rescaled matrix is bounded
  have hdeg : ∀ i j, (pqE b r P S0 i j).natDegree ≤ (X ^ r i * S0).natDegree := by
    intro i
    have hwt0 : S.InfOrd K (S.wTil w r i) 0 := S.infOrd_wTil w r i (hrw i)
    have hu := S.infOrd_derivE b hx hK (S.wTil w r i) 0 hwt0
    have hq : (X ^ r i * S0 : C[X]) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
    have hid := S.deriv_wTilE b hx w r S0 P hP i
    refine S.reduced_normal (K := K) w r hrw hredw _ hu (fun j ↦ pqE b r P S0 i j)
      (X ^ r i * S0) hq ?_
    have hqL : aeval S.x (X ^ r i * S0) ≠ 0 := fun h ↦ hq ((transcendental_iff.mp S.htr) _ h)
    apply Subtype.ext
    have e : ((∑ j, S.polyE (pqE b r P S0 i j) * (S.polyE (X ^ r i * S0))⁻¹ *
        ((S.polyE (X ^ r j))⁻¹ * w j) : C⟮S.x⟯⟮S.y⟯) : L) =
        (∑ j, aeval S.x (pqE b r P S0 i j) * (S.wTil w r j : L)) / aeval S.x (X ^ r i * S0) := by
      rw [Finset.sum_div]
      push_cast
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [polyE, wTil]
      push_cast
      ring
    rw [e, eq_div_iff hqL]
    exact hid
  refine ⟨w, r, S0, P, hwB, hrw, hredw, ?_, hS00, hsq0,
    fun h0' ↦ hS0X (Polynomial.X_dvd_iff.mpr h0'), hP, hdeg⟩
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

end SplitGaugeE

end CurveData

end Curves
