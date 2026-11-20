import RischTragerBronstein.Torsion.IntBasisCheck
import RischTragerBronstein.Algebraic.SupLogSem

/-!
# Certificates for a good prime

* `nsCheck`: the non-speciality condition `hNS` at the base points, by a linear-dependence
  certificate `λ` (each row at `(xᵢ, y_{i0})` is a combination of the rows at the other points);
* `detCheck`: the matrices `[Bⱼ(xᵢ, y_{ik})]` are invertible (left inverses);
* `cover_red`: the cover polynomial `disc · D · ∏ⱼ Bⱼ,ⱼ` reduces modulo `p` to the one of the
  reduced data.
-/

open Polynomial

namespace Curves

open CPoly Sup GTors

section NS

variable {F : Type*} [Field F] [DecidableEq F]

/-- The row entry `xᵢᵈ Bⱼ(xᵢ, y_{ik})`. -/
def nsRow (Bc : List (BPoly F)) (xs : List F) (ys : List (List F)) (i k j d : ℕ) : F :=
  xs.getD i 0 ^ d * evalB (Bc.getD j []) (xs.getD i 0) ((ys.getD i []).getD k 0)

/-- **The non-speciality check.** -/
def nsCheck (n g : ℕ) (δL : List ℕ) (Bc : List (BPoly F)) (xs : List F) (ys : List (List F))
    (lam : List (List F)) : Bool :=
  (List.range g).all fun i0 ↦ (List.range n).all fun j ↦ (List.range (g + 1)).all fun d ↦
    !decide (d + δL.getD j 0 ≤ g) ||
    decide (nsRow Bc xs ys i0 0 j d = ∑ i ∈ Finset.range g, ∑ k ∈ Finset.range n,
      (if k = 0 then 0 else (lam.getD i0 []).getD (i * n + k) 0) * nsRow Bc xs ys i k j d)

variable {K : Type*} [Field K] (ψ : F →+* K)

lemma evalW_PsiC_rows {n g : ℕ} (δL : List ℕ) (Bc : List (BPoly F)) (xs : List F)
    (ys : List (List F)) (q : Fin n → K[X]) (hq : ∀ j, (q j).natDegree ≤ g) (i k : ℕ) :
    evalW (PsiC (fun j : Fin n ↦ (toB (Bc.getD j [])).map (mapRingHom ψ)) q) (ψ (xs.getD i 0))
      (ψ ((ys.getD i []).getD k 0)) =
      ∑ j : Fin n, ∑ d ∈ Finset.range (g + 1), (q j).coeff d * ψ (nsRow Bc xs ys i k j d) := by
  rw [evalW_PsiC]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [evalW_mapG, ← evalB_eq, eval_eq_sum_range' (n := g + 1) (by have := hq j; omega),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [nsRow, map_mul, map_pow]
  ring

/-- **Non-speciality from the certificate.** -/
theorem nsCheck_spec {n g : ℕ} {δL : List ℕ} {Bc : List (BPoly F)} {xs : List F}
    {ys : List (List F)} {lam : List (List F)} (h : nsCheck n g δL Bc xs ys lam = true)
    (q : Fin n → K[X]) (hq : ∀ j, q j ≠ 0 → (q j).natDegree + δL.getD j 0 ≤ g)
    (hv : ∀ (i : Fin g) (k : Fin n), (k : ℕ) ≠ 0 →
      evalW (PsiC (fun j : Fin n ↦ (toB (Bc.getD j [])).map (mapRingHom ψ)) q)
        (ψ (xs.getD i 0)) (ψ ((ys.getD i []).getD k 0)) = 0) (i0 : Fin g) :
    evalW (PsiC (fun j : Fin n ↦ (toB (Bc.getD j [])).map (mapRingHom ψ)) q)
      (ψ (xs.getD i0 0)) (ψ ((ys.getD i0 []).getD 0 0)) = 0 := by
  classical
  simp only [nsCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  have hdeg : ∀ j, (q j).natDegree ≤ g := fun j ↦ by
    by_cases h0 : q j = 0
    · rw [h0, natDegree_zero]; exact Nat.zero_le _
    · have := hq j h0; omega
  have hvan : ∀ (j : Fin n) d, g < d + δL.getD j 0 → (q j).coeff d = 0 := fun j d hd ↦ by
    by_cases h0 : q j = 0
    · rw [h0, Polynomial.coeff_zero]
    · exact coeff_eq_zero_of_natDegree_lt (by have := hq j h0; omega)
  set lamF : ℕ → ℕ → K := fun i k ↦
    ψ (if k = 0 then 0 else (lam.getD i0 []).getD (i * n + k) 0) with hlamF
  have hrow : ∀ (j : Fin n) d, d ∈ Finset.range (g + 1) →
      (q j).coeff d * ψ (nsRow Bc xs ys i0 0 j d) = ∑ i ∈ Finset.range g, ∑ k ∈ Finset.range n,
        lamF i k * ((q j).coeff d * ψ (nsRow Bc xs ys i k j d)) := by
    intro j d hd
    by_cases hv0 : d + δL.getD j 0 ≤ g
    · rcases h i0 i0.2 j j.2 d (Finset.mem_range.mp hd) with h1 | h1
      · exact absurd hv0 h1
      · rw [h1, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [map_mul, hlamF]
        ring
    · rw [hvan j d (by omega), zero_mul]
      simp
  rw [evalW_PsiC_rows ψ δL Bc xs ys q hdeg,
    Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun d hd ↦ hrow j d hd]
  rw [sum_swap2]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [sum_swap2]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  simp_rw [← Finset.mul_sum]
  by_cases hk0 : k = 0
  · rw [hlamF]; simp [hk0]
  · have := hv ⟨i, Finset.mem_range.mp hi⟩ ⟨k, Finset.mem_range.mp hk⟩ hk0
    rw [evalW_PsiC_rows ψ δL Bc xs ys q hdeg] at this
    rw [this, mul_zero]

end NS

section Det

variable {F : Type*} [Field F] [DecidableEq F]

/-- The matrix `[Bⱼ(xᵢ, y_{ik})]_{k, j}` at the base point `i`. -/
def detMat (Bc : List (BPoly F)) (xs : List F) (ys : List (List F)) (i : ℕ) (k j : ℕ) : F :=
  evalB (Bc.getD j []) (xs.getD i 0) ((ys.getD i []).getD k 0)

/-- **The invertibility check** at the `g` base points. -/
def detCheck (n g : ℕ) (Bc : List (BPoly F)) (xs : List F) (ys : List (List F))
    (Ls : List (List (List F))) : Bool :=
  (List.range g).all fun i ↦ leftInvCheck (Ls.getD i []) (detMat Bc xs ys i) n n

lemma detCheck_spec {n g : ℕ} {Bc : List (BPoly F)} {xs : List F} {ys : List (List F)}
    {Ls : List (List (List F))} (h : detCheck n g Bc xs ys Ls = true) (i : ℕ) (hi : i < g) :
    (Matrix.of fun k j : Fin n ↦ detMat Bc xs ys i k j).det ≠ 0 := by
  simp only [detCheck, List.all_eq_true, List.mem_range] at h
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hv0
  refine eq_zero_of_leftInvCheck (RingHom.id F) (h i hi) v fun r hr ↦ ?_
  have := congrFun hv ⟨r, hr⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
  simpa using this

end Det

section Cover

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K]
variable (R : Sup.RedFns p K) (φ : K →+* ℚ_[p]) (hR : Sup.RedValid p R φ)

/-- The reduction of a bivariate list. -/
def redBL (W : BPoly K) : BPoly (ZMod p) := W.map (·.map R.red)

lemma resultant_map_deriv {A B : Type*} [CommRing A] [CommRing B] (h : A →+* B) (P : A[X])
    (m k : ℕ) : h (resultant P (derivative P) m k) =
      resultant (P.map h) (derivative (P.map h)) m k := by
  rw [Polynomial.derivative_map, resultant_map_map]

include φ hR in
/-- **The cover polynomial reduces modulo `p`.** -/
theorem cover_red (Fc : BPoly K) (n : ℕ) (Dc : CPoly K) (Bc : List (BPoly K)) (G : CPoly K)
    (hG : toPoly G = resultant (toB Fc) (derivative (toB Fc)) n (n - 1) * toPoly Dc *
      (Matrix.of fun (i j : Fin n) ↦ (toB (Bc.getD j [])).coeff i).det)
    (hokF : ∀ P ∈ Fc, ∀ c ∈ P, R.ok c = true) (hokD : ∀ c ∈ Dc, R.ok c = true)
    (hokB : ∀ W ∈ Bc, ∀ P ∈ W, ∀ c ∈ P, R.ok c = true) (hokG : ∀ c ∈ G, R.ok c = true) :
    toPoly (G.map R.red) = resultant (toB (redBL R Fc)) (derivative (toB (redBL R Fc))) n (n - 1) *
      toPoly (Dc.map R.red) *
        (Matrix.of fun (i j : Fin n) ↦ (toB ((Bc.map (redBL R)).getD j [])).coeff i).det := by
  classical
  set ι := algebraMap ℤ_[p] ℚ_[p] with hι
  have hιi : Function.Injective ι := IsFractionRing.injective ℤ_[p] ℚ_[p]
  set FO := toB (liftBL R φ hR Fc) with hFO
  set resO := resultant FO (derivative FO) n (n - 1) with hresO
  set DO := toPoly (liftL R φ hR Dc) with hDO
  have hBok : ∀ j : ℕ, ∀ P ∈ Bc.getD j [], ∀ c ∈ P, R.ok c = true := fun j P hP c hc ↦ by
    by_cases hj : j < Bc.length
    · rw [List.getD_eq_getElem _ _ hj] at hP; exact hokB _ (List.getElem_mem hj) P hP c hc
    · rw [List.getD_eq_default _ _ (by omega)] at hP; simp at hP
  set MO : Matrix (Fin n) (Fin n) ℤ_[p][X] :=
    Matrix.of fun i j ↦ (toB (liftBL R φ hR (Bc.getD j []))).coeff i with hMO
  set QO := resO * DO * MO.det with hQO
  have hmapB : ∀ j, (Bc.map (redBL R)).getD j [] = redBL R (Bc.getD j []) := fun j ↦ by
    rw [← List.getD_map (f := redBL R)]; rfl
  have hMι : mapRingHom ι MO.det =
      mapRingHom φ (Matrix.of fun (i j : Fin n) ↦ (toB (Bc.getD j [])).coeff i).det := by
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hMO, Matrix.of_apply]
    rw [← Polynomial.coeff_map, toB_liftBL_map R φ hR _ (hBok j), Polynomial.coeff_map]
  have hMz : mapRingHom PadicInt.toZMod MO.det =
      (Matrix.of fun (i j : Fin n) ↦ (toB ((Bc.map (redBL R)).getD j [])).coeff i).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hMO, Matrix.of_apply]
    rw [← Polynomial.coeff_map, toB_liftBL_red R φ hR _ (hBok j), hmapB]
    rfl
  -- to `ℚ_p`
  have h1 : QO.map ι = (toPoly G).map φ := by
    rw [hG, hQO, ← coe_mapRingHom, ← coe_mapRingHom, map_mul, map_mul, map_mul, map_mul, hMι,
      hresO, resultant_map_deriv, resultant_map_deriv, hFO, coe_mapRingHom, coe_mapRingHom,
      toB_liftBL_map R φ hR Fc hokF, hDO, toPoly_liftL_map R φ hR Dc hokD]
  have h2 : QO = toPoly (liftL R φ hR G) := by
    apply Polynomial.map_injective ι hιi
    rw [h1, toPoly_liftL_map R φ hR G hokG]
  -- to `𝔽_p`
  rw [← toPoly_liftL_red R φ hR G hokG, ← h2, hQO, ← coe_mapRingHom, map_mul, map_mul, hMz,
    hresO, resultant_map_deriv, hFO, coe_mapRingHom, toB_liftBL_red R φ hR Fc hokF, ← coe_mapRingHom,
    hDO, coe_mapRingHom, toPoly_liftL_red R φ hR Dc hokD]
  rfl

end Cover

end Curves
