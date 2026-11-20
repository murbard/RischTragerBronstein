import RischTragerBronstein.Computable.SysDen

/-!
# The norm test for a common factor

For monic `q ∈ K[t]` of degree `m` and `P ∈ K[t]`, the multiplication matrix `multMat q P` of
`w ↦ P w mod q` on the basis `1, t, …, t^{m−1}` of `K[t]/(q)`. If `P` and `q` have a common
irreducible factor `p`, then `P (q/p) ≡ 0 mod q` with `q/p ≠ 0` of degree `< m`, so
`det (multMat q P) = 0` (`det_multMat_eq_zero`). This turns the indicial condition "some prime
factor of `q` divides `det(A₀ − e q′ I)`" into the vanishing of a polynomial in `e`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K]

/-- The multiplication matrix of `P` on `K[t]/(q)`, basis `tʲ`, `j < deg q`. -/
noncomputable def multMat (q P : K[X]) : Matrix (Fin q.natDegree) (Fin q.natDegree) K :=
  Matrix.of fun i j ↦ ((P * X ^ (j : ℕ)) %ₘ q).coeff i

/-- The coefficient vector of `w` (degree `< deg q`). -/
noncomputable def coeffVec (q w : K[X]) : Fin q.natDegree → K := fun i ↦ w.coeff i

/-- Reduction mod a monic polynomial, as an additive map. -/
noncomputable def modHom (q : K[X]) : K[X] →+ K[X] :=
  AddMonoidHom.mk' (fun p ↦ p %ₘ q) (fun p₁ p₂ ↦ add_modByMonic p₁ p₂)

lemma multMat_mulVec (q P w : K[X]) (hw : w.natDegree < q.natDegree) :
    (multMat q P).mulVec (coeffVec q w) = coeffVec q ((P * w) %ₘ q) := by
  funext i
  have hw' : w = ∑ j : Fin q.natDegree, C (w.coeff j) * X ^ (j : ℕ) := by
    conv_lhs => rw [as_sum_range' w q.natDegree hw]
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ monomial j (w.coeff j))]
    simp [C_mul_X_pow_eq_monomial]
  simp only [Matrix.mulVec, dotProduct, multMat, Matrix.of_apply, coeffVec]
  have e : (P * w) %ₘ q = ∑ j : Fin q.natDegree, C (w.coeff j) * ((P * X ^ (j : ℕ)) %ₘ q) := by
    conv_lhs => rw [hw', Finset.mul_sum]
    change modHom q _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    change (P * (C (w.coeff j) * X ^ (j : ℕ))) %ₘ q = _
    rw [show P * (C (w.coeff j) * X ^ (j : ℕ)) = w.coeff j • (P * X ^ (j : ℕ)) by
      rw [smul_eq_C_mul]; ring, smul_modByMonic, smul_eq_C_mul]
  rw [e, finset_sum_coeff]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [coeff_C_mul, mul_comm]

/-- **A common factor forces the norm to vanish.** -/
theorem det_multMat_eq_zero (q P p : K[X]) (hq : q.Monic) (hp : Irreducible p) (hpq : p ∣ q)
    (hpP : p ∣ P) : (multMat q P).det = 0 := by
  classical
  obtain ⟨r, hr⟩ := hpq
  have hq0 : q ≠ 0 := hq.ne_zero
  have hr0 : r ≠ 0 := fun h ↦ hq0 (by rw [hr, h, mul_zero])
  have hrdeg : r.natDegree < q.natDegree := by
    rw [hr, natDegree_mul hp.ne_zero hr0]
    have := Irreducible.natDegree_pos hp
    omega
  refine (Matrix.exists_mulVec_eq_zero_iff).mp ⟨coeffVec q r, fun h ↦ ?_, ?_⟩
  · apply hr0
    ext i
    by_cases hi : i < q.natDegree
    · have := congrFun h ⟨i, hi⟩
      simpa [coeffVec] using this
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; rfl
  · rw [multMat_mulVec q P r hrdeg]
    have : (P * r) %ₘ q = 0 := by
      rw [modByMonic_eq_zero_iff_dvd hq, hr]
      obtain ⟨s, hs⟩ := hpP
      exact ⟨s, by rw [hs]; ring⟩
    funext i
    simp [coeffVec, this]

/-- **A kernel modulo `p` forces `p ∣ det`.** -/
theorem det_dvd_of_ker {n : ℕ} (p : K[X]) (hp : Irreducible p) (Z : Fin n → K[X]) (hZ : ∃ i, ¬ p ∣ Z i)
    (Mt : Matrix (Fin n) (Fin n) K[X]) (hker : ∀ i, p ∣ ∑ j, Mt i j * Z j) : p ∣ Mt.det := by
  classical
  haveI := Fact.mk hp
  set φ : K[X] →+* AdjoinRoot p := AdjoinRoot.mk p with hφ
  set z : Fin n → AdjoinRoot p := fun i ↦ φ (Z i) with hz
  have hz0 : z ≠ 0 := by
    obtain ⟨i, hi⟩ := hZ
    intro h
    apply hi
    have := congrFun h i
    simpa [hz, hφ, AdjoinRoot.mk_eq_zero] using this
  have hk : (Mt.map φ).mulVec z = 0 := by
    funext i
    have h := hker i
    rw [← AdjoinRoot.mk_eq_zero] at h
    simp only [map_sum, map_mul] at h
    simpa [Matrix.mulVec, dotProduct, hz] using h
  have hdet : (Mt.map φ).det = 0 := (Matrix.exists_mulVec_eq_zero_iff).mp ⟨z, hz0, hk⟩
  rw [show (Mt.map φ).det = φ Mt.det from (RingHom.map_det φ Mt).symm] at hdet
  exact AdjoinRoot.mk_eq_zero.mp hdet

/-- **The local denominator bound at a factor `p` of `q`** (in terms of the whole `q = p r`):
if `r p D(Z) − e r D(p) Z + A₀ Z ≡ 0 (mod p)` with `p ∤ Z`, then `p ∣ det(A₀ − e D(q) I)`, hence
`e` is a root of the indicial norm of `(q, D(q), A₀)`. -/
theorem den_local {n : ℕ} (p r : K[X]) (hp : Irreducible p) (D : K[X] → K[X])
    (hDq : D (p * r) = D p * r + p * D r) (Z : Fin n → K[X]) (hZ : ∃ i, ¬ p ∣ Z i) (e : ℕ)
    (A0 : Matrix (Fin n) (Fin n) K[X])
    (hdiv : ∀ i, p ∣ r * p * D (Z i) - (e : K[X]) * r * D p * Z i + ∑ j, A0 i j * Z j) :
    p ∣ (Matrix.of fun i j ↦ A0 i j - if i = j then C (e : K) * D (p * r) else 0).det := by
  classical
  refine det_dvd_of_ker p hp Z hZ _ fun i ↦ ?_
  have h := hdiv i
  have e1 : ∑ j, (Matrix.of fun i j ↦ A0 i j - if i = j then C (e : K) * D (p * r) else 0) i j * Z j =
      (r * p * D (Z i) - (e : K[X]) * r * D p * Z i + ∑ j, A0 i j * Z j) -
        p * (r * D (Z i) + (e : K[X]) * D r * Z i) := by
    simp only [Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hDq, map_natCast]
    ring
  rw [e1]
  exact dvd_sub h (dvd_mul_right _ _)

/-! ### The symbolic norm in `e` -/

section Symbolic

variable {n : ℕ}

/-- The multiplication matrix with an explicit size. -/
noncomputable def multMatN {R : Type*} [CommRing R] (m : ℕ) (q P : R[X]) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j ↦ ((P * X ^ (j : ℕ)) %ₘ q).coeff i

lemma multMatN_eq (q P : K[X]) : multMatN q.natDegree q P = multMat q P := rfl

lemma multMatN_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) (q P : R[X])
    (hq : q.Monic) : (multMatN m q P).map φ = multMatN m (q.map φ) (P.map φ) := by
  ext i j
  simp only [Matrix.map_apply, multMatN, Matrix.of_apply, ← coeff_map]
  rw [map_modByMonic φ hq, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]

/-- The indicial matrix `A₀ − E dq I` (`dq` the tower derivative of `q`) over `K[E][t]` (`E` the inner variable). -/
noncomputable def indMat (dq : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) : Matrix (Fin n) (Fin n) K[X][X] :=
  Matrix.of fun i j ↦ (A0 i j).map C - if i = j then C X * dq.map C else 0

/-- **The indicial norm** `ρ(E) = N_{K[t]/(q)}(det(A₀ − E q′ I))`. -/
noncomputable def indNorm (q dq : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) : K[X] :=
  (multMatN q.natDegree (q.map C) (indMat dq A0).det).det

lemma indMat_eval (dq : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) (e : K) :
    (indMat dq A0).map (mapRingHom (evalRingHom e)) =
      Matrix.of fun i j ↦ A0 i j - if i = j then C e * dq else 0 := by
  have hid : (evalRingHom e).comp C = RingHom.id K := RingHom.ext fun a ↦ by simp
  refine Matrix.ext fun i j ↦ ?_
  simp only [Matrix.map_apply, indMat, Matrix.of_apply, coe_mapRingHom]
  rw [Polynomial.map_sub, Polynomial.map_map, hid, Polynomial.map_id]
  split_ifs
  · rw [Polynomial.map_mul, Polynomial.map_map, hid, Polynomial.map_id, Polynomial.map_C,
      coe_evalRingHom, eval_X]
  · simp

/-- **Every indicial root is a root of the indicial norm.** -/
theorem indNorm_eval_eq_zero (q dq : K[X]) (hq : q.Monic) (A0 : Matrix (Fin n) (Fin n) K[X]) (e : K)
    (p : K[X]) (hp : Irreducible p) (hpq : p ∣ q)
    (hdet : p ∣ (Matrix.of fun i j ↦ A0 i j - if i = j then C e * dq else 0).det) :
    (indNorm q dq A0).eval e = 0 := by
  have hqC : (q.map C).Monic := hq.map _
  rw [indNorm, ← coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply, multMatN_map _ _ _ _ hqC,
    Polynomial.map_map,
    show (evalRingHom e).comp C = RingHom.id K from RingHom.ext fun a ↦ by simp, Polynomial.map_id,
    ← coe_mapRingHom, RingHom.map_det, RingHom.mapMatrix_apply, indMat_eval, multMatN_eq]
  exact det_multMat_eq_zero q _ p hq hp hpq hdet

end Symbolic

/-! ### The norm with `E` as the outer variable -/

section Outer

/-- **Degree of a determinant** of a polynomial matrix with entries of degree `≤ d`. -/
theorem natDegree_det_le_of {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R[X]) (d : ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ d) : M.det.natDegree ≤ Fintype.card ι * d := by
  rw [Matrix.det_apply]
  refine (natDegree_sum_le_of_forall_le _ _ fun σ _ ↦ ?_)
  rw [Units.smul_def]
  refine (natDegree_smul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i, (M (σ i) i).natDegree ≤ ∑ _i : ι, d := Finset.sum_le_sum fun i _ ↦ h _ _
    _ = Fintype.card ι * d := by simp

variable {n : ℕ}

/-- The indicial polynomial `P(E) = det(A₀ − E dq I)` with `E` outer (coefficients in `K[t]`). -/
noncomputable def indPoly (dq : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) : K[X][X] :=
  (Matrix.of fun i j ↦ C (A0 i j) - if i = j then X * C dq else 0).det

lemma indPoly_eval (dq : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) (e : K) :
    (indPoly dq A0).eval (C e) =
      (Matrix.of fun i j ↦ A0 i j - if i = j then C e * dq else 0).det := by
  rw [indPoly, ← coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, coe_evalRingHom]
  split_ifs <;> simp <;> ring

lemma natDegree_indPoly (dq : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) :
    (indPoly dq A0).natDegree ≤ n := by
  have := natDegree_det_le_of ((Matrix.of fun i j ↦ C (A0 i j) - if i = j then X * C dq else 0 :
      Matrix (Fin n) (Fin n) K[X][X])) 1
    (fun i j ↦ by
      simp only [Matrix.of_apply]
      split_ifs
      · exact (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_mul_C_le _ _).trans natDegree_X_le))
      · simp)
  unfold indPoly
  simpa using this

/-- **The indicial norm** `ρ(E) = det (∑ₖ Eᵏ multMat(q, aₖ))`, `P(E) = ∑ₖ Eᵏ aₖ`. -/
noncomputable def indNorm' (q dq : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) : K[X] :=
  (Matrix.of fun i j ↦ ∑ k ∈ Finset.range (n + 1),
    C ((multMat q ((indPoly dq A0).coeff k)) i j) * X ^ k).det

lemma natDegree_indNorm' (q dq : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) :
    (indNorm' q dq A0).natDegree ≤ q.natDegree * n := by
  have := natDegree_det_le_of (Matrix.of fun i j ↦ ∑ k ∈ Finset.range (n + 1),
    C ((multMat q ((indPoly dq A0).coeff k)) i j) * X ^ k) n (fun i j ↦ by
      simp only [Matrix.of_apply]
      refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
      refine (natDegree_C_mul_X_pow_le _ _).trans ?_
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  unfold indNorm'
  simpa using this

/-- `multMat` is additive and `K`-linear in `P`. -/
lemma multMat_sum (q : K[X]) (N : ℕ) (a : ℕ → K) (P : ℕ → K[X]) :
    multMat q (∑ k ∈ Finset.range N, C (a k) * P k) =
      ∑ k ∈ Finset.range N, a k • multMat q (P k) := by
  ext i j
  simp only [multMat, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  have e : (∑ k ∈ Finset.range N, C (a k) * P k * X ^ (j : ℕ)) %ₘ q =
      ∑ k ∈ Finset.range N, C (a k) * ((P k * X ^ (j : ℕ)) %ₘ q) := by
    change modHom q _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    change ((C (a k) * P k * X ^ (j : ℕ)) %ₘ q) = C (a k) * ((P k * X ^ (j : ℕ)) %ₘ q)
    rw [show C (a k) * P k * X ^ (j : ℕ) = a k • (P k * X ^ (j : ℕ)) by rw [smul_eq_C_mul]; ring,
      smul_modByMonic, smul_eq_C_mul]
  rw [e, finset_sum_coeff]
  simp only [coeff_C_mul]

/-- **Evaluation of the norm**: `ρ(e) = det multMat(q, det(A₀ − e dq I))`. -/
lemma indNorm'_eval (q dq : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) (e : K) :
    (indNorm' q dq A0).eval e =
      (multMat q (Matrix.of fun i j ↦ A0 i j - if i = j then C e * dq else 0).det).det := by
  rw [indNorm', ← coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply, ← indPoly_eval]
  congr 1
  have hP : (indPoly dq A0).eval (C e) = ∑ k ∈ Finset.range (n + 1),
      C (e ^ k) * (indPoly dq A0).coeff k := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_indPoly dq A0))]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [C_pow]; ring
  rw [hP, multMat_sum]
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, coe_evalRingHom, eval_finset_sum, eval_mul, eval_C,
    eval_pow, eval_X, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- **Every indicial root is a root of the norm.** -/
theorem indNorm'_eval_eq_zero (q dq : K[X]) (hq : q.Monic) (A0 : Matrix (Fin n) (Fin n) K[X])
    (e : K) (p : K[X]) (hp : Irreducible p) (hpq : p ∣ q)
    (hdet : p ∣ (Matrix.of fun i j ↦ A0 i j - if i = j then C e * dq else 0).det) :
    (indNorm' q dq A0).eval e = 0 := by
  rw [indNorm'_eval]
  exact det_multMat_eq_zero q _ p hq hp hpq hdet

end Outer

/-! ### Interpolation at `0, …, N` -/

section Interp

/-- The Lagrange basis polynomial `ℓₖ = ∏_{i ≠ k} (X − i)/(k − i)` at the nodes `0, …, N`. -/
def lagrangeL (N k : ℕ) : CPoly ℚ :=
  ((List.range (N + 1)).filter (· != k)).foldr
    (fun i acc ↦ CPoly.mul [-(i : ℚ) / ((k : ℚ) - i), 1 / ((k : ℚ) - i)] acc) [1]

/-- **The check** `∑ₖ (ℓₖ)ⱼ kˡ = δⱼₗ` for `j, l ≤ N`. -/
def vandCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun j ↦ (List.range (N + 1)).all fun l ↦
    decide (∑ k ∈ Finset.range (N + 1), (lagrangeL N k).getD j 0 * ((k : ℚ) ^ l) =
      if j = l then 1 else 0)

/-- **Interpolation**: a polynomial of degree `≤ N` is recovered from its values at `0, …, N`. -/
theorem coeff_eq_interp {R : Type*} [Field R] [CharZero R] (N : ℕ) (hc : vandCheck N = true)
    (ρ : R[X]) (hρ : ρ.natDegree ≤ N) (j : ℕ) (hj : j ≤ N) :
    ρ.coeff j = ∑ k ∈ Finset.range (N + 1), (((lagrangeL N k).getD j 0 : ℚ) : R) * ρ.eval (k : R) := by
  have hev : ∀ k : ℕ, ρ.eval (k : R) = ∑ l ∈ Finset.range (N + 1), ρ.coeff l * (k : R) ^ l :=
    fun k ↦ eval_eq_sum_range' (Nat.lt_succ_of_le hρ) _
  simp only [hev, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hcheck : ∀ l ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      (((lagrangeL N k).getD j 0 : ℚ) : R) * (ρ.coeff l * (k : R) ^ l) =
      ρ.coeff l * ((if j = l then 1 else 0 : ℚ) : R) := by
    intro l hl
    have h := List.all_eq_true.mp (List.all_eq_true.mp hc j (List.mem_range.mpr (by omega))) l
      (List.mem_range.mpr (Finset.mem_range.mp hl))
    rw [decide_eq_true_eq] at h
    rw [← h]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [Finset.sum_congr rfl hcheck]
  rw [Finset.sum_eq_single j (fun l _ hl ↦ by rw [if_neg (Ne.symm hl)]; simp)
    (fun h ↦ absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) h)]
  simp

end Interp

end Tower.Sys
