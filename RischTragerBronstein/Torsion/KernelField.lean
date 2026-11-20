import RischTragerBronstein.Torsion.MatJet

/-!
# The residue-field steps of the kernel argument (general curves, basis coordinates)

A function is given by its coordinates `c : Fin n → k[X]` in a basis whose (scaled) numerators are
`B : Fin n → k[X][X]`; `Ψ(c) = ∑ⱼ cⱼ(x) Bⱼ(x, Y)`. The pole order bound is `deg cⱼ + δⱼ ≤ M`
(`δ₀ = 0`, `δⱼ ≥ 1` otherwise). The base points are `g` split fibres `x = xᵢ` with jets `V i k`
through the `n` points of each fibre, at which the matrix of basis values is invertible.

* `structure_modG`: if `Ψ(c)` (with `M = ℓ g`) vanishes to order `ℓ` at all fibre points, then
  `cⱼ = 0` for `j ≠ 0` and `c₀ = a · uˡ`, `u = ∏ (x − xᵢ)`;
* `tangentG`: the first-order terms at the base points vanish, under the non-speciality
  hypothesis `hNS` (functions with `M = g` vanishing on the other fibre points vanish at `Pᵢ`).
-/

open Polynomial Sup

namespace GTors

section Ring

variable {R : Type*} [CommRing R]

/-- The polynomial `∑ⱼ cⱼ(x) Bⱼ(x, Y)`. -/
noncomputable def PsiC {n : ℕ} (B : Fin n → R[X][X]) (c : Fin n → R[X]) : R[X][X] :=
  ∑ j, Polynomial.C (c j) * B j

lemma PsiC_C_mul {n : ℕ} (B : Fin n → R[X][X]) (P : R[X]) (q : Fin n → R[X]) :
    PsiC B (fun j ↦ P * q j) = Polynomial.C P * PsiC B q := by
  simp only [PsiC, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

lemma PsiC_add {n : ℕ} (B : Fin n → R[X][X]) (c c' : Fin n → R[X]) :
    PsiC B (fun j ↦ c j + c' j) = PsiC B c + PsiC B c' := by
  simp only [PsiC, map_add, add_mul, Finset.sum_add_distrib]

lemma PsiC_map {S : Type*} [CommRing S] (φ : R →+* S) {n : ℕ} (B : Fin n → R[X][X])
    (c : Fin n → R[X]) :
    (PsiC B c).map (mapRingHom φ) = PsiC (fun j ↦ (B j).map (mapRingHom φ)) fun j ↦ (c j).map φ := by
  simp [PsiC, Polynomial.map_sum, Polynomial.map_mul]

end Ring

section Field

variable {k : Type*} [Field k]

/-- **Structure over the residue field.** -/
theorem structure_modG {n g ℓ : ℕ} (B : Fin n → k[X][X]) (δ : Fin n → ℕ) (hn : 0 < n)
    (hδ : ∀ j : Fin n, (j : ℕ) ≠ 0 → 1 ≤ δ j) (x : Fin g → k) (hx : Function.Injective x)
    (V : Fin g → Fin n → k[X])
    (hdet : ∀ i, IsUnit (Matrix.det (Matrix.of fun kk j ↦ evalW (B j) (x i) ((V i kk).coeff 0))))
    (c : Fin n → k[X]) (hdeg : ∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ ℓ * g)
    (hv : ∀ i kk, X ^ ℓ ∣ jetN (PsiC B c) (x i) (V i kk)) :
    (∀ j : Fin n, (j : ℕ) ≠ 0 → c j = 0) ∧ ∃ a : k, c ⟨0, hn⟩ = C a * (∏ i, (X - C (x i))) ^ ℓ := by
  have hdv : ∀ j i, (X - C (x i)) ^ ℓ ∣ c j := fun j i ↦
    coords_dvd_of_vanish c B (x i) (V i) ℓ (hdet i) (hv i) j
  have hU := fun j ↦ Jac.prod_pow_dvd hx ℓ (hdv j)
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · by_contra h0
    have h1 := natDegree_le_of_dvd (hU j) h0
    rw [Jac.natDegree_prod_pow] at h1
    have h2 := hdeg j h0
    have h3 := hδ j hj
    nlinarith
  · obtain ⟨q, hq⟩ := hU ⟨0, hn⟩
    by_cases hq0 : q = 0
    · exact ⟨0, by rw [hq, hq0]; simp⟩
    have hU0 : (∏ i, (X - C (x i))) ^ ℓ ≠ 0 :=
      ((monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)).pow _).ne_zero
    have hc0 : c ⟨0, hn⟩ ≠ 0 := by rw [hq]; exact mul_ne_zero hU0 hq0
    have hdeg0 : q.natDegree = 0 := by
      have := congrArg natDegree hq
      rw [natDegree_mul hU0 hq0, Jac.natDegree_prod_pow] at this
      have h2 := hdeg _ hc0
      rw [this] at h2
      nlinarith
    refine ⟨q.coeff 0, ?_⟩
    rw [hq, mul_comm]; congr 1; exact eq_C_of_natDegree_eq_zero hdeg0

/-- **The tangent step over the residue field.** -/
theorem tangentG {n g m : ℕ} (B : Fin n → k[X][X]) (δ : Fin n → ℕ) (hn : 0 < n)
    (x : Fin g → k) (hx : Function.Injective x) (V : Fin g → Fin n → k[X])
    (hdet : ∀ i, IsUnit (Matrix.det (Matrix.of fun kk j ↦ evalW (B j) (x i) ((V i kk).coeff 0))))
    (c : Fin n → k[X]) (hdeg : ∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ (m + 1) * g)
    (lam : Fin g → k)
    (h0 : ∀ i, X ^ (m + 1) ∣ jetN (PsiC B c) (x i) (V i ⟨0, hn⟩) - C (lam i) * X ^ m)
    (hk : ∀ i (kk : Fin n), (kk : ℕ) ≠ 0 → X ^ (m + 1) ∣ jetN (PsiC B c) (x i) (V i kk))
    (hNS : ∀ q : Fin n → k[X], (∀ j, q j ≠ 0 → (q j).natDegree + δ j ≤ g) →
      (∀ i (kk : Fin n), (kk : ℕ) ≠ 0 → evalW (PsiC B q) (x i) ((V i kk).coeff 0) = 0) →
      ∀ i, evalW (PsiC B q) (x i) ((V i ⟨0, hn⟩).coeff 0) = 0) :
    ∀ i, lam i = 0 := by
  classical
  set u : k[X] := ∏ j, (X - C (x j)) with hu
  have hXm : (X : k[X]) ^ m ∣ X ^ (m + 1) := pow_dvd_pow X (Nat.le_succ m)
  -- vanishing to order `m` at every fibre point
  have hvm : ∀ i kk, X ^ m ∣ jetN (PsiC B c) (x i) (V i kk) := by
    intro i kk
    by_cases hkk : (kk : ℕ) = 0
    · have e : kk = ⟨0, hn⟩ := Fin.ext hkk
      subst e
      have := dvd_add (hXm.trans (h0 i)) (dvd_mul_left (X ^ m) (C (lam i)))
      rwa [sub_add_cancel] at this
    · exact hXm.trans (hk i kk hkk)
  have hdv : ∀ j i, (X - C (x i)) ^ m ∣ c j := fun j i ↦
    coords_dvd_of_vanish c B (x i) (V i) m (hdet i) (hvm i) j
  have hU : ∀ j, u ^ m ∣ c j := fun j ↦ Jac.prod_pow_dvd hx m (hdv j)
  choose q hq using hU
  have hu0 : u ^ m ≠ 0 := ((monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)).pow _).ne_zero
  have hcq : c = fun j ↦ u ^ m * q j := funext hq
  have hqdeg : ∀ j, q j ≠ 0 → (q j).natDegree + δ j ≤ g := by
    intro j hj
    have hcj : c j ≠ 0 := by rw [hq]; exact mul_ne_zero hu0 hj
    have h1 := hdeg j hcj
    rw [hq, natDegree_mul hu0 hj, Jac.natDegree_prod_pow] at h1
    nlinarith
  set G : Fin g → k[X] := fun i ↦ ∏ j ∈ Finset.univ.erase i, (X + C (x i - x j)) with hG
  have hG0 : ∀ i, IsUnit ((G i ^ m).coeff 0) := fun i ↦ by
    rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, coeff_zero_prod_erase]
    refine Ne.isUnit (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_))
    exact sub_ne_zero.mpr fun h ↦ (Finset.ne_of_mem_erase hj) (hx h).symm
  have hjet : ∀ i W, jetN (PsiC B c) (x i) W = X ^ m * (G i ^ m * jetN (PsiC B q) (x i) W) := by
    intro i W
    rw [hcq, PsiC_C_mul, jetN_C_poly_mul, pow_comp, u_comp_self]
    simp only [hG]; ring
  have hcancel : ∀ P : k[X], X ^ (m + 1) ∣ X ^ m * P → X ∣ P := fun P h ↦ by
    rw [pow_succ] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero m X_ne_zero)).mp h
  -- `Ψ(q)` vanishes at the other fibre points, hence at the base points
  have hconj : ∀ i (kk : Fin n), (kk : ℕ) ≠ 0 →
      evalW (PsiC B q) (x i) ((V i kk).coeff 0) = 0 := by
    intro i kk hkk
    have h1 := hcancel _ (by rw [← hjet]; exact hk i kk hkk)
    have h2 := Jac.X_pow_dvd_of_mul (hG0 i) (by rwa [pow_one])
    rw [pow_one, X_dvd_iff, jetN_coeff_zero] at h2
    exact h2
  have hval := hNS q hqdeg hconj
  intro i
  have h1 := hcancel _ (by
    have := h0 i
    rw [hjet] at this
    rwa [show X ^ m * (G i ^ m * jetN (PsiC B q) (x i) (V i ⟨0, hn⟩)) - C (lam i) * X ^ m =
      X ^ m * (G i ^ m * jetN (PsiC B q) (x i) (V i ⟨0, hn⟩) - C (lam i)) by ring] at this)
  rw [X_dvd_iff, coeff_sub, coeff_C_zero, mul_coeff_zero, jetN_coeff_zero, hval i, mul_zero,
    zero_sub, neg_eq_zero] at h1
  exact h1

end Field

end GTors
