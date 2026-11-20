import RischTragerBronstein.Weil.Stepanov3
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Stepanov's method for `n`-th powers, step 3: the independence lemma

Over `F = 𝔽_p` with `n ∣ p − 1`, let `f ≠ 0` have an irreducible factor `P` of multiplicity `e`
prime to `n`, and `g = f^c`, `c = (p − 1)/n`. If `∑_{i<n} Aᵢ gⁱ = 0` with
`Aᵢ = ∑_{j<J} rᵢⱼ X^{jp}` and `n (deg f + deg rᵢⱼ) < p`, then all `rᵢⱼ = 0` (`indepN`).

Proof. Put `Ahᵢ = ∑ⱼ rᵢⱼ Yʲ ∈ F[X][Y]` and the `n × n` matrix
`C m k = (if m ≤ k then f(X) else f(Y)) · Ah_{k − m mod n}`. At `Y = X^p` (where `f(X^p) = f g^n`),
`∑ₖ C m k gᵏ = f gᵐ ∑ᵢ Aᵢ gⁱ = 0`, so `det C(X, X^p) = 0`; the coefficients of `det C` have
`X`-degree `< p`, hence `det C = 0` (base-`p` digits). On the other hand, writing `vᵢ` for the
exponent of `P(X)` in `Ahᵢ`, the exponent of `P(X)` in the term of a permutation `σ` is
`(e n² + ∑ₖ ν_{k − σ k}) / n` with `νᵢ = n vᵢ − e i`; the `νᵢ` are distinct (`gcd(e, n) = 1`), so the
shift by the minimizing `i` is the unique term of least exponent, and `det C ≠ 0` unless all
`Ahᵢ = 0` (`det_ne_zero_of_val`).
-/

open Polynomial

namespace Stepanov

section Val

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A sum with a unique term of least `π`-exponent is non-zero. -/
lemma sum_ne_zero_of_unique_min {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → R) {π : R}
    (hπ : Prime π) {σ₀ : ι} (hσ₀ : σ₀ ∈ s) {V : ℕ} {u : R} (hu : ¬ π ∣ u)
    (h0 : t σ₀ = π ^ V * u) (hrest : ∀ σ ∈ s, σ ≠ σ₀ → π ^ (V + 1) ∣ t σ) : ∑ σ ∈ s, t σ ≠ 0 := by
  intro hsum
  rw [← Finset.add_sum_erase s t hσ₀] at hsum
  have hdvd : π ^ (V + 1) ∣ ∑ σ ∈ s.erase σ₀, t σ :=
    Finset.dvd_sum fun σ hσ ↦ hrest σ (Finset.mem_of_mem_erase hσ) (Finset.ne_of_mem_erase hσ)
  obtain ⟨w, hw⟩ := hdvd
  rw [h0, hw, pow_succ, mul_assoc, ← mul_add] at hsum
  have := (mul_eq_zero.mp hsum).resolve_left (pow_ne_zero V hπ.ne_zero)
  exact hu ⟨-w, by linear_combination this⟩

end Val

section Perm

/-- `∑ₖ (k − σ k mod n) = n · #{k < σ k}`. -/
lemma sum_sub_val {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) :
    ∑ k, ((k - σ k : Fin n) : ℕ) = n * (Finset.univ.filter fun k ↦ k < σ k).card := by
  classical
  have h1 : ∀ k : Fin n, ((k - σ k : Fin n) : ℕ) + (σ k : ℕ) = k + n * (if k < σ k then 1 else 0) := by
    intro k
    split_ifs with h
    · rw [(Fin.coe_sub_iff_lt).mpr h]; have := k.2; have := (σ k).2; omega
    · rw [(Fin.coe_sub_iff_le).mpr (not_lt.mp h)]; have : (σ k : ℕ) ≤ k := not_lt.mp h; omega
  have h2 : ∑ k : Fin n, (((k - σ k : Fin n) : ℕ) + (σ k : ℕ)) =
      ∑ k : Fin n, ((k : ℕ) + n * (if k < σ k then 1 else 0)) :=
    Finset.sum_congr rfl fun k _ ↦ h1 k
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Equiv.sum_comp σ (fun k ↦ (k : ℕ)),
    ← Finset.mul_sum, Finset.sum_boole] at h2
  simp only [Nat.cast_id] at h2
  omega

end Perm

section Det

variable {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R]

open Matrix in
/-- **The determinant is non-zero** by a unique term of least `π`-exponent. -/
theorem det_ne_zero_of_val {n : ℕ} [NeZero n] {π : R} (hπ : Prime π) {e : ℕ} (hen : Nat.Coprime e n)
    {fX fY f' : R} (hfX : fX = π ^ e * f') (hf' : ¬ π ∣ f') (hfY : ¬ π ∣ fY) (Ah : Fin n → R)
    (hAh : ∃ i, Ah i ≠ 0) :
    (Matrix.of fun r k : Fin n ↦ (if r ≤ k then fX else fY) * Ah (k - r)).det ≠ 0 := by
  classical
  -- exponents of `π` in the `Ahᵢ`
  have hdec : ∀ i, Ah i ≠ 0 → ∃ v w, Ah i = π ^ v * w ∧ ¬ π ∣ w := fun i hi ↦ by
    obtain ⟨v, w, hw, he⟩ := WfDvdMonoid.max_power_factor hi hπ.irreducible
    exact ⟨v, w, he, hw⟩
  choose! v w hvw using hdec
  set supp := Finset.univ.filter fun i : Fin n ↦ Ah i ≠ 0 with hsupp
  have hsne : supp.Nonempty := by
    obtain ⟨i, hi⟩ := hAh; exact ⟨i, by simp [hsupp, hi]⟩
  set ν : Fin n → ℤ := fun i ↦ (n : ℤ) * v i - e * (i : ℕ) with hν
  obtain ⟨i₀, hi₀, hmin⟩ := supp.exists_min_image ν hsne
  have hi₀' : Ah i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2
  -- distinct `ν`
  have hdist : ∀ i j : Fin n, ν i = ν j → i = j := by
    intro i j hij
    simp only [hν] at hij
    have h1 : (n : ℤ) ∣ (e : ℤ) * ((i : ℕ) - (j : ℕ) : ℤ) := ⟨v i - v j, by linear_combination -hij⟩
    have h2 : (n : ℤ) ∣ ((i : ℕ) - (j : ℕ) : ℤ) :=
      (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd, Nat.Coprime] using hen.symm)).dvd_of_dvd_mul_left h1
    apply Fin.ext
    have hi := i.2; have hj := j.2
    obtain ⟨t, ht⟩ := h2
    rcases lt_trichotomy t 0 with h | h | h
    · have : (n : ℤ) * t ≤ -n := by nlinarith
      omega
    · subst h; omega
    · have : (n : ℤ) ≤ (n : ℤ) * t := by nlinarith
      omega
  -- the exponent of a term and its `π`-free part
  set a : Equiv.Perm (Fin n) → ℕ := fun σ ↦ ∑ k, ((if σ k ≤ k then e else 0) + v (k - σ k)) with ha
  set u : Equiv.Perm (Fin n) → R := fun σ ↦ ∏ k, ((if σ k ≤ k then f' else fY) * w (k - σ k))
    with hu
  have hterm : ∀ σ : Equiv.Perm (Fin n), (∀ k, Ah (k - σ k) ≠ 0) →
      ∏ k, (if σ k ≤ k then fX else fY) * Ah (k - σ k) = π ^ a σ * u σ ∧ ¬ π ∣ u σ := by
    intro σ hσ
    constructor
    · rw [ha, hu, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [(hvw _ (hσ k)).1, pow_add]
      split_ifs
      · rw [hfX]; ring
      · ring
    · rw [hu, Prime.dvd_finset_prod_iff hπ]
      rintro ⟨k, -, hk⟩
      rcases hπ.dvd_or_dvd hk with h | h
      · split_ifs at h
        · exact hf' h
        · exact hfY h
      · exact (hvw _ (hσ k)).2 h
  -- `n · a σ = e n² + ∑ₖ ν (k − σ k)`
  have hna : ∀ σ : Equiv.Perm (Fin n),
      ((n * a σ : ℕ) : ℤ) = e * n * n + ∑ k, ν (k - σ k) := by
    intro σ
    have hW := sum_sub_val σ
    have hcard : (Finset.univ.filter fun k ↦ σ k ≤ k).card +
        (Finset.univ.filter fun k ↦ k < σ k).card = n := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
        (fun k ↦ σ k ≤ k)
      simp only [not_le, Finset.card_univ, Fintype.card_fin] at this
      exact this
    have hsplit : a σ = e * (Finset.univ.filter fun k ↦ σ k ≤ k).card + ∑ k, v (k - σ k) := by
      show ∑ k, ((if σ k ≤ k then e else 0) + v (k - σ k)) = _
      rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, smul_eq_mul, mul_comm]
    simp only [hν]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    push_cast
    rw [hsplit]
    push_cast
    have hW' : ((∑ k, ((k - σ k : Fin n) : ℕ) : ℕ) : ℤ) =
        n * ((Finset.univ.filter fun k ↦ k < σ k).card : ℤ) := by exact_mod_cast hW
    push_cast at hW'
    rw [hW']
    have hcard' : ((Finset.univ.filter fun k ↦ σ k ≤ k).card : ℤ) =
        n - ((Finset.univ.filter fun k ↦ k < σ k).card : ℤ) := by omega
    rw [hcard']
    ring
  -- the minimal permutation
  set σ₀ : Equiv.Perm (Fin n) := Equiv.subRight i₀ with hσ₀
  have hs₀ : ∀ k, k - σ₀ k = i₀ := fun k ↦ by simp [hσ₀]
  have hσ₀supp : ∀ k, Ah (k - σ₀ k) ≠ 0 := fun k ↦ by rw [hs₀]; exact hi₀'
  obtain ⟨hprod₀, hu₀⟩ := hterm σ₀ hσ₀supp
  have hlt : ∀ σ : Equiv.Perm (Fin n), σ ≠ σ₀ → (∀ k, Ah (k - σ k) ≠ 0) → a σ₀ < a σ := by
    intro σ hne hσ
    have h1 := hna σ
    have h0 := hna σ₀
    simp only [hs₀, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h0
    have hk : ∃ k, k - σ k ≠ i₀ := by
      by_contra hall
      push_neg at hall
      apply hne
      ext k
      have := hall k
      simp only [hσ₀, Equiv.subRight_apply]
      rw [← this]; simp
    obtain ⟨k₀, hk₀⟩ := hk
    have hsum : ∑ k : Fin n, ν i₀ < ∑ k, ν (k - σ k) := by
      refine Finset.sum_lt_sum (fun k _ ↦ hmin _ (by simp [hsupp, hσ k])) ⟨k₀, Finset.mem_univ _, ?_⟩
      exact lt_of_le_of_ne (hmin _ (by simp [hsupp, hσ k₀])) (fun h ↦ hk₀ (hdist _ _ h).symm)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have : ((n * a σ₀ : ℕ) : ℤ) < ((n * a σ : ℕ) : ℤ) := by rw [h0, h1]; linarith
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact Nat.lt_of_mul_lt_mul_left (by exact_mod_cast this)
  -- the determinant
  rw [Matrix.det_apply]
  simp only [Matrix.of_apply]
  have hsign : ∀ (σ : Equiv.Perm (Fin n)) (x : R), ((Equiv.Perm.sign σ) • x) = (Equiv.Perm.sign σ : ℤ) * x :=
    fun σ x ↦ by rw [Units.smul_def, zsmul_eq_mul]
  refine sum_ne_zero_of_unique_min Finset.univ _ hπ (Finset.mem_univ σ₀) (V := a σ₀)
    (u := (Equiv.Perm.sign σ₀ : ℤ) * u σ₀) ?_ ?_ ?_
  · intro hd
    apply hu₀
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ₀) with h | h
    · rw [h] at hd; simpa using hd
    · rw [h] at hd; simpa using (dvd_neg.mp (by simpa using hd))
  · rw [hsign, hprod₀]; ring
  · intro σ _ hne
    rw [hsign]
    by_cases hσ : ∀ k, Ah (k - σ k) ≠ 0
    · obtain ⟨hprod, -⟩ := hterm σ hσ
      rw [hprod]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (pow_dvd_pow π (hlt σ hne hσ)) _) _
    · push_neg at hσ
      obtain ⟨k, hk⟩ := hσ
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, mul_zero]), mul_zero]
      exact dvd_zero _

end Det


section Digits2

variable {R : Type*} [CommRing R]

lemma coeff_prod_natDegree_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (U : ι → R[X][X])
    (a : ι → ℕ) (hU : ∀ i ∈ s, ∀ k, ((U i).coeff k).natDegree ≤ a i) :
    ∀ k, ((∏ i ∈ s, U i).coeff k).natDegree ≤ ∑ i ∈ s, a i := by
  induction s using Finset.induction_on with
  | empty =>
    intro k
    rw [Finset.prod_empty, coeff_one]; split_ifs <;> simp
  | insert j s hj ih =>
    intro k
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact coeff_mul_natDegree_le _ _ _ _ (hU j (Finset.mem_insert_self j s))
      (ih fun i hi ↦ hU i (Finset.mem_insert_of_mem hi)) k

lemma det_coeff_natDegree_le {n : ℕ} (M : Matrix (Fin n) (Fin n) (R[X][X])) (B : ℕ)
    (hM : ∀ r k t, ((M r k).coeff t).natDegree ≤ B) :
    ∀ t, ((M.det).coeff t).natDegree ≤ n * B := by
  classical
  intro t
  rw [Matrix.det_apply, finsetSum_coeff]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ ↦ ?_
  rw [Units.smul_def, zsmul_eq_mul, ← C_eq_intCast, coeff_C_mul]
  refine (natDegree_mul_le).trans ?_
  have h1 : ((((Equiv.Perm.sign σ : ℤ) : R[X])).natDegree) = 0 := natDegree_intCast _
  have h2 := coeff_prod_natDegree_le Finset.univ (fun k ↦ M (σ k) k) (fun _ ↦ B)
    (fun k _ t ↦ hM _ _ t) t
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

end Digits2

variable {p : ℕ} [hp : Fact p.Prime]

local notation "F" => ZMod p

/-- **The independence lemma for `n`-th powers.** -/
theorem indepN (n : ℕ) (hn : 1 ≤ n) (hnp : n ∣ p - 1) (f : F[X]) (hf0 : f ≠ 0) (P : F[X])
    (hP : Irreducible P) (e : ℕ) (hen : Nat.Coprime e n) (hPe : P ^ e ∣ f)
    (hPe1 : ¬ P ^ (e + 1) ∣ f) (J : ℕ) (r : ℕ → ℕ → F[X])
    (hr : ∀ i < n, ∀ j < J, n * (f.natDegree + (r i j).natDegree) < p)
    (h : ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range J, r i j * X ^ (j * p)) *
      f ^ ((p - 1) / n * i) = 0) :
    ∀ i < n, ∀ j < J, r i j = 0 := by
  classical
  have : NeZero n := ⟨by omega⟩
  set c := (p - 1) / n with hc
  have hp1 : n * c + 1 = p := by
    have h1 := hp.out.one_lt
    rw [hc, Nat.mul_div_cancel' hnp]; omega
  set g := f ^ c with hg
  set Ah : Fin n → F[X][X] := fun i ↦ bivOf J (r i) with hAh
  set A : ℕ → F[X] := fun i ↦ ∑ j ∈ Finset.range J, r i j * X ^ (j * p) with hA
  set M : Matrix (Fin n) (Fin n) (F[X][X]) :=
    Matrix.of fun a k ↦ (if a ≤ k then C f else f.map C) * Ah (k - a) with hM
  set φ : F[X][X] →+* F[X] := Polynomial.evalRingHom (X ^ p) with hφ
  have hφA : ∀ i : Fin n, φ (Ah i) = A i := fun i ↦ by simp [hφ, hAh, hA, eval_bivOf]
  have hφf : φ (C f) = f := by simp [hφ]
  have hφfY : φ (f.map C) = f * g ^ n := by
    simp only [hφ, coe_evalRingHom, eval_map]
    rw [← coe_expand, ZMod.expand_card, hg, ← pow_mul, ← pow_succ', mul_comm c n, hp1]
  -- the vector `(gᵏ)` is in the kernel
  have hsumA : ∑ i : Fin n, A i * g ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ A i * g ^ i) n, ← h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hA, hg, ← pow_mul]
  have hker : Matrix.mulVec (M.map φ) (fun k : Fin n ↦ g ^ (k : ℕ)) = 0 := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hM, Matrix.of_apply, map_mul, Pi.zero_apply]
    have hterm : ∀ k : Fin n, φ (if a ≤ k then C f else f.map C) * φ (Ah (k - a)) * g ^ (k : ℕ) =
        f * g ^ (a : ℕ) * (A ((k - a : Fin n) : ℕ) * g ^ ((k - a : Fin n) : ℕ)) := by
      intro k
      rw [hφA]
      split_ifs with hak
      · rw [hφf, (Fin.coe_sub_iff_le).mpr hak]
        have : (k : ℕ) = a + (k - a : ℕ) := by have : (a : ℕ) ≤ k := hak; omega
        rw [this, pow_add]; simp only [Nat.add_sub_cancel_left]; ring
      · rw [hφfY, (Fin.coe_sub_iff_lt).mpr (not_le.mp hak)]
        have hka : (k : ℕ) < a := not_le.mp hak
        have e1 : g ^ (a : ℕ) * g ^ (n + k - a : ℕ) = g ^ n * g ^ (k : ℕ) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        linear_combination (-(f * A (n + (k : ℕ) - a))) * e1
    rw [Finset.sum_congr rfl fun k _ ↦ hterm k, ← Finset.mul_sum]
    rw [Fintype.sum_equiv (Equiv.subRight a) (fun k ↦ A ((k - a : Fin n) : ℕ) * g ^ ((k - a : Fin n) : ℕ))
      (fun i : Fin n ↦ A i * g ^ (i : ℕ)) (fun k ↦ rfl), hsumA, mul_zero]
  have hdetφ : (M.map φ).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, fun h0 ↦ by
      have := congrFun h0 0; simp at this, hker⟩
  replace hdetφ : φ M.det = 0 := by rw [RingHom.map_det]; exact hdetφ
  -- the coefficients have degree `< p`, hence `det M = 0`
  set b := (Finset.range n ×ˢ Finset.range J).sup fun ij ↦ (r ij.1 ij.2).natDegree with hb
  have hrb : ∀ i < n, ∀ j, ((bivOf J (r i)).coeff j).natDegree ≤ b := fun i hi j ↦ by
    rw [coeff_bivOf]; split_ifs with hj
    · exact Finset.le_sup (f := fun ij : ℕ × ℕ ↦ (r ij.1 ij.2).natDegree) (b := (i, j))
        (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩)
    · simp
  have hJ : 0 < J ∨ J = 0 := by omega
  rcases hJ with hJ | hJ
  swap
  · intro i _ j hj; omega
  have hbp : n * (f.natDegree + b) < p := by
    obtain ⟨ij, hij, hijm⟩ := Finset.exists_mem_eq_sup (Finset.range n ×ˢ Finset.range J)
      ⟨(0, 0), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr hJ⟩⟩
      fun ij ↦ (r ij.1 ij.2).natDegree
    rw [hb, hijm]
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hij
    exact hr _ (Finset.mem_range.mp h1) _ (Finset.mem_range.mp h2)
  have hMdeg : ∀ a k t, ((M a k).coeff t).natDegree ≤ f.natDegree + b := by
    intro a k t
    simp only [hM, Matrix.of_apply]
    split_ifs
    · refine coeff_mul_natDegree_le _ _ f.natDegree b (fun t ↦ ?_) (hrb _ (k - a).2) t
      rw [coeff_C]; split_ifs <;> simp
    · refine (coeff_mul_natDegree_le _ _ 0 b (fun t ↦ ?_) (hrb _ (k - a).2) t).trans (by omega)
      rw [coeff_map]; simp
  have hdet0 : M.det = 0 := by
    refine eq_zero_of_eval_X_pow p hp.out.pos _ (fun t ↦ Or.inl ?_) hdetφ
    exact lt_of_le_of_lt (det_coeff_natDegree_le M _ hMdeg t) hbp
  -- the valuation argument
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi, j, hj, hij⟩ := hcon
  have hAhi : Ah ⟨i, hi⟩ ≠ 0 := by
    intro h0
    apply hij
    have := congrArg (fun G : F[X][X] ↦ G.coeff j) h0
    simpa [hAh, coeff_bivOf, hj] using this
  have hPprime : Prime P := hP.prime
  have hπ : Prime (C P : F[X][X]) := prime_C_iff.mpr hPprime
  have hπf : ¬ (C P : F[X][X]) ∣ f.map C := by
    rintro ⟨Q, hQ⟩
    apply hf0
    ext i
    have hc := congrArg (fun G : F[X][X] ↦ G.coeff i) hQ
    simp only [coeff_map, coeff_C_mul] at hc
    have hdvd : P ∣ C (f.coeff i) := ⟨Q.coeff i, hc⟩
    by_contra hne
    have hu' : IsUnit (C (f.coeff i)) := isUnit_C.mpr (Ne.isUnit hne)
    exact hP.not_isUnit (isUnit_of_dvd_unit hdvd hu')
  obtain ⟨f', hf'⟩ := hPe
  have hf'P : ¬ P ∣ f' := by
    rintro ⟨g', rfl⟩; exact hPe1 ⟨g', by rw [hf']; ring⟩
  have hπf' : ¬ (C P : F[X][X]) ∣ C f' := by
    rintro ⟨Q, hQ⟩
    apply hf'P
    have := congrArg (fun G : F[X][X] ↦ G.coeff 0) hQ
    simp only [coeff_C_zero, coeff_C_mul] at this
    exact ⟨Q.coeff 0, this⟩
  exact det_ne_zero_of_val hπ hen (fX := C f) (f' := C f') (by rw [hf', C_mul, C_pow]) hπf' hπf Ah
    ⟨_, hAhi⟩ hdet0

end Stepanov
