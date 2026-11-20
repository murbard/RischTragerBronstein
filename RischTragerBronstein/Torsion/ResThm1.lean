import RischTragerBronstein.Torsion.IBExist5

/-!
# The residue theorem on the line

For a fraction field `Kx` of `C[X]`, `resAt a h` is the residue of `h dx` at `x = a` (the coefficient
of `T⁻¹` in `h(a + T)`), and `resInf h` the residue at infinity (`x = T⁻¹`, `dx = −T⁻² dT`).
**`sum_res_eq_zero`**: if the denominator of `h` splits over `C` with roots in `R`, then
`∑_{a ∈ R} resAt a h + resInf h = 0` (partial fractions, by induction on the denominator).
-/

open Polynomial HahnSeries

namespace Curves

open Differential LaurentSeries

section Line

variable {C : Type*} [Field C] {Kx : Type*} [Field Kx] [Algebra C[X] Kx] [IsFractionRing C[X] Kx]

variable (Kx) in
/-- The expansion at `x = a`. -/
noncomputable def expAt (a : C) : Kx →+* LaurentSeries C :=
  IsFractionRing.lift (branchSub_injective (C := C) (K := C) 1 one_pos a)

variable (Kx) in
/-- The expansion at infinity. -/
noncomputable def expInf : Kx →+* LaurentSeries C :=
  IsFractionRing.lift (infSub_injective (C := C) (K := C) 1 one_pos)

/-- The residue of `h dx` at `x = a`. -/
noncomputable def resAt (a : C) (h : Kx) : C := (expAt Kx a h).coeff (-1)

variable (C) in
/-- The residue of `h dx` at infinity. -/
noncomputable def resInf (h : Kx) : C := (expInf Kx h * single (-2 : ℤ) (-1 : C)).coeff (-1)

lemma expAt_algebraMap (a : C) (P : C[X]) :
    expAt Kx a (algebraMap C[X] Kx P) = branchSub (C := C) (K := C) 1 a P :=
  IsFractionRing.lift_algebraMap _ _

lemma expInf_algebraMap (P : C[X]) :
    expInf (C := C) Kx (algebraMap C[X] Kx P) = infSub (C := C) (K := C) 1 P :=
  IsFractionRing.lift_algebraMap _ _

lemma resAt_add (a : C) (h h' : Kx) : resAt a (h + h') = resAt a h + resAt a h' := by
  simp [resAt]

lemma resInf_add (h h' : Kx) : resInf C (h + h') = resInf C h + resInf C h' := by
  rw [resInf, resInf, resInf, map_add, add_mul, HahnSeries.coeff_add]

lemma resAt_poly (a : C) (P : C[X]) : resAt a (algebraMap C[X] Kx P) = 0 := by
  rw [resAt, expAt_algebraMap]
  exact lowerBd_ofPS _ _ (by norm_num)

lemma resInf_poly (P : C[X]) : resInf C (algebraMap C[X] Kx P) = 0 := by
  rw [resInf, expInf_algebraMap, infSub, coe_eval₂RingHom, eval₂_eq_sum_range, Finset.sum_mul,
    HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  simp only [RingHom.comp_apply, single_pow, one_pow, mul_assoc, single_mul_single]
  rw [HahnSeries.C_apply, single_mul_single, coeff_single_of_ne]
  simp only [nsmul_eq_mul, mul_neg, mul_one, zero_add]
  omega

lemma resAt_C_mul (a : C) (c : C) (h : Kx) :
    resAt a (algebraMap C[X] Kx (Polynomial.C c) * h) = c * resAt a h := by
  rw [resAt, resAt, map_mul, expAt_algebraMap, bs_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
  rfl

lemma resInf_C_mul (c : C) (h : Kx) :
    resInf C (algebraMap C[X] Kx (Polynomial.C c) * h) = c * resInf C h := by
  rw [resInf, resInf, map_mul, expInf_algebraMap, is_C, mul_assoc, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul]
  rfl

/-- The basic fraction `1/(x − a)ʲ`. -/
noncomputable def ufrac (Kx : Type*) [Field Kx] [Algebra C[X] Kx] (a : C) (j : ℕ) : Kx :=
  (algebraMap C[X] Kx ((X - Polynomial.C a) ^ j))⁻¹

lemma expAt_X_sub (b a : C) : expAt Kx b (algebraMap C[X] Kx (X - Polynomial.C a)) =
    HahnSeries.C (b - a) + single (1 : ℤ) (1 : C) := by
  rw [expAt_algebraMap, map_sub, bs_X, bs_C]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Nat.cast_one, map_sub]
  ring

lemma expAt_ufrac (b a : C) (j : ℕ) : expAt Kx b (ufrac Kx a j) =
    ((HahnSeries.C (b - a) + single (1 : ℤ) (1 : C)) ^ j)⁻¹ := by
  rw [ufrac, map_inv₀, map_pow, map_pow, expAt_X_sub]

lemma resAt_ufrac_self (a : C) (j : ℕ) : resAt a (ufrac Kx a j) = if j = 1 then 1 else 0 := by
  rw [resAt, expAt_ufrac, sub_self, map_zero, zero_add, single_pow, one_pow, inv_single, inv_one,
    coeff_single]
  by_cases hj : j = 1
  · subst hj; simp
  · rw [if_neg hj, if_neg]
    intro h
    apply hj
    have : ((j : ℤ) : ℤ) = 1 := by simpa using h.symm
    exact_mod_cast this

lemma unit_order_zero (u : LaurentSeries C) (hu : LowerBd u 0) (h0 : u.coeff 0 ≠ 0) :
    u ≠ 0 ∧ u.order = 0 ∧ LowerBd u⁻¹ 0 ∧ (u⁻¹).coeff 0 = (u.coeff 0)⁻¹ := by
  have hne : u ≠ 0 := fun h ↦ h0 (by rw [h, HahnSeries.coeff_zero])
  have hord : u.order = 0 := le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h0)
    (le_order_of_lowerBd _ hne 0 hu)
  have hinv := lowerBd_inv _ hne
  rw [hord, neg_zero] at hinv
  have hine : u⁻¹ ≠ 0 := inv_ne_zero hne
  have hord' : u⁻¹.order = 0 := by
    have := HahnSeries.order_mul hne hine
    rw [mul_inv_cancel₀ hne, HahnSeries.order_one, hord, zero_add] at this
    exact this.symm
  have hc := HahnSeries.coeff_mul_order_add_order u u⁻¹
  rw [hord, hord', add_zero, mul_inv_cancel₀ hne, HahnSeries.coeff_one, if_pos rfl,
    HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hord, hord'] at hc
  refine ⟨hne, hord, hinv, ?_⟩
  exact eq_inv_of_mul_eq_one_right hc.symm

lemma resAt_ufrac_ne (a b : C) (hb : b ≠ a) (j : ℕ) : resAt b (ufrac Kx a j) = 0 := by
  have hd : b - a ≠ 0 := sub_ne_zero.mpr hb
  have hlow : LowerBd (HahnSeries.C (b - a) + single (1 : ℤ) (1 : C)) 0 :=
    (lowerBd_C _).add ((lowerBd_single _ _).mono (by norm_num))
  have h0 : (HahnSeries.C (b - a) + single (1 : ℤ) (1 : C)).coeff 0 = b - a := by
    rw [HahnSeries.coeff_add, HahnSeries.C_apply, coeff_single_same,
      coeff_single_of_ne (show (0 : ℤ) ≠ 1 by norm_num), add_zero]
  obtain ⟨-, -, hinv, -⟩ := unit_order_zero _ hlow (by rw [h0]; exact hd)
  rw [resAt, expAt_ufrac, ← inv_pow]
  exact (hinv.pow j) (-1) (by norm_num)

lemma resInf_ufrac (a : C) (j : ℕ) (hj : 0 < j) :
    resInf C (ufrac Kx a j) = if j = 1 then -1 else 0 := by
  set v : LaurentSeries C := 1 - HahnSeries.C a * single (1 : ℤ) (1 : C) with hv
  have hvlow : LowerBd v 0 := (lowerBd_C 1).sub (by
    have := (lowerBd_C a).mul (lowerBd_single (1 : ℤ) (1 : C))
    exact this.mono (by norm_num))
  have hv0 : v.coeff 0 = 1 := by
    rw [hv, HahnSeries.coeff_sub, HahnSeries.coeff_one, if_pos rfl, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, coeff_single_of_ne (show (0 : ℤ) ≠ 1 by norm_num), smul_zero,
      sub_zero]
  obtain ⟨hvne, -, hvinv, hvinv0⟩ := unit_order_zero v hvlow (by rw [hv0]; exact one_ne_zero)
  rw [hv0, inv_one] at hvinv0
  have hw : infSub (C := C) (K := C) 1 (X - Polynomial.C a) = single (-1 : ℤ) (1 : C) * v := by
    rw [map_sub, is_X, is_C, hv, mul_sub, mul_one, ← mul_assoc,
      mul_comm (single (-1 : ℤ) (1 : C)), mul_assoc, single_mul_single]
    simp
  have hexp : expInf (C := C) Kx (ufrac Kx a j) = single (j : ℤ) (1 : C) * v⁻¹ ^ j := by
    rw [ufrac, map_inv₀, map_pow, map_pow, expInf_algebraMap, hw, mul_pow, mul_inv, single_pow,
      one_pow, inv_single, inv_one, inv_pow]
    congr 2
    simp
  rw [resInf, hexp, mul_comm (single (j : ℤ) (1 : C)), mul_assoc, single_mul_single, one_mul,
    mul_comm, HahnSeries.coeff_single_mul]
  by_cases hj1 : j = 1
  · subst hj1
    simp only [if_true, pow_one]
    rw [show (-1 : ℤ) - (((1 : ℕ) : ℤ) + -2) = 0 by norm_num, hvinv0]
    ring
  · rw [if_neg hj1, (hvinv.pow j) _ (by omega), mul_zero]

lemma sum_res_ufrac (R : Finset C) (a : C) (ha : a ∈ R) (j : ℕ) (hj : 0 < j) :
    ∑ b ∈ R, resAt b (ufrac Kx a j) + resInf C (ufrac Kx a j) = 0 := by
  classical
  have h1 : ∀ b ∈ R, resAt b (ufrac Kx a j) = if b = a then (if j = 1 then 1 else 0) else 0 := by
    intro b _
    by_cases hb : b = a
    · subst hb; rw [if_pos rfl, resAt_ufrac_self]
    · rw [if_neg hb]; exact resAt_ufrac_ne a b hb j
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' R a, if_pos ha, resInf_ufrac a j hj]
  split_ifs <;> ring

lemma ufrac_zero (a : C) : ufrac Kx a 0 = 1 := by simp [ufrac]

lemma X_sub_mul_ufrac (a : C) (m : ℕ) :
    algebraMap C[X] Kx (X - Polynomial.C a) * ufrac Kx a (m + 1) = ufrac Kx a m := by
  have hne : ∀ k, algebraMap C[X] Kx ((X - Polynomial.C a) ^ k) ≠ 0 := fun k ↦
    (map_ne_zero_iff _ (IsFractionRing.injective C[X] Kx)).mpr (pow_ne_zero _ (X_sub_C_ne_zero a))
  rw [ufrac, ufrac, pow_succ, map_mul, mul_inv, ← mul_assoc, mul_comm (algebraMap C[X] Kx _),
    mul_assoc, mul_inv_cancel₀ (by
      simpa using (map_ne_zero_iff _ (IsFractionRing.injective C[X] Kx)).mpr (X_sub_C_ne_zero a)),
    mul_one]

lemma sum_res_pow (R : Finset C) (a : C) (ha : a ∈ R) :
    ∀ (m : ℕ) (W : C[X]), ∑ b ∈ R, resAt b (algebraMap C[X] Kx W * ufrac Kx a m) +
      resInf C (algebraMap C[X] Kx W * ufrac Kx a m) = 0 := by
  intro m
  induction m with
  | zero =>
    intro W
    rw [ufrac_zero, mul_one, resInf_poly, add_zero]
    exact Finset.sum_eq_zero fun b _ ↦ resAt_poly b W
  | succ m ih =>
    intro W
    have hW : W = (X - Polynomial.C a) * (W /ₘ (X - Polynomial.C a)) + Polynomial.C (W.eval a) := by
      rw [← modByMonic_X_sub_C_eq_C_eval, add_comm, modByMonic_add_div]
    have e : algebraMap C[X] Kx W * ufrac Kx a (m + 1) =
        algebraMap C[X] Kx (W /ₘ (X - Polynomial.C a)) * ufrac Kx a m +
          algebraMap C[X] Kx (Polynomial.C (W.eval a)) * ufrac Kx a (m + 1) := by
      conv_lhs => rw [hW]
      rw [map_add, map_mul, add_mul, ← X_sub_mul_ufrac a m]
      ring
    rw [e]
    simp only [resAt_add, resInf_add, Finset.sum_add_distrib, resAt_C_mul, resInf_C_mul,
      ← Finset.mul_sum]
    have h2 := sum_res_ufrac (Kx := Kx) R a ha (m + 1) (Nat.succ_pos m)
    have h1 := ih (W /ₘ (X - Polynomial.C a))
    linear_combination h1 + (W.eval a) * h2

/-- **The residue theorem on the line.** -/
theorem sum_res_eq_zero (R : Finset C) :
    ∀ (Q : C[X]), Q ≠ 0 → Multiset.card Q.roots = Q.natDegree → (∀ b, Q.IsRoot b → b ∈ R) →
      ∀ P : C[X], ∑ b ∈ R, resAt b (algebraMap C[X] Kx P / algebraMap C[X] Kx Q) +
        resInf C (algebraMap C[X] Kx P / algebraMap C[X] Kx Q) = 0 := by
  classical
  intro Q
  induction hd : Q.natDegree using Nat.strong_induction_on generalizing Q with
  | _ d ih =>
  intro hQ hs hR P
  have hQK : algebraMap C[X] Kx Q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective C[X] Kx)).mpr hQ
  by_cases hroots : Q.roots = 0
  · -- constant denominator
    rw [hroots, Multiset.card_zero] at hs
    obtain ⟨c, rfl⟩ : ∃ c, Q = Polynomial.C c :=
      ⟨Q.coeff 0, eq_C_of_natDegree_eq_zero (hd.trans hs.symm)⟩
    have hc : c ≠ 0 := fun h ↦ hQ (by rw [h, map_zero])
    have e : algebraMap C[X] Kx P / algebraMap C[X] Kx (Polynomial.C c) =
        algebraMap C[X] Kx (Polynomial.C c⁻¹ * P) := by
      rw [map_mul, div_eq_iff hQK, mul_comm, ← mul_assoc, ← map_mul, ← Polynomial.C_mul,
        mul_inv_cancel₀ hc, map_one, map_one, one_mul]
    rw [e, resInf_poly, add_zero]
    exact Finset.sum_eq_zero fun b _ ↦ resAt_poly b _
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hroots
  have haR : a ∈ R := hR a ((mem_roots hQ).mp ha)
  set m := Q.rootMultiplicity a with hm
  have hm0 : 0 < m := (rootMultiplicity_pos hQ).mpr ((mem_roots hQ).mp ha)
  obtain ⟨Q₁, hQQ, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ a
  rw [← hm] at hQQ
  have hQ₁ : Q₁ ≠ 0 := fun h ↦ hQ (by rw [hQQ, h, mul_zero])
  have hcop : IsCoprime ((X - Polynomial.C a) ^ m) Q₁ :=
    ((irreducible_X_sub_C a).coprime_iff_not_dvd.mpr hndvd).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  -- the degrees and roots of `Q₁`
  have hdeg : Q.natDegree = m + Q₁.natDegree := by
    rw [hQQ, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero a)) hQ₁, natDegree_pow, natDegree_X_sub_C,
      mul_one]
  have hroots1 : Q.roots = Multiset.replicate m a + Q₁.roots := by
    rw [hQQ, roots_mul (by rw [← hQQ]; exact hQ), roots_pow, roots_X_sub_C,
      Multiset.nsmul_singleton]
  have hs1 : Multiset.card Q₁.roots = Q₁.natDegree := by
    have := hs
    rw [hroots1, Multiset.card_add, Multiset.card_replicate] at this
    omega
  have hR1 : ∀ b, Q₁.IsRoot b → b ∈ R := fun b hb ↦ hR b (by
    rw [hQQ, IsRoot, eval_mul, hb.eq_zero, mul_zero])
  have hlt : Q₁.natDegree < d := by omega
  -- partial fractions
  have hXm : algebraMap C[X] Kx ((X - Polynomial.C a) ^ m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective C[X] Kx)).mpr (pow_ne_zero _ (X_sub_C_ne_zero a))
  have hQ₁K : algebraMap C[X] Kx Q₁ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective C[X] Kx)).mpr hQ₁
  have e : algebraMap C[X] Kx P / algebraMap C[X] Kx Q =
      algebraMap C[X] Kx (P * u) / algebraMap C[X] Kx Q₁ +
        algebraMap C[X] Kx (P * v) * ufrac Kx a m := by
    have h1 := congrArg (algebraMap C[X] Kx) huv
    rw [map_add, map_mul, map_mul, map_one] at h1
    rw [hQQ, map_mul, ufrac]
    field_simp
    rw [map_mul, map_mul]
    linear_combination (-(algebraMap C[X] Kx P)) * h1
  rw [e]
  simp only [resAt_add, resInf_add, Finset.sum_add_distrib]
  have h1 := ih _ hlt Q₁ rfl hQ₁ hs1 hR1 (P * u)
  have h2 := sum_res_pow (Kx := Kx) R a haR m (P * v)
  linear_combination h1 + h2

end Line

end Curves