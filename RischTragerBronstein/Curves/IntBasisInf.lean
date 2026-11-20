import RischTragerBronstein.Curves.IntBasisFin

/-!
# Orders above infinity

`InfOrd z k`: along every branch above infinity (`x = T^{−N}`) the expansion of `z` starts at
`T^{−kN}` or later, i.e. `x^{−k} z` has no pole above infinity. Closed under sums and products
(`k` adds); a polynomial `p(x)` has `InfOrd (deg p)`; every element has some `InfOrd`
(`infOrd_exists`). **A non-zero integral element has no `InfOrd` below `0`** (`infOrd_nonneg`):
otherwise `xʲ z` (`j ≥ 1`) has no pole at all, so it is algebraic over `C`, but it vanishes along
the branches above `x = 0`.
-/

open Polynomial HahnSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section InfOrd

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

variable (K) in
/-- `x^{−k} z` has no pole above infinity. -/
def InfOrd (z : C⟮S.x⟯⟮S.y⟯) (k : ℤ) : Prop :=
  ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l),
    LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r (S.root_of_mem hl hr) z)
      (-(k * N))

lemma infOrd_zero_iff (z : C⟮S.x⟯⟮S.y⟯) : S.InfOrd K z 0 ↔ S.RegularInf K z := by
  constructor
  · intro h N hN l hl r hr
    have := h N hN l hl r hr
    rw [zero_mul, neg_zero] at this
    exact order_nonneg_of_lowerBd _ this
  · intro h N hN l hl r hr
    rw [zero_mul, neg_zero]
    exact lowerBd_of_order_nonneg (h N hN l hl r hr)

lemma InfOrd.mono {z : C⟮S.x⟯⟮S.y⟯} {k k' : ℤ} (h : S.InfOrd K z k) (hk : k ≤ k') :
    S.InfOrd K z k' := fun N hN l hl r hr ↦
  (h N hN l hl r hr).mono (by
    have : (k : ℤ) * N ≤ k' * N := Int.mul_le_mul_of_nonneg_right hk (by positivity)
    linarith)

lemma InfOrd.add {z z' : C⟮S.x⟯⟮S.y⟯} {k : ℤ} (h : S.InfOrd K z k) (h' : S.InfOrd K z' k) :
    S.InfOrd K (z + z') k := fun N hN l hl r hr ↦ by
  rw [map_add]; exact (h N hN l hl r hr).add (h' N hN l hl r hr)

lemma InfOrd.neg {z : C⟮S.x⟯⟮S.y⟯} {k : ℤ} (h : S.InfOrd K z k) : S.InfOrd K (-z) k :=
  fun N hN l hl r hr ↦ by rw [map_neg]; exact (h N hN l hl r hr).neg

lemma InfOrd.sub {z z' : C⟮S.x⟯⟮S.y⟯} {k : ℤ} (h : S.InfOrd K z k) (h' : S.InfOrd K z' k) :
    S.InfOrd K (z - z') k := by
  rw [sub_eq_add_neg]; exact InfOrd.add S h (InfOrd.neg S h')

lemma infOrd_zero (k : ℤ) : S.InfOrd K 0 k := fun N hN l hl r hr ↦ by
  rw [map_zero]; exact lowerBd_zero _

lemma InfOrd.mul {z z' : C⟮S.x⟯⟮S.y⟯} {k k' : ℤ} (h : S.InfOrd K z k) (h' : S.InfOrd K z' k') :
    S.InfOrd K (z * z') (k + k') := fun N hN l hl r hr ↦ by
  rw [map_mul]
  exact ((h N hN l hl r hr).mul (h' N hN l hl r hr)).mono (by ring_nf; rfl)

lemma InfOrd.sum {ι : Type*} (s : Finset ι) (z : ι → C⟮S.x⟯⟮S.y⟯) {k : ℤ}
    (h : ∀ i ∈ s, S.InfOrd K (z i) k) : S.InfOrd K (∑ i ∈ s, z i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact S.infOrd_zero k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact InfOrd.add S (h a (Finset.mem_insert_self a s)) (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- A polynomial `p(x)` has order `deg p` above infinity. -/
lemma infOrd_poly (p : C[X]) : S.InfOrd K ⟨aeval S.x p, S.aeval_mem p⟩ p.natDegree :=
  fun N hN l hl r hr ↦ by
  rw [S.embG_polyX]
  have := lowerBd_infSub (C := C) (K := K) N (Nat.pos_of_ne_zero hN) p
  refine this.mono (le_of_eq ?_)
  push_cast; ring

/-- The inverse of a non-zero polynomial `q(x)` has order `−deg q` above infinity. -/
lemma infOrd_inv_poly (q : C[X]) (hq : q ≠ 0) :
    S.InfOrd K (⟨aeval S.x q, S.aeval_mem q⟩ : C⟮S.x⟯⟮S.y⟯)⁻¹ (-(q.natDegree : ℤ)) :=
  fun N hN l hl r hr ↦ by
  rw [map_inv₀, S.embG_polyX]
  have h0 := infSub_ne_zero (C := C) (K := K) N (Nat.pos_of_ne_zero hN) q hq
  have := lowerBd_inv _ h0
  rw [order_infSub N (Nat.pos_of_ne_zero hN) q hq] at this
  refine this.mono (le_of_eq ?_)
  push_cast; ring

/-- **Every element has an order above infinity.** -/
lemma infOrd_exists (z : C⟮S.x⟯⟮S.y⟯) : ∃ k : ℤ, S.InfOrd K z k := by
  obtain ⟨W, Q, hQ, hWQ⟩ := S.exists_repr z
  set DW := ∑ i ∈ Finset.range (W.natDegree + 1), ((W.coeff i).natDegree + S.degB * i) with hDW
  have hDWi : ∀ i, W.coeff i ≠ 0 → (W.coeff i).natDegree + S.degB * i ≤ DW := by
    intro i hi
    have hi' : i ≤ W.natDegree := le_natDegree_of_ne_zero hi
    exact Finset.single_le_sum (f := fun i ↦ (W.coeff i).natDegree + S.degB * i)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi'))
  refine ⟨(DW : ℤ) - Q.natDegree, fun N hN l hl r hr ↦ ?_⟩
  have := S.lowerBd_inf N (Nat.pos_of_ne_zero hN) S.degB S.degB_spec r (S.root_of_mem hl hr) z W Q
    hQ hWQ DW hDWi
  refine this.mono (le_of_eq ?_)
  push_cast; ring

variable [IsAlgClosed K]

/-- **A non-zero element without finite poles has no zero above infinity beyond its pole order**:
`InfOrd z k` forces `k ≥ 0`. -/
theorem infOrd_nonneg (z : C⟮S.x⟯⟮S.y⟯) (hz0 : z ≠ 0) (hz : S.RegularFinite K z) (k : ℤ)
    (hk : S.InfOrd K z k) : 0 ≤ k := by
  classical
  by_contra hneg
  push Not at hneg
  set j := (-k).toNat with hj
  have hjk : (j : ℤ) = -k := Int.toNat_of_nonneg (by omega)
  have hj1 : 1 ≤ j := by omega
  set xj : C⟮S.x⟯⟮S.y⟯ := ⟨aeval S.x (X ^ j : C[X]), S.aeval_mem _⟩ with hxj
  set u := xj * z with hu
  have hxj0 : xj ≠ 0 := by
    intro h0
    have := congrArg (fun t : C⟮S.x⟯⟮S.y⟯ ↦ (t : L)) h0
    simp only [hxj, map_pow, aeval_X, ZeroMemClass.coe_zero] at this
    exact S.htr.ne_zero (pow_eq_zero_iff (by omega) |>.mp this)
  have hu0 : u ≠ 0 := mul_ne_zero hxj0 hz0
  -- `u` has no pole at all
  have hufin : S.RegularFinite K u := by
    intro a N hN l hl r hr
    rw [hu, map_mul, hxj, S.embG_polyX]
    exact order_nonneg_of_lowerBd _ (by
      have := (lowerBd_branchSub_nonneg (C := C) N a (X ^ j)).mul
        (lowerBd_of_order_nonneg (hz a N hN l hl r hr))
      rwa [zero_add] at this)
  have huinf : S.RegularInf K u := by
    rw [← S.infOrd_zero_iff]
    have := InfOrd.mul S (S.infOrd_poly (X ^ j : C[X])) hk
    rw [natDegree_X_pow] at this
    exact InfOrd.mono S this (by omega)
  obtain ⟨M0, hM0, hev⟩ := S.algebraic_of_regular u hufin huinf
  -- remove the factor `Zᵉ`
  obtain ⟨M1, hM1, hX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd M0 hM0.ne_zero 0
  have hev1 : aeval (u : L) M1 = 0 := by
    rw [hM1, map_mul, map_pow, map_sub, aeval_X, aeval_C, map_zero, sub_zero] at hev
    exact (mul_eq_zero.mp hev).resolve_left (pow_ne_zero _ (by
      intro h0; exact hu0 (Subtype.val_injective (by rw [h0]; rfl))))
  have hc0 : M1.coeff 0 ≠ 0 := by
    intro h0; exact hX (by rw [map_zero, sub_zero]; exact X_dvd_iff.mpr h0)
  -- a branch above `x = 0`
  obtain ⟨N, hN, l0, hlen, hsplit0⟩ := S.branches_at (K := K) 0
  set l := l0.map (ofPowerSeries ℤ K) with hl
  have hsplit : S.F.map (branchSub N 0) = (l.map fun r ↦ X - Polynomial.C r).prod := by
    rw [hsplit0, hl, List.map_map]; rfl
  have hn : 0 < S.F.natDegree := by
    rw [← S.natDegree_minpoly]
    letI := algebraAdjoinSimple (F := C) S.x
    exact minpoly.natDegree_pos S.isIntegral
  obtain ⟨r, hr⟩ : ∃ r, r ∈ l := List.exists_mem_of_length_pos (by rw [hl, List.length_map]; omega)
  have hN0 := Nat.pos_of_ne_zero hN
  have hY := S.root_of_mem hsplit hr
  set σ := S.embG (branchSub N 0) (branchSub_injective N hN0 0) r hY
  -- `σ u` vanishes at `T = 0`
  have hσu : LowerBd (σ u) 1 := by
    rw [hu, map_mul, hxj, S.embG_polyX]
    have h1 : LowerBd (branchSub (C := C) (K := K) N 0 (X ^ j)) 1 := by
      have ho := order_branchSub (K := K) N hN0 0 (X ^ j : C[X]) (pow_ne_zero _ X_ne_zero)
      have hm : ((X : K[X]) ^ j).rootMultiplicity 0 = j := by
        simpa using rootMultiplicity_X_sub_C_pow (0 : K) j
      rw [Polynomial.map_pow, Polynomial.map_X, hm] at ho
      have hNj : 1 ≤ N * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN (by omega))
      intro m hm'
      refine HahnSeries.coeff_eq_zero_of_lt_order ?_
      rw [ho]
      have : (1 : ℤ) ≤ ((N * j : ℕ) : ℤ) := by exact_mod_cast hNj
      omega
    have := h1.mul (lowerBd_of_order_nonneg (hz 0 N hN l hsplit r hr))
    rwa [add_zero] at this
  -- `M₁(σ u) = 0`
  have hroot := S.embG_eval_poly (branchSub N 0) (branchSub_injective N hN0 0) r hY u
    (M1.map Polynomial.C) (by
      have e : (aeval S.x).toRingHom.comp Polynomial.C = algebraMap C L := by
        ext c; simp
      rw [Polynomial.map_map, e, eval_map, ← aeval_def]; exact hev1)
  rw [Polynomial.map_map] at hroot
  -- its constant coefficient is `M₁(0) ≠ 0`
  have hsplitP := (M1.map ((branchSub (C := C) (K := K) N 0).comp Polynomial.C)).divX_mul_X_add
  have hcoef := congrArg (fun P ↦ (P.eval (σ u)).coeff 0) hsplitP
  simp only [eval_add, eval_mul, eval_X, eval_C, coeff_map] at hcoef
  have hdivX : LowerBd (((M1.map ((branchSub (C := C) (K := K) N 0).comp Polynomial.C)).divX).eval
      (σ u) * σ u) 1 := by
    have h0 : LowerBd (((M1.map ((branchSub (C := C) (K := K) N 0).comp Polynomial.C)).divX).eval
        (σ u)) 0 := lowerBd_eval _ _ 0 le_rfl (hσu.mono (by norm_num)) 0 fun i ↦ by
      rw [coeff_divX, coeff_map, zero_mul, sub_zero, RingHom.comp_apply]
      exact lowerBd_branchSub_nonneg N 0 _
    have := h0.mul hσu
    rwa [zero_add] at this
  rw [HahnSeries.coeff_add, hdivX 0 (by norm_num), zero_add, RingHom.comp_apply, SuperData.branchSub_C,
    HahnSeries.C_apply, HahnSeries.coeff_single_same] at hcoef
  rw [hroot, HahnSeries.coeff_zero] at hcoef
  exact hc0 ((algebraMap C K).injective (by rw [hcoef, map_zero]))

/-- `p(x)` as an element of the function field. -/
noncomputable abbrev polyE (p : C[X]) : C⟮S.x⟯⟮S.y⟯ := ⟨aeval S.x p, S.aeval_mem p⟩

lemma polyE_ne_zero (p : C[X]) (hp : p ≠ 0) : S.polyE p ≠ 0 := by
  intro h0
  have := congrArg (fun t : C⟮S.x⟯⟮S.y⟯ ↦ (t : L)) h0
  simp only [ZeroMemClass.coe_zero] at this
  exact hp (transcendental_iff_injective.mp S.htr (by rw [this, map_zero]))

lemma polyE_mul (p q : C[X]) : S.polyE (p * q) = S.polyE p * S.polyE q :=
  Subtype.ext (by simp)

lemma polyE_sub (p q : C[X]) : S.polyE (p - q) = S.polyE p - S.polyE q :=
  Subtype.ext (by simp)

lemma polyE_C_mul (c : C) (p : C[X]) :
    S.polyE (Polynomial.C c * p) = S.polyE (Polynomial.C c) * S.polyE p := S.polyE_mul _ _

/-- A quotient `p(x)/q(x)` has order `deg p − deg q` above infinity. -/
lemma infOrd_frac (p q : C[X]) (hq : q ≠ 0) :
    S.InfOrd K (S.polyE p * (S.polyE q)⁻¹) ((p.natDegree : ℤ) - q.natDegree) := by
  have := InfOrd.mul S (S.infOrd_poly (K := K) p) (S.infOrd_inv_poly (K := K) q hq)
  exact InfOrd.mono S this (by omega)

variable (K) in
/-- **Reduced bases**: no non-trivial constant combination of the `x^{−rⱼ} wⱼ` vanishes above
infinity. -/
def Reduced {n : ℕ} (w : Fin n → C⟮S.x⟯⟮S.y⟯) (r : Fin n → ℕ) : Prop :=
  ∀ c : Fin n → C, S.InfOrd K (∑ j, S.polyE (Polynomial.C (c j)) *
    ((S.polyE (X ^ r j))⁻¹ * w j)) (-1) → ∀ j, c j = 0

/-- **A reduced basis is normal at infinity**: if `u = ∑ (pⱼ/q) x^{−rⱼ} wⱼ` has no pole above
infinity, then `deg pⱼ ≤ deg q`. -/
theorem reduced_normal {n : ℕ} (w : Fin n → C⟮S.x⟯⟮S.y⟯) (r : Fin n → ℕ)
    (hw : ∀ j, S.InfOrd K (w j) (r j)) (hred : S.Reduced K w r) (u : C⟮S.x⟯⟮S.y⟯)
    (hu : S.InfOrd K u 0) (p : Fin n → C[X]) (q : C[X]) (hq : q ≠ 0)
    (hup : u = ∑ j, S.polyE (p j) * (S.polyE q)⁻¹ * ((S.polyE (X ^ r j))⁻¹ * w j)) :
    ∀ j, (p j).natDegree ≤ q.natDegree := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨j1, hj1⟩ := hcon
  -- the largest excess degree
  set J := Finset.univ.filter fun j ↦ q.natDegree < (p j).natDegree with hJ
  have hJne : J.Nonempty := ⟨j1, by simp [hJ, hj1]⟩
  obtain ⟨j0, hj0J, hj0max⟩ := J.exists_max_image (fun j ↦ (p j).natDegree) hJne
  set D := (p j0).natDegree with hD
  set d := D - q.natDegree with hd
  have hj0 : q.natDegree < D := (Finset.mem_filter.mp hj0J).2
  have hd1 : 1 ≤ d := by omega
  have hmax : ∀ j, (p j).natDegree ≤ D := fun j ↦ by
    by_cases hj : q.natDegree < (p j).natDegree
    · exact hj0max j (by simp [hJ, hj])
    · omega
  -- the leading coefficients
  set γ : Fin n → C := fun j ↦ if (p j).natDegree = D then (p j).leadingCoeff / q.leadingCoeff else 0
    with hγ
  have hγ0 : γ j0 ≠ 0 := by
    have e0 : γ j0 = (p j0).leadingCoeff / q.leadingCoeff := if_pos rfl
    have hp0 : p j0 ≠ 0 := fun h0 ↦ by
      have : D = 0 := by rw [hD, h0, natDegree_zero]
      omega
    rw [e0]
    exact div_ne_zero (leadingCoeff_ne_zero.mpr hp0) (leadingCoeff_ne_zero.mpr hq)
  -- the remainders `eⱼ = pⱼ − γⱼ xᵈ q` have degree `< D`
  set e : Fin n → C[X] := fun j ↦ p j - Polynomial.C (γ j) * X ^ d * q with he
  have hqd : (X ^ d * q : C[X]).natDegree = D := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hq, natDegree_X_pow]; omega
  have hrem : ∀ j, e j = 0 ∨ (e j).natDegree < D := by
    intro j
    by_cases hpD : (p j).natDegree = D
    · have hp0 : p j ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hpD; omega
      have hγj : γ j = (p j).leadingCoeff / q.leadingCoeff := by simp only [hγ, if_pos hpD]
      have hq0 : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
      have hg0 : γ j ≠ 0 := by rw [hγj]; exact div_ne_zero (leadingCoeff_ne_zero.mpr hp0) hq0
      have hdeg : (Polynomial.C (γ j) * X ^ d * q).degree = (p j).degree := by
        rw [mul_assoc, degree_C_mul hg0, degree_eq_natDegree (mul_ne_zero (pow_ne_zero _ X_ne_zero) hq),
          hqd, degree_eq_natDegree hp0, hpD]
      have hlc : (p j).leadingCoeff = (Polynomial.C (γ j) * X ^ d * q).leadingCoeff := by
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, leadingCoeff_C,
          leadingCoeff_X_pow, mul_one, hγj,
          div_mul_cancel₀ _ hq0]
      have hlt := degree_sub_lt_left hdeg.symm hp0 hlc
      by_cases he0 : e j = 0
      · exact Or.inl he0
      · right
        rw [degree_eq_natDegree hp0, degree_eq_natDegree he0, hpD] at hlt
        exact_mod_cast hlt
    · have hγj : γ j = 0 := by simp only [hγ, if_neg hpD]
      right
      have : e j = p j := by simp only [he, hγj, map_zero, zero_mul, sub_zero]
      rw [this]
      exact lt_of_le_of_ne (hmax j) hpD
  -- `∑ γⱼ x^{−rⱼ} wⱼ = x^{−d} u − ∑ eⱼ/(xᵈ q) x^{−rⱼ} wⱼ`
  have hxd0 : S.polyE (X ^ d) ≠ 0 := S.polyE_ne_zero _ (pow_ne_zero _ X_ne_zero)
  have hq0 : S.polyE q ≠ 0 := S.polyE_ne_zero _ hq
  have hid : ∑ j, S.polyE (Polynomial.C (γ j)) * ((S.polyE (X ^ r j))⁻¹ * w j) =
      (S.polyE (X ^ d))⁻¹ * u - ∑ j, S.polyE (e j) * (S.polyE (X ^ d * q))⁻¹ *
        ((S.polyE (X ^ r j))⁻¹ * w j) := by
    rw [hup, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [he, S.polyE_sub, S.polyE_mul]
    field_simp
    ring
  -- its order above infinity is `≤ −1`
  have hord : S.InfOrd K (∑ j, S.polyE (Polynomial.C (γ j)) * ((S.polyE (X ^ r j))⁻¹ * w j)) (-1) := by
    rw [hid]
    refine InfOrd.sub S ?_ (InfOrd.sum S _ _ fun j _ ↦ ?_)
    · have := InfOrd.mul S (S.infOrd_inv_poly (K := K) (X ^ d) (pow_ne_zero _ X_ne_zero)) hu
      rw [natDegree_X_pow] at this
      exact InfOrd.mono S this (by omega)
    · have hxw : S.InfOrd K ((S.polyE (X ^ r j))⁻¹ * w j) 0 := by
        have := InfOrd.mul S (S.infOrd_inv_poly (K := K) (X ^ r j) (pow_ne_zero _ X_ne_zero)) (hw j)
        rw [natDegree_X_pow] at this
        exact InfOrd.mono S this (by omega)
      rcases hrem j with h0 | hlt
      · rw [h0]
        have : S.polyE 0 = 0 := Subtype.ext (by simp)
        rw [this, zero_mul, zero_mul]; exact S.infOrd_zero _
      · have hf := S.infOrd_frac (K := K) (e j) (X ^ d * q) (mul_ne_zero (pow_ne_zero _ X_ne_zero) hq)
        rw [hqd] at hf
        have := InfOrd.mul S hf hxw
        exact InfOrd.mono S this (by omega)
  exact hγ0 (hred γ hord j0)

lemma regularFinite_add {z z' : C⟮S.x⟯⟮S.y⟯} (h : S.RegularFinite K z) (h' : S.RegularFinite K z') :
    S.RegularFinite K (z + z') := fun a N hN l hl r hr ↦ by
  rw [map_add]
  exact order_nonneg_of_lowerBd _ ((lowerBd_of_order_nonneg (h a N hN l hl r hr)).add
    (lowerBd_of_order_nonneg (h' a N hN l hl r hr)))

lemma regularFinite_polyE_mul (p : C[X]) {z : C⟮S.x⟯⟮S.y⟯} (h : S.RegularFinite K z) :
    S.RegularFinite K (S.polyE p * z) := fun a N hN l hl r hr ↦ by
  rw [map_mul, S.embG_polyX]
  have := (lowerBd_branchSub_nonneg (C := C) N a p).mul (lowerBd_of_order_nonneg (h a N hN l hl r hr))
  rw [zero_add] at this
  exact order_nonneg_of_lowerBd _ this

lemma regularFinite_zero : S.RegularFinite K 0 := fun a N hN l hl r hr ↦ by
  rw [map_zero, HahnSeries.order_zero]

lemma regularFinite_sum {ι : Type*} (s : Finset ι) (z : ι → C⟮S.x⟯⟮S.y⟯)
    (h : ∀ i ∈ s, S.RegularFinite K (z i)) : S.RegularFinite K (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact S.regularFinite_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact S.regularFinite_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

variable (K) in
/-- **Integral basis data**: regular at finite places, every regular element is a polynomial
combination, and polynomial combinations are unique. -/
def IBasis {n : ℕ} (w : Fin n → C⟮S.x⟯⟮S.y⟯) : Prop :=
  (∀ j, S.RegularFinite K (w j)) ∧
    (∀ z, S.RegularFinite K z → ∃ c : Fin n → C[X], z = ∑ j, S.polyE (c j) * w j) ∧
    ∀ c : Fin n → C[X], ∑ j, S.polyE (c j) * w j = 0 → ∀ j, c j = 0

lemma IBasis.ne_zero {n : ℕ} {w : Fin n → C⟮S.x⟯⟮S.y⟯} (hw : S.IBasis K w) (j : Fin n) :
    w j ≠ 0 := by
  classical
  intro h0
  have := hw.2.2 (fun i ↦ if i = j then 1 else 0) (by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    by_cases hij : i = j
    · subst hij; rw [h0, mul_zero]
    · simp only [hij, if_false]
      have : S.polyE 0 = 0 := Subtype.ext (by simp)
      rw [this, zero_mul]) j
  simp at this

lemma polyE_add (p q : C[X]) : S.polyE (p + q) = S.polyE p + S.polyE q := Subtype.ext (by simp)

lemma polyE_one : S.polyE 1 = 1 := Subtype.ext (by simp)

lemma polyE_zero' : S.polyE 0 = 0 := Subtype.ext (by simp)

/-- **One reduction step**: replacing `w_{j0}` by `∑ cⱼ x^{r_{j0} − rⱼ} wⱼ` (`c_{j0} ≠ 0`) keeps an
integral basis. -/
lemma IBasis.update {n : ℕ} {w : Fin n → C⟮S.x⟯⟮S.y⟯} (hw : S.IBasis K w) (a : Fin n → C[X])
    (j0 : Fin n) (c0 : C) (hc0 : c0 ≠ 0) (ha0 : a j0 = Polynomial.C c0) :
    S.IBasis K (Function.update w j0 (∑ j, S.polyE (a j) * w j)) := by
  classical
  set w' := ∑ j, S.polyE (a j) * w j with hw'
  -- sums over the updated family
  have hsplit : ∀ d : Fin n → C[X], ∑ j, S.polyE (d j) * Function.update w j0 w' j =
      ∑ j, S.polyE (d j0 * a j + if j = j0 then 0 else d j) * w j := by
    intro d
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), Function.update_self]
    rw [← Finset.add_sum_erase (Finset.univ) (fun j ↦ S.polyE (d j0 * a j + if j = j0 then 0 else d j) *
      w j) (Finset.mem_univ j0)]
    rw [Finset.sum_congr rfl fun j hj ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
    simp only [hw', Finset.mul_sum, ↓reduceIte, add_zero]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    · rw [S.polyE_mul]; ring
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      simp only [Finset.ne_of_mem_erase hj, ↓reduceIte, S.polyE_add, S.polyE_mul]; ring
  refine ⟨fun j ↦ ?_, fun z hz ↦ ?_, fun d hd ↦ ?_⟩
  · by_cases hj : j = j0
    · subst hj; rw [Function.update_self]
      exact S.regularFinite_sum _ _ fun i _ ↦ S.regularFinite_polyE_mul _ (hw.1 i)
    · rw [Function.update_of_ne hj]; exact hw.1 j
  · obtain ⟨b, hb⟩ := hw.2.1 z hz
    set k := Polynomial.C c0⁻¹ * b j0 with hk
    refine ⟨fun j ↦ if j = j0 then k else b j - k * a j, ?_⟩
    rw [hsplit, hb]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 2
    by_cases hj : j = j0
    · subst hj
      simp only [↓reduceIte, add_zero, hk, ha0]
      have hcc : Polynomial.C c0⁻¹ * Polynomial.C c0 = (1 : C[X]) := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ hc0, Polynomial.C_1]
      linear_combination (-(b j)) * hcc
    · simp only [↓reduceIte, hj]; ring
  · have h1 := hw.2.2 _ ((hsplit d).symm.trans hd)
    have hd0 : d j0 = 0 := by
      have := h1 j0
      simp only [↓reduceIte, add_zero, ha0] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd (Polynomial.C_eq_zero.mp h) hc0
    intro j
    by_cases hj : j = j0
    · subst hj; exact hd0
    · have := h1 j
      simpa [hd0, hj] using this

/-- **The reduction descent**: every integral basis with orders `r` above infinity can be
transformed into a reduced one. -/
theorem exists_reduced_of {n : ℕ} :
    ∀ (m : ℕ) (w : Fin n → C⟮S.x⟯⟮S.y⟯) (r : Fin n → ℕ), S.IBasis K w →
      (∀ j, S.InfOrd K (w j) (r j)) → ∑ j, r j = m →
      ∃ (w' : Fin n → C⟮S.x⟯⟮S.y⟯) (r' : Fin n → ℕ), S.IBasis K w' ∧
        (∀ j, S.InfOrd K (w' j) (r' j)) ∧ S.Reduced K w' r' := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro w r hw hr hm
  by_cases hred : S.Reduced K w r
  · exact ⟨w, r, hw, hr, hred⟩
  -- a vanishing combination
  simp only [Reduced, not_forall] at hred
  obtain ⟨c, hc, j1, hj1⟩ := hred
  set J := Finset.univ.filter fun j ↦ c j ≠ 0 with hJ
  have hJne : J.Nonempty := ⟨j1, by simp [hJ, hj1]⟩
  obtain ⟨j0, hj0J, hj0max⟩ := J.exists_max_image r hJne
  have hc0 : c j0 ≠ 0 := (Finset.mem_filter.mp hj0J).2
  have hle : ∀ j, c j ≠ 0 → r j ≤ r j0 := fun j hj ↦ hj0max j (by simp [hJ, hj])
  set a : Fin n → C[X] := fun j ↦ Polynomial.C (c j) * X ^ (r j0 - r j) with ha
  have ha0 : a j0 = Polynomial.C (c j0) := by simp [ha]
  set w' := ∑ j, S.polyE (a j) * w j with hw'
  -- `w' = x^{r_{j0}} ∑ cⱼ x^{−rⱼ} wⱼ`
  have hw'eq : w' = S.polyE (X ^ r j0) *
      ∑ j, S.polyE (Polynomial.C (c j)) * ((S.polyE (X ^ r j))⁻¹ * w j) := by
    rw [hw', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hcj : c j = 0
    · simp [ha, hcj, S.polyE_mul, S.polyE_zero']
    · have hrj := hle j hcj
      have hX : S.polyE (X ^ r j0) = S.polyE (X ^ (r j0 - r j)) * S.polyE (X ^ r j) := by
        rw [← S.polyE_mul, ← pow_add, Nat.sub_add_cancel hrj]
      have hxj0 : S.polyE (X ^ r j) ≠ 0 := S.polyE_ne_zero _ (pow_ne_zero _ X_ne_zero)
      rw [ha, S.polyE_mul, hX]
      field_simp
  have hw'ord : S.InfOrd K w' ((r j0 : ℤ) - 1) := by
    rw [hw'eq]
    have := InfOrd.mul S (S.infOrd_poly (K := K) (X ^ r j0)) hc
    rw [natDegree_X_pow] at this
    exact InfOrd.mono S this (by omega)
  -- the new basis
  have hv := IBasis.update S hw a j0 (c j0) hc0 ha0
  have hv0 := IBasis.ne_zero S hv j0
  rw [Function.update_self] at hv0
  have hreg' : S.RegularFinite K w' := by
    have := hv.1 j0
    rwa [Function.update_self] at this
  have hr1 : 1 ≤ r j0 := by
    have := S.infOrd_nonneg w' hv0 hreg' _ hw'ord
    omega
  set r' := Function.update r j0 (r j0 - 1) with hr'
  have hsum : ∑ j, r' j + 1 = ∑ j, r j := by
    rw [hr', Finset.sum_update_of_mem (Finset.mem_univ j0), ← Finset.add_sum_erase _ _ (Finset.mem_univ j0),
      Finset.sdiff_singleton_eq_erase]
    omega
  refine ih (∑ j, r' j) (by omega) _ r' hv (fun j ↦ ?_) rfl
  by_cases hj : j = j0
  · subst hj
    rw [Function.update_self, hr', Function.update_self]
    exact InfOrd.mono S hw'ord (by omega)
  · rw [Function.update_of_ne hj, hr', Function.update_of_ne hj]
    exact hr j

variable (K) in
/-- **Reduced integral bases exist.** -/
theorem exists_reduced {n : ℕ} (w : Fin n → C⟮S.x⟯⟮S.y⟯) (hw : S.IBasis K w) :
    ∃ (w' : Fin n → C⟮S.x⟯⟮S.y⟯) (r' : Fin n → ℕ), S.IBasis K w' ∧
      (∀ j, S.InfOrd K (w' j) (r' j)) ∧ S.Reduced K w' r' := by
  choose k hk using fun j ↦ S.infOrd_exists (K := K) (w j)
  have hk0 : ∀ j, 0 ≤ k j := fun j ↦
    S.infOrd_nonneg (w j) (IBasis.ne_zero S hw j) (hw.1 j) (k j) (hk j)
  exact S.exists_reduced_of _ w (fun j ↦ (k j).toNat) hw
    (fun j ↦ InfOrd.mono S (hk j) (by rw [Int.toNat_of_nonneg (hk0 j)])) rfl

variable (K) in
/-- **Integral basis data exist** (from Mathlib's integral closure). -/
theorem exists_IBasis : ∃ w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯, S.IBasis K w := by
  classical
  obtain ⟨b, hbi, hbs⟩ := S.exists_intBasis
  refine ⟨fun j ↦ b j, fun j ↦ ?_, fun z hz ↦ ?_, fun c hc ↦ ?_⟩
  · obtain ⟨M, hM, hev⟩ := hbi j
    exact S.regularFinite_of_integral (b j) M hM hev
  · obtain ⟨M, hM, hev⟩ := S.integral_of_regular (K := K) z hz
    obtain ⟨c, hc⟩ := hbs z ⟨M, hM, hev⟩
    refine ⟨c, Subtype.ext ?_⟩
    rw [hc]
    push_cast
    rfl
  · -- `C(x)`-independence of the basis
    letI := algebraAdjoinSimple (F := C) S.x
    have hpoly : ∀ p : C[X], S.polyE p =
        algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (algebraMap C[X] C⟮S.x⟯ p) := fun p ↦ Subtype.ext (by
      show aeval S.x p = ((algebraMap C[X] C⟮S.x⟯ p : C⟮S.x⟯) : L)
      rw [algebraMap_adjoinSimple])
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli (fun j ↦ algebraMap C[X] C⟮S.x⟯ (c j)) (by
      rw [← hc]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Algebra.smul_def, hpoly])
    intro j
    have hj := this j
    have hinj : Function.Injective (algebraMap C[X] C⟮S.x⟯) := by
      haveI := isFractionRing_adjoin_simple S.x S.htr
      exact IsFractionRing.injective _ _
    exact hinj (by rw [hj, map_zero])

end CurveData

end InfOrd

section Deriv

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma derivation_infX_ne (N : ℕ) (hN : 0 < N) :
    LaurentSeries.derivation (single (-(N : ℤ)) (1 : K)) ≠ 0 := by
  rw [SuperData.derivation_infX N]
  refine HahnSeries.single_ne_zero ?_
  simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
  exact hN.ne'

/-- **Logarithmic stability at infinity**: `x d/dx` preserves the orders above infinity. -/
theorem infOrd_x_deriv (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (z : C⟮S.x⟯⟮S.y⟯) (k : ℤ)
    (hz : S.InfOrd K z k) :
    S.InfOrd K (S.polyE X * ⟨(z : L)′, S.derivClosedXY hC hx z z.2⟩) k := by
  intro N hN l hl r hr
  have hN0 := Nat.pos_of_ne_zero hN
  have hY := S.root_of_mem hl hr
  rw [map_mul, S.embG_polyX]
  have hd := S.embG_derivG (single (-(N : ℤ)) (1 : K)) (derivation_infX_ne N hN0)
    (infSub N) (infSub_injective N hN0) (fun P ↦ by rw [SuperData.infSub_eq_subst])
    hC hx r hY (z : L) z.2
  simp only [Subtype.coe_eta] at hd
  rw [hd]
  have hδ : SuperData.deltaX (single (-(N : ℤ)) (1 : K))
      (S.embG (infSub N) (infSub_injective N hN0) r hY z) =
      (single (-(N : ℤ) - 1) (-(N : K)))⁻¹ * LaurentSeries.derivative K
        (S.embG (infSub N) (infSub_injective N hN0) r hY z) := by
    show (LaurentSeries.derivation (single (-(N : ℤ)) (1 : K)))⁻¹ *
      LaurentSeries.derivation _ = _
    rw [SuperData.derivation_infX N, LaurentSeries.derivation_apply]
  rw [hδ]
  have hX : infSub (C := C) (K := K) N X = single (-(N : ℤ)) 1 := by
    rw [infSub, coe_eval₂RingHom, eval₂_X]
  rw [hX]
  have hN' : (-(N : K)) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hN0.ne')
  have hinv : LowerBd (single (-(N : ℤ) - 1) (-(N : K)))⁻¹ ((N : ℤ) + 1) := by
    have := lowerBd_inv (single (-(N : ℤ) - 1) (-(N : K))) (HahnSeries.single_ne_zero hN')
    rw [HahnSeries.order_single hN'] at this
    exact this.mono (by omega)
  have := (lowerBd_single (-(N : ℤ)) (1 : K)).mul (hinv.mul (hz N hN l hl r hr).derivative)
  exact this.mono (by ring_nf; omega)

end CurveData

end Deriv

end Curves
