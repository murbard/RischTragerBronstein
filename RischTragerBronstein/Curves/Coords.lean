import RischTragerBronstein.Curves.Poles

/-!
# Bounds on the coordinates `z = ∑ Zᵢ(x) yⁱ` from the branch values

`discR = Res_Y(F, F_Y) ∈ C[x]` (non-zero, `F` separable). Along a split fibre
`F(g, Y) = ∏ⱼ (Y − rⱼ)` we have `g(discR) = ∏ⱼ F_Y(rⱼ)` and, by interpolation at the `rⱼ`,

  `g(discR) · ∑ᵢ ĝ(Zᵢ) Yⁱ = ∑ⱼ φⱼ(z) ∏_{k≠j} F_Y(r_k) ∏_{k≠j} (Y − r_k)`.

So if the branch values `φⱼ(z)` have no coefficient below `Tᵐ` and the `rⱼ` are power series, the
same holds for `g(discR · Zᵢ)` (`coord_lowerBd`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section PolyLB

variable {K : Type*} [Field K]

/-- All coefficients have no term below `Tᵐ`. -/
def PolyLB (p : (LaurentSeries K)[X]) (m : ℤ) : Prop := ∀ i, LowerBd (p.coeff i) m

lemma PolyLB.mul {p q : (LaurentSeries K)[X]} {m m' : ℤ} (hp : PolyLB p m) (hq : PolyLB q m') :
    PolyLB (p * q) (m + m') := fun i ↦ by
  rw [Polynomial.coeff_mul]
  exact lowerBd_sum _ _ fun x _ ↦ (hp x.1).mul (hq x.2)

lemma polyLB_C {c : LaurentSeries K} {m : ℤ} (hc : LowerBd c m) :
    PolyLB (Polynomial.C c) m := fun i ↦ by
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hc
  · exact lowerBd_zero m

lemma polyLB_X_sub_C {r : LaurentSeries K} {b : ℤ} (hr : LowerBd r b) (hb : b ≤ 0) :
    PolyLB (X - Polynomial.C r) b :=
  fun i ↦ by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    refine LowerBd.sub ?_ ?_
    · split_ifs
      · rw [← HahnSeries.C_one]; exact (lowerBd_C 1).mono hb
      · exact lowerBd_zero b
    · split_ifs
      · exact hr
      · exact lowerBd_zero b

lemma polyLB_prod {ι : Type*} (s : Finset ι) (p : ι → (LaurentSeries K)[X]) {b : ℤ}
    (h : ∀ i ∈ s, PolyLB (p i) b) : PolyLB (∏ i ∈ s, p i) (s.card * b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, ← Polynomial.C_1, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact polyLB_C (by rw [← HahnSeries.C_one]; exact lowerBd_C 1)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have := (h i (Finset.mem_insert_self _ _)).mul
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
    convert this using 1
    push_cast; ring

lemma polyLB_sum {ι : Type*} (s : Finset ι) (p : ι → (LaurentSeries K)[X]) {m : ℤ}
    (h : ∀ i ∈ s, PolyLB (p i) m) : PolyLB (∑ i ∈ s, p i) m := fun k ↦ by
  rw [finsetSum_coeff]
  exact lowerBd_sum _ _ fun i hi ↦ h i hi k

end PolyLB

section Interp

variable {R : Type*} [CommRing R]

/-- `(∏ₖ (X − rₖ))′(rᵢ) = ∏_{k ≠ i} (rᵢ − rₖ)`. -/
lemma eval_derivative_prod {n : ℕ} (r : Fin n → R) (i : Fin n) :
    (derivative (∏ k, (X - Polynomial.C (r k)))).eval (r i) =
      ∏ k ∈ Finset.univ.erase i, (r i - r k) := by
  classical
  rw [derivative_prod_finset, eval_finsetSum, Finset.sum_eq_single i]
  · rw [derivative_X_sub_C, mul_one, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
  · intro k _ hki
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.mpr ⟨Ne.symm hki,
      Finset.mem_univ _⟩) (by simp), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Interpolation at the roots of a split polynomial.** -/
lemma interp_identity [IsDomain R] {n : ℕ} (r : Fin n → R)
    (hne : ∏ j, (derivative (∏ k, (X - Polynomial.C (r k)))).eval (r j) ≠ 0)
    (P : R[X]) (hP : P.natDegree < n) :
    Polynomial.C (∏ j, (derivative (∏ k, (X - Polynomial.C (r k)))).eval (r j)) * P =
      ∑ j, Polynomial.C (P.eval (r j) *
        ∏ k ∈ Finset.univ.erase j, (derivative (∏ k, (X - Polynomial.C (r k)))).eval (r k)) *
          ∏ k ∈ Finset.univ.erase j, (X - Polynomial.C (r k)) := by
  classical
  have hinj : Function.Injective r := by
    intro i j hij
    by_contra hne'
    apply hne
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [eval_derivative_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hne', Finset.mem_univ j⟩)
      (by rw [hij, sub_self])
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact absurd hP (Nat.not_lt_zero _)
  refine eq_of_natDegree_lt_card_of_eval_eq _ _ hinj (fun i ↦ ?_) (max_lt ?_ ?_)
  · rw [eval_mul, eval_C, eval_finsetSum, Finset.sum_eq_single i]
    · rw [eval_mul, eval_C, eval_prod]
      simp only [eval_sub, eval_X, eval_C]
      rw [← eval_derivative_prod r i,
        ← Finset.prod_erase_mul (s := Finset.univ) (a := i) _ (Finset.mem_univ i)]
      ring
    · intro j _ hji
      rw [eval_mul, eval_prod]
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := i)
        (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ _⟩) ?_)
      simp
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [Fintype.card_fin]
    exact (natDegree_C_mul_le _ _).trans_lt hP
  · rw [Fintype.card_fin]
    refine (natDegree_sum_le_of_forall_le _ _ (n := n - 1) fun j _ ↦ ?_).trans_lt (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun k _ ↦ natDegree_X_sub_C_le (r k))).trans ?_
    simp [Finset.card_erase_of_mem (Finset.mem_univ j)]

end Interp

section CoordCurve

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- `Res_Y(F, F_Y)`. -/
noncomputable def discR : C[X] :=
  resultant S.F (derivative S.F) S.F.natDegree (S.F.natDegree - 1)

lemma discR_map (g : C[X] →+* LaurentSeries K) (r : Fin S.F.natDegree → LaurentSeries K)
    (hsplit : S.F.map g = ∏ k, (X - Polynomial.C (r k))) :
    g S.discR = ∏ j, (derivative (∏ k, (X - Polynomial.C (r k)))).eval (r j) := by
  have hlist : ∏ k, (X - Polynomial.C (r k)) =
      ((List.ofFn r).map fun a ↦ X - Polynomial.C a).prod := by
    rw [List.map_ofFn, List.prod_ofFn]; rfl
  have hdeg : (derivative (((List.ofFn r).map fun a ↦ X - Polynomial.C a).prod)).natDegree ≤
      S.F.natDegree - 1 :=
    (natDegree_derivative_le _).trans (by rw [← hlist, ← hsplit, S.monic.natDegree_map])
  have h := resultant_list_prod (List.ofFn r) _ _ hdeg
  rw [List.length_ofFn] at h
  rw [discR, ← resultant_map_map, ← Polynomial.derivative_map, hsplit, hlist, h, List.map_ofFn,
    List.prod_ofFn]
  rfl

/-- The discriminant is nonzero when the characteristic does not divide `deg_Y F`. -/
lemma discR_ne_zero_of (hn : ((S.F.natDegree : ℕ) : C) ≠ 0) : S.discR ≠ 0 := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  intro h0
  have h1 := congrArg (algebraMap C[X] C⟮S.x⟯) h0
  rw [discR, ← resultant_map_map, ← Polynomial.derivative_map, map_zero, ← S.minpoly_eq] at h1
  set m := minpoly C⟮S.x⟯ S.y with hm
  have hdeg : m.natDegree = S.F.natDegree := S.natDegree_minpoly
  have hmon : m.Monic := minpoly.monic S.isIntegral
  have hnx : ((S.F.natDegree : ℕ) : C⟮S.x⟯) ≠ 0 := by
    rw [← map_natCast (algebraMap C C⟮S.x⟯)]
    exact (map_ne_zero_iff _ (algebraMap C C⟮S.x⟯).injective).mpr hn
  have hc : (derivative m).coeff (S.F.natDegree - 1) ≠ 0 := by
    have hpos := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
    rw [coeff_derivative, Nat.sub_add_cancel hpos, ← hdeg, hmon.coeff_natDegree, one_mul, hdeg,
      Nat.cast_pred hpos, sub_add_cancel]
    exact hnx
  have hd1 : (derivative m).natDegree = S.F.natDegree - 1 :=
    le_antisymm ((natDegree_derivative_le m).trans (by rw [hdeg]))
      (le_natDegree_of_ne_zero hc)
  have hsep : m.Separable :=
    (separable_iff_derivative_ne_zero (minpoly.irreducible S.isIntegral)).mpr
      fun h ↦ hc (by rw [h, Polynomial.coeff_zero])
  rw [← hdeg] at h1 hd1
  rw [← hd1] at h1
  exact resultant_ne_zero _ _ hsep h1

lemma discR_ne_zero [CharZero C] : S.discR ≠ 0 :=
  S.discR_ne_zero_of (by exact_mod_cast S.natDegree_F_ne_zero)

/-- The coordinates of `z` in the basis `1, y, …, yⁿ⁻¹` over `C⟮x⟯`. -/
noncomputable def coords (z : C⟮S.x⟯⟮S.y⟯) (i : Fin S.F.natDegree) : C⟮S.x⟯ :=
  (IntermediateField.adjoin.powerBasis S.isIntegral).basis.repr z
    ⟨i, by rw [IntermediateField.adjoin.powerBasis_dim, S.natDegree_minpoly]; exact i.2⟩

lemma coords_spec (z : C⟮S.x⟯⟮S.y⟯) :
    z = ∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (S.coords z i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ) := by
  set pb := IntermediateField.adjoin.powerBasis S.isIntegral
  have hdim : pb.dim = S.F.natDegree := by
    rw [IntermediateField.adjoin.powerBasis_dim, S.natDegree_minpoly]
  have hgen : pb.gen = AdjoinSimple.gen C⟮S.x⟯ S.y := IntermediateField.adjoin.powerBasis_gen _
  have := pb.basis.sum_repr z
  conv_lhs => rw [← this]
  rw [← Equiv.sum_comp (finCongr hdim.symm)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [PowerBasis.coe_basis, hgen, Algebra.smul_def]
  rfl

lemma embG_coords (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (z : C⟮S.x⟯⟮S.y⟯) :
    S.embG g hg Y hY z = ∑ i, S.embXG g hg (S.coords z i) * Y ^ (i : ℕ) := by
  conv_lhs => rw [S.coords_spec z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, S.embG_algebraMap, S.embG_gen]

/-- The polynomial `∑ ĝ(Zᵢ) Yⁱ`. -/
noncomputable def coordPoly (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (z : C⟮S.x⟯⟮S.y⟯) : (LaurentSeries K)[X] :=
  ∑ i : Fin S.F.natDegree, Polynomial.C (S.embXG g hg (S.coords z i)) * X ^ (i : ℕ)

lemma coordPoly_coeff (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (z : C⟮S.x⟯⟮S.y⟯) (i : Fin S.F.natDegree) :
    (S.coordPoly g hg z).coeff i = S.embXG g hg (S.coords z i) := by
  classical
  rw [coordPoly, finsetSum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hji
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h ↦ hji (Fin.ext h.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma coordPoly_natDegree (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (z : C⟮S.x⟯⟮S.y⟯) : (S.coordPoly g hg z).natDegree < S.F.natDegree := by
  have hn := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := S.F.natDegree - 1)
    fun i _ ↦ ?_) (by omega)
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  have := i.2; omega

lemma coordPoly_eval (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (z : C⟮S.x⟯⟮S.y⟯) :
    (S.coordPoly g hg z).eval Y = S.embG g hg Y hY z := by
  rw [S.embG_coords g hg Y hY z, coordPoly, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]

lemma root_of_split (g : C[X] →+* LaurentSeries K) (r : Fin S.F.natDegree → LaurentSeries K)
    (hsplit : S.F.map g = ∏ k, (X - Polynomial.C (r k))) (k : Fin S.F.natDegree) :
    (S.F.map g).eval (r k) = 0 := by
  rw [hsplit, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)

/-- **Coordinates from branch values**: if all branch values of `z` have no coefficient below
`Tᵐ` and the roots `rₖ` none below `Tᵇ` (`b ≤ 0`), then `g(discR) · ĝ(Zᵢ)` has none below
`T^{m + ((n−1)² + (n−1)) b}`. -/
theorem coord_lowerBd (hdisc : S.discR ≠ 0) (g : C[X] →+* LaurentSeries K)
    (hg : Function.Injective g) (r : Fin S.F.natDegree → LaurentSeries K)
    (hsplit : S.F.map g = ∏ k, (X - Polynomial.C (r k))) (b : ℤ) (hb : b ≤ 0)
    (hr : ∀ k, LowerBd (r k) b)
    (z : C⟮S.x⟯⟮S.y⟯) (m : ℤ)
    (hz : ∀ k, LowerBd (S.embG g hg (r k) (S.root_of_split g r hsplit k) z) m)
    (i : Fin S.F.natDegree) :
    LowerBd (g S.discR * S.embXG g hg (S.coords z i))
      (m + (((S.F.natDegree - 1) * (S.F.natDegree - 1) + (S.F.natDegree - 1) : ℕ) : ℤ) * b) := by
  classical
  have hD := S.discR_map g r hsplit
  have hne : ∏ j, (derivative (∏ k, (X - Polynomial.C (r k)))).eval (r j) ≠ 0 := by
    rw [← hD]; exact (map_ne_zero_iff _ hg).mpr hdisc
  have hid := interp_identity r hne (S.coordPoly g hg z) (S.coordPoly_natDegree g hg z)
  have hc := congrArg (fun p ↦ p.coeff (i : ℕ)) hid
  simp only [coeff_C_mul] at hc
  rw [S.coordPoly_coeff, ← hD] at hc
  rw [hc]
  have hcard : ∀ j : Fin S.F.natDegree, (Finset.univ.erase j).card = S.F.natDegree - 1 := fun j ↦ by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hG : ∀ k, LowerBd ((derivative (∏ k, (X - Polynomial.C (r k)))).eval (r k))
      ((S.F.natDegree - 1 : ℕ) * b) := by
    intro k
    rw [eval_derivative_prod]
    have := polyLB_prod (Finset.univ.erase k) (fun j ↦ Polynomial.C (r k - r j))
      (fun j _ ↦ polyLB_C ((hr k).sub (hr j))) 0
    rwa [← map_prod, coeff_C_zero, hcard] at this
  refine polyLB_sum _ _ (fun j _ ↦ ?_) (i : ℕ)
  have h1 : LowerBd ((S.coordPoly g hg z).eval (r j) *
      ∏ k ∈ Finset.univ.erase j, (derivative (∏ k, (X - Polynomial.C (r k)))).eval (r k))
      (m + ((S.F.natDegree - 1 : ℕ) * ((S.F.natDegree - 1 : ℕ) * b))) := by
    rw [S.coordPoly_eval g hg (r j) (S.root_of_split g r hsplit j)]
    have h2 := polyLB_prod (Finset.univ.erase j)
      (fun k ↦ Polynomial.C ((derivative (∏ k, (X - Polynomial.C (r k)))).eval (r k)))
      (fun k _ ↦ polyLB_C (hG k)) 0
    rw [← map_prod, coeff_C_zero, hcard] at h2
    exact (hz j).mul h2
  have := (polyLB_C h1).mul (polyLB_prod (Finset.univ.erase j) _ fun k _ ↦
    polyLB_X_sub_C (hr k) hb)
  convert this using 1
  rw [hcard]
  push_cast
  ring

end CurveData

end CoordCurve

end Curves
