import RischTragerBronstein.Curves.Invert

/-!
# The branches above infinity, and functions without poles

* `infSub_reflect`: `P(T⁻ᴺ) = rev_M(P)(Tᴺ) · T^{−NM}` for `deg P ≤ M`;
* `F_map_infSub`: `F(T⁻ᴺ, Y)` is the root-scaling of `F'(Tᴺ, Y)` (`F'` the inverted equation);
* `branches_inf`: `F(T⁻ᴺ, Y) = ∏ⱼ (Y − Yⱼ)` with `Yⱼ ∈ T^{−kN} K⟦T⟧`;
* `M_map_split`: along any split fibre, the monic equation `M` of `integral_of_regular_data`
  becomes `∏ⱼ (Z − fⱼ)` (the branch values of `f`);
* `algebraic_of_regular`: a function without poles along all branches (finite and infinite)
  satisfies a monic equation with constant coefficients.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential

section InfSub

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

lemma infSub_reflect (N : ℕ) (P : C[X]) (M : ℕ) (hM : P.natDegree ≤ M) :
    infSub (K := K) N P = branchSub N 0 (reflect M P) * single (-(N * M : ℤ)) 1 := by
  let _ : Invertible (single (-(N : ℤ)) (1 : K)) :=
    ⟨single (N : ℤ) 1, by simp [single_mul_single], by simp [single_mul_single]⟩
  have h := eval₂_reflect_mul_pow ((HahnSeries.C).comp (algebraMap C K))
    (single (-(N : ℤ)) (1 : K)) M P hM
  rw [show ⅟(single (-(N : ℤ)) (1 : K)) = single (N : ℤ) 1 from rfl, eval₂_single_nat,
    single_pow, one_pow] at h
  rw [infSub, coe_eval₂RingHom, ← h, branchSub_apply, map_zero, zero_add]
  congr 2
  rw [nsmul_eq_mul]; push_cast; ring

variable {R : Type*} [CommRing R] [IsDomain R]

lemma list_scaleRoots (l : List R) (s : R) :
    ((l.map fun r ↦ X - Polynomial.C r).prod).scaleRoots s =
      (l.map fun r ↦ X - Polynomial.C (r * s)).prod := by
  induction l with
  | nil => simp
  | cons r l ih =>
    rw [List.map_cons, List.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots,
      List.map_cons, List.prod_cons]

end InfSub

section Branches

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

/-- `F(T⁻ᴺ, Y)` is the root scaling of `F'(Tᴺ, Y)` by `T^{−kN}`. -/
lemma F_map_infSub (F : C[X][X]) (hF : F.Monic) (k : ℕ) (hk : ∀ i, (F.coeff i).natDegree ≤ k)
    (N : ℕ) :
    F.map (infSub (K := K) N) =
      ((invF F 0 k).map (branchSub N 0)).scaleRoots (single (-(k * N : ℤ)) 1) := by
  refine Polynomial.ext fun i ↦ ?_
  rw [coeff_map, coeff_scaleRoots, coeff_map, (invF_monic hF 0 k).natDegree_map,
    invF_natDegree hF, invF_coeff]
  split_ifs with hi
  · rw [taylor_zero, single_pow, one_pow,
      infSub_reflect N _ (k * (F.natDegree - i)) (by
        rcases lt_or_eq_of_le hi with h | h
        · exact (hk i).trans (Nat.le_mul_of_pos_right k (by omega))
        · rw [h, hF.coeff_natDegree, natDegree_one]; exact Nat.zero_le _)]
    congr 2
    rw [nsmul_eq_mul]; push_cast; ring
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), map_zero, map_zero, zero_mul]

variable [IsAlgClosed K] [CharZero K]

/-- **The branches above infinity**: `F(T⁻ᴺ, Y) = ∏ⱼ (Y − Yⱼ)`, `Yⱼ ∈ T^{−kN} K⟦T⟧`. -/
theorem split_inf (F : C[X][X]) (hF : F.Monic) (k : ℕ) (hk : ∀ i, (F.coeff i).natDegree ≤ k) :
    ∃ N, N ≠ 0 ∧ ∃ l : List (LaurentSeries K), l.length = F.natDegree ∧
      F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod ∧
      ∀ r ∈ l, ∃ w : PowerSeries K, r = ofPowerSeries ℤ K w * single (-(k * N : ℤ)) 1 := by
  obtain ⟨N, hN, l0, hl0, hsplit⟩ := split_at (K := K) (invF F 0 k) (invF_monic hF 0 k) 0
  refine ⟨N, hN, l0.map fun w ↦ ofPowerSeries ℤ K w * single (-(k * N : ℤ)) 1,
    by rw [List.length_map, hl0, invF_natDegree hF], ?_, ?_⟩
  · have e : (l0.map fun r ↦ X - Polynomial.C (ofPowerSeries ℤ K r)) =
        ((l0.map (ofPowerSeries ℤ K)).map fun r ↦ X - Polynomial.C r) := by
      rw [List.map_map]; rfl
    rw [F_map_infSub F hF k hk N, hsplit, e, list_scaleRoots, List.map_map, List.map_map]
    rfl
  · intro r hr
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
    exact ⟨w, rfl⟩

end Branches

section Const

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Along a split fibre**, the monic equation `M` of `f` becomes `∏ⱼ (Z − fⱼ)`. -/
theorem M_map_split (f : C⟮S.x⟯⟮S.y⟯) (W : C[X][X]) (Q : C[X]) (M : C[X][X]) (hQ : Q ≠ 0)
    (hWQ : (f : L) * aeval S.x Q = S.evXY W)
    (hPM : S.resP W Q = Polynomial.C (Q ^ S.F.natDegree) * M)
    (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (l : List (LaurentSeries K))
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) :
    ∃ v : LaurentSeries K → LaurentSeries K,
      (∀ r (hr : r ∈ l), v r = S.embG g hg r (S.root_of_mem hl hr) f) ∧
      M.map g = (l.map fun r ↦ X - Polynomial.C (v r)).prod := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : LaurentSeries K → LaurentSeries K,
      ∀ r (hr : r ∈ l), v r = S.embG g hg r (S.root_of_mem hl hr) f :=
    ⟨fun r ↦ if hr : r ∈ l then S.embG g hg r (S.root_of_mem hl hr) f else 0,
      fun r hr ↦ by simp only [hr, dite_true]⟩
  refine ⟨v, hv, ?_⟩
  have hlen : l.length = S.F.natDegree := by
    have := congrArg natDegree hl
    rw [S.monic.natDegree_map, (list_prod_X_sub_C l).2] at this
    exact this.symm
  have h1 := congrArg (Polynomial.map g) hPM
  have h2 := list_prod_scale l (g Q) (fun r ↦ (W.map g).eval r) v (fun r hr ↦ by
      rw [hv r hr]; exact S.eval_W_branch g hg r _ f W Q hWQ)
  rw [S.resP_map g l hl W Q, h2, Polynomial.map_mul, Polynomial.map_C, hlen] at h1
  have hQ0 : g Q ^ S.F.natDegree ≠ 0 := pow_ne_zero _ ((map_ne_zero_iff _ hg).mpr hQ)
  refine Polynomial.ext fun j ↦ ?_
  have h3 := congrArg (fun P ↦ P.coeff j) h1
  rw [coeff_C_mul, coeff_C_mul, map_pow] at h3
  exact (mul_left_cancel₀ hQ0 h3).symm

/-- **Regularity along all branches above infinity.** -/
def RegularInf (K : Type*) [Field K] [Algebra C K] (f : C⟮S.x⟯⟮S.y⟯) : Prop :=
  ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l),
    0 ≤ (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
      (S.root_of_mem hl hr) f).order

/-- A bound on the degrees of the coefficients of `F`. -/
noncomputable def degB : ℕ := ∑ i ∈ Finset.range (S.F.natDegree + 1), (S.F.coeff i).natDegree

lemma degB_spec : ∀ i, (S.F.coeff i).natDegree ≤ S.degB := by
  intro i
  by_cases hi : i ≤ S.F.natDegree
  · exact Finset.single_le_sum (f := fun i ↦ (S.F.coeff i).natDegree) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), natDegree_zero]; exact Nat.zero_le _

/-- A complete branch system above infinity. -/
def HasBranchesInf (K : Type*) [Field K] [Algebra C K] : Prop :=
  ∃ N, N ≠ 0 ∧ ∃ l : List (LaurentSeries K), l.length = S.F.natDegree ∧
    S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod

variable [IsAlgClosed K]

/-- **A function without poles is algebraic over the constants** (given branch systems). -/
theorem algebraic_of_regularG (hB : S.HasBranches K) (hBI : S.HasBranchesInf K)
    (f : C⟮S.x⟯⟮S.y⟯) (hfin : S.RegularFinite K f)
    (hinf : S.RegularInf K f) : ∃ M0 : C[X], M0.Monic ∧ aeval (f : L) M0 = 0 := by
  classical
  obtain ⟨W, Q, M, hQ, hWQ, hM, hPM, hev⟩ := S.integral_of_regular_dataG hB f hfin
  obtain ⟨N, hN, l, -, hl⟩ := hBI
  have hinj := infSub_injective (C := C) (K := K) N (Nat.pos_of_ne_zero hN)
  obtain ⟨v, hv, hMg⟩ := S.M_map_split f W Q M hQ hWQ hPM (infSub (K := K) N) hinj l hl
  have hconst : ∀ j, (M.coeff j).natDegree = 0 := by
    intro j
    by_cases h0 : M.coeff j = 0
    · rw [h0, natDegree_zero]
    have hord : 0 ≤ (infSub (K := K) N (M.coeff j)).order := by
      have := congrArg (fun P ↦ P.coeff j) hMg
      simp only [coeff_map] at this
      rw [this, show (l.map fun r ↦ (X - Polynomial.C (v r) : (LaurentSeries K)[X])) =
        ((l.map v).map fun s ↦ X - Polynomial.C s) by rw [List.map_map]; rfl]
      refine order_coeff_prod_nonneg (K := K) _ (fun s hs ↦ ?_) j
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
      rw [hv r hr]
      exact hinf N hN l hl r hr
    rw [order_infSub N (Nat.pos_of_ne_zero hN) _ h0] at hord
    have h1 : ((N * (M.coeff j).natDegree : ℕ) : ℤ) ≤ 0 := by push_cast; linarith
    have h2 : N * (M.coeff j).natDegree = 0 := by omega
    exact (mul_eq_zero.mp h2).resolve_left hN
  refine ⟨M.map Polynomial.constantCoeff, hM.map _, ?_⟩
  have hMC : M = (M.map Polynomial.constantCoeff).map Polynomial.C := by
    refine Polynomial.ext fun j ↦ ?_
    rw [coeff_map, coeff_map, Polynomial.constantCoeff_apply]
    exact eq_C_of_natDegree_eq_zero (hconst j)
  rw [hMC, Polynomial.map_map] at hev
  rw [aeval_def, ← eval_map]
  convert hev using 2
  ext c
  simp

variable [CharZero K]

/-- In characteristic `0`, the branch system above infinity exists. -/
theorem hasBranchesInf : S.HasBranchesInf K := by
  obtain ⟨N, hN, l, hl, hs, -⟩ := split_inf (K := K) S.F S.monic S.degB S.degB_spec
  exact ⟨N, hN, l, hl, hs⟩

/-- **A function without poles is algebraic over the constants.** -/
theorem algebraic_of_regular (f : C⟮S.x⟯⟮S.y⟯) (hfin : S.RegularFinite K f)
    (hinf : S.RegularInf K f) : ∃ M0 : C[X], M0.Monic ∧ aeval (f : L) M0 = 0 :=
  S.algebraic_of_regularG S.hasBranches S.hasBranchesInf f hfin hinf

end CurveData

end Const

end Curves
