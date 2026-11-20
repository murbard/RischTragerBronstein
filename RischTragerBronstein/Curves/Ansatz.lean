import RischTragerBronstein.Curves.Coords

/-!
# A finite-dimensional ansatz for functions with bounded poles

If `z ∈ C⟮x⟯⟮y⟯` has, along every branch above every finite `a`, a pole of order at most
`N · mult_a(P)` (in the branch parameter, `x = a + Tᴺ`), and a pole of order at most `N · B`
along every branch above infinity (`x = T⁻ᴺ`), then (`ansatz`)

  `z · discR(x) P(x) = W(x, y)`,  `W = ∑_{i<n} Wᵢ(x) Yⁱ`,  `deg Wᵢ ≤ deg P + B + c · degB`

with `c = (n − 1)² + (n − 1)`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Split

variable {C K : Type*} [Field C] [Field K]

lemma split_fin (F : C[X][X]) (g : C[X] →+* LaurentSeries K) (l : List (LaurentSeries K))
    (hl : l.length = F.natDegree) (hsplit : F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) :
    ∃ r : Fin F.natDegree → LaurentSeries K, (∀ k, r k ∈ l) ∧
      F.map g = ∏ k, (X - Polynomial.C (r k)) := by
  refine ⟨fun k ↦ l[Fin.cast hl.symm k], fun k ↦ List.getElem_mem _, ?_⟩
  rw [hsplit, ← Fin.prod_univ_fun_getElem]
  exact (Fintype.prod_equiv (finCongr hl) _ _ (fun k ↦ rfl))

end Split

section Ansatz

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Polynomials from regularity** in `C⟮x⟯`. -/
theorem poly_of_branch_regular [IsAlgClosed K] (q : C⟮S.x⟯)
    (h : ∀ a : K, ∃ N, ∃ hN : N ≠ 0,
      LowerBd (S.embXG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) q) 0) :
    ∃ W : C[X], (letI := algebraAdjoinSimple (F := C) S.x; algebraMap C[X] C⟮S.x⟯ W) = q := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  obtain ⟨⟨A, B⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors C[X]) q
  have hB : (B : C[X]) ≠ 0 := nonZeroDivisors.ne_zero B.2
  by_cases hA : A = 0
  · refine ⟨0, ?_⟩
    show _ = IsLocalization.mk' C⟮S.x⟯ A B
    rw [hA, IsLocalization.mk'_zero, map_zero]
  have hdvd : (B : C[X]) ∣ A := by
    refine dvd_of_branch_order (K := K) A B hB fun a ↦ ?_
    obtain ⟨N, hN, hlb⟩ := h a
    refine ⟨N, hN, ?_⟩
    have hinj := branchSub_injective (C := C) (K := K) N (Nat.pos_of_ne_zero hN) a
    rw [embXG, IsFractionRing.lift_mk'] at hlb
    have hgB : branchSub N a (B : C[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hB
    have hgA : branchSub N a A ≠ 0 := (map_ne_zero_iff _ hinj).mpr hA
    set z := branchSub N a A / branchSub N a (B : C[X])
    have hz0 : z ≠ 0 := div_ne_zero hgA hgB
    have hzo : 0 ≤ z.order := by
      by_contra hneg
      push Not at hneg
      exact HahnSeries.coeff_order_eq_zero.not.mpr hz0 (hlb _ hneg)
    have hA' : branchSub N a A = z * branchSub N a (B : C[X]) := by
      rw [div_mul_cancel₀ _ hgB]
    rw [hA', HahnSeries.order_mul hz0 hgB]
    omega
  obtain ⟨W, hW⟩ := hdvd
  refine ⟨W, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, hW, map_mul, mul_comm]

lemma coords_mul (P : C[X]) (z : C⟮S.x⟯⟮S.y⟯) (i : Fin S.F.natDegree) :
    letI := algebraAdjoinSimple (F := C) S.x
    S.coords (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ P) * z) i =
      algebraMap C[X] C⟮S.x⟯ P * S.coords z i := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [coords, coords, ← Algebra.smul_def, map_smul]
  rfl

lemma lowerBd_branchSub [IsAlgClosed K] (N : ℕ) (hN : N ≠ 0) (a : K) (P : C[X]) (hP : P ≠ 0) :
    LowerBd (branchSub N a P) ((N * (P.map (algebraMap C K)).rootMultiplicity a : ℕ) : ℤ) := by
  intro k hk
  rw [← order_branchSub N (Nat.pos_of_ne_zero hN) a P hP] at hk
  exact HahnSeries.coeff_eq_zero_of_lt_order hk

/-- Pole bounds `N · mult_a(P)` along all branches above finite points. -/
def PoleBoundFin (K : Type*) [Field K] [Algebra C K] (z : C⟮S.x⟯⟮S.y⟯) (P : C[X]) : Prop :=
  ∀ (a : K) (N : ℕ) (hN : N ≠ 0) (r : Fin S.F.natDegree → LaurentSeries K)
    (hsplit : S.F.map (branchSub N a) = ∏ k, (X - Polynomial.C (r k))) (k : Fin S.F.natDegree),
    LowerBd (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) (r k)
      (S.root_of_split _ r hsplit k) z)
      (-((N * (P.map (algebraMap C K)).rootMultiplicity a : ℕ) : ℤ))

/-- Pole bounds `N · B` along all branches above infinity. -/
def PoleBoundInf (K : Type*) [Field K] [Algebra C K] (z : C⟮S.x⟯⟮S.y⟯) (B : ℕ) : Prop :=
  ∀ (N : ℕ) (hN : N ≠ 0) (r : Fin S.F.natDegree → LaurentSeries K)
    (hsplit : S.F.map (infSub N) = ∏ k, (X - Polynomial.C (r k))) (k : Fin S.F.natDegree),
    LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) (r k)
      (S.root_of_split _ r hsplit k) z) (-((N * B : ℕ) : ℤ))

variable [IsAlgClosed K]

/-- A branch system above infinity with root bounds `≥ −kB·N`. -/
def HasBranchesInfB (K : Type*) [Field K] [Algebra C K] (kB : ℕ) : Prop :=
  ∃ N, N ≠ 0 ∧ ∃ l : List (LaurentSeries K), l.length = S.F.natDegree ∧
    S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod ∧
      ∀ r ∈ l, ∃ w : PowerSeries K, r = ofPowerSeries ℤ K w * single (-(kB * N : ℤ)) 1

/-- **The finite part of the ansatz**: `discR · P · Zᵢ` is a polynomial. -/
theorem coords_polyG (hdisc : S.discR ≠ 0) (hB : S.HasBranches K) (z : C⟮S.x⟯⟮S.y⟯) (P : C[X]) (hP : P ≠ 0) (hz : S.PoleBoundFin K z P)
    (i : Fin S.F.natDegree) :
    ∃ W : C[X], (letI := algebraAdjoinSimple (F := C) S.x; algebraMap C[X] C⟮S.x⟯ W) =
      (letI := algebraAdjoinSimple (F := C) S.x;
        algebraMap C[X] C⟮S.x⟯ (S.discR * P) * S.coords z i) := by
  letI := algebraAdjoinSimple (F := C) S.x
  refine S.poly_of_branch_regular (K := K) _ fun a ↦ ?_
  obtain ⟨N, hN, l0, hl0, hsplit0⟩ := hB a
  obtain ⟨r, hrl, hsplit⟩ := split_fin S.F (branchSub N a) (l0.map (ofPowerSeries ℤ K))
    (by rw [List.length_map, hl0]) (by rw [hsplit0, List.map_map]; rfl)
  refine ⟨N, hN, ?_⟩
  have hinj := branchSub_injective (C := C) (K := K) N (Nat.pos_of_ne_zero hN) a
  have hr : ∀ k, LowerBd (r k) 0 := fun k ↦ by
    obtain ⟨w, -, hw⟩ := List.mem_map.mp (hrl k)
    rw [← hw]; exact lowerBd_ofPS w
  set Pz := algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ P) * z
  have hPz : ∀ k, LowerBd (S.embG (branchSub N a) hinj (r k) (S.root_of_split _ r hsplit k) Pz) 0 :=
    fun k ↦ by
      rw [map_mul, S.embG_algebraMap, S.embXG_algebraMap]
      have := (lowerBd_branchSub N hN a P hP).mul (hz a N hN r hsplit k)
      rwa [add_neg_cancel] at this
  have h := S.coord_lowerBd hdisc (branchSub N a) hinj r hsplit 0 le_rfl hr Pz 0 hPz i
  rw [mul_zero, add_zero, S.coords_mul] at h
  simp only [map_mul, S.embXG_algebraMap] at h ⊢
  convert h using 1
  ring

/-- **Degree bounds at infinity.** -/
theorem coords_degreeG (hdisc : S.discR ≠ 0) (kB : ℕ) (hBI : S.HasBranchesInfB K kB)
    (z : C⟮S.x⟯⟮S.y⟯) (P : C[X]) (B : ℕ) (hz : S.PoleBoundInf K z B)
    (i : Fin S.F.natDegree) (W : C[X])
    (hW : (letI := algebraAdjoinSimple (F := C) S.x; algebraMap C[X] C⟮S.x⟯ W) =
      (letI := algebraAdjoinSimple (F := C) S.x;
        algebraMap C[X] C⟮S.x⟯ (S.discR * P) * S.coords z i)) :
    W.natDegree ≤ P.natDegree + B +
      ((S.F.natDegree - 1) * (S.F.natDegree - 1) + (S.F.natDegree - 1)) * kB := by
  letI := algebraAdjoinSimple (F := C) S.x
  by_cases hW0 : W = 0
  · rw [hW0, natDegree_zero]; exact Nat.zero_le _
  obtain ⟨N, hN, l, hl, hsplitl, hroots⟩ := hBI
  obtain ⟨r, hrl, hsplit⟩ := split_fin S.F (infSub N) l hl hsplitl
  have hinj := infSub_injective (C := C) (K := K) N (Nat.pos_of_ne_zero hN)
  have hr : ∀ k, LowerBd (r k) (-((kB * N : ℕ) : ℤ)) := fun k ↦ by
    obtain ⟨w, hw⟩ := hroots (r k) (hrl k)
    rw [hw, mul_comm]
    have := (lowerBd_single (-((kB : ℤ) * N)) (1 : K)).mul (lowerBd_ofPS w)
    rw [add_zero] at this
    push_cast
    exact this
  have h := S.coord_lowerBd hdisc (infSub N) hinj r hsplit _ (by push_cast; nlinarith) hr z _
    (hz N hN r hsplit) i
  have hP : LowerBd (infSub (K := K) N P) (-((N * P.natDegree : ℕ) : ℤ)) := by
    rw [infSub_eq]
    refine ((lowerBd_single _ (1 : K)).mul (lowerBd_ofPS _)).mono ?_
    push_cast; omega
  have hWx := congrArg (S.embXG (infSub N) hinj) hW
  rw [S.embXG_algebraMap, map_mul, S.embXG_algebraMap, map_mul] at hWx
  have hbd := hP.mul h
  rw [show infSub N P * (infSub N S.discR * S.embXG (infSub N) hinj (S.coords z i)) =
    infSub N S.discR * infSub N P * S.embXG (infSub N) hinj (S.coords z i) by ring, ← hWx] at hbd
  have hWne : infSub (K := K) N W ≠ 0 := (map_ne_zero_iff _ hinj).mpr hW0
  have hord := order_infSub (K := K) N (Nat.pos_of_ne_zero hN) W hW0
  have hle : ¬ (infSub (K := K) N W).order <
      -((N * P.natDegree : ℕ) : ℤ) + (-((N * B : ℕ) : ℤ) +
        (((S.F.natDegree - 1) * (S.F.natDegree - 1) + (S.F.natDegree - 1) : ℕ) : ℤ) *
          -((kB * N : ℕ) : ℤ)) := fun hlt ↦
    HahnSeries.coeff_order_eq_zero.not.mpr hWne (hbd _ hlt)
  rw [hord] at hle
  push Not at hle
  have hN0 : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  set c := (S.F.natDegree - 1) * (S.F.natDegree - 1) + (S.F.natDegree - 1)
  have : (N : ℤ) * W.natDegree ≤ N * (P.natDegree + B + c * kB) := by
    push_cast at hle ⊢; nlinarith
  exact_mod_cast le_of_mul_le_mul_left this hN0

/-- **The ansatz**: `z · discR(x) P(x) = W(x, y)` with `deg_Y W < n` and bounded `deg_x`. -/
theorem ansatzG (hdisc : S.discR ≠ 0) (hB : S.HasBranches K) (kB : ℕ)
    (hBI : S.HasBranchesInfB K kB) (z : C⟮S.x⟯⟮S.y⟯) (P : C[X]) (hP : P ≠ 0) (B : ℕ)
    (hfin : S.PoleBoundFin K z P) (hinf : S.PoleBoundInf K z B) :
    ∃ W : C[X][X], W.natDegree < S.F.natDegree ∧
      (∀ j, (W.coeff j).natDegree ≤ P.natDegree + B +
        ((S.F.natDegree - 1) * (S.F.natDegree - 1) + (S.F.natDegree - 1)) * kB) ∧
      (z : L) * aeval S.x (S.discR * P) = S.evXY W := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  choose Wc hWc using fun i ↦ S.coords_polyG (K := K) hdisc hB z P hP hfin i
  have hn := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  set W : C[X][X] := ∑ i : Fin S.F.natDegree, Polynomial.C (Wc i) * X ^ (i : ℕ) with hWdef
  have hWcoeff : ∀ j, W.coeff j = if h : j < S.F.natDegree then Wc ⟨j, h⟩ else 0 := by
    intro j
    rw [hWdef, finsetSum_coeff]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨j, h⟩]
      · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
      · intro k _ hk
        rw [coeff_C_mul, coeff_X_pow, if_neg (fun h' ↦ hk (Fin.ext h'.symm)), mul_zero]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [coeff_C_mul, coeff_X_pow, if_neg (fun (h' : j = (k : ℕ)) ↦ h (h' ▸ k.2)), mul_zero]
  refine ⟨W, ?_, fun j ↦ ?_, ?_⟩
  · refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ ?_) (by omega :
      S.F.natDegree - 1 < S.F.natDegree)
    have : S.F.natDegree - 1 < j := by exact_mod_cast hj
    rw [hWcoeff, dif_neg (by omega)]
  · rw [hWcoeff]
    split_ifs with h
    · exact S.coords_degreeG (K := K) hdisc kB hBI z P B hinf ⟨j, h⟩ (Wc ⟨j, h⟩) (hWc ⟨j, h⟩)
    · rw [natDegree_zero]; exact Nat.zero_le _
  · have hz := congrArg (fun w : C⟮S.x⟯⟮S.y⟯ ↦ (w : L)) (S.coords_spec z)
    have hz' : (z : L) = ∑ i : Fin S.F.natDegree, ((S.coords z i : C⟮S.x⟯) : L) * S.y ^ (i : ℕ) :=
      by rw [hz]; simp
    rw [hz', Finset.sum_mul, evXY, hWdef, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul,
      eval_C, eval_pow, eval_X]
    have hc := congrArg (fun w : C⟮S.x⟯ ↦ (w : L)) (hWc i)
    simp only [IntermediateField.coe_mul, algebraMap_adjoinSimple] at hc
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hc]
    ring

variable [CharZero C] [CharZero K]

lemma hasBranchesInfB : S.HasBranchesInfB K S.degB := by
  obtain ⟨N, hN, l, hl, hs, hr⟩ := split_inf (K := K) S.F S.monic S.degB S.degB_spec
  exact ⟨N, hN, l, hl, hs, hr⟩

/-- **The finite part of the ansatz**: `discR · P · Zᵢ` is a polynomial. -/
theorem coords_poly (z : C⟮S.x⟯⟮S.y⟯) (P : C[X]) (hP : P ≠ 0) (hz : S.PoleBoundFin K z P)
    (i : Fin S.F.natDegree) :
    ∃ W : C[X], (letI := algebraAdjoinSimple (F := C) S.x; algebraMap C[X] C⟮S.x⟯ W) =
      (letI := algebraAdjoinSimple (F := C) S.x;
        algebraMap C[X] C⟮S.x⟯ (S.discR * P) * S.coords z i) :=
  S.coords_polyG S.discR_ne_zero S.hasBranches z P hP hz i

/-- **The ansatz**: `z · discR(x) P(x) = W(x, y)` with `deg_Y W < n` and bounded `deg_x`. -/
theorem ansatz (z : C⟮S.x⟯⟮S.y⟯) (P : C[X]) (hP : P ≠ 0) (B : ℕ) (hfin : S.PoleBoundFin K z P)
    (hinf : S.PoleBoundInf K z B) :
    ∃ W : C[X][X], W.natDegree < S.F.natDegree ∧
      (∀ j, (W.coeff j).natDegree ≤ P.natDegree + B +
        ((S.F.natDegree - 1) * (S.F.natDegree - 1) + (S.F.natDegree - 1)) * S.degB) ∧
      (z : L) * aeval S.x (S.discR * P) = S.evXY W :=
  S.ansatzG S.discR_ne_zero S.hasBranches S.degB S.hasBranchesInfB z P hP B hfin hinf

end CurveData

end Ansatz

end Curves
