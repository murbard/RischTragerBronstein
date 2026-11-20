import RischTragerBronstein.Mixed.NKExactTR

/-!
# `exactTR` answers in its regime

`matW`, `vecF`: the derivation matrix of `w = T θ` and the coordinates of `f` on codes (as computed
by `exactTG`); `basisW_facts`: `matW` is the derivation matrix of `w` and `w` is independent.

**`exactTR_isSome`**: `exactTR` answers when its checks pass (monic `P`, `T T⁻¹ = T⁻¹ T = 1`,
`θ′` computable) and the derivation matrix of `w = T θ` has squarefree denominators and a
rescaled matrix vanishing at infinity (`η` not a derivative).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The derivation matrix of `w = T θ` on codes (as in `exactTG`). -/
def matW (m : ℕ) (P dθ : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) (N : ℕ) :
    List (List (LC (m + 1))) :=
  (List.range N).map fun i ↦ (List.range N).map fun j ↦
    lsumC (MOr Fc ks (m + 1)) ((List.range N).map fun l ↦ (MOr Fc ks (m + 1)).mul
      ((MOr Fc ks (m + 1)).add ((MOr Fc ks (m + 1)).deriv ((Tc.getD i []).getD l (MOr Fc ks (m + 1)).zero))
        (lsumC (MOr Fc ks (m + 1)) ((List.range N).map fun k ↦ (MOr Fc ks (m + 1)).mul
          ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero)
          ((dPowC (MOr Fc ks (m + 1)) P dθ k).getD l (MOr Fc ks (m + 1)).zero))))
      ((Ti.getD l []).getD j (MOr Fc ks (m + 1)).zero))

/-- The coordinates of `f` in `w = T θ` on codes. -/
def vecF (m : ℕ) (f : List (LC (m + 1))) (Ti : List (List (LC (m + 1)))) (N : ℕ) :
    List (LC (m + 1)) :=
  (List.range N).map fun j ↦ lsumC (MOr Fc ks (m + 1)) ((List.range N).map fun k ↦
    (MOr Fc ks (m + 1)).mul (f.getD k (MOr Fc ks (m + 1)).zero) ((Ti.getD k []).getD j (MOr Fc ks (m + 1)).zero))

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ)

set_option maxHeartbeats 3200000 in
/-- **The basis `w = T θ`**: its derivation matrix is `matW` and it is independent. -/
lemma basisW_facts (h1 : T.Tr (m + 1)) (P : GPoly (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (N : ℕ) (hPm : (GPoly.toPoly (T.MPr (m + 1) h1) P).Monic)
    (hPdeg : (GPoly.toPoly (T.MPr (m + 1) h1) P).natDegree = N)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θ ^ j = 0 →
      ∀ j < N, a j = 0)
    (dθ : GPoly (LC (m + 1))) (hd : dThetaC (MOr Fc ks (m + 1)) P = some dθ)
    (Tc Ti : List (List (LC (m + 1))))
    (hok' : prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true ∧
      prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true) :
    (∀ i < N, (∑ k ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
        ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : L) * θ ^ k)′ =
      ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem (((matW Fc ks m P dθ Tc Ti N).getD i []).getD j
        (MOr Fc ks (m + 1)).zero) : L) *
        ∑ k ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
          ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : L) * θ ^ k) ∧
    (∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) *
        (∑ k ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
          ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : L) * θ ^ k) = 0 →
      ∀ j < N, a j = 0) := by
  classical
  set O1 := MOr Fc ks (m + 1) with hO1
  set M1 := T.MPr (m + 1) h1 with hM1
  -- the values
  set t : ℕ → ℕ → L := fun i j ↦ (M1.sem ((Tc.getD i []).getD j O1.zero) : L) with ht
  set s : ℕ → ℕ → L := fun i j ↦ (M1.sem ((Ti.getD i []).getD j O1.zero) : L) with hs
  have hts := T.prodIdC_sound m h1 N _ _ hok'.1
  have hst := T.prodIdC_sound m h1 N _ _ hok'.2
  set w : ℕ → L := fun i ↦ ∑ k ∈ Finset.range N, t i k * θ ^ k with hw
  have hθw : ∀ l < N, θ ^ l = ∑ j ∈ Finset.range N, s l j * w j := fun l hl ↦
    (sum_inv_basis N t s (fun k ↦ θ ^ k) hst l hl).symm
  have hθd := fun i ↦ T.deriv_θ_pow_sum m h1 θ P hP hPm dθ hd i
  rw [hPdeg] at hθd
  -- the derivation matrix of `w`
  have hwd : ∀ i < N, (w i)′ = ∑ j ∈ Finset.range N,
      ((M1.sem (((matW Fc ks m P dθ Tc Ti N).getD i []).getD j O1.zero) : T.F (m + 1)) : L) *
        w j := by
    intro i hi
    have hA : (w i)′ = ∑ l ∈ Finset.range N, (((M1.sem ((Tc.getD i []).getD l O1.zero))′ : T.F (m + 1)) +
        ∑ k ∈ Finset.range N, t i k * (T.Mθ m h1 P dθ k l : L)) * θ ^ l := by
      rw [hw, map_sum]
      simp only [Derivation.leibniz, smul_eq_mul]
      rw [Finset.sum_add_distrib]
      simp only [add_mul, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_comm]; rfl
      · rw [Finset.sum_congr rfl fun k hk ↦ by rw [hθd k, Finset.mul_sum], Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [hA]
    refine (Finset.sum_congr rfl fun l hl ↦ by rw [hθw l (Finset.mem_range.mp hl)]).trans ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [matW, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ (Finset.mem_range.mp hj),
      T.sem_lsum_range m h1]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [hO1, (T.MPr (m + 1) h1).sem_mul, (T.MPr (m + 1) h1).sem_add,
      (T.MPr (m + 1) h1).sem_deriv, T.sem_lsum_range m h1,
      IntermediateField.coe_mul, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum,
      MTower.coe_deriv, Mθ, ht, hs, Finset.sum_mul]
    ring
  -- independence of `w`
  have hindw : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * w j = 0 →
      ∀ j < N, a j = 0 := by
    intro a ha j hj
    have h0 : ∑ k ∈ Finset.range N, ((∑ i ∈ Finset.range N, a i * M1.sem ((Tc.getD i []).getD k O1.zero) :
        T.F (m + 1)) : L) * θ ^ k = 0 := by
      rw [← ha, hw]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hz := hind _ h0
    have := coords_inv N t s (fun i ↦ (a i : L)) hts j hj
    apply Subtype.ext
    change (a j : L) = 0
    rw [← this]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have := congrArg (fun z : T.F (m + 1) ↦ (z : L)) (hz k (Finset.mem_range.mp hk))
    push_cast at this
    simp only [ht]
    rw [this, zero_mul]
  exact ⟨hwd, hindw⟩

variable {m} in
/-- A code whose value is a proper fraction has a proper numerator/denominator pair. -/
lemma deg_lt_of_sem (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m)) (e : LC (m + 1))
    (he : GPoly.toPoly (T.MP m h1.of_succ) e.2 ≠ 0) (A B : (T.F m)[X]) (hB : B ≠ 0)
    (hAB : A.degree < B.degree) (hval : (T.MPr (m + 1) h1).sem e = T.phi m A / T.phi m B) :
    (GPoly.toPoly (T.MP m h1.of_succ) e.1).degree < (GPoly.toPoly (T.MP m h1.of_succ) e.2).degree := by
  set M := T.MP m h1.of_succ
  rw [MPr_sem, T.sem_MP_succ] at hval
  change T.phi m (GPoly.toPoly M e.1) / T.phi m (GPoly.toPoly M e.2) = _ at hval
  have hφe : T.phi m (GPoly.toPoly M e.2) ≠ 0 := fun h0 ↦ he (T.phi_injective htr (by rw [h0, map_zero]))
  have hφB : T.phi m B ≠ 0 := fun h0 ↦ hB (T.phi_injective htr (by rw [h0, map_zero]))
  rw [div_eq_div_iff hφe hφB] at hval
  have heq : GPoly.toPoly M e.1 * B = A * GPoly.toPoly M e.2 :=
    T.phi_injective htr (by rw [map_mul, map_mul, hval])
  by_cases h0 : GPoly.toPoly M e.1 = 0
  · rw [h0, degree_zero]; exact bot_lt_iff_ne_bot.mpr (by rwa [Ne, degree_eq_bot])
  have hA : A ≠ 0 := by
    rintro rfl; rw [zero_mul] at heq; exact h0 ((mul_eq_zero.mp heq).resolve_right hB)
  have hn := congrArg natDegree heq
  rw [natDegree_mul h0 hB, natDegree_mul hA he] at hn
  have hlt : A.natDegree < B.natDegree := by
    rwa [degree_eq_natDegree hA, degree_eq_natDegree hB, Nat.cast_lt] at hAB
  rw [degree_eq_natDegree h0, degree_eq_natDegree he, Nat.cast_lt]
  omega

lemma matW_row_length (P dθ : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) (N i : ℕ)
    (hi : i < N) : ((matW Fc ks m P dθ Tc Ti N).getD i []).length = N := by
  rw [matW, NestTower.getD_range_map _ _ hi, List.length_map, List.length_range]

lemma redMat_entry (P dθ : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) (N i j : ℕ)
    (hi : i < N) (hj : j < N) :
    ((((matW Fc ks m P dθ Tc Ti N).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j
      (MOr Fc ks (m + 1)).zero) =
      redC Fc ks m (((matW Fc ks m P dθ Tc Ti N).getD i []).getD j (MOr Fc ks (m + 1)).zero) := by
  rw [getD_map_map_redC (Fc := Fc) (ks := ks) m]
  have hl := matW_row_length (Fc := Fc) (ks := ks) m P dθ Tc Ti N i hi
  have hl' : ((matW Fc ks m P dθ Tc Ti N)[i]?.getD []).length = N := by
    rw [← List.getD_eq_getElem?_getD]; exact hl
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by rw [hl']; exact hj)]
  rfl

variable {m} in
set_option maxHeartbeats 1600000 in
/-- **`exactTR` answers in its regime.** -/
theorem exactTR_isSome (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m)) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h1.of_succ) lim)
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h1.of_succ).sem η) (r : ℕ → ℤ)
    (P : GPoly (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hPc : (MOr Fc ks (m + 1)).isZero ((MOr Fc ks (m + 1)).add
      (P.getD (P.length - 1) (MOr Fc ks (m + 1)).zero)
      ((MOr Fc ks (m + 1)).neg (MOr Fc ks (m + 1)).one)) = true)
    (hN : P.length - 1 ≠ 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (dθ : GPoly (LC (m + 1))) (hd : dThetaC (MOr Fc ks (m + 1)) P = some dθ)
    (Tc Ti : List (List (LC (m + 1))))
    (hok : prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true ∧
      prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true)
    (f : List (LC (m + 1))) (Mval : ℕ → ℕ → T.F (m + 1))
    (hMval : ∀ i < P.length - 1, (∑ k ∈ Finset.range (P.length - 1), ((T.MPr (m + 1) h1).sem
        ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : L) * θ ^ k)′ =
      ∑ j ∈ Finset.range (P.length - 1), (Mval i j : L) *
        ∑ k ∈ Finset.range (P.length - 1), ((T.MPr (m + 1) h1).sem
          ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : L) * θ ^ k)
    (hsq : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A S : (T.F m)[X], Squarefree S ∧
      Mval i j = T.phi m A / T.phi m S)
    (hprop : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A B : (T.F m)[X], B ≠ 0 ∧
      A.degree < B.degree ∧
      Mval i j * T.tau m ^ (r j - r i) - (if i = j then (r i : T.F (m + 1)) *
        T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem η)) / T.tau m else 0) =
        T.phi m A / T.phi m B) :
    (exactTR Fc ks m η lim r P Tc Ti f).isSome := by
  classical
  set O1 := MOr Fc ks (m + 1) with hO1
  set M1 := T.MPr (m + 1) h1 with hM1
  set N := P.length - 1 with hNdef
  -- `P` is monic of degree `N`
  have hlead : M1.sem (P.getD N O1.zero) = 1 := by
    have := (M1.isZero_iff _).mp hPc
    rw [M1.sem_add, M1.sem_neg, M1.sem_one, add_neg_eq_zero] at this
    exact this
  have hPdeg : (GPoly.toPoly M1 P).natDegree = N := by
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_toPoly_sem, List.getD_eq_default _ _ (by
        have : N < k := by exact_mod_cast hk
        omega), M1.sem_zero]
    · exact le_natDegree_of_ne_zero (by rw [coeff_toPoly_sem, hlead]; exact one_ne_zero)
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [Monic, leadingCoeff, hPdeg, coeff_toPoly_sem, hlead]
  obtain ⟨hwd, hindw⟩ := T.basisW_facts m h1 P θ hP N hPm hPdeg hind dθ hd Tc Ti hok
  -- the computed matrix is `Mval`
  have hsem : ∀ i < N, ∀ j < N,
      M1.sem (((matW Fc ks m P dθ Tc Ti N).getD i []).getD j O1.zero) = Mval i j := by
    intro i hi
    have h0 := hindw (fun j ↦ M1.sem (((matW Fc ks m P dθ Tc Ti N).getD i []).getD j O1.zero) -
      Mval i j) (by
        have := (hwd i hi).symm.trans (hMval i hi)
        push_cast
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]; exact this)
    intro j hj
    exact sub_eq_zero.mp (h0 j hj)
  set MW := matW Fc ks m P dθ Tc Ti N with hMW
  set Mc' := MW.map fun l ↦ l.map (redC Fc ks m) with hMc'
  set M := T.MP m h1.of_succ
  have hent : ∀ i < N, ∀ j < N, GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).2 ≠ 0 ∧
      Squarefree (GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).2) := by
    intro i hi j hj
    rw [hMc', redMat_entry (Fc := Fc) (ks := ks) m P dθ Tc Ti N i j hi hj]
    refine ⟨T.redC_den_ne_zero m h1 _, ?_⟩
    obtain ⟨A, S, hS, hAS⟩ := hsq i hi j hj
    exact T.redC_den_squarefree m h1 htr _ A S hS (by rw [hsem i hi j hj]; exact hAS)
  have hprop' : ∀ i < N, ∀ j < N,
      (GPoly.toPoly M (((rescaleM Fc ks m η N Mc' r).getD i []).getD j O1.zero).1).degree <
      (GPoly.toPoly M (((rescaleM Fc ks m η N Mc' r).getD i []).getD j O1.zero).2).degree := by
    intro i hi j hj
    obtain ⟨A, B, hB, hAB, hval⟩ := hprop i hi j hj
    have hc := redMat_entry (Fc := Fc) (ks := ks) m P dθ Tc Ti N i j hi hj
    have hcd := T.redC_den_ne_zero m h1 (((matW Fc ks m P dθ Tc Ti N).getD i []).getD j O1.zero)
    have hcs := T.sem_redC m h1 htr (((matW Fc ks m P dθ Tc Ti N).getD i []).getD j O1.zero)
    rw [hsem i hi j hj] at hcs
    rw [rescaleM, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ hj]
    rw [← hMc'] at hc
    split_ifs with hij
    · subst hij
      rw [hc]
      have hden : GPoly.toPoly M (addOverT Fc ks m (tpowL Fc ks m 0 (redC Fc ks m
          (((matW Fc ks m P dθ Tc Ti N).getD i []).getD i O1.zero)))
          ((MO Fc ks m).mul (mcst Fc ks m (-(r i : ℚ))) η)).2 ≠ 0 := by
        simp only [addOverT, GPoly.toPoly_mul, tpowL_zero_snd]
        exact mul_ne_zero hcd (by rw [T.toPoly_tX]; exact X_ne_zero)
      refine T.deg_lt_of_sem h1 htr _ hden A B hB hAB ?_
      rw [T.sem_addOverT m h1 htr _ _ (by
        rw [tpowL_zero_snd]
        exact fun h0 ↦ hcd (T.phi_injective htr (by rw [h0, map_zero]))),
        T.sem_tpowL m h1 htr, hcs, (T.MP m h1.of_succ).sem_mul, T.sem_mcst m h1.of_succ, ← hval,
        if_pos rfl, sub_self, zpow_zero]
      have : T.phi m (Polynomial.C (((-(r i : ℚ) : ℚ) : T.F m) * (T.MP m h1.of_succ).sem η)) =
          (-(r i : T.F (m + 1))) * T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem η)) := by
        rw [Polynomial.C_mul, map_mul]; congr 1; simp
      rw [this]; ring
    · rw [hc]
      refine T.deg_lt_of_sem h1 htr _ (T.tpowL_snd_ne_zero h1 _ _ hcd) A B hB hAB ?_
      rw [T.sem_tpowL m h1 htr, hcs, ← hval, if_neg hij, sub_zero]
  have hf' : ∀ c ∈ (vecF Fc ks m f Ti N).map (redC Fc ks m), GPoly.toPoly M c.2 ≠ 0 := by
    intro c hc
    obtain ⟨c0, -, rfl⟩ := List.mem_map.mp hc
    exact T.redC_den_ne_zero m h1 c0
  have hWR := T.exactWR_isSome h1 hm hk htr lim hlim hη N hN Mc' ((vecF Fc ks m f Ti N).map
    (redC Fc ks m)) r hent hprop' hf'
  -- unfold `exactTR`
  have hcheck : ¬((!(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || decide (N = 0)) ||
      !(prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
        (fun i j ↦ (Ti.getD i []).getD j O1.zero) &&
        prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
        (fun i j ↦ (Tc.getD i []).getD j O1.zero))) = true := by
    rw [hPc, hok.1, hok.2]; simp [hN]
  unfold exactTR exactTG
  simp only
  rw [if_neg hcheck, hd]
  exact hWR

end MTower

end Curves.MT
