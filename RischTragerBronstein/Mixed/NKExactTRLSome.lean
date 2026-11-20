import RischTragerBronstein.Mixed.NKExactTGL
import RischTragerBronstein.Mixed.NKExactTRESome

/-!
# The parametric tests `exactTRL`, `exactTREL` answer in their regimes

Same hypotheses as `exactTR_isSome`, `exactTRE_isSome` (the parameters `gs` add nothing: their
gcd-reduced codes have non-zero denominators).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable {m} in
set_option maxHeartbeats 1600000 in
/-- **`exactTRL` answers in its regime.** -/
theorem exactTRL_isSome (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
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
    (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (Mval : ℕ → ℕ → T.F (m + 1))
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
    (exactTRL Fc ks m η lim r P Tc Ti f gs).isSome := by
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
  have hf' : ∀ c ∈ (vecF Fc ks m f Ti N).map (redC Fc ks m) ++
      ((gs.map fun g ↦ vecF Fc ks m g Ti N).map fun l ↦ l.map (redC Fc ks m)).flatten,
      GPoly.toPoly M c.2 ≠ 0 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨c0, -, rfl⟩ := List.mem_map.mp hc
      exact T.redC_den_ne_zero m h1 c0
    · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
      obtain ⟨l', -, rfl⟩ := List.mem_map.mp hl
      obtain ⟨c0, -, rfl⟩ := List.mem_map.mp hcl
      exact T.redC_den_ne_zero m h1 c0
  have hWR := T.exactWRL_isSome h1 hm hk htr lim hlim hη N hN Mc' ((vecF Fc ks m f Ti N).map
    (redC Fc ks m)) ((gs.map fun g ↦ vecF Fc ks m g Ti N).map fun l ↦ l.map (redC Fc ks m)) r hent
    hprop' hf'
  -- unfold `exactTR`
  have hcheck : ¬((!(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || decide (N = 0)) ||
      !(prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
        (fun i j ↦ (Ti.getD i []).getD j O1.zero) &&
        prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
        (fun i j ↦ (Tc.getD i []).getD j O1.zero))) = true := by
    rw [hPc, hok.1, hok.2]; simp [hN]
  unfold exactTRL exactTGL
  simp only
  rw [if_neg hcheck, hd]
  exact hWR


section E

variable {m : ℕ} (h1 : T.Tr (m + 1))

set_option maxHeartbeats 3200000 in
/-- **`exactTREL` answers in its regime.** -/
theorem exactTREL_isSome (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hb0 : (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) ≠ 0)
    (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ))
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
    (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) (Mval : ℕ → ℕ → T.F (m + 1))
    (hMval : ∀ i < P.length - 1, (∑ k ∈ Finset.range (P.length - 1), ((T.MPr (m + 1) h1).sem
        ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : L) * θ ^ k)′ =
      ∑ j ∈ Finset.range (P.length - 1), (Mval i j : L) *
        ∑ k ∈ Finset.range (P.length - 1), ((T.MPr (m + 1) h1).sem
          ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : L) * θ ^ k)
    (lam0 : ℕ → ℕ → ℚ)
    (hsq : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A S : (T.F m)[X], Squarefree S ∧
      S.coeff 0 ≠ 0 ∧ A.coeff 0 = (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) *
        (lam0 j i : T.F m) * S.coeff 0 ∧ Mval i j = T.phi m A / T.phi m S)
    (hN0 : 0 < N0) (hP0 : aeval (Matrix.of fun i j : Fin (P.length - 1) ↦ lam0 i j)
      (Lagrange.nodal (Finset.range N0) (annNodes N0)) = 0)
    (hC1 : ∀ i < P.length - 1, ∀ j < P.length - 1, ∑ k ∈ Finset.range (P.length - 1),
      qget C i k * qget Ci k j = if i = j then 1 else 0)
    (hC2 : ∀ i < P.length - 1, ∀ j < P.length - 1, ∑ k ∈ Finset.range (P.length - 1),
      qget Ci i k * qget C k j = if i = j then 1 else 0)
    (lamI : ℕ → ℕ → ℚ)
    (hlim : ∀ k < P.length - 1, ∀ l < P.length - 1, ∃ A B : (T.F m)[X], B ≠ 0 ∧
      A.natDegree ≤ B.natDegree ∧
      A.coeff B.natDegree = (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * (lamI l k : T.F m) *
        B.leadingCoeff ∧
      ∑ i ∈ Finset.range (P.length - 1), ∑ j ∈ Finset.range (P.length - 1),
        (qget C k i : T.F (m + 1)) * (T.tau m ^ (r j - r i) * Mval i j -
          (if i = j then (r i : T.F (m + 1)) *
            T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a))) else 0)) *
          (qget Ci j l : T.F (m + 1)) = T.phi m A / T.phi m B)
    (htri : ∀ i < P.length - 1, ∀ j < P.length - 1, j < i → lamI i j = 0) :
    (exactTREL Fc ks m a rdeD r N0 C Ci P Tc Ti f gs).isSome := by
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
  have hc : ∀ i < N, ∀ j < N, (Mc'.getD i []).getD j O1.zero =
      redC Fc ks m ((MW.getD i []).getD j O1.zero) := fun i hi j hj ↦
    redMat_entry (Fc := Fc) (ks := ks) m P dθ Tc Ti N i j hi hj
  have hcs : ∀ i < N, ∀ j < N, M1.sem ((Mc'.getD i []).getD j O1.zero) = Mval i j :=
    fun i hi j hj ↦ by rw [hc i hi j hj, T.sem_redC m h1 htr, hsem i hi j hj]
  have hent : ∀ i < N, ∀ j < N, Squarefree (GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).2) ∧
      (GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).2).coeff 0 ≠ 0 := by
    intro i hi j hj
    obtain ⟨A, S, hS, hS0, -, hAS⟩ := hsq i hi j hj
    rw [hc i hi j hj]
    refine ⟨T.redC_den_squarefree m h1 htr _ A S hS (by rw [hsem i hi j hj]; exact hAS), ?_⟩
    intro h0
    have hdv := T.redC_den_dvd h1 htr _ A S hS.ne_zero (by rw [hsem i hi j hj]; exact hAS)
    rw [← X_dvd_iff] at h0
    exact hS0 (X_dvd_iff.mp (h0.trans hdv))
  have hz : ∀ i < N, ∀ j < N, (GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).1).coeff 0 =
      M.sem ((MO Fc ks m).deriv a) * (lam0 j i : T.F m) *
        (GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).2).coeff 0 := by
    intro i hi j hj
    obtain ⟨A, S, -, hS0, hA0, hAS⟩ := hsq i hi j hj
    exact T.zero_of_sem h1 htr _ (by rw [hc i hi j hj]; exact T.redC_den_ne_zero m h1 _) A S hS0 _
      hA0 (by rw [hcs i hi j hj]; exact hAS)
  have hlim' : ∀ k < N, ∀ l < N, ∃ A B : (T.F m)[X], B ≠ 0 ∧ A.natDegree ≤ B.natDegree ∧
      A.coeff B.natDegree = M.sem ((MO Fc ks m).deriv a) * (lamI l k : T.F m) * B.leadingCoeff ∧
      M1.sem (((conjM Fc ks m N C (rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc' r)
        Ci).getD k []).getD l O1.zero) = T.phi m A / T.phi m B := by
    intro k hk l hl
    obtain ⟨A, B, hB, hAB, hcB, hv⟩ := hlim k hk l hl
    refine ⟨A, B, hB, hAB, hcB, ?_⟩
    rw [T.sem_conjM h1 N C Ci _ k l hk hl, ← hv]
    refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rw [T.sem_rescaleME h1 htr _ N Mc' r i j hi' hj' (by
      rw [hc i hi' i hi']
      exact fun h0 ↦ T.redC_den_ne_zero m h1 _ (T.phi_injective htr (by rw [h0, map_zero]))),
      hcs i hi' j hj']
  have hf' : ∀ c ∈ (vecF Fc ks m f Ti N).map (redC Fc ks m) ++
      ((gs.map fun g ↦ vecF Fc ks m g Ti N).map fun l ↦ l.map (redC Fc ks m)).flatten,
      GPoly.toPoly M c.2 ≠ 0 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨c0, -, rfl⟩ := List.mem_map.mp hc
      exact T.redC_den_ne_zero m h1 c0
    · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
      obtain ⟨l', -, rfl⟩ := List.mem_map.mp hl
      obtain ⟨c0, -, rfl⟩ := List.mem_map.mp hcl
      exact T.redC_den_ne_zero m h1 c0
  have hWRE := T.exactWREL_isSome h1 hm hk htr rdeD hb0 N hN Mc' ((vecF Fc ks m f Ti N).map
    (redC Fc ks m)) ((gs.map fun g ↦ vecF Fc ks m g Ti N).map fun l ↦ l.map (redC Fc ks m)) r N0 C Ci
    hent lam0 hz hN0 hP0 hC1 hC2 lamI hlim' htri hf'
  -- unfold `exactTRE`
  have hcheck : ¬((!(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || decide (N = 0)) ||
      !(prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
        (fun i j ↦ (Ti.getD i []).getD j O1.zero) &&
        prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
        (fun i j ↦ (Tc.getD i []).getD j O1.zero))) = true := by
    rw [hPc, hok.1, hok.2]; simp [hN]
  unfold exactTREL exactTGL
  simp only
  rw [if_neg hcheck, hd]
  exact hWRE


end E

end MTower

end Curves.MT
