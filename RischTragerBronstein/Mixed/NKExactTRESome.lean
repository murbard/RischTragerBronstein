import RischTragerBronstein.Mixed.NKExactTRE
import RischTragerBronstein.Mixed.NKExactWRESome
import RischTragerBronstein.Mixed.NKExactTRSome

/-!
# `exactTRE` answers in its regime

The value of an entry of `rescaleME` (`sem_rescaleME`) and of `conjM` (`sem_conjM`); the reduced
denominator of a code divides every denominator of its value (`redC_den_dvd`); a code whose value
has the limit `c` at `t = 0` has that limit on its numerator and denominator (`zero_of_sem`).

**`exactTRE_isSome`**: `exactTRE` answers when its checks pass (monic `P`, `T T⁻¹ = T⁻¹ T = 1`,
`θ′` computable) and the derivation matrix of `w = T θ` has squarefree denominators prime to `t`,
a rational limit `a′ Λ₀` at `t = 0` annihilated by `∏_{k<N₀} (X − k/N₀)`, and a conjugated
rescaled matrix `C (t^{rⱼ−rᵢ} Mᵢⱼ − δᵢⱼ rᵢ a′) C⁻¹` with an upper triangular rational limit
`a′ Λ∞` at infinity.
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

variable {m : ℕ} (h1 : T.Tr (m + 1))

lemma sem_qcstF (q : ℚ) : (T.MPr (m + 1) h1).sem (mcst Fc ks (m + 1) q) = (q : T.F (m + 1)) := by
  have := T.sem_qcst h1 (L := L) q
  exact_mod_cast this

/-- **The entries of `rescaleME`**: `t^{rⱼ−rᵢ} Mᵢⱼ − δᵢⱼ rᵢ a′`. -/
lemma sem_rescaleME (htr : Transcendental (T.F m) (T.ts m)) (bc : LC m) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (r : ℕ → ℤ) (i j : ℕ) (hi : i < N) (hj : j < N)
    (hden : T.phi m (GPoly.toPoly (T.MP m h1.of_succ)
      ((Mc.getD i []).getD i (MOr Fc ks (m + 1)).zero).2) ≠ 0) :
    (T.MPr (m + 1) h1).sem (((rescaleME Fc ks m bc N Mc r).getD i []).getD j (MOr Fc ks (m + 1)).zero) =
      T.tau m ^ (r j - r i) * (T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) -
        (if i = j then (r i : T.F (m + 1)) * T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem bc))
          else 0) := by
  rw [rescaleME, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ hj]
  split_ifs with hij
  · subst hij
    rw [T.sem_addConstC m h1 htr _ _ (by rw [tpowL_zero_snd]; exact hden),
      T.sem_tpowL m h1 htr, (T.MP m h1.of_succ).sem_mul, T.sem_mcst m h1.of_succ]
    have e1 : T.phi m (Polynomial.C (((-(r i : ℚ) : ℚ) : T.F m) *
        (T.MP m h1.of_succ).sem bc)) =
        ((-(r i : ℚ) : ℚ) : T.F (m + 1)) * T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem bc)) := by
      rw [Polynomial.C_mul, map_mul]; congr 1; simp
    rw [e1, sub_self, zpow_zero]
    push_cast
    ring
  · rw [T.sem_tpowL m h1 htr, sub_zero, mul_comm]

/-- **The entries of `conjM`**: `(C M C⁻¹)ₖₗ`. -/
lemma sem_conjM (N : ℕ) (C Ci : List (List ℚ)) (Mr : List (List (LC (m + 1)))) (k l : ℕ)
    (hk : k < N) (hl : l < N) :
    (T.MPr (m + 1) h1).sem (((conjM Fc ks m N C Mr Ci).getD k []).getD l (MOr Fc ks (m + 1)).zero) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (qget C k i : T.F (m + 1)) *
        (T.MPr (m + 1) h1).sem ((Mr.getD i []).getD j (MOr Fc ks (m + 1)).zero) *
          (qget Ci j l : T.F (m + 1)) := by
  rw [conjM, NestTower.getD_range_map _ _ hk, NestTower.getD_range_map _ _ hl, T.sem_lsum_range m h1]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [T.sem_lsum_range m h1]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [(T.MPr (m + 1) h1).sem_mul, (T.MPr (m + 1) h1).sem_mul, T.sem_qcstF h1, T.sem_qcstF h1]

/-- **The reduced denominator divides every denominator of the value.** -/
lemma redC_den_dvd (htr : Transcendental (T.F m) (T.ts m)) (c : LC (m + 1))
    (A S : (T.F m)[X]) (hS0 : S ≠ 0)
    (hval : (T.MPr (m + 1) h1).sem c = T.phi m A / T.phi m S) :
    GPoly.toPoly (T.MP m h1.of_succ) (redC Fc ks m c).2 ∣ S := by
  classical
  set M := T.MP m h1.of_succ
  have hφS : T.phi m S ≠ 0 := fun h0 ↦ hS0 (T.phi_injective htr (by rw [h0, map_zero]))
  by_cases hz : GPoly.isZero (MO Fc ks m) c.2 = true
  · rw [redC_of_zero Fc ks m c hz]
    show GPoly.toPoly M [(MO Fc ks m).one] ∣ S
    have : GPoly.toPoly M [(MO Fc ks m).one] = 1 := by simp [GPoly.toPoly, M.sem_one]
    rw [this]; exact one_dvd _
  · rw [redC_of_ne Fc ks m c hz]
    have hc2 : GPoly.toPoly M c.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
    obtain ⟨hg1, hg2⟩ := GPoly.egcd_dvd M c.1 c.2
    set g := (GPoly.egcd (MO Fc ks m) c.1 c.2).1
    have hg0 : GPoly.toPoly M g ≠ 0 := fun h0 ↦ hc2 (zero_dvd_iff.mp (h0 ▸ hg2))
    have e1 := GPoly.div_mul_of_dvd M c.1 g hg0 hg1
    have e2 := GPoly.div_mul_of_dvd M c.2 g hg0 hg2
    set q1 := GPoly.toPoly M (GPoly.divMod (MO Fc ks m) c.1 g).1
    set q2 := GPoly.toPoly M (GPoly.divMod (MO Fc ks m) c.2 g).1
    have hq2 : q2 ≠ 0 := fun h0 ↦ hc2 (by rw [e2, h0, zero_mul])
    have hφq2 : T.phi m q2 ≠ 0 := fun h0 ↦ hq2 (T.phi_injective htr (by rw [h0, map_zero]))
    have hφg : T.phi m (GPoly.toPoly M g) ≠ 0 := fun h0 ↦ hg0 (T.phi_injective htr
      (by rw [h0, map_zero]))
    rw [MPr_sem, T.sem_MP_succ] at hval
    change T.phi m (GPoly.toPoly M c.1) / T.phi m (GPoly.toPoly M c.2) = _ at hval
    rw [e1, e2, map_mul, map_mul, mul_div_mul_right _ _ hφg, div_eq_div_iff hφq2 hφS] at hval
    have heq : q1 * S = A * q2 := T.phi_injective htr (by rw [map_mul, map_mul, hval])
    have hcop : IsCoprime q1 q2 := by
      rw [← EuclideanDomain.gcd_isUnit_iff]
      have hd1 : EuclideanDomain.gcd q1 q2 * GPoly.toPoly M g ∣ GPoly.toPoly M c.1 := by
        rw [e1]; exact mul_dvd_mul_right (EuclideanDomain.gcd_dvd_left _ _) _
      have hd2 : EuclideanDomain.gcd q1 q2 * GPoly.toPoly M g ∣ GPoly.toPoly M c.2 := by
        rw [e2]; exact mul_dvd_mul_right (EuclideanDomain.gcd_dvd_right _ _) _
      have hdg := GPoly.dvd_egcd M c.1 c.2 hd1 hd2
      obtain ⟨u, hu⟩ := hdg
      have : GPoly.toPoly M g * (EuclideanDomain.gcd q1 q2 * u) = GPoly.toPoly M g * 1 := by
        rw [mul_one]; conv_rhs => rw [hu]
        ring
      have h1' := mul_left_cancel₀ hg0 this
      exact IsUnit.of_mul_eq_one _ h1'
    exact hcop.symm.dvd_of_dvd_mul_left ⟨A, by rw [heq]; ring⟩

/-- **A code whose value has the limit `c` at `t = 0`**: if `e = A / S` with `S(0) ≠ 0` and
`A(0) = c S(0)`, then `e₁(0) = c e₂(0)`. -/
lemma zero_of_sem (htr : Transcendental (T.F m) (T.ts m)) (e : LC (m + 1))
    (he : GPoly.toPoly (T.MP m h1.of_succ) e.2 ≠ 0) (A S : (T.F m)[X]) (hS : S.coeff 0 ≠ 0)
    (c : T.F m) (hc : A.coeff 0 = c * S.coeff 0)
    (hval : (T.MPr (m + 1) h1).sem e = T.phi m A / T.phi m S) :
    (GPoly.toPoly (T.MP m h1.of_succ) e.1).coeff 0 =
      c * (GPoly.toPoly (T.MP m h1.of_succ) e.2).coeff 0 := by
  set M := T.MP m h1.of_succ
  have hS0 : S ≠ 0 := fun h0 ↦ hS (by rw [h0, coeff_zero])
  rw [MPr_sem, T.sem_MP_succ] at hval
  change T.phi m (GPoly.toPoly M e.1) / T.phi m (GPoly.toPoly M e.2) = _ at hval
  have hφe : T.phi m (GPoly.toPoly M e.2) ≠ 0 := fun h0 ↦ he (T.phi_injective htr (by rw [h0, map_zero]))
  have hφS : T.phi m S ≠ 0 := fun h0 ↦ hS0 (T.phi_injective htr (by rw [h0, map_zero]))
  rw [div_eq_div_iff hφe hφS] at hval
  have heq : GPoly.toPoly M e.1 * S = A * GPoly.toPoly M e.2 :=
    T.phi_injective htr (by rw [map_mul, map_mul, hval])
  have h0 := congrArg (fun p : (T.F m)[X] ↦ p.coeff 0) heq
  simp only [mul_coeff_zero, hc] at h0
  apply mul_right_cancel₀ hS
  linear_combination h0

set_option maxHeartbeats 3200000 in
/-- **`exactTRE` answers in its regime.** -/
theorem exactTRE_isSome (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
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
    (f : List (LC (m + 1))) (Mval : ℕ → ℕ → T.F (m + 1))
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
    (exactTRE Fc ks m a rdeD r N0 C Ci P Tc Ti f).isSome := by
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
  have hf' : ∀ c ∈ (vecF Fc ks m f Ti N).map (redC Fc ks m), GPoly.toPoly M c.2 ≠ 0 := by
    intro c hc
    obtain ⟨c0, -, rfl⟩ := List.mem_map.mp hc
    exact T.redC_den_ne_zero m h1 c0
  have hWRE := T.exactWRE_isSome h1 hm hk htr rdeD hb0 N hN Mc' ((vecF Fc ks m f Ti N).map
    (redC Fc ks m)) r N0 C Ci hent lam0 hz hN0 hP0 hC1 hC2 lamI hlim' htri hf'
  -- unfold `exactTRE`
  have hcheck : ¬((!(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || decide (N = 0)) ||
      !(prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
        (fun i j ↦ (Ti.getD i []).getD j O1.zero) &&
        prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
        (fun i j ↦ (Tc.getD i []).getD j O1.zero))) = true := by
    rw [hPc, hok.1, hok.2]; simp [hN]
  unfold exactTRE exactTG
  simp only
  rw [if_neg hcheck, hd]
  exact hWRE

end MTower

end Curves.MT
