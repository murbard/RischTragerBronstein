import RischTragerBronstein.Mixed.NKExactTRSome
import RischTragerBronstein.Mixed.NKExactTV
import RischTragerBronstein.Mixed.NKExactWRVSome

/-!
# When `exactTV` answers

`exactTV_isSome`: as `exactTR_isSome`, for a rescaled derivation matrix that is bounded at
infinity with a limit `Λ` that is lower triangular with diagonal `fCode dgᵢ` and a non-degenerate
limit system — the regime of integral bases of non-constant curves (`exists_nkBasis`,
`nk_inf_struct`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ)

variable {m} in
/-- A code whose value is a bounded fraction `A/B` has a bounded numerator/denominator pair with the
same value at infinity. -/
lemma limE_of_sem (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m)) (e : LC (m + 1))
    (he : GPoly.toPoly (T.MP m h1.of_succ) e.2 ≠ 0) (A B : (T.F m)[X]) (hB : B ≠ 0)
    (hAB : A.natDegree ≤ B.natDegree) {lam0 : T.F m} (hlam : A.coeff B.natDegree / B.leadingCoeff = lam0)
    (hval : (T.MPr (m + 1) h1).sem e = T.phi m A / T.phi m B) :
    GPoly.toPoly (T.MP m h1.of_succ) e.2 ≠ 0 ∧
      (GPoly.toPoly (T.MP m h1.of_succ) e.1).natDegree ≤
        (GPoly.toPoly (T.MP m h1.of_succ) e.2).natDegree ∧
      T.limE m h1.of_succ e = lam0 := by
  set M := T.MP m h1.of_succ
  rw [MPr_sem, T.sem_MP_succ] at hval
  change T.phi m (GPoly.toPoly M e.1) / T.phi m (GPoly.toPoly M e.2) = _ at hval
  have hφe : T.phi m (GPoly.toPoly M e.2) ≠ 0 := fun h0 ↦ he (T.phi_injective htr (by rw [h0, map_zero]))
  have hφB : T.phi m B ≠ 0 := fun h0 ↦ hB (T.phi_injective htr (by rw [h0, map_zero]))
  rw [div_eq_div_iff hφe hφB] at hval
  have heq : GPoly.toPoly M e.1 * B = A * GPoly.toPoly M e.2 :=
    T.phi_injective htr (by rw [map_mul, map_mul, hval])
  have hlB : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  have hle : leadingCoeff (GPoly.toPoly M e.2) ≠ 0 := leadingCoeff_ne_zero.mpr he
  by_cases h0 : GPoly.toPoly M e.1 = 0
  · have hA : A = 0 := by
      rw [h0, zero_mul] at heq; exact (mul_eq_zero.mp heq.symm).resolve_right he
    refine ⟨he, by rw [h0, natDegree_zero]; exact Nat.zero_le _, ?_⟩
    rw [limE, ← hlam, hA, h0]; simp
  have hA : A ≠ 0 := by
    rintro rfl; rw [zero_mul] at heq; exact h0 ((mul_eq_zero.mp heq).resolve_right hB)
  have hn := congrArg natDegree heq
  rw [natDegree_mul h0 hB, natDegree_mul hA he] at hn
  have hdeg : (GPoly.toPoly M e.1).natDegree ≤ (GPoly.toPoly M e.2).natDegree := by omega
  refine ⟨he, hdeg, ?_⟩
  have hc : (GPoly.toPoly M e.1 * B).coeff ((GPoly.toPoly M e.2).natDegree + B.natDegree) =
      (A * GPoly.toPoly M e.2).coeff ((GPoly.toPoly M e.2).natDegree + B.natDegree) := by rw [heq]
  rw [MTower.coeff_mul_of_natDegree_le' hdeg le_rfl, add_comm,
    MTower.coeff_mul_of_natDegree_le' hAB le_rfl] at hc
  rw [limE, ← hlam, div_eq_div_iff hle hlB]
  change _ * B.coeff B.natDegree = A.coeff B.natDegree * (GPoly.toPoly M e.2).coeff _
  rw [hc]

variable {m} in
set_option maxHeartbeats 1600000 in
/-- **`exactTV` answers in its regime** (non-constant curves: a triangular limit `Λ`). -/
theorem exactTV_isSome (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (FRep (LC m))) (r : ℕ → ℤ)
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
    (Λ : ℕ → ℕ → T.F m)
    (hprop : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A B : (T.F m)[X], B ≠ 0 ∧
      A.natDegree ≤ B.natDegree ∧ A.coeff B.natDegree / B.leadingCoeff = Λ i j ∧
      Mval i j * T.tau m ^ (r j - r i) - (if i = j then (r i : T.F (m + 1)) *
        T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem η)) / T.tau m else 0) =
        T.phi m A / T.phi m B)
    (htri : ∀ i < P.length - 1, ∀ j < P.length - 1, i < j → Λ i j = 0)
    (hdiag : ∀ i < P.length - 1, Λ i i = (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (dgAt Fc ks m dg i)))
    (hokd : ∀ i, ∀ cw ∈ (dgAt Fc ks m dg i).logs, ((T.MP m h1.of_succ).sem cw.1)′ = 0)
    (hnd : ∀ c : Fin (P.length - 1) → T.F m, c ≠ 0 →
      (∀ a : Fin (P.length - 1), (c a)′ + ∑ b : Fin (P.length - 1), Λ b a * c b = 0) →
      ¬ ∃ y : Fin (P.length - 1) → T.F m, ∀ a : Fin (P.length - 1),
        (y a)′ + ∑ b : Fin (P.length - 1), Λ b a * y b = (T.MP m h1.of_succ).sem η * c a) :
    (exactTV Fc ks m η rde dg r P Tc Ti f).isSome := by
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
      GPoly.toPoly M (((rescaleM Fc ks m η N Mc' r).getD i []).getD j O1.zero).2 ≠ 0 ∧
      (GPoly.toPoly M (((rescaleM Fc ks m η N Mc' r).getD i []).getD j O1.zero).1).natDegree ≤
      (GPoly.toPoly M (((rescaleM Fc ks m η N Mc' r).getD i []).getD j O1.zero).2).natDegree ∧
      T.limE m h1.of_succ (((rescaleM Fc ks m η N Mc' r).getD i []).getD j O1.zero) = Λ i j := by
    intro i hi j hj
    obtain ⟨A, B, hB, hAB, hΛ, hval⟩ := hprop i hi j hj
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
      refine T.limE_of_sem h1 htr _ hden A B hB hAB hΛ ?_
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
      refine T.limE_of_sem h1 htr _ (T.tpowL_snd_ne_zero h1 _ _ hcd) A B hB hAB hΛ ?_
      rw [T.sem_tpowL m h1 htr, hcs, ← hval, if_neg hij, sub_zero]
  have hf' : ∀ c ∈ (vecF Fc ks m f Ti N).map (redC Fc ks m), GPoly.toPoly M c.2 ≠ 0 := by
    intro c hc
    obtain ⟨c0, -, rfl⟩ := List.mem_map.mp hc
    exact T.redC_den_ne_zero m h1 c0
  have hWR := T.exactWRV_isSome h1 hm hk htr rde hrde dg N hN Mc' ((vecF Fc ks m f Ti N).map
    (redC Fc ks m)) r hent (fun i hi j hj ↦ ⟨(hprop' i hi j hj).1, (hprop' i hi j hj).2.1⟩)
    (fun i hi j hj hij ↦ by rw [(hprop' i hi j hj).2.2]; exact htri i hi j hj hij)
    (fun i hi ↦ by rw [(hprop' i hi i hi).2.2]; exact hdiag i hi) hokd
    (by
      have e : ∀ a b : Fin N, T.limE m h1.of_succ
          (((rescaleM Fc ks m η N Mc' r).getD (b : ℕ) []).getD (a : ℕ) O1.zero) = Λ b a :=
        fun a b ↦ (hprop' b b.2 a a.2).2.2
      intro c hc hhom hy
      refine hnd c hc (fun a ↦ by
        rw [← hhom a]; congr 1; exact Finset.sum_congr rfl fun b _ ↦ by rw [e a b]) ?_
      obtain ⟨y, hy⟩ := hy
      exact ⟨y, fun a ↦ by
        rw [← hy a]; congr 1; exact Finset.sum_congr rfl fun b _ ↦ by rw [e a b]⟩) hf'
  -- unfold `exactTR`
  have hcheck : ¬((!(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || decide (N = 0)) ||
      !(prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
        (fun i j ↦ (Ti.getD i []).getD j O1.zero) &&
        prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
        (fun i j ↦ (Tc.getD i []).getD j O1.zero))) = true := by
    rw [hPc, hok.1, hok.2]; simp [hN]
  unfold exactTV exactTG
  simp only
  rw [if_neg hcheck, hd]
  exact hWR

end MTower

end Curves.MT
