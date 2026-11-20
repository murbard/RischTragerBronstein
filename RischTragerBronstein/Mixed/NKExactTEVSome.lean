import RischTragerBronstein.Mixed.NKExactTRESome
import RischTragerBronstein.Mixed.NKExactTEV
import RischTragerBronstein.Mixed.NKExactWREVSome

/-!
# When `exactTEV` answers

`exactTEV_isSome`: as `exactTRE_isSome`, for non-constant curves over an exponential: the value of
the matrix at `t = 0` made triangular by a gauge `C` (diagonal `p⁰ᵢ a′ + q⁰ᵢ c′/c`, `p⁰ᵢ` not a
positive integer) and the rescaled matrix with a lower triangular limit `Λ` at infinity
(diagonal `pᵢ a′ + qᵢ c′/c`).
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

variable (T : MTower Fc ks Cc L) {m : ℕ} (h1 : T.Tr (m + 1))

set_option maxHeartbeats 3200000 in
/-- **`exactTEV` answers in its regime** (non-constant curves over an exponential). -/
theorem exactTEV_isSome (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (ℚ × ℚ × LC m)) (r : ℕ → ℤ) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
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
    (M0v : ℕ → ℕ → T.F m)
    (hsq : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A S : (T.F m)[X], Squarefree S ∧
      S.coeff 0 ≠ 0 ∧ A.coeff 0 = M0v j i * S.coeff 0 ∧ Mval i j = T.phi m A / T.phi m S)
    (hC1 : ∀ i j : Fin (P.length - 1), ∑ k : Fin (P.length - 1),
      (T.MP m h1.of_succ).sem (cget Fc ks m C (i : ℕ) (k : ℕ)) *
      (T.MP m h1.of_succ).sem (cget Fc ks m Ci (k : ℕ) (j : ℕ)) = if i = j then 1 else 0)
    (hC2 : ∀ i j : Fin (P.length - 1), ∑ k : Fin (P.length - 1),
      (T.MP m h1.of_succ).sem (cget Fc ks m Ci (i : ℕ) (k : ℕ)) *
      (T.MP m h1.of_succ).sem (cget Fc ks m C (k : ℕ) (j : ℕ)) = if i = j then 1 else 0)
    (hgtri : ∀ i j : Fin (P.length - 1), j < i →
      ((Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m C i j)) *
        Matrix.of (fun i j : Fin (P.length - 1) ↦ M0v i j) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j)) -
        (Matrix.of fun i j : Fin (P.length - 1) ↦
          (T.MP m h1.of_succ).sem (cget Fc ks m C i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j)))
          i j = 0)
    (hgdiag : ∀ i : Fin (P.length - 1),
      ((Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m C i j)) *
        Matrix.of (fun i j : Fin (P.length - 1) ↦ M0v i j) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j)) -
        (Matrix.of fun i j : Fin (P.length - 1) ↦
          (T.MP m h1.of_succ).sem (cget Fc ks m C i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Ci i j)))
          i i =
      (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg0 (i : ℕ)))))
    (hgp : ∀ i : Fin (P.length - 1),
      (dgEAt Fc ks m dg0 (i : ℕ)).1.den ≠ 1 ∨ (dgEAt Fc ks m dg0 (i : ℕ)).1 ≤ 0)
    (Λ : ℕ → ℕ → T.F m)
    (hlim : ∀ k < P.length - 1, ∀ l < P.length - 1, ∃ A B : (T.F m)[X], B ≠ 0 ∧
      A.natDegree ≤ B.natDegree ∧ A.coeff B.natDegree / B.leadingCoeff = Λ k l ∧
      T.tau m ^ (r l - r k) * Mval k l -
          (if k = l then (r k : T.F (m + 1)) *
            T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a))) else 0) =
        T.phi m A / T.phi m B)
    (htri : ∀ i < P.length - 1, ∀ j < P.length - 1, i < j → Λ i j = 0)
    (hdiag : ∀ i < P.length - 1, Λ i i =
      (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg i)))) :
    (exactTEV Fc ks m a rde dg r C Ci dg0 P Tc Ti f).isSome := by
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
      M0v j i * (GPoly.toPoly M ((Mc'.getD i []).getD j O1.zero).2).coeff 0 := by
    intro i hi j hj
    obtain ⟨A, S, -, hS0, hA0, hAS⟩ := hsq i hi j hj
    exact T.zero_of_sem h1 htr _ (by rw [hc i hi j hj]; exact T.redC_den_ne_zero m h1 _) A S hS0 _
      hA0 (by rw [hcs i hi j hj]; exact hAS)
  have hlim' : ∀ k < N, ∀ l < N, ∃ A B : (T.F m)[X], B ≠ 0 ∧ A.natDegree ≤ B.natDegree ∧
      A.coeff B.natDegree / B.leadingCoeff = Λ k l ∧
      M1.sem (((rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc' r).getD k []).getD l O1.zero) =
        T.phi m A / T.phi m B := by
    intro k hk l hl
    obtain ⟨A, B, hB, hAB, hcB, hv⟩ := hlim k hk l hl
    refine ⟨A, B, hB, hAB, hcB, ?_⟩
    rw [T.sem_rescaleME h1 htr _ N Mc' r k l hk hl (by
      rw [hc k hk k hk]
      exact fun h0 ↦ T.redC_den_ne_zero m h1 _ (T.phi_injective htr (by rw [h0, map_zero]))),
      hcs k hk l hl, ← hv]
  have hf' : ∀ c ∈ (vecF Fc ks m f Ti N).map (redC Fc ks m), GPoly.toPoly M c.2 ≠ 0 := by
    intro c hc
    obtain ⟨c0, -, rfl⟩ := List.mem_map.mp hc
    exact T.redC_den_ne_zero m h1 c0
  have hWRE := T.exactWREV_isSome h1 hm hk htr rde hrde dg N hN Mc' ((vecF Fc ks m f Ti N).map
    (redC Fc ks m)) r C Ci dg0 hent M0v hz hC1 hC2 hgtri hgdiag hgp Λ hlim' htri hdiag hf'
  -- unfold `exactTRE`
  have hcheck : ¬((!(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || decide (N = 0)) ||
      !(prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
        (fun i j ↦ (Ti.getD i []).getD j O1.zero) &&
        prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
        (fun i j ↦ (Tc.getD i []).getD j O1.zero))) = true := by
    rw [hPc, hok.1, hok.2]; simp [hN]
  unfold exactTEV exactTG
  simp only
  rw [if_neg hcheck, hd]
  exact hWRE

end MTower

end Curves.MT
