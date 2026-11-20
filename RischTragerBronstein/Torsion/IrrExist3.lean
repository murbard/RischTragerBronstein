import RischTragerBronstein.Torsion.IrrExist2
import RischTragerBronstein.Curves.NewtonT

/-!
# Irreducibility certificates exist (3): the subset certificate at a split point

**`irrAt_complete`**: for the equation `F` of a curve over `F` (`S.F = F.map ψ`), monic of degree
`n > 0` with `x`-degrees `≤ d`, and `n` distinct simple roots `y₀` of `F(a, Y)` in `F`, the subset
certificate `irrAt F n d a ys₀ prec` passes for every large precision.
-/

open Polynomial

namespace Curves

open CPoly Sup Differential

lemma mem_subsetsL : ∀ (n : ℕ) (L : List ℕ), L ∈ subsetsL n → L.Nodup ∧ ∀ j ∈ L, j < n
  | 0, L, h => by
    simp only [subsetsL, List.mem_singleton] at h; subst h; exact ⟨List.nodup_nil, by simp⟩
  | n + 1, L, h => by
    simp only [subsetsL, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨L', hL', rfl⟩
    · obtain ⟨h1, h2⟩ := mem_subsetsL n L h
      exact ⟨h1, fun j hj ↦ by have := h2 j hj; omega⟩
    · obtain ⟨h1, h2⟩ := mem_subsetsL n L' hL'
      refine ⟨List.nodup_cons.mpr ⟨fun hm ↦ by have := h2 n hm; omega, h1⟩, fun j hj ↦ ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · have := h2 j hj; omega

section Complete

variable {F : Type*} [Field F] [DecidableEq F]

local notation "cT" => (Polynomial.coeToPowerSeries.ringHom (R := F))

lemma constantCoeff_eval_eq (P : (PowerSeries F)[X]) (ρ : PowerSeries F) :
    PowerSeries.constantCoeff (P.eval ρ) =
      PowerSeries.constantCoeff (P.eval (PowerSeries.C (PowerSeries.constantCoeff ρ))) := by
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval₂_at_apply, ← eval_map, ← eval_map]
  simp

end Complete

section Main

variable {F : Type*} [Field F] [DecidableEq F]

local notation "cT" => (Polynomial.coeToPowerSeries.ringHom (R := F))

lemma branchSub_one_eq (a : F) :
    branchSub (C := F) (K := F) 1 a =
      (HahnSeries.ofPowerSeries ℤ F).comp (RingHom.comp cT (compRingHom (Polynomial.C a + X))) := by
  refine RingHom.ext fun P ↦ ?_
  rw [branchSub_apply]
  simp [pow_one]

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- **Subset certificates of irreducibility exist** at every split point with simple roots. -/
theorem irrAt_complete (S : CurveData C L) (Fc : BPoly F) (ψ : F →+* C)
    (hSF : S.F = (toB Fc).map (mapRingHom ψ)) (n d : ℕ) (hmon : (toB Fc).Monic)
    (hn : (toB Fc).natDegree = n) (hd : ∀ q ∈ Fc, q.length ≤ d + 1) (a : F) (ys0 : List F)
    (hlen : ys0.length = n) (hnd : ys0.Nodup) (hroot : ∀ y0 ∈ ys0, evalB Fc a y0 = 0)
    (hsimple : ∀ y0 ∈ ys0, evalB (derivYB Fc) a y0 ≠ 0) :
    ∃ p₀, ∀ prec, p₀ ≤ prec → irrAt Fc n d a ys0 prec = true := by
  classical
  set H := Fc.map fun q ↦ compC q (shiftC a 1) with hH
  set φ := compRingHom (Polynomial.C a + X) with hφ
  have hHS : (toB H).map cT = ((toB Fc).map φ).map cT := by rw [hH, toB_shiftF]
  set yv : Fin n → F := fun k ↦ ys0.getD k 0 with hyv
  have hyv_mem : ∀ k, yv k ∈ ys0 := fun k ↦ by
    simp only [hyv]; rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2)]; exact List.getElem_mem _
  have hyv_inj : Function.Injective yv := fun k l h ↦ by
    simp only [hyv] at h
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2),
      List.getD_eq_getElem _ _ (by rw [hlen]; exact l.2)] at h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h)
  -- the roots through the `yv k`
  have hex : ∀ k, ∃ ρ : PowerSeries F, (HS H).eval ρ = 0 ∧ PowerSeries.constantCoeff ρ = yv k ∧
      ∀ Lp, (PowerSeries.X : PowerSeries F) ^ Lp ∣ valT (newtonT H Lp (Nat.log2 Lp + 3) [yv k]) - ρ := by
    intro k
    refine exists_newtonT_root H (yv k) ?_ ?_
    · show PowerSeries.constantCoeff (((toB H).map cT).eval (PowerSeries.C (yv k))) = 0
      rw [hHS, constantCoeff_eval_map, ← evalB_eq]
      exact hroot _ (hyv_mem k)
    · show PowerSeries.constantCoeff ((derivative ((toB H).map cT)).eval (PowerSeries.C (yv k))) ≠ 0
      rw [hHS, derivative_map, derivative_map, constantCoeff_eval_map, ← toB_derivYB, ← evalB_eq]
      exact hsimple _ (hyv_mem k)
  choose ρ hρ hρ0 hρap using hex
  have hρinj : Function.Injective ρ := fun k l h ↦ hyv_inj (by rw [← hρ0, ← hρ0, h])
  have hHm : (HS H).Monic := by
    show ((toB H).map cT).Monic
    rw [hHS]; exact (hmon.map _).map _
  have hHn : (HS H).natDegree = n := by
    show ((toB H).map cT).natDegree = n
    rw [hHS, (hmon.map _).natDegree_map, hmon.natDegree_map, hn]
  have hsplitPS : HS H = ∏ k, (X - Polynomial.C (ρ k)) :=
    GTors.eq_prod_of_distinct_roots' (HS H) hHm hHn ρ hρinj hρ
  set nF := (toB Fc).natDegree
  set ρ' : Fin nF → PowerSeries F := fun k ↦ ρ (Fin.cast hn k) with hρ'
  have hsplit : (toB Fc).map (branchSub (C := F) (K := F) 1 a) =
      ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ F (ρ' k))) := by
    rw [branchSub_one_eq, ← Polynomial.map_map, ← Polynomial.map_map, ← hHS]
    show (HS H).map _ = _
    rw [hsplitPS, Polynomial.map_prod]
    refine (Fintype.prod_equiv (finCongr hn.symm) _ _ fun k ↦ ?_)
    simp [hρ']
  have hdC : ∀ i, ((toB Fc).coeff i).natDegree ≤ d := fun i ↦ by
    rw [coeff_toB]
    refine (natDegree_toPoly_le_length _).trans ?_
    by_cases hi : i < Fc.length
    · rw [List.getD_eq_getElem _ _ hi]; have := hd _ (List.getElem_mem hi); omega
    · rw [List.getD_eq_default _ _ (by omega)]; simp
  -- the witnesses
  have hwit : ∀ J : Finset (Fin nF), 0 < J.card → J.card < nF → ∃ i t, d < t ∧
      PowerSeries.coeff t ((∏ j ∈ J, (X - Polynomial.C (ρ' j))).coeff i) ≠ 0 := fun J h0 h1 ↦
    exists_coeff_subset S ψ (toB Fc) hSF hmon a d hdC ρ' hsplit J h0 h1
  choose! wi wt hwt hwne using hwit
  set p₀ := 1 + ∑ J ∈ (Finset.univ : Finset (Fin nF)).powerset, wt J
  refine ⟨p₀, fun prec hprec ↦ ?_⟩
  have hprec1 : 1 ≤ prec := by omega
  -- the constant terms of the lifts
  have hconst : ∀ k, (newtonT H prec (Nat.log2 prec + 3) [yv k]).getD 0 0 = yv k := fun k ↦ by
    have h1 := (PowerSeries.X_pow_dvd_iff.mp (hρap k prec)) 0 (by omega)
    rw [map_sub, sub_eq_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply (ρ k), hρ0] at h1
    have h2 : (newtonT H prec (Nat.log2 prec + 3) [yv k]).getD 0 0 =
        PowerSeries.coeff 0 (valT (newtonT H prec (Nat.log2 prec + 3) [yv k])) := by
      simp only [valT, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, coeff_toPoly]
    rw [h2]; exact h1
  have hindex : ∀ y0 ∈ ys0, ∃ k, yv k = y0 := fun y0 hy0 ↦ by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy0
    exact ⟨⟨i, by rw [← hlen]; exact hi⟩, by simp [hyv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]⟩
  have hderiv : ∀ k, PowerSeries.coeff 0 ((derivative (repEq (RingHom.id F) Fc a 1)).eval (ρ k)) ≠ 0 := by
    intro k
    rw [repEq_id_eq_HS, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_eval_eq, hρ0, hHS,
      derivative_map, derivative_map, constantCoeff_eval_map, ← toB_derivYB, ← evalB_eq]
    exact hsimple _ (hyv_mem k)
  simp only [irrAt, irrSubsetCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, List.any_eq_true, List.mem_range]
  refine ⟨⟨⟨?_, rfl⟩, hd⟩, fun Ls hLs ↦ ?_⟩
  · -- the certificate of the lifted roots
    simp only [certCheck, liftRootsAt, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.length_map]
    refine ⟨⟨⟨rfl, by simp [hlen]⟩, fun y hy ↦ ?_⟩, ?_⟩
    · obtain ⟨y0, hy0, rfl⟩ := List.mem_map.mp hy
      obtain ⟨k, rfl⟩ := hindex y0 hy0
      refine rootCheck_of_root (RingHom.id F) (ρ k) (by rw [repEq_id_eq_HS]; exact hρ k) 0
        (fun i hi ↦ absurd hi (Nat.not_lt_zero _)) (hderiv k) (by omega) ?_
      rw [zero_add, ← dvd_neg, neg_sub]
      convert hρap k prec using 2
      simp [thetaT_apply, valT]
      rfl
    · simp only [sepCheck, List.all_eq_true, List.mem_range, List.length_map, Bool.or_eq_true,
        decide_eq_true_eq, List.any_eq_true]
      intro k' hk' l' hl'
      by_cases hkl : k' = l'
      · exact Or.inl hkl
      right
      refine ⟨0, by omega, ?_⟩
      have e : ∀ m (hm : m < ys0.length), ((ys0.map fun y0 ↦ newtonT H prec (Nat.log2 prec + 3) [y0]).getD m
          []).getD 0 0 = yv ⟨m, by rw [← hlen]; exact hm⟩ := fun m hm ↦ by
        rw [List.getD_eq_getElem (l := ys0.map fun y0 ↦ newtonT H prec (Nat.log2 prec + 3) [y0])
          (d := []) (by simpa using hm), List.getElem_map]
        have := hconst ⟨m, by rw [← hlen]; exact hm⟩
        have hy : yv ⟨m, by rw [← hlen]; exact hm⟩ = ys0[m] := by
          simp only [hyv]; exact List.getD_eq_getElem _ _ hm
        rw [hy] at this ⊢
        exact this
      rw [e k' hk', e l' hl']
      exact fun h ↦ hkl (congrArg Fin.val (hyv_inj h))
  · -- the subsets
    by_cases hc : 0 < Ls.length ∧ 2 * Ls.length ≤ n
    swap
    · left
      by_contra hcon
      push Not at hcon
      exact hc ⟨by omega, by omega⟩
    right
    obtain ⟨hLnd, hLlt⟩ := mem_subsetsL n Ls hLs
    set J : Finset (Fin nF) := Finset.univ.filter fun k ↦ (k : ℕ) ∈ Ls with hJ
    have hJc : J.card = Ls.length := by
      have := length_of_mem_iff hLnd (S := J.map Fin.valEmbedding) (fun j ↦ by
        simp only [Finset.mem_map, hJ, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
        constructor
        · intro hj; exact ⟨⟨j, by rw [hn]; exact hLlt j hj⟩, hj, rfl⟩
        · rintro ⟨k, hk, rfl⟩; exact hk)
      rw [this, Finset.card_map]
    have h0 : 0 < J.card := by rw [hJc]; exact hc.1
    have h1 : J.card < nF := by rw [hJc, hn]; omega
    have hne := hwne J h0 h1
    refine ⟨wi J, ?_, wt J, ?_, hwt J h0 h1, ?_⟩
    · -- the index is at most the degree
      by_contra hi
      apply hne
      rw [coeff_eq_zero_of_natDegree_lt, map_zero]
      rw [natDegree_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C _]
      simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
      omega
    · -- the precision
      show wt J < prec
      have : wt J ≤ ∑ J' ∈ (Finset.univ : Finset (Fin nF)).powerset, wt J' :=
        Finset.single_le_sum (f := wt) (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_powerset.mpr (Finset.subset_univ J))
      omega
    · -- the computed coefficient is the exact one
      set ys := ys0.map fun y0 ↦ newtonT H prec (Nat.log2 prec + 3) [y0]
      set v : ℕ → PowerSeries F := fun j ↦ if h : j < nF then ρ' ⟨j, h⟩ else 0 with hv
      have happ : ∀ j ∈ Ls, (PowerSeries.X : PowerSeries F) ^ prec ∣ valT (ys.getD j []) - v j := by
        intro j hj
        have hjn : j < n := hLlt j hj
        have hjl : j < ys0.length := by rw [hlen]; exact hjn
        have e1 : ys.getD j [] = newtonT H prec (Nat.log2 prec + 3) [yv ⟨j, hjn⟩] := by
          rw [List.getD_eq_getElem (l := ys) (d := []) (by simpa [ys] using hjl), List.getElem_map]
          simp [hyv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
        have e2 : v j = ρ ⟨j, hjn⟩ := by
          simp only [hv, dif_pos (show j < nF by rw [hn]; exact hjn), hρ']
          rfl
        rw [e1, e2]; exact hρap _ prec
      have hdv := prod_sub_dvd prec Ls (fun j ↦ valT (ys.getD j [])) v happ (wi J)
      have hcoef := (PowerSeries.X_pow_dvd_iff.mp hdv) (wt J) (by
        have : wt J ≤ ∑ J' ∈ (Finset.univ : Finset (Fin nF)).powerset, wt J' :=
          Finset.single_le_sum (f := wt) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_powerset.mpr (Finset.subset_univ J))
        omega)
      rw [Polynomial.coeff_sub, map_sub, sub_eq_zero] at hcoef
      have hLHS : ((prodSubB ys Ls).getD (wi J) []).getD (wt J) 0 =
          PowerSeries.coeff (wt J) (((Ls.map fun j ↦ X - Polynomial.C (valT (ys.getD j []))).prod).coeff (wi J)) := by
        rw [← coeff_toPoly, ← coeff_toB, toB_prodSubB]
        rw [show (Ls.map fun j ↦ X - Polynomial.C (valT (ys.getD j []))).prod =
          ((Ls.map fun j ↦ X - Polynomial.C (toPoly (ys.getD j []))).prod).map cT by
            rw [Polynomial.map_list_prod, List.map_map]
            congr 1
            refine List.map_congr_left fun j _ ↦ ?_
            simp [valT]]
        rw [coeff_map]
        simp [Polynomial.coeff_coe]
      have hRHS : (Ls.map fun j ↦ X - Polynomial.C (v j)).prod = ∏ k ∈ J, (X - Polynomial.C (ρ' k)) := by
        rw [← List.prod_toFinset _ hLnd]
        rw [show Ls.toFinset = J.map Fin.valEmbedding by
          ext j
          simp only [List.mem_toFinset, Finset.mem_map, hJ, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.valEmbedding_apply]
          constructor
          · intro hj; exact ⟨⟨j, by rw [hn]; exact hLlt j hj⟩, hj, rfl⟩
          · rintro ⟨k, hk, rfl⟩; exact hk]
        rw [Finset.prod_map]
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        simp [hv]
      show ((prodSubB ys Ls).getD (wi J) []).getD (wt J) 0 ≠ 0
      rw [hLHS, hcoef, hRHS]
      exact hne

end Main

end Curves
