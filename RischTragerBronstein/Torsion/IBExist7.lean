import RischTragerBronstein.Torsion.IBExist6

/-!
# Integral bases exist (7): transfer between certified systems, and the check above infinity

* `regAt_transfer`, `indepAt_transfer`: regularity and local independence only depend on the point
  and the ramification index of the branch system (the roots are the same);
* `infSysOf`: the branch system above infinity with exact roots from a certificate;
* **`basisCheckInfS_complete`**: the check above infinity accepts a basis with pole bounds `δ`
  independent at infinity, at every large precision.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries CPoly Sup

section Transfer

variable {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]

namespace CurveData

variable {S : CurveData C L}

lemma locSys_root (σ σ' : S.LocSys) (ha : σ.a = σ'.a) (hN : σ.N = σ'.N) (k' : Fin S.F.natDegree) :
    ∃ k, σ'.r k' = σ.r k := by
  have h := S.root_of_split _ σ'.r σ'.hs k'
  have hg : branchSub (C := C) σ'.N (algebraMap C C σ'.a) = branchSub σ.N (algebraMap C C σ.a) := by
    rw [ha, hN]
  rw [hg, σ.hs, eval_prod] at h
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h
  exact ⟨k, by simpa [sub_eq_zero] using hk⟩

lemma locSys_ev (σ σ' : S.LocSys) (ha : σ.a = σ'.a) (hN : σ.N = σ'.N) (k k' : Fin S.F.natDegree)
    (hk : σ'.r k' = σ.r k) (f : C⟮S.x⟯⟮S.y⟯) : σ'.ev k' f = σ.ev k f := by
  unfold LocSys.ev
  have hg : branchSub (C := C) σ'.N (algebraMap C C σ'.a) = branchSub σ.N (algebraMap C C σ.a) := by
    rw [ha, hN]
  exact congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries C ↦ φ f) (S.embG_congr hg _ _ hk _ _)

lemma regAt_transfer (σ σ' : S.LocSys) (ha : σ.a = σ'.a) (hN : σ.N = σ'.N)
    (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (h : RegAt σ B D) : RegAt σ' B D := by
  intro j k'
  obtain ⟨k, hk⟩ := locSys_root σ σ' ha hN k'
  rw [locSys_ev σ σ' ha hN k k' hk]
  exact h j k

lemma indepAt_transfer (σ σ' : S.LocSys) (ha : σ.a = σ'.a) (hN : σ.N = σ'.N)
    (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (h : IndepAt σ B D) : IndepAt σ' B D := by
  intro c hc
  refine h c fun k ↦ ?_
  obtain ⟨k', hk'⟩ := locSys_root σ' σ ha.symm hN.symm k
  have e : ∀ f, σ.ev k f = σ'.ev k' f := fun f ↦ locSys_ev σ' σ ha.symm hN.symm k' k hk' f
  simp only [e]
  rw [hN]
  exact hc k'

end CurveData

end Transfer

section Syn

variable {F : Type*} [Field F] [DecidableEq F]

lemma le_foldr_max (f : ℕ → ℕ) : ∀ (l : List ℕ) (i : ℕ), i ∈ l →
    f i ≤ l.foldr (fun i m ↦ max m (f i)) 0
  | [], _, h => by simp at h
  | a :: l, i, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_right _ _
    · exact (le_foldr_max f l i h).trans (le_max_left _ _)

lemma le_synDelta (k : ℕ) (Dc : CPoly F) (B : BPoly F) (i : ℕ) (hi : i < B.length) :
    (B.getD i []).length + k * i - 1 - (Dc.length - 1) ≤ synDelta k Dc B :=
  le_foldr_max (fun i ↦ (B.getD i []).length + k * i - 1 - (Dc.length - 1)) _ i
    (List.mem_range.mpr hi)

lemma invOKb_synDelta (k : ℕ) (Dc : CPoly F) (B : BPoly F) :
    invOKb k (synDelta k Dc B + (Dc.length - 1)) B = true := by
  simp only [invOKb, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro i hi
  have := le_synDelta k Dc B i hi
  omega

end Syn

section InfCert

variable {F E : Type*} [Field F] [CharZero F] [DecidableEq F] [Field E] [Algebra F E]

namespace CurveData

variable (S : CurveData F E)

lemma exists_infRoots (Fc : BPoly F) (hSF : S.F = toB Fc) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = S.F.natDegree) (k : ℕ)
    (hok : InvOK k (k * S.F.natDegree) 0 Fc) (hmon' : (toB (invB Fc k (k * S.F.natDegree))).Monic)
    (hn' : (toB (invB Fc k (k * S.F.natDegree))).natDegree = S.F.natDegree) (c : BranchCert F)
    (h : certCheck (invB Fc k (k * S.F.natDegree)) S.F.natDegree 0 c = true) :
    ∃ w : Fin S.F.natDegree → PowerSeries F,
      (∀ j, (PowerSeries.X : PowerSeries F) ^ c.prec ∣
        w j - thetaT ((algebraMap F F).comp (RingHom.id F)) (toPoly (c.ys.getD j []))) ∧
      S.F.map (infSub c.N) = ∏ j, (X - Polynomial.C (single (-((k * c.N : ℕ) : ℤ)) (1 : F) *
        ofPowerSeries ℤ F (w j))) := by
  obtain ⟨w, hw, hs⟩ := certInf_spec (C := F) (K := F) Fc S.F.natDegree hmon hdeg k hok hmon' hn' c
    h (RingHom.id F)
  refine ⟨w, hw, ?_⟩
  rw [Polynomial.mapRingHom_id, Polynomial.map_id] at hs
  rw [show S.F.map (infSub (C := F) (K := F) c.N) = (toB Fc).map (infSub c.N) by rw [hSF]]
  exact hs

/-- The branch system above infinity from a certificate. -/
noncomputable def infSysOf (Fc : BPoly F) (hSF : S.F = toB Fc) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = S.F.natDegree) (k : ℕ)
    (hok : InvOK k (k * S.F.natDegree) 0 Fc) (hmon' : (toB (invB Fc k (k * S.F.natDegree))).Monic)
    (hn' : (toB (invB Fc k (k * S.F.natDegree))).natDegree = S.F.natDegree) (c : BranchCert F)
    (h : certCheck (invB Fc k (k * S.F.natDegree)) S.F.natDegree 0 c = true) : S.InfSys where
  N := c.N
  hN := N_pos_of_certCheck h
  r := fun j ↦ single (-((k * c.N : ℕ) : ℤ)) (1 : F) *
    ofPowerSeries ℤ F (Classical.choose (S.exists_infRoots Fc hSF hmon hdeg k hok hmon' hn' c h) j)
  hs := (Classical.choose_spec (S.exists_infRoots Fc hSF hmon hdeg k hok hmon' hn' c h)).2

variable {S}

lemma dcOf_length (D : F[X]) : (dcOf D).length = D.natDegree + 1 := by simp [dcOf]

lemma dcOf_last (D : F[X]) (hD : D ≠ 0) : (dcOf D).getD ((dcOf D).length - 1) 0 ≠ 0 := by
  rw [dcOf_length, Nat.add_sub_cancel, dcOf, List.getD_eq_getElem _ _ (by simp),
    List.getElem_map, List.getElem_range]
  exact leadingCoeff_ne_zero.mpr hD

/-- The expansion above infinity in terms of the syntactic order and the truncations. -/
lemma inf_rep (Fc : BPoly F) (hSF : S.F = toB Fc) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = S.F.natDegree) (k : ℕ)
    (hok : InvOK k (k * S.F.natDegree) 0 Fc) (hmon' : (toB (invB Fc k (k * S.F.natDegree))).Monic)
    (hn' : (toB (invB Fc k (k * S.F.natDegree))).natDegree = S.F.natDegree) (c : BranchCert F)
    (h : certCheck (invB Fc k (k * S.F.natDegree)) S.F.natDegree 0 c = true)
    (B : Fin S.F.natDegree → F[X][X]) (D : F[X]) (hD : D ≠ 0) (j m : Fin S.F.natDegree) :
    ∃ V : PowerSeries F,
      (S.infSysOf Fc hSF hmon hdeg k hok hmon' hn' c h).ev m (S.fnWQ (B j) D) =
        single (-((c.N * synDelta k (dcOf D) (ofB (B j)) : ℕ) : ℤ)) (1 : F) * ofPowerSeries ℤ F V ∧
      ∀ t < c.prec, PowerSeries.coeff t V =
        (serInf (ofB (B j)) (dcOf D) k (synDelta k (dcOf D) (ofB (B j))) c.N c.prec
          (c.ys.getD m [])).getD t 0 := by
  set hex := S.exists_infRoots Fc hSF hmon hdeg k hok hmon' hn' c h
  have hw := (Classical.choose_spec hex).1 m
  have hSF' : S.F = (toB Fc).map (mapRingHom (RingHom.id F)) := by
    rw [Polynomial.mapRingHom_id, Polynomial.map_id]; exact hSF
  have hD' : (toPoly (dcOf D)).map (RingHom.id F) ≠ 0 := by
    rw [Polynomial.map_id, toPoly_dcOf]; exact hD
  have hz : (S.fnWQ (B j) D : E) * aeval S.x ((toPoly (dcOf D)).map (RingHom.id F)) =
      S.evXY ((toB (ofB (B j))).map (mapRingHom (RingHom.id F))) := by
    rw [Polynomial.map_id, toPoly_dcOf, toB_ofB, Polynomial.mapRingHom_id, Polynomial.map_id]
    exact S.fnWQ_mul _ _ hD
  obtain ⟨V, hV, hVt⟩ := S.phi_repr_inf (K := F) Fc (RingHom.id F) hSF' k c.N
    (N_pos_of_certCheck h) (Classical.choose hex m)
    (S.root_of_split _ (S.infSysOf Fc hSF hmon hdeg k hok hmon' hn' c h).r
      (S.infSysOf Fc hSF hmon hdeg k hok hmon' hn' c h).hs m)
    (c.ys.getD m []) c.prec hw (S.fnWQ (B j) D) (ofB (B j)) (dcOf D) hz
    (synDelta k (dcOf D) (ofB (B j)) + ((dcOf D).length - 1))
    (invOKb_spec (invOKb_synDelta k _ _)) (by rw [dcOf_length]; omega) (dcOf_last D hD)
  refine ⟨V, ?_, fun t ht ↦ ?_⟩
  · have hexp : -((c.N * (synDelta k (dcOf D) (ofB (B j)) + ((dcOf D).length - 1)) : ℕ) : ℤ) +
        ((c.N * ((dcOf D).length - 1) : ℕ) : ℤ) =
        -((c.N * synDelta k (dcOf D) (ofB (B j)) : ℕ) : ℤ) := by push_cast; ring
    rw [hexp] at hV
    exact hV
  · have := (PowerSeries.X_pow_dvd_iff.mp hVt) t ht
    rw [map_sub, coeff_thetaT, sub_eq_zero] at this
    rw [this]; rfl

lemma coeff_single_ofPS (b t : ℤ) (V : PowerSeries F) :
    (single b (1 : F) * ofPowerSeries ℤ F V).coeff t =
      if 0 ≤ t - b then PowerSeries.coeff (t - b).toNat V else 0 := by
  rw [HahnSeries.coeff_single_mul, one_mul]
  split_ifs with h
  · obtain ⟨u, hu⟩ := Int.eq_ofNat_of_zero_le h
    rw [hu, ofPowerSeries_apply_coeff]; simp
  · exact lowerBd_ofPS V _ (by omega)

/-- **The check above infinity accepts a basis independent at infinity.** -/
theorem basisCheckInfS_complete (Fc : BPoly F) (hSF : S.F = toB Fc) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = S.F.natDegree) (k : ℕ)
    (hok : InvOK k (k * S.F.natDegree) 0 Fc) (hmon' : (toB (invB Fc k (k * S.F.natDegree))).Monic)
    (hn' : (toB (invB Fc k (k * S.F.natDegree))).natDegree = S.F.natDegree) (c : BranchCert F)
    (h : certCheck (invB Fc k (k * S.F.natDegree)) S.F.natDegree 0 c = true)
    (B : Fin S.F.natDegree → F[X][X]) (D : F[X]) (hD : D ≠ 0) (δ : Fin S.F.natDegree → ℕ)
    (hP : PoleBd (S.infSysOf Fc hSF hmon hdeg k hok hmon' hn' c h) B D δ)
    (hI : IndepInf (S.infSysOf Fc hSF hmon hdeg k hok hmon' hn' c h) B D δ)
    (hprec : ∀ j, c.N * synDelta k (dcOf D) (ofB (B j)) + c.N ≤ c.prec) :
    ∃ Linf, basisCheckInfS S.F.natDegree k (bcOf B) (dcOf D) (List.ofFn δ) c Linf = true := by
  classical
  set τ := S.infSysOf Fc hSF hmon hdeg k hok hmon' hn' c h with hτ
  set sy : Fin S.F.natDegree → ℕ := fun j ↦ synDelta k (dcOf D) (ofB (B j)) with hsy
  have hN : 0 < c.N := N_pos_of_certCheck h
  have hrep := fun j m ↦ S.inf_rep Fc hSF hmon hdeg k hok hmon' hn' c h B D hD j m
  choose V hV hVt using hrep
  have hδL : ∀ j : Fin S.F.natDegree, (List.ofFn δ).getD j 0 = δ j := fun j ↦ by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  -- the coefficients of `T^{N δ} wⱼ`
  have hcoef : ∀ j m (t : ℤ), (single ((τ.N * δ j : ℕ) : ℤ) (1 : F) * τ.ev m (S.fnWQ (B j) D)).coeff t =
      if 0 ≤ t + ((c.N * sy j : ℕ) : ℤ) - ((c.N * δ j : ℕ) : ℤ) then
        PowerSeries.coeff (t + ((c.N * sy j : ℕ) : ℤ) - ((c.N * δ j : ℕ) : ℤ)).toNat (V j m) else 0 := by
    intro j m t
    rw [hV j m, ← mul_assoc, single_mul_single, one_mul, coeff_single_ofPS]
    have e : t - (((τ.N * δ j : ℕ) : ℤ) + -((c.N * sy j : ℕ) : ℤ)) =
        t + ((c.N * sy j : ℕ) : ℤ) - ((c.N * δ j : ℕ) : ℤ) := by
      simp only [hτ, infSysOf]; ring
    rw [e]
  -- `δ ≤ synDelta`
  have hle : ∀ j, δ j ≤ sy j := by
    intro j
    by_contra hlt
    push Not at hlt
    have := hI (Pi.single j 1) fun m t ht ↦ by
      rw [Finset.sum_eq_single j (fun i _ hi ↦ by rw [Pi.single_eq_of_ne hi, map_zero, zero_mul])
        (by simp), Pi.single_eq_same, map_one, one_mul, hcoef, if_neg]
      have h1 : c.N * sy j + c.N ≤ c.N * δ j := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      have ht' : t < c.N := ht
      push_cast at h1 ⊢
      omega
    have h0 := congrFun this j
    rw [Pi.single_eq_same, Pi.zero_apply] at h0
    exact one_ne_zero h0
  -- the left inverse
  obtain ⟨Linf, hL⟩ := exists_leftInvCheck (matInfS (bcOf B) (dcOf D) k (List.ofFn δ) c)
    (S.F.natDegree * c.N) S.F.natDegree (fun cc hcc ↦ hI cc fun m t ht ↦ by
      rw [HahnSeries.coeff_sum]
      simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
      by_cases ht0 : t < 0
      · refine Finset.sum_eq_zero fun j _ ↦ ?_
        have hlb : LowerBd (single ((τ.N * δ j : ℕ) : ℤ) (1 : F) * τ.ev m (S.fnWQ (B j) D)) 0 := by
          have := (lowerBd_single ((τ.N * δ j : ℕ) : ℤ) (1 : F)).mul (hP j m)
          simpa using this
        rw [hlb t ht0, mul_zero]
      · push Not at ht0
        obtain ⟨t', rfl⟩ := Int.eq_ofNat_of_zero_le ht0
        have ht' : t' < c.N := by exact_mod_cast ht
        have hr : m * c.N + t' < S.F.natDegree * c.N := by
          have := m.2
          calc m * c.N + t' < m * c.N + c.N := by omega
            _ = (m + 1) * c.N := by ring
            _ ≤ S.F.natDegree * c.N := Nat.mul_le_mul_right _ this
        rw [← hcc _ hr]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hcoef, if_pos (by push_cast; nlinarith [hle j]), mul_comm]
        congr 1
        have hsh : (t' : ℤ) + ((c.N * sy j : ℕ) : ℤ) - ((c.N * δ j : ℕ) : ℤ) =
            ((c.N * (sy j - δ j) + t' : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub (hle j)]; ring
        have hb : c.N * (sy j - δ j) + t' < c.prec := by
          have h1 := hprec j
          have h2 : c.N * (sy j - δ j) ≤ c.N * sy j := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          simp only [hsy] at h1 h2 ⊢
          omega
        rw [hsh, Int.toNat_natCast, hVt j m _ hb]
        simp only [matInfS, bcOf_getD, hδL]
        rw [show (m * c.N + t') / c.N = m by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt ht', zero_add],
          show (m * c.N + t') % c.N = t' by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht']])
  refine ⟨Linf, ?_⟩
  simp only [basisCheckInfS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨by rw [dcOf_length]; omega, dcOf_last D hD⟩, fun j hj ↦ ?_⟩, hL⟩
  have hj' : (bcOf B).getD j [] = ofB (B ⟨j, hj⟩) := bcOf_getD B ⟨j, hj⟩
  have hδj : (List.ofFn δ).getD j 0 = δ ⟨j, hj⟩ := hδL ⟨j, hj⟩
  rw [hj', hδj]
  refine ⟨⟨⟨invOKb_synDelta k _ _, hle ⟨j, hj⟩⟩, ?_⟩, fun m hm t ht ↦ ?_⟩
  · have h1 := hprec ⟨j, hj⟩
    have h2 : c.N * (sy ⟨j, hj⟩ - δ ⟨j, hj⟩) ≤ c.N * sy ⟨j, hj⟩ :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    simp only [hsy] at h1 h2 ⊢
    omega
  · have h1 := hVt ⟨j, hj⟩ ⟨m, hm⟩ t (by
      have h1 := hprec ⟨j, hj⟩
      have h2 : c.N * (sy ⟨j, hj⟩ - δ ⟨j, hj⟩) ≤ c.N * sy ⟨j, hj⟩ :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      simp only [hsy] at h1 h2 ht ⊢
      omega)
    rw [← h1]
    set Y := synDelta k (dcOf D) (ofB (B ⟨j, hj⟩)) with hY
    have hsyY : sy ⟨j, hj⟩ = Y := rfl
    have ht' : t < c.N * (Y - δ ⟨j, hj⟩) := by rw [← hsyY]; exact ht
    have hle' : δ ⟨j, hj⟩ ≤ Y := by rw [← hsyY]; exact hle ⟨j, hj⟩
    have hmul : c.N * (Y - δ ⟨j, hj⟩) = c.N * Y - c.N * δ ⟨j, hj⟩ := Nat.mul_sub _ _ _
    have h2 := hP ⟨j, hj⟩ ⟨m, hm⟩ ((t : ℤ) - ((c.N * Y : ℕ) : ℤ)) (by
      simp only [hτ, infSysOf]
      have : c.N * δ ⟨j, hj⟩ ≤ c.N * Y := Nat.mul_le_mul_left _ hle'
      push_cast
      omega)
    rw [hV, coeff_single_ofPS, ← hY, if_pos (by push_cast; omega)] at h2
    rw [show ((t : ℤ) - ((c.N * Y : ℕ) : ℤ) - -((c.N * Y : ℕ) : ℤ)).toNat = t by omega] at h2
    exact h2

end CurveData

end InfCert

end Curves
