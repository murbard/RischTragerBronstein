import RischTragerBronstein.Mixed.KYSem

/-!
# The column code over `K_{m+1} ⊗ N`

`liftNFM φ₀ ρ`: the ring homomorphism `Kₘ ⊗ N → E` extending `φ₀ : Kₘ → E` by `X ↦ ρ`, for any
root `ρ ∈ E` of `M`. `kyColM_spec`: for a differential field `E ⊇ L` and a constant root `ρ` of
`M` in `E`, the extended gcd computation of `kyColM` becomes, through `liftNFM`, the identities of
`twist_dlog` for the polynomial whose coefficients are `∑_f W_{i,f} ρᶠ`, and the coordinates of
the column give `zʲ Dⱼ/g`.
-/

open Polynomial Differential IntermediateField CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

section Lift

variable {Fc : BPoly ℚ} [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (M : CPoly ℚ)
  [Fact (Irreducible (toPoly (liftQ Fc m M)))] {E : Type*} [Field E] (φ₀ : KF Fc m →+* E) (ρ : E)
  (hρ : (toPoly (liftQ Fc m M)).eval₂ φ₀ ρ = 0)

/-- **`Kₘ ⊗ N → E`**, `X ↦ ρ`. -/
noncomputable def liftNFM : NFM Fc m M →+* E :=
  (AdjoinRoot.lift φ₀ ρ hρ).comp (NFK.toARHom _)

lemma liftNFM_val (a : NFM Fc m M) : liftNFM m M φ₀ ρ hρ a = (toPoly a.1).eval₂ φ₀ ρ := by
  simp only [liftNFM, RingHom.comp_apply]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk _ (toPoly a.1)) = _
  rw [AdjoinRoot.lift_mk]

lemma liftNFM_mk (l : CPoly (KF Fc m)) :
    liftNFM m M φ₀ ρ hρ (NFK.mk _ l) = (toPoly l).eval₂ φ₀ ρ := by
  simp only [liftNFM, RingHom.comp_apply]
  change AdjoinRoot.lift _ _ _ (NFK.toAR _ (NFK.mk _ l)) = _
  rw [NFK.toAR_mk, AdjoinRoot.lift_mk]

lemma liftNFM_embM (a : KF Fc m) : liftNFM m M φ₀ ρ hρ (embM Fc m M a) = φ₀ a := by
  rw [embM, liftNFM_mk]; simp

lemma eval₂_list_sum {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (x : S)
    (l : List R) : (toPoly l).eval₂ φ x = ∑ f ∈ Finset.range l.length, φ (l.getD f 0) * x ^ f := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [toPoly_cons, eval₂_add, eval₂_C, eval₂_mul, eval₂_X, ih, List.length_cons,
      Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun f _ ↦ by ring

lemma eval₂_list_sum' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (x : S)
    (l : List R) (N : ℕ) (hN : l.length ≤ N) :
    (toPoly l).eval₂ φ x = ∑ f ∈ Finset.range N, φ (l.getD f 0) * x ^ f := by
  rw [eval₂_list_sum, ← Finset.sum_range_add_sum_Ico _ hN]
  rw [Finset.sum_eq_zero (s := Finset.Ico _ _) fun f hf ↦ by
    rw [List.getD_eq_default _ _ (Finset.mem_Ico.mp hf).1, map_zero, zero_mul], add_zero]

end Lift

end Curves.MT

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 4000000 in
/-- **The column code over `K_{m+1} ⊗ N`**, read in a differential field `E ⊇ L` through a
constant root `ρ` of `M`. -/
theorem kyColM_spec (m n : ℕ) (hn : 0 < n) (hTr : T.Tr (m + 1)) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (htrim : CPoly.trim M = M) (hlen : 1 < M.length)
    (Ah : GPoly (LC m)) (z : LC m) (j : ℕ) (W : BPoly (NFM Fc m M)) (cols : List (LC (m + 1)))
    (h : kyColM Fc ks m n M Ah z j W = some cols)
    {E : Type*} [Field E] [CharZero E] [Differential E] [Algebra L E] [DifferentialAlgebra L E]
    (ρE : E) (hρE : aeval ρE (toPoly M) = 0) (hρd : ρE′ = 0) :
    ∃ Wd s1 s2 Q D : E[X], ∃ gg : E, gg ≠ 0 ∧
      (∀ i, Wd.coeff i = ((toPoly (W.map fun c ↦ ∑ f ∈ Finset.range (M.length - 1),
          algebraMap L E (T.ev (m + 1) (pcP Fc ks m ((c.map fun a ↦ a.1.getD f 0).map (unTr Fc m)))) *
            ρE ^ f)).coeff i)′ +
        i * (((1 / n : ℚ) : E) * ((algebraMap L E (T.ev (m + 1) (pcP Fc ks m Ah)))′ *
          (algebraMap L E (T.ev (m + 1) (pcP Fc ks m Ah)))⁻¹)) *
          (toPoly (W.map fun c ↦ ∑ f ∈ Finset.range (M.length - 1),
            algebraMap L E (T.ev (m + 1) (pcP Fc ks m ((c.map fun a ↦ a.1.getD f 0).map (unTr Fc m)))) *
              ρE ^ f)).coeff i) ∧
      s1 * toPoly (W.map fun c ↦ ∑ f ∈ Finset.range (M.length - 1),
          algebraMap L E (T.ev (m + 1) (pcP Fc ks m ((c.map fun a ↦ a.1.getD f 0).map (unTr Fc m)))) *
            ρE ^ f) +
        s2 * (X ^ n - Polynomial.C (algebraMap L E (T.ev (m + 1) (pcP Fc ks m Ah)))) = Polynomial.C gg ∧
      Wd * s1 = Q * (X ^ n - Polynomial.C (algebraMap L E (T.ev (m + 1) (pcP Fc ks m Ah)))) + D ∧
      (∀ i, n ≤ i → D.coeff i = 0) ∧
      ∑ f ∈ Finset.range (M.length - 1),
          algebraMap L E (T.ev (m + 1) (cols.getD f (MO Fc ks (m + 1)).zero)) * ρE ^ f =
        algebraMap L E (T.ev (m + 1) (pcP Fc ks m [powC (MO Fc ks m) z j])) * D.coeff j / gg ∧
      ∃ (D' : (NFM Fc (m + 1) M)[X]) (g' : NFM Fc (m + 1) M) (hroot : (toPoly (liftQ Fc (m + 1) M)).eval₂
          ((algebraMap L E).comp ((algebraMap (T.F (m + 1)) L).comp (T.psiF (m + 1) hTr))) ρE = 0),
        D = D'.map (liftNFM (m + 1) M ((algebraMap L E).comp ((algebraMap (T.F (m + 1)) L).comp
          (T.psiF (m + 1) hTr))) ρE hroot) ∧
        gg = liftNFM (m + 1) M ((algebraMap L E).comp ((algebraMap (T.F (m + 1)) L).comp
          (T.psiF (m + 1) hTr))) ρE hroot g' := by
  classical
  unfold kyColM at h
  simp only at h
  split_ifs at h with hgl
  obtain rfl := (Option.some.inj h).symm
  set d := M.length - 1 with hd
  set evE : LC (m + 1) → E := fun q ↦ algebraMap L E (T.ev (m + 1) q) with hevE
  have hsem : ∀ q, T.ev (m + 1) q = (((T.MP (m + 1) hTr).sem q : T.F (m + 1)) : L) :=
    fun q ↦ (T.sem_MP (m + 1) hTr q).symm
  set φ₀ : KF Fc (m + 1) →+* E :=
    (algebraMap L E).comp ((algebraMap (T.F (m + 1)) L).comp (T.psiF (m + 1) hTr)) with hφ₀def
  have hφ₀ : ∀ q, φ₀ (trC Fc (m + 1) q) = evE q := fun q ↦ by
    simp only [hφ₀def, RingHom.comp_apply, T.psiF_trC (m + 1) hTr, hevE, hsem]
    rfl
  have hroot : (toPoly (liftQ Fc (m + 1) M)).eval₂ φ₀ ρE = 0 := by
    rw [toPoly_liftQ, eval₂_map, show φ₀.comp (algebraMap ℚ (KF Fc (m + 1))) = algebraMap ℚ E
      from RingHom.ext_rat _ _, ← aeval_def, hρE]
  set Φ := liftNFM (m + 1) M φ₀ ρE hroot with hΦ
  have hMne : M ≠ [] := fun h0 ↦ by rw [h0] at hlen; simp at hlen
  have hMdeg : (toPoly M).natDegree = d := by
    have := CPoly.length_trim (p := M) (by rw [htrim]; exact hMne)
    rw [htrim] at this; omega
  have hLdeg : (toPoly (liftQ Fc (m + 1) M)).natDegree = d := by
    rw [toPoly_liftQ, natDegree_map_eq_of_injective (algebraMap ℚ _).injective, hMdeg]
  -- `Φ` on coordinates
  have hΦN : ∀ cs : List (LC (m + 1)), cs.length ≤ d →
      Φ (NFK.mk _ (cs.map (trC Fc (m + 1)))) = ∑ f ∈ Finset.range d,
        evE (cs.getD f (MO Fc ks (m + 1)).zero) * ρE ^ f := by
    intro cs hcs
    rw [hΦ, liftNFM_mk, eval₂_list_sum' _ _ _ d (by simpa using hcs)]
    refine Finset.sum_congr rfl fun f _ ↦ ?_
    by_cases hf : f < cs.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hf), List.getElem_map, hφ₀,
        List.getD_eq_getElem _ _ hf]
    · rw [List.getD_eq_default _ _ (by simpa using hf), List.getD_eq_default _ _ (by omega),
        map_zero]
      simp only [hevE, hsem, (T.MP (m + 1) hTr).sem_zero]
      simp
  set tr := trC Fc (m + 1)
  set toN : List (LC (m + 1)) → NFM Fc (m + 1) M := fun cf ↦ NFK.mk _ (cf.map tr) with htoN
  set Wc : List (List (LC (m + 1))) := W.map (kyCoords Fc ks m M d) with hWc
  have hWcl : ∀ i, (Wc.getD i []).length ≤ d := fun i ↦ by
    by_cases hi : i < Wc.length
    · rw [List.getD_eq_getElem _ _ hi]; simp [hWc, kyCoords]
    · rw [List.getD_eq_default _ _ (by omega)]; simp
  set Ahc := pcP Fc ks m Ah with hAhc
  set rc := (MO Fc ks (m + 1)).mul (mcst Fc ks (m + 1) (1 / n)) ((MO Fc ks (m + 1)).mul ((MO Fc ks (m + 1)).deriv Ahc) ((MO Fc ks (m + 1)).inv Ahc)) with hrc
  set Wd : List (List (LC (m + 1))) := (List.range Wc.length).map fun i ↦
    (Wc.getD i []).map fun c ↦ (MO Fc ks (m + 1)).add ((MO Fc ks (m + 1)).deriv c) ((MO Fc ks (m + 1)).mul ((MO Fc ks (m + 1)).mul (mcst Fc ks (m + 1) i) rc) c) with hWd
  set WK : CPoly (NFM Fc (m + 1) M) := Wc.map toN with hWK
  set WdK : CPoly (NFM Fc (m + 1) M) := Wd.map toN with hWdK
  set MK : CPoly (NFM Fc (m + 1) M) := (-(embM Fc (m + 1) M (tr Ahc))) :: (List.replicate (n - 1) 0 ++ [1])
    with hMK
  set e := CPoly.egcd WK MK with he
  set gg := CPoly.trim e.1 with hgg
  set D := (CPoly.divMod (CPoly.mul WdK e.2.1) MK).2 with hD
  -- the semantics of the codes
  have hevadd : ∀ a b, evE ((MO Fc ks (m + 1)).add a b) = evE a + evE b := fun a b ↦ by
    simp only [hevE, hsem, (T.MP (m + 1) hTr).sem_add, IntermediateField.coe_add, map_add]
  have hevmul : ∀ a b, evE ((MO Fc ks (m + 1)).mul a b) = evE a * evE b := fun a b ↦ by
    simp only [hevE, hsem, (T.MP (m + 1) hTr).sem_mul, IntermediateField.coe_mul, map_mul]
  have hevder : ∀ a, evE ((MO Fc ks (m + 1)).deriv a) = (evE a)′ := fun a ↦ by
    simp only [hevE, hsem, (T.MP (m + 1) hTr).sem_deriv, MTower.coe_deriv, deriv_algebraMap]
  have hevinv : ∀ a, evE ((MO Fc ks (m + 1)).inv a) = (evE a)⁻¹ := fun a ↦ by
    simp only [hevE, hsem, (T.MP (m + 1) hTr).sem_inv, IntermediateField.coe_inv, map_inv₀]
  have hevc : ∀ q : ℚ, evE (mcst Fc ks (m + 1) q) = (q : E) := fun q ↦ by
    simp only [hevE, hsem, T.sem_mcst]
    rw [show (((q : ℚ) : T.F (m + 1)) : L) = (q : L) by simp, map_ratCast]
  -- the polynomials
  have hMKp : toPoly MK = X ^ n - Polynomial.C (embM Fc (m + 1) M (tr Ahc)) := toPoly_xnSubC _ n hn
  have hMK0 : toPoly MK ≠ 0 := by rw [hMKp]; exact X_pow_sub_C_ne_zero hn _
  have hMKm : (toPoly MK).map Φ = X ^ n - Polynomial.C (evE Ahc) := by
    rw [hMKp, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, hΦ, liftNFM_embM, hφ₀]
  have hWl : (toPoly WK).map Φ = toPoly (W.map fun c ↦ ∑ f ∈ Finset.range d,
      evE (pcP Fc ks m ((c.map fun a ↦ a.1.getD f 0).map (unTr Fc m))) * ρE ^ f) := by
    rw [← toPoly_map', hWK, hWc, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun c _ ↦ ?_
    simp only [Function.comp_apply]
    rw [hΦN _ (by simp [kyCoords])]
    refine Finset.sum_congr rfl fun f hf ↦ ?_
    rw [kyCoords, List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.mp hf),
      List.getElem_map, List.getElem_range]
  -- the gcd
  have hg1 : gg = [gg.getD 0 1] := by
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hgl
    rw [ha]; rfl
  have hg0 : gg.getD 0 1 ≠ 0 := by
    have hgl' : (CPoly.trim e.1).length = 1 := hgl
    have hne : CPoly.trim e.1 ≠ [] := fun h0 ↦ by rw [h0] at hgl'; simp at hgl'
    have h1 := getLast_trim_ne_zero e.1 hne
    rw [List.getLast_eq_getElem] at h1
    simp only [hgl'] at h1
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact h1
  have hge : toPoly e.1 = Polynomial.C (gg.getD 0 1) := by
    rw [← toPoly_trim, ← hgg, hg1]; simp
  have hbez := CPoly.egcd_spec WK MK
  rw [← he, hge] at hbez
  have hdm := CPoly.divMod_spec (CPoly.mul WdK e.2.1) MK
  rw [← hD, CPoly.toPoly_mul] at hdm
  have hdeg := CPoly.divMod_degree_lt (CPoly.mul WdK e.2.1) MK hMK0
  rw [← hD] at hdeg
  have hMKdeg : (toPoly MK).degree = n := by rw [hMKp, degree_X_pow_sub_C hn]
  refine ⟨(toPoly WdK).map Φ, (toPoly e.2.1).map Φ, (toPoly e.2.2).map Φ,
    (toPoly (CPoly.divMod (CPoly.mul WdK e.2.1) MK).1).map Φ, (toPoly D).map Φ, Φ (gg.getD 0 1),
    (map_ne_zero Φ).mpr hg0, fun i ↦ ?_, ?_, ?_, fun i hi ↦ ?_, ?_,
    ⟨toPoly D, gg.getD 0 1, hroot, rfl, rfl⟩⟩
  · -- the derivatives
    rw [← hWl, coeff_map, coeff_map, coeff_toPoly, coeff_toPoly]
    by_cases hi : i < Wc.length
    · have hWdi : WdK.getD i 0 = toN ((Wc.getD i []).map fun c ↦ (MO Fc ks (m + 1)).add
          ((MO Fc ks (m + 1)).deriv c) ((MO Fc ks (m + 1)).mul ((MO Fc ks (m + 1)).mul
            (mcst Fc ks (m + 1) i) rc) c)) := by
        simp only [hWdK, hWd, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
          Option.map_some, Option.getD_some]
      have hWKi : WK.getD i 0 = toN (Wc.getD i []) := by
        simp only [hWK, List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getD_eq_getElem?_getD] at *
        rw [List.getElem?_eq_getElem hi]
        rfl
      rw [hWdi, hWKi, htoN, hΦN _ (by simpa using hWcl i), hΦN _ (hWcl i)]
      rw [Finset.mul_sum, show ∀ F : ℕ → E, (∑ f ∈ Finset.range d, F f)′ = ∑ f ∈ Finset.range d, (F f)′
        from fun F ↦ map_sum _ _ _, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f hf ↦ ?_
      by_cases hfl : f < (Wc.getD i []).length
      · rw [List.getD_eq_getElem _ _ (by simpa using hfl), List.getElem_map, hevadd, hevder, hevmul,
          hevmul, hevc, hrc, hevmul, hevc, hevmul, hevder, hevinv, Derivation.leibniz,
          Derivation.leibniz_pow, hρd, List.getD_eq_getElem _ _ hfl]
        simp only [smul_zero, zero_add, smul_eq_mul, hAhc]
        push_cast
        ring
      · rw [List.getD_eq_default _ _ (by simpa using hfl), List.getD_eq_default _ _ (by omega)]
        simp [hevE, hsem, (T.MP (m + 1) hTr).sem_zero]
    · rw [List.getD_eq_default _ _ (by simp [hWdK, hWd]; omega),
        List.getD_eq_default _ _ (by simp [hWK]; omega), map_zero, map_zero]
      simp
  · rw [← hWl, ← hMKm, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hbez,
      Polynomial.map_C]
  · rw [← hMKm, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, ← hdm]
  · rw [coeff_map, coeff_eq_zero_of_degree_lt, map_zero]
    calc (toPoly D).degree < n := hMKdeg ▸ hdeg
      _ ≤ i := by exact_mod_cast hi
  · -- the column
    set col := embM Fc (m + 1) M (tr (pcP Fc ks m [powC (MO Fc ks m) z j])) *
      (D.getD j 0 * (gg.getD 0 1)⁻¹) with hcol
    have hcl : col.1.length ≤ d := by
      by_cases h0 : col.1 = []
      · rw [h0]; simp
      have htr : CPoly.trim col.1 = col.1 := by rw [← col.2, NFK.norm, CPoly.trim_trim]
      have hl := CPoly.length_trim (p := col.1) (by rw [htr]; exact h0)
      rw [htr] at hl
      have hdv := NFK.degree_val (liftQ Fc (m + 1) M) col
      have hne : toPoly col.1 ≠ 0 := fun h1 ↦ h0 (by
        have := (CPoly.trim_eq_nil_iff col.1).mpr h1; rwa [htr] at this)
      rw [degree_eq_natDegree hne, degree_eq_natDegree (Irreducible.ne_zero Fact.out), hLdeg] at hdv
      have : (toPoly col.1).natDegree < d := by exact_mod_cast hdv
      omega
    have hΦcol : Φ col = ∑ f ∈ Finset.range d, φ₀ (col.1.getD f 0) * ρE ^ f := by
      rw [hΦ, liftNFM_val, eval₂_list_sum' _ _ _ d hcl]
    have hcols : ∀ f ∈ Finset.range d, algebraMap L E (T.ev (m + 1)
        (((List.range d).map (fun f ↦ normC Fc (m + 1) (unTr Fc (m + 1) (col.1.getD f 0)))).getD f
          (MO Fc ks (m + 1)).zero)) * ρE ^ f = φ₀ (col.1.getD f 0) * ρE ^ f := by
      intro f hf
      rw [List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.mp hf), List.getElem_map,
        List.getElem_range, T.ev_normC (m + 1) hTr, T.ev_unTr (m + 1) hTr]
      rfl
    rw [Finset.sum_congr rfl hcols, ← hΦcol, hcol,
      map_mul, map_mul, map_inv₀, hΦ, liftNFM_embM, hφ₀, coeff_map, coeff_toPoly]
    rw [← hΦ]
    ring


end MTower

end Curves.MT
