import RischTragerBronstein.Torsion.MobExist2
import RischTragerBronstein.Curves.Restrict
import RischTragerBronstein.Torsion.ValidExt
import RischTragerBronstein.Torsion.NonTorsExist3
import RischTragerBronstein.Torsion.BasePtsAlg

/-!
# Certificates exist (without infinity residues)

**`certExistsN_of_inf0`**: for a problem over `ℚ` with valid shape and separable at the finite
fibres and at infinity, whose computed residues above infinity vanish for all valid branch data,
certificates without the Möbius option exist:

* a first number field and integral basis give, over the constants `Kc`, non-special base fibres
  with integer abscissas (`exists_basepointsR`), whose coordinates are algebraic
  (`exists_QB_pre`);
* a number field containing them, the roots of unity and the branch data (`exists_valid_ext`);
* if every residue coordinate is torsion: logarithmic witnesses (`certExistsN_of_tors`); else the
  genus is positive (`genus_pos_of_nonTors`) and a non-torsion witness exists
  (`exists_torsOKP_of_base`, `hbase_of_C`).
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup NFC

section Final

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [CharZero Kc] [IsAlgClosed Kc]

/-- The embedding of `ℚ̄` into the constants. -/
noncomputable abbrev liftK : QB →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := QB) (M := Kc)).toRingHom

lemma rootQ_pre (Fc : BPoly ℚ) (hmon : (toB Fc).Monic) (m : ℕ) (y : Kc)
    (hy : evalW ((toB Fc).map (mapRingHom (algebraMap ℚ Kc))) (m : Kc) y = 0) :
    ∃ z : QB, liftK z = y := by
  refine exists_QB_pre ((toB Fc).map (evalRingHom (m : ℚ))) (hmon.map _).ne_zero y ?_
  rw [evalW, Polynomial.map_map] at hy
  rw [Polynomial.map_map]
  convert hy using 3
  refine RingHom.ext fun P ↦ ?_
  simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, coe_mapRingHom]
  rw [eval_map, show (m : Kc) = algebraMap ℚ Kc (m : ℚ) by simp, eval₂_at_apply]

/-- **Certificates exist when the residues above infinity vanish.** -/
theorem certExistsN_of_inf0 (P0 : CurveProb ℚ) (hS : P0.shapeOK = true)
    (hsep : ∃ (R : ℚ[X]) (A B : ℚ[X][X]), R ≠ 0 ∧
      Polynomial.C R = A * toB P0.Fc + B * derivative (toB P0.Fc))
    (hsepI : ∃ (R : ℚ[X]) (A B : ℚ[X][X]), R ≠ 0 ∧ Polynomial.C R =
      A * toB (invB P0.Fc P0.k (P0.k * P0.n)) +
        B * derivative (toB (invB P0.Fc P0.k (P0.k * P0.n))))
    (S : CurveData Kc E) (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc)))
    (hinf0 : ∀ (M : CPoly ℚ) (hM : Kron.irredQ M = true),
      haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∀ (pts : List (NF M × BranchCert (NF M))) (inf : BranchCert (NF M)),
        (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).valid = true →
        ∀ wt ∈ inf.ys, (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).resInf wt = 0) :
    CertExistsN P0 := by
  classical
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  have hS' := hS
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩, h7⟩, -⟩, h9⟩, -⟩, -⟩ := hS'
  obtain ⟨hmon, hn, hk⟩ := shape_monic P0.Fc P0.n P0.k h2 h3 h7
  have hSn : S.F.natDegree = P0.n := by
    rw [hSF, hmon.natDegree_map, hn]
  have hn0 : 0 < S.F.natDegree := by rw [hSn]; exact h1
  ------------------------------------------------------------------
  -- a first number field and an integral basis over the constants
  obtain ⟨M0, hM0, -, θ0, hθ0, -, pts0, inf0, hvalid0, hnd0, -, -⟩ :=
    exists_valid_ext P0 hS hsep hsepI ∅
  haveI : Fact (Irreducible (toPoly M0)) := ⟨Kron.irredQ_sound M0 hM0⟩
  set ψ0 : NF M0 →+* Kc := liftK.comp (rho M0 hθ0) with hψ0
  set P00 := P0.baseChange (algebraMap ℚ (NF M0)) P0.k pts0 inf0 with hP00
  have hV0 := P00.valid_spec hvalid0
  have hψ0q : ψ0.comp (algebraMap ℚ (NF M0)) = algebraMap ℚ Kc := Subsingleton.elim _ _
  have hSF0 : S.F = (toB P00.Fc).map (mapRingHom ψ0) := by
    rw [hSF, hP00, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp, hψ0q]
  letI : Algebra (NF M0) E := ((algebraMap Kc E).comp ψ0).toAlgebra
  have hmon0 : (toB P00.Fc).Monic := hV0.mon
  set SF0 := S.restrict ψ0 (fun _ ↦ rfl) (toB P00.Fc) hSF0 hmon0 with hSF0def
  obtain ⟨T0, hT0, hT0F, hT0n, -, -, -⟩ := exists_globalCert P00 hvalid0 hV0 hnd0 SF0 rfl
  have hT0f := globalCheck_spec hT0
  have hSF0' : S.F = (toB T0.Fc).map (mapRingHom ψ0) := by rw [hT0F]; exact hSF0
  have hnT0 : T0.n = S.F.natDegree := by rw [hT0n, hSn]; rfl
  have hB0 := ibCheckR_spec (K := Kc) S T0.Fc ψ0 hSF0' T0.n T0.k hnT0 T0.I T0.G hT0f.ib
    (dvd_of_eq hT0f.G_eq.symm)
  set B0 : Fin S.F.natDegree → Kc[X][X] := fun j ↦ (toB (T0.I.Bc.getD j [])).map (mapRingHom ψ0)
  set D0 : Kc[X] := (toPoly T0.I.Dc).map ψ0
  set δ0 : Fin S.F.natDegree → ℕ := fun j ↦ T0.I.δL.getD j 0
  have hnorm0 := hT0f.norm
  simp only [normCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hnorm0
  obtain ⟨⟨hBn0, hδn0⟩, hδs0⟩ := hnorm0
  have hB00 : B0 ⟨0, hn0⟩ = Polynomial.C D0 := by
    simp only [B0, D0, hBn0]
    rw [toB_cons, toB_nil, mul_zero, add_zero, Polynomial.map_C]; rfl
  have hδ00 : δ0 ⟨0, hn0⟩ = 0 := hδn0
  have hδ0 : ∀ j, j ≠ ⟨0, hn0⟩ → 1 ≤ δ0 j := fun j hj ↦ by
    have := hδs0 j (by rw [hnT0]; exact j.2)
    rcases this with h | h
    · exact absurd (Fin.ext h) hj
    · exact h
  have hsumge : S.F.natDegree ≤ ∑ j, δ0 j + 1 := by
    have : ∀ j ∈ Finset.univ.erase (⟨0, hn0⟩ : Fin S.F.natDegree), 1 ≤ δ0 j := fun j hj ↦
      hδ0 j (Finset.ne_of_mem_erase hj)
    have h' := Finset.card_nsmul_le_sum _ _ 1 this
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at h'
    calc S.F.natDegree ≤ S.F.natDegree - 1 + 1 := by omega
      _ ≤ (Finset.univ.erase (⟨0, hn0⟩ : Fin S.F.natDegree)).sum δ0 + 1 := by omega
      _ ≤ ∑ j, δ0 j + 1 := by
        exact Nat.add_le_add_right (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)) 1
  set g := ∑ j, δ0 j + 1 - S.F.natDegree with hg
  have hsum : ∑ j, δ0 j = g + S.F.natDegree - 1 := by omega
  have hsum0 : ∑ j, δ0 j + 1 = g + S.F.natDegree := by omega
  ------------------------------------------------------------------
  -- base fibres over the constants, with integer abscissas
  set Z : Finset Kc := ((toPoly (mul P0.D (discRC P0.Fc P0.n P0.k))).map (algebraMap ℚ Kc)).roots.toFinset
  have hR : ∀ s : Finset Kc, ∃ x, x ∉ s ∧ ∃ m : ℕ, (m : Kc) = x := fun s ↦ by
    obtain ⟨m, hm⟩ := (Set.infinite_range_of_injective (Nat.cast_injective (R := Kc))).exists_notMem_finset s
    obtain ⟨m', rfl⟩ := hm.1
    exact ⟨_, hm.2, m', rfl⟩
  obtain ⟨f0, hinj0, hbad0, hD0x, hroot0, hsimple0, hns0, hR0⟩ :=
    exists_basepointsR (fun x ↦ ∃ m : ℕ, (m : Kc) = x) hR S.F S.monic rfl hn0 B0 hB0.deg D0 hB0.hD
      S.discR_ne_zero hB0.det δ0 hδ00 hδ0 hsum Z
  choose mx hmx using hR0
  -- algebraic preimages
  have hpre_y : ∀ l k, ∃ z : QB, liftK z = (f0 l).ys k := fun l k ↦ by
    refine rootQ_pre P0.Fc hmon (mx l) _ ?_
    rw [← hSF, hmx]; exact hroot0 l k
  choose zy hzy using hpre_y
  set extra : Finset QB := (Finset.univ.image fun l : Fin g ↦ ((mx l : ℕ) : QB)) ∪
    (Finset.univ.image fun lk : Fin g × Fin S.F.natDegree ↦ zy lk.1 lk.2) with hextra
  ------------------------------------------------------------------
  -- the number field
  obtain ⟨M, hM, hMint, θ, hθ, hex, pts, inf, hvalid, hnd, hroots, hζQ⟩ :=
    exists_valid_ext P0 hS hsep hsepI extra
  haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  set ψ : NF M →+* Kc := liftK.comp (rho M hθ) with hψ
  set P := P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf with hP
  have hV := P.valid_spec hvalid
  have hψq : ψ.comp (algebraMap ℚ (NF M)) = algebraMap ℚ Kc := Subsingleton.elim _ _
  have hSFP : S.F = (toB P.Fc).map (mapRingHom ψ) := by
    rw [hSF, hP, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp, hψq]
  have hζ : ∀ ac ∈ P.pts, ∃ ζF : NF M, IsPrimitiveRoot (ψ ζF) ac.2.N := fun ac hac ↦ by
    obtain ⟨ζF, hζF⟩ := hζQ ac hac
    exact ⟨ζF, hζF.map_of_injective liftK.injective⟩
  have hinfP : ∀ wt ∈ P.inf.ys, P.resInf wt = 0 := hinf0 M hM pts inf hvalid
  -- the base coordinates in the number field
  have hxF : ∀ l, ∃ c : NF M, ψ c = (f0 l).x := fun l ↦ by
    obtain ⟨c, hc⟩ := hex _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ l)))
    refine ⟨c, ?_⟩
    rw [hψ, RingHom.comp_apply, hc, map_natCast, hmx]
  have hyF : ∀ l k, ∃ c : NF M, ψ c = (f0 l).ys k := fun l k ↦ by
    obtain ⟨c, hc⟩ := hex _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun lk : Fin g × Fin S.F.natDegree ↦ zy lk.1 lk.2) (Finset.mem_univ (l, k))))
    exact ⟨c, by rw [hψ, RingHom.comp_apply, hc, hzy]⟩
  choose xF hxF using hxF
  choose yF hyF using hyF
  have havoid : ∀ l, ∀ ac ∈ P.pts, xF l ≠ ac.1 := fun l ac hac h ↦ by
    apply hbad0 l
    rw [← hxF, h]
    have h0 := hroots ac hac
    have hR0 : toPoly P0.R0 ≠ 0 := fun h0 ↦ by
      rw [← trim_eq_nil_iff] at h0; rw [h0] at h9; simp at h9
    have hQ0 : toPoly (mul P0.D (discRC P0.Fc P0.n P0.k)) ≠ 0 := by
      rw [CPoly.toPoly_mul, mul_comm, ← CPoly.toPoly_mul, ← toPoly_trim]
      exact hR0
    simp only [Z, Multiset.mem_toFinset]
    rw [mem_roots ((Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr hQ0), IsRoot.def]
    have hm : (toPoly (mul P0.D (discRC P0.Fc P0.n P0.k))).map (algebraMap ℚ Kc) =
        ((toPoly (mul P0.D (discRC P0.Fc P0.n P0.k))).map (algebraMap ℚ QB)).map liftK := by
      rw [Polynomial.map_map]; congr 1; exact Subsingleton.elim _ _
    rw [hm, eval_map, hψ, RingHom.comp_apply, eval₂_hom, h0, map_zero]
  ------------------------------------------------------------------
  -- the dichotomy
  by_cases hall : ∀ j : Fin (dim (NF M)), ∃ m, 0 < m ∧ ∃ Λ : Kc →ₗ[ℚ] ℚ,
      (∀ r : NF M, Λ (algebraMap Kc Kc (ψ r)) = coord j r) ∧ ∃ w : Kc⟮S.x⟯⟮S.y⟯, w ≠ 0 ∧
        S.TorsOrdStd P ψ m w Λ
  · exact certExistsN_of_tors (K := Kc) P0 M hM pts inf hvalid S ψ hSFP hall
  push Not at hall
  obtain ⟨j₀, hNT'⟩ := hall
  have hNT : ∀ m, 0 < m → ∀ Λ : Kc →ₗ[ℚ] ℚ, (∀ r : NF M, Λ (ψ r) = coord j₀ r) →
      ∀ w : Kc⟮S.x⟯⟮S.y⟯, w ≠ 0 → ¬ S.TorsOrdStd (K := Kc) P ψ m w Λ := fun m hm Λ hΛ w hw ↦
    hNT' m hm Λ (fun r ↦ by rw [Algebra.algebraMap_self, RingHom.id_apply]; exact hΛ r) w hw
  -- the curve over the number field
  letI : Algebra (NF M) E := ((algebraMap Kc E).comp ψ).toAlgebra
  set SF := S.restrict ψ (fun _ ↦ rfl) (toB P.Fc) hSFP hV.mon with hSFdef
  -- positive genus
  obtain ⟨T, hT, hTF, hTn, -, -, -⟩ := exists_globalCert P hvalid hV hnd SF rfl
  have hgen := S.genus_pos_of_nonTors P hSFP hV hζ j₀ hnd hinfP T hT hTF hNT
  have hTf := globalCheck_spec hT
  have hSFT : S.F = (toB T.Fc).map (mapRingHom ψ) := by rw [hTF]; exact hSFP
  have hnT : T.n = S.F.natDegree := by rw [hTn, hSn]; rfl
  have hBT := ibCheckR_spec (K := Kc) S T.Fc ψ hSFT T.n T.k hnT T.I T.G hTf.ib (dvd_of_eq hTf.G_eq.symm)
  have hδeq := CurveData.sum_delta_eq hB0 hBT
  have hg0 : 0 < g := by
    have : ∑ j, δ0 j + 1 ≠ S.F.natDegree := by rw [hδeq]; exact hgen
    omega
  -- the non-torsion witness
  have hint : Curves.intCoeffs M = some (M.map Rat.num) := by
    unfold Curves.intCoeffs
    rw [if_pos (List.all_eq_true.mpr fun q hq ↦ by simpa using hMint q hq)]
  obtain ⟨tw, htw⟩ := S.exists_torsOKP_of_base P hSFP hV hζ j₀ hint hvalid hnd hinfP hNT SF rfl
    (hbase_of_C S ψ P hV hSFP hB0 hn0 hB00 hg0 hsum0 f0 hinj0 hns0 hD0x hroot0 hsimple0 xF hxF
      yF hyF havoid)
  refine ⟨M, hM, pts, inf, [], [tw], ?_⟩
  unfold decideLogTP
  split
  · simp
  · have htw' : torsOKP (redAtM M) (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf) tw = true :=
      htw
    simp [htw']

end Final

end Curves
