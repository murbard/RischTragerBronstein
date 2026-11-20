import RischTragerBronstein.Torsion.TorsResExist4

/-!
# Residue data at places from a valid problem (4): the certificate

**`exists_placeRes`**: for a valid problem over `F` (with the primitive roots of unity of the
ramification indices, distinct special points, and vanishing computed residues above infinity),
and any coordinate `j₀`, there are a place certificate `Pc` (the places of all special fibres),
integers `eL` and a scale `s` passing `Pc.check` and `torsResCheckP`.

The multiplicity of a place `π` above `a_j` is `s ρ_π + eL_j e_π` with `ρ_π = coord_{j₀}(res_π)/s_π`
(`s` clears the denominators, `eL_j` makes them non-negative); their sum is `n ∑ eL_j` by the
residue theorem (`sum_places_res`).
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries

section Cert

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : F, IsPrimitiveRoot (ψ ζF) ac.2.N) (j₀ : Fin (dim F))

/-- The `j₀`-coordinate of the residue of the place series `π` of the fibre `j`. -/
noncomputable def crj (j : Fin P.pts.length) (π : Fin S.F.natDegree) : ℚ :=
  coord j₀ (S.Rj P hSF hV hζ j π / ((S.Φj P hSF hV j).sIdx (S.ζj_spec P hSF hV hζ j) π : F))

/-- The common denominator. -/
noncomputable def sden : ℕ := ∏ j, ∏ π, (S.crj P hSF hV hζ j₀ j π).den

lemma sden_pos : 0 < S.sden P hSF hV hζ j₀ :=
  Finset.prod_pos fun j _ ↦ Finset.prod_pos fun π _ ↦ (S.crj P hSF hV hζ j₀ j π).den_pos

lemma den_dvd_sden (j : Fin P.pts.length) (π : Fin S.F.natDegree) :
    (S.crj P hSF hV hζ j₀ j π).den ∣ S.sden P hSF hV hζ j₀ :=
  (Finset.dvd_prod_of_mem _ (Finset.mem_univ π)).trans (Finset.dvd_prod_of_mem
    (fun j ↦ ∏ π, (S.crj P hSF hV hζ j₀ j π).den) (Finset.mem_univ j))

/-- The scaled coordinate (an integer). -/
noncomputable def zj (j : Fin P.pts.length) (π : Fin S.F.natDegree) : ℤ :=
  ((S.sden P hSF hV hζ j₀ / (S.crj P hSF hV hζ j₀ j π).den : ℕ) : ℤ) * (S.crj P hSF hV hζ j₀ j π).num

lemma zj_eq (j : Fin P.pts.length) (π : Fin S.F.natDegree) :
    (S.zj P hSF hV hζ j₀ j π : ℚ) = S.sden P hSF hV hζ j₀ * S.crj P hSF hV hζ j₀ j π := by
  set q := S.crj P hSF hV hζ j₀ j π
  obtain ⟨c, hc⟩ := S.den_dvd_sden P hSF hV hζ j₀ j π
  have hq : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
  rw [zj, hc, Nat.mul_div_cancel_left _ q.den_pos]
  push_cast
  rw [hq]; ring

/-- The shift of the fibre `j`. -/
noncomputable def eLj (j : Fin P.pts.length) : ℕ := ∑ π, (S.zj P hSF hV hζ j₀ j π).natAbs

/-- The multiplicity of the place `π` of the fibre `j`. -/
noncomputable def Γj (j : Fin P.pts.length) (π : Fin S.F.natDegree) : ℕ :=
  (S.zj P hSF hV hζ j₀ j π +
    S.eLj P hSF hV hζ j₀ j * (S.Φj P hSF hV j).period (S.ζj_spec P hSF hV hζ j) π).toNat

lemma Γj_eq (j : Fin P.pts.length) (π : Fin S.F.natDegree) :
    (S.Γj P hSF hV hζ j₀ j π : ℤ) = S.zj P hSF hV hζ j₀ j π +
      S.eLj P hSF hV hζ j₀ j * (S.Φj P hSF hV j).period (S.ζj_spec P hSF hV hζ j) π := by
  rw [Γj, Int.toNat_of_nonneg]
  have h1 : (S.zj P hSF hV hζ j₀ j π).natAbs ≤ S.eLj P hSF hV hζ j₀ j :=
    Finset.single_le_sum (f := fun π ↦ (S.zj P hSF hV hζ j₀ j π).natAbs)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ π)
  have h2 := (S.Φj P hSF hV j).period_pos (S.ζj_spec P hSF hV hζ j) π
  have h3 : (S.eLj P hSF hV hζ j₀ j : ℤ) ≤
      S.eLj P hSF hV hζ j₀ j * (S.Φj P hSF hV j).period (S.ζj_spec P hSF hV hζ j) π := by
    exact_mod_cast Nat.le_mul_of_pos_right _ h2
  have h4 : -(S.zj P hSF hV hζ j₀ j π) ≤ (S.eLj P hSF hV hζ j₀ j : ℤ) := by
    have h5 : -(S.zj P hSF hV hζ j₀ j π) ≤ ((S.zj P hSF hV hζ j₀ j π).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]; exact neg_le_abs _
    have h6 : ((S.zj P hSF hV hζ j₀ j π).natAbs : ℤ) ≤ S.eLj P hSF hV hζ j₀ j := by exact_mod_cast h1
    omega
  omega

/-- The local data of all special fibres. -/
noncomputable def Ls (tx : ℕ := 0) : List (LocPlaces F) :=
  List.ofFn fun j ↦ S.lpj P hSF hV hζ j (S.Γj P hSF hV hζ j₀ j) tx

/-- **The place certificate.** -/
noncomputable def PcE (tx : ℕ := 0) : PlaceCert F :=
  assemble (S.Ls P hSF hV hζ j₀ tx) (∑ j, S.eLj P hSF hV hζ j₀ j)

lemma Ls_length (tx : ℕ := 0) : (S.Ls P hSF hV hζ j₀ tx).length = P.pts.length := by simp [Ls]

lemma Ls_getD (j : ℕ) (hj : j < P.pts.length) (tx : ℕ := 0) :
    (S.Ls P hSF hV hζ j₀ tx).getD j locDef =
      S.lpj P hSF hV hζ ⟨j, hj⟩ (S.Γj P hSF hV hζ j₀ ⟨j, hj⟩) tx := by
  rw [Ls, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]

lemma lpj_Γ_sum (j : Fin P.pts.length) (Γf : Fin S.F.natDegree → ℕ) (tx : ℕ := 0) :
    (S.lpj P hSF hV hζ j Γf tx).Γ.sum = ∑ π ∈ Finset.univ.filter
      (fun π ↦ (S.Φj P hSF hV j).rep (S.ζj_spec P hSF hV hζ j) π = π), Γf π := by
  simp only [lpj, SplitFibre.locPlaces, SplitFibre.repL]
  exact SplitFibre.sum_sort_map _ _


/-- **The multiplicities add up to `n ∑ eL_j`.** -/
lemma sum_Γj (hnd : (P.pts.map Prod.fst).Nodup) (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0)
    (tx : ℕ := 0) :
    ∑ j, ((S.lpj P hSF hV hζ j (S.Γj P hSF hV hζ j₀ j) tx).Γ.sum : ℤ) =
      (∑ j, S.eLj P hSF hV hζ j₀ j : ℕ) * P.n := by
  have hn := S.natDegree_F_eq P ψ hSF hV
  have hz : ∑ j : Fin P.pts.length, ∑ π ∈ Finset.univ.filter
      (fun π ↦ (S.Φj P hSF hV j).rep (S.ζj_spec P hSF hV hζ j) π = π), (S.zj P hSF hV hζ j₀ j π : ℚ) = 0 := by
    simp only [S.zj_eq P hSF hV hζ j₀, ← Finset.mul_sum, crj, ← map_sum]
    rw [S.sum_places_res P hSF hV hζ hnd hinf0, map_zero, mul_zero]
  have hz' : ∑ j : Fin P.pts.length, ∑ π ∈ Finset.univ.filter
      (fun π ↦ (S.Φj P hSF hV j).rep (S.ζj_spec P hSF hV hζ j) π = π), S.zj P hSF hV hζ j₀ j π = 0 := by
    exact_mod_cast hz
  simp only [S.lpj_Γ_sum P hSF hV hζ _ _ tx, Nat.cast_sum, S.Γj_eq P hSF hV hζ j₀, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [hz', zero_add, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  rw [← hn]
  exact_mod_cast (S.Φj P hSF hV j).sum_period_reps (S.ζj_spec P hSF hV hζ j)


/-- **The place certificate passes `check`.** -/
theorem PcE_check (hnd : (P.pts.map Prod.fst).Nodup) (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0)
    (tx : ℕ := 0) : (S.PcE P hSF hV hζ j₀ tx).check P.Fc P.n = true := by
  have hn := S.natDegree_F_eq P ψ hSF hV
  refine assemble_check P.Fc P.n ?_ ?_ ?_
  · intro L hL
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL
    rw [← hn]
    exact (S.Φj P hSF hV j).locPlaces_OK (S.ζj_spec P hSF hV hζ j) (S.Φj_a P hSF hV j)
      (txj P j + tx) (Function.invFun ψ) (ζj P hζ j) _ ψ.injective rfl (S.hpre_j P hSF hV hζ j tx)
  · have : (S.Ls P hSF hV hζ j₀ tx).map (·.α) = P.pts.map Prod.fst := by
      apply List.ext_getElem (by simp [Ls])
      intro i h1 h2
      simp [Ls, lpj, SplitFibre.locPlaces]
    rw [this]; exact hnd
  · rw [S.Ls_length P hSF hV hζ j₀ tx]
    have h := S.sum_Γj P hSF hV hζ j₀ hnd hinf0 tx
    have e : ∑ j ∈ Finset.range P.pts.length, ((S.Ls P hSF hV hζ j₀ tx).getD j locDef).Γ.sum =
        ∑ j : Fin P.pts.length, (S.lpj P hSF hV hζ j (S.Γj P hSF hV hζ j₀ j) tx).Γ.sum := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [S.Ls_getD P hSF hV hζ j₀ j j.2 tx]
    rw [e]
    exact_mod_cast h

/-- The shifts. -/
noncomputable def eLE : List ℤ := List.ofFn fun j ↦ (S.eLj P hSF hV hζ j₀ j : ℤ)

lemma Rj_rep (j : Fin P.pts.length) (k : Fin S.F.natDegree) :
    S.Rj P hSF hV hζ j k = S.Rj P hSF hV hζ j ((S.Φj P hSF hV j).rep (S.ζj_spec P hSF hV hζ j) k) := by
  apply ψ.injective
  rw [S.psi_Rj P hSF hV hζ, S.psi_Rj P hSF hV hζ]
  exact (S.Φj P hSF hV j).resAlong_rep S P hSF (S.ζj_spec P hSF hV hζ j) (S.fE P ψ) k

lemma coord_Rj (j : Fin P.pts.length) (π : Fin S.F.natDegree) :
    coord j₀ (S.Rj P hSF hV hζ j π) =
      ((S.Φj P hSF hV j).sIdx (S.ζj_spec P hSF hV hζ j) π : ℚ) * S.crj P hSF hV hζ j₀ j π := by
  have hs : ((S.Φj P hSF hV j).sIdx (S.ζj_spec P hSF hV hζ j) π : F) ≠ 0 := by
    exact_mod_cast ((S.Φj P hSF hV j).sIdx_pos (S.ζj_spec P hSF hV hζ j) π).ne'
  rw [crj, ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hs]

variable (T : GlobalCert F)

/-- **The residue check passes.** -/
theorem PcE_torsRes (hnd : (P.pts.map Prod.fst).Nodup) (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0)
    (hT1 : T.Fc = P.Fc) (hT2 : T.n = P.n) (tx : ℕ := 0) :
    torsResCheckP P T (S.PcE P hSF hV hζ j₀ tx) (S.eLE P hSF hV hζ j₀) (S.sden P hSF hV hζ j₀) j₀ =
      true := by
  classical
  have hn := S.natDegree_F_eq P ψ hSF hV
  set D := S.PcE P hSF hV hζ j₀ tx with hD
  set Ls := S.Ls P hSF hV hζ j₀ tx
  have hLl : Ls.length = P.pts.length := S.Ls_length P hSF hV hζ j₀ tx
  have hfl : D.fib.length = P.pts.length := by simp [hD, PcE, assemble, Ls, CurveData.Ls]
  have hαs : D.αs = P.pts.map Prod.fst := by
    apply List.ext_getElem (by simp [hD, PcE, assemble, PlaceCert.αs, CurveData.Ls])
    intro i h1 h2
    simp [hD, PcE, assemble, PlaceCert.αs, CurveData.Ls, lpj, SplitFibre.locPlaces]
  have hinfl : P.inf.ys.length = P.n := by
    have := hV.certInf
    simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.2
  have hres0 : P.resInf (P.inf.ys.getD 0 []) = 0 :=
    hinf0 _ (by rw [List.getD_eq_getElem _ _ (by rw [hinfl]; exact hV.n_pos)]; exact List.getElem_mem _)
  simp only [torsResCheckP, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨hT1, hT2⟩, S.sden_pos P hSF hV hζ j₀⟩, hnd⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- the places
    intro j hj
    rw [hfl] at hj
    set jj : Fin P.pts.length := ⟨j, hj⟩
    have hjL : j < Ls.length := by rw [hLl]; exact hj
    have hLj := S.Ls_getD P hSF hV hζ j₀ j hj tx
    have hfα : D.fα j = (P.pts[j]).1 := by rw [hD, PcE, assemble_fα _ j hjL, hLj]; rfl
    have hfN : D.fN j = (P.pts[j]).2.N := by rw [hD, PcE, assemble_fN _ j hjL, hLj]; rfl
    have htp : D.tp.getD j 0 = (S.Φj P hSF hV jj).tpF + (txj P jj + tx) := by
      rw [hD, PcE, assemble_tp _ j hjL, hLj]; rfl
    have hprec := hV.prec _ (List.getElem_mem (l := P.pts) hj)
    refine ⟨⟨?_, ?_⟩, fun k hk ↦ ?_⟩
    · rw [hfα, hfN, htp]
      unfold txj
      have h1 : 0 < (P.pts[j]).2.N := (S.Φj P hSF hV jj).hN
      simp only [jj, Fin.getElem_fin] at h1 ⊢
      omega
    · rw [hfα, hfN]; exact hprec.2.2.2
    · -- the residue equation at the root `k`
      rw [hT2, ← hn] at hk
      set kk : Fin S.F.natDegree := ⟨k, hk⟩
      set L := S.lpj P hSF hV hζ jj (S.Γj P hSF hV hζ j₀ jj) tx with hL
      have hkL : k < L.rts.length := by
        simp only [hL, lpj, SplitFibre.locPlaces, List.length_map, List.length_finRange]; exact hk
      have hLj' : Ls.getD j locDef = L := hLj
      have hrs : D.rs j k = L.s k := by rw [hD, PcE, assemble_rs _ j hjL k (by rw [hLj']; exact hkL), hLj']
      have hrπ : D.rπ j k = offF (plBlocks Ls) j + L.idx k := by
        rw [hD, PcE, assemble_rπ _ j hjL k (by rw [hLj']; exact hkL), hLj']
      have hrζ : D.rζ j k = L.ζ k := by rw [hD, PcE, assemble_rζ _ j hjL k (by rw [hLj']; exact hkL), hLj']
      have hidx : L.idx k < (Ls.getD j locDef).pls.length := by
        rw [hLj', hL, lpj, SplitFibre.lp_idx _ _ _ _ _ _ _ k hk, SplitFibre.lp_pls_length]
        exact (S.Φj P hSF hV jj).idxOf_lt _ kk
      have hpy : D.py (D.rπ j k) = L.y (L.idx k) := by
        rw [hrπ, hD, PcE, assemble_py _ j hjL _ hidx, hLj']
      have hΓp : D.Γp.getD (D.rπ j k) 0 = L.Γ.getD (L.idx k) 0 := by
        rw [hrπ, hD, PcE, assemble_Γp _ (fun L hL ↦ ?_) j hjL _ hidx, hLj']
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL
        simp [lpj, SplitFibre.locPlaces]
      have hapx : D.apx j k = S.apxj P hSF hV hζ jj k tx := by
        rw [PlaceCert.apx, hrζ, hrs, hpy]; rfl
      have hfc : D.fc j = ⟨(S.Φj P hSF hV jj).N, [], (S.Φj P hSF hV jj).tpF + (txj P jj + tx)⟩ := by
        rw [PlaceCert.fc, hfN, htp]; rfl
      rw [hfα, hfc, hapx, hrs, hΓp, show P.resFin (P.pts[j]).1 ⟨(S.Φj P hSF hV jj).N, [],
        (S.Φj P hSF hV jj).tpF + (txj P jj + tx)⟩ (S.apxj P hSF hV hζ jj k tx) =
          S.Rj P hSF hV hζ jj kk from S.Rj_tx P hSF hV hζ jj kk tx,
        S.Rj_rep P hSF hV hζ jj kk, S.coord_Rj P hSF hV hζ j₀]
      -- the local accessors at the root
      have hs : L.s k = (S.Φj P hSF hV jj).sIdx (S.ζj_spec P hSF hV hζ jj)
          ((S.Φj P hSF hV jj).rep (S.ζj_spec P hSF hV hζ jj) kk) :=
        SplitFibre.lp_s _ _ _ _ _ _ _ k hk
      have hΓ : L.Γ.getD (L.idx k) 0 = S.Γj P hSF hV hζ j₀ jj
          ((S.Φj P hSF hV jj).rep (S.ζj_spec P hSF hV hζ jj) kk) := by
        rw [hL, lpj, SplitFibre.lp_idx _ _ _ _ _ _ _ k hk,
          SplitFibre.lp_Γ _ _ _ _ _ _ _ _ ((S.Φj P hSF hV jj).idxOf_lt _ kk)]
        exact congrArg _ ((S.Φj P hSF hV jj).getElem_idxOf _ kk)
      have heL : (S.eLE P hSF hV hζ j₀).getD j 0 = S.eLj P hSF hV hζ j₀ jj := by
        rw [eLE, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
      rw [hs, hΓ, heL, hfN]
      set π := (S.Φj P hSF hV jj).rep (S.ζj_spec P hSF hV hζ jj) kk
      have hN : ((P.pts[j]).2.N : ℚ) = (S.Φj P hSF hV jj).sIdx (S.ζj_spec P hSF hV hζ jj) π *
          (S.Φj P hSF hV jj).period (S.ζj_spec P hSF hV hζ jj) π := by
        exact_mod_cast ((S.Φj P hSF hV jj).sIdx_mul _ π).symm
      have hz := S.zj_eq P hSF hV hζ j₀ jj π
      have hΓe := S.Γj_eq P hSF hV hζ j₀ jj π
      have hΓq : (S.Γj P hSF hV hζ j₀ jj π : ℚ) = (S.zj P hSF hV hζ j₀ jj π : ℚ) +
          (S.eLj P hSF hV hζ j₀ jj : ℚ) * ((S.Φj P hSF hV jj).period (S.ζj_spec P hSF hV hζ jj) π : ℚ) := by
        exact_mod_cast hΓe
      push_cast
      rw [hN, hΓq, hz]
      ring
  · intro ac hac
    left; rw [hαs]; exact List.mem_map_of_mem hac
  · intro wt hwt
    rw [hinf0 wt hwt, hres0]
  · have hf : ∀ ac ∈ P.pts, fexpP P D (S.sden P hSF hV hζ j₀) j₀ ac = 0 := fun ac hac ↦ by
      rw [fexpP, if_pos (by rw [hαs]; exact List.mem_map_of_mem hac)]
    rw [List.map_congr_left hf, hres0, map_zero, mul_zero, zero_div, sub_zero]
    simp only [List.map_const', List.sum_replicate, smul_zero, Int.cast_zero, add_zero]
    rw [hfl, show D.cΓ = ∑ j, S.eLj P hSF hV hζ j₀ j from rfl, ← Fin.sum_univ_eq_sum_range]
    push_cast
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [eLE, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    rfl

end CurveData

end Cert

end Curves
