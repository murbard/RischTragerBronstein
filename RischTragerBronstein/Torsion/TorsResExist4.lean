import RischTragerBronstein.Torsion.TorsResExist3

/-!
# Residue data at places from a valid problem (3): the local data of all special fibres

For a valid problem whose special fibres carry primitive roots of unity of the ramification indices
(`hζ`), the local place data `lpj j Γf` of the special fibres, their computed residues `Rj j π`
(`ψ (Rj j π)` is the residue along the root `π`, `psi_Rj`), and **`sum_places_res`**: if the computed
residues at infinity vanish, `∑_j ∑_{π place} Rj j π / s_π = 0` (residue theorem).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

section Local

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : F, IsPrimitiveRoot (ψ ζF) ac.2.N)

/-- The fibre `j`. -/
noncomputable def Φj (j : Fin P.pts.length) :
    SplitFibre (C := C) (K := C) ((toB P.Fc).map (mapRingHom ψ)) S.F.natDegree :=
  S.fibreΦ P hSF hV P.pts[j] (List.getElem_mem _)

/-- The root of unity of the fibre `j`. -/
noncomputable def ζj (j : Fin P.pts.length) : F := Classical.choose (hζ P.pts[j] (List.getElem_mem _))

lemma ζj_spec (j : Fin P.pts.length) : IsPrimitiveRoot (ψ (ζj P hζ j)) (S.Φj P hSF hV j).N :=
  Classical.choose_spec (hζ P.pts[j] (List.getElem_mem _))

lemma Φj_a (j : Fin P.pts.length) : ψ (P.pts[j]).1 = (S.Φj P hSF hV j).a := rfl

/-- The slack of the test precision. -/
def txj (j : Fin P.pts.length) : ℕ := P.mufFin (P.pts[j]).1 (P.pts[j]).2.N

/-- The local place data of the fibre `j`. -/
noncomputable def lpj (j : Fin P.pts.length) (Γf : Fin S.F.natDegree → ℕ) (tx : ℕ := 0) :
    LocPlaces F :=
  (S.Φj P hSF hV j).locPlaces (S.ζj_spec P hSF hV hζ j) (S.Φj_a P hSF hV j) (txj P j + tx)
    (Function.invFun ψ) (ζj P hζ j) Γf

/-- The approximation of the root `k` of the fibre `j`. -/
noncomputable def apxj (j : Fin P.pts.length) (k : ℕ) (tx : ℕ := 0) : CPoly F :=
  conjC ((S.lpj P hSF hV hζ j 0 tx).ζ k) ((S.lpj P hSF hV hζ j 0 tx).s k)
    ((S.lpj P hSF hV hζ j 0 tx).y ((S.lpj P hSF hV hζ j 0 tx).idx k))

lemma apxj_eq (j : Fin P.pts.length) (Γf : Fin S.F.natDegree → ℕ) (k tx : ℕ) :
    conjC ((S.lpj P hSF hV hζ j Γf tx).ζ k) ((S.lpj P hSF hV hζ j Γf tx).s k)
      ((S.lpj P hSF hV hζ j Γf tx).y ((S.lpj P hSF hV hζ j Γf tx).idx k)) =
      S.apxj P hSF hV hζ j k tx := rfl

/-- The computed residue along the root `k` of the fibre `j`. -/
noncomputable def Rj (j : Fin P.pts.length) (k : ℕ) : F :=
  P.resFin (P.pts[j]).1 ⟨(S.Φj P hSF hV j).N, [], (S.Φj P hSF hV j).tpF + txj P j⟩
    (S.apxj P hSF hV hζ j k)

lemma hpre_j (j : Fin P.pts.length) (tx : ℕ := 0) : ∀ π : Fin S.F.natDegree,
    ∀ i < (S.Φj P hSF hV j).bnd (S.ζj_spec P hSF hV hζ j) (S.Φj_a P hSF hV j) (txj P j + tx),
      ψ (Function.invFun ψ (PowerSeries.coeff i ((S.Φj P hSF hV j).placeSer
        (S.ζj_spec P hSF hV hζ j) π))) =
      PowerSeries.coeff i ((S.Φj P hSF hV j).placeSer (S.ζj_spec P hSF hV hζ j) π) := by
  intro π i _
  apply Function.invFun_eq
  simp only [SplitFibre.placeSer, PowerSeries.coeff_mk]
  exact S.fibreΦ_coeff P hSF hV _ _ π _

/-- **The computed residues are the residues along the roots.** -/
lemma psi_Rj (j : Fin P.pts.length) (k : Fin S.F.natDegree) :
    ψ (S.Rj P hSF hV hζ j k) = S.resAlong (S.Φj P hSF hV j).N (S.Φj P hSF hV j).hN
      (S.Φj P hSF hV j).a ((S.Φj P hSF hV j).y k) ((S.Φj P hSF hV j).root_S S P hSF k) (S.fE P ψ) := by
  have hprec := hV.prec _ (List.getElem_mem (l := P.pts) j.2)
  exact (S.Φj P hSF hV j).resFin_locPlaces S P hSF (S.ζj_spec P hSF hV hζ j) hV
    (S.Φj_a P hSF hV j) (txj P j) (Function.invFun ψ) 0 rfl
    (S.hpre_j P hSF hV hζ j) (by
      have h1 : 0 < (S.Φj P hSF hV j).N := (S.Φj P hSF hV j).hN
      change 0 < (P.pts[j]).2.N at h1
      change P.mufFin (P.pts[j]).1 (P.pts[j]).2.N < _ + P.mufFin (P.pts[j]).1 (P.pts[j]).2.N +
        (P.pts[j]).2.N
      omega) hprec.2.2.2 k

/-- The residues computed with more precision are the same. -/
lemma psi_RjT (j : Fin P.pts.length) (k : Fin S.F.natDegree) (tx : ℕ) :
    ψ (P.resFin (P.pts[j]).1 ⟨(S.Φj P hSF hV j).N, [], (S.Φj P hSF hV j).tpF + (txj P j + tx)⟩
      (S.apxj P hSF hV hζ j k tx)) = S.resAlong (S.Φj P hSF hV j).N (S.Φj P hSF hV j).hN
      (S.Φj P hSF hV j).a ((S.Φj P hSF hV j).y k) ((S.Φj P hSF hV j).root_S S P hSF k) (S.fE P ψ) := by
  have hprec := hV.prec _ (List.getElem_mem (l := P.pts) j.2)
  exact (S.Φj P hSF hV j).resFin_locPlaces S P hSF (S.ζj_spec P hSF hV hζ j) hV
    (S.Φj_a P hSF hV j) (txj P j + tx) (Function.invFun ψ) 0 rfl
    (S.hpre_j P hSF hV hζ j tx) (by
      have h1 : 0 < (S.Φj P hSF hV j).N := (S.Φj P hSF hV j).hN
      change 0 < (P.pts[j]).2.N at h1
      change P.mufFin (P.pts[j]).1 (P.pts[j]).2.N < _ + (P.mufFin (P.pts[j]).1 (P.pts[j]).2.N + tx) +
        (P.pts[j]).2.N
      omega) hprec.2.2.2 k

lemma Rj_tx (j : Fin P.pts.length) (k : Fin S.F.natDegree) (tx : ℕ) :
    P.resFin (P.pts[j]).1 ⟨(S.Φj P hSF hV j).N, [], (S.Φj P hSF hV j).tpF + (txj P j + tx)⟩
      (S.apxj P hSF hV hζ j k tx) = S.Rj P hSF hV hζ j k :=
  ψ.injective ((S.psi_RjT P hSF hV hζ j k tx).trans (S.psi_Rj P hSF hV hζ j k).symm)

lemma fE_eq_fnWQ : S.fE P ψ = S.fnWQ (((toB P.A).map (mapRingHom ψ)) %ₘ S.F) ((toPoly P.D).map ψ) := by
  apply Subtype.ext
  have e1 : S.evXY (((toB P.A).map (mapRingHom ψ)) %ₘ S.F) = S.evXY ((toB P.A).map (mapRingHom ψ)) := by
    conv_rhs => rw [← modByMonic_add_div ((toB P.A).map (mapRingHom ψ)) S.F]
    rw [S.evXY_add, S.evXY_mul, S.evXY_F, zero_mul, add_zero]
  rw [coe_fnWQ, e1]
  exact div_eq_mul_inv _ _

include hζ in
/-- **The residue theorem over the places of the special fibres.** -/
theorem sum_places_res (hnd : (P.pts.map Prod.fst).Nodup) (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0) :
    ∑ j : Fin P.pts.length, ∑ π ∈ Finset.univ.filter
      (fun π ↦ (S.Φj P hSF hV j).rep (S.ζj_spec P hSF hV hζ j) π = π),
      S.Rj P hSF hV hζ j π / ((S.Φj P hSF hV j).sIdx (S.ζj_spec P hSF hV hζ j) π : F) = 0 := by
  classical
  apply ψ.injective
  rw [map_zero, map_sum]
  simp only [map_sum, map_div₀, map_natCast, S.psi_Rj P hSF hV hζ]
  -- the residue theorem
  set W := ((toB P.A).map (mapRingHom ψ)) %ₘ S.F
  have hW : W.natDegree < S.F.natDegree :=
    natDegree_modByMonic_lt _ S.monic (fun h ↦ S.natDegree_F_ne_zero (by rw [h, natDegree_one]))
  set Q := (toPoly P.D).map ψ
  have hQ : Q ≠ 0 := (Polynomial.map_ne_zero_iff ψ.injective).mpr hV.D0
  have hs : Multiset.card Q.roots = Q.natDegree :=
    (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits Q))
  set a : Fin P.pts.length → C := fun j ↦ ψ (P.pts[j]).1
  have ha : Function.Injective a := by
    intro j j' h
    have h1 : (P.pts.map Prod.fst)[j]'(by simp) = (P.pts.map Prod.fst)[j']'(by simp) := by
      simpa using ψ.injective h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h1)
  have hR : ∀ b, Q.IsRoot b → ∃ j, a j = b := by
    intro b hb
    obtain ⟨a', ha', hb'⟩ := coverCheck_spec _ _ hV.cover ψ b (by
      rw [CPoly.toPoly_mul, Polynomial.map_mul, eval_mul]
      rw [IsRoot.def] at hb; rw [hb, zero_mul])
    obtain ⟨ac, hac, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hac
    exact ⟨⟨j, hj⟩, hb'.symm⟩
  obtain ⟨w, happ, hroot, hinj⟩ := S.inf_roots_F_approx P hSF hV
  have hn := S.natDegree_F_eq P ψ hSF hV
  have key := S.res_theorem_fibres W hW Q hQ hs a ha hR (fun j ↦ (S.Φj P hSF hV j).N)
    (fun j ↦ (S.Φj P hSF hV j).hN) (fun j k ↦ ofPowerSeries ℤ C ((S.Φj P hSF hV j).y k))
    (fun j ↦ (congrArg (fun G : C[X][X] ↦ G.map (branchSub (K := C) (S.Φj P hSF hV j).N (a j))) hSF).trans
      (S.Φj P hSF hV j).split)
    (fun j k ↦ (S.Φj P hSF hV j).root_S S P hSF k) P.inf.N hV.infN _
    (S.inf_split_approx P hSF hV w hroot hinj) (fun k ↦ hroot _)
  rw [← S.fE_eq_fnWQ P] at key
  have hinf : ∀ k : Fin S.F.natDegree, LaurentSeries.res (S.embG (infSub P.inf.N)
      (infSub_injective _ hV.infN) _ (hroot (Fin.cast hn k)) (S.fE P ψ) *
        LaurentSeries.derivation (single (-(P.inf.N : ℤ)) (1 : C))) = 0 := fun k ↦
    S.res_inf_root P hSF hV w happ hroot hinf0 _
  rw [Finset.sum_congr rfl fun k _ ↦ hinf k, Finset.sum_const_zero, mul_zero, add_zero] at key
  rw [← key]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have := (S.Φj P hSF hV j).sum_resAlong S P hSF (S.ζj_spec P hSF hV hζ j) (S.fE P ψ)
  rw [← this]
  rfl

end CurveData

end Local

end Curves
