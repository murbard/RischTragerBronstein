import RischTragerBronstein.Torsion.TorsOrdExist1

/-!
# Torsion data from principal divisors (2): the torsion witness

For the place certificate `PcE` of a valid problem (vanishing computed residues above infinity) and
`γ ≠ 0` whose divisor is exactly `M (Γ − cΓ ∞ₓ)` (orders `M s_k Γ_π` along the roots of the special
fibres, `0` elsewhere, `−N M cΓ` above infinity), **`torsOrdStd_of_exact`**: the function
`w = γ ∏_j (x − a_j)^{−M eL_j}` satisfies the torsion relation `TorsOrdStd` with multiplier
`M · s` (`s` the common denominator) for any `Λ` extending `coord j₀`.
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries

section Tors

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : F, IsPrimitiveRoot (ψ ζF) ac.2.N) (j₀ : Fin (dim F))

/-- The correction factor `∏_j (x − a_j)^{−M eL_j}`. -/
noncomputable def Uq (M : ℕ) : C⟮S.x⟯⟮S.y⟯ :=
  ∏ j : Fin P.pts.length, (S.qE ψ (xSubC (P.pts[j]).1)) ^ (-((M * S.eLj P hSF hV hζ j₀ j : ℕ) : ℤ))

lemma qE_ne_zero' (a : F) : S.qE ψ (xSubC a) ≠ 0 := fun h ↦
  S.aeval_x_ne_zero _ ((Polynomial.map_ne_zero_iff ψ.injective).mpr
    (by rw [toPoly_xSubC]; exact X_sub_C_ne_zero _)) (congrArg Subtype.val h)

omit [CharZero F] [EllQuad.QCoords F] [IsAlgClosed C] [CharZero L] in
/-- The order of a product of integer powers along an embedding. -/
lemma order_prod_zpow' {K : Type*} [Field K] (φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K) {ι : Type*}
    (s : Finset ι) (u : ι → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i ∈ s, u i ≠ 0) (e : ι → ℤ) :
    (φ (∏ i ∈ s, u i ^ e i)).order = ∑ i ∈ s, e i * (φ (u i)).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, map_mul, map_zpow₀]
    have hu0 : φ (u j) ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr (hu j (Finset.mem_insert_self _ _))
    have hp0 : φ (∏ i ∈ s, u i ^ e i) ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr fun i hi ↦ by
        rw [map_zpow₀]; exact zpow_ne_zero _ ((map_ne_zero_iff φ φ.injective).mpr
          (hu i (Finset.mem_insert_of_mem hi)))
    rw [HahnSeries.order_mul (zpow_ne_zero _ hu0) hp0, order_zpow' _ hu0,
      ih fun i hi ↦ hu i (Finset.mem_insert_of_mem hi)]

lemma Uq_ne_zero (M : ℕ) : S.Uq P hSF hV hζ j₀ M ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (S.qE_ne_zero' _)

open Classical in
lemma order_Uq_fin (M : ℕ) (N : ℕ) (hN : 0 < N) (b : C) (Y : LaurentSeries C)
    (hY : (S.F.map (branchSub (K := C) N b)).eval Y = 0) :
    (S.embG (branchSub N b) (branchSub_injective N hN b) Y hY (S.Uq P hSF hV hζ j₀ M)).order =
      ∑ j : Fin P.pts.length, -((M * S.eLj P hSF hV hζ j₀ j : ℕ) : ℤ) *
        (if b = ψ (P.pts[j]).1 then (N : ℤ) else 0) := by
  rw [Uq, S.order_prod_zpow' _ _ _ (fun j _ ↦ S.qE_ne_zero' _)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [S.order_qE_xSubC_fin ψ _ N hN b]
  rfl

lemma order_Uq_inf (M : ℕ) (N : ℕ) (hN : 0 < N) (Y : LaurentSeries C)
    (hY : (S.F.map (infSub (K := C) N)).eval Y = 0) :
    (S.embG (infSub N) (infSub_injective N hN) Y hY (S.Uq P hSF hV hζ j₀ M)).order =
      N * M * ∑ j : Fin P.pts.length, (S.eLj P hSF hV hζ j₀ j : ℤ) := by
  rw [Uq, S.order_prod_zpow' _ _ _ (fun j _ ↦ S.qE_ne_zero' _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [S.order_qE_xSubC_inf ψ _ N hN]
  push_cast; ring

/-- The branch system of the fibre `j`. -/
noncomputable def lfj (j : Fin P.pts.length) : List (LaurentSeries C) :=
  List.ofFn fun k ↦ ofPowerSeries ℤ C ((S.Φj P hSF hV j).y k)

lemma lfj_split (j : Fin P.pts.length) :
    S.F.map (branchSub (K := C) (S.Φj P hSF hV j).N (S.Φj P hSF hV j).a) =
      ((S.lfj P hSF hV j).map fun r ↦ X - Polynomial.C r).prod :=
  S.split_ofFn _ _ ((congrArg (fun G : C[X][X] ↦ G.map (branchSub (K := C) (S.Φj P hSF hV j).N
    (S.Φj P hSF hV j).a)) hSF).trans (S.Φj P hSF hV j).split)

/-- **The torsion witness from an exact principal divisor.** -/
theorem torsOrdStd_of_exact (hnd : (P.pts.map Prod.fst).Nodup)
    (hinf0 : ∀ wt ∈ P.inf.ys, P.resInf wt = 0) (Λ : C →ₗ[ℚ] ℚ)
    (hΛ : ∀ r : F, Λ (ψ r) = coord j₀ r) (M : ℕ) (γ : C⟮S.x⟯⟮S.y⟯) (hγ : γ ≠ 0)
    (h1 : ∀ (j : Fin P.pts.length) (k : Fin S.F.natDegree),
      (S.embG (branchSub (S.Φj P hSF hV j).N (S.Φj P hSF hV j).a)
        (branchSub_injective _ (S.Φj P hSF hV j).hN _) _
          ((S.Φj P hSF hV j).root_S S P hSF k) γ).order =
        M * ((S.Φj P hSF hV j).sIdx (S.ζj_spec P hSF hV hζ j)
          ((S.Φj P hSF hV j).rep (S.ζj_spec P hSF hV hζ j) k) *
            S.Γj P hSF hV hζ j₀ j ((S.Φj P hSF hV j).rep (S.ζj_spec P hSF hV hζ j) k) : ℕ))
    (h2 : ∀ b : C, b ∉ Set.range (fun j : Fin P.pts.length ↦ ψ (P.pts[j]).1) → ∀ (N' : ℕ)
      (hN' : 0 < N') (l : List (LaurentSeries C))
      (hl : S.F.map (branchSub (K := C) N' b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries C) (hr : r ∈ l),
      (S.embG (branchSub N' b) (branchSub_injective N' hN' b) r (S.root_of_mem hl hr) γ).order = 0)
    (h3 : ∀ (N' : ℕ) (hN' : 0 < N') (l : List (LaurentSeries C))
      (hl : S.F.map (infSub (K := C) N') = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries C) (hr : r ∈ l),
      (S.embG (infSub N') (infSub_injective N' hN') r (S.root_of_mem hl hr) γ).order =
        -((N' * (M * ∑ j, S.eLj P hSF hV hζ j₀ j) : ℕ) : ℤ)) :
    S.TorsOrdStd (K := C) P ψ (M * S.sden P hSF hV hζ j₀) (γ * S.Uq P hSF hV hζ j₀ M) Λ := by
  classical
  have hn := S.natDegree_F_eq P ψ hSF hV
  set m := M * S.sden P hSF hV hζ j₀
  set U := S.Uq P hSF hV hζ j₀ M
  have hU0 := S.Uq_ne_zero P hSF hV hζ j₀ M
  have hγU : ∀ (g : C[X] →+* LaurentSeries C) (hg : Function.Injective g) (Y : LaurentSeries C)
      (hY : (S.F.map g).eval Y = 0),
      (S.embG g hg Y hY (γ * U)).order = (S.embG g hg Y hY γ).order + (S.embG g hg Y hY U).order :=
    fun g hg Y hY ↦ by
      rw [map_mul, HahnSeries.order_mul ((map_ne_zero_iff _ (RingHom.injective _)).mpr hγ)
        ((map_ne_zero_iff _ (RingHom.injective _)).mpr hU0)]
  have hainj : ∀ j j' : Fin P.pts.length, ψ (P.pts[j]).1 = ψ (P.pts[j']).1 → j = j' := by
    intro j j' h
    have h1 : (P.pts.map Prod.fst)[j]'(by simp) = (P.pts.map Prod.fst)[j']'(by simp) := by
      simpa using ψ.injective h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h1)
  refine ⟨fun a N hN r hr ↦ ?_, fun N hN r hr ↦ ?_⟩
  · by_cases ha : ∃ j : Fin P.pts.length, a = ψ (P.pts[j]).1
    · obtain ⟨j, rfl⟩ := ha
      set Φ := S.Φj P hSF hV j
      have hζj := S.ζj_spec P hSF hV hζ j
      have hgood : ∀ r' (hr' : r' ∈ S.lfj P hSF hV j), S.GoodFin (S.fE P ψ) (γ * U) m Λ Φ.N Φ.hN Φ.a
          r' (S.root_of_mem (S.lfj_split P hSF hV j) hr') := by
        intro r' hr'
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr'
        unfold GoodFin
        rw [hγU]
        have ho1 : (S.embG (branchSub Φ.N Φ.a) (branchSub_injective _ Φ.hN _) _
            (S.root_of_mem (S.lfj_split P hSF hV j) hr') γ).order =
            M * (Φ.sIdx hζj (Φ.rep hζj k) * S.Γj P hSF hV hζ j₀ j (Φ.rep hζj k) : ℕ) := h1 j k
        have ho2 := S.order_Uq_fin P hSF hV hζ j₀ M Φ.N Φ.hN Φ.a _
          (S.root_of_mem (S.lfj_split P hSF hV j) hr')
        rw [Finset.sum_eq_single j (fun j' _ hj' ↦ by
            rw [if_neg (show ¬ (Φ.a = ψ (P.pts[j']).1) from fun h ↦ hj' (hainj _ _ h).symm),
              mul_zero])
          (by simp), if_pos (show Φ.a = ψ (P.pts[j]).1 from rfl)] at ho2
        have hres : LaurentSeries.res (S.embG (branchSub Φ.N Φ.a) (branchSub_injective _ Φ.hN _) _
            (S.root_of_mem (S.lfj_split P hSF hV j) hr') (S.fE P ψ) *
              LaurentSeries.derivation (HahnSeries.C Φ.a + single (Φ.N : ℤ) (1 : C))) =
            ψ (S.Rj P hSF hV hζ j k) := by
          rw [S.psi_Rj P hSF hV hζ j k]; rfl
        rw [ho1, ho2, hres, hΛ, S.Rj_rep P hSF hV hζ j k, S.coord_Rj P hSF hV hζ j₀]
        set π := Φ.rep hζj k
        have hΓ := S.Γj_eq P hSF hV hζ j₀ j π
        have hz := S.zj_eq P hSF hV hζ j₀ j π
        have hN : (Φ.N : ℚ) = Φ.sIdx hζj π * Φ.period hζj π := by
          exact_mod_cast (Φ.sIdx_mul hζj π).symm
        have hΓq : (S.Γj P hSF hV hζ j₀ j π : ℚ) = (S.zj P hSF hV hζ j₀ j π : ℚ) +
            (S.eLj P hSF hV hζ j₀ j : ℚ) * (Φ.period hζj π : ℚ) := by exact_mod_cast hΓ
        push_cast
        rw [hN, hΓq, hz]
        simp only [m]; push_cast; ring
      exact S.good_transfer_fin _ _ m Λ Φ.a Φ.N Φ.hN _ (S.lfj_split P hSF hV j) hgood N hN r hr
    · -- a non-special point
      have ha' : a ∉ Set.range (fun j : Fin P.pts.length ↦ ψ (P.pts[j]).1) := fun ⟨j, hj⟩ ↦
        ha ⟨j, hj.symm⟩
      obtain ⟨Nb, hNb, lb, -, hlb⟩ := S.hasBranches (K := C) a
      have hNb' := Nat.pos_of_ne_zero hNb
      have hlb' : S.F.map (branchSub Nb a) =
          ((lb.map (ofPowerSeries ℤ C)).map fun r ↦ X - Polynomial.C r).prod := by
        rw [hlb, List.map_map]; rfl
      have hDa : (((toPoly P.D).map ψ).map (algebraMap C C)).eval a ≠ 0 := by
        intro h0
        obtain ⟨a', ha'', hb'⟩ := coverCheck_spec _ _ hV.cover ψ a (by
          rw [CPoly.toPoly_mul, Polynomial.map_mul, eval_mul]
          simp only [Algebra.algebraMap_self, Polynomial.map_id] at h0
          rw [h0, zero_mul])
        obtain ⟨ac, hac, rfl⟩ := List.mem_map.mp ha''
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hac
        exact ha ⟨⟨j, hj⟩, hb'⟩
      have hgood : ∀ r' (hr' : r' ∈ lb.map (ofPowerSeries ℤ C)),
          S.GoodFin (S.fE P ψ) (γ * U) m Λ Nb hNb' a r' (S.root_of_mem hlb' hr') := by
        intro r' hr'
        unfold GoodFin
        rw [hγU, h2 a ha' Nb hNb' _ hlb' r' hr', S.order_Uq_fin P hSF hV hζ j₀ M Nb hNb' a,
          Finset.sum_eq_zero fun j _ ↦ by rw [if_neg (fun h ↦ ha ⟨j, h⟩), mul_zero],
          S.res_fE_regular (K := C) P ψ hV.D0 a hDa Nb hNb' r' _, map_zero, mul_zero]
        simp
      exact S.good_transfer_fin _ _ m Λ a Nb hNb' _ hlb' hgood N hN r hr
  · -- infinity
    obtain ⟨w, happ, hroot, hinj⟩ := S.inf_roots_F_approx P hSF hV
    have hsplit := S.inf_split_approx P hSF hV w hroot hinj
    have hli := S.split_ofFn _ _ hsplit
    have hNi := hV.infN
    have hgood : ∀ r' (hr' : r' ∈ List.ofFn fun k : Fin S.F.natDegree ↦
        single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : C) *
          ofPowerSeries ℤ C (PowerSeries.map ψ (w (Fin.cast hn k)))),
        S.GoodInf (S.fE P ψ) (γ * U) m Λ P.inf.N hNi r' (S.root_of_mem hli hr') := by
      intro r' hr'
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr'
      unfold GoodInf
      rw [hγU, h3 P.inf.N hNi _ hli _ hr', S.order_Uq_inf P hSF hV hζ j₀ M P.inf.N hNi]
      have hr0 := S.res_inf_root P hSF hV w happ hroot hinf0 (Fin.cast hn k)
      have e : LaurentSeries.res (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hNi) _
          (S.root_of_mem hli hr') (S.fE P ψ) * LaurentSeries.derivation (single (-(P.inf.N : ℤ)) (1 : C))) = 0 :=
        hr0
      rw [e, map_zero, mul_zero]
      push_cast; ring
    exact S.good_transfer_inf _ _ m Λ P.inf.N hNi _ hli hgood N hN r hr

end CurveData

end Tors

end Curves
