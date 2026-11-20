import RischTragerBronstein.Torsion.LogWitFacts
import RischTragerBronstein.Torsion.LogWitDescent
import RischTragerBronstein.Curves.HenselQ
import RischTragerBronstein.Curves.ProcRFSound6
import RischTragerBronstein.Torsion.LogWitExist
import RischTragerBronstein.Algebraic.NFExists

/-!
# Logarithmic witnesses from torsion data

For a curve `S` over a field `C` of characteristic `0` (branches with coefficients in an
algebraically closed `K ⊇ C`), a valid problem `P` over `F` (`ψ₀ : F →+* C`) and a non-zero
`w ∈ C(x, y)` whose order along every branch is `m · Λ(res f dX)` (`TorsOrd`, the output of
`curve_abel`):

* `exists_W1`: `w = W₁(x, y)/Q(x)` with `Q` defined over `F` and vanishing only at certified points;
* `exists_WF`: linear descent of `W₁` to `W` over `F`, keeping the orders along all certified
  branches (exact roots over `F`, `fin_roots_F` / `inf_roots_F`) as lower bounds;
* `exact_at`: these lower bounds are attained (`exact_divisor`), and the norm of `W` vanishes only at
  certified points;
* **`witOK_of_tors`**: `⟨m, W, Q⟩` passes `witOK` for every valid problem with the same curve,
  integrand, certified points and ramification indices, once the precisions are large.
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries

lemma map_thetaN {F R : Type*} [Field F] [Field R] (ψ₀ : F →+* R) (a : F) (N : ℕ) (P : F[X]) :
    PowerSeries.map ψ₀ (thetaN (RingHom.id F) a N P) = thetaN ψ₀ a N P := by
  simp only [thetaN, RingHom.comp_apply, thetaT_apply, Polynomial.map_id]
  rw [← Polynomial.polynomial_map_coe]

lemma root_of_prod {K : Type*} [Field K] {n : ℕ} {G : (LaurentSeries K)[X]}
    (r : Fin n → LaurentSeries K) (hG : G = ∏ k, (X - Polynomial.C (r k))) (z : LaurentSeries K)
    (hz : G.eval z = 0) : ∃ k, z = r k := by
  rw [hG, eval_prod] at hz
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hz
  exact ⟨k, by simpa [sub_eq_zero] using hk⟩

lemma mem_of_root {K : Type*} [Field K] {G : (LaurentSeries K)[X]} {l : List (LaurentSeries K)}
    (hG : G = (l.map fun r ↦ X - Polynomial.C r).prod) (z : LaurentSeries K) (hz : G.eval z = 0) :
    z ∈ l := by
  rw [hG, eval_list_prod, List.prod_eq_zero_iff] at hz
  obtain ⟨u, hu, hu0⟩ := List.mem_map.mp hz
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hu0
  exact hu0 ▸ hr

lemma lowerBd_order_self {K : Type*} [Field K] (z : LaurentSeries K) : LowerBd z z.order :=
  fun _ hk ↦ HahnSeries.coeff_eq_zero_of_lt_order hk

lemma rootMultiplicity_le_natDegree' {K : Type*} [Field K] (p : K[X]) (a : K) :
    p.rootMultiplicity a ≤ p.natDegree := by
  classical
  rw [← count_roots]; exact (Multiset.count_le_card _ _).trans (card_roots' p)

lemma branchSub_eq_subst' {C K : Type*} [Field C] [Field K] [Algebra C K] (m : ℕ) (e : K) :
    branchSub (C := C) m e = substHom (HahnSeries.C e + single (m : ℤ) 1) := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · rw [bs_C, substHom_apply, Polynomial.map_C, aeval_C, HahnSeries.algebraMap_apply']
    exact (ofPowerSeries_C _).symm
  · rw [substHom_apply, Polynomial.map_X, aeval_X, branchSub_apply, Polynomial.map_X, X_comp,
      Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, map_add,
      ofPowerSeries_C, ofPowerSeries_X_pow]

lemma infSub_eq_subst' {C K : Type*} [Field C] [Field K] [Algebra C K] (m : ℕ) :
    infSub (C := C) (K := K) m = substHom (single (-(m : ℤ)) 1) := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · rw [infSub, coe_eval₂RingHom, eval₂_C, substHom_apply, Polynomial.map_C, aeval_C,
      HahnSeries.algebraMap_apply']
    exact (ofPowerSeries_C _).symm
  · rw [substHom_apply, Polynomial.map_X, aeval_X, infSub, coe_eval₂RingHom, eval₂_X]

section Roots

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L)
variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- **Exact roots over `F` at a certified point, mapped to `K`, split `F`.** -/
theorem fin_roots_F (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) (ac : F × BranchCert F) (hac : ac ∈ P.pts) :
    ∃ y : Fin S.F.natDegree → PowerSeries F, Function.Injective y ∧
      S.F.map (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1))) =
        ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K
          (PowerSeries.map ((algebraMap C K).comp ψ₀) (y k)))) := by
  classical
  have hn := S.natDegree_F_eq P ψ₀ hSF hV
  obtain ⟨y, -, hinj, hsplit⟩ := certCheck_spec (C := F) (K := F) P.Fc P.n hV.mon hV.deg ac.1 ac.2
    (hV.certs ac hac) (RingHom.id F)
  set a := ac.1
  set N := ac.2.N
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  have hidF : (algebraMap F F).comp (RingHom.id F) = RingHom.id F := RingHom.ext fun _ ↦ rfl
  -- the roots over `F`
  have hrootF : ∀ k, ((toB P.Fc).map (thetaN (RingHom.id F) a N)).eval (y k) = 0 := by
    intro k
    have h1 : ((((toB P.Fc).map (mapRingHom (RingHom.id F))).map
        (branchSub (C := F) (K := F) N (algebraMap F F (RingHom.id F a))))).eval
        (ofPowerSeries ℤ F (y k)) = 0 := by
      rw [hsplit, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
    have hG : ((toB P.Fc).map (mapRingHom (RingHom.id F))).map
        (branchSub (C := F) (K := F) N (algebraMap F F (RingHom.id F a))) =
        ((toB P.Fc).map (thetaN (RingHom.id F) a N)).map (ofPowerSeries ℤ F) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      refine RingHom.ext fun Q ↦ ?_
      have := ofPS_thetaN (C := F) (K := F) (RingHom.id F) a N Q
      rw [hidF] at this
      simpa using this.symm
    rw [hG, eval_map, eval₂_at_apply] at h1
    exact HahnSeries.ofPowerSeries_injective (by rw [h1, map_zero])
  -- mapped to `K`
  have hrootC : ∀ k, (S.F.map (branchSub N (algebraMap C K (ψ₀ a)))).eval
      (ofPowerSeries ℤ K (PowerSeries.map ψ (y k))) = 0 := by
    intro k
    have h2 : PowerSeries.map ψ (((toB P.Fc).map (thetaN (RingHom.id F) a N)).eval (y k)) =
        ((toB P.Fc).map (thetaN ψ a N)).eval (PowerSeries.map ψ (y k)) := by
      rw [eval_map, hom_eval₂, eval_map]
      congr 1
      exact RingHom.ext fun Q ↦ map_thetaN ψ a N Q
    rw [hrootF k, map_zero] at h2
    have hGC : S.F.map (branchSub N (algebraMap C K (ψ₀ a))) =
        ((toB P.Fc).map (thetaN ψ a N)).map (ofPowerSeries ℤ K) := by
      rw [hSF, Polynomial.map_map, Polynomial.map_map]
      congr 1
      refine RingHom.ext fun Q ↦ ?_
      have := ofPS_thetaN (K := K) ψ₀ a N Q
      simpa using this.symm
    rw [hGC, eval_map, eval₂_at_apply, ← h2, map_zero]
  have hψi : Function.Injective ψ := (algebraMap C K).injective.comp ψ₀.injective
  set r : Fin S.F.natDegree → LaurentSeries K := fun k ↦
    ofPowerSeries ℤ K (PowerSeries.map ψ (y (Fin.cast hn k))) with hr
  have hinjr : Function.Injective r := by
    intro k l hkl
    have h1 := HahnSeries.ofPowerSeries_injective hkl
    have h2 : y (Fin.cast hn k) = y (Fin.cast hn l) := by
      ext t
      have := congrArg (PowerSeries.coeff t) h1
      rw [PowerSeries.coeff_map, PowerSeries.coeff_map] at this
      exact hψi this
    exact Fin.cast_injective hn (hinj h2)
  refine ⟨fun k ↦ y (Fin.cast hn k), fun k l h ↦ Fin.cast_injective hn (hinj h), ?_⟩
  exact eq_prod_of_distinct_roots _ (S.monic.map _) (by rw [S.monic.natDegree_map]) r hinjr
    fun k ↦ hrootC _

/-- **Exact roots over `F` above infinity, mapped to `K`, split `F`.** -/
theorem inf_roots_F (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) :
    ∃ w : Fin S.F.natDegree → PowerSeries F, Function.Injective w ∧
      S.F.map (infSub (K := K) P.inf.N) = ∏ k, (X - Polynomial.C
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) *
          ofPowerSeries ℤ K (PowerSeries.map ((algebraMap C K).comp ψ₀) (w k)))) := by
  classical
  have hn := S.natDegree_F_eq P ψ₀ hSF hV
  set N := P.inf.N
  have hN := hV.infN
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  obtain ⟨w, -, hinj, hsplit⟩ := certCheck_spec (C := F) (K := F) (invB P.Fc P.k (P.k * P.n)) P.n
    hV.mon' hV.deg' 0 P.inf hV.certInf (RingHom.id F)
  have hidF : (algebraMap F F).comp (RingHom.id F) = RingHom.id F := RingHom.ext fun _ ↦ rfl
  -- the roots over `F` (of the inverted polynomial at `0`)
  have hrootF : ∀ k, ((toB (invB P.Fc P.k (P.k * P.n))).map (thetaN (RingHom.id F) 0 N)).eval
      (w k) = 0 := by
    intro k
    have h1 : ((((toB (invB P.Fc P.k (P.k * P.n))).map (mapRingHom (RingHom.id F))).map
        (branchSub (C := F) (K := F) N (algebraMap F F (RingHom.id F 0))))).eval
        (ofPowerSeries ℤ F (w k)) = 0 := by
      rw [hsplit, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
    have hG : ((toB (invB P.Fc P.k (P.k * P.n))).map (mapRingHom (RingHom.id F))).map
        (branchSub (C := F) (K := F) N (algebraMap F F (RingHom.id F 0))) =
        ((toB (invB P.Fc P.k (P.k * P.n))).map (thetaN (RingHom.id F) 0 N)).map
          (ofPowerSeries ℤ F) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      refine RingHom.ext fun Q ↦ ?_
      have := ofPS_thetaN (C := F) (K := F) (RingHom.id F) 0 N Q
      rw [hidF] at this
      simpa using this.symm
    rw [hG, eval_map, eval₂_at_apply] at h1
    exact HahnSeries.ofPowerSeries_injective (by rw [h1, map_zero])
  have hrootC : ∀ k, (S.F.map (infSub N)).eval (single (-((P.k * N : ℕ) : ℤ)) (1 : K) *
      ofPowerSeries ℤ K (PowerSeries.map ψ (w k))) = 0 := by
    intro k
    have h2 : PowerSeries.map ψ
        (((toB (invB P.Fc P.k (P.k * P.n))).map (thetaN (RingHom.id F) 0 N)).eval (w k)) =
        ((toB (invB P.Fc P.k (P.k * P.n))).map (thetaN ψ 0 N)).eval (PowerSeries.map ψ (w k)) := by
      rw [eval_map, hom_eval₂, eval_map]
      congr 1
      exact RingHom.ext fun Q ↦ by simpa using map_thetaN ψ 0 N Q
    rw [hrootF k, map_zero] at h2
    have := eval_invB (K := K) ψ₀ N hN P.k (P.k * P.n) (PowerSeries.map ψ (w k)) P.Fc hV.okF
    rw [hSF, this, ← h2, map_zero, mul_zero]
  have hψi : Function.Injective ψ := (algebraMap C K).injective.comp ψ₀.injective
  set r : Fin S.F.natDegree → LaurentSeries K := fun k ↦
    single (-((P.k * N : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K (PowerSeries.map ψ (w (Fin.cast hn k)))
    with hr
  have hinjr : Function.Injective r := by
    intro k l hkl
    have h0 : single (-((P.k * N : ℕ) : ℤ)) (1 : K) ≠ 0 := single_ne_zero one_ne_zero
    have h1 := HahnSeries.ofPowerSeries_injective (mul_left_cancel₀ h0 hkl)
    have h2 : w (Fin.cast hn k) = w (Fin.cast hn l) := by
      ext t
      have := congrArg (PowerSeries.coeff t) h1
      rw [PowerSeries.coeff_map, PowerSeries.coeff_map] at this
      exact hψi this
    exact Fin.cast_injective hn (hinj h2)
  refine ⟨fun k ↦ w (Fin.cast hn k), fun k l h ↦ Fin.cast_injective hn (hinj h), ?_⟩
  exact eq_prod_of_distinct_roots _ (S.monic.map _) (by rw [S.monic.natDegree_map]) r hinjr
    fun k ↦ hrootC _

/-- The torsion hypothesis on `w` (the output of `curve_abel`), for branches over `K`. -/
def TorsOrd (P : CurveProb F) (ψ₀ : F →+* C) (m : ℕ) (w : C⟮S.x⟯⟮S.y⟯) (Λ : K →ₗ[ℚ] ℚ) : Prop :=
  ∀ (Xh : LaurentSeries K) (_ : LaurentSeries.derivation Xh ≠ 0)
    (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (_ : ∀ P', g P' = substHom Xh P') (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0),
    ((S.embG g hg Y hY w).order : ℚ) =
      m * Λ (LaurentSeries.res (S.embG g hg Y hY (S.fE P ψ₀) * LaurentSeries.derivation Xh))

/-- The torsion hypothesis along the standard branches only (`x = a + Tᴺ`, `x = T⁻ᴺ`). -/
def TorsOrdStd (P : CurveProb F) (ψ₀ : F →+* C) (m : ℕ) (w : C⟮S.x⟯⟮S.y⟯) (Λ : K →ₗ[ℚ] ℚ) : Prop :=
  (∀ (a : K) (N : ℕ) (hN : 0 < N) (r : LaurentSeries K) (hr : (S.F.map (branchSub N a)).eval r = 0),
    ((S.embG (branchSub N a) (branchSub_injective N hN a) r hr w).order : ℚ) =
      m * Λ (LaurentSeries.res (S.embG (branchSub N a) (branchSub_injective N hN a) r hr (S.fE P ψ₀) *
        LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K))))) ∧
  (∀ (N : ℕ) (hN : 0 < N) (r : LaurentSeries K) (hr : (S.F.map (infSub (K := K) N)).eval r = 0),
    ((S.embG (infSub N) (infSub_injective N hN) r hr w).order : ℚ) =
      m * Λ (LaurentSeries.res (S.embG (infSub N) (infSub_injective N hN) r hr (S.fE P ψ₀) *
        LaurentSeries.derivation (single (-(N : ℤ)) (1 : K)))))

omit [IsAlgClosed K] in
lemma TorsOrd.std {P : CurveProb F} {ψ₀ : F →+* C} {m : ℕ} {w : C⟮S.x⟯⟮S.y⟯} {Λ : K →ₗ[ℚ] ℚ}
    (h : S.TorsOrd P ψ₀ m w Λ) : S.TorsOrdStd P ψ₀ m w Λ := by
  refine ⟨fun a N hN r hr ↦ ?_, fun N hN r hr ↦ ?_⟩
  · exact h (HahnSeries.C a + single (N : ℤ) (1 : K))
      (by
        rw [SuperData.derivation_branchX N hN a]
        exact HahnSeries.single_ne_zero (by exact_mod_cast hN.ne'))
      (branchSub N a) (branchSub_injective N hN a) (fun Q ↦ by rw [branchSub_eq_subst']) r hr
  · exact h (single (-(N : ℤ)) (1 : K))
      (by
        rw [SuperData.derivation_infX]
        exact HahnSeries.single_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hN.ne')))
      (infSub N) (infSub_injective _ hN) (fun Q ↦ by rw [infSub_eq_subst']) r hr

open Classical in
/-- The points of the certificates, in the constants. -/
noncomputable def ptsC (P : CurveProb F) (ψ₀ : F →+* C) : Finset C :=
  ((P.pts.map Prod.fst).toFinset).image ψ₀

open Classical in
/-- The points of the certificates, in `K`. -/
noncomputable def ptsK (P : CurveProb F) (ψ₀ : F →+* C) : Finset K :=
  ((P.pts.map Prod.fst).toFinset).image ((algebraMap C K).comp ψ₀)

omit [CharZero C] [CharZero K] [IsAlgClosed K] in
lemma mem_ptsK_of_cover (P : CurveProb F) (ψ₀ : F →+* C) (hV : P.ValidFacts) (a : K)
    (h0 : ((toPoly (mul P.D (discRC P.Fc P.n P.k))).map ((algebraMap C K).comp ψ₀)).eval a = 0) :
    a ∈ ptsK P ψ₀ := by
  classical
  obtain ⟨b, hb, hab⟩ := coverCheck_spec _ _ hV.cover _ a h0
  exact Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb, hab.symm⟩

omit [CharZero C] [CharZero K] [IsAlgClosed K] in
lemma exists_of_mem_ptsK (P : CurveProb F) (ψ₀ : F →+* C) (a : K) (ha : a ∈ ptsK P ψ₀) :
    ∃ ac ∈ P.pts, algebraMap C K (ψ₀ ac.1) = a := by
  classical
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨ac, hac, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  exact ⟨ac, hac, rfl⟩

omit [CharZero C] [CharZero K] [IsAlgClosed K] in
lemma mem_ptsK (P : CurveProb F) (ψ₀ : F →+* C) (ac : F × BranchCert F) (hac : ac ∈ P.pts) :
    algebraMap C K (ψ₀ ac.1) ∈ ptsK P ψ₀ := by
  classical
  exact Finset.mem_image.mpr ⟨ac.1, List.mem_toFinset.mpr (List.mem_map.mpr ⟨ac, hac, rfl⟩), rfl⟩

lemma N_pos_of_mem (P : CurveProb F) (hV : P.ValidFacts) (ac : F × BranchCert F) (hac : ac ∈ P.pts) :
    0 < ac.2.N := by
  have hc := hV.certs ac hac
  simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1.1.1

/-- **Poles only above the certified points.** -/
theorem order_nonneg_off (P : CurveProb F) (ψ₀ : F →+* C) (hV : P.ValidFacts) (m : ℕ)
    (w : C⟮S.x⟯⟮S.y⟯) (Λ : K →ₗ[ℚ] ℚ) (hord : S.TorsOrdStd P ψ₀ m w Λ)
    (a : K) (ha : a ∉ ptsK P ψ₀) (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (branchSub N a)).eval r = 0) :
    (S.embG (branchSub N a) (branchSub_injective N hN a) r hr w).order = 0 := by
  classical
  have hDa : (((toPoly P.D).map ψ₀).map (algebraMap C K)).eval a ≠ 0 := by
    intro h0
    exact ha (mem_ptsK_of_cover P ψ₀ hV a (by
      rw [CPoly.toPoly_mul, Polynomial.map_mul, eval_mul, ← Polynomial.map_map, h0, zero_mul]))
  have hres := S.res_fE_regular (K := K) P ψ₀ hV.D0 a hDa N hN r hr
  have h1 := hord.1 a N hN r hr
  rw [hres, map_zero, mul_zero] at h1
  exact_mod_cast h1

/-- **`w = W₁(x, y) / Q(x)`** with `Q` defined over `F`, vanishing only at certified points, and
`deg_y W₁ < n`. -/
theorem exists_W1 (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) (m : ℕ) (w : C⟮S.x⟯⟮S.y⟯) (Λ : K →ₗ[ℚ] ℚ) (hord : S.TorsOrdStd P ψ₀ m w Λ) :
    ∃ (W₁ : C[X][X]) (QF : F[X]), QF ≠ 0 ∧
      (∀ c : K, (QF.map ((algebraMap C K).comp ψ₀)).IsRoot c → c ∈ ptsK P ψ₀) ∧
      W₁.natDegree < S.F.natDegree ∧ (w : L) * aeval S.x (QF.map ψ₀) = S.evXY W₁ := by
  classical
  set T := ptsC P ψ₀ with hT
  set A := (P.pts.map Prod.fst).toFinset with hA
  obtain ⟨W, Q₀, hQ₀, -, ⟨e, hQe⟩, hWQ⟩ := S.exists_repr_poles (K := K) w T
    (fun a ha N hN l hl r hr ↦ by
      have ha' : a ∉ ptsK P ψ₀ := by
        intro h
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
        exact ha (ψ₀ b) (Finset.mem_image_of_mem ψ₀ hb) rfl
      rw [S.order_nonneg_off P ψ₀ hV m w Λ hord a ha' N (Nat.pos_of_ne_zero hN) r
        (S.root_of_mem hl hr)])
  set QF : F[X] := toPoly (discRC P.Fc P.n P.k) * ∏ b ∈ A, (X - Polynomial.C b) ^ e (ψ₀ b) with hQF
  have hmap : QF.map ψ₀ = S.discR * Q₀ := by
    rw [hQF, Polynomial.map_mul, ← S.discR_eq hSF hV, hQe, Polynomial.map_prod, hT, ptsC,
      Finset.prod_image (fun x _ y _ h ↦ ψ₀.injective h)]
    congr 1
    exact Finset.prod_congr rfl fun b _ ↦ by simp
  have hne : QF.map ψ₀ ≠ 0 := by rw [hmap]; exact mul_ne_zero S.discR_ne_zero hQ₀
  refine ⟨W %ₘ S.F, QF, fun h ↦ hne (by rw [h, Polynomial.map_zero]), fun c hc ↦ ?_,
    natDegree_modByMonic_lt _ S.monic (fun h ↦ S.natDegree_F_ne_zero (by rw [h, natDegree_one])), ?_⟩
  · rw [hQF, Polynomial.map_mul, IsRoot, eval_mul] at hc
    rcases mul_eq_zero.mp hc with h | h
    · refine mem_ptsK_of_cover P ψ₀ hV c ?_
      rw [CPoly.toPoly_mul, Polynomial.map_mul, eval_mul, h, mul_zero]
    · rw [Polynomial.map_prod, eval_prod] at h
      obtain ⟨b, hb, hb0⟩ := Finset.prod_eq_zero_iff.mp h
      rw [Polynomial.map_pow, eval_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        eval_sub, eval_X, eval_C] at hb0
      have := sub_eq_zero.mp (pow_eq_zero_iff'.mp hb0).1
      exact Finset.mem_image.mpr ⟨b, hb, this.symm⟩
  · have e1 : S.evXY (W %ₘ S.F) = S.evXY W := by
      conv_rhs => rw [← modByMonic_add_div W S.F]
      rw [S.evXY_add, S.evXY_mul, S.evXY_F, zero_mul, add_zero]
    rw [e1, hmap, CurveData.discR]
    exact hWQ

/-- **Descent of `W₁` to `F`** keeping the orders along all certified branches as lower bounds. -/
theorem exists_WF (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) (W₁ : C[X][X]) (hW₁n : W₁.natDegree < S.F.natDegree) (hW₁ : W₁ ≠ 0) :
    ∃ W : F[X][X], W ≠ 0 ∧ W.natDegree < S.F.natDegree ∧
      (∀ ac ∈ P.pts, ∀ r, (S.F.map (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))).eval r = 0 →
        LowerBd (((W.map (mapRingHom ψ₀)).map (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))).eval r)
          ((W₁.map (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))).eval r).order) ∧
      (∀ r, (S.F.map (infSub (K := K) P.inf.N)).eval r = 0 →
        LowerBd (((W.map (mapRingHom ψ₀)).map (infSub P.inf.N)).eval r)
          ((W₁.map (infSub P.inf.N)).eval r).order) := by
  classical
  set n := S.F.natDegree with hn
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  have hfr := fun ac (hac : ac ∈ P.pts) ↦ S.fin_roots_F (K := K) P ψ₀ hSF hV ac hac
  choose yf hyfi hyf using hfr
  obtain ⟨wi, -, hwi⟩ := S.inf_roots_F (K := K) P ψ₀ hSF hV
  set E := (Finset.range n).sup fun i ↦ (W₁.coeff i).natDegree with hE
  have hEi : ∀ i, (W₁.coeff i).natDegree ≤ E := fun i ↦ by
    by_cases hi : i < n
    · exact Finset.le_sup (f := fun i ↦ (W₁.coeff i).natDegree) (Finset.mem_range.mpr hi)
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), natDegree_zero]; exact Nat.zero_le _
  set fb : List (F × ℕ × PowerSeries F × ℕ) := P.pts.attach.flatMap fun ac ↦
    (List.finRange n).map fun k ↦ (ac.1.1, ac.1.2.N, yf ac.1 ac.2 k,
      ((W₁.map (branchSub ac.1.2.N (ψ ac.1.1))).eval
        (ofPowerSeries ℤ K (PowerSeries.map ψ (yf ac.1 ac.2 k)))).order.toNat) with hfb
  set ib : List (ℕ × PowerSeries F × ℤ) := (List.finRange n).map fun k ↦ (P.inf.N, wi k,
    ((W₁.map (infSub P.inf.N)).eval (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) *
      ofPowerSeries ℤ K (PowerSeries.map ψ (wi k)))).order) with hib
  obtain ⟨W, hW0, hWn, -, hWf, hWi⟩ := descend_W (K := K) ψ₀ n E P.k (E + P.k * (n - 1)) le_rfl
    fb ib W₁ hW₁n hEi hW₁ (fun β hβ ↦ by
      obtain ⟨⟨ac, hac⟩, -, hk⟩ := List.mem_flatMap.mp hβ
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hk
      have h0 : 0 ≤ ((W₁.map (branchSub ac.2.N (ψ ac.1))).eval
          (ofPowerSeries ℤ K (PowerSeries.map ψ (yf ac hac k)))).order := by
        rw [branch_expansion ψ W₁ n E hW₁n hEi]; exact order_ofPS_nonneg _
      simp only
      rw [Int.toNat_of_nonneg h0]
      exact lowerBd_order_self _) (fun γ hγ ↦ by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hγ
      exact lowerBd_order_self _)
  refine ⟨W, hW0, hWn, fun ac hac r hr ↦ ?_, fun r hr ↦ ?_⟩
  · obtain ⟨k, rfl⟩ := root_of_prod _ (hyf ac hac) r hr
    have h := hWf _ (List.mem_flatMap.mpr ⟨⟨ac, hac⟩, List.mem_attach _ _,
      List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩⟩)
    exact h.mono (Int.self_le_toNat _)
  · obtain ⟨k, rfl⟩ := root_of_prod _ hwi r hr
    have h := hWi _ (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)
    simp only at h
    exact h

/-- **The norm of `W₁` vanishes only at certified points.** -/
theorem normW1_off (P : CurveProb F) (ψ₀ : F →+* C) (hV : P.ValidFacts) (m : ℕ)
    (w : C⟮S.x⟯⟮S.y⟯) (Λ : K →ₗ[ℚ] ℚ) (hord : S.TorsOrdStd P ψ₀ m w Λ)
    (hw : w ≠ 0) (W₁ : C[X][X]) (hW₁n : W₁.natDegree < S.F.natDegree) (QF : F[X])
    (hQr : ∀ c : K, (QF.map ((algebraMap C K).comp ψ₀)).IsRoot c → c ∈ ptsK P ψ₀)
    (hQ0 : QF.map ψ₀ ≠ 0)
    (hwQ : (w : L) * aeval S.x (QF.map ψ₀) = S.evXY W₁) (a : K) (ha : a ∉ ptsK P ψ₀) :
    ((S.normW W₁ S.F.natDegree).map (algebraMap C K)).rootMultiplicity a = 0 := by
  obtain ⟨N, hN, l, -, hl⟩ := split_at (K := K) S.F S.monic a
  have hN' := Nat.pos_of_ne_zero hN
  set l' := l.map (ofPowerSeries ℤ K) with hl'
  have hl'' : S.F.map (branchSub N a) = (l'.map fun r ↦ X - Polynomial.C r).prod := by
    rw [hl, hl', List.map_map]; rfl
  have hW₁ : S.evXY W₁ ≠ 0 := by
    rw [← hwQ]; exact mul_ne_zero (fun h ↦ hw (Subtype.ext h)) (S.aeval_x_ne_zero _ hQ0)
  have hs := S.sum_order_fin W₁ S.F.natDegree hW₁n.le hW₁ N hN' a l' hl''
  have hz : ∀ r ∈ l', ((W₁.map (branchSub N a)).eval r).order = 0 := by
    intro r hr
    have hroot := S.root_of_mem hl'' hr
    rw [S.eval_W_branch (branchSub N a) (branchSub_injective N hN' a) r hroot w W₁ _ hwQ]
    have he : S.embG _ (branchSub_injective N hN' a) r hroot w ≠ 0 :=
      (map_ne_zero_iff _ (S.embG _ _ r hroot).injective).mpr hw
    have hg : branchSub N a (QF.map ψ₀) ≠ 0 :=
      (map_ne_zero_iff _ (branchSub_injective N hN' a)).mpr hQ0
    rw [HahnSeries.order_mul he hg, S.order_nonneg_off P ψ₀ hV m w Λ hord a ha N hN' r hroot,
      order_branchSub N hN' a _ hQ0]
    have : ((QF.map ψ₀).map (algebraMap C K)).rootMultiplicity a = 0 := by
      rw [Polynomial.map_map]
      exact rootMultiplicity_eq_zero (fun h ↦ ha (hQr a h))
    rw [this]; simp
  have h0 : (l'.map fun r ↦ ((W₁.map (branchSub N a)).eval r).order).sum = 0 :=
    List.sum_eq_zero fun x hx ↦ by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx; exact hz r hr
  rw [h0] at hs
  exact_mod_cast (mul_eq_zero.mp hs.symm).resolve_left (by exact_mod_cast hN)

/-- **Exactness**: the descended `W` has the same orders as `W₁` along all certified branches, and
its norm vanishes only at certified points. -/
theorem exact_at (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) (m : ℕ) (w : C⟮S.x⟯⟮S.y⟯) (Λ : K →ₗ[ℚ] ℚ) (hord : S.TorsOrdStd P ψ₀ m w Λ)
    (hw : w ≠ 0) (W₁ : C[X][X]) (hW₁n : W₁.natDegree < S.F.natDegree) (QF : F[X])
    (hQr : ∀ c : K, (QF.map ((algebraMap C K).comp ψ₀)).IsRoot c → c ∈ ptsK P ψ₀)
    (hQ0 : QF.map ψ₀ ≠ 0)
    (hwQ : (w : L) * aeval S.x (QF.map ψ₀) = S.evXY W₁) (W : F[X][X])
    (hW0 : S.evXY (W.map (mapRingHom ψ₀)) ≠ 0)
    (hWf : ∀ ac ∈ P.pts, ∀ r, (S.F.map (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))).eval r = 0 →
        LowerBd (((W.map (mapRingHom ψ₀)).map (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))).eval r)
          ((W₁.map (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))).eval r).order)
    (hWi : ∀ r, (S.F.map (infSub (K := K) P.inf.N)).eval r = 0 →
        LowerBd (((W.map (mapRingHom ψ₀)).map (infSub P.inf.N)).eval r)
          ((W₁.map (infSub P.inf.N)).eval r).order)
    (ac0 : F × BranchCert F) (hN0 : 0 < ac0.2.N) :
    (ac0 ∈ P.pts → ∀ r, (S.F.map (branchSub ac0.2.N (algebraMap C K (ψ₀ ac0.1)))).eval r = 0 →
      (((W.map (mapRingHom ψ₀)).map (branchSub ac0.2.N (algebraMap C K (ψ₀ ac0.1)))).eval r).order =
        ((W₁.map (branchSub ac0.2.N (algebraMap C K (ψ₀ ac0.1)))).eval r).order) ∧
    (∀ r, (S.F.map (infSub (K := K) P.inf.N)).eval r = 0 →
      (((W.map (mapRingHom ψ₀)).map (infSub P.inf.N)).eval r).order =
        ((W₁.map (infSub P.inf.N)).eval r).order) ∧
    (∀ a ∉ ptsK P ψ₀,
      ((S.normW (W.map (mapRingHom ψ₀)) W.natDegree).map (algebraMap C K)).rootMultiplicity a =
        0) := by
  classical
  set T := ptsK (K := K) P ψ₀ with hT
  set n := S.F.natDegree with hn
  set Q := QF.map ψ₀ with hQ
  set Wc := W.map (mapRingHom ψ₀) with hWc
  have hQK : Q.map (algebraMap C K) = QF.map ((algebraMap C K).comp ψ₀) := by
    rw [hQ, Polynomial.map_map]
  have hQK0 : Q.map (algebraMap C K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hQ0
  have hW₁ : S.evXY W₁ ≠ 0 := by
    rw [← hwQ]; exact mul_ne_zero (fun h ↦ hw (Subtype.ext h)) (S.aeval_x_ne_zero _ hQ0)
  -- the selection of a certificate above each point
  have hTex := exists_of_mem_ptsK (K := K) P ψ₀
  set sel : K → F × BranchCert F := fun a ↦
    if a = algebraMap C K (ψ₀ ac0.1) ∧ ac0 ∈ P.pts then ac0 else
    if h : a ∈ T then Classical.choose (hTex a h) else ac0 with hsel
  have hsel0 : ac0 ∈ P.pts → sel (algebraMap C K (ψ₀ ac0.1)) = ac0 := fun h ↦ by simp [hsel, h]
  have hselm : ∀ a ∈ T, sel a ∈ P.pts := fun a ha ↦ by
    simp only [hsel]
    split_ifs with h1
    · exact h1.2
    · exact (Classical.choose_spec (hTex a ha)).1
  have hselN : ∀ a, 0 < (sel a).2.N := fun a ↦ by
    simp only [hsel]
    split_ifs with h1 h2
    · exact hN0
    · exact N_pos_of_mem P hV _ (Classical.choose_spec (hTex a h2)).1
    · exact hN0
  have hsela : ∀ a ∈ T, algebraMap C K (ψ₀ (sel a).1) = a := fun a ha ↦ by
    simp only [hsel]
    split_ifs with h1
    · exact h1.1.symm
    · exact (Classical.choose_spec (hTex a ha)).2
  have hL : ∀ a, ∃ l : List (LaurentSeries K), a ∈ T →
      S.F.map (branchSub (sel a).2.N a) = (l.map fun r ↦ X - Polynomial.C r).prod := by
    intro a
    by_cases ha : a ∈ T
    · obtain ⟨y, -, hy⟩ := S.fin_roots_F (K := K) P ψ₀ hSF hV (sel a) (hselm a ha)
      rw [hsela a ha] at hy
      refine ⟨List.ofFn fun k ↦ ofPowerSeries ℤ K (PowerSeries.map ((algebraMap C K).comp ψ₀) (y k)),
        fun _ ↦ ?_⟩
      rw [hy, List.map_ofFn, List.prod_ofFn]; rfl
    · exact ⟨[], fun h ↦ absurd h ha⟩
  choose lf hlf using hL
  obtain ⟨wi, -, hwi⟩ := S.inf_roots_F (K := K) P ψ₀ hSF hV
  set li : List (LaurentSeries K) := List.ofFn fun k ↦ single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) *
    ofPowerSeries ℤ K (PowerSeries.map ((algebraMap C K).comp ψ₀) (wi k)) with hli
  have hli' : S.F.map (infSub P.inf.N) = (li.map fun r ↦ X - Polynomial.C r).prod := by
    rw [hwi, hli, List.map_ofFn, List.prod_ofFn]; rfl
  have hNi := hV.infN
  -- `W₁` has no roots of its norm off `T`
  set PW := (S.normW W₁ n).map (algebraMap C K) with hPW
  have hPW0 : PW ≠ 0 := by
    rw [hPW, Ne, Polynomial.map_eq_zero_iff (algebraMap C K).injective]
    exact S.normW_ne_zero W₁ n hW₁n.le hW₁ _ (infSub_injective P.inf.N hNi) li hli'
  have hPWT : ∀ a, PW.IsRoot a → a ∈ T := fun a ha ↦ by
    by_contra haT
    exact ((rootMultiplicity_pos hPW0).mpr ha).ne'
      (S.normW1_off P ψ₀ hV m w Λ hord hw W₁ hW₁n QF hQr hQ0 hwQ a haT)
  have hQT : ∀ a, (Q.map (algebraMap C K)).IsRoot a → a ∈ T := fun a h ↦ hQr a (by rw [← hQK]; exact h)
  have hPsum := sum_rootMultiplicity_eq PW hPW0 T hPWT
  have hQsum := sum_rootMultiplicity_eq (Q.map (algebraMap C K)) hQK0 T hQT
  have hPdeg : PW.natDegree = (S.normW W₁ n).natDegree :=
    natDegree_map_eq_of_injective (algebraMap C K).injective _
  have hQdeg : (Q.map (algebraMap C K)).natDegree = Q.natDegree :=
    natDegree_map_eq_of_injective (algebraMap C K).injective _
  -- apply `exact_divisor`
  have hED := S.exact_divisor (K := K) Wc W.natDegree natDegree_map_le hW0 Q hQ0 T hQT
    (fun a ↦ (sel a).2.N) hselN lf hlf
    (fun a r ↦ ((W₁.map (branchSub (sel a).2.N a)).eval r).order -
      (sel a).2.N * ((Q.map (algebraMap C K)).rootMultiplicity a : ℤ))
    (fun a ha r hr ↦ by
      have hroot := S.root_of_mem (hlf a ha) hr
      have h1 := hWf (sel a) (hselm a ha) r (by rw [hsela a ha]; exact hroot)
      rw [hsela a ha] at h1
      have hne : ((Wc.map (branchSub (sel a).2.N a)).eval r) ≠ 0 :=
        S.branch_values_ne_zero Wc hW0 _ (branchSub_injective _ (hselN a) a)
          (lf a) (hlf a ha) _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
      have := le_order_of_lowerBd _ hne _ h1
      omega)
    P.inf.N hNi li hli'
    (fun r ↦ ((W₁.map (infSub P.inf.N)).eval r).order + P.inf.N * (Q.natDegree : ℤ))
    (fun r hr ↦ by
      have h1 := hWi r (S.root_of_mem hli' hr)
      have hne : ((Wc.map (infSub P.inf.N)).eval r) ≠ 0 :=
        S.branch_values_ne_zero Wc hW0 _ (infSub_injective _ hNi) li hli' _
          (List.mem_map.mpr ⟨r, hr, rfl⟩)
      have := le_order_of_lowerBd _ hne _ h1
      omega)
    (fun a ↦ (PW.rootMultiplicity a : ℤ) - n * ((Q.map (algebraMap C K)).rootMultiplicity a : ℤ))
    (fun a ha ↦ by
      have h1 := S.sum_order_fin W₁ n hW₁n.le hW₁ _ (hselN a) a (lf a) (hlf a ha)
      have hlen := S.length_of_split (hlf a ha)
      rw [list_sum_map_sub', h1, hlen]
      ring)
    (-(PW.natDegree : ℤ) + n * Q.natDegree)
    (by
      have h1 := S.sum_order_inf W₁ n hW₁n.le hW₁ _ hNi li hli'
      have hlen := S.length_of_split hli'
      rw [list_sum_map_add', h1, hlen, hPdeg]
      ring)
    (by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hPsum, hQsum, hQdeg]
      ring)
  obtain ⟨h1, h2, h3⟩ := hED
  refine ⟨fun hac0 r hr ↦ ?_, fun r hr ↦ ?_, h3⟩
  · have ha : algebraMap C K (ψ₀ ac0.1) ∈ T := mem_ptsK P ψ₀ ac0 hac0
    have hl0 := hlf _ ha
    rw [hsel0 hac0] at hl0
    have := h1 _ ha r (mem_of_root hl0 r hr)
    simp only [hsel0 hac0] at this
    omega
  · have := h2 r (mem_of_root hli' r hr)
    omega

end CurveData

end Roots

section Pack

variable {F : Type*} [Field F]

/-- A bivariate polynomial as a `BPoly`. -/
noncomputable def ofB (W : F[X][X]) : BPoly F :=
  (List.range (W.natDegree + 1)).map fun i ↦
    (List.range ((W.coeff i).natDegree + 1)).map (W.coeff i).coeff

lemma toB_ofB (W : F[X][X]) : toB (ofB W) = W := by
  ext1 l
  rw [coeff_toB]
  rcases Nat.lt_or_ge l (W.natDegree + 1) with hl | hl
  · simp only [ofB, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl,
      Option.map_some, Option.getD_some]
    exact NFC.toPoly_coeffList _
  · rw [List.getD_eq_default _ _ (by simp [ofB]; omega), coeff_eq_zero_of_natDegree_lt (by omega)]
    rfl

lemma length_ofB (W : F[X][X]) : (ofB W).length = W.natDegree + 1 := by simp [ofB]

end Pack

section Wit

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L)
variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- **Logarithmic witnesses from torsion data**: if `w ≠ 0` has order `m · Λ(res f dx)` along every
branch (`Λ ∘ ψ₀ = coord_j`), there is a witness `⟨m, W, Q⟩` accepted by `witOK` for coordinate `j`
by every valid problem with the same curve, integrand, certified points and ramification indices,
once the precisions exceed a bound `B`. -/
theorem witOK_of_tors (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) (j : Fin (dim F)) (m : ℕ) (hm : 0 < m) (Λ : K →ₗ[ℚ] ℚ)
    (hΛ : ∀ r : F, Λ (algebraMap C K (ψ₀ r)) = coord j r) (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (hord : S.TorsOrdStd P ψ₀ m w Λ) :
    ∃ (W : BPoly F) (Q : CPoly F) (B : ℕ), ∀ P' : CurveProb F, P'.Fc = P.Fc → P'.n = P.n →
      P'.k = P.k → P'.A = P.A → P'.D = P.D →
      P'.pts.map (fun ac ↦ (ac.1, ac.2.N)) = P.pts.map (fun ac ↦ (ac.1, ac.2.N)) →
      P'.inf.N = P.inf.N → P'.ValidFacts → (∀ ac ∈ P'.pts, B ≤ ac.2.prec) → B ≤ P'.inf.prec →
      P'.witOK ⟨m, W, Q⟩ j = true := by
  classical
  obtain ⟨W₁, QF, hQF0, hQr, hW₁n, hwQ⟩ := S.exists_W1 P ψ₀ hSF hV m w Λ hord
  have hQ0 : QF.map ψ₀ ≠ 0 := (Polynomial.map_ne_zero_iff ψ₀.injective).mpr hQF0
  have hW₁e : S.evXY W₁ ≠ 0 := by
    rw [← hwQ]; exact mul_ne_zero (fun h ↦ hw (Subtype.ext h)) (S.aeval_x_ne_zero _ hQ0)
  have hW₁0 : W₁ ≠ 0 := fun h ↦ hW₁e (by rw [h, evXY, Polynomial.map_zero, eval_zero])
  obtain ⟨W, hW0, hWn, hWf, hWi⟩ := S.exists_WF (K := K) P ψ₀ hSF hV W₁ hW₁n hW₁0
  have hWc0 : S.evXY (W.map (mapRingHom ψ₀)) ≠ 0 := fun h ↦ hW0 (by
    have := S.irr _ (lt_of_le_of_lt natDegree_map_le hWn) h
    exact (Polynomial.map_eq_zero_iff (Polynomial.map_injective _ ψ₀.injective)).mp this)
  have hex := fun ac0 hN0 ↦ S.exact_at P ψ₀ hSF hV m w Λ hord hw W₁ hW₁n QF hQr hQ0 hwQ W hWc0
    hWf hWi ac0 hN0
  have h3 := (hex ((0 : F), (⟨1, [], 0⟩ : BranchCert F)) one_pos).2.2
  set WB := ofB W with hWBdef
  set Q : CPoly F := (List.range (QF.natDegree + 1)).map QF.coeff with hQdef
  have hWB : toB WB = W := toB_ofB W
  have hQ : toPoly Q = QF := NFC.toPoly_coeffList QF
  have hlen : WB.length - 1 = W.natDegree := by rw [length_ofB]; rfl
  set d := ((S.normW ((toB WB).map (mapRingHom ψ₀)) (WB.length - 1)).map (algebraMap C K)).natDegree
    with hd
  set Nsum := (P.pts.map fun ac ↦ ac.2.N).sum with hNsum
  set I := P.n * (P.inf.N * invDeg WB P.k) with hI
  -- exact roots above infinity
  obtain ⟨wi, -, hwi⟩ := S.inf_roots_F (K := K) P ψ₀ hSF hV
  set li : List (LaurentSeries K) := List.ofFn fun k ↦ single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) *
    ofPowerSeries ℤ K (PowerSeries.map ((algebraMap C K).comp ψ₀) (wi k)) with hli
  have hli' : S.F.map (infSub P.inf.N) = (li.map fun r ↦ X - Polynomial.C r).prod := by
    rw [hwi, hli, List.map_ofFn, List.prod_ofFn]; rfl
  have hnW : S.normW (W.map (mapRingHom ψ₀)) W.natDegree ≠ 0 :=
    S.normW_ne_zero _ W.natDegree natDegree_map_le hWc0 _ (infSub_injective P.inf.N hV.infN) li hli'
  have hnWK : (S.normW (W.map (mapRingHom ψ₀)) W.natDegree).map (algebraMap C K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hnW
  refine ⟨WB, Q, Nsum * (d + 1) + I + 1, fun P' hFc hn hk hA hD hpts hinfN hV' hB hBi ↦ ?_⟩
  have hSF' : S.F = (toB P'.Fc).map (mapRingHom ψ₀) := by rw [hFc]; exact hSF
  have hfE : S.fE P' ψ₀ = S.fE P ψ₀ := by simp only [CurveData.fE, hA, hD]
  have hmemP : ∀ ac ∈ P'.pts, ∃ ac' ∈ P.pts, ac'.1 = ac.1 ∧ ac'.2.N = ac.2.N := by
    intro ac hac
    have : (ac.1, ac.2.N) ∈ P.pts.map (fun ac ↦ (ac.1, ac.2.N)) :=
      hpts ▸ List.mem_map.mpr ⟨ac, hac, rfl⟩
    obtain ⟨ac', h', he⟩ := List.mem_map.mp this
    exact ⟨ac', h', (Prod.mk.inj he).1, (Prod.mk.inj he).2⟩
  have hfst : P'.pts.map Prod.fst = P.pts.map Prod.fst := by
    have := congrArg (List.map Prod.fst) hpts
    simpa [List.map_map, Function.comp_def] using this
  have hnorm : (toPoly (normRC P'.Fc WB P'.n P'.k)).map ψ₀ =
      S.normW (W.map (mapRingHom ψ₀)) W.natDegree := by
    rw [toPoly_normRC P'.Fc WB P'.n P'.k hV'.mon hV'.deg (fun i ↦ by rw [coeff_toB]; exact hV'.kF i),
      CurveData.normW, S.natDegree_F_eq P' ψ₀ hSF' hV', hSF', hlen, hWB, resultant_map_map]
    rfl
  have hkey : ∀ z : K,
      ((toPoly (mul (normRC P'.Fc WB P'.n P'.k) Q)).map ((algebraMap C K).comp ψ₀)).eval z = 0 →
      z ∈ ptsK P ψ₀ := by
    intro z hz
    rw [← Polynomial.map_map, CPoly.toPoly_mul, Polynomial.map_mul, hnorm, hQ, Polynomial.map_mul,
      eval_mul] at hz
    rcases mul_eq_zero.mp hz with h | h
    · by_contra hzT
      exact ((rootMultiplicity_pos hnWK).mpr h).ne' (h3 z hzT)
    · exact hQr z (by rw [← Polynomial.map_map]; exact h)
  refine S.witOK_of_exact P' ψ₀ hSF' hV' WB Q j m hm Λ hΛ (by rw [hWB]; exact hWc0)
    (by rw [hQ]; exact hQF0) ?_ ?_ ?_ ?_ ?_ ?_
  · -- finite branches
    intro ac hac hN r hr
    obtain ⟨ac', hac', h1, h2⟩ := hmemP ac hac
    have e := (hex ac' (N_pos_of_mem P hV ac' hac')).1 hac' r (by rw [h1, h2]; exact hr)
    rw [h1, h2] at e
    have hb := S.eval_W_branch (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))
      (branchSub_injective _ hN _) r hr w W₁ _ hwQ
    have he : S.embG _ (branchSub_injective ac.2.N hN (algebraMap C K (ψ₀ ac.1))) r hr w ≠ 0 :=
      (map_ne_zero_iff _ (S.embG _ _ r hr).injective).mpr hw
    have hg : branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)) (QF.map ψ₀) ≠ 0 :=
      (map_ne_zero_iff _ (branchSub_injective _ hN _)).mpr hQ0
    have ho := hord.1 (algebraMap C K (ψ₀ ac.1)) ac.2.N hN r hr
    rw [hfE, hWB, hQ, e, hb, HahnSeries.order_mul he hg, ← ho]
    push_cast; ring
  · -- infinity
    have hkeyI : ∀ (N : ℕ) (hN : 0 < N), N = P.inf.N →
        ∀ r (hr : (S.F.map (infSub (K := K) N)).eval r = 0),
        (((((toB WB).map (mapRingHom ψ₀)).map (infSub N)).eval r).order +
          ((N * degT Q : ℕ) : ℤ) : ℚ) =
        m * Λ (LaurentSeries.res (S.embG (infSub N) (infSub_injective N hN) r hr
          (S.fE P ψ₀) * LaurentSeries.derivation (single (-(N : ℤ)) (1 : K)))) := by
      rintro N hN rfl r hr
      have e := (hex ((0 : F), (⟨1, [], 0⟩ : BranchCert F)) one_pos).2.1 r hr
      have hb := S.eval_W_branch (infSub P.inf.N) (infSub_injective _ hN) r hr w W₁ _ hwQ
      have he : S.embG _ (infSub_injective P.inf.N hN) r hr w ≠ 0 :=
        (map_ne_zero_iff _ (S.embG _ _ r hr).injective).mpr hw
      have hg : infSub (K := K) P.inf.N (QF.map ψ₀) ≠ 0 :=
        (map_ne_zero_iff _ (infSub_injective _ hN)).mpr hQ0
      have ho := hord.2 P.inf.N hN r hr
      rw [hWB, e, hb, HahnSeries.order_mul he hg, order_infSub _ hN _ hQ0, degT_eq, hQ,
        natDegree_map_eq_of_injective ψ₀.injective, ← ho]
      push_cast; ring
    intro r hr
    rw [hfE]
    exact hkeyI P'.inf.N hV'.infN hinfN r hr
  · -- the norm times `Q` is non-zero
    intro h0
    have := congrArg (Polynomial.map ψ₀) h0
    rw [CPoly.toPoly_mul, Polynomial.map_mul, hnorm, hQ, Polynomial.map_zero] at this
    exact mul_ne_zero hnW hQ0 this
  · -- cover
    intro z hz
    obtain ⟨b, hb, hbz⟩ := Finset.mem_image.mp (hkey z hz)
    exact ⟨b, hfst ▸ List.mem_toFinset.mp hb, hbz.symm⟩
  · -- precision at finite points
    intro ac hac
    obtain ⟨ac', hac', -, h2⟩ := hmemP ac hac
    have hN : ac.2.N ≤ Nsum := h2 ▸ List.le_sum_of_mem (List.mem_map.mpr ⟨ac', hac', rfl⟩)
    have hmu := rootMultiplicity_le_natDegree'
      ((S.normW ((toB WB).map (mapRingHom ψ₀)) (WB.length - 1)).map (algebraMap C K))
      (algebraMap C K (ψ₀ ac.1))
    have h1 : ac.2.N * ((S.normW ((toB WB).map (mapRingHom ψ₀)) (WB.length - 1)).map
        (algebraMap C K)).rootMultiplicity (algebraMap C K (ψ₀ ac.1)) ≤ Nsum * d :=
      Nat.mul_le_mul hN hmu
    have h2 := hB ac hac
    rw [mul_add, mul_one] at h2
    omega
  · -- precision at infinity
    rw [hn, hinfN, hk]
    omega

end CurveData

end Wit

end Curves
