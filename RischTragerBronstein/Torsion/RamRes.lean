import RischTragerBronstein.Torsion.RamNonTors
import RischTragerBronstein.Torsion.ResTors

/-!
# Non-elementary integrals from non-torsion residue divisors at places

The version of `ResTors` for divisors supported on arbitrary (possibly ramified) places above the
fibres of a `PlaceCert`: `torsResCheckP P T Pc eL s j₀` checks that `s` times the `j₀`-residue of
`f dx` along the certified root `k` above `α_j` (parameter `x = α_j + T^{N_j}`) is
`s_{jk} Γ_{π_{jk}} − e_j N_j`, that the residues are uniform at the other special points and above
infinity, and computes the degree. `false_of_torsResP`: then `f dx` has no elementary integral,
given the certificates of `not_torsion_places_map`.
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries GTors

section Defs

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- The exponent of `x − a` at a special point outside the fibres of `Pc`. -/
def fexpP (P : CurveProb F) (Pc : PlaceCert F) (s : ℕ) (j₀ : Fin (dim F))
    (ac : F × BranchCert F) : ℤ :=
  if ac.1 ∈ Pc.αs then 0 else (-(s * rho0 P j₀ ac / ac.2.N)).num

/-- The certificate of the fibre `j` (the approximations are not used by `resFin`). -/
def PlaceCert.fc (Pc : PlaceCert F) (j : ℕ) : BranchCert F := ⟨Pc.fN j, [], Pc.tp.getD j 0⟩

/-- **The residue check at places.** -/
def torsResCheckP (P : CurveProb F) (T : GlobalCert F) (Pc : PlaceCert F) (eL : List ℤ) (s : ℕ)
    (j₀ : Fin (dim F)) : Bool :=
  decide (T.Fc = P.Fc) && decide (T.n = P.n) && decide (0 < s) &&
  decide (P.pts.map Prod.fst).Nodup &&
  (List.range Pc.fib.length).all (fun j ↦
    decide (P.mufFin (Pc.fα j) (Pc.fN j) < Pc.tp.getD j 0 + Pc.fN j) &&
    decide (P.mufFin (Pc.fα j) (Pc.fN j) < (P.QfFin (Pc.fα j) (Pc.fN j)).length) &&
    (List.range T.n).all fun k ↦
      decide ((s : ℚ) * coord j₀ (P.resFin (Pc.fα j) (Pc.fc j) (Pc.apx j k)) =
        (((Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0 : ℕ) : ℤ) - eL.getD j 0 * Pc.fN j : ℤ))) &&
  P.pts.all (fun ac ↦ decide (ac.1 ∈ Pc.αs) ||
    (ac.2.ys.all (fun yt ↦ decide (coord j₀ (P.resFin ac.1 ac.2 yt) = rho0 P j₀ ac)) &&
      decide ((s * rho0 P j₀ ac / ac.2.N).den = 1))) &&
  P.inf.ys.all (fun wt ↦ decide (coord j₀ (P.resInf wt) = coord j₀ (P.resInf (P.inf.ys.getD 0 [])))) &&
  decide (((∑ j ∈ Finset.range Pc.fib.length, eL.getD j 0 : ℤ) : ℚ) +
      ((P.pts.map (fexpP P Pc s j₀)).sum : ℚ) -
      s * coord j₀ (P.resInf (P.inf.ys.getD 0 [])) / P.inf.N = Pc.cΓ)

/-- The content of `torsResCheckP`. -/
structure TorsResFactsP (P : CurveProb F) (T : GlobalCert F) (Pc : PlaceCert F) (eL : List ℤ)
    (s : ℕ) (j₀ : Fin (dim F)) : Prop where
  Fc : T.Fc = P.Fc
  n : T.n = P.n
  s_pos : 0 < s
  nd : (P.pts.map Prod.fst).Nodup
  Γpt : ∀ j < Pc.fib.length,
    P.mufFin (Pc.fα j) (Pc.fN j) < Pc.tp.getD j 0 + Pc.fN j ∧
    P.mufFin (Pc.fα j) (Pc.fN j) < (P.QfFin (Pc.fα j) (Pc.fN j)).length ∧
    ∀ k < T.n, (s : ℚ) * coord j₀ (P.resFin (Pc.fα j) (Pc.fc j) (Pc.apx j k)) =
      (((Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0 : ℕ) : ℤ) - eL.getD j 0 * Pc.fN j : ℤ)
  other : ∀ ac ∈ P.pts, ac.1 ∉ Pc.αs → (∀ yt ∈ ac.2.ys, coord j₀ (P.resFin ac.1 ac.2 yt) =
    rho0 P j₀ ac) ∧ (s * rho0 P j₀ ac / ac.2.N).den = 1
  inf : ∀ wt ∈ P.inf.ys, coord j₀ (P.resInf wt) = coord j₀ (P.resInf (P.inf.ys.getD 0 []))
  csum : (((∑ j ∈ Finset.range Pc.fib.length, eL.getD j 0 : ℤ) : ℚ) +
      ((P.pts.map (fexpP P Pc s j₀)).sum : ℚ) -
      s * coord j₀ (P.resInf (P.inf.ys.getD 0 [])) / P.inf.N = Pc.cΓ)

lemma torsResCheckP_spec {P : CurveProb F} {T : GlobalCert F} {Pc : PlaceCert F} {eL : List ℤ}
    {s : ℕ} {j₀ : Fin (dim F)} (h : torsResCheckP P T Pc eL s j₀ = true) :
    TorsResFactsP P T Pc eL s j₀ := by
  simp only [torsResCheckP, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, and_assoc] at h
  obtain ⟨hFc, hn, hs, hnd, hΓ, hoth, hinf, hsum⟩ := h
  refine ⟨hFc, hn, hs, hnd, fun j hj ↦ ?_, fun ac hac hna ↦ ?_, fun wt hwt ↦ hinf wt hwt, hsum⟩
  · obtain ⟨h1, h2, h3⟩ := hΓ j hj
    exact ⟨h1, h2, fun k hk ↦ by exact_mod_cast h3 k hk⟩
  · rcases hoth ac hac with h1 | ⟨h1, h2⟩
    · exact absurd h1 hna
    · exact ⟨h1, h2⟩

end Defs

section Link

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L] [Field K]
  [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) (ψ : F →+* C)
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)

include hSF hV in
/-- **The `j₀`-residues along the certified roots at places.** -/
lemma lam_res_ΓP (Λ : K →ₗ[ℚ] ℚ) {j₀ : Fin (dim F)}
    (hΛ : ∀ r : F, Λ (algebraMap C K (ψ r)) = coord j₀ r) {T : GlobalCert F} {Pc : PlaceCert F}
    {eL : List ℤ} {s : ℕ} (hTR : TorsResFactsP P T Pc eL s j₀)
    (hPc : Pc.Facts T.Fc T.n) (j : ℕ) (hj : j < Pc.fib.length) (k : Fin S.F.natDegree)
    (r : LaurentSeries K) (hr : r = lmap (algebraMap C K) (rCC ψ T.Fc Pc j k))
    (hY : (S.F.map (branchSub (Pc.fN j) (algebraMap C K (ψ (Pc.fα j))))).eval r = 0) (hN : 0 < Pc.fN j) :
    (s : ℚ) * Λ (LaurentSeries.res (S.embG (branchSub (Pc.fN j) (algebraMap C K (ψ (Pc.fα j))))
      (branchSub_injective _ hN _) r hY (S.fE P ψ) *
        LaurentSeries.derivation (HahnSeries.C (algebraMap C K (ψ (Pc.fα j))) +
          single ((Pc.fN j : ℕ) : ℤ) (1 : K)))) =
      (((Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0 : ℕ) : ℤ) - eL.getD j 0 * Pc.fN j : ℤ) := by
  classical
  have hf := S.fE_spec P ψ hV
  have hnS : S.F.natDegree = T.n := by rw [S.natDegree_F_eq P ψ hSF hV, hTR.n]
  set g : F →+* K := (algebraMap C K).comp ψ with hg
  obtain ⟨-, hrt⟩ := hPc.rt j hj
  obtain ⟨hπ, -, hs, -, -, htp⟩ := hrt k (by rw [← hnS]; exact k.2)
  set Y : PowerSeries K := PowerSeries.map g
    (conjPS (Pc.rζ j k) (Pc.rs j k) (repK T.Fc Pc (Pc.rπ j k))) with hYdef
  have e : r = ofPowerSeries ℤ K Y := by
    rw [hr, rCC, rCK, lmap_ofPS, lmap_ofPS, hYdef, hg, PowerSeries.map_comp]
    rfl
  subst e
  have hy : (PowerSeries.X : PowerSeries K) ^ (Pc.fc j).prec ∣
      Y - thetaT ((algebraMap C K).comp ψ) (toPoly (Pc.apx j k)) := by
    obtain ⟨-, hd⟩ := repK_spec T.Fc Pc (Pc.rπ j k) (hPc.pl _ hπ).2.2
    have hd' := map_dvd (PowerSeries.map g) hd
    rw [map_pow, PowerSeries.map_X, map_sub, thetaT_apply, map_coe_poly, Polynomial.map_map,
      RingHom.comp_id, ← thetaT_apply] at hd'
    rw [hYdef, map_conjPS]
    exact conj_approx g (Pc.rζ j k) hs _ _ hd' htp
  obtain ⟨hμf, hQfl, hck⟩ := hTR.Γpt j hj
  have hres := S.resFin_sem P ψ hSF (Pc.fα j) (Pc.fc j) hN Y hY (Pc.apx j k) hy hμf hQfl _ hf
  simp only [PlaceCert.fc] at hres hck
  rw [hres, RingHom.comp_apply, hΛ, hck k (by rw [← hnS]; exact k.2)]

end CurveData

end Link

section Main

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

namespace CurveData

variable (S : CurveData C L)

lemma fexpP_eq {P : CurveProb F} {Pc : PlaceCert F} {s : ℕ} {j₀ : Fin (dim F)}
    {ac : F × BranchCert F} (hna : ac.1 ∉ Pc.αs) (hden : (s * rho0 P j₀ ac / ac.2.N).den = 1) :
    (fexpP P Pc s j₀ ac : ℚ) = -(s * rho0 P j₀ ac / ac.2.N) := by
  rw [fexpP, if_neg hna]
  exact Rat.coe_int_num_of_den_eq_one (by rw [Rat.den_neg_eq_den]; exact hden)

lemma fexpP_mem {P : CurveProb F} {Pc : PlaceCert F} {s : ℕ} {j₀ : Fin (dim F)}
    {ac : F × BranchCert F} (ha : ac.1 ∈ Pc.αs) : fexpP P Pc s j₀ ac = 0 := by
  rw [fexpP, if_pos ha]

set_option maxHeartbeats 16000000 in
/-- **A Liouville form contradicts the non-torsion certificate at places.** -/
theorem false_of_torsResP (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (P : CurveProb F) (ψ : F →+* C)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts) (T : GlobalCert F)
    (hT : T.globalCheck = true) (Pc : PlaceCert F) (hPc : Pc.check T.Fc T.n = true)
    (eL : List ℤ) (s : ℕ) (j₀ : Fin (dim F))
    (hTR : torsResCheckP P T Pc eL s j₀ = true) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q)
    (Rp : RedFns p F) (φp : F →+* ℚ_[p]) (hRp : RedValid p Rp φp) (Pp : PrimeCert p)
    (hPp : primeCheck Rp T Pp = true) (Qp : PlaceCert.PrimeData p)
    (hQp : Pc.primeCheck Rp T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pp.xs Qp = true)
    (Rq : RedFns q F) (φq : F →+* ℚ_[q]) (hRq : RedValid q Rq φq) (Pq : PrimeCert q)
    (hPq : primeCheck Rq T Pq = true) (Qq : PlaceCert.PrimeData q)
    (hQq : Pc.primeCheck Rq T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pq.xs Qq = true)
    (Pb : ℕ) (Lm : List (List F))
    (htest : nonPrincOK T.n ((Qp.mp * Qq.mp) * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (Qp.mp * Qq.mp)) Lm = true ∨
      nonPrincOK T.n (pairMult p q Qp.mp Qq.mp * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (pairMult p q Qp.mp Qq.mp)) Lm = true)
    (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) {ιI : Type*} [DecidableEq ιI] (sI : Finset ιI) (c : ιI → C)
    (u : ιI → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0)
    (heq : (S.fE P ψ : L) = v′ + ∑ i ∈ sI, algebraMap C L (c i) * ((u i)′ / u i)) : False := by
  classical
  set Kb := AlgebraicClosure C
  haveI : CharZero Kb := charZero_of_injective_algebraMap (algebraMap C Kb).injective
  have hTR' := torsResCheckP_spec hTR
  have hTf := globalCheck_spec hT
  obtain ⟨hn0, hmon, hdeg, -⟩ := hTf.shape
  have hPcF := Pc.check_spec hPc
  -- the functional `Λ` extending `coord j₀`, and its multiple `s Λ`
  have hinj : Function.Injective ((algebraMap C Kb).comp ψ) :=
    (algebraMap C Kb).injective.comp ψ.injective
  set ιF : F →ₗ[ℚ] Kb := ((algebraMap C Kb).comp ψ).toRatAlgHom.toLinearMap with hιF
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ιF (LinearMap.ker_eq_bot.mpr hinj)
  set Λ : Kb →ₗ[ℚ] ℚ := (coord j₀).comp g with hΛdef
  have hΛ : ∀ r : F, Λ (algebraMap C Kb (ψ r)) = coord j₀ r := fun r ↦ by
    have : g (ιF r) = r := by rw [← LinearMap.comp_apply, hg, LinearMap.id_apply]
    rw [hΛdef, LinearMap.comp_apply]
    exact congrArg (coord j₀) this
  set Λs : Kb →ₗ[ℚ] ℚ := (s : ℚ) • Λ with hΛs
  have hΛs' : ∀ z, Λs z = s * Λ z := fun z ↦ by rw [hΛs, LinearMap.smul_apply, smul_eq_mul]
  -- Abel
  obtain ⟨m, hm, w, hw0, hord⟩ := S.curve_abel (K := Kb) hC hx _ v (S.fE P ψ).2 hv sI c u hu hu0
    heq Λs
  -- the fibres
  set mf := Pc.fib.length with hmf
  have hSF' : S.F = (toB T.Fc).map (mapRingHom ψ) := by rw [hSF, hTR'.Fc]
  have hnS : S.F.natDegree = T.n := by rw [hSF', hmon.natDegree_map, hdeg]
  have hPcd : Pc.Facts T.Fc (toB T.Fc).natDegree := by rw [hdeg]; exact hPcF
  have hNpos : ∀ j : Fin mf, 0 < Pc.fN j := fun j ↦ PlaceCert.fN_pos hPcF hn0 j j.2
  have hαinj := PlaceCert.fα_inj hPcF
  have hspC := fun j : Fin mf ↦ split_places_map S ψ T.Fc hmon hSF' Pc hPcd j j.2
  have hlf : ∀ j : Fin mf, S.F.map (branchSub (Pc.fN j) (algebraMap C Kb (ψ (Pc.fα j)))) =
      ((List.ofFn fun k : Fin S.F.natDegree ↦ lmap (algebraMap C Kb) (rCC ψ T.Fc Pc j k)).map
        fun r ↦ X - Polynomial.C r).prod := fun j ↦
    S.split_lmap (K := Kb) (Pc.fN j) (ψ (Pc.fα j)) (fun k ↦ rCC ψ T.Fc Pc j k) (hspC j).1
  have hinjK : ∀ j : Fin mf, Function.Injective fun k : Fin S.F.natDegree ↦
      lmap (algebraMap C Kb) (rCC ψ T.Fc Pc j k) := fun j ↦ (lmap_injective _).comp (hspC j).2
  set α : Fin mf → F := fun j ↦ Pc.fα j with hα
  set pt : Fin P.pts.length → F × BranchCert F := fun i ↦ P.pts[i.1] with hpt
  set fe : Fin P.pts.length → ℤ := fun i ↦ fexpP P Pc s j₀ (pt i) with hfe
  set U1 : C⟮S.x⟯⟮S.y⟯ := ∏ j ∈ Finset.univ, (S.qE ψ (xSubC (α j))) ^ ((m : ℤ) * eL.getD j 0)
    with hU1
  set U2 : C⟮S.x⟯⟮S.y⟯ := ∏ i ∈ Finset.univ, (S.qE ψ (xSubC (pt i).1)) ^ ((m : ℤ) * fe i)
    with hU2
  have hq0 : ∀ a : F, S.qE ψ (xSubC a) ≠ 0 := fun a h ↦
    S.qE_ne_zero (ψ₀ := ψ) _ (by rw [toPoly_xSubC]; exact X_sub_C_ne_zero _) (congrArg Subtype.val h)
  have hU10 : U1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (hq0 _)
  have hU20 : U2 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hq0 _)
  have hptmem : ∀ i, pt i ∈ P.pts := fun i ↦ List.getElem_mem _
  have hptinj : ∀ i i', (pt i).1 = (pt i').1 → i = i' := fun i i' h ↦ by
    have := (List.Nodup.getElem_inj_iff hTR'.nd (i := i.1) (j := i'.1)
      (hi := by simpa using i.2) (hj := by simpa using i'.2)).mp (by simpa [hpt] using h)
    exact Fin.ext this
  have hαmem : ∀ j : Fin mf, α j ∈ Pc.αs := fun j ↦ by
    rw [hα]; dsimp only
    rw [← Pc.αs_getD j j.2, List.getD_eq_getElem _ _ (by simp only [PlaceCert.αs, List.length_map]; exact j.2)]
    exact List.getElem_mem _
  -- orders of the correction factors along finite branches
  have hordU : ∀ (N' : ℕ) (hN' : 0 < N') (b : Kb) (Y : LaurentSeries Kb)
      (hY : (S.F.map (branchSub N' b)).eval Y = 0),
      (S.embG (branchSub N' b) (branchSub_injective N' hN' b) Y hY (U1 * U2)).order =
        (∑ j : Fin mf, (m : ℤ) * eL.getD j 0 *
          (if b = algebraMap C Kb (ψ (α j)) then (N' : ℤ) else 0)) +
        ∑ i : Fin P.pts.length, (m : ℤ) * fe i *
          (if b = algebraMap C Kb (ψ (pt i).1) then (N' : ℤ) else 0) := by
    intro N' hN' b Y hY
    rw [map_mul, HahnSeries.order_mul ((map_ne_zero_iff _ (RingHom.injective _)).mpr hU10)
      ((map_ne_zero_iff _ (RingHom.injective _)).mpr hU20), hU1, hU2,
      S.order_prod_zpow _ _ _ (fun j _ ↦ hq0 _), S.order_prod_zpow _ _ _ (fun i _ ↦ hq0 _)]
    simp only [S.order_qE_xSubC_fin ψ _ N' hN']
  have hordUi : ∀ (N' : ℕ) (hN' : 0 < N') (Y : LaurentSeries Kb)
      (hY : (S.F.map (infSub N')).eval Y = 0),
      (S.embG (infSub N') (infSub_injective N' hN') Y hY (U1 * U2)).order =
        -(N' : ℤ) * m * ((∑ j : Fin mf, eL.getD j 0) + ∑ i, fe i) := by
    intro N' hN' Y hY
    rw [map_mul, HahnSeries.order_mul ((map_ne_zero_iff _ (RingHom.injective _)).mpr hU10)
      ((map_ne_zero_iff _ (RingHom.injective _)).mpr hU20), hU1, hU2,
      S.order_prod_zpow _ _ _ (fun j _ ↦ hq0 _), S.order_prod_zpow _ _ _ (fun i _ ↦ hq0 _)]
    simp only [S.order_qE_xSubC_inf ψ _ N' hN']
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ ↦ by ring
  have hwne : ∀ (g' : C[X] →+* LaurentSeries Kb) (hg' : Function.Injective g') (Y : LaurentSeries Kb)
      (hY : (S.F.map g').eval Y = 0), S.embG g' hg' Y hY w ≠ 0 :=
    fun g' hg' Y hY ↦ (map_ne_zero_iff _ (RingHom.injective _)).mpr hw0
  have hUne : ∀ (g' : C[X] →+* LaurentSeries Kb) (hg' : Function.Injective g') (Y : LaurentSeries Kb)
      (hY : (S.F.map g').eval Y = 0), S.embG g' hg' Y hY (U1 * U2) ≠ 0 :=
    fun g' hg' Y hY ↦ (map_ne_zero_iff _ (RingHom.injective _)).mpr (mul_ne_zero hU10 hU20)
  refine not_torsion_places_map (Kb := Kb) S ψ T hSF' (globalCheckR_of_globalCheck hT) Pc hPc hpq Rp φp hRp Pp hPp Qp hQp
    Rq φq hRq Pq hPq Qq hQq Pb Lm htest m hm hNpos hlf
    ⟨w * (U1 * U2), mul_ne_zero hw0 (mul_ne_zero hU10 hU20), ?_, ?_, ?_⟩
  · -- the fibres of `Γ`
    intro j r hr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    set a := algebraMap C Kb (ψ (Pc.fα j)) with ha
    have hY := S.root_of_mem (hlf j) hr
    have h1 := hord (HahnSeries.C a + single ((Pc.fN j : ℕ) : ℤ) (1 : Kb)) (hX_fin _ (hNpos j) a)
      (branchSub (Pc.fN j) a) (branchSub_injective _ (hNpos j) a)
      (fun Q ↦ by rw [SuperData.branchSub_eq_subst]) _ hY
    simp only [Subtype.coe_eta] at h1
    rw [hΛs', S.lam_res_ΓP P ψ hSF hV Λ hΛ hTR' hPcF j j.2 k _ rfl hY
      (hNpos j)] at h1
    have h3 : (S.embG (branchSub (Pc.fN j) a) (branchSub_injective _ (hNpos j) a) _ hY w).order =
        m * (((Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0 : ℕ) : ℤ) - eL.getD j 0 * Pc.fN j) := by
      exact_mod_cast h1
    have hs1 : (∑ j' : Fin mf, (m : ℤ) * eL.getD j' 0 *
        (if a = algebraMap C Kb (ψ (α j')) then ((Pc.fN j : ℕ) : ℤ) else 0)) =
        m * eL.getD j 0 * Pc.fN j := by
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl]
      · intro j' _ hj'
        rw [if_neg, mul_zero]
        intro he
        exact hj' (hαinj (ψ.injective ((algebraMap C Kb).injective he)).symm)
      · simp
    have hs2 : (∑ i : Fin P.pts.length, (m : ℤ) * fe i *
        (if a = algebraMap C Kb (ψ (pt i).1) then ((Pc.fN j : ℕ) : ℤ) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      split_ifs with he
      · have hmem : (pt i).1 ∈ Pc.αs := by
          rw [← ψ.injective ((algebraMap C Kb).injective he)]; exact hαmem j
        rw [hfe]; dsimp only; rw [fexpP_mem hmem]; ring
      · ring
    have hext : Function.extend
        (fun k : Fin S.F.natDegree ↦ lmap (algebraMap C Kb) (rCC ψ T.Fc Pc j k))
        (fun k ↦ Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) 0
        (lmap (algebraMap C Kb) (rCC ψ T.Fc Pc j k)) = Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0 :=
      (hinjK j).extend_apply _ _ k
    beta_reduce
    rw [hext, map_mul, HahnSeries.order_mul (hwne _ _ _ _) (hUne _ _ _ _),
      hordU _ (hNpos j) a _ hY, hs1, hs2, h3]
    push_cast; ring_nf; exact le_refl _
  · -- the other finite points
    intro b hb N' hN' l hl r hr
    have hb' : ∀ j : Fin mf, b ≠ algebraMap C Kb (ψ (α j)) := fun j he ↦ hb ⟨j, he.symm⟩
    have hN0 := Nat.pos_of_ne_zero hN'
    have h1 := hord (HahnSeries.C b + single (N' : ℤ) (1 : Kb)) (hX_fin N' hN0 b)
      (branchSub N' b) (branchSub_injective N' hN0 b)
      (fun Q ↦ by rw [SuperData.branchSub_eq_subst]) r (S.root_of_mem hl hr)
    simp only [Subtype.coe_eta] at h1
    rw [hΛs'] at h1
    have hs1 : (∑ j' : Fin mf, (m : ℤ) * eL.getD j' 0 *
        (if b = algebraMap C Kb (ψ (α j')) then (N' : ℤ) else 0)) = 0 :=
      Finset.sum_eq_zero fun j' _ ↦ by rw [if_neg (hb' j'), mul_zero]
    rw [map_mul, HahnSeries.order_mul (hwne _ _ _ _) (hUne _ _ _ _), hordU N' hN0 b _ _, hs1,
      zero_add]
    by_cases hsp : ∃ i, b = algebraMap C Kb (ψ (pt i).1)
    · obtain ⟨i, rfl⟩ := hsp
      have hna : (pt i).1 ∉ Pc.αs := by
        intro hm'
        obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hm'
        have hj' : j < mf := by simpa [PlaceCert.αs] using hj
        refine hb' ⟨j, hj'⟩ ?_
        rw [hα]; dsimp only
        rw [← Pc.αs_getD j hj', List.getD_eq_getElem _ _ hj, hje]
      obtain ⟨hρ, hden⟩ := hTR'.other (pt i) (hptmem i) hna
      have h2 := S.lam_res_fin_special P ψ hSF hV Λ hΛ (pt i).1 (pt i).2 (hptmem i) _ hρ N' hN' l
        hl r hr
      obtain ⟨-, hNc⟩ := CurveProb.length_ys_of_cert (hV.certs _ (hptmem i))
      have hs2 : (∑ i' : Fin P.pts.length, (m : ℤ) * fe i' *
          (if algebraMap C Kb (ψ (pt i).1) = algebraMap C Kb (ψ (pt i').1) then (N' : ℤ)
            else 0)) = m * fe i * N' := by
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl]
        · intro i' _ hi'
          rw [if_neg, mul_zero]
          intro he
          exact hi' (hptinj i' i (ψ.injective ((algebraMap C Kb).injective he)).symm)
        · simp
      rw [hs2]
      have hfe' : (fe i : ℚ) = -(s * rho0 P j₀ (pt i) / (pt i).2.N) := fexpP_eq hna hden
      have hNq : ((pt i).2.N : ℚ) ≠ 0 := by exact_mod_cast hNc.ne'
      have hΛv : Λ (LaurentSeries.res (S.embG (branchSub N' (algebraMap C Kb (ψ (pt i).1)))
          (branchSub_injective N' hN0 _) r (S.root_of_mem hl hr) (S.fE P ψ) *
          LaurentSeries.derivation (HahnSeries.C (algebraMap C Kb (ψ (pt i).1)) +
            single (N' : ℤ) (1 : Kb)))) = N' * rho0 P j₀ (pt i) / (pt i).2.N := by
        field_simp; linarith [h2]
      rw [hΛv] at h1
      have h4 : ((S.embG (branchSub N' (algebraMap C Kb (ψ (pt i).1)))
          (branchSub_injective N' hN0 _) r (S.root_of_mem hl hr) w).order + m * fe i * N' : ℤ) =
          (0 : ℚ) := by
        push_cast; rw [h1, hfe']; field_simp; ring
      exact_mod_cast h4.ge
    · push Not at hsp
      have hreg := S.res_fin_regular P ψ hSF hV b (fun ac hac h ↦ by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hac
        exact hsp ⟨i, hi⟩ h) N' hN' l hl r hr
      rw [hreg, map_zero, mul_zero, mul_zero] at h1
      have hs2 : (∑ i : Fin P.pts.length, (m : ℤ) * fe i *
          (if b = algebraMap C Kb (ψ (pt i).1) then (N' : ℤ) else 0)) = 0 :=
        Finset.sum_eq_zero fun i _ ↦ by rw [if_neg (hsp i), mul_zero]
      rw [hs2, add_zero]
      exact_mod_cast h1.ge
  · -- infinity
    intro N' hN' l hl r hr
    have hN0 := Nat.pos_of_ne_zero hN'
    have h1 := hord (single (-(N' : ℤ)) (1 : Kb)) (hX_inf N' hN0)
      (infSub N') (infSub_injective N' hN0)
      (fun Q ↦ by rw [SuperData.infSub_eq_subst]) r (S.root_of_mem hl hr)
    simp only [Subtype.coe_eta] at h1
    rw [hΛs'] at h1
    have h2 := S.lam_res_inf P ψ hSF hV Λ hΛ _ hTR'.inf N' hN' l hl r hr
    have hNq : (P.inf.N : ℚ) ≠ 0 := by exact_mod_cast hV.infN.ne'
    rw [map_mul, HahnSeries.order_mul (hwne _ _ _ _) (hUne _ _ _ _), hordUi N' hN0 _ _]
    have hfs : (∑ i : Fin P.pts.length, (fe i : ℚ)) = ((P.pts.map (fexpP P Pc s j₀)).sum : ℚ) := by
      rw [← Int.cast_sum]
      congr 1
      rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
    have hes : (∑ j : Fin mf, (eL.getD j 0 : ℚ)) =
        ((∑ j ∈ Finset.range mf, eL.getD j 0 : ℤ) : ℚ) := by
      rw [Fin.sum_univ_eq_sum_range (fun j ↦ (eL.getD j 0 : ℚ)), Int.cast_sum]
    have hcs := hTR'.csum
    have hΛv : Λ (LaurentSeries.res (S.embG (infSub N') (infSub_injective N' hN0) r
        (S.root_of_mem hl hr) (S.fE P ψ) * LaurentSeries.derivation (single (-(N' : ℤ)) (1 : Kb)))) =
        N' * coord j₀ (P.resInf (P.inf.ys.getD 0 [])) / P.inf.N := by
      field_simp; linarith [h2]
    rw [hΛv] at h1
    have h4 : ((S.embG (infSub N') (infSub_injective N' hN0) r (S.root_of_mem hl hr) w).order +
        -(N' : ℤ) * m * ((∑ j : Fin mf, eL.getD j 0) + ∑ i, fe i) : ℤ) =
        ((-((N' * (m * Pc.cΓ) : ℕ) : ℤ) : ℤ) : ℚ) := by
      push_cast
      rw [h1, hfs, hes, ← hcs]
      field_simp; ring
    exact_mod_cast h4.ge

end CurveData

end Main

end Curves
