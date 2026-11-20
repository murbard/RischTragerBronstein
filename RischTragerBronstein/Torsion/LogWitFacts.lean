import RischTragerBronstein.Torsion.LogWitExist
import RischTragerBronstein.Torsion.Degree
import RischTragerBronstein.Curves.ProcRFSem3
import RischTragerBronstein.Torsion.IntBasisCheck
import RischTragerBronstein.Curves.ProcRFSound5
import RischTragerBronstein.Curves.ProcRFSound4

/-!
# From exact divisors to the witness check

**`fin_facts`**: a function `W/Q` (`W`, `Q` over `F`) whose order along *every* finite branch is
`m Λ(res f dX)` gives the facts along the certified branches of a valid problem required by
`witOK_of_orders`, as soon as the precisions exceed the orders (bounded by the norm of `W`).
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries

section Facts

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L)
variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- **Facts along the certified finite branches from an exact divisor.** -/
theorem fin_facts (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) (W : BPoly F) (Q : CPoly F) (j : Fin (dim F)) (m : ℕ)
    (Λ : K →ₗ[ℚ] ℚ) (hΛ : ∀ r : F, Λ (algebraMap C K (ψ₀ r)) = coord j r)
    (hW0 : S.evXY ((toB W).map (mapRingHom ψ₀)) ≠ 0) (hQ0 : toPoly Q ≠ 0)
    (hex : ∀ ac ∈ P.pts, ∀ (hN : 0 < ac.2.N) (r : LaurentSeries K)
      (hr : (S.F.map (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))).eval r = 0),
      (((((toB W).map (mapRingHom ψ₀)).map (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))).eval r).order -
        (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)) ((toPoly Q).map ψ₀)).order : ℚ) =
        m * Λ (LaurentSeries.res (S.embG (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))
          (branchSub_injective ac.2.N hN (algebraMap C K (ψ₀ ac.1))) r hr (S.fE P ψ₀) *
          LaurentSeries.derivation (HahnSeries.C (algebraMap C K (ψ₀ ac.1)) + single (ac.2.N : ℤ) (1 : K)))))
    (hB : ∀ ac ∈ P.pts, ac.2.N * (((S.normW ((toB W).map (mapRingHom ψ₀)) (W.length - 1)).map
      (algebraMap C K)).rootMultiplicity (algebraMap C K (ψ₀ ac.1))) < ac.2.prec) :
    ∀ ac ∈ P.pts, ∀ yt ∈ ac.2.ys, ∃ ρ : PowerSeries K,
      (PowerSeries.X : PowerSeries K) ^ ac.2.prec ∣ ρ - thetaT ((algebraMap C K).comp ψ₀) (toPoly yt) ∧
      ∃ o : ℕ, o < ac.2.prec ∧
        (∀ t < o, PowerSeries.coeff t (((toB W).map (thetaN ((algebraMap C K).comp ψ₀) ac.1 ac.2.N)).eval ρ) = 0) ∧
        PowerSeries.coeff o (((toB W).map (thetaN ((algebraMap C K).comp ψ₀) ac.1 ac.2.N)).eval ρ) ≠ 0 ∧
        (((o : ℤ) - ordQFin Q ac.1 ac.2.N : ℚ) = m * coord j (P.resFin ac.1 ac.2 yt)) := by
  classical
  intro ac hac yt hyt
  have hcert := hV.certs ac hac
  obtain ⟨y, hy, -, hsplit⟩ := certCheck_spec (C := C) (K := K) P.Fc P.n hV.mon hV.deg ac.1 ac.2
    hcert ψ₀
  have hlen : ac.2.ys.length = P.n := by
    simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at hcert
    exact hcert.1.1.2
  have hN : 0 < ac.2.N := by
    simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at hcert
    exact hcert.1.1.1
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hyt
  have hkn : k < P.n := by rw [← hlen]; exact hk
  set ρ := y ⟨k, hkn⟩ with hρ
  have hyk := hy ⟨k, hkn⟩
  rw [List.getD_eq_getElem _ _ hk] at hyk
  refine ⟨ρ, hyk, ?_⟩
  set a := ac.1
  set N := ac.2.N
  set l : List (LaurentSeries K) := List.ofFn fun k ↦ ofPowerSeries ℤ K (y k) with hldef
  have hl : S.F.map (branchSub N (algebraMap C K (ψ₀ a))) = (l.map fun r ↦ X - Polynomial.C r).prod := by
    rw [hSF, hsplit, hldef, List.map_ofFn, List.prod_ofFn]; rfl
  have hrl : ofPowerSeries ℤ K ρ ∈ l := List.mem_ofFn.mpr ⟨⟨k, hkn⟩, rfl⟩
  have hr := S.root_of_mem hl hrl
  set WC := (toB W).map (mapRingHom ψ₀) with hWC
  have hthe : ∀ P' : F[X], ofPowerSeries ℤ K (thetaN ((algebraMap C K).comp ψ₀) a N P') =
      branchSub N (algebraMap C K (ψ₀ a)) (P'.map ψ₀) :=
    fun P' ↦ ofPS_thetaN (K := K) ψ₀ a N P'
  have hval : ∀ z : PowerSeries K, (WC.map (branchSub N (algebraMap C K (ψ₀ a)))).eval
      (ofPowerSeries ℤ K z) =
      ofPowerSeries ℤ K (((toB W).map (thetaN ((algebraMap C K).comp ψ₀) a N)).eval z) := fun z ↦ by
    have hG : WC.map (branchSub N (algebraMap C K (ψ₀ a))) =
        ((toB W).map (thetaN ((algebraMap C K).comp ψ₀) a N)).map (ofPowerSeries ℤ K) := by
      rw [hWC, Polynomial.map_map, Polynomial.map_map]
      congr 1
      exact RingHom.ext fun P' ↦ (hthe P').symm
    rw [hG, eval_map, eval₂_at_apply]
  set V := ((toB W).map (thetaN ((algebraMap C K).comp ψ₀) a N)).eval ρ with hVdef
  have hWm : WC.natDegree ≤ W.length - 1 := natDegree_map_le.trans (natDegree_toB_le_len' W)
  have hne := S.branch_values_ne_zero WC hW0 _ (branchSub_injective N hN (algebraMap C K (ψ₀ a))) l hl
    _ (List.mem_map.mpr ⟨_, hrl, rfl⟩)
  rw [hval] at hne
  have hV0 : V ≠ 0 := fun h ↦ hne (by
    rw [show ((toB W).map (thetaN ((algebraMap C K).comp ψ₀) a N)).eval ρ = V from rfl, h, map_zero])
  have hex0 : ∃ t, PowerSeries.coeff t V ≠ 0 := by
    by_contra h; push Not at h; exact hV0 (PowerSeries.ext fun t ↦ by rw [h t, map_zero])
  set o := Nat.find hex0 with ho
  have h1 : PowerSeries.coeff o V ≠ 0 := Nat.find_spec hex0
  have h0 : ∀ t < o, PowerSeries.coeff t V = 0 := fun t ht ↦ by
    by_contra h; exact Nat.find_min hex0 ht h
  have hordV : (ofPowerSeries ℤ K V).order = o := order_ofPS_eq V o h0 h1
  -- the order is below the precision
  have hsum := S.sum_order_fin WC (W.length - 1) hWm hW0 N hN (algebraMap C K (ψ₀ a)) l hl
  have hnn : ∀ z ∈ l.map (fun r ↦ ((WC.map (branchSub N (algebraMap C K (ψ₀ a)))).eval r).order),
      0 ≤ z := by
    intro z hz
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hz
    obtain ⟨k', rfl⟩ := List.mem_ofFn.mp hr'
    rw [hval]; exact order_ofPS_nonneg _
  have hle := List.single_le_sum hnn _ (List.mem_map.mpr ⟨_, hrl, rfl⟩)
  rw [hval, hordV, hsum] at hle
  have hlt : o < ac.2.prec := by
    have := hB ac hac
    have : (o : ℤ) < ac.2.prec := lt_of_le_of_lt hle (by exact_mod_cast this)
    exact_mod_cast this
  refine ⟨o, hlt, h0, h1, ?_⟩
  -- the residue and the order of `Q`
  obtain ⟨hμ, hμf, -, hQfl⟩ := hV.prec ac hac
  have hres := S.resFin_sem (K := K) P ψ₀ hSF a ac.2 hN ρ hr ac.2.ys[k] hyk hμf
    hQfl (S.fE P ψ₀) (S.fE_spec P ψ₀ hV)
  have hQord := CurveData.ordQFin_spec (K := K) ψ₀ Q hQ0 a N hN
  have hx := hex ac hac hN _ hr
  rw [hval, hordV] at hx
  rw [hQord, hres, RingHom.comp_apply, hΛ] at hx
  push_cast at hx ⊢
  exact hx

/-- **Facts along the certified branches above infinity from an exact divisor.** -/
theorem inf_facts (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) (W : BPoly F) (Q : CPoly F) (j : Fin (dim F)) (m : ℕ)
    (Λ : K →ₗ[ℚ] ℚ) (hΛ : ∀ r : F, Λ (algebraMap C K (ψ₀ r)) = coord j r)
    (hW0 : S.evXY ((toB W).map (mapRingHom ψ₀)) ≠ 0)
    (hex : ∀ (r : LaurentSeries K) (hr : (S.F.map (infSub (K := K) P.inf.N)).eval r = 0),
      (((((toB W).map (mapRingHom ψ₀)).map (infSub P.inf.N)).eval r).order +
        ((P.inf.N * degT Q : ℕ) : ℤ) : ℚ) =
        m * Λ (LaurentSeries.res (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hV.infN) r hr
          (S.fE P ψ₀) * LaurentSeries.derivation (single (-(P.inf.N : ℤ)) (1 : K)))))
    (hB : P.n * (P.inf.N * invDeg W P.k) < P.inf.prec) :
    ∀ wt ∈ P.inf.ys, ∃ ρ : PowerSeries K,
      (PowerSeries.X : PowerSeries K) ^ P.inf.prec ∣ ρ - thetaT ((algebraMap C K).comp ψ₀) (toPoly wt) ∧
      ∃ o : ℕ, o < P.inf.prec ∧
        (∀ t < o, PowerSeries.coeff t
          (((toB (invB W P.k (invDeg W P.k))).map (thetaN ((algebraMap C K).comp ψ₀) 0 P.inf.N)).eval ρ) = 0) ∧
        PowerSeries.coeff o
          (((toB (invB W P.k (invDeg W P.k))).map (thetaN ((algebraMap C K).comp ψ₀) 0 P.inf.N)).eval ρ) ≠ 0 ∧
        (((-((P.inf.N * invDeg W P.k : ℕ) : ℤ) + o) + ((P.inf.N * degT Q : ℕ) : ℤ) : ℚ) =
          m * coord j (P.resInf wt)) := by
  classical
  intro wt hwt
  obtain ⟨w, hw, hsplit⟩ := S.certInfSys (K := K) P ψ₀ hSF hV
  have hlen : P.inf.ys.length = P.n := by
    have hc := hV.certInf
    simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.1.2
  obtain ⟨k, hk⟩ := S.index_of_mem P ψ₀ hSF hV P.inf.ys hlen wt hwt
  set N := P.inf.N
  set D := invDeg W P.k
  set ρ := w k with hρ
  have hwk := hw k
  rw [hk] at hwk
  refine ⟨ρ, hwk, ?_⟩
  set l : List (LaurentSeries K) := List.ofFn fun k ↦
    single (-((P.k * N : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K (w k) with hldef
  have hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod := by
    rw [hsplit, hldef, List.map_ofFn, List.prod_ofFn]; rfl
  have hrl : single (-((P.k * N : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K ρ ∈ l :=
    List.mem_ofFn.mpr ⟨k, rfl⟩
  have hr := S.root_of_mem hl hrl
  set WC := (toB W).map (mapRingHom ψ₀) with hWC
  have hval : ∀ z : PowerSeries K, (WC.map (infSub N)).eval
      (single (-((P.k * N : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K z) =
      single (-((N * D : ℕ) : ℤ)) (1 : K) *
        ofPowerSeries ℤ K (((toB (invB W P.k D)).map (thetaN ((algebraMap C K).comp ψ₀) 0 N)).eval z) :=
    fun z ↦ eval_invB (K := K) ψ₀ N hV.infN P.k D z W (invOK_invDeg W P.k)
  set V := ((toB (invB W P.k D)).map (thetaN ((algebraMap C K).comp ψ₀) 0 N)).eval ρ with hVdef
  have hWm : WC.natDegree ≤ W.length - 1 := natDegree_map_le.trans (natDegree_toB_le_len' W)
  have hne := S.branch_values_ne_zero WC hW0 _ (infSub_injective N hV.infN) l hl
    _ (List.mem_map.mpr ⟨_, hrl, rfl⟩)
  rw [hval] at hne
  have hV0 : V ≠ 0 := fun h ↦ hne (by
    rw [show ((toB (invB W P.k D)).map (thetaN ((algebraMap C K).comp ψ₀) 0 N)).eval ρ = V from rfl, h,
      map_zero, mul_zero])
  have hex0 : ∃ t, PowerSeries.coeff t V ≠ 0 := by
    by_contra h; push Not at h; exact hV0 (PowerSeries.ext fun t ↦ by rw [h t, map_zero])
  set o := Nat.find hex0 with ho
  have h1 : PowerSeries.coeff o V ≠ 0 := Nat.find_spec hex0
  have h0 : ∀ t < o, PowerSeries.coeff t V = 0 := fun t ht ↦ by
    by_contra h; exact Nat.find_min hex0 ht h
  have hordV : (ofPowerSeries ℤ K V).order = o := order_ofPS_eq V o h0 h1
  have hordS : ∀ z : PowerSeries K,
      (single (-((N * D : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K z) ≠ 0 →
      (single (-((N * D : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K z).order =
        -((N * D : ℕ) : ℤ) + (ofPowerSeries ℤ K z).order := fun z hz ↦ by
    have hz' : ofPowerSeries ℤ K z ≠ 0 := fun h ↦ hz (by rw [h, mul_zero])
    rw [HahnSeries.order_mul (single_ne_zero one_ne_zero) hz', order_single one_ne_zero]
  -- the order is below the precision
  have hsum := S.sum_order_inf WC (W.length - 1) hWm hW0 N hV.infN l hl
  have hnn : ∀ z ∈ l.map (fun r ↦ ((WC.map (infSub N)).eval r).order + ((N * D : ℕ) : ℤ)),
      0 ≤ z := by
    intro z hz
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hz
    obtain ⟨k', rfl⟩ := List.mem_ofFn.mp hr'
    rw [hval]
    by_cases h0' : single (-((N * D : ℕ) : ℤ)) (1 : K) *
        ofPowerSeries ℤ K (((toB (invB W P.k D)).map
          (thetaN ((algebraMap C K).comp ψ₀) 0 N)).eval (w k')) = 0
    · rw [h0', order_zero]; positivity
    · rw [hordS _ h0']
      linarith [order_ofPS_nonneg (((toB (invB W P.k D)).map
        (thetaN ((algebraMap C K).comp ψ₀) 0 N)).eval (w k'))]
  have hle := List.single_le_sum hnn _ (List.mem_map.mpr ⟨_, hrl, rfl⟩)
  have hsne : single (-((N * D : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K V ≠ 0 := hne
  rw [hval, hordS V hsne, hordV, list_sum_map_add', hsum] at hle
  have hln : l.length = P.n := by rw [hldef, List.length_ofFn, S.natDegree_F_eq P ψ₀ hSF hV]
  rw [hln] at hle
  have hlt : o < P.inf.prec := by
    have hdeg0 : (0 : ℤ) ≤ ((S.normW WC (W.length - 1)).natDegree : ℤ) := by positivity
    have hB' : ((P.n * (N * D) : ℕ) : ℤ) < P.inf.prec := by exact_mod_cast hB
    push_cast at hle hB'
    have : (o : ℤ) < P.inf.prec := by nlinarith
    exact_mod_cast this
  refine ⟨o, hlt, h0, h1, ?_⟩
  have hres := S.resInf_sem (K := K) P ψ₀ hSF hV.infN ρ hr wt hwk hV.sf
    hV.Dl hV.okA (S.fE P ψ₀) (S.fE_spec P ψ₀ hV)
  have hx := hex _ hr
  rw [hval, hordS V hsne, hordV] at hx
  rw [hres, RingHom.comp_apply, hΛ] at hx
  push_cast at hx ⊢
  exact hx

/-- **Theorem C: an exact divisor gives a passing witness** (precisions above the orders). -/
theorem witOK_of_exact (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) (W : BPoly F) (Q : CPoly F) (j : Fin (dim F)) (m : ℕ) (hm : 0 < m)
    (Λ : K →ₗ[ℚ] ℚ) (hΛ : ∀ r : F, Λ (algebraMap C K (ψ₀ r)) = coord j r)
    (hW0 : S.evXY ((toB W).map (mapRingHom ψ₀)) ≠ 0) (hQ0 : toPoly Q ≠ 0)
    (hexF : ∀ ac ∈ P.pts, ∀ (hN : 0 < ac.2.N) (r : LaurentSeries K)
      (hr : (S.F.map (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))).eval r = 0),
      (((((toB W).map (mapRingHom ψ₀)).map (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))).eval r).order -
        (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)) ((toPoly Q).map ψ₀)).order : ℚ) =
        m * Λ (LaurentSeries.res (S.embG (branchSub ac.2.N (algebraMap C K (ψ₀ ac.1)))
          (branchSub_injective ac.2.N hN (algebraMap C K (ψ₀ ac.1))) r hr (S.fE P ψ₀) *
          LaurentSeries.derivation (HahnSeries.C (algebraMap C K (ψ₀ ac.1)) + single (ac.2.N : ℤ) (1 : K)))))
    (hexI : ∀ (r : LaurentSeries K) (hr : (S.F.map (infSub (K := K) P.inf.N)).eval r = 0),
      (((((toB W).map (mapRingHom ψ₀)).map (infSub P.inf.N)).eval r).order +
        ((P.inf.N * degT Q : ℕ) : ℤ) : ℚ) =
        m * Λ (LaurentSeries.res (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hV.infN) r hr
          (S.fE P ψ₀) * LaurentSeries.derivation (single (-(P.inf.N : ℤ)) (1 : K)))))
    (hnq : toPoly (mul (normRC P.Fc W P.n P.k) Q) ≠ 0)
    (hcov : ∀ z : K, ((toPoly (mul (normRC P.Fc W P.n P.k) Q)).map ((algebraMap C K).comp ψ₀)).eval z = 0 →
      ∃ a ∈ P.pts.map Prod.fst, z = (algebraMap C K).comp ψ₀ a)
    (hBF : ∀ ac ∈ P.pts, ac.2.N * (((S.normW ((toB W).map (mapRingHom ψ₀)) (W.length - 1)).map
      (algebraMap C K)).rootMultiplicity (algebraMap C K (ψ₀ ac.1))) < ac.2.prec)
    (hBI : P.n * (P.inf.N * invDeg W P.k) < P.inf.prec) :
    P.witOK ⟨m, W, Q⟩ j = true :=
  witOK_of_orders ((algebraMap C K).comp ψ₀) P ⟨m, W, Q⟩ j hm hQ0
    (S.fin_facts P ψ₀ hSF hV W Q j m Λ hΛ hW0 hQ0 hexF hBF)
    (S.inf_facts P ψ₀ hSF hV W Q j m Λ hΛ hW0 hexI hBI)
    (coverCheck_complete _ _ hnq _ hcov)

end CurveData

end Facts

end Curves
