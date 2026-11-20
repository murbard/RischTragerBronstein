import RischTragerBronstein.Curves.ProcRFSound3

/-!
# Rows versus simple poles along all branches

For `v = ∑ c_b b` in the ansatz space:

* `rows_of_simple`: if `φ(f) dX̂ − d(φ v)` has at most simple poles along every branch, then
  `c` satisfies every row of the linear system;
* `simpleFin_all`, `simpleInf_all`: conversely, a solution of the rows gives at most simple poles
  along *every* branch of *every* branch system (special points via the certified systems and
  `transfer_diff`, other points by regularity);
* `resFin_all`, `resInf_all`: if all computed residues vanish, then the residues of `f dx` vanish
  along every branch.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

section Rows

variable {F : Type*} [Field F] [DecidableEq F]

namespace CurveProb

variable (P : CurveProb F)

lemma mem_rowsFin (a : F) (c : BranchCert F) (yt : CPoly F) (r : List F × F) :
    r ∈ P.rowsFin a c yt ↔ ∃ j, P.jminFin a c ≤ j ∧ j ≤ -2 ∧ r = P.rowFinAt a c yt j := by
  simp only [rowsFin, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [List.bind_eq_flatMap, List.pure_def, List.mem_flatMap, List.mem_range,
      List.mem_singleton] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact ⟨P.jminFin a c + s, by omega, by omega, rfl⟩
  · rintro ⟨j, h1, h2, rfl⟩
    refine ⟨j - P.jminFin a c, ?_, by congr 1; ring⟩
    simp only [List.bind_eq_flatMap, List.pure_def, List.mem_flatMap, List.mem_range,
      List.mem_singleton]
    exact ⟨(j - P.jminFin a c).toNat, by omega, by omega⟩

lemma mem_rowsInf (wt : CPoly F) (r : List F × F) :
    r ∈ P.rowsInf wt ↔ ∃ j, P.jminInf ≤ j ∧ j ≤ -2 ∧ r = P.rowInfAt wt j := by
  simp only [rowsInf, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [List.bind_eq_flatMap, List.pure_def, List.mem_flatMap, List.mem_range,
      List.mem_singleton] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact ⟨P.jminInf + s, by omega, by omega, rfl⟩
  · rintro ⟨j, h1, h2, rfl⟩
    refine ⟨j - P.jminInf, ?_, by congr 1; ring⟩
    simp only [List.bind_eq_flatMap, List.pure_def, List.mem_flatMap, List.mem_range,
      List.mem_singleton]
    exact ⟨(j - P.jminInf).toNat, by omega, by omega⟩

lemma rowFin_mem_allRows {a : F} {c : BranchCert F} (hac : (a, c) ∈ P.pts) {yt : CPoly F}
    (hyt : yt ∈ c.ys) {j : ℤ} (h1 : P.jminFin a c ≤ j) (h2 : j ≤ -2) :
    P.rowFinAt a c yt j ∈ P.allRows :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨(a, c), hac,
    List.mem_flatMap.mpr ⟨yt, hyt, (P.mem_rowsFin a c yt _).mpr ⟨j, h1, h2, rfl⟩⟩⟩)

lemma rowInf_mem_allRows {wt : CPoly F} (hwt : wt ∈ P.inf.ys) {j : ℤ} (h1 : P.jminInf ≤ j)
    (h2 : j ≤ -2) : P.rowInfAt wt j ∈ P.allRows :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨wt, hwt,
    (P.mem_rowsInf wt _).mpr ⟨j, h1, h2, rfl⟩⟩)

lemma length_ys_of_cert {Fc : BPoly F} {n : ℕ} {a : F} {c : BranchCert F}
    (h : certCheck Fc n a c = true) : c.ys.length = n ∧ 0 < c.N := by
  simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.1.1.1⟩

end CurveProb

end Rows

section Sys

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L] [Field K]
  [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma natDegree_F_eq (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) : S.F.natDegree = P.n := by
  rw [hSF, natDegree_map_eq_of_injective (Polynomial.map_injective _ ψ₀.injective), hV.deg]

/-- The certified system above a special point, indexed by `Fin (deg F)`. -/
lemma certFinSys (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) (a : F) (c : BranchCert F) (hac : (a, c) ∈ P.pts) :
    ∃ y : Fin S.F.natDegree → PowerSeries K,
      (∀ k, (PowerSeries.X : PowerSeries K) ^ c.prec ∣
        y k - thetaT ((algebraMap C K).comp ψ₀) (toPoly (c.ys.getD k []))) ∧
      S.F.map (branchSub c.N (algebraMap C K (ψ₀ a))) =
        ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ K (y k))) := by
  obtain ⟨y, hy, -, hs⟩ := certCheck_spec (K := K) P.Fc P.n hV.mon hV.deg a c (hV.certs _ hac) ψ₀
  have hn := S.natDegree_F_eq P ψ₀ hSF hV
  refine ⟨fun k ↦ y (Fin.cast hn k), fun k ↦ hy _, ?_⟩
  refine (congrArg (Polynomial.map _) hSF).trans ?_
  rw [hs]
  exact (Fintype.prod_equiv (finCongr hn) _ _ (fun k ↦ rfl)).symm

/-- The certified system above infinity, indexed by `Fin (deg F)`. -/
lemma certInfSys (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) :
    ∃ w : Fin S.F.natDegree → PowerSeries K,
      (∀ k, (PowerSeries.X : PowerSeries K) ^ P.inf.prec ∣
        w k - thetaT ((algebraMap C K).comp ψ₀) (toPoly (P.inf.ys.getD k []))) ∧
      S.F.map (infSub P.inf.N) =
        ∏ k, (X - Polynomial.C (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (w k))) := by
  obtain ⟨w, hw, hs⟩ := certInf_spec (K := K) P.Fc P.n hV.mon hV.deg P.k hV.okF hV.mon' hV.deg'
    P.inf hV.certInf ψ₀
  have hn := S.natDegree_F_eq P ψ₀ hSF hV
  refine ⟨fun k ↦ w (Fin.cast hn k), fun k ↦ hw _, ?_⟩
  refine (congrArg (Polynomial.map _) hSF).trans ?_
  rw [hs]
  exact (Fintype.prod_equiv (finCongr hn) _ _ (fun k ↦ rfl)).symm

lemma index_of_mem (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) (ys : List (CPoly F)) (hl : ys.length = P.n) (yt : CPoly F)
    (hyt : yt ∈ ys) : ∃ k : Fin S.F.natDegree, ys.getD k [] = yt := by
  have hn := S.natDegree_F_eq P ψ₀ hSF hV
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hyt
  exact ⟨⟨i, by omega⟩, List.getD_eq_getElem _ _ hi⟩

lemma getD_mem_ys (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts) (ys : List (CPoly F)) (hl : ys.length = P.n) (k : Fin S.F.natDegree) :
    ys.getD k [] ∈ ys := by
  have hn := S.natDegree_F_eq P ψ₀ hSF hV
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

variable (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
  (hV : P.ValidFacts) (f : C⟮S.x⟯⟮S.y⟯)
  (hf : (f : L) * aeval S.x ((toPoly P.D).map ψ₀) = S.evXY ((toB P.A).map (mapRingHom ψ₀)))
  (bE : ℕ × ℕ → C⟮S.x⟯⟮S.y⟯)
  (hbE : ∀ ie, (bE ie : L) * aeval S.x ((toPoly P.R0).map ψ₀) =
    S.evXY ((toB (basisB ie.1 ie.2)).map (mapRingHom ψ₀)))
  (cv : ℕ → C)

include hSF hV hf hbE in
/-- **Simple poles everywhere ⇒ the rows hold.** -/
theorem rows_of_simple
    (hsimF : ∀ (a : K) (N : ℕ) (hN : 0 < N) (Y : LaurentSeries K)
      (hY : (S.F.map (branchSub N a)).eval Y = 0),
      LowerBd (S.embG (branchSub N a) (branchSub_injective N hN a) Y hY f *
          LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K)) -
        LaurentSeries.derivation (S.embG (branchSub N a) (branchSub_injective N hN a) Y hY
          (∑ b ∈ Finset.range P.basisIdx.length,
            S.cst (cv b) * bE (P.basisIdx.getD b (0, 0))))) (-1))
    (hsimI : ∀ (N : ℕ) (hN : 0 < N) (Y : LaurentSeries K)
      (hY : (S.F.map (infSub N)).eval Y = 0),
      LowerBd (S.embG (infSub N) (infSub_injective N hN) Y hY f *
          LaurentSeries.derivation (single (-(N : ℤ)) (1 : K)) -
        LaurentSeries.derivation (S.embG (infSub N) (infSub_injective N hN) Y hY
          (∑ b ∈ Finset.range P.basisIdx.length,
            S.cst (cv b) * bE (P.basisIdx.getD b (0, 0))))) (-1)) :
    ∀ r ∈ P.allRows, ∑ b ∈ Finset.range P.basisIdx.length, cv b * ψ₀ (r.1.getD b 0) = ψ₀ r.2 := by
  intro r hr
  simp only [CurveProb.allRows, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ⟨⟨a, c⟩, hac, yt, hyt, hr⟩ | ⟨wt, hwt, hr⟩
  · obtain ⟨j, hj1, hj2, rfl⟩ := (P.mem_rowsFin a c yt r).mp hr
    obtain ⟨hl, hN⟩ := CurveProb.length_ys_of_cert (hV.certs _ hac)
    obtain ⟨k, rfl⟩ := S.index_of_mem P ψ₀ hSF hV c.ys hl yt hyt
    obtain ⟨y, hy, hs⟩ := S.certFinSys (K := K) P ψ₀ hSF hV a c hac
    exact S.rowFin_of_simple P ψ₀ hSF a c hN (y k) (S.root_of_split _ _ hs k) _ (hy k)
      (hV.prec _ hac) f hf bE hbE cv (hsimF _ c.N hN _ _) j hj1 hj2
  · obtain ⟨j, hj1, hj2, rfl⟩ := (P.mem_rowsInf wt r).mp hr
    obtain ⟨hl, -⟩ := CurveProb.length_ys_of_cert hV.certInf
    obtain ⟨k, rfl⟩ := S.index_of_mem P ψ₀ hSF hV P.inf.ys hl wt hwt
    obtain ⟨w, hw, hs⟩ := S.certInfSys (K := K) P ψ₀ hSF hV
    exact S.rowInf_of_simple P ψ₀ hSF hV.infN (w k) (S.root_of_split _ _ hs k) _ (hw k)
      hV.sb hV.sf hV.R0l hV.Dl hV.okA (P.okB hV.n_pos) f hf bE hbE cv
      (hsimI _ hV.infN _ _) j hj2

omit [CharZero K] in
lemma toPoly_R0 : toPoly P.R0 = toPoly (discRC P.Fc P.n P.k) * toPoly P.D := by
  rw [CurveProb.R0, toPoly_trim, toPoly_mul]

include hSF hV in
/-- Away from the special points, `φ(z) ≥ 0` for `z = W/Q` with `Q | D · discR`. -/
lemma lb_regular (Q : CPoly F) (hQ : toPoly Q ∣ toPoly (mul P.D (discRC P.Fc P.n P.k)))
    (hQ0 : toPoly Q ≠ 0) (z : C⟮S.x⟯⟮S.y⟯) (W : BPoly F)
    (hz : (z : L) * aeval S.x ((toPoly Q).map ψ₀) = S.evXY ((toB W).map (mapRingHom ψ₀)))
    (a : K) (hsp : ((toPoly (mul P.D (discRC P.Fc P.n P.k))).map
      ((algebraMap C K).comp ψ₀)).eval a ≠ 0)
    (N : ℕ) (hN : 0 < N) (Y : LaurentSeries K) (hY : (S.F.map (branchSub N a)).eval Y = 0) :
    LowerBd (S.embG (branchSub N a) (branchSub_injective N hN a) Y hY z) 0 := by
  have hQ0' : (toPoly Q).map ψ₀ ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff ψ₀.injective]
  have h := S.lowerBd_fin N hN a Y hY z _ _ hQ0' hz
  have hnr : ¬ (((toPoly Q).map ψ₀).map (algebraMap C K)).IsRoot a := by
    intro hr
    apply hsp
    obtain ⟨q, hq⟩ := hQ
    rw [hq, Polynomial.map_mul, eval_mul, ← Polynomial.map_map]
    rw [IsRoot.def] at hr
    rw [hr, zero_mul]
  rwa [rootMultiplicity_eq_zero hnr, mul_zero, Nat.cast_zero, neg_zero] at h

include hSF hV hf hbE in
/-- **Rows ⇒ simple poles along every finite branch.** -/
theorem simpleFin_all
    (hrows : ∀ r ∈ P.allRows, ∑ b ∈ Finset.range P.basisIdx.length, cv b * ψ₀ (r.1.getD b 0) =
      ψ₀ r.2)
    (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx : x ∈ l) :
    LowerBd (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) x
        (S.root_of_mem hl hx) f *
        LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K)) -
      LaurentSeries.derivation (S.embG (branchSub N a)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) a) x (S.root_of_mem hl hx)
          (∑ b ∈ Finset.range P.basisIdx.length,
            S.cst (cv b) * bE (P.basisIdx.getD b (0, 0))))) (-1) := by
  by_cases hsp : ((toPoly (mul P.D (discRC P.Fc P.n P.k))).map
      ((algebraMap C K).comp ψ₀)).eval a = 0
  · obtain ⟨a0, ha0, hae⟩ := coverCheck_spec _ _ hV.cover ((algebraMap C K).comp ψ₀) a hsp
    obtain ⟨⟨a1, c⟩, hac, rfl⟩ := List.mem_map.mp ha0
    rw [RingHom.comp_apply] at hae
    subst hae
    obtain ⟨hl0, hN0⟩ := CurveProb.length_ys_of_cert (hV.certs _ hac)
    obtain ⟨y, hy, hs0⟩ := S.certFinSys (K := K) P ψ₀ hSF hV a1 c hac
    obtain ⟨k, hk⟩ := S.fin_rel_list _ c.N hN0 _ hs0 N hN l hl x hx
    refine transfer_diff c.N N hN0 (Nat.pos_of_ne_zero hN) _ _ _ _ _ _ (hk f) (hk _)
      (by rw [lsub_Xfin, lsub_Xfin, mul_comm]) ?_
    exact S.certFin_simple P ψ₀ hSF a1 c hN0 (y k) (S.root_of_split _ _ hs0 k) _ (hy k)
      (hV.prec _ hac) f hf bE hbE cv fun j hj1 hj2 ↦
        hrows _ (P.rowFin_mem_allRows hac (S.getD_mem_ys P ψ₀ hSF hV c.ys hl0 k) hj1 hj2)
  · have hN' := Nat.pos_of_ne_zero hN
    have hDd : toPoly P.D ∣ toPoly (mul P.D (discRC P.Fc P.n P.k)) :=
      ⟨_, toPoly_mul _ _⟩
    have hRd : toPoly P.R0 ∣ toPoly (mul P.D (discRC P.Fc P.n P.k)) :=
      ⟨1, by rw [toPoly_R0, toPoly_mul]; ring⟩
    have hR0 : toPoly P.R0 ≠ 0 := by
      rw [← toPoly_trim]
      intro h0
      have := (trim_eq_nil_iff (trim P.R0)).mpr h0
      rw [trim_trim] at this
      have := hV.R0l; simp_all
    have h1 := (S.lb_regular P ψ₀ hSF hV P.D hDd hV.D0 f P.A hf a hsp N hN' x
      (S.root_of_mem hl hx)).mul (lowerBd_single ((N : ℤ) - 1) (N : K))
    have h2 := (S.lb_lcomb _ (branchSub_injective N hN' a) (fun c' ↦ branchSub_C' _ _ c') x
      (S.root_of_mem hl hx) P.basisIdx.length cv (fun b ↦ bE (P.basisIdx.getD b (0, 0))) 0
      fun b _ ↦ S.lb_regular P ψ₀ hSF hV P.R0 hRd hR0 _ _ (hbE _) a hsp N hN' x
        (S.root_of_mem hl hx)).derivative
    rw [← LaurentSeries.derivation_apply] at h2
    rw [SuperData.derivation_branchX N hN']
    exact (h1.mono (by omega)).sub (h2.mono (by omega))

include hSF hV hf hbE in
/-- **Rows ⇒ simple poles along every branch above infinity.** -/
theorem simpleInf_all
    (hrows : ∀ r ∈ P.allRows, ∑ b ∈ Finset.range P.basisIdx.length, cv b * ψ₀ (r.1.getD b 0) =
      ψ₀ r.2)
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx : x ∈ l) :
    LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) x
        (S.root_of_mem hl hx) f *
        LaurentSeries.derivation (single (-(N : ℤ)) (1 : K)) -
      LaurentSeries.derivation (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) x
        (S.root_of_mem hl hx)
          (∑ b ∈ Finset.range P.basisIdx.length,
            S.cst (cv b) * bE (P.basisIdx.getD b (0, 0))))) (-1) := by
  obtain ⟨hl0, -⟩ := CurveProb.length_ys_of_cert hV.certInf
  obtain ⟨w, hw, hs0⟩ := S.certInfSys (K := K) P ψ₀ hSF hV
  obtain ⟨k, hk⟩ := S.inf_rel_list P.inf.N hV.infN _ hs0 N hN l hl x hx
  refine transfer_diff P.inf.N N hV.infN (Nat.pos_of_ne_zero hN) _ _ _ _ _ _ (hk f) (hk _)
    (by rw [lsub_Xinf, lsub_Xinf, mul_comm]) ?_
  exact S.certInf_simple P ψ₀ hSF hV.infN (w k) (S.root_of_split _ _ hs0 k) _ (hw k)
    hV.sb hV.sf hV.R0l hV.Dl hV.okA (P.okB hV.n_pos) f hf bE hbE cv fun j hj1 hj2 ↦
      hrows _ (P.rowInf_mem_allRows (S.getD_mem_ys P ψ₀ hSF hV P.inf.ys hl0 k) hj1 hj2)

include hSF hV hf in
/-- **Vanishing computed residues ⇒ vanishing residues along every finite branch.** -/
theorem resFin_all (hres : ∀ r ∈ P.allRes, r = 0)
    (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx : x ∈ l) :
    LaurentSeries.res (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) x
        (S.root_of_mem hl hx) f *
        LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K))) = 0 := by
  by_cases hsp : ((toPoly (mul P.D (discRC P.Fc P.n P.k))).map
      ((algebraMap C K).comp ψ₀)).eval a = 0
  · obtain ⟨a0, ha0, hae⟩ := coverCheck_spec _ _ hV.cover ((algebraMap C K).comp ψ₀) a hsp
    obtain ⟨⟨a1, c⟩, hac, rfl⟩ := List.mem_map.mp ha0
    rw [RingHom.comp_apply] at hae
    subst hae
    obtain ⟨hl0, hN0⟩ := CurveProb.length_ys_of_cert (hV.certs _ hac)
    obtain ⟨y, hy, hs0⟩ := S.certFinSys (K := K) P ψ₀ hSF hV a1 c hac
    obtain ⟨k, hk⟩ := S.fin_rel_list _ c.N hN0 _ hs0 N hN l hl x hx
    refine transfer_res0 c.N N hN0 (Nat.pos_of_ne_zero hN) _ _ _ _ (hk f)
      (by rw [lsub_Xfin, lsub_Xfin, mul_comm]) ?_
    obtain ⟨-, hμf, -, hQfl⟩ := hV.prec _ hac
    rw [S.resFin_sem P ψ₀ hSF a1 c hN0 (y k) (S.root_of_split _ _ hs0 k) _ (hy k) hμf hQfl f hf,
      hres _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨(a1, c), hac,
        List.mem_map.mpr ⟨_, S.getD_mem_ys P ψ₀ hSF hV c.ys hl0 k, rfl⟩⟩)), map_zero]
  · have hN' := Nat.pos_of_ne_zero hN
    have hDd : toPoly P.D ∣ toPoly (mul P.D (discRC P.Fc P.n P.k)) :=
      ⟨_, toPoly_mul _ _⟩
    have h1 := (S.lb_regular P ψ₀ hSF hV P.D hDd hV.D0 f P.A hf a hsp N hN' x
      (S.root_of_mem hl hx)).mul (lowerBd_single ((N : ℤ) - 1) (N : K))
    rw [SuperData.derivation_branchX N hN', LaurentSeries.res]
    exact h1 (-1) (by omega)

include hSF hV hf in
/-- **Vanishing computed residues ⇒ vanishing residues above infinity.** -/
theorem resInf_all (hres : ∀ r ∈ P.allRes, r = 0)
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx : x ∈ l) :
    LaurentSeries.res (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) x
        (S.root_of_mem hl hx) f *
        LaurentSeries.derivation (single (-(N : ℤ)) (1 : K))) = 0 := by
  obtain ⟨hl0, -⟩ := CurveProb.length_ys_of_cert hV.certInf
  obtain ⟨w, hw, hs0⟩ := S.certInfSys (K := K) P ψ₀ hSF hV
  obtain ⟨k, hk⟩ := S.inf_rel_list P.inf.N hV.infN _ hs0 N hN l hl x hx
  refine transfer_res0 P.inf.N N hV.infN (Nat.pos_of_ne_zero hN) _ _ _ _ (hk f)
    (by rw [lsub_Xinf, lsub_Xinf, mul_comm]) ?_
  rw [S.resInf_sem P ψ₀ hSF hV.infN (w k) (S.root_of_split _ _ hs0 k) _ (hw k) hV.sf hV.Dl
      hV.okA f hf,
    hres _ (List.mem_append_right _
      (List.mem_map.mpr ⟨_, S.getD_mem_ys P ψ₀ hSF hV P.inf.ys hl0 k, rfl⟩)), map_zero]

end CurveData

end Sys

end Curves
