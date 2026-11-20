import RischTragerBronstein.Mixed.MTRdeE
import RischTragerBronstein.Computable.NestXRdeED

/-!
# Mixed towers over a curve (`RdeED`)

Ported from `Tower.NestX` (`NestXRdeED`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

/-- A logarithm `(c, w)` of level `m + 1`, typed with pairs of polynomials. -/
abbrev LgXEC (m : ℕ) : Type :=
  (GPoly (LC m) × GPoly (LC m)) × (GPoly (LC m) × GPoly (LC m))

/-- A code of level `m + 1`, typed as a pair of polynomials. -/
abbrev PrXEC (m : ℕ) : Type := GPoly (LC m) × GPoly (LC m)


/-- The code `∑ vⱼ cⱼ` of `logBoundC`. -/
def codeXEC (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) (v : List ℤ)
    (logs : List (LgXEC m)) : LC (m + 1) :=
  (List.zip v logs).foldr (fun p acc2 ↦ (MO Fc ks (m + 1)).add ((MO Fc ks (m + 1)).mul
    (mcst Fc ks (m + 1) ((p.1 : ℤ) : ℚ)) p.2.1) acc2) (MO Fc ks (m + 1)).zero

lemma le_foldr_genXEC {β : Type*} (g : β → ℕ → ℕ) (hmono : ∀ v acc, acc ≤ g v acc) :
    ∀ (l : List β) (v : β), v ∈ l → ∀ k : ℕ, (∀ acc, k ≤ g v acc) → k ≤ l.foldr g 0
  | [], _, hv, _, _ => by simp at hv
  | w :: l, v, hv, k, hk => by
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hk _
    · exact (le_foldr_genXEC g hmono l v hv k hk).trans (hmono _ _)

/-- `∑ cⱼ ordₜ wⱼ`. -/
def sumOrdXEC (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) (logsC : List (LC m × PrXEC m)) :
    LC m :=
  logsC.foldr (fun cw acc ↦ (MO Fc ks m).add ((MO Fc ks m).mul cw.1
    (mcst Fc ks m (ordZ (MO Fc ks m) cw.2 : ℚ))) acc) (MO Fc ks m).zero

/-- `∑ cⱼ deg wⱼ`. -/
def sumDegXEC (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) (logsC : List (LC m × PrXEC m)) :
    LC m :=
  logsC.foldr (fun cw acc ↦ (MO Fc ks m).add ((MO Fc ks m).mul cw.1
    (mcst Fc ks m (degZ (MO Fc ks m) cw.2 : ℚ))) acc) (MO Fc ks m).zero

/-- The special bound `κ`. -/
def kapXEC (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) (a : LC m) (hc : PrXEC m) (eps : ℕ)
    (so : LC m) : ℕ :=
  if !GPoly.isZero (MO Fc ks m) hc.1 && decide (lowZ (MO Fc ks m) hc.1 < lowZ (MO Fc ks m) hc.2) then
    eps
  else match (pldC Fc ks m ((MO Fc ks m).neg (peH0 (MO Fc ks m) hc)) a), ratValC Fc ks m so with
    | some μ, some s => match natOfQ (μ + s) with
      | some k => max eps k
      | none => eps
    | _, _ => eps

/-- The normal denominator bound. -/
def DXEC (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) (Wc : List (PrXEC m))
    (logs : List (LgXEC m)) : GPoly (LC m) :=
  peDX (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) (peE (MO Fc ks m) Wc) (logPoly (MO Fc ks m) true logs)
    (logBoundC Fc ks m logs)

lemma eps_le_kapXEC (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) (a : LC m) (hc : PrXEC m)
    (eps : ℕ) (so : LC m) : eps ≤ kapXEC Fc ks m a hc eps so := by
  unfold kapXEC
  split
  · exact le_rfl
  · split
    · split
      · exact le_max_left _ _
      · exact le_rfl
    · exact le_rfl



namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]
variable (T : MTower Fc ks Cc L)


section Const

variable (m : ℕ) (h : T.Tr (m + 1))

/-- The leading-coefficient ratio of a constant of level `m + 1` is that constant. -/
lemma sem_lcC_constXE (q : PrXEC m) (κ : Cc)
    (hq : (T.M1X m h).sem q = algebraMap Cc (T.F (m + 1)) κ) :
    (T.MX m h).sem (lcC (MO Fc ks m) q) = algebraMap Cc (T.F m) κ := by
  rw [sem_lcC_XE]
  rw [T.semX] at hq
  by_cases hd : GPoly.toPoly (T.MX m h) q.2 = 0
  · rw [hd, leadingCoeff_zero, div_zero]
    rw [σX, σX, hd, map_zero, div_zero] at hq
    have : κ = 0 := (algebraMap Cc (T.F (m + 1))).injective (by rw [← hq, map_zero])
    rw [this, map_zero]
  · have hσd : T.σX m h q.2 ≠ 0 := by
      rw [σX, Ne, map_eq_zero_iff _ (T.phi_injX m h)]; exact hd
    have h1 : T.σX m h q.1 = T.phi m (C (algebraMap Cc (T.F m) κ)) * T.σX m h q.2 := by
      rw [← T.algebraMap_succ, ← hq]; field_simp
    have h2 : GPoly.toPoly (T.MX m h) q.1 = C (algebraMap Cc (T.F m) κ) * GPoly.toPoly (T.MX m h) q.2 :=
      T.phi_injX m h (by rw [map_mul]; exact h1)
    rw [h2, leadingCoeff_mul, leadingCoeff_C]
    field_simp [leadingCoeff_ne_zero.mpr hd]

/-- The constants of the logarithms of a valid `FRep`. -/
lemma exists_consts_XE (logs : List (LgXEC m))
    (hok : ∀ cw ∈ logs, ((T.M1X m h).sem cw.1)′ = 0) (d : LgXEC m) :
    ∃ κ : ℕ → Cc, ∀ i < logs.length,
      (T.M1X m h).sem (logs.getD i d).1 = algebraMap Cc (T.F (m + 1)) (κ i) := by
  have : ∀ i, ∃ κ : Cc, i < logs.length →
      (T.M1X m h).sem (logs.getD i d).1 = algebraMap Cc (T.F (m + 1)) κ := by
    intro i
    by_cases hi : i < logs.length
    · have hmem : logs.getD i d ∈ logs := by
        rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
      obtain ⟨κ, hκ⟩ := T.const_F _ (hok _ hmem)
      exact ⟨κ, fun _ ↦ hκ⟩
    · exact ⟨0, fun h' ↦ absurd h' hi⟩
  choose κ hκ using this
  exact ⟨κ, fun i hi ↦ hκ i hi⟩

/-- The numerator polynomial of a logarithm (`1` for a zero `w`). -/
noncomputable def NwXE (cw : LgXEC m) : (T.F m)[X] :=
  if nzXE (MO Fc ks m) cw then GPoly.toPoly (T.MX m h) cw.2.1 else 1

/-- The denominator polynomial of a logarithm (`1` for a zero `w`). -/
noncomputable def DwXE (cw : LgXEC m) : (T.F m)[X] :=
  if nzXE (MO Fc ks m) cw then GPoly.toPoly (T.MX m h) cw.2.2 else 1

/-- The part of the numerator prime to `t`. -/
noncomputable def N1XE (cw : LgXEC m) : (T.F m)[X] :=
  if nzXE (MO Fc ks m) cw then GPoly.toPoly (T.MX m h) (cw.2.1.drop (lowZ (MO Fc ks m) cw.2.1))
  else 1

/-- The part of the denominator prime to `t`. -/
noncomputable def D1XE (cw : LgXEC m) : (T.F m)[X] :=
  if nzXE (MO Fc ks m) cw then GPoly.toPoly (T.MX m h) (cw.2.2.drop (lowZ (MO Fc ks m) cw.2.2))
  else 1

lemma nz_iffXE (cw : LgXEC m) :
    nzXE (MO Fc ks m) cw = true ↔
      GPoly.toPoly (T.MX m h) cw.2.1 ≠ 0 ∧ GPoly.toPoly (T.MX m h) cw.2.2 ≠ 0 := by
  unfold nzXE
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true',
    ← Bool.not_eq_true, ← Bool.not_eq_true, GPoly.isZero_iff (T.MX m h),
    GPoly.isZero_iff (T.MX m h)]

lemma NwD_ne_XE (cw : LgXEC m) :
    T.NwXE m h cw ≠ 0 ∧ T.DwXE m h cw ≠ 0 := by
  unfold NwXE DwXE
  split_ifs with hnz
  · exact (T.nz_iffXE m h cw).mp hnz
  · exact ⟨one_ne_zero, one_ne_zero⟩

lemma Nw_splitXE (cw : LgXEC m) :
    T.NwXE m h cw = X ^ aNXE (MO Fc ks m) cw * T.N1XE m h cw ∧ ¬X ∣ T.N1XE m h cw := by
  unfold NwXE N1XE aNXE
  split_ifs with hnz
  · exact ⟨toPoly_lowZ _ _, not_X_dvd_drop_lowZ _ _ ((T.nz_iffXE m h cw).mp hnz).1⟩
  · exact ⟨by simp, fun h' ↦ not_isUnit_X (isUnit_of_dvd_one h')⟩

lemma Dw_splitXE (cw : LgXEC m) :
    T.DwXE m h cw = X ^ aDXE (MO Fc ks m) cw * T.D1XE m h cw ∧ ¬X ∣ T.D1XE m h cw := by
  unfold DwXE D1XE aDXE
  split_ifs with hnz
  · exact ⟨toPoly_lowZ _ _, not_X_dvd_drop_lowZ _ _ ((T.nz_iffXE m h cw).mp hnz).2⟩
  · exact ⟨by simp, fun h' ↦ not_isUnit_X (isUnit_of_dvd_one h')⟩

/-- The value of a logarithm, in terms of `NwXE`, `DwXE`. -/
lemma logDeriv_sem_XE (cw : LgXEC m) :
    logDeriv ((T.M1X m h).sem cw.2) = logDeriv (T.phi m (T.NwXE m h cw) / T.phi m (T.DwXE m h cw)) := by
  rw [T.semX]
  unfold NwXE DwXE
  split_ifs with hnz
  · rfl
  · have : T.σX m h cw.2.1 / T.σX m h cw.2.2 = 0 := by
      rw [T.nz_iffXE m h cw, not_and_or, not_not, not_not] at hnz
      rcases hnz with h1 | h1
      · rw [σX, h1, map_zero, zero_div]
      · rw [σX, σX, h1, map_zero, div_zero]
    rw [this, map_one, div_one]
    simp [logDeriv]

/-- **The logarithmic part in `F (m + 1)`**, as a sum over the logarithms. -/
lemma logSumV_eqXE (logs : List (LgXEC m)) (d : LgXEC m)
    (κ : ℕ → Cc) (hκ : ∀ i < logs.length,
      (T.M1X m h).sem (logs.getD i d).1 = algebraMap Cc (T.F (m + 1)) (κ i)) :
    logSumV (T.M1X m h) logs = ∑ i ∈ Finset.range logs.length,
      T.phi m (C (algebraMap Cc (T.F m) (κ i))) *
        logDeriv (T.phi m (T.NwXE m h (logs.getD i d)) / T.phi m (T.DwXE m h (logs.getD i d))) := by
  unfold logSumV
  rw [list_sum_map_getD_XE _ d]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [hκ i (Finset.mem_range.mp hi), T.algebraMap_succ, T.logDeriv_sem_XE]

lemma Nw_nzXE (cw : LgXEC m) (hnz : nzXE (MO Fc ks m) cw = true) :
    T.N1XE m h cw = GPoly.toPoly (T.MX m h) (nrmP (MO Fc ks m) true cw.2.1) := by
  rw [toPoly_nrmP_XE _ _ ((T.nz_iffXE m h cw).mp hnz).1]
  exact if_pos hnz

lemma Dw_nzXE (cw : LgXEC m) (hnz : nzXE (MO Fc ks m) cw = true) :
    T.D1XE m h cw = GPoly.toPoly (T.MX m h) (nrmP (MO Fc ks m) true cw.2.2) := by
  rw [toPoly_nrmP_XE _ _ ((T.nz_iffXE m h cw).mp hnz).2]
  exact if_pos hnz

lemma NwDw_not_nzXE (cw : LgXEC m) (hnz : ¬nzXE (MO Fc ks m) cw = true) :
    T.NwXE m h cw = 1 ∧ T.DwXE m h cw = 1 := by
  unfold NwXE DwXE
  simp [hnz]

/-- A prime other than `t` dividing a logarithm divides `logPoly`. -/
lemma dvd_logPolyXE (logs : List (LgXEC m)) (cw : LgXEC m)
    (hcw : cw ∈ logs) (p : (T.F m)[X]) (hp : Irreducible p) (hXp : ¬X ∣ p)
    (hdvd : p ∣ T.NwXE m h cw * T.DwXE m h cw) :
    p ∣ GPoly.toPoly (T.MX m h) (logPoly (MO Fc ks m) true logs) := by
  have hL := dvd_logPoly_XE (T.MX m h) logs cw hcw
  have hpX : ∀ u : ℕ, ¬p ∣ X ^ u := fun u h' ↦
    hXp (hp.dvd_symm irreducible_X (hp.prime.dvd_of_dvd_pow h'))
  by_cases hnz : nzXE (MO Fc ks m) cw = true
  · rw [← T.Nw_nzXE m h cw hnz, ← T.Dw_nzXE m h cw hnz] at hL
    rw [(T.Nw_splitXE m h cw).1, (T.Dw_splitXE m h cw).1] at hdvd
    refine dvd_trans ?_ hL
    rcases hp.prime.dvd_or_dvd hdvd with h1 | h1
    · rcases hp.prime.dvd_or_dvd h1 with h2 | h2
      · exact absurd h2 (hpX _)
      · exact dvd_mul_of_dvd_left h2 _
    · rcases hp.prime.dvd_or_dvd h1 with h2 | h2
      · exact absurd h2 (hpX _)
      · exact dvd_mul_of_dvd_right h2 _
  · obtain ⟨h1, h2⟩ := T.NwDw_not_nzXE m h cw hnz
    rw [h1, h2, one_mul] at hdvd
    exact absurd (isUnit_of_dvd_one hdvd) hp.not_isUnit

/-- **The bound `N = logBoundC`** on the positive integer residues of the logarithmic part. -/
lemma logBound_geXE (logs : List (LgXEC m)) (d : LgXEC m)
    (κ : ℕ → Cc) (hκ : ∀ i < logs.length,
      (T.M1X m h).sem (logs.getD i d).1 = algebraMap Cc (T.F (m + 1)) (κ i))
    (k : ℕ) (n : ℕ → ℤ)
    (hn : ∀ i ∈ Finset.range logs.length, |n i| ≤ (((T.NwXE m h (logs.getD i d)).natDegree +
      (T.DwXE m h (logs.getD i d)).natDegree : ℕ) : ℤ))
    (hkn : (k : T.F m) = ∑ i ∈ Finset.range logs.length,
      algebraMap Cc (T.F m) (κ i) * (n i : T.F m)) :
    k ≤ logBoundC Fc ks m logs := by
  set v := (List.range logs.length).map n with hv
  have hvl : v.length = logs.length := by simp [hv]
  have hvg : ∀ j < logs.length, v.getD j 0 = n j := fun j hj ↦ NestTower.getD_range_map _ _ hj
  set ds := logs.map fun cw ↦ degG (MO Fc ks m) cw.2.1 + degG (MO Fc ks m) cw.2.2 with hds
  have hmem : v ∈ intVecs ds := by
    refine mem_intVecs ds v (by rw [hvl, hds, List.length_map]) fun j hj ↦ ?_
    have hj' : j < logs.length := by simpa [hds] using hj
    rw [hvg j hj', hds, NestTower.getD_map' _ _ d _ hj']
    refine (hn j (Finset.mem_range.mpr hj')).trans ?_
    have e1 : (T.NwXE m h (logs.getD j d)).natDegree ≤ degG (MO Fc ks m) (logs.getD j d).2.1 := by
      unfold NwXE; split_ifs
      · rw [degG_eq (T.MX m h)]
      · simp
    have e2 : (T.DwXE m h (logs.getD j d)).natDegree ≤ degG (MO Fc ks m) (logs.getD j d).2.2 := by
      unfold DwXE; split_ifs
      · rw [degG_eq (T.MX m h)]
      · simp
    push_cast
    omega
  -- the value of the code
  have hcode : (T.MP (m + 1) h).sem (codeXEC Fc ks m v logs) = ((k : ℚ) : T.F (m + 1)) := by
    unfold codeXEC
    refine (sem_zip_foldr_XE (T.MP (m + 1) h) (mcst Fc ks (m + 1)) (T.sem_mcst (m + 1) h) d v logs
      hvl).trans ?_
    have hk' := congrArg (fun z : T.F m ↦ T.phi m (C z)) hkn
    simp only [map_natCast, map_sum, map_mul, map_intCast] at hk'
    rw [show ((k : ℚ) : T.F (m + 1)) = (k : T.F (m + 1)) by push_cast; rfl, hk']
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    rw [hvg j hj', ← T.algebraMap_succ, ← hκ j hj']
    exact mul_comm _ _
  have hrat := T.ratVal_spec (m + 1) h _ _ hcode
  unfold logBoundC
  refine le_foldr_genXEC _ (fun w acc ↦ ?_) _ v hmem k (fun acc ↦ ?_)
  · simp only
    split
    · exact le_max_left _ _
    · exact le_rfl
  · simp only
    split
    · next q hq =>
      have hqk : q = (k : ℚ) := Option.some.inj (hq.symm.trans hrat)
      rw [hqk, natOfQ_natCast]
      exact le_max_right _ _
    · next hq => exact absurd (hq.symm.trans hrat) (by simp)

/-- The value of `∑ cⱼ ordₜ wⱼ`. -/
lemma sem_sumOrdXE (logs : List (LgXEC m)) (d : LgXEC m)
    (κ : ℕ → Cc) (hκ : ∀ i < logs.length,
      (T.M1X m h).sem (logs.getD i d).1 = algebraMap Cc (T.F (m + 1)) (κ i)) :
    (T.MX m h).sem (sumOrdXEC Fc ks m (logsCXE (MO Fc ks m) logs)) = ∑ i ∈ Finset.range logs.length,
      algebraMap Cc (T.F m) (κ i) *
        ((aNXE (MO Fc ks m) (logs.getD i d) : T.F m) - aDXE (MO Fc ks m) (logs.getD i d)) := by
  unfold sumOrdXEC logsCXE
  rw [List.foldr_map]
  have := sem_foldr_filter_XE (T.MX m h) (mcst Fc ks m) (T.sem_cstX m h)
    (fun cw : LgXEC m ↦ !GPoly.isZero (MO Fc ks m) cw.2.1 &&
      !GPoly.isZero (MO Fc ks m) cw.2.2)
    (fun cw ↦ lcC (MO Fc ks m) cw.1) (fun cw ↦ (ordZ (MO Fc ks m) cw.2 : ℚ)) d logs
  simp only at this ⊢
  rw [this]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hnzd : nzXE (MO Fc ks m) (logs.getD i d) = (!GPoly.isZero (MO Fc ks m) (logs.getD i d).2.1 &&
      !GPoly.isZero (MO Fc ks m) (logs.getD i d).2.2) := rfl
  unfold aNXE aDXE
  rw [hnzd]
  split_ifs with hnz
  · rw [T.sem_lcC_constXE m h _ (κ i) (hκ i (Finset.mem_range.mp hi)), ordZ]
    push_cast
    ring
  · simp

end Const

section Pld

variable (m : ℕ) (hM : T.MixHyp (m + 1)) {a : LC m}

/-- `pldX_spec`, stated in `F m`. -/
lemma pldX_specF_XE
    (hc2 : ∀ u ∈ mrel Fc ks m ((MO Fc ks m).deriv a :: gensDC Fc ks m), u.getD 0 0 = 0)
    (V : LC m) (μ : Cc) {ι : Type} (s : Finset ι) (c : ι → Cc) (u : ι → T.F m)
    (hu : ∀ i ∈ s, u i ≠ 0)
    (hd : ((T.MX m hM.tr).sem V + algebraMap Cc (T.F m) μ * (T.MX m hM.tr).sem a)′ =
      ∑ i ∈ s, algebraMap Cc (T.F m) (c i) * logDeriv (u i)) :
    ∃ q : ℚ, pldC Fc ks m V a = some q ∧ μ = (q : Cc) := by
  refine T.pldX_spec m hM.mono hc2 V μ s c (fun i ↦ (u i : L))
    (fun i hi ↦ ⟨(u i).2, fun h0 ↦ hu i hi (Subtype.ext h0)⟩) ?_
  have := congrArg (fun z : T.F m ↦ (z : L)) hd
  simp only [coe_deriv, IntermediateField.coe_add, IntermediateField.coe_mul,
    AddSubmonoidClass.coe_finset_sum, T.coe_logDeriv_FX] at this
  rw [← T.sem_MP m hM.mono.tr V, ← T.sem_MP m hM.mono.tr a]
  convert this using 2 <;> rfl

end Pld

section Hno

variable (m : ℕ) (hM : T.MixHyp (m + 1)) {a : LC m} (hk : ks m = .exp a)

include hk in
set_option maxHeartbeats 1600000 in
/-- **No cancellation beyond `κ` at `t = 0`** (`h` regular at `t`): the structure theorem. -/
lemma hno_XE (hc2 : ∀ u ∈ mrel Fc ks m ((MO Fc ks m).deriv a :: gensDC Fc ks m), u.getD 0 0 = 0)
    (logs : List (LgXEC m)) (d : LgXEC m) (κ : ℕ → Cc)
    (hκ : ∀ i < logs.length,
      (T.M1X m hM.tr).sem (logs.getD i d).1 = algebraMap Cc (T.F (m + 1)) (κ i))
    (hc : PrXEC m) (eps : ℕ)
    (hB : ¬((!GPoly.isZero (MO Fc ks m) hc.1 &&
      decide (lowZ (MO Fc ks m) hc.1 < lowZ (MO Fc ks m) hc.2)) = true))
    (k : ℕ) (hk' : kapXEC Fc ks m a hc eps (sumOrdXEC Fc ks m (logsCXE (MO Fc ks m) logs)) < k)
    (e : T.F m) (he : e ≠ 0) :
    e′ + (((T.MX m hM.tr).sem (peH0 (MO Fc ks m) hc))′ +
      ∑ i ∈ Finset.range logs.length, algebraMap Cc (T.F m) (κ i) *
        (((aNXE (MO Fc ks m) (logs.getD i d) : T.F m) - aDXE (MO Fc ks m) (logs.getD i d)) *
          T.bX m hM.tr a + ((T.N1XE m hM.tr (logs.getD i d)).coeff 0)′ /
            (T.N1XE m hM.tr (logs.getD i d)).coeff 0 -
          ((T.D1XE m hM.tr (logs.getD i d)).coeff 0)′ / (T.D1XE m hM.tr (logs.getD i d)).coeff 0) -
        k * T.bX m hM.tr a) * e ≠ 0 := by
  classical
  intro h0
  set h := hM.tr with hh
  set len := logs.length with hlen
  set b := T.bX m h a with hb
  set α := (T.MX m h).sem a with hα
  set h0v := (T.MX m h).sem (peH0 (MO Fc ks m) hc) with hh0v
  set cK : ℕ → T.F m := fun i ↦ algebraMap Cc (T.F m) (κ i) with hcK
  set n1 : ℕ → T.F m := fun i ↦ (T.N1XE m h (logs.getD i d)).coeff 0 with hn1
  set d1 : ℕ → T.F m := fun i ↦ (T.D1XE m h (logs.getD i d)).coeff 0 with hd1
  have hn10 : ∀ i, n1 i ≠ 0 := fun i h' ↦ (T.Nw_splitXE m h (logs.getD i d)).2 (X_dvd_iff.mpr h')
  have hd10 : ∀ i, d1 i ≠ 0 := fun i h' ↦ (T.Dw_splitXE m h (logs.getD i d)).2 (X_dvd_iff.mpr h')
  set so : Cc := ∑ i ∈ Finset.range len, κ i *
    ((aNXE (MO Fc ks m) (logs.getD i d) : Cc) - aDXE (MO Fc ks m) (logs.getD i d)) with hso
  have hsoF : algebraMap Cc (T.F m) so = ∑ i ∈ Finset.range len, cK i *
      ((aNXE (MO Fc ks m) (logs.getD i d) : T.F m) - aDXE (MO Fc ks m) (logs.getD i d)) := by
    simp [hso, hcK, map_sum, map_mul, map_sub, map_natCast]
  have hK0 : ∀ c : Cc, (algebraMap Cc (T.F m) c)′ = 0 := fun c ↦ T.deriv_algebraMap_Cc c
  set r0 := ∑ i ∈ Finset.range len, cK i *
      (((aNXE (MO Fc ks m) (logs.getD i d) : T.F m) - aDXE (MO Fc ks m) (logs.getD i d)) * b +
        (n1 i)′ / n1 i - (d1 i)′ / d1 i) with hr0
  have hr0' : r0 = algebraMap Cc (T.F m) so * b + ∑ i ∈ Finset.range len, cK i * logDeriv (n1 i) -
      ∑ i ∈ Finset.range len, cK i * logDeriv (d1 i) := by
    rw [hsoF, Finset.sum_mul, hr0, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    unfold logDeriv
    ring
  have hle : logDeriv e = -(h0v′ + r0 - k * b) := by
    rw [logDeriv, div_eq_iff he]; linear_combination h0
  -- the logarithmic-derivative identity
  set s' : Finset (Option (Bool × ℕ)) :=
    Finset.insertNone (Finset.univ ×ˢ Finset.range len) with hs'
  set c' : Option (Bool × ℕ) → Cc := fun j ↦ match j with
    | none => 1
    | some (true, i) => κ i
    | some (false, i) => -κ i with hc'
  set u' : Option (Bool × ℕ) → T.F m := fun j ↦ match j with
    | none => e
    | some (true, i) => n1 i
    | some (false, i) => d1 i with hu'
  have hsum : ∑ j ∈ s', algebraMap Cc (T.F m) (c' j) * logDeriv (u' j) =
      logDeriv e + ∑ i ∈ Finset.range len, cK i * logDeriv (n1 i) -
        ∑ i ∈ Finset.range len, cK i * logDeriv (d1 i) := by
    rw [hs', Finset.sum_insertNone, Finset.sum_product, Fintype.sum_bool]
    simp only [hc', hu', map_one, one_mul, map_neg, neg_mul, Finset.sum_neg_distrib, hcK]
    ring
  obtain ⟨q, hpl, hμ⟩ := T.pldX_specF_XE m hM hc2 ((MO Fc ks m).neg (peH0 (MO Fc ks m) hc))
    ((k : Cc) - so) s' c' u' (fun j _ ↦ by
      rcases j with _ | ⟨_ | _, i⟩
      · exact he
      · exact hd10 i
      · exact hn10 i) (by
      rw [hsum, (T.MX m h).sem_neg, ← hh0v, ← hα, map_add, map_neg, Derivation.leibniz,
        hK0, smul_zero, add_zero, smul_eq_mul, hle, hr0', map_sub, map_natCast]
      change -h0v′ + ((k : T.F m) - algebraMap Cc (T.F m) so) * b = _
      ring)
  -- the value of `∑ cⱼ ordₜ wⱼ` is rational
  have hsoq : algebraMap Cc (T.F m) so = (((k : ℚ) - q : ℚ) : T.F m) := by
    have : so = (k : Cc) - (q : Cc) := by rw [← hμ]; ring
    rw [this, map_sub, map_natCast, map_ratCast]
    push_cast; ring
  have hrv := T.ratVal_spec m hM.mono.tr (sumOrdXEC Fc ks m (logsCXE (MO Fc ks m) logs)) ((k : ℚ) - q)
    (by rw [← hsoq, hsoF]; exact T.sem_sumOrdXE m h logs d κ hκ)
  unfold kapXEC at hk'
  rw [if_neg hB, hpl, hrv] at hk'
  simp only at hk'
  rw [show q + ((k : ℚ) - q) = ((k : ℕ) : ℚ) by ring, natOfQ_natCast] at hk'
  exact absurd hk' (not_lt.mpr (le_max_right _ _))

end Hno

section Denominator

variable (m : ℕ) (h : T.Tr (m + 1))

/-- The normal part of the common denominator: non-zero, a multiple of every normal
denominator. -/
lemma peE_specXE (Wc : List (PrXEC m)) (hWc : ∀ q ∈ Wc, GPoly.toPoly (T.MX m h) q.2 ≠ 0) :
    GPoly.toPoly (T.MX m h) (peE (MO Fc ks m) Wc) ≠ 0 ∧
      (∀ q ∈ Wc, GPoly.toPoly (T.MX m h) (q.2.drop (lowZ (MO Fc ks m) q.2)) ∣
        GPoly.toPoly (T.MX m h) (peE (MO Fc ks m) Wc)) := by
  have hne : ∀ p ∈ Wc.map fun q ↦ q.2.drop (lowZ (MO Fc ks m) q.2),
      GPoly.toPoly (T.MX m h) p ≠ 0 := fun p hp ↦ by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    intro h0
    apply hWc q hq
    rw [toPoly_lowZ (T.MX m h) q.2, h0, mul_zero]
  obtain ⟨hdvd, hne0, -⟩ := GPolyLcm.lcmList_spec (T.MX m h) _ hne
  exact ⟨hne0, fun q hq ↦ hdvd _ (List.mem_map.mpr ⟨q, hq, rfl⟩)⟩

/-- The normal denominator bound `D` is non-zero, monic, and `C lc⁻¹ · gcd(e, e′) Lᴺ`. -/
lemma DXE_spec (Wc : List (PrXEC m)) (logs : List (LgXEC m))
    (he : GPoly.toPoly (T.MX m h) (peE (MO Fc ks m) Wc) ≠ 0) :
    ∃ u : T.F m, GPoly.toPoly (T.MX m h) (DXEC Fc ks m Wc logs) =
      C u * (GPoly.toPoly (T.MX m h) (GPoly.egcd (MO Fc ks m) (peE (MO Fc ks m) Wc)
        (GPoly.derivT (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) (peE (MO Fc ks m) Wc))).1 *
        GPoly.toPoly (T.MX m h) (logPoly (MO Fc ks m) true logs) ^ logBoundC Fc ks m logs) ∧
      (GPoly.toPoly (T.MX m h) (DXEC Fc ks m Wc logs)).Monic := by
  set O := MO Fc ks m
  set g := (GPoly.egcd O (peE O Wc) (GPoly.derivT O (wKC O (ks m)) (peE O Wc))).1 with hg
  have hge : GPoly.toPoly (T.MX m h) g ∣ GPoly.toPoly (T.MX m h) (peE O Wc) :=
    (GPoly.egcd_dvd _ _ _).1
  have hg0 : GPoly.toPoly (T.MX m h) g ≠ 0 := fun h0 ↦ he (zero_dvd_iff.mp (h0 ▸ hge))
  have hP0 : GPoly.toPoly (T.MX m h) (GPoly.mul O g (powG O (logPoly O true logs) (logBoundC Fc ks m logs)))
      ≠ 0 := by
    rw [GPoly.toPoly_mul, toPoly_powG_XE]
    exact mul_ne_zero hg0 (pow_ne_zero _ (toPoly_logPoly_ne_XE _ _ _))
  obtain ⟨h1, h2⟩ := toPoly_monicG (T.MX m h) _ hP0
  refine ⟨(GPoly.toPoly (T.MX m h) (GPoly.mul O g (powG O (logPoly O true logs)
    (logBoundC Fc ks m logs)))).leadingCoeff⁻¹, ?_, h2⟩
  change GPoly.toPoly (T.MX m h) (monicG O (GPoly.mul O g (powG O (logPoly O true logs)
    (logBoundC Fc ks m logs)))) = _
  rw [h1, GPoly.toPoly_mul, toPoly_powG_XE]

end Denominator


end MTower

end Curves.MT
