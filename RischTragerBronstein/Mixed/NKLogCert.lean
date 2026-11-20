import RischTragerBronstein.Mixed.NKLogRes

/-!
# The logarithmic part with a certificate for the logarithms

For `f` with non-zero residues, a certificate `(uⱼ, cⱼ)` (`uⱼ ∈ Fₘ₊₁[θ]`, `cⱼ ∈ ℚ`) with
`g = f − ∑ cⱼ uⱼ′/uⱼ` residue-free: `∑ cⱼ log uⱼ` is elementary, so `f` has an elementary integral
iff `g` has one, which `nk_iffR` decides (`nk_iffC`). `logCert` checks `f − g − ∑ cⱼ uⱼ′/uⱼ ≡ 0`
modulo `P`, computing `uⱼ′/uⱼ` from `θ′` (`dThetaC`) and a Bezout inverse of `uⱼ` modulo `P`.
Existence of such a certificate is the torsion question for the residue divisors.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

section Codes

variable {α : Type} (O : COps α)

/-- The inverse of `u` modulo `P` (Bezout with a constant gcd). -/
def invModC (P u : GPoly α) : Option (GPoly α) :=
  let e := GPoly.egcd O u P
  let g := GPoly.trim O e.1
  if g.length = 1 then some (GPoly.smul O (O.inv (g.getD 0 O.zero)) e.2.1) else none

/-- `u′/u` modulo `P`, given `θ′ = dθ(θ)`. -/
def logDerC (P dθ u : GPoly α) : Option (GPoly α) :=
  (invModC O P u).map fun iv ↦
    remP O P (GPoly.mul O (GPoly.add O (GPoly.mapD O u) (GPoly.mul O dθ (GPoly.derivX O u))) iv)

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The logarithm certificate**: `f − g − ∑ cⱼ uⱼ′/uⱼ ≡ 0 mod P`. -/
def logCert (m : ℕ) (P : GPoly (LC (m + 1))) (fl gl : List (LC (m + 1)))
    (us : List (GPoly (LC (m + 1)))) (cs : List ℚ) : Bool :=
  let O1 := MOr Fc ks (m + 1)
  match dThetaC O1 P with
  | none => false
  | some dθ =>
    let lds := us.map (logDerC O1 P dθ)
    let tot := ((List.range us.length).map fun j ↦
      GPoly.smul O1 (mcst Fc ks (m + 1) (cs.getD j 0)) ((lds.getD j none).getD [])).foldr
        (GPoly.add O1) []
    (lds.all Option.isSome) &&
      (remP O1 P (GPoly.sub O1 (GPoly.sub O1 fl gl) tot)).all O1.isZero

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L)

lemma sem_mcst_L (c : ℚ) :
    (((T.MPr (m + 1) h1).sem (mcst Fc ks (m + 1) c) : T.F (m + 1)) : L) = (c : L) := by
  rw [MPr_sem, T.sem_mcst (m + 1) h1 c]
  push_cast; rfl

/-- A coordinate list evaluated at `θ`. -/
lemma evθ_list (l : List (LC (m + 1))) :
    T.evθ m h1 θ l = ∑ j ∈ Finset.range l.length,
      ((T.MPr (m + 1) h1).sem (l.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j := by
  induction l with
  | nil => simp [evθ]
  | cons a l ih =>
    have e : T.evθ m h1 θ (a :: l) = ((T.MPr (m + 1) h1).sem a : L) + θ * T.evθ m h1 θ l := by
      simp [evθ, GPoly.toPoly_cons]
    rw [e, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by ring

lemma invModC_sound (P u iv : GPoly (LC (m + 1))) (hP : T.evθ m h1 θ P = 0)
    (h : invModC (MOr Fc ks (m + 1)) P u = some iv) :
    T.evθ m h1 θ iv * T.evθ m h1 θ u = 1 := by
  set O1 := MOr Fc ks (m + 1)
  set M1 := T.MPr (m + 1) h1
  unfold invModC at h
  simp only at h
  split_ifs at h with hg
  obtain rfl := Option.some.inj h
  set e := GPoly.egcd O1 u P with he
  obtain ⟨a, ha⟩ : ∃ a, GPoly.trim O1 e.1 = [a] := by
    match hx : GPoly.trim O1 e.1, hg with
    | [a], _ => exact ⟨a, rfl⟩
  have hga : (GPoly.trim O1 e.1).getD 0 O1.zero = a := by rw [ha]; rfl
  rw [hga]
  have hne : GPoly.trim O1 e.1 ≠ [] := by rw [ha]; simp
  have hlc0 := (GPoly.natDegree_toPoly_of_trim_ne_nil M1 hne).2.2
  rw [ha] at hlc0
  change M1.sem a ≠ 0 at hlc0
  have hgC : GPoly.toPoly M1 e.1 = C (M1.sem a) := by
    rw [← GPoly.toPoly_trim, ha]; simp
  have hbez := GPoly.egcd_spec M1 u P
  rw [← he, hgC] at hbez
  have hbezθ := congrArg (aeval θ) hbez
  simp only [map_add, map_mul, aeval_C] at hbezθ
  have hPθ : aeval θ (GPoly.toPoly M1 P) = 0 := hP
  rw [hPθ, mul_zero, add_zero] at hbezθ
  unfold evθ
  rw [GPoly.toPoly_smul, map_mul, aeval_C, mul_assoc, hbezθ, M1.sem_inv, map_inv₀]
  have : algebraMap (T.F (m + 1)) L (M1.sem a) ≠ 0 :=
    (algebraMap (T.F (m + 1)) L).injective.ne (by simpa using hlc0)
  field_simp

lemma logDerC_sound (P dθ u ld : GPoly (LC (m + 1))) (hP : T.evθ m h1 θ P = 0)
    (hd : dThetaC (MOr Fc ks (m + 1)) P = some dθ)
    (h : logDerC (MOr Fc ks (m + 1)) P dθ u = some ld) :
    T.evθ m h1 θ u ≠ 0 ∧ T.evθ m h1 θ ld = (T.evθ m h1 θ u)′ / T.evθ m h1 θ u := by
  unfold logDerC at h
  obtain ⟨iv, hiv, rfl⟩ := Option.map_eq_some_iff.mp h
  have hinv := T.invModC_sound m h1 θ P u iv hP hiv
  have hu0 : T.evθ m h1 θ u ≠ 0 := fun h0 ↦ by rw [h0, mul_zero] at hinv; exact zero_ne_one hinv
  refine ⟨hu0, ?_⟩
  rw [T.evθ_remP m h1 θ P hP]
  have hdu := T.deriv_evθ m h1 θ u
  rw [T.deriv_θ m h1 θ P hP dθ hd] at hdu
  have hiv' : T.evθ m h1 θ iv = (T.evθ m h1 θ u)⁻¹ := eq_inv_of_mul_eq_one_left hinv
  unfold evθ at hdu hiv' ⊢
  rw [GPoly.toPoly_mul, GPoly.toPoly_add, GPoly.toPoly_mul, map_mul, map_add, map_mul, hiv', hdu,
    div_eq_mul_inv]
  ring

/-- **The certificate is sound**: every `uⱼ(θ) ≠ 0` and `f = g + ∑ cⱼ uⱼ′/uⱼ`. -/
lemma logCert_sound (P : GPoly (LC (m + 1))) (hP : T.evθ m h1 θ P = 0) (fl gl : List (LC (m + 1)))
    (us : List (GPoly (LC (m + 1)))) (cs : List ℚ) (hc : logCert Fc ks m P fl gl us cs = true) :
    (∀ j < us.length, T.evθ m h1 θ (us.getD j []) ≠ 0) ∧
    T.evθ m h1 θ fl = T.evθ m h1 θ gl + ∑ j ∈ Finset.range us.length,
      ((cs.getD j 0 : ℚ) : L) * ((T.evθ m h1 θ (us.getD j []))′ / T.evθ m h1 θ (us.getD j [])) := by
  classical
  set O1 := MOr Fc ks (m + 1)
  set M1 := T.MPr (m + 1) h1
  unfold logCert at hc
  simp only at hc
  split at hc
  · exact absurd hc (by simp)
  rename_i dθ hd
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hc
  obtain ⟨hsome, hzero⟩ := hc
  have hld : ∀ j < us.length, ∃ ld, logDerC O1 P dθ (us.getD j []) = some ld ∧
      ((us.map (logDerC O1 P dθ)).getD j none).getD [] = ld := by
    intro j hj
    have hm : (us.map (logDerC O1 P dθ)).getD j none ∈ us.map (logDerC O1 P dθ) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hj)]; exact List.getElem_mem _
    have hs := hsome _ hm
    have e1 : (us.map (logDerC O1 P dθ)).getD j none = logDerC O1 P dθ (us.getD j []) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
        List.getD_eq_getElem _ _ hj]
    rw [e1] at hs
    obtain ⟨ld, hld⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨ld, hld, by rw [e1, hld]; rfl⟩
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · obtain ⟨ld, hld1, -⟩ := hld j hj
    exact (T.logDerC_sound m h1 θ P dθ _ ld hP hd hld1).1
  · -- the difference vanishes at `θ`
    set tot := ((List.range us.length).map fun j ↦
      GPoly.smul O1 (mcst Fc ks (m + 1) (cs.getD j 0))
        (((us.map (logDerC O1 P dθ)).getD j none).getD [])).foldr (GPoly.add O1) [] with htot
    have h0 : GPoly.toPoly M1 (remP O1 P (GPoly.sub O1 (GPoly.sub O1 fl gl) tot)) = 0 := by
      refine Polynomial.ext fun i ↦ ?_
      rw [coeff_toPoly_sem, Polynomial.coeff_zero]
      by_cases hi : i < (remP O1 P (GPoly.sub O1 (GPoly.sub O1 fl gl) tot)).length
      · rw [List.getD_eq_getElem _ _ hi]
        exact (M1.isZero_iff _).mp (hzero _ (List.getElem_mem hi))
      · rw [List.getD_eq_default _ _ (by omega)]; exact M1.sem_zero
    have h1' : T.evθ m h1 θ (GPoly.sub O1 (GPoly.sub O1 fl gl) tot) = 0 := by
      rw [← T.evθ_remP m h1 θ P hP, evθ, h0, map_zero]
    have hfold : ∀ l : List (GPoly (LC (m + 1))),
        T.evθ m h1 θ (l.foldr (GPoly.add O1) []) = (l.map (T.evθ m h1 θ)).sum := by
      intro l
      induction l with
      | nil => simp [evθ]
      | cons a l ih =>
        rw [List.foldr_cons, List.map_cons, List.sum_cons, ← ih]
        unfold evθ; rw [GPoly.toPoly_add, map_add]
    have htotv : T.evθ m h1 θ tot = ∑ j ∈ Finset.range us.length,
        ((cs.getD j 0 : ℚ) : L) * ((T.evθ m h1 θ (us.getD j []))′ / T.evθ m h1 θ (us.getD j [])) := by
      rw [htot, hfold, List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      obtain ⟨ld, hld1, hld2⟩ := hld j (Finset.mem_range.mp hj)
      simp only [Function.comp_apply]
      rw [hld2]
      have hs := (T.logDerC_sound m h1 θ P dθ _ ld hP hd hld1).2
      unfold evθ at hs ⊢
      rw [GPoly.toPoly_smul, map_mul, aeval_C, hs]
      congr 1
      exact T.sem_mcst_L m h1 _
    unfold evθ at h1' htotv ⊢
    rw [GPoly.toPoly_sub, GPoly.toPoly_sub, map_sub, map_sub, sub_eq_zero] at h1'
    rw [← htotv]
    linear_combination h1'

lemma deriv_ratCast_any {E : Type*} [Field E] [Differential E] [CharZero E] (q : ℚ) :
    ((q : E))′ = 0 := by
  have hd : ((q.den : ℕ) : E) ≠ 0 := by exact_mod_cast q.den_nz
  have e : (q : E) * ((q.den : ℕ) : E) = ((q.num : ℤ) : E) := by
    rw [← Rat.cast_natCast, ← Rat.cast_intCast, ← Rat.cast_mul]
    congr 1
    exact_mod_cast Rat.mul_den_eq_num q
  have h := congrArg (fun z : E ↦ z′) e
  simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_natCast, Derivation.map_intCast,
    mul_zero, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left hd

/-- A rational combination of logarithmic derivatives is elementary in every extension. -/
lemma hasElementaryIntegralIn_logs {F : Type u} [Field F] [Differential F] [CharZero F] (N : ℕ) (c : ℕ → ℚ)
    (w : ℕ → F) (hw : ∀ j < N, w j ≠ 0) :
    HasElementaryIntegralIn (∑ j ∈ Finset.range N, ((c j : ℚ) : F) * ((w j)′ / w j)) := by
  intro E _ _ _ _ _
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  have hl : ∀ p ∈ ((List.range N).map fun j ↦ (((c j : ℚ) : E), algebraMap F E (w j))),
      p.1′ = 0 ∧ p.2 ≠ 0 := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    refine ⟨?_, (map_ne_zero_iff _ (algebraMap F E).injective).mpr (hw j (List.mem_range.mp hj))⟩
    exact deriv_ratCast_any _
  have h := hasElementaryIntegral_of_liouville_form (0 : E) _ hl
  convert h using 1
  rw [Derivation.map_zero, zero_add, List.map_map, ← List.sum_toFinset _ List.nodup_range,
    List.toFinset_range, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Function.comp_apply, map_mul, map_div₀, map_ratCast, logDeriv, deriv_algebraMap]

set_option maxHeartbeats 4000000 in
-- the proof unfolds the tower specifications
/-- **The log-certified decision**: with a certificate `(uⱼ, cⱼ)` making `g = f − ∑ cⱼ uⱼ′/uⱼ`
residue-free (`resCert`), `∫ f` is elementary iff `g − τ(g)/n` is exact and `τ(g)/n` is
elementary. -/
theorem nk_iffC (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fl : List (LC (m + 1))) (hfl : fl.length = Pp.length)
    (gp : List (GPoly (LC m))) (D : GPoly (LC m))
    (hsq : GPoly.squarefreeCheck (MO Fc ks m) D = true) (kc : ℕ) (U : List (GPoly (LC m)))
    (hcert : resCert Fc ks m Pp gp D kc U = true) (hgpl : gp.length = Pp.length)
    (us : List (GPoly (LC (m + 1)))) (cs : List ℚ)
    (hlog : logCert Fc ks m (nkPC Fc ks m Pp) fl (nkFlR m gp D) us cs = true)
    (res : Bool)
    (hres : exactG Fc ks m (primSysC Fc ks m η (paramLimC Fc ks lv m)) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFlR m gp D) (nkTau Fc ks m Pp.length (nkFlR m gp D) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
      ((T.MPr (m + 1) (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr).sem
        (fl.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFlR m gp D) s)) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  obtain ⟨hu0, hfg⟩ := T.logCert_sound m hTr θ _ hP _ _ us cs hlog
  have hlen : ∀ (l : List (GPoly (LC m))) (D0 : GPoly (LC m)), (nkFlR m l D0).length = l.length :=
    fun l D0 ↦ List.length_map _
  have hev : ∀ (l : List (GPoly (LC m))) (D0 : GPoly (LC m)), l.length = Pp.length →
      T.evθ m hTr θ (nkFlR m l D0) =
        ∑ j ∈ Finset.range Pp.length, T.evP m (l.getD j []) / T.evP m D0 * θ ^ j := by
    intro l D0 hl
    rw [T.evθ_list, hlen, hl]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [T.sem_nkFlR m hTr l D0 j]
  rw [T.evθ_list, hfl, hev gp D hgpl] at hfg
  have hL := hasElementaryIntegralIn_logs us.length (fun j ↦ cs.getD j 0)
    (fun j ↦ T.evθ m hTr θ (us.getD j [])) hu0
  rw [← T.nk_iffR hmon hdeg m hn hc hk Pp hsh θ hθ hgen s hs gp D hsq kc U hcert hgpl res hres, hfg]
  constructor
  · intro h
    have := h.sub_in hL
    simpa using this
  · intro h
    exact h.add_in hL

end MTower

end Curves.MT
