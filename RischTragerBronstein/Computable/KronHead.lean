import RischTragerBronstein.Computable.KronComplete

/-!
# The head certificate: combinations with a non-zero leading coefficient

`genResCertHead s ws`: every combination `∑ βⱼ wⱼ` that is a rational constant modulo every
irreducible factor of `s` has `β₀ = 0` (all null-space basis vectors of `modCols` have head `0`).

* `genResCertHead_sound`: the certificate refutes every such combination with `β₀ ≠ 0`, over any
  constant field;
* `genResCertHead_complete`: if the certificate fails, there is such a combination over `ℚ` (by
  completeness of the Kronecker factorisation, `factorQ_spec`).
-/

open Polynomial

namespace CPoly

namespace Kron

/-- **The head certificate.** -/
def genResCertHead (s : CPoly ℚ) (ws : List (CPoly ℚ)) : Bool :=
  let ps := factorQ (degC s + 1) s
  ps.all (fun p ↦ irredQ p && isZero (divMod s p).2) &&
    (nullBasis (modCols ps ws)).all fun v ↦ v.getD 0 0 == 0

lemma sum_zipWith_eq_zero {α : Type*} (f : ℚ → α → ℚ) : ∀ (l₁ : List ℚ) (l₂ : List α),
    (∀ a ∈ l₂, ∀ b, f b a = 0) → (List.zipWith f l₁ l₂).sum = 0
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | b :: l₁, a :: l₂, h => by
    rw [List.zipWith_cons_cons, List.sum_cons, h a List.mem_cons_self b,
      sum_zipWith_eq_zero f l₁ l₂ fun a' ha' ↦ h a' (List.mem_cons_of_mem _ ha'), add_zero]

/-- **The head certificate is sound.** -/
theorem genResCertHead_sound {Kc : Type*} [Field Kc] (ι : ℚ →+* Kc) (s : CPoly ℚ)
    (ws : List (CPoly ℚ)) (h : genResCertHead s ws = true) (β : List ℚ)
    (hβl : β.length = ws.length)
    (key : ∀ p : Kc[X], Irreducible p → p ∣ (toPoly s).map ι →
      ∃ q : ℚ, p ∣ (lcomb β ws).map ι - C (ι q)) : β.getD 0 0 = 0 := by
  classical
  simp only [genResCertHead, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hps, hnull⟩ := h
  set ps := factorQ (degC s + 1) s with hpsd
  have hP : ∀ P ∈ ps, Irreducible (toPoly P) ∧ toPoly P ∣ toPoly s := fun P hP ↦ by
    obtain ⟨h1, h2⟩ := hps P hP
    refine ⟨irredQ_sound P h1, ?_⟩
    have hsp := divMod_spec s P
    rw [(isZero_iff _).mp h2, add_zero] at hsp
    exact ⟨_, by rw [hsp, mul_comm]⟩
  have h0 := modCols_null ι s ws ps hP β key
  obtain ⟨β', -, heq⟩ := nullBasis_complete (RingHom.id ℚ) (modCols ps ws) β
    (by rw [modCols, List.length_map, hβl]) h0
  have hsnd : (nsItems (modCols ps ws)).map Prod.snd = (List.range β.length).map unitL := by
    simp only [nsItems, List.map_map]
    rw [modCols, List.length_map, ← hβl]
    rfl
  rw [hsnd, lcombS_range_unitLQ] at heq
  have hc := congrArg (fun Q : ℚ[X] ↦ Q.coeff 0) heq
  simp only [coeff_toPoly, coeff_lcombSQ] at hc
  rw [hc]
  exact sum_zipWith_eq_zero _ _ _ fun v hv b ↦ by rw [hnull v hv, mul_zero]

/-- A combination of two polynomials. -/
lemma lcomb_two (β : List ℚ) (a b : CPoly ℚ) :
    lcomb β [a, b] = C (β.getD 0 0) * toPoly a + C (β.getD 1 0) * toPoly b := by
  rcases β with _ | ⟨x, _ | ⟨y, β⟩⟩ <;> simp [lcomb]

/-- **The head certificate is complete**: if it fails, some combination with non-zero head is a
rational constant modulo every irreducible factor of `s` over `ℚ`. -/
theorem genResCertHead_complete (s : CPoly ℚ) (ws : List (CPoly ℚ)) (hs0 : toPoly s ≠ 0)
    (h : genResCertHead s ws = false) :
    ∃ β : List ℚ, β.getD 0 0 ≠ 0 ∧ ∀ p : ℚ[X], Irreducible p → p ∣ toPoly s →
      ∃ q : ℚ, p ∣ lcomb β ws - C q := by
  classical
  by_cases hdeg : (toPoly s).natDegree = 0
  · refine ⟨[1], by simp, fun p hp hps ↦ absurd ?_ hp.not_isUnit⟩
    have hs0' := hs0
    rw [eq_C_of_natDegree_eq_zero hdeg] at hps hs0'
    exact isUnit_of_dvd_unit hps (isUnit_C.mpr (Ne.isUnit fun h0 ↦ hs0' (by rw [h0, C_0])))
  obtain ⟨hirr, k, hk0, hk⟩ := factorQ_spec (degC s + 1) s (Nat.pos_of_ne_zero hdeg)
    (by rw [degC_eq s hs0]; omega)
  set ps := factorQ (degC s + 1) s with hpsd
  have hdvd : ∀ P ∈ ps, toPoly P ∣ toPoly s := fun P hP ↦ by
    rw [hk]
    exact dvd_mul_of_dvd_right (List.dvd_prod (List.mem_map_of_mem hP)) _
  have hchk : ps.all (fun p ↦ irredQ p && isZero (divMod s p).2) = true := by
    rw [List.all_eq_true]
    intro P hP
    rw [Bool.and_eq_true]
    refine ⟨hirr P hP, (isZero_iff _).mpr ?_⟩
    have hP0 : toPoly P ≠ 0 := (irredQ_sound P (hirr P hP)).ne_zero
    refine toPoly_eq_zero_of_dvd_of_degree_lt ?_ (divMod_degree_lt s P hP0)
    have : toPoly (divMod s P).2 = toPoly s - toPoly (divMod s P).1 * toPoly P := by
      rw [divMod_spec s P]; ring
    rw [this]
    exact dvd_sub (hdvd P hP) (dvd_mul_left _ _)
  simp only [genResCertHead, ← hpsd, hchk, Bool.true_and, List.all_eq_false, beq_iff_eq] at h
  obtain ⟨v, hv, hv0⟩ := h
  refine ⟨v, by simpa using hv0, fun p hp hps ↦ ?_⟩
  have hrel := nullBasis_sound (modCols ps ws) v hv
  -- `p` divides some factor
  have hps' : p ∣ (ps.map toPoly).prod := by
    rw [hk] at hps
    exact (hp.prime.dvd_or_dvd hps).resolve_left fun hd ↦
      hp.not_isUnit (isUnit_of_dvd_unit hd (isUnit_C.mpr (Ne.isUnit hk0)))
  obtain ⟨Pp, hPm, hpP⟩ := (hp.prime.dvd_prod_iff).mp hps'
  obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hPm
  have hPirr := irredQ_sound P (hirr P hP)
  have hP0 : toPoly P ≠ 0 := hPirr.ne_zero
  -- the remainder combination is constant
  set Rem := lcomb v (ws.map fun w ↦ (divMod w P).2) with hRem
  have hRdeg : Rem.degree < (toPoly P).degree := by
    have hdegP : 0 < (toPoly P).degree := by
      rw [degree_eq_natDegree hP0]
      have : (toPoly P).natDegree ≠ 0 := fun h0 ↦ hPirr.not_isUnit
        (isUnit_iff_degree_eq_zero.mpr (by rw [degree_eq_natDegree hP0, h0]; rfl))
      exact_mod_cast Nat.pos_of_ne_zero this
    exact degree_lcomb_lt' (lt_of_lt_of_le (WithBot.bot_lt_coe 0) hdegP.le) v _ fun u hu ↦ by
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hu
      exact divMod_degree_lt w P hP0
  have hcoef : ∀ i, 1 ≤ i → Rem.coeff i = 0 := by
    intro i hi
    by_cases hiP : i < degC P
    · -- `(P, i)` is an index of `modCols`
      have hmem : (P, i) ∈ modIdx ps := by
        unfold modIdx
        simp only [List.mem_flatMap, List.mem_map, List.mem_range]
        exact ⟨P, hP, i - 1, by omega, by rw [Nat.sub_add_cancel hi]⟩
      obtain ⟨t, ht, heqt⟩ := List.getElem_of_mem hmem
      have hc := congrArg (fun Q : ℚ[X] ↦ Q.coeff t) hrel
      simp only [coeff_lcomb, coeff_zero] at hc
      rw [hRem, coeff_lcomb, List.zipWith_map_right]
      rw [modCols, List.zipWith_map_right] at hc
      have e : ∀ w : CPoly ℚ, ((modIdx ps).map fun pi ↦ (divMod w pi.1).2.getD pi.2 0).getD t 0 =
          (divMod w P).2.getD i 0 := fun w ↦ by
        rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map, heqt]
      simp only [e] at hc
      exact hc
    · rw [degC_eq P hP0] at hiP
      exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hRdeg (by
        rw [degree_eq_natDegree hP0]; exact_mod_cast (by omega : (toPoly P).natDegree ≤ i)))
  have hRC : Rem = C (Rem.coeff 0) := by
    ext i
    rw [coeff_C]
    split_ifs with hi
    · rw [hi]
    · exact hcoef i (Nat.pos_of_ne_zero hi)
  refine ⟨Rem.coeff 0, hpP.trans ?_⟩
  have e := lcomb_rem P v ws
  rw [← hRem, hRC] at e
  rw [show lcomb v ws - C (Rem.coeff 0) = lcomb v (ws.map fun w ↦ (divMod w P).1) * toPoly P from
    by rw [← e]]
  exact dvd_mul_left _ _

end Kron

end CPoly
