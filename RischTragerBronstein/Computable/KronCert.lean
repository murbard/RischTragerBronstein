import RischTragerBronstein.Computable.Kronecker
import RischTragerBronstein.Computable.NullSpace

/-!
# Rational residues at every root: a certificate by factorisation

For a squarefree `s ∈ ℚ[x]` and residue polynomials `w₁, …, w_d`, `genResCert s ws` certifies that
**no non-zero `β ∈ ℚᵈ` makes `∑ βⱼ wⱼ` a rational constant modulo every irreducible factor of
`s`** (equivalently: rational valued at every root of `s`). The factors are found by an untrusted
Kronecker search (`factorQ`), each is certified irreducible over `ℚ` (`irredQ_sound`) and to divide
`s`; the condition "constant modulo `pₖ`" is linear in `β` (the non-constant coefficients of the
remainders vanish), and the null space of this linear system is checked to be trivial.

`genResCert_sound` is stated in the form used by the Hermite-kernel certificate of mixed towers:
if every irreducible factor `p` (over any extension `Kc ⊇ ℚ`) of `s` divides `∑ βⱼ wⱼ - q` for some
rational `q`, then `β = 0`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

namespace Kron

/-! ### The untrusted factoriser -/

/-- A factor of degree `e` found by the Kronecker search. -/
def findFactorDeg (F : CPoly ℚ) (e : ℕ) : Option (CPoly ℚ) :=
  let pts := ptsFor F (e + 1)
  let ptsQ := pts.map fun a : ℤ ↦ (Int.cast a : ℚ)
  let W : ℤ := ((lagDen ptsQ : ℕ) : ℤ)
  let BZ := basisZ ptsQ
  let ok := basisOk ptsQ
  (List.sections (pts.map fun a : ℤ ↦ divsZ (evalC F (Int.cast a : ℚ)).num)).findSome? fun ds ↦
    if ok && !zFilter F W (lagZ BZ ds) then none
    else
      let g := lagr ptsQ (ds.map fun d : ℤ ↦ (Int.cast d : ℚ))
      if (trim g).length == e + 1 && intC g && valTest F g && isZero (divMod F g).2 then some g
      else none

/-- A non-trivial factor, if any. -/
def findFactor (F : CPoly ℚ) : Option (CPoly ℚ) :=
  (List.range (degC F / 2)).findSome? fun e ↦ findFactorDeg F (e + 1)

/-- The primitive integral associate. -/
def primInt (g : CPoly ℚ) : CPoly ℚ :=
  let d : ℚ := (g.foldr (fun q acc ↦ Nat.lcm q.den acc) 1 : ℕ)
  let g' := g.map (· * d)
  let c : ℚ := (gcdL (g'.map Rat.num) : ℕ)
  if c = 0 then g' else g'.map (· / c)

/-- The factorisation (untrusted: its factors are certified by `irredQ`). -/
def factorQ : ℕ → CPoly ℚ → List (CPoly ℚ)
  | 0, F => [primInt F]
  | fuel + 1, F =>
    match findFactor (primInt F) with
    | none => [primInt F]
    | some g => factorQ fuel g ++ factorQ fuel (divMod (primInt F) g).1

/-! ### The certificate -/

/-- The index set: the non-constant coefficient positions of the remainders modulo each factor. -/
def modIdx (ps : List (CPoly ℚ)) : List (CPoly ℚ × ℕ) :=
  ps.flatMap fun p ↦ (List.range (degC p - 1)).map fun i ↦ (p, i + 1)

/-- The columns: the non-constant coefficients of `w mod p` for every factor `p`. -/
def modCols (ps ws : List (CPoly ℚ)) : List (CPoly ℚ) :=
  ws.map fun w ↦ (modIdx ps).map fun pi ↦ (divMod w pi.1).2.getD pi.2 0

/-- **The certificate**: the factors are irreducible divisors of `s`, and no non-zero combination
of the `wⱼ` is constant modulo each of them. -/
def genResCert (s : CPoly ℚ) (ws : List (CPoly ℚ)) : Bool :=
  let ps := factorQ (degC s + 1) s
  ps.all (fun p ↦ irredQ p && isZero (divMod s p).2) && (nullBasis (modCols ps ws)).isEmpty

/-! ### Soundness -/

section Sound

lemma toPoly_unitLQ (j : ℕ) : toPoly (unitL j : CPoly ℚ) = X ^ j := by
  rw [unitL, toPoly_append]
  have : toPoly (List.replicate j (0 : ℚ)) = 0 := by
    induction j with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ih]
  simp [this]

lemma lcombS_range_unitLQ : ∀ (c : List ℚ),
    lcombS (RingHom.id ℚ) c ((List.range c.length).map unitL) = toPoly c := by
  classical
  intro c
  induction c using List.reverseRecOn with
  | nil => simp [lcombS]
  | append_singleton c x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
      List.map_singleton, lcombS_append (RingHom.id ℚ) _ _ _ _ (by simp), ih, toPoly_append,
      toPoly_unitLQ]
    simp

lemma coeff_lcombSQ (j : ℕ) : ∀ (β : List ℚ) (ws : List (CPoly ℚ)),
    (lcombS (RingHom.id ℚ) β ws).coeff j = (List.zipWith (fun b w ↦ b * w.getD j 0) β ws).sum
  | [], _ => by simp [lcombS]
  | _ :: _, [] => by simp [lcombS]
  | b :: β, w :: ws => by
    have ih := coeff_lcombSQ j β ws
    simp only [lcombS] at ih
    simp only [lcombS, List.zipWith_cons_cons, List.sum_cons, coeff_add, coeff_C_mul, coeff_map,
      coeff_toPoly, ih, RingHom.id_apply]

lemma coeff_lcomb (j : ℕ) : ∀ (β : List ℚ) (ws : List (CPoly ℚ)),
    (lcomb β ws).coeff j = (List.zipWith (fun b w ↦ b * w.getD j 0) β ws).sum
  | [], _ => by simp [lcomb]
  | _ :: _, [] => by simp [lcomb]
  | b :: β, w :: ws => by
    have ih := coeff_lcomb j β ws
    simp only [lcomb] at ih
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons, coeff_add, coeff_C_mul, coeff_toPoly, ih]

/-- Remainders of a combination. -/
lemma lcomb_rem (P : CPoly ℚ) : ∀ (β : List ℚ) (ws : List (CPoly ℚ)),
    lcomb β ws - lcomb β (ws.map fun w ↦ (divMod w P).2) =
      lcomb β (ws.map fun w ↦ (divMod w P).1) * toPoly P
  | [], _ => by simp [lcomb]
  | _ :: _, [] => by simp [lcomb]
  | b :: β, w :: ws => by
    have ih := lcomb_rem P β ws
    simp only [lcomb, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [add_mul, ← ih, divMod_spec w P]
    ring

lemma degree_lcomb_lt' {d : WithBot ℕ} (hd : ⊥ < d) : ∀ (β : List ℚ) (vs : List (CPoly ℚ)),
    (∀ v ∈ vs, (toPoly v).degree < d) → (lcomb β vs).degree < d
  | [], _, _ => by simpa [lcomb] using hd
  | _ :: _, [], _ => by simpa [lcomb] using hd
  | b :: β, v :: vs, h => by
    simp only [lcomb, List.zipWith_cons_cons, List.sum_cons]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _)
        (h v List.mem_cons_self)
    · exact degree_lcomb_lt' hd β vs fun u hu ↦ h u (List.mem_cons_of_mem _ hu)

lemma zipWith_zero_sum {α β : Type*} : ∀ (l₁ : List α) (l₂ : List β),
    (List.zipWith (fun _ _ ↦ (0 : ℚ)) l₁ l₂).sum = 0
  | [], _ => by simp
  | _ :: _, [] => by simp
  | _ :: l₁, _ :: l₂ => by simp [zipWith_zero_sum l₁ l₂]

/-- **The core of the certificate**: a combination that is a rational constant modulo every
irreducible factor of `s` (over any constant field) is in the null space of `modCols`. -/
theorem modCols_null {Kc : Type*} [Field Kc] (ι : ℚ →+* Kc) (s : CPoly ℚ)
    (ws ps : List (CPoly ℚ)) (hP : ∀ P ∈ ps, Irreducible (toPoly P) ∧ toPoly P ∣ toPoly s)
    (β : List ℚ)
    (key : ∀ p : Kc[X], Irreducible p → p ∣ (toPoly s).map ι →
      ∃ q : ℚ, p ∣ (lcomb β ws).map ι - C (ι q)) :
    lcombS (RingHom.id ℚ) β (modCols ps ws) = 0 := by
  classical
  set r := lcomb β ws with hr
  -- `r` is a rational constant modulo every factor
  have hA : ∀ P ∈ ps, ∃ q : ℚ, toPoly P ∣ r - C q := by
    intro P hPm
    obtain ⟨hirr, hdvd⟩ := hP P hPm
    have hne : (toPoly P).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hirr.ne_zero
    have hnu : ¬IsUnit ((toPoly P).map ι) := by
      intro hu
      have h1 := natDegree_eq_zero_of_isUnit hu
      rw [natDegree_map_eq_of_injective ι.injective] at h1
      exact hirr.not_isUnit (isUnit_iff_degree_eq_zero.mpr (by
        rw [degree_eq_natDegree hirr.ne_zero, h1]; rfl))
    obtain ⟨p, hp, hpP⟩ := WfDvdMonoid.exists_irreducible_factor hnu hne
    obtain ⟨q, hq⟩ := key p hp (hpP.trans (Polynomial.map_dvd ι hdvd))
    refine ⟨q, ?_⟩
    by_contra hnd
    have hcop := (hirr.coprime_iff_not_dvd).mpr hnd
    have hcopK := hcop.map (Polynomial.mapRingHom ι)
    simp only [coe_mapRingHom, Polynomial.map_sub, map_C] at hcopK
    exact hp.not_isUnit (hcopK.isUnit_of_dvd' hpP hq)
  -- the non-constant coefficients of the remainders vanish
  have hB : ∀ P ∈ ps, ∀ i, 1 ≤ i → (List.zipWith (fun b w ↦ b * w.getD i 0) β
      (ws.map fun w ↦ (divMod w P).2)).sum = 0 := by
    intro P hPm i hi
    obtain ⟨hirr, -⟩ := hP P hPm
    obtain ⟨q, hq⟩ := hA P hPm
    have hP0 : toPoly P ≠ 0 := hirr.ne_zero
    have hdegP : 0 < (toPoly P).degree := by
      rw [degree_eq_natDegree hP0]
      have : (toPoly P).natDegree ≠ 0 := fun h0 ↦
        hirr.not_isUnit (isUnit_iff_degree_eq_zero.mpr (by rw [degree_eq_natDegree hP0, h0]; rfl))
      exact_mod_cast Nat.pos_of_ne_zero this
    set Rem := lcomb β (ws.map fun w ↦ (divMod w P).2) with hRem
    have hRdeg : Rem.degree < (toPoly P).degree := degree_lcomb_lt' (lt_of_lt_of_le
      (WithBot.bot_lt_coe 0) hdegP.le) β _ fun v hv ↦ by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
        exact divMod_degree_lt w P hP0
    have hRq : Rem - C q = 0 := by
      refine Kron.toPoly_eq_zero_of_dvd_of_degree_lt ?_ (lt_of_le_of_lt (degree_sub_le _ _)
        (max_lt hRdeg (lt_of_le_of_lt degree_C_le hdegP)))
      have e := lcomb_rem P β ws
      rw [← hr] at e
      have : Rem - C q = (r - C q) - lcomb β (ws.map fun w ↦ (divMod w P).1) * toPoly P := by
        rw [← e]; ring
      rw [this]
      exact dvd_sub hq (dvd_mul_left _ _)
    have hc := congrArg (fun Q : ℚ[X] ↦ Q.coeff i) (sub_eq_zero.mp hRq)
    simp only [coeff_C, if_neg (by omega : i ≠ 0)] at hc
    rw [hRem, coeff_lcomb] at hc
    exact hc
  -- the linear system
  have h0 : lcombS (RingHom.id ℚ) β (modCols ps ws) = 0 := by
    ext t
    rw [coeff_lcombSQ, coeff_zero, modCols, List.zipWith_map_right]
    by_cases ht : t < (modIdx ps).length
    · obtain ⟨P, hPm, i, hi, heq⟩ : ∃ P ∈ ps, ∃ i < degC P - 1, (P, i + 1) = (modIdx ps)[t] := by
        have h := List.getElem_mem (l := modIdx ps) ht
        unfold modIdx at h ⊢
        simp only [List.mem_flatMap, List.mem_map, List.mem_range] at h
        obtain ⟨P, hPm, i, hi, heq⟩ := h
        exact ⟨P, hPm, i, hi, heq⟩
      have e : ∀ w : CPoly ℚ, ((modIdx ps).map fun pi ↦ (divMod w pi.1).2.getD pi.2 0).getD t 0 =
          (divMod w P).2.getD (i + 1) 0 := fun w ↦ by
        rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map, ← heq]
      simp only [e]
      have := hB P hPm (i + 1) (by omega)
      rwa [List.zipWith_map_right] at this
    · have e : ∀ w : CPoly ℚ, ((modIdx ps).map fun pi ↦ (divMod w pi.1).2.getD pi.2 0).getD t 0 = 0 :=
        fun w ↦ List.getD_eq_default _ _ (by simp; omega)
      simp only [e, mul_zero]
      exact zipWith_zero_sum β ws
  exact h0

/-- **The certificate is sound.** -/
theorem genResCert_sound {Kc : Type*} [Field Kc] (ι : ℚ →+* Kc) (s : CPoly ℚ)
    (ws : List (CPoly ℚ)) (h : genResCert s ws = true) (β : List ℚ) (hβl : β.length = ws.length)
    (key : ∀ p : Kc[X], Irreducible p → p ∣ (toPoly s).map ι →
      ∃ q : ℚ, p ∣ (lcomb β ws).map ι - C (ι q)) : ∀ b ∈ β, b = 0 := by
  classical
  simp only [genResCert, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at h
  obtain ⟨hps, hnull⟩ := h
  set ps := factorQ (degC s + 1) s with hpsd
  have hP : ∀ P ∈ ps, Irreducible (toPoly P) ∧ toPoly P ∣ toPoly s := fun P hP ↦ by
    obtain ⟨h1, h2⟩ := hps P hP
    refine ⟨irredQ_sound P h1, ?_⟩
    have hsp := divMod_spec s P
    rw [(isZero_iff _).mp h2, add_zero] at hsp
    exact ⟨_, by rw [hsp, mul_comm]⟩
  have h0 := modCols_null ι s ws ps hP β key
  obtain ⟨β', hβ'l, heq⟩ := nullBasis_complete (RingHom.id ℚ) (modCols ps ws) β
    (by rw [modCols, List.length_map, hβl]) h0
  rw [hnull, List.length_nil, List.length_eq_zero_iff] at hβ'l
  subst hβ'l
  have hsnd : (nsItems (modCols ps ws)).map Prod.snd = (List.range β.length).map unitL := by
    simp only [nsItems, List.map_map]
    rw [modCols, List.length_map, ← hβl]
    rfl
  rw [hsnd, lcombS_range_unitLQ, hnull] at heq
  have hβ0 : toPoly β = 0 := by rw [heq]; simp [lcombS]
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  have := congrArg (fun Q : ℚ[X] ↦ Q.coeff j) hβ0
  simp only [coeff_toPoly, coeff_zero, List.getD_eq_getElem _ _ hj] at this
  exact this

end Sound

end Kron

end CPoly
