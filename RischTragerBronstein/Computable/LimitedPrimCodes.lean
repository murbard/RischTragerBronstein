import RischTragerBronstein.Computable.LimitedPrim

/-!
# Limited integration inside `R(x)(t₁)`: explicit coefficient codes

`coeffFn` reads off, from the list returned by `primLoop`, fraction codes for the coefficients
`pⱼ = Qⱼ + cⱼ₋₁ / j` (`j ≥ 2`), `p₁ = Q₁ + b₁` of the polynomial `P` with
`pⱼ′ + (j + 1) η₁ pⱼ₊₁ = aⱼ` (`j ≥ 1`). `primLoop_codes` proves these equations for the codes, in
every model.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- `q + c`. -/
def addConst (q : CPoly R × CPoly R) (c : R) : CPoly R × CPoly R :=
  (add q.1 (smul c q.2), q.2)

/-- Coefficient codes of `P`: `m` is the index of the current top coefficient. -/
def coeffFn : ℕ → CPoly R × CPoly R → List (R × (CPoly R × CPoly R)) → R → ℕ → CPoly R × CPoly R
  | m, Q, [], b₁ => fun j ↦ if j = m then addConst Q b₁ else ([], [1])
  | m, Q, cQ :: L, b₁ => fun j ↦
    if j = m then addConst Q (cQ.1 / (m : R)) else coeffFn (m - 1) cQ.2 L b₁ j

/-- `G = gn / gd + Q` as a fraction. -/
def Gfrac (I : RationalIntegral R) : CPoly R × CPoly R := (add I.gn (mul I.Q I.gd), I.gd)

/-- Difference of fractions. -/
def fsub (q₁ q₂ : CPoly R × CPoly R) : CPoly R × CPoly R :=
  (sub (mul q₁.1 q₂.2) (mul q₂.1 q₁.2), mul q₁.2 q₂.2)

/-- Scalar multiple of a fraction. -/
def fsmul (c : R) (q : CPoly R × CPoly R) : CPoly R × CPoly R := (smul c q.1, q.2)

/-- The level-`0` coefficient `G_I - b G₁ - c G₂`. -/
def level0 (I Iη₁ Iη₂ : RationalIntegral R) (b c : R) : CPoly R × CPoly R :=
  fsub (fsub (Gfrac I) (fsmul b (Gfrac Iη₁))) (fsmul c (Gfrac Iη₂))

/-- `limitedPrim`, returning the constant `c` and codes for all coefficients of `P`
(`P′ = A - c η₂`). -/
def limitedPrimCodes (En Ed : CPoly R) (Iη₁ Iη₂ : RationalIntegral R) (A D : ℕ → CPoly R)
    (d : ℕ) : Option (R × (ℕ → CPoly R × CPoly R)) :=
  match primLoop En Ed Iη₁ A D d ([], [1]) with
  | none => none
  | some L =>
    let g := primG En Ed 0 (A 0) (D 0) (primLastQ ([], [1]) L)
    let I := integrateRational g.1 g.2
    match limitedCritN I.r I.s [(Iη₁.r, Iη₁.s), (Iη₂.r, Iη₂.s)] with
    | none => none
    | some cs => some (cs.getD 1 0, fun j ↦
        if j = 0 then level0 I Iη₁ Iη₂ (cs.getD 0 0) (cs.getD 1 0)
        else coeffFn (d + 1) ([], [1]) L (cs.getD 0 0) j)

lemma limitedPrimCodes_isSome (En Ed : CPoly R) (Iη₁ Iη₂ : RationalIntegral R)
    (A D : ℕ → CPoly R) (d : ℕ) :
    (limitedPrimCodes En Ed Iη₁ Iη₂ A D d).isSome = (limitedPrim En Ed Iη₁ Iη₂ A D d).isSome := by
  simp only [limitedPrimCodes, limitedPrim]
  cases primLoop En Ed Iη₁ A D d ([], [1]) with
  | none => rfl
  | some L =>
    simp only
    split <;> rename_i h <;> simp [h]

end Defs

variable {R S K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K] [Algebra S[X] K] [IsFractionRing S[X] K]
variable [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

lemma ev_addConst (ι : R →+* S) {q : CPoly R × CPoly R} (hq : toPoly q.2 ≠ 0) (c : R) :
    toPoly (addConst q c).2 ≠ 0 ∧ ev K ι (addConst q c) = ev K ι q + φ (C (ι c)) := by
  refine ⟨hq, ?_⟩
  have h := map_toPoly_ne_zero (K := K) ι hq
  simp only [ev, addConst, toPoly_add, toPoly_smul, Polynomial.map_add, Polynomial.map_mul, map_C,
    map_add, map_mul]
  field_simp

/-- **The coefficient codes solve the equations of levels `1 … k`.** -/
theorem primLoop_codes (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {En Ed : CPoly R} {Iη : RationalIntegral R} (hcη : rationalCheck En Ed Iη = true)
    (hEd : toPoly Ed ≠ 0) (A D : ℕ → CPoly R) (k : ℕ)
    (hD0 : ∀ j, 1 ≤ j → j ≤ k → toPoly (D j) ≠ 0) (Q : CPoly R × CPoly R)
    (hQ : toPoly Q.2 ≠ 0) {L : List (R × (CPoly R × CPoly R))}
    (hL : primLoop En Ed Iη A D k Q = some L) (b₁ : R) :
    (∀ j, 1 ≤ j → j ≤ k + 1 → toPoly (coeffFn (k + 1) Q L b₁ j).2 ≠ 0) ∧
      (∃ γ : R, ev K ι (coeffFn (k + 1) Q L b₁ (k + 1)) = ev K ι Q + φ (C (ι γ))) ∧
      (∀ j, 1 ≤ j → j ≤ k →
        (ev K ι (coeffFn (k + 1) Q L b₁ j))′ + ((j + 1 : ℕ) : K) * ev K ι (En, Ed) *
          ev K ι (coeffFn (k + 1) Q L b₁ (j + 1)) = ev K ι (A j, D j)) ∧
      ev K ι (coeffFn (k + 1) Q L b₁ 1) = ev K ι (primLastQ Q L) + φ (C (ι b₁)) := by
  induction k generalizing Q L with
  | zero =>
    simp only [primLoop, Option.some.injEq] at hL
    subst hL
    obtain ⟨h1, h2⟩ := ev_addConst (K := K) ι hQ b₁
    refine ⟨fun j hj1 hj2 ↦ ?_, ⟨b₁, ?_⟩, fun j hj1 hj2 ↦ by omega, ?_⟩
    · have : j = 1 := by omega
      subst this
      simpa [coeffFn] using h1
    · simpa [coeffFn] using h2
    · simpa [coeffFn, primLastQ] using h2
  | succ k ih =>
    simp only [primLoop] at hL
    cases hstep : primStep En Ed Iη (k + 1) (A (k + 1)) (D (k + 1)) Q with
    | none => rw [hstep] at hL; exact absurd hL (by simp)
    | some cQ =>
      obtain ⟨c, Q'⟩ := cQ
      rw [hstep] at hL
      simp only [Option.map_eq_some_iff] at hL
      obtain ⟨L', hL', rfl⟩ := hL
      obtain ⟨hQ', hsol⟩ := primStep_sound (K := K) ι hD hcη hEd (hD0 (k + 1) (by omega) le_rfl)
        hQ hstep
      obtain ⟨hden, ⟨γ', hγ'⟩, hpe, hp1⟩ := ih (fun j h1 h2 ↦ hD0 j h1 (by omega)) Q' hQ' hL'
      obtain ⟨hA1, hA2⟩ := ev_addConst (K := K) ι hQ (c / ((k + 1 + 1 : ℕ) : R))
      have htop : coeffFn (k + 1 + 1) Q ((c, Q') :: L') b₁ (k + 1 + 1) =
          addConst Q (c / ((k + 1 + 1 : ℕ) : R)) := by simp [coeffFn]
      have hlow : ∀ j, j ≤ k + 1 → coeffFn (k + 1 + 1) Q ((c, Q') :: L') b₁ j =
          coeffFn (k + 1) Q' L' b₁ j := fun j hj ↦ by
        simp only [coeffFn, Nat.add_sub_cancel]
        rw [if_neg (by omega)]
      have hγc : ((k + 1 + 1 : ℕ) : K) * φ (C (ι (c / ((k + 1 + 1 : ℕ) : R)))) = φ (C (ι c)) := by
        have hn : (((k + 1 + 1 : ℕ) : K)) = φ (C (ι (((k + 1 + 1 : ℕ) : R)))) := by
          rw [map_natCast ι, map_natCast (C : S →+* S[X]), map_natCast]
        rw [hn, ← map_mul, ← C_mul, ← map_mul,
          mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega) : (((k + 1 + 1 : ℕ) : R)) ≠ 0)]
      have hcγ' : (φ (C (ι γ')))′ = 0 := by rw [deriv_algebraMap, hD, derivative_C, map_zero]
      refine ⟨fun j hj1 hj2 ↦ ?_, ⟨_, by rw [htop]; exact hA2⟩, fun j hj1 hj2 ↦ ?_, ?_⟩
      · rcases Nat.eq_or_lt_of_le hj2 with rfl | hlt
        · rw [htop]; exact hA1
        · rw [hlow j (by omega)]; exact hden j hj1 (by omega)
      · rcases Nat.eq_or_lt_of_le hj2 with rfl | hlt
        · rw [hlow (k + 1) le_rfl, htop, hγ', hA2, map_add, hcγ', add_zero, hsol]
          linear_combination ev K ι (En, Ed) * hγc
        · rw [hlow j (by omega), hlow (j + 1) (by omega)]
          exact hpe j hj1 (by omega)
      · rw [hlow 1 (by omega)]
        exact hp1

lemma ev_Gfrac (ι : R →+* S) {I : RationalIntegral R} (hgd : toPoly I.gd ≠ 0) :
    toPoly (Gfrac I).2 ≠ 0 ∧ ev K ι (Gfrac I) =
      φ ((toPoly I.gn).map ι) / φ ((toPoly I.gd).map ι) + φ ((toPoly I.Q).map ι) := by
  refine ⟨hgd, ?_⟩
  have h := map_toPoly_ne_zero (K := K) ι hgd
  simp only [ev, Gfrac, toPoly_add, toPoly_mul, Polynomial.map_add, Polynomial.map_mul, map_add,
    map_mul]
  field_simp

lemma ev_fsub (ι : R →+* S) {q₁ q₂ : CPoly R × CPoly R} (h₁ : toPoly q₁.2 ≠ 0)
    (h₂ : toPoly q₂.2 ≠ 0) :
    toPoly (fsub q₁ q₂).2 ≠ 0 ∧ ev K ι (fsub q₁ q₂) = ev K ι q₁ - ev K ι q₂ := by
  refine ⟨by simp only [fsub, toPoly_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
  have h1 := map_toPoly_ne_zero (K := K) ι h₁
  have h2 := map_toPoly_ne_zero (K := K) ι h₂
  simp only [ev, fsub, toPoly_sub, toPoly_mul, Polynomial.map_sub, Polynomial.map_mul, map_sub,
    map_mul]
  field_simp

lemma ev_fsmul (ι : R →+* S) (c : R) (q : CPoly R × CPoly R) :
    ev K ι (fsmul c q) = φ (C (ι c)) * ev K ι q := by
  simp only [ev, fsmul, toPoly_smul, Polynomial.map_mul, map_C, map_mul]
  ring

/-- The derivative of the level-`0` code. -/
theorem deriv_ev_level0 (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {gn gd En₁ Ed₁ En₂ Ed₂ : CPoly R} {I Iη₁ Iη₂ : RationalIntegral R}
    (hI : rationalCheck gn gd I = true) (hc₁ : rationalCheck En₁ Ed₁ Iη₁ = true)
    (hc₂ : rationalCheck En₂ Ed₂ Iη₂ = true) (b c : R)
    (hfrac : φ ((toPoly I.r).map ι) / φ ((toPoly I.s).map ι) =
      φ (C (ι b)) * (φ ((toPoly Iη₁.r).map ι) / φ ((toPoly Iη₁.s).map ι)) +
        φ (C (ι c)) * (φ ((toPoly Iη₂.r).map ι) / φ ((toPoly Iη₂.s).map ι))) :
    toPoly (level0 I Iη₁ Iη₂ b c).2 ≠ 0 ∧
      (ev K ι (level0 I Iη₁ Iη₂ b c))′ = ev K ι (gn, gd) - φ (C (ι b)) * ev K ι (En₁, Ed₁) -
        φ (C (ι c)) * ev K ι (En₂, Ed₂) := by
  obtain ⟨hGI0, hGI⟩ := ev_Gfrac (K := K) ι (gd_ne_zero_of_rationalCheck hI)
  obtain ⟨hG₁0, hG₁⟩ := ev_Gfrac (K := K) ι (gd_ne_zero_of_rationalCheck hc₁)
  obtain ⟨hG₂0, hG₂⟩ := ev_Gfrac (K := K) ι (gd_ne_zero_of_rationalCheck hc₂)
  obtain ⟨hs1, he1⟩ := ev_fsub (K := K) ι (q₁ := Gfrac I) (q₂ := fsmul b (Gfrac Iη₁)) hGI0 hG₁0
  obtain ⟨hs2, he2⟩ := ev_fsub (K := K) ι (q₁ := fsub (Gfrac I) (fsmul b (Gfrac Iη₁)))
    (q₂ := fsmul c (Gfrac Iη₂)) hs1 hG₂0
  refine ⟨hs2, ?_⟩
  obtain ⟨hdecI, -, -⟩ := rationalCheck_sound_map (K := K) ι hD gn gd I hI
  obtain ⟨hdec₁, -, -⟩ := rationalCheck_sound_map (K := K) ι hD En₁ Ed₁ Iη₁ hc₁
  obtain ⟨hdec₂, -, -⟩ := rationalCheck_sound_map (K := K) ι hD En₂ Ed₂ Iη₂ hc₂
  have hcb : (φ (C (ι b)))′ = 0 := by rw [deriv_algebraMap, hD, derivative_C, map_zero]
  have hcc : (φ (C (ι c)))′ = 0 := by rw [deriv_algebraMap, hD, derivative_C, map_zero]
  rw [level0, he2, he1, ev_fsmul, ev_fsmul, hGI, hG₁, hG₂, deriv_sub', deriv_sub',
    Derivation.leibniz, Derivation.leibniz, hcb, hcc]
  simp only [ev, smul_eq_mul, mul_zero, add_zero]
  rw [hdecI, hdec₁, hdec₂, hfrac]
  ring

lemma primLastQ_den_ne_zero (K : Type*) [Field K] [Algebra S[X] K] [IsFractionRing S[X] K]
    [Differential K] [DifferentialAlgebra S[X] K] (ι : R →+* S)
    (hD : ∀ P : S[X], (P′ : S[X]) = derivative P)
    {En Ed : CPoly R} {Iη : RationalIntegral R} (hcη : rationalCheck En Ed Iη = true)
    (hEd : toPoly Ed ≠ 0) (A D : ℕ → CPoly R) :
    ∀ (k : ℕ) (Q : CPoly R × CPoly R) (L : List (R × (CPoly R × CPoly R))),
      (∀ j, 1 ≤ j → j ≤ k → toPoly (D j) ≠ 0) → toPoly Q.2 ≠ 0 →
      primLoop En Ed Iη A D k Q = some L → toPoly (primLastQ Q L).2 ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro Q L _ hQ hL
    simp only [primLoop, Option.some.injEq] at hL
    subst hL
    exact hQ
  | succ k ih =>
    intro Q L hD0' hQ hL
    simp only [primLoop] at hL
    cases hstep : primStep En Ed Iη (k + 1) (A (k + 1)) (D (k + 1)) Q with
    | none => rw [hstep] at hL; exact absurd hL (by simp)
    | some cQ =>
      rw [hstep] at hL
      simp only [Option.map_eq_some_iff] at hL
      obtain ⟨L', hL', rfl⟩ := hL
      obtain ⟨hQ', -⟩ := primStep_sound (K := K) ι hD hcη hEd
        (hD0' (k + 1) (by omega) le_rfl) hQ (c := cQ.1) (Q' := cQ.2) hstep
      exact ih cQ.2 L' (fun j h1 h2 ↦ hD0' j h1 (by omega)) hQ' hL'

/-- **Soundness of the codes.** -/
theorem limitedPrimCodes_sound (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {En Ed En₂ Ed₂ : CPoly R} {Iη₁ Iη₂ : RationalIntegral R}
    (hcη₁ : rationalCheck En Ed Iη₁ = true) (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true)
    (hEd : toPoly Ed ≠ 0) (A D : ℕ → CPoly R) (d : ℕ)
    (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) {c : R} {P : ℕ → CPoly R × CPoly R}
    (h : limitedPrimCodes En Ed Iη₁ Iη₂ A D d = some (c, P)) :
    (∀ j ≤ d + 1, toPoly (P j).2 ≠ 0) ∧
      (∀ j, 1 ≤ j → j ≤ d → (ev K ι (P j))′ + ((j + 1 : ℕ) : K) * ev K ι (En, Ed) *
        ev K ι (P (j + 1)) = ev K ι (A j, D j)) ∧
      (ev K ι (P 0))′ + ev K ι (En, Ed) * ev K ι (P 1) =
        ev K ι (A 0, D 0) - φ (C (ι c)) * ev K ι (En₂, Ed₂) ∧
      (ev K ι (P (d + 1)))′ = 0 := by
  simp only [limitedPrimCodes] at h
  cases hL : primLoop En Ed Iη₁ A D d ([], [1]) with
  | none => rw [hL] at h; exact absurd h (by simp)
  | some L =>
    rw [hL] at h
    simp only at h
    have hlast := primLastQ_den_ne_zero K ι hD hcη₁ hEd A D d _ L
      (fun j _ hj ↦ hD0 j hj) (by simp) hL
    set Q₁ := primLastQ ([], [1]) L with hQ₁
    obtain ⟨hg0, hg⟩ := ev_primG (K := K) ι (En := En) (An := A 0) 0 hEd (hD0 0 (Nat.zero_le d))
      hlast
    set g := primG En Ed 0 (A 0) (D 0) Q₁ with hgdef
    set I := integrateRational g.1 g.2 with hI
    have hIc : rationalCheck g.1 g.2 I = true := rationalCheck_integrateRational _ _ hg0
    cases hcs : limitedCritN I.r I.s [(Iη₁.r, Iη₁.s), (Iη₂.r, Iη₂.s)] with
    | none => rw [hcs] at h; exact absurd h (by simp)
    | some cs =>
      rw [hcs] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hdecI, hsqI, hdegI⟩ := rationalCheck_sound_map (K := K) ι hD g.1 g.2 I hIc
      obtain ⟨hdec₁, hsq₁, hdeg₁⟩ := rationalCheck_sound_map (K := K) ι hD En Ed Iη₁ hcη₁
      obtain ⟨hdec₂, hsq₂, hdeg₂⟩ := rationalCheck_sound_map (K := K) ι hD En₂ Ed₂ Iη₂ hcη₂
      have hfrac := limitedCritN_frac (K := K) ι hD hsqI hdegI
        (ηs := [(Iη₁.r, Iη₁.s), (Iη₂.r, Iη₂.s)])
        (fun η hη ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hη
          rcases hη with rfl | rfl
          · exact ⟨hsq₁, hdeg₁⟩
          · exact ⟨hsq₂, hdeg₂⟩) hcs
      erw [Fin.sum_univ_two] at hfrac
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, List.getElem_cons_zero,
        List.getElem_cons_succ, Fin.getElem_fin] at hfrac
      obtain ⟨h0den, h0der⟩ := deriv_ev_level0 (K := K) ι hD hIc hcη₁ hcη₂ (cs.getD 0 0)
        (cs.getD 1 0) hfrac
      obtain ⟨hden, ⟨γ, hγ⟩, hpe, hp1⟩ := primLoop_codes (K := K) ι hD hcη₁ hEd A D d
        (fun j _ hj ↦ hD0 j hj) ([], [1]) (by simp) hL (cs.getD 0 0)
      have hγ0 : (φ (C (ι γ)))′ = 0 := by rw [deriv_algebraMap, hD, derivative_C, map_zero]
      refine ⟨fun j hj ↦ ?_, fun j h1 h2 ↦ ?_, ?_, ?_⟩
      · by_cases hj0 : j = 0
        · simp only [hj0, if_true]; exact h0den
        · simp only [if_neg hj0]; exact hden j (by omega) hj
      · simp only [if_neg (by omega : ¬j = 0), if_neg (by omega : ¬j + 1 = 0)]
        exact hpe j h1 h2
      · simp only [if_true, if_neg (by omega : ¬(1 : ℕ) = 0)]
        rw [h0der, hp1]
        have hgE : ev K ι (g.1, g.2) = ev K ι g := rfl
        rw [hgE, hg]
        simp only [Nat.cast_one, zero_add, one_mul]
        ring
      · simp only [if_neg (by omega : ¬d + 1 = 0)]
        rw [hγ, map_add, hγ0, add_zero]
        simp [ev]

end CPoly
