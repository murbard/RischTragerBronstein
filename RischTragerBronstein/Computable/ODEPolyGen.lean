import RischTragerBronstein.Computable.ODEPoly
import RischTragerBronstein.Computable.LimitedCrit

/-!
# `P₁ Y′ + P₀ Y = A` over polynomials, general degrees

`odeSolve` requires `deg P₁ ≤ deg P₀`. For the Risch differential equation with a rational
coefficient one meets `deg P₀ = deg P₁ - 1` (or smaller), where the pivot
`piv k = k lc(P₁) [+ lc(P₀)]` of the triangular system vanishes for one exponent `k₀`. The
coefficient of `x ^ k₀` is then a free parameter `λ`:

* `odeLoopGen` eliminates from the top, carrying a particular track `(Y, Rm)` and, after the zero
  pivot, a homogeneous track `(Yh, Rh)`;
* `odeSolveGen` finally solves `Rm + λ Rh = 0` for the constant `λ` (`limitedCrit`).

`odeSolveGen_sound`: a returned `Y` satisfies `P₁ Y′ + P₀ Y = A`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

/-- State of the general loop: particular track and optional homogeneous track. -/
structure OdeState (R : Type*) where
  /-- particular solution so far -/
  Y : CPoly R
  /-- `A - Op Y` -/
  Rm : CPoly R
  /-- homogeneous track `(Yh, -Op Yh)`, once a zero pivot has been met -/
  hom : Option (CPoly R × CPoly R)

/-- One elimination step at exponent `k`, pivot `pv`, top degree offset `dg`. -/
def odeStepGen (P₁ P₀ : CPoly R) (dg k : ℕ) (pv : R) (st : OdeState R) : OdeState R :=
  if pv = 0 then
    match st.hom with
    | none => ⟨st.Y, st.Rm, some (monomial k 1, neg (odeOp P₁ P₀ (monomial k 1)))⟩
    | some _ => st
  else
    let m := monomial k (st.Rm.getD (k + dg) 0 / pv)
    let hom' := st.hom.map fun yh ↦
      let mh := monomial k (yh.2.getD (k + dg) 0 / pv)
      (add yh.1 mh, sub yh.2 (odeOp P₁ P₀ mh))
    ⟨add st.Y m, sub st.Rm (odeOp P₁ P₀ m), hom'⟩

/-- Eliminate exponents `k - 1, …, 0` with the pivot function `piv`. -/
def odeLoopGen (P₁ P₀ : CPoly R) (dg : ℕ) (piv : ℕ → R) : ℕ → OdeState R → OdeState R
  | 0, st => st
  | k + 1, st => odeLoopGen P₁ P₀ dg piv k (odeStepGen P₁ P₀ dg k (piv k) st)

/-- Decide `P₁ Y′ + P₀ Y = A` with pivots `piv`, exponents below `N`. -/
def odeSolveGen (P₁ P₀ A : CPoly R) (dg : ℕ) (piv : ℕ → R) (N : ℕ) : Option (CPoly R) :=
  let st := odeLoopGen P₁ P₀ dg piv N ⟨[], A, none⟩
  match st.hom with
  | none => if isZero st.Rm then some (trim st.Y) else none
  | some yh =>
    -- `Rm + λ Rh = 0`
    match limitedCrit st.Rm [1] (neg yh.2) [1] with
    | none => none
    | some c => some (trim (add st.Y (smul c yh.1)))

/-- The invariant of the loop. -/
def OdeInv (P₁ P₀ A : CPoly R) (st : OdeState R) : Prop :=
  toPoly st.Rm = toPoly A - toPoly (odeOp P₁ P₀ st.Y) ∧
    ∀ yh, st.hom = some yh → toPoly yh.2 = -toPoly (odeOp P₁ P₀ yh.1)

lemma odeStepGen_inv (P₁ P₀ A : CPoly R) (dg k : ℕ) (pv : R) (st : OdeState R)
    (h : OdeInv P₁ P₀ A st) : OdeInv P₁ P₀ A (odeStepGen P₁ P₀ dg k pv st) := by
  obtain ⟨h1, h2⟩ := h
  unfold odeStepGen
  split_ifs with hpv
  · cases hh : st.hom with
    | none =>
      refine ⟨h1, fun yh hyh ↦ ?_⟩
      simp only [Option.some.injEq] at hyh
      rw [← hyh]
      simp [neg, toPoly_smul]
    | some yh0 => exact ⟨h1, fun yh hyh ↦ h2 yh (by rw [← hyh, hh])⟩
  · refine ⟨?_, fun yh hyh ↦ ?_⟩
    · simp only [toPoly_sub, toPoly_odeOp, toPoly_add, derivative_add, h1]
      ring
    · simp only [Option.map_eq_some_iff] at hyh
      obtain ⟨yh0, hyh0, rfl⟩ := hyh
      have := h2 yh0 hyh0
      simp only [toPoly_sub, toPoly_odeOp, toPoly_add, derivative_add] at this ⊢
      rw [this]
      ring

lemma odeLoopGen_inv (P₁ P₀ A : CPoly R) (dg : ℕ) (piv : ℕ → R) (k : ℕ) (st : OdeState R)
    (h : OdeInv P₁ P₀ A st) : OdeInv P₁ P₀ A (odeLoopGen P₁ P₀ dg piv k st) := by
  induction k generalizing st with
  | zero => exact h
  | succ k ih => exact ih _ (odeStepGen_inv P₁ P₀ A dg k (piv k) st h)

/-- **Soundness.** -/
theorem odeSolveGen_sound {P₁ P₀ A Y : CPoly R} {dg : ℕ} {piv : ℕ → R} {N : ℕ}
    (h : odeSolveGen P₁ P₀ A dg piv N = some Y) :
    toPoly P₁ * derivative (toPoly Y) + toPoly P₀ * toPoly Y = toPoly A := by
  have hinv := odeLoopGen_inv P₁ P₀ A dg piv N ⟨[], A, none⟩
    ⟨by simp [odeOp], fun yh hyh ↦ by simp at hyh⟩
  simp only [odeSolveGen] at h
  set st := odeLoopGen P₁ P₀ dg piv N ⟨[], A, none⟩
  obtain ⟨h1, h2⟩ := hinv
  cases hh : st.hom with
  | none =>
    rw [hh] at h
    simp only at h
    split_ifs at h with hz
    rw [(isZero_iff _).mp hz, toPoly_odeOp] at h1
    rw [← Option.some.inj h, toPoly_trim]
    exact (sub_eq_zero.mp h1.symm).symm
  | some yh =>
    rw [hh] at h
    simp only at h
    cases hc : limitedCrit st.Rm [1] (neg yh.2) [1] with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some c =>
      rw [hc] at h
      have hs := limitedCrit_sound hc
      have hyh := h2 yh hh
      rw [← Option.some.inj h, toPoly_trim, toPoly_add, toPoly_smul, derivative_add,
        derivative_mul, derivative_C, zero_mul, zero_add]
      simp only [toPoly_odeOp, neg, toPoly_smul, toPoly_cons, toPoly_nil, mul_zero, add_zero,
        mul_one, C_1, C_neg, neg_mul, one_mul, mul_neg] at h1 hyh hs
      linear_combination h1 - hs + C c * hyh

/-! ### Completeness over extensions of the coefficient field -/

section Complete

variable {S : Type*} [Field S] [CharZero S] (ι : R →+* S)

/-- The operator over `S`. -/
noncomputable def opS (P₁ P₀ : CPoly R) (Y : S[X]) : S[X] :=
  (toPoly P₁).map ι * derivative Y + (toPoly P₀).map ι * Y

lemma opS_sub (P₁ P₀ : CPoly R) (Y Z : S[X]) :
    opS ι P₁ P₀ (Y - Z) = opS ι P₁ P₀ Y - opS ι P₁ P₀ Z := by
  simp only [opS, derivative_sub]; ring

lemma opS_C_mul (P₁ P₀ : CPoly R) (c : S) (Y : S[X]) :
    opS ι P₁ P₀ (C c * Y) = C c * opS ι P₁ P₀ Y := by
  simp only [opS, derivative_mul, derivative_C, zero_mul, zero_add]; ring

lemma opS_map (P₁ P₀ Y : CPoly R) :
    opS ι P₁ P₀ ((toPoly Y).map ι) = (toPoly (odeOp P₁ P₀ Y)).map ι := by
  simp only [opS, toPoly_odeOp, Polynomial.map_add, Polynomial.map_mul, derivative_map]

/-- The pivot: the coefficient of `x ^ (k + dg)` in `Op Z` for `deg Z ≤ k`. -/
lemma coeff_opS {P₁ P₀ : CPoly R} {dg : ℕ} (h1 : (toPoly P₁).natDegree ≤ dg + 1)
    (h0 : (toPoly P₀).natDegree ≤ dg) {Z : S[X]} {k : ℕ} (hZ : ∀ m, k < m → Z.coeff m = 0) :
    (opS ι P₁ P₀ Z).coeff (k + dg) =
      ι ((k : R) * (toPoly P₁).coeff (dg + 1) + (toPoly P₀).coeff dg) * Z.coeff k := by
  have hZd : Z.natDegree ≤ k := natDegree_le_iff_coeff_eq_zero.mpr hZ
  have hp1 : ((toPoly P₁).map ι).natDegree ≤ dg + 1 := natDegree_map_le.trans h1
  have hp0 : ((toPoly P₀).map ι).natDegree ≤ dg := natDegree_map_le.trans h0
  have hA : ((toPoly P₀).map ι * Z).coeff (k + dg) = ι ((toPoly P₀).coeff dg) * Z.coeff k := by
    rw [add_comm, coeff_mul_add_eq_of_natDegree_le hp0 hZd, coeff_map]
  have hB : ((toPoly P₁).map ι * derivative Z).coeff (k + dg) =
      ι ((k : R) * (toPoly P₁).coeff (dg + 1)) * Z.coeff k := by
    cases k with
    | zero =>
      rw [eq_C_of_natDegree_le_zero hZd, derivative_C, mul_zero, coeff_zero]
      simp
    | succ j =>
      have hd : (derivative Z).natDegree ≤ j := by
        have := natDegree_derivative_le Z
        omega
      rw [show j + 1 + dg = dg + 1 + j by ring, coeff_mul_add_eq_of_natDegree_le hp1 hd, coeff_map,
        coeff_derivative, map_mul, map_natCast]
      push_cast
      ring
  rw [opS, coeff_add, hA, hB, RingHom.map_add]
  ring

/-- The completeness invariant at stage `k`. -/
def OdeCInv (P₁ P₀ : CPoly R) (piv : ℕ → R) (Ys : S[X]) (k : ℕ) (st : OdeState R) : Prop :=
  (st.hom = none → ∀ m, k ≤ m → (Ys - (toPoly st.Y).map ι).coeff m = 0) ∧
    ∀ yh, st.hom = some yh → (∃ k', k ≤ k' ∧ piv k' = 0) ∧ ∃ l : S, ∀ m, k ≤ m →
      (Ys - (toPoly st.Y).map ι - C l * (toPoly yh.1).map ι).coeff m = 0

lemma coeff_monomial_map (k : ℕ) (c : R) (m : ℕ) :
    ((toPoly (monomial k c)).map ι).coeff m = if m = k then ι c else 0 := by
  rw [toPoly_monomial, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, coeff_C_mul,
    coeff_X_pow]
  split_ifs <;> simp

lemma odeStepGen_cinv {P₁ P₀ A : CPoly R} {dg : ℕ} {piv : ℕ → R}
    (h1 : (toPoly P₁).natDegree ≤ dg + 1) (h0 : (toPoly P₀).natDegree ≤ dg)
    (hpiv : ∀ k, piv k = (k : R) * (toPoly P₁).coeff (dg + 1) + (toPoly P₀).coeff dg)
    (huniq : ∀ k k', piv k = 0 → piv k' = 0 → k = k')
    {Ys : S[X]} (hYs : opS ι P₁ P₀ Ys = (toPoly A).map ι) (k : ℕ) (st : OdeState R)
    (hinv : OdeInv P₁ P₀ A st) (hc : OdeCInv ι P₁ P₀ piv Ys (k + 1) st) :
    OdeCInv ι P₁ P₀ piv Ys k (odeStepGen P₁ P₀ dg k (piv k) st) := by
  obtain ⟨hi1, hi2⟩ := hinv
  obtain ⟨hc1, hc2⟩ := hc
  have hRm : (toPoly st.Rm).map ι = opS ι P₁ P₀ Ys - opS ι P₁ P₀ ((toPoly st.Y).map ι) := by
    rw [hi1, Polynomial.map_sub, hYs, opS_map]
  unfold odeStepGen
  cases hh : st.hom with
  | none =>
    have hZ := hc1 hh
    set Z := Ys - (toPoly st.Y).map ι with hZdef
    have hop : opS ι P₁ P₀ Z = (toPoly st.Rm).map ι := by rw [hZdef, opS_sub, hRm]
    have hco := coeff_opS ι h1 h0 (Z := Z) (k := k) fun m hm ↦ hZ m hm
    rw [hop, coeff_map, coeff_toPoly, ← hpiv] at hco
    split_ifs with hpv
    · -- zero pivot: start the homogeneous track
      refine ⟨fun hn ↦ by simp [hh] at hn, fun yh hyh ↦ ?_⟩
      simp only [hh, Option.some.injEq] at hyh
      subst hyh
      refine ⟨⟨k, le_rfl, hpv⟩, Z.coeff k, fun m hm ↦ ?_⟩
      rw [coeff_sub, coeff_C_mul, coeff_monomial_map]
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · rw [if_pos rfl, map_one, mul_one]
        exact sub_self _
      · rw [if_neg (by omega), hZ m hlt]; simp
    · refine ⟨fun _ m hm ↦ ?_, fun yh hyh ↦ by simp [hh] at hyh⟩
      simp only [toPoly_add, Polynomial.map_add]
      rw [← sub_sub, coeff_sub, coeff_monomial_map]
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · rw [if_pos rfl, map_div₀, hco]
        have : ι (piv k) ≠ 0 := (map_ne_zero ι).mpr hpv
        field_simp
        ring
      · rw [if_neg (by omega), hZ m hlt, sub_zero]
  | some yh =>
    obtain ⟨⟨k', hk', hpk'⟩, l, hZ⟩ := hc2 yh hh
    have hpv : piv k ≠ 0 := fun h ↦ by
      have := huniq k k' h hpk'
      omega
    rw [if_neg hpv]
    have hRh : (toPoly yh.2).map ι = -opS ι P₁ P₀ ((toPoly yh.1).map ι) := by
      rw [hi2 yh hh, Polynomial.map_neg, opS_map]
    set Z := Ys - (toPoly st.Y).map ι - C l * (toPoly yh.1).map ι with hZdef
    have hop : opS ι P₁ P₀ Z = (toPoly st.Rm).map ι + C l * (toPoly yh.2).map ι := by
      rw [hZdef, opS_sub, opS_sub, opS_C_mul, hRm, hRh]
      ring
    have hco := coeff_opS ι h1 h0 (Z := Z) (k := k) fun m hm ↦ hZ m hm
    rw [hop, coeff_add, coeff_C_mul, coeff_map, coeff_map, coeff_toPoly, coeff_toPoly,
      ← hpiv] at hco
    refine ⟨fun hn ↦ by simp at hn, fun yh' hyh' ↦ ?_⟩
    simp only [Option.map_some, Option.some.injEq] at hyh'
    subst hyh'
    refine ⟨⟨k', by omega, hpk'⟩, l, fun m hm ↦ ?_⟩
    simp only [toPoly_add, Polynomial.map_add]
    have hexp : Ys - ((toPoly st.Y).map ι + (toPoly (monomial k (st.Rm.getD (k + dg) 0 / piv k))).map ι) -
        C l * ((toPoly yh.1).map ι + (toPoly (monomial k (yh.2.getD (k + dg) 0 / piv k))).map ι) =
        Z - (toPoly (monomial k (st.Rm.getD (k + dg) 0 / piv k))).map ι -
          C l * (toPoly (monomial k (yh.2.getD (k + dg) 0 / piv k))).map ι := by
      rw [hZdef]; ring
    rw [hexp, coeff_sub, coeff_sub, coeff_C_mul, coeff_monomial_map, coeff_monomial_map]
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · rw [if_pos rfl, if_pos rfl, map_div₀, map_div₀]
      have : ι (piv k) ≠ 0 := (map_ne_zero ι).mpr hpv
      field_simp
      linear_combination -hco
    · rw [if_neg (by omega), if_neg (by omega), hZ m hlt]; simp
lemma odeLoopGen_cinv {P₁ P₀ A : CPoly R} {dg : ℕ} {piv : ℕ → R}
    (h1 : (toPoly P₁).natDegree ≤ dg + 1) (h0 : (toPoly P₀).natDegree ≤ dg)
    (hpiv : ∀ k, piv k = (k : R) * (toPoly P₁).coeff (dg + 1) + (toPoly P₀).coeff dg)
    (huniq : ∀ k k', piv k = 0 → piv k' = 0 → k = k')
    {Ys : S[X]} (hYs : opS ι P₁ P₀ Ys = (toPoly A).map ι) (k : ℕ) (st : OdeState R)
    (hinv : OdeInv P₁ P₀ A st) (hc : OdeCInv ι P₁ P₀ piv Ys k st) :
    OdeCInv ι P₁ P₀ piv Ys 0 (odeLoopGen P₁ P₀ dg piv k st) := by
  induction k generalizing st with
  | zero => exact hc
  | succ k ih =>
    exact ih _ (odeStepGen_inv P₁ P₀ A dg k (piv k) st hinv)
      (odeStepGen_cinv ι h1 h0 hpiv huniq hYs k st hinv hc)

/-- **Completeness.** If `P₁ Y′ + P₀ Y = A` has a polynomial solution of degree `< N` over an
extension `S` of the coefficient field, the solver succeeds. -/
theorem odeSolveGen_complete_map {P₁ P₀ A : CPoly R} {dg : ℕ} {piv : ℕ → R} {N : ℕ}
    (h1 : (toPoly P₁).natDegree ≤ dg + 1) (h0 : (toPoly P₀).natDegree ≤ dg)
    (hpiv : ∀ k, piv k = (k : R) * (toPoly P₁).coeff (dg + 1) + (toPoly P₀).coeff dg)
    (huniq : ∀ k k', piv k = 0 → piv k' = 0 → k = k')
    (Ys : S[X]) (hYs : (toPoly P₁).map ι * derivative Ys + (toPoly P₀).map ι * Ys =
      (toPoly A).map ι) (hN : Ys.natDegree < N) :
    odeSolveGen P₁ P₀ A dg piv N ≠ none := by
  have hinv0 : OdeInv P₁ P₀ A ⟨[], A, none⟩ :=
    ⟨by simp [odeOp], fun yh hyh ↦ by simp at hyh⟩
  have hc0 : OdeCInv ι P₁ P₀ piv Ys N ⟨[], A, none⟩ := by
    refine ⟨fun _ m hm ↦ ?_, fun yh hyh ↦ by simp at hyh⟩
    rw [toPoly_nil, Polynomial.map_zero, sub_zero]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hN hm)
  have hinv := odeLoopGen_inv P₁ P₀ A dg piv N _ hinv0
  have hc := odeLoopGen_cinv ι h1 h0 hpiv huniq (Ys := Ys) hYs N _ hinv0 hc0
  simp only [odeSolveGen]
  set st := odeLoopGen P₁ P₀ dg piv N ⟨[], A, none⟩
  obtain ⟨hi1, hi2⟩ := hinv
  obtain ⟨hc1, hc2⟩ := hc
  have hRm : (toPoly st.Rm).map ι = opS ι P₁ P₀ Ys - opS ι P₁ P₀ ((toPoly st.Y).map ι) := by
    rw [hi1, Polynomial.map_sub, opS_map]
    congr 1
    exact hYs.symm
  cases hh : st.hom with
  | none =>
    have hZ : Ys - (toPoly st.Y).map ι = 0 := by
      ext m; simpa using hc1 hh m (Nat.zero_le m)
    have hz : toPoly st.Rm = 0 := by
      rw [← Polynomial.map_eq_zero_iff ι.injective, hRm, ← opS_sub, hZ]
      simp [opS]
    simp only
    rw [if_pos ((isZero_iff _).mpr hz)]
    exact Option.some_ne_none _
  | some yh =>
    obtain ⟨-, l, hZ⟩ := hc2 yh hh
    have hZ0 : Ys - (toPoly st.Y).map ι - C l * (toPoly yh.1).map ι = 0 := by
      ext m; simpa using hZ m (Nat.zero_le m)
    have hRh : (toPoly yh.2).map ι = -opS ι P₁ P₀ ((toPoly yh.1).map ι) := by
      rw [hi2 yh hh, Polynomial.map_neg, opS_map]
    have hop : opS ι P₁ P₀ (Ys - (toPoly st.Y).map ι - C l * (toPoly yh.1).map ι) = 0 := by
      rw [hZ0]; simp [opS]
    rw [opS_sub, opS_sub, opS_C_mul] at hop
    have hrel : (toPoly st.Rm).map ι * (toPoly ([1] : CPoly R)).map ι =
        C l * (toPoly (neg yh.2)).map ι * (toPoly ([1] : CPoly R)).map ι := by
      simp only [neg, toPoly_smul, toPoly_cons, toPoly_nil, mul_zero, add_zero, C_1,
        Polynomial.map_one, mul_one, Polynomial.map_mul, Polynomial.map_neg, C_neg, neg_mul,
        one_mul, hRm, hRh]
      linear_combination hop
    obtain ⟨c₀, hc₀⟩ := limited_descent ι hrel
    simp only
    cases hcrit : limitedCrit st.Rm [1] (neg yh.2) [1] with
    | none => exact absurd ⟨c₀, hc₀⟩ (limitedCrit_complete hcrit)
    | some c => exact Option.some_ne_none _

/-- **Degree bound.** Beyond the zero pivots, the degree of a solution is bounded by
`deg A - dg`. -/
theorem natDegree_le_of_opS {P₁ P₀ A : CPoly R} {dg : ℕ} {piv : ℕ → R}
    (h1 : (toPoly P₁).natDegree ≤ dg + 1) (h0 : (toPoly P₀).natDegree ≤ dg)
    (hpiv : ∀ k, piv k = (k : R) * (toPoly P₁).coeff (dg + 1) + (toPoly P₀).coeff dg)
    {kb : ℕ} (hkb : ∀ k, kb < k → piv k ≠ 0) (Ys : S[X])
    (hYs : opS ι P₁ P₀ Ys = (toPoly A).map ι) :
    Ys.natDegree ≤ max ((toPoly A).natDegree - dg) kb := by
  by_contra hlt
  rw [not_le, max_lt_iff] at hlt
  obtain ⟨hA, hk⟩ := hlt
  have hY0 : Ys ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hk; omega
  have hco := coeff_opS ι h1 h0 (Z := Ys) (k := Ys.natDegree)
    fun m hm ↦ coeff_eq_zero_of_natDegree_lt hm
  rw [hYs, ← hpiv, coeff_map, coeff_eq_zero_of_natDegree_lt (by omega), map_zero] at hco
  rcases mul_eq_zero.mp hco.symm with h | h
  · exact hkb _ hk ((map_eq_zero ι).mp h)
  · exact hY0 (leadingCoeff_eq_zero.mp h)

end Complete

/-! ### The packaged solver -/

/-- `max (deg P₁ - 1) (deg P₀)`. -/
def odeDg (P₁ P₀ : CPoly R) : ℕ := max ((trim P₁).length - 2) ((trim P₀).length - 1)

/-- The pivot `k ↦ k lc₁ + lc₀`. -/
def odePiv (P₁ P₀ : CPoly R) (k : ℕ) : R :=
  (k : R) * P₁.getD (odeDg P₁ P₀ + 1) 0 + P₀.getD (odeDg P₁ P₀) 0

/-- Decide `P₁ Y′ + P₀ Y = A` (`P₀ ≠ 0`), given a bound `kb` on the zero of the pivot. -/
def odeSolveFull (P₁ P₀ A : CPoly R) (kb : ℕ) : Option (CPoly R) :=
  odeSolveGen P₁ P₀ A (odeDg P₁ P₀) (odePiv P₁ P₀)
    (max ((trim A).length - 1 - odeDg P₁ P₀) kb + 1)

lemma natDegree_toPoly_le (P : CPoly R) : (toPoly P).natDegree ≤ (trim P).length - 1 := by
  by_cases hP : trim P = []
  · rw [(trim_eq_nil_iff P).mp hP, natDegree_zero]; exact Nat.zero_le _
  · exact (natDegree_toPoly_of_trim_ne_nil hP).1.le

theorem odeSolveFull_sound {P₁ P₀ A Y : CPoly R} {kb : ℕ}
    (h : odeSolveFull P₁ P₀ A kb = some Y) :
    toPoly P₁ * derivative (toPoly Y) + toPoly P₀ * toPoly Y = toPoly A :=
  odeSolveGen_sound h

section

variable {S : Type*} [Field S] [CharZero S] (ι : R →+* S)

/-- **Completeness of the packaged solver**, over every extension of the coefficient field. -/
theorem odeSolveFull_complete_map {P₁ P₀ A : CPoly R} {kb : ℕ} (hP₀ : trim P₀ ≠ [])
    (hkb : ∀ k, odePiv P₁ P₀ k = 0 → k ≤ kb) (h : odeSolveFull P₁ P₀ A kb = none) :
    ¬∃ Ys : S[X], (toPoly P₁).map ι * derivative Ys + (toPoly P₀).map ι * Ys =
      (toPoly A).map ι := by
  rintro ⟨Ys, hYs⟩
  set dg := odeDg P₁ P₀ with hdg
  have h1 : (toPoly P₁).natDegree ≤ dg + 1 := by
    have := natDegree_toPoly_le P₁
    have : (trim P₁).length - 2 ≤ dg := le_max_left _ _
    omega
  have h0 : (toPoly P₀).natDegree ≤ dg := (natDegree_toPoly_le P₀).trans (le_max_right _ _)
  have hpiv : ∀ k, odePiv P₁ P₀ k =
      (k : R) * (toPoly P₁).coeff (dg + 1) + (toPoly P₀).coeff dg := fun k ↦ by
    rw [odePiv, coeff_toPoly, coeff_toPoly]
  obtain ⟨hd₀, hlc₀, hlc₀0⟩ := natDegree_toPoly_of_trim_ne_nil hP₀
  -- the pivot has at most one zero
  have hab : (toPoly P₁).coeff (dg + 1) ≠ 0 ∨ (toPoly P₀).coeff dg ≠ 0 := by
    by_cases hcase : (trim P₁).length - 2 ≤ (trim P₀).length - 1
    · right
      rw [hdg, odeDg, max_eq_right hcase, hlc₀]
      exact hlc₀0
    · left
      have hP₁ : trim P₁ ≠ [] := fun h0' ↦ by rw [h0'] at hcase; simp at hcase
      obtain ⟨-, hlc₁, hlc₁0⟩ := natDegree_toPoly_of_trim_ne_nil hP₁
      have : dg + 1 = (trim P₁).length - 1 := by
        rw [hdg, odeDg, max_eq_left (by omega)]
        omega
      rw [this, hlc₁]
      exact hlc₁0
  have huniq : ∀ k k', odePiv P₁ P₀ k = 0 → odePiv P₁ P₀ k' = 0 → k = k' := by
    intro k k' hk hk'
    rw [hpiv] at hk hk'
    by_cases ha : (toPoly P₁).coeff (dg + 1) = 0
    · rw [ha, mul_zero, zero_add] at hk
      exact absurd hk (hab.resolve_left (not_not.mpr ha))
    · have : ((k : R) - k') * (toPoly P₁).coeff (dg + 1) = 0 := by linear_combination hk - hk'
      have := (mul_eq_zero.mp this).resolve_right ha
      exact_mod_cast sub_eq_zero.mp this
  have hbound := natDegree_le_of_opS ι h1 h0 hpiv (kb := kb)
    (fun k hk hz ↦ absurd (hkb k hz) (by omega)) Ys hYs
  have hA := natDegree_toPoly_le A
  refine odeSolveGen_complete_map ι h1 h0 hpiv huniq Ys hYs ?_ h
  have : max ((toPoly A).natDegree - dg) kb ≤ max ((trim A).length - 1 - dg) kb :=
    max_le_max (by omega) le_rfl
  omega

end

-- `x² Y′ - Y = -1 - x` … the equation behind `∫ e^{1/x} (…)`: here `x² Y′ + (x - 1) Y = x² - x … `
-- sanity check: `x Y′ - 2 Y = 0` has the solution family `λ x²`; with right-hand side `-2` : `Y = 1 + λ x²`
#eval odeSolveGen (R := ℚ) [0, 1] [-2] [-2] 0 (fun k ↦ (k : ℚ) - 2) 4
-- `x Y′ - 2 Y = x` : `Y = -x`
#eval odeSolveGen (R := ℚ) [0, 1] [-2] [0, 1] 0 (fun k ↦ (k : ℚ) - 2) 4
-- `x Y′ - 2 Y = x²` : no polynomial solution (`x² log x`)
#eval odeSolveGen (R := ℚ) [0, 1] [-2] [0, 0, 1] 0 (fun k ↦ (k : ℚ) - 2) 4

end CPoly
