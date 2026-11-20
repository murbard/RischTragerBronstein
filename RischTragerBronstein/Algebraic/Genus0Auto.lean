import RischTragerBronstein.Algebraic.Genus0Tower

/-!
# Towers over a genus-zero base, automatically

A tower of logarithms and exponentials over `Kc(x, y)`, `y² = q(x)` of genus zero, is described by
*input codes* (`ICode`): at level `0` pairs `(u, v)` of rational functions meaning `u(x) + v(x) y`,
above that fractions of polynomials in `tₘ` as for `Code`. Given a rational parametrisation
`x = P(t)/Q(t)`, `y = R(t)/S(t)` with `t′ ρ(t) = 1`, the translation `tr` substitutes at level `0`;
logarithmic levels `tₘ′ = η` become `.prim (ρ · tr η)` for the derivation rescaled by `1/t′`,
exponential levels keep their argument. `genus0_decides`: `certX`/`elemNX` on the translated data
decide `∫ A` in the original tower.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.Genus0Auto

open Tower Tower.PrimN Tower.NestP Tower.NestM Tower.NestX CPoly

/-- Input codes: `u(x) + v(x) y` at level `0`, fractions of polynomials in `tₘ` above. -/
def ICode : ℕ → Type
  | 0 => GFrac ℚ × GFrac ℚ
  | m + 1 => GFrac (ICode m)

/-- `Q ^ N`. -/
def powP (Q : CPoly ℚ) : ℕ → CPoly ℚ
  | 0 => [1]
  | N + 1 => mul Q (powP Q N)

/-- `Q(t)^N n(P(t)/Q(t))` (for `N ≥ length n`). -/
def homog (P Q : CPoly ℚ) : CPoly ℚ → ℕ → CPoly ℚ
  | [], _ => []
  | c :: t, N => add (smul c (powP Q N)) (mul P (homog P Q t (N - 1)))

/-- Substitution `x = P/Q` into a rational function. -/
def subst0 (P Q : CPoly ℚ) (u : GFrac ℚ) : GFrac ℚ :=
  (homog P Q u.1 (max u.1.length u.2.length), homog P Q u.2 (max u.1.length u.2.length))

/-- The base translation of `u(x) + v(x) y`, `y = R/S`. -/
def baseTr (P Q R S : CPoly ℚ) (c : GFrac ℚ × GFrac ℚ) : Code 1 :=
  let U : CPoly ℚ × CPoly ℚ := subst0 P Q c.1
  let V : CPoly ℚ × CPoly ℚ := subst0 P Q c.2
  ((add (mul (mul U.1 V.2) S) (mul (mul V.1 R) U.2) : CPoly ℚ), (mul (mul U.2 V.2) S : CPoly ℚ))

/-- The translation of input codes. -/
def tr (P Q R S : CPoly ℚ) : (m : ℕ) → ICode m → Code (m + 1)
  | 0, c => baseTr P Q R S c
  | m + 1, c => (c.1.map (tr P Q R S m), c.2.map (tr P Q R S m))

/-- Multiplication by a code of `ℚ(t)`. -/
def scal (c : Code 1) : (m : ℕ) → Code (m + 1) → Code (m + 1)
  | 0, q => ((mul (c.1 : CPoly ℚ) (q.1 : CPoly ℚ) : CPoly ℚ),
      (mul (c.2 : CPoly ℚ) (q.2 : CPoly ℚ) : CPoly ℚ))
  | m + 1, q => (q.1.map (scal c m), q.2)

/-- Well-formedness: the level-`0` denominators are non-zero. -/
def wfI : (m : ℕ) → ICode m → Bool
  | 0, c => !isZero c.1.2 && !isZero c.2.2
  | m + 1, c => c.1.all (wfI m) && c.2.all (wfI m)

/-- The kinds of the input tower: `tₘ′ = η` or `tₘ = exp a`. -/
inductive IKind (m : ℕ)
  | prim (η : ICode m)
  | exp (a : ICode m)

/-- The translated kinds. -/
def trK (P Q R S : CPoly ℚ) (ρ : Code 1) (m : ℕ) : IKind m → KindN m
  | .prim η => .prim (scal ρ m (tr P Q R S m η))
  | .exp a => .exp (tr P Q R S m a)

section Eval

variable (Kc : Type*) {E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc]
variable [Differential E] [DifferentialAlgebra Kc E] [CharZero Kc]

/-- The value of an input code. -/
noncomputable def evI (x y : E) (ts : ℕ → E) : (m : ℕ) → ICode m → E
  | 0, c => evx Kc x c.1 + evx Kc x c.2 * y
  | m + 1, c => (c.1.foldr (fun a acc ↦ evI x y ts m a + ts m * acc) 0) /
      (c.2.foldr (fun a acc ↦ evI x y ts m a + ts m * acc) 0)

/-- The kinds' derivatives in the input tower. -/
noncomputable def kderI (x y : E) (ts : ℕ → E) (m : ℕ) : IKind m → E
  | .prim η => evI Kc x y ts m η
  | .exp a => (evI Kc x y ts m a)′ * ts m

variable {Kc}

lemma aeval_powP (τ : E) (Q : CPoly ℚ) : ∀ N,
    aeval τ ((toPoly (powP Q N)).map (algebraMap ℚ Kc)) =
      aeval τ ((toPoly Q).map (algebraMap ℚ Kc)) ^ N
  | 0 => by simp [powP, CPoly.toPoly]
  | N + 1 => by
    rw [powP, toPoly_mul, Polynomial.map_mul, map_mul, aeval_powP τ Q N, pow_succ]; ring

lemma aeval_homog (τ : E) (P Q : CPoly ℚ)
    (hQ : aeval τ ((toPoly Q).map (algebraMap ℚ Kc)) ≠ 0) :
    ∀ (n : CPoly ℚ) (N : ℕ), n.length ≤ N →
      aeval τ ((toPoly (homog P Q n N)).map (algebraMap ℚ Kc)) =
        aeval τ ((toPoly Q).map (algebraMap ℚ Kc)) ^ N *
          aeval (aeval τ ((toPoly P).map (algebraMap ℚ Kc)) /
            aeval τ ((toPoly Q).map (algebraMap ℚ Kc))) ((toPoly n).map (algebraMap ℚ Kc))
  | [], N, _ => by simp [homog, CPoly.toPoly]
  | c :: t, N, h => by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at h; omega⟩
    have ih := aeval_homog τ P Q hQ t N' (by simp at h; omega)
    simp only [homog, toPoly_add, toPoly_smul, toPoly_mul, Polynomial.map_add, Polynomial.map_mul,
      map_C, map_add, map_mul, aeval_C, aeval_powP, toPoly_cons, aeval_X, Nat.add_sub_cancel] at ih ⊢
    rw [ih]
    simp only [Polynomial.map_X, aeval_X]
    field_simp
    ring

/-- The value of `P` at `τ` (through `Kc`). -/
noncomputable abbrev ev (τ : E) (P : CPoly ℚ) : E := aeval τ ((toPoly P).map (algebraMap ℚ Kc))

lemma evx_subst0 (t : E) (P Q : CPoly ℚ) (hQ : ev (Kc := Kc) t Q ≠ 0) (u : GFrac ℚ) :
    evx Kc t (subst0 P Q u) = evx Kc (ev (Kc := Kc) t P / ev (Kc := Kc) t Q) u := by
  unfold PrimN.evx subst0
  rw [aeval_homog t P Q hQ _ _ (le_max_left _ _), aeval_homog t P Q hQ _ _ (le_max_right _ _)]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hQ)

lemma ev_subst0_den (t : E) (P Q : CPoly ℚ) (hQ : ev (Kc := Kc) t Q ≠ 0) (u : GFrac ℚ) :
    ev (Kc := Kc) t (subst0 P Q u).2 = ev (Kc := Kc) t Q ^ (max u.1.length u.2.length) *
      ev (Kc := Kc) (ev (Kc := Kc) t P / ev (Kc := Kc) t Q) u.2 :=
  aeval_homog t P Q hQ _ _ (le_max_right _ _)

lemma evx_baseTr (t x y : E) (P Q R S : CPoly ℚ) (hQ : ev (Kc := Kc) t Q ≠ 0)
    (hS : ev (Kc := Kc) t S ≠ 0) (hx : x = ev (Kc := Kc) t P / ev (Kc := Kc) t Q)
    (hy : y = ev (Kc := Kc) t R / ev (Kc := Kc) t S) (c : GFrac ℚ × GFrac ℚ)
    (hu : ev (Kc := Kc) x c.1.2 ≠ 0) (hv : ev (Kc := Kc) x c.2.2 ≠ 0) :
    evx Kc t (baseTr P Q R S c) = evx Kc x c.1 + evx Kc x c.2 * y := by
  have hU := evx_subst0 t P Q hQ c.1
  have hV := evx_subst0 t P Q hQ c.2
  have hU2 := ev_subst0_den t P Q hQ c.1
  have hV2 := ev_subst0_den t P Q hQ c.2
  rw [← hx] at hU hV hU2 hV2
  have hU0 : ev (Kc := Kc) t (subst0 P Q c.1).2 ≠ 0 := by rw [hU2]; exact mul_ne_zero (pow_ne_zero _ hQ) hu
  have hV0 : ev (Kc := Kc) t (subst0 P Q c.2).2 ≠ 0 := by rw [hV2]; exact mul_ne_zero (pow_ne_zero _ hQ) hv
  rw [← hU, ← hV, hy]
  unfold PrimN.evx baseTr
  simp only [toPoly_add, toPoly_mul, Polynomial.map_add, Polynomial.map_mul, map_add, map_mul]
  field_simp

lemma evx_mulpair (t : E) (a b : CPoly ℚ × CPoly ℚ) :
    evx Kc t ((mul a.1 b.1 : CPoly ℚ), (mul a.2 b.2 : CPoly ℚ)) = evx Kc t a * evx Kc t b := by
  unfold PrimN.evx
  simp only [toPoly_mul, Polynomial.map_mul, map_mul]
  rw [mul_div_mul_comm]

lemma evN_scal (t : E) (ts : ℕ → E) (c : Code 1) :
    ∀ (m : ℕ) (q : Code (m + 1)), evN Kc t ts m (scal c m q) = evx Kc t c * evN Kc t ts m q
  | 0, q => by
    exact evx_mulpair t c q
  | m + 1, q => by
    rw [evN_succ, evN_succ]
    have h : ∀ l : GPoly (Code (m + 1)), evP Kc t ts m (l.map (scal c m)) =
        evx Kc t c * evP Kc t ts m l := by
      intro l
      induction l with
      | nil => simp [evP]
      | cons a l ih =>
        simp only [evP, List.map_cons, List.foldr_cons] at ih ⊢
        rw [ih, evN_scal t ts c m a]; ring
    show evP Kc t ts m (q.1.map (scal c m)) / evP Kc t ts m q.2 = _
    rw [h, mul_div_assoc]

/-- **The translation is semantically correct.** -/
lemma evN_tr (t x y : E) (ts : ℕ → E) (P Q R S : CPoly ℚ) (hQ : ev (Kc := Kc) t Q ≠ 0)
    (hS : ev (Kc := Kc) t S ≠ 0) (hx : x = ev (Kc := Kc) t P / ev (Kc := Kc) t Q)
    (hy : y = ev (Kc := Kc) t R / ev (Kc := Kc) t S)
    (hne : ∀ D : CPoly ℚ, toPoly D ≠ 0 → ev (Kc := Kc) x D ≠ 0) :
    ∀ (m : ℕ) (c : ICode m), wfI m c = true →
      evN Kc t ts m (tr P Q R S m c) = evI Kc x y ts m c
  | 0, c, hw => by
    simp only [wfI, Bool.and_eq_true, Bool.not_eq_true'] at hw
    have hu : ev (Kc := Kc) x c.1.2 ≠ 0 := hne _ (by
      intro h0; rw [← isZero_iff] at h0; rw [h0] at hw; exact Bool.noConfusion hw.1)
    have hv : ev (Kc := Kc) x c.2.2 ≠ 0 := hne _ (by
      intro h0; rw [← isZero_iff] at h0; rw [h0] at hw; exact Bool.noConfusion hw.2)
    exact evx_baseTr t x y P Q R S hQ hS hx hy c hu hv
  | m + 1, c, hw => by
    simp only [wfI, Bool.and_eq_true, List.all_eq_true] at hw
    have h : ∀ l : List (ICode m), (∀ a ∈ l, wfI m a = true) →
        evP Kc t ts m (l.map (tr P Q R S m)) =
          l.foldr (fun a acc ↦ evI Kc x y ts m a + ts m * acc) 0 := by
      intro l hl
      induction l with
      | nil => simp [evP]
      | cons a l ih =>
        simp only [evP, List.map_cons, List.foldr_cons] at ih ⊢
        rw [ih (fun b hb ↦ hl b (List.mem_cons_of_mem _ hb)),
          evN_tr t x y ts P Q R S hQ hS hx hy hne m a (hl a List.mem_cons_self)]
    rw [evN_succ]
    show evP Kc t ts m (c.1.map (tr P Q R S m)) / evP Kc t ts m (c.2.map (tr P Q R S m)) = _
    rw [h _ hw.1, h _ hw.2]
    rfl

end Eval

/-- Well-formedness of a kind. -/
def wfK (m : ℕ) : IKind m → Bool
  | .prim η => wfI m η
  | .exp a => wfI m a

section Decide

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Towers over a genus-zero base are decided.** Given a rational parametrisation
`x = P(t)/Q(t)`, `y = R(t)/S(t)` with `t′ ρ(t) = 1`, an input tower `tₘ′ = η` / `tₘ = exp a` over
`Kc(x, y)` generating `E`, the certificate `certX` on the translated tower, and a well-formed
integrand `A`: `∫ A` is elementary iff `elemNX` answers `true` on `ρ · tr A`. -/
theorem genus0_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y t : E) (hx : x′ = 1)
    (P Q R S : CPoly ℚ) (ρ : Code 1) (hQ : ev (Kc := Kc) t Q ≠ 0) (hS : ev (Kc := Kc) t S ≠ 0)
    (hxt : x = ev (Kc := Kc) t P / ev (Kc := Kc) t Q)
    (hyt : y = ev (Kc := Kc) t R / ev (Kc := Kc) t S) (hρ : t′ * evx Kc t ρ = 1)
    (iks : (m : ℕ) → IKind m) (ilv : (m : ℕ) → ICode m) (ts : ℕ → E)
    (hts : ∀ m, (ts m)′ = kderI Kc x y ts m (iks m))
    (hts0 : ∀ m (a : ICode m), iks m = .exp a → ts m ≠ 0) (hwk : ∀ m, wfK m (iks m) = true)
    (n : ℕ) (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc (insert x (insert y (ts '' Set.Iio n))))
    (hcert : certX (fun m ↦ trK P Q R S ρ m (iks m)) (fun m ↦ tr P Q R S m (ilv m)) n = true)
    (A : ICode n) (hwA : wfI n A = true) :
    HasElementaryIntegral (evI Kc x y ts n A) ↔
      elemNX (fun m ↦ trK P Q R S ρ m (iks m)) (fun m ↦ tr P Q R S m (ilv m)) n
        (scal ρ n (tr P Q R S n A)) = true := by
  -- `x` is transcendental
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ D : CPoly ℚ, toPoly D ≠ 0 → ev (Kc := Kc) x D ≠ 0 := fun D hD ↦
    aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr hD)
  have htr := fun m c hw ↦ evN_tr (Kc := Kc) t x y ts P Q R S hQ hS hxt hyt hne m c hw
  -- the rescaled derivation
  set τ : E := t′ with hτ
  have hτ0 : τ ≠ 0 := fun h0 ↦ by rw [h0, zero_mul] at hρ; exact zero_ne_one hρ
  have hρτ : evx Kc t ρ = 1 / τ := by rw [eq_div_iff hτ0, mul_comm]; exact hρ
  let d0 : Derivation ℤ E E := Differential.deriv
  have hd0 : ∀ z : E, d0 z = z′ := fun _ ↦ rfl
  have hc0 : ∀ r : Kc, d0 (algebraMap Kc E r) = 0 := fun r ↦ by
    rw [hd0, deriv_algebraMap, hC, map_zero]
  let D' : Differential E := rescale ⟨d0⟩ (1 / τ)
  have hD' : ∀ z : E, D'.deriv z = 1 / τ * d0 z := fun _ ↦ rfl
  have hD't : D'.deriv t = 1 := by rw [hD', hd0, ← hτ]; exact one_div_mul_cancel hτ0
  have hDA' : @DifferentialAlgebra Kc E _ _ _ _ D' :=
    @DifferentialAlgebra.mk Kc E _ _ _ _ D' (fun r ↦ by
      show 1 / τ * d0 (algebraMap Kc E r) = algebraMap Kc E r′
      rw [hc0, hC, map_zero, mul_zero])
  have hCall' : ∀ z : E, D'.deriv z = 0 → z ∈ Set.range (algebraMap Kc E) := by
    intro z hz
    apply hCall
    rw [hD'] at hz
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact absurd h0 (one_div_ne_zero hτ0)
    · rw [hd0] at h0; exact h0
  -- the translated tower
  let T : @NestMTower Kc E _ _ _ _ D' _ (fun m ↦ trK P Q R S ρ m (iks m)) :=
    { x := t
      ts := ts
      hC := hC
      hx := hD't
      ht := fun m ↦ by
        have hw := hwk m
        have h := hts m
        revert hw h
        cases iks m with
        | prim η =>
          intro hw h
          show D'.deriv (ts m) = evN Kc t ts m (scal ρ m (tr P Q R S m η))
          rw [evN_scal, htr m η hw, hρτ, hD', hd0, h]
          rfl
        | exp a =>
          intro hw h
          show D'.deriv (ts m) = D'.deriv (evN Kc t ts m (tr P Q R S m a)) * ts m
          rw [htr m a hw, hD', hD', hd0, hd0, h]
          simp only [kderI]
          ring
      hts0 := fun m a hk ↦ by
        revert hk
        cases h : iks m with
        | prim η => intro hk; simp [trK] at hk
        | exp a₀ => intro _; exact hts0 m a₀ h
      hCall := hCall' }
  -- generation
  have hF0 : ∀ P' : CPoly ℚ, ev (Kc := Kc) t P' ∈ T.F n := fun P' ↦
    T.F_mono (Nat.zero_le n) (T.aeval_mem_F0 _)
  have hgenT : T.F n = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hle : IntermediateField.adjoin Kc (insert x (insert y (ts '' Set.Iio n))) ≤ T.F n := by
      rw [IntermediateField.adjoin_le_iff]
      intro w hw
      rcases hw with rfl | rfl | ⟨i, hi, rfl⟩
      · rw [hxt]; exact div_mem (hF0 P) (hF0 Q)
      · rw [hyt]; exact div_mem (hF0 R) (hF0 S)
      · exact T.F_mono (Nat.succ_le_of_lt hi) (T.ts_mem i)
    exact hle (hgen z)
  have hdec := T.nestX_decides (fun m ↦ tr P Q R S m (ilv m)) n hgenT hcert
    (scal ρ n (tr P Q R S n A))
  have hval : (((T.MP n (T.xspecs (fun m ↦ tr P Q R S m (ilv m)) n hcert).hyp.tr).sem
      (scal ρ n (tr P Q R S n A)) : T.F n) : E) = 1 / τ * evI Kc x y ts n A := by
    rw [T.sem_MP]
    show evN Kc t ts n (scal ρ n (tr P Q R S n A)) = _
    rw [evN_scal, htr n A hwA, hρτ]
  rw [hval] at hdec
  rw [← hdec]
  exact (hasElementaryIntegral_rescale_iff ⟨d0⟩ (1 / τ) _ (one_div_ne_zero hτ0)).symm

end Decide

end Tower.Genus0Auto
