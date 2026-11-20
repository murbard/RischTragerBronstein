import RischTragerBronstein.Algebraic.EllQuarticComplete
import RischTragerBronstein.Rational.IntegrableIn

/-!
# Quartics with a square leading coefficient: `∫ A(x) / (D(x) √q(x)) dx`, `q = s²x⁴ + ax³ + …`

The points at infinity are rational; the model change
`X = y − g(x)`, `W = h(x) X − c′` (`g = s x² + (a/2s) x + β`, `h = 4 s x + a/s`) gives the cubic
curve `W² = P(X)` with `Kc(x, y) = Kc(X, W)`. Rescaling the derivation by `1/X′`, the integrand
becomes `R₁(X) + R₂(X) W` (computed in `ℚ(X)[W]` and checked by the kernel in `ℚ[x][y]/(y² − q)`);
the rational part is elementary and `R₂ W = R₂ P / W` is decided by `ellDecideCubic`.
-/

open Polynomial

namespace EllAlgo

open CPoly

/-! ### Arithmetic in `ℚ[x][y]/(y² − q)` (the kernel check) -/

/-- `(u + v y)(u′ + v′ y)` with `y² = q`. -/
def qyMul (q : CPoly ℚ) (a b : CPoly ℚ × CPoly ℚ) : CPoly ℚ × CPoly ℚ :=
  (add (mul a.1 b.1) (mul (mul a.2 b.2) q), add (mul a.1 b.2) (mul a.2 b.1))

def qyAdd (a b : CPoly ℚ × CPoly ℚ) : CPoly ℚ × CPoly ℚ := (add a.1 b.1, add a.2 b.2)

/-- `N(X)` at `X = (u, v)` by Horner. -/
def qyEval (q : CPoly ℚ) (X : CPoly ℚ × CPoly ℚ) (N : CPoly ℚ) : CPoly ℚ × CPoly ℚ :=
  N.foldr (fun c acc ↦ qyAdd ([c], []) (qyMul q X acc)) ([], [])

/-! ### Arithmetic in `ℚ(X)[W]/(W² − P)` (the untrusted computation) -/

/-- `(u + v W) / den`. -/
abbrev WEl := CPoly ℚ × CPoly ℚ × CPoly ℚ

/-- Divide out a common factor. -/
def wReduce (z : WEl) : WEl :=
  let g := (egcd (egcd z.1 z.2.1).1 z.2.2).1
  if (trim g).length ≤ 1 then (trim z.1, trim z.2.1, trim z.2.2) else
    (trim (divMod z.1 g).1, trim (divMod z.2.1 g).1, trim (divMod z.2.2 g).1)

def wAdd (a b : WEl) : WEl :=
  wReduce (add (mul a.1 b.2.2) (mul b.1 a.2.2), add (mul a.2.1 b.2.2) (mul b.2.1 a.2.2),
    mul a.2.2 b.2.2)

def wMul (P : CPoly ℚ) (a b : WEl) : WEl :=
  wReduce (add (mul a.1 b.1) (mul (mul a.2.1 b.2.1) P), add (mul a.1 b.2.1) (mul a.2.1 b.1),
    mul a.2.2 b.2.2)

def wInv (P : CPoly ℚ) (a : WEl) : WEl :=
  wReduce (mul a.2.2 a.1, smul (-1) (mul a.2.2 a.2.1), sub (mul a.1 a.1) (mul (mul a.2.1 a.2.1) P))

def wConst (c : ℚ) : WEl := ([c], [], [1])

/-- `N(z)` by Horner. -/
def wEval (P : CPoly ℚ) (z : WEl) (N : CPoly ℚ) : WEl :=
  N.foldr (fun c acc ↦ wAdd (wConst c) (wMul P z acc)) (wConst 0)

/-! ### The model change -/

/-- The data `(s, a, b, c, d, β, c′, d′)` of `q = s²x⁴ + ax³ + bx² + cx + d`. -/
def sqData (q : CPoly ℚ) : Option (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) :=
  if q.length = 5 then
    match qsqrt (q.getD 4 0) with
    | some s =>
      if s ≠ 0 then
        let a := q.getD 3 0
        let b := q.getD 2 0
        let c := q.getD 1 0
        let d := q.getD 0 0
        let β := (b - a ^ 2 / (4 * s ^ 2)) / (2 * s)
        some (s, a, b, c, d, β, c - a * β / s, d - β ^ 2)
      else none
    | none => none
  else none

/-- `g = s x² + (a/2s) x + β`. -/
def gOf (s a β : ℚ) : CPoly ℚ := [β, a / (2 * s), s]
/-- `h = 4 s x + a/s`. -/
def hOf (s a : ℚ) : CPoly ℚ := [a / s, 4 * s]
/-- `P(X) = −8sX³ + (a²/s² − 16sβ)X² + (8sd′ − 2ac′/s)X + c′²`. -/
def POf (s a β c' d' : ℚ) : CPoly ℚ :=
  [c' ^ 2, 8 * s * d' - 2 * a * c' / s, a ^ 2 / s ^ 2 - 16 * s * β, -8 * s]

/-- `f / X′ = (N₁ + N₂ W) / M` for `f = A(x) / (D(x) y)`, computed in `ℚ(X)[W]`. -/
def sqRep (q A D : CPoly ℚ) (s a β c' : ℚ) (P : CPoly ℚ) : WEl :=
  let Xe : WEl := ([0, 1], [], [1])
  let xE : WEl := wReduce ([c', -a / s], [1], [0, 4 * s])
  let yE : WEl := wAdd Xe (wEval P xE (gOf s a β))
  let Xd : WEl := wAdd (wMul P (wEval P xE (deriv q)) (wInv P (wMul P (wConst 2) yE)))
    (wMul P (wConst (-1)) (wEval P xE (deriv (gOf s a β))))
  wMul P (wMul P (wEval P xE A) (wInv P (wEval P xE D))) (wMul P (wInv P yE) (wInv P Xd))

/-- The kernel check `2 A M(X) = D (q′ − 2g′y) (N₁(X) + N₂(X) W)` in `ℚ[x][y]/(y² − q)`. -/
def sqCheck (q A D : CPoly ℚ) (s a β c' : ℚ) (r : WEl) : Bool :=
  let g := gOf s a β
  let h := hOf s a
  let X : CPoly ℚ × CPoly ℚ := (smul (-1) g, [1])
  let W : CPoly ℚ × CPoly ℚ := (sub (mul h (smul (-1) g)) [c'], h)
  let lhs := qyMul q ([2], []) (qyMul q (A, []) (qyEval q X r.2.2))
  let rhs := qyMul q (D, []) (qyMul q (deriv q, smul (-2) (deriv g))
    (qyAdd (qyEval q X r.1) (qyMul q (qyEval q X r.2.1) W)))
  beq lhs.1 rhs.1 && beq lhs.2 rhs.2

/-- **The decision procedure for quartics with a square leading coefficient.** -/
def ellDecideQuarticSq (q A D : CPoly ℚ) (fuel : ℕ) : Option Bool :=
  match sqData q with
  | some (s, a, _, _, _, β, c', d') =>
    let P := POf s a β c' d'
    let r := sqRep q A D s a β c' P
    if sepCheck q && sepCheck P && !isZero D && !isZero r.2.2 && sqCheck q A D s a β c' r then
      ellDecideCubic P (mul r.2.1 P) r.2.2 fuel
    else none
  | none => none

/-! ### Correctness: helpers -/

lemma toPoly_of_length_five (p : CPoly ℚ) (h : p.length = 5) :
    toPoly p = C (p.getD 0 0) + C (p.getD 1 0) * X + C (p.getD 2 0) * X ^ 2 +
      C (p.getD 3 0) * X ^ 3 + C (p.getD 4 0) * X ^ 4 := by
  ext i
  rw [coeff_toPoly]
  simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X_pow, coeff_X]
  rcases Nat.lt_or_ge i 5 with hi | hi
  · interval_cases i <;> simp
  · rw [List.getD_eq_default _ _ (by omega)]
    simp only [show i ≠ 0 by omega, show ¬(1 = i) by omega, show i ≠ 2 by omega,
      show i ≠ 3 by omega, show i ≠ 4 by omega, if_false, mul_zero, add_zero]

lemma sqData_spec {q : CPoly ℚ} {s a b c d β c' d' : ℚ}
    (h : sqData q = some (s, a, b, c, d, β, c', d')) :
    q.length = 5 ∧ s ^ 2 = q.getD 4 0 ∧ s ≠ 0 ∧ a = q.getD 3 0 ∧ b = q.getD 2 0 ∧
      c = q.getD 1 0 ∧ d = q.getD 0 0 ∧ β = (b - a ^ 2 / (4 * s ^ 2)) / (2 * s) ∧
      c' = c - a * β / s ∧ d' = d - β ^ 2 := by
  unfold sqData at h
  split_ifs at h with h5
  split at h
  · rename_i s' hs'
    split_ifs at h with hs0
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨h5, qsqrt_spec hs', hs0, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact absurd h (by simp)

section Eval

variable {E : Type*} [Field E] [CharZero E] (x y : E) (q : CPoly ℚ)

/-- The value of `u + v y`. -/
noncomputable def evQY (z : CPoly ℚ × CPoly ℚ) : E := aeval x (toPoly z.1) + aeval x (toPoly z.2) * y

variable {x y q}

lemma evQY_add (a b : CPoly ℚ × CPoly ℚ) : evQY x y (qyAdd a b) = evQY x y a + evQY x y b := by
  simp only [evQY, qyAdd, toPoly_add, map_add]; ring

lemma evQY_mul (hy : y ^ 2 = aeval x (toPoly q)) (a b : CPoly ℚ × CPoly ℚ) :
    evQY x y (qyMul q a b) = evQY x y a * evQY x y b := by
  simp only [evQY, qyMul, toPoly_add, toPoly_mul, map_add, map_mul]
  rw [← hy]; ring

lemma evQY_const (c : ℚ) : evQY x y (([c], []) : CPoly ℚ × CPoly ℚ) = (c : E) := by
  simp [evQY, CPoly.toPoly]

lemma evQY_eval (hy : y ^ 2 = aeval x (toPoly q)) (Z : CPoly ℚ × CPoly ℚ) :
    ∀ N : CPoly ℚ, evQY x y (qyEval q Z N) = aeval (evQY x y Z) (toPoly N)
  | [] => by simp [qyEval, evQY, CPoly.toPoly]
  | c :: t => by
    have ih := evQY_eval hy Z t
    simp only [qyEval, List.foldr_cons] at ih ⊢
    rw [evQY_add, evQY_mul hy, ih, evQY_const, toPoly_cons, map_add, map_mul, aeval_X, aeval_C,
      eq_ratCast]

end Eval

/-- **The model change**: `W² = P(X) + 8sX (y² − q(x))`. -/
lemma sq_model {F : Type*} [Field F] [CharZero F] (s a b c d x y : F) (hs : s ≠ 0) :
    ((4 * s * x + a / s) * (y - (s * x ^ 2 + a / (2 * s) * x + (b - a ^ 2 / (4 * s ^ 2)) / (2 * s))) -
      (c - a * ((b - a ^ 2 / (4 * s ^ 2)) / (2 * s)) / s)) ^ 2 =
    -8 * s * (y - (s * x ^ 2 + a / (2 * s) * x + (b - a ^ 2 / (4 * s ^ 2)) / (2 * s))) ^ 3 +
      (a ^ 2 / s ^ 2 - 16 * s * ((b - a ^ 2 / (4 * s ^ 2)) / (2 * s))) *
        (y - (s * x ^ 2 + a / (2 * s) * x + (b - a ^ 2 / (4 * s ^ 2)) / (2 * s))) ^ 2 +
      (8 * s * (d - ((b - a ^ 2 / (4 * s ^ 2)) / (2 * s)) ^ 2) -
        2 * a * (c - a * ((b - a ^ 2 / (4 * s ^ 2)) / (2 * s)) / s) / s) *
        (y - (s * x ^ 2 + a / (2 * s) * x + (b - a ^ 2 / (4 * s ^ 2)) / (2 * s))) +
      (c - a * ((b - a ^ 2 / (4 * s ^ 2)) / (2 * s)) / s) ^ 2 +
      8 * s * (y - (s * x ^ 2 + a / (2 * s) * x + (b - a ^ 2 / (4 * s ^ 2)) / (2 * s))) *
        (y ^ 2 - (s ^ 2 * x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d)) := by
  field_simp
  ring

section RatIn

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- Rational functions of `X` (`X′ = 1`) are elementary-integrable in every elementary
extension. -/
theorem ratX_in (hC : ∀ c : Kc, c′ = 0) (X : E) (hX : X′ = 1) (N M : ℚ[X]) (hM : M ≠ 0) :
    HasElementaryIntegralIn (aeval X N / aeval X M) := by
  intro E' _ _ _ _ hE'
  let _ : Algebra Kc E' := ((algebraMap E E').comp (algebraMap Kc E)).toAlgebra
  have hDA : DifferentialAlgebra Kc E' :=
    ⟨fun a ↦ by
      change (algebraMap E E' (algebraMap Kc E a))′ = algebraMap E E' (algebraMap Kc E a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have : CharZero E' := charZero_of_injective_algebraMap (algebraMap E E').injective
  have hx : (algebraMap E E' X)′ = 1 := by rw [deriv_algebraMap, hX, map_one]
  have hM' : M.map (algebraMap ℚ Kc) ≠ 0 := (Polynomial.map_ne_zero_iff
    (algebraMap ℚ Kc).injective).mpr hM
  have := hasElementaryIntegral_rational_in hC (algebraMap E E' X) hx (N.map (algebraMap ℚ Kc))
    (M.map (algebraMap ℚ Kc)) hM' 0
  rw [Derivation.map_zero, zero_add, aeval_map_algebraMap, aeval_map_algebraMap] at this
  rwa [map_div₀, ← aeval_algebraMap_apply, ← aeval_algebraMap_apply]

end RatIn

section Spec

open Differential IntermediateField

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 3200000 in
/-- **Correctness of `ellDecideQuarticSq`.** -/
theorem ellDecideQuarticSq_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly ℚ) (hy : y ^ 2 = aeval x (toPoly q)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (fuel : ℕ) (ans : Bool) (h : ellDecideQuarticSq q A D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold ellDecideQuarticSq at h
  split at h
  swap
  · exact absurd h (by simp)
  rename_i s a b c d β c' d' hsd
  obtain ⟨h5, hs2, hs0, ha, hb, hc, hd, hβ, hc', hd'⟩ := sqData_spec hsd
  dsimp only at h
  split_ifs at h with hchk
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hchk
  obtain ⟨⟨⟨⟨hsepq, hsepP⟩, hD0⟩, hM0⟩, hcheck⟩ := hchk
  set P := POf s a β c' d' with hPdef
  set r := sqRep q A D s a β c' P with hr
  -- transcendence of `x`
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hq0 : toPoly q ≠ 0 := (sepCheck_sound hsepq).ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl; apply hne _ hq0; rw [← hy]; ring
  -- the curve in coordinates
  have hq : aeval x (toPoly q) = (s : E) ^ 2 * x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d := by
    rw [toPoly_of_length_five q h5, ← hs2, ← ha, ← hb, ← hc, ← hd]
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, eq_ratCast]
    push_cast; ring
  have hsE : (s : E) ≠ 0 := by exact_mod_cast hs0
  set g : E := (s : E) * x ^ 2 + (a : E) / (2 * s) * x + (β : E) with hg
  set Xv : E := y - g with hXv
  set Wv : E := (4 * s * x + a / s) * Xv - c' with hWv
  have hWP : Wv ^ 2 = aeval Xv (toPoly P) := by
    have key := sq_model (s : E) a b c d x y hsE
    have hβE : (β : E) = ((b : E) - a ^ 2 / (4 * s ^ 2)) / (2 * s) := by rw [hβ]; push_cast; ring
    have hc'E : (c' : E) = c - a * ((b - a ^ 2 / (4 * s ^ 2)) / (2 * s)) / s := by
      rw [hc', hβ]; push_cast; ring
    have hd'E : (d' : E) = d - ((b - a ^ 2 / (4 * s ^ 2)) / (2 * s)) ^ 2 := by
      rw [hd', hβ]; push_cast; ring
    rw [← hq, ← hy, sub_self, mul_zero, add_zero] at key
    simp only [hPdef, POf, toPoly_cons, toPoly_nil, mul_zero, add_zero, map_add, map_mul,
      aeval_C, aeval_X, eq_ratCast]
    rw [hWv, hXv, hg, hc'E, hβE, key]
    push_cast
    rw [hc'E, hd'E, hβE]
    ring
  -- derivatives
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hyd : y′ = aeval x (derivative (toPoly q)) / (2 * y) := by
    have := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul] at this
    rw [deriv_aeval_rat x hx] at this
    rw [eq_div_iff (mul_ne_zero two_ne_zero hy0)]
    linear_combination this
  set G' : E := 2 * (s : E) * x + (a : E) / (2 * s) with hG'
  have hXd : Xv′ = aeval x (derivative (toPoly q)) / (2 * y) - G' := by
    rw [hXv, hg, map_sub, hyd]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, hx,
      deriv_ratCast_L]
    rw [hG']
    have : ((a : E) / (2 * s))′ = 0 := by
      rw [show (a : E) / (2 * s) = ((a / (2 * s) : ℚ) : E) by push_cast; ring]
      exact deriv_ratCast_L _
    rw [this]
    ring
  -- `X` is not a constant
  have hXd0 : Xv′ ≠ 0 := by
    intro h0
    obtain ⟨κ, hκ⟩ := hCall Xv h0
    set hK : Kc[X] := C (s : Kc) * X ^ 2 + C ((a / (2 * s) : ℚ) : Kc) * X + C ((β : Kc) + κ)
    have hev : aeval x hK = y := by
      simp only [hK, map_add, map_mul, map_pow, aeval_C, aeval_X, map_ratCast]
      have : y = Xv + g := by rw [hXv]; ring
      rw [this, ← hκ, hg]
      push_cast; ring
    set qK := (toPoly q).map (algebraMap ℚ Kc)
    have heq : hK ^ 2 = qK := by
      by_contra hne'
      apply aeval_ne_zero_of_tr x htrK (sub_ne_zero.mpr hne')
      rw [map_sub, map_pow, hev, aeval_map_algebraMap, ← hy, sub_self]
    have hsep : qK.Separable := (sepCheck_sound hsepq).map
    have hu : IsUnit hK := IsCoprime.isUnit_of_dvd' hsep ⟨hK, by rw [← heq]; ring⟩
      ⟨C 2 * derivative hK, by rw [← heq, derivative_pow]; simp; ring⟩
    have hdeg : hK.natDegree = 2 := natDegree_quadratic (by exact_mod_cast hs0)
    rw [natDegree_eq_zero_of_isUnit hu] at hdeg
    exact absurd hdeg (by norm_num)
  have htrX : Transcendental Kc Xv := transcendental_of_deriv_ne_zero hC hXd0
  have hneX : ∀ Q : ℚ[X], Q ≠ 0 → aeval Xv Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr Xv htrX ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hXne : Xv ≠ 0 := fun h0 ↦ hXd0 (by rw [h0, Derivation.map_zero])
  -- the rescaled derivation
  set τ : E := Xv′ with hτ
  let d0 : Derivation ℤ E E := Differential.deriv
  have hd0 : ∀ z : E, d0 z = z′ := fun _ ↦ rfl
  let D' : Differential E := rescale ⟨d0⟩ (1 / τ)
  have hT' : D'.deriv Xv = 1 := by
    show 1 / τ * d0 Xv = 1
    rw [hd0]; exact one_div_mul_cancel hXd0
  have hDA' : @DifferentialAlgebra Kc E _ _ _ _ D' :=
    @DifferentialAlgebra.mk Kc E _ _ _ _ D' (fun r ↦ by
      show 1 / τ * d0 (algebraMap Kc E r) = algebraMap Kc E r′
      rw [hd0, hconstE, hC, map_zero, mul_zero])
  have hCall' : ∀ z : E, D'.deriv z = 0 → z ∈ Set.range (algebraMap Kc E) := by
    intro z hz
    apply hCall
    have : 1 / τ * d0 z = 0 := hz
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (one_div_ne_zero hXd0)
    · exact h0
  -- the cubic model generates
  have hPform : toPoly P = C (-8 * s) * X ^ 3 + C (a ^ 2 / s ^ 2 - 16 * s * β) * X ^ 2 +
      C (8 * s * d' - 2 * a * c' / s) * X + C (c' ^ 2) := by
    simp only [hPdef, POf, toPoly_cons, toPoly_nil, mul_zero, add_zero]; ring
  set pK := (toPoly P).map (algebraMap ℚ Kc) with hpK
  have hodd : Odd pK.natDegree := by
    rw [hpK, hPform]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X]
    rw [natDegree_cubic (by simp [hs0])]
    decide
  have hWK : Wv ^ 2 = aeval Xv pK := by rw [hpK, aeval_map_algebraMap, hWP]
  set S := hypField Xv Wv htrX pK hodd hWK with hS
  let NF : IntermediateField Kc E :=
    { S with algebraMap_mem' := fun κ ↦ ⟨algebraMap Kc E κ, 0,
        IntermediateField.algebraMap_mem _ _, zero_mem _, by ring⟩ }
  have hQmem : ∀ r : ℚ, ((r : ℚ) : E) ∈ Kc⟮Xv⟯ := fun r ↦ by
    have := IntermediateField.algebraMap_mem Kc⟮Xv⟯ (r : Kc)
    rwa [map_ratCast] at this
  have hQN : ∀ r : ℚ, ((r : ℚ) : E) ∈ NF := fun r ↦ by
    have := NF.algebraMap_mem (r : Kc)
    rwa [map_ratCast] at this
  have hXmem : Xv ∈ Kc⟮Xv⟯ := mem_adjoin_simple_self _ _
  have hxN : x ∈ NF := by
    refine ⟨((c' : ℚ) : E) / (4 * s * Xv) - ((a / s : ℚ) : E) / (4 * s), 1 / (4 * s * Xv), ?_, ?_, ?_⟩
    · exact sub_mem (div_mem (hQmem _) (mul_mem (mul_mem (by simpa using hQmem 4) (hQmem s)) hXmem))
        (div_mem (hQmem _) (mul_mem (by simpa using hQmem 4) (hQmem s)))
    · exact div_mem (one_mem _) (mul_mem (mul_mem (by simpa using hQmem 4) (hQmem s)) hXmem)
    · rw [hWv]; push_cast; field_simp; ring
  have hXN : Xv ∈ NF := ⟨Xv, 0, hXmem, zero_mem _, by ring⟩
  have hyN : y ∈ NF := by
    have : y = Xv + ((s : ℚ) : E) * x ^ 2 + ((a / (2 * s) : ℚ) : E) * x + ((β : ℚ) : E) := by
      rw [hXv, hg]; push_cast; ring
    rw [this]
    exact add_mem (add_mem (add_mem hXN (mul_mem (hQN _) (pow_mem hxN _)))
      (mul_mem (hQN _) hxN)) (hQN _)
  have hgen' : ∀ z : E, InHyp Kc Xv Wv z := by
    intro z
    obtain ⟨α, β₀, hα, hβ₀, rfl⟩ := hgen z
    have hle : Kc⟮x⟯ ≤ NF := adjoin_simple_le_iff.mpr hxN
    exact add_mem (hle hα) (mul_mem (hle hβ₀) hyN)
  -- the kernel identity
  have hDne : aeval x (toPoly D) ≠ 0 := hne _ (by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hD0; exact hD0 h0)
  have hMne : aeval Xv (toPoly r.2.2) ≠ 0 := hneX _ (by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hM0; exact hM0 h0)
  have hWne : Wv ≠ 0 := by
    intro h0
    have hP0 : toPoly P ≠ 0 := (sepCheck_sound hsepP).ne_zero
    apply hneX _ hP0; rw [← hWP, h0]; ring
  unfold sqCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨h1, h2⟩ := hcheck
  have hid : evQY x y (qyMul q ([2], []) (qyMul q (A, [])
      (qyEval q (smul (-1) (gOf s a β), [1]) r.2.2))) =
      evQY x y (qyMul q (D, []) (qyMul q (deriv q, smul (-2) (deriv (gOf s a β)))
        (qyAdd (qyEval q (smul (-1) (gOf s a β), [1]) r.1)
          (qyMul q (qyEval q (smul (-1) (gOf s a β), [1]) r.2.1)
            (sub (mul (hOf s a) (smul (-1) (gOf s a β))) [c'], hOf s a))))) := by
    unfold evQY
    rw [(beq_iff _ _).mp h1, (beq_iff _ _).mp h2]
  have hZ : evQY x y ((smul (-1) (gOf s a β), [1]) : CPoly ℚ × CPoly ℚ) = Xv := by
    simp only [evQY, gOf, toPoly_smul, toPoly_cons, toPoly_nil, map_mul, map_add, aeval_C,
      aeval_X, eq_ratCast, mul_zero, add_zero, map_neg, map_one]
    rw [hXv, hg]; push_cast; ring
  have hWq : evQY x y ((sub (mul (hOf s a) (smul (-1) (gOf s a β))) [c'], hOf s a) :
      CPoly ℚ × CPoly ℚ) = Wv := by
    simp only [evQY, gOf, hOf, toPoly_sub, toPoly_mul, toPoly_smul, toPoly_cons, toPoly_nil,
      map_mul, map_add, map_sub, aeval_C, aeval_X, eq_ratCast, mul_zero, add_zero, map_neg,
      map_one]
    rw [hWv, hXv, hg]; push_cast; ring
  have hdq : evQY x y ((deriv q, smul (-2) (deriv (gOf s a β))) : CPoly ℚ × CPoly ℚ) =
      aeval x (derivative (toPoly q)) - 2 * G' * y := by
    simp only [evQY, gOf, toPoly_deriv, toPoly_smul, toPoly_cons, toPoly_nil, mul_zero, add_zero,
      map_mul, aeval_C, eq_ratCast, derivative_add, derivative_mul, derivative_C, derivative_X,
      zero_mul, zero_add, mul_one, map_add, aeval_X, one_mul]
    rw [hG']; push_cast; ring
  simp only [evQY_mul hy, evQY_add, evQY_eval hy, hZ, hWq, hdq] at hid
  simp only [evQY, toPoly_cons, toPoly_nil, mul_zero, add_zero, map_zero, zero_mul, add_zero,
    aeval_C, eq_ratCast] at hid
  -- the rescaled integrand
  have hQd : aeval x (derivative (toPoly q)) - 2 * G' * y ≠ 0 := by
    intro h0; apply hXd0; rw [hXd]; field_simp; linear_combination h0
  set T : E := aeval x (derivative (toPoly q)) - 2 * G' * y with hT
  have hint : 1 / τ * (aeval x (toPoly A) / (aeval x (toPoly D) * y)) =
      aeval Xv (toPoly r.1) / aeval Xv (toPoly r.2.2) +
        aeval Xv (toPoly (mul r.2.1 P)) / (aeval Xv (toPoly r.2.2) * Wv) := by
    have e1 : τ = T / (2 * y) := by rw [hXd, hT]; field_simp
    have e2 : 1 / τ * (aeval x (toPoly A) / (aeval x (toPoly D) * y)) =
        2 * aeval x (toPoly A) / (aeval x (toPoly D) * T) := by
      rw [e1]; field_simp
    have e3 : aeval Xv (toPoly r.1) / aeval Xv (toPoly r.2.2) +
        aeval Xv (toPoly (mul r.2.1 P)) / (aeval Xv (toPoly r.2.2) * Wv) =
        (aeval Xv (toPoly r.1) + aeval Xv (toPoly r.2.1) * Wv) / aeval Xv (toPoly r.2.2) := by
      rw [toPoly_mul, map_mul, ← hWP]; field_simp
    rw [e2, e3, div_eq_div_iff (mul_ne_zero hDne hQd) hMne]
    linear_combination hid
  have hspec := @ellDecideCubic_spec Kc E _ _ _ _ D' hDA' _ _ hC hCall' Xv Wv hT' P
    (sepCheck_sound hsepP).squarefree hWP hgen' _ _ fuel ans h
  rw [hspec]
  have hrat := @ratX_in Kc E _ _ _ _ D' hDA' _ _ hC Xv hT' (toPoly r.1) (toPoly r.2.2) (by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hM0; exact hM0 h0)
  have hstep : @HasElementaryIntegral E _ D' (aeval Xv (toPoly (mul r.2.1 P)) /
      (aeval Xv (toPoly r.2.2) * Wv)) ↔
      @HasElementaryIntegral E _ D' (1 / τ * (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
    letI : Differential E := D'
    rw [hint]
    constructor
    · intro h1; have := h1.add_in hrat; rwa [add_comm] at this
    · intro h1; have := h1.sub_in hrat; rwa [add_sub_cancel_left] at this
  rw [hstep]
  exact hasElementaryIntegral_rescale_iff ⟨d0⟩ (1 / τ) _ (one_div_ne_zero hXd0)

end Spec

end EllAlgo
