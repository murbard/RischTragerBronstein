import RischTragerBronstein.Algebraic.EllQuarticSq
import RischTragerBronstein.Computable.KronCert

/-!
# Galois orbits of poles with rational residues: Cantor reduction on the curve

For `y² = p(x)` (`p = x³ + a x² + b x + c`) and an irreducible factor `f` of the denominator whose
poles `(α, g(α))` (`f ∣ p − g²`) carry the rational residue `z`, the function
`u = (y − g) / (y + g)` has
`u′ / u = (p′ g − 2 g′ p) / ((p − g²) y)` (`orbit_logDeriv`),
with simple poles of residue `±1` at the points `(α, ±g(α))` and `∓1` at the residual points
over the roots of `h = (p − g²) / f`. Subtracting `z u′/u` moves the orbit's residues to the roots
of `h` (of smaller degree when `deg f ≥ 3`, linear when `deg f = 2`): Cantor's reduction in the
Jacobian. Iterating, the denominator becomes a product of rational linear factors and the
integral is decided by `ellDecideEll`.

The reduction steps are found by an untrusted search (`orbitSearch`: Kronecker factorisation,
modular inverses, a rational square root of the constant `T² / (f′² p) mod f`) and each is
checked by a polynomial identity `A D′ Q = D (A′ Q + z N D′)` (`stepOk`). Soundness:
`ellDecideOrbit_spec`.
-/

open Polynomial Differential

namespace EllAlgo

open CPoly

/-! ### The reduction steps -/

/-- `p′ g − 2 g′ p`. -/
def orbN (p g : CPoly ℚ) : CPoly ℚ := sub (mul (deriv p) g) (smul 2 (mul (deriv g) p))

/-- `p − g²`. -/
def orbQ (p g : CPoly ℚ) : CPoly ℚ := sub p (mul g g)

/-- A reduction step `(z, g, A′, D′)`. -/
abbrev OStep := ℚ × CPoly ℚ × CPoly ℚ × CPoly ℚ

/-- **The check of a step**: `A / D = A′ / D′ + z N / Q`, i.e. `A D′ Q = D (A′ Q + z N D′)`. -/
def stepOk (p A D : CPoly ℚ) (st : OStep) : Bool :=
  !isZero st.2.2.2 && !isZero (orbQ p st.2.1) &&
    beq (mul (mul A st.2.2.2) (orbQ p st.2.1))
      (mul D (add (mul st.2.2.1 (orbQ p st.2.1)) (smul st.1 (mul (orbN p st.2.1) st.2.2.2))))

/-- Apply checked steps; returns the final `(A, D)`. -/
def chainOk (p : CPoly ℚ) : CPoly ℚ → CPoly ℚ → List OStep → Option (CPoly ℚ × CPoly ℚ)
  | A, D, [] => some (A, D)
  | A, D, st :: sts => if stepOk p A D st then chainOk p st.2.2.1 st.2.2.2 sts else none

/-! ### The untrusted search -/

/-- The inverse of `u` modulo `f` (when coprime). -/
def modInv (u f : CPoly ℚ) : CPoly ℚ :=
  let e := egcd u f
  (divMod (smul (lead (trim e.1))⁻¹ e.2.1) f).2

/-- One Cantor step at the irreducible factor `f` of `D`. -/
def orbitStep (p A D f : CPoly ℚ) : Option OStep :=
  let R := (divMod D f).1
  let T := (divMod (mul A (modInv R f)) f).2
  let fd := deriv f
  let w := (divMod (mul (mul T T) (modInv (mul (mul fd fd) p) f)) f).2
  match trim w with
  | [c0] =>
    match qsqrt c0 with
    | some z =>
      if z = 0 then none else
        let g := (divMod (mul T (modInv (smul z fd) f)) f).2
        let h := (divMod (orbQ p g) f).1
        some (z, g, (divMod (sub (mul A h) (smul z (mul (orbN p g) R))) f).1, mul R h)
    | none => none
  | _ => none

/-- Iterate Cantor steps while the denominator has a non-linear factor. -/
def orbitSearch (p : CPoly ℚ) : ℕ → CPoly ℚ → CPoly ℚ → List OStep
  | 0, _, _ => []
  | fuel + 1, A, D =>
    match (Kron.factorQ (Kron.degC D + 1) D).find? (fun f ↦ decide (2 ≤ Kron.degC f)) with
    | none => []
    | some f =>
      match orbitStep p A D f with
      | some st => st :: orbitSearch p fuel st.2.2.1 st.2.2.2
      | none => []

/-- **The decision procedure with Galois orbits of rational-residue poles.** -/
def ellDecideOrbit (a b c : ℤ) (A D : CPoly ℚ) (fuel : ℕ) : Option Bool :=
  let p := pOf a b c
  if isZero D then none else
    match chainOk p A D (orbitSearch p (Kron.degC D + 1) A D) with
    | some (A', D') => ellDecideEll a b c A' D' fuel
    | none => none

/-! ### Soundness -/

section Sound

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The logarithmic derivative of `(y − g) / (y + g)`.** -/
lemma orbit_logDeriv (x y : E) (hx : x′ = 1) (p g : ℚ[X]) (hy : y ^ 2 = aeval x p) (hy0 : y ≠ 0)
    (hQ : aeval x (p - g * g) ≠ 0) :
    y - aeval x g ≠ 0 ∧ y + aeval x g ≠ 0 ∧
      logDeriv ((y - aeval x g) / (y + aeval x g)) =
        aeval x (derivative p * g - 2 * (derivative g * p)) / (aeval x (p - g * g) * y) := by
  set G := aeval x g with hG
  have hQ' : y ^ 2 - G ^ 2 ≠ 0 := by
    rw [hy, hG, ← map_pow, ← map_sub]; rwa [sq]
  have hm : y - G ≠ 0 := fun h0 ↦ hQ' (by
    rw [show y ^ 2 - G ^ 2 = (y - G) * (y + G) by ring, h0, zero_mul])
  have hp : y + G ≠ 0 := fun h0 ↦ hQ' (by
    rw [show y ^ 2 - G ^ 2 = (y - G) * (y + G) by ring, h0, mul_zero])
  refine ⟨hm, hp, ?_⟩
  have hyd : 2 * y * y′ = aeval x (derivative p) := by
    have := congrArg (fun t : E ↦ t′) hy
    rw [deriv_aeval_rat x hx] at this
    rw [← this, pow_two, Derivation.leibniz]
    simp only [smul_eq_mul]; ring
  have hGd : G′ = aeval x (derivative g) := deriv_aeval_rat x hx g
  rw [logDeriv_div _ _ hm hp, logDeriv, logDeriv, map_sub, map_add, hGd]
  have hQe : aeval x (p - g * g) = y ^ 2 - G ^ 2 := by
    rw [map_sub, map_mul, ← hy, hG]; ring
  rw [hQe]
  simp only [map_sub, map_mul, map_ofNat]
  rw [← hG, ← hyd, ← hy]
  field_simp
  ring

variable (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
include hC hx

/-- **One checked step preserves elementary integrability.** -/
lemma stepOk_spec (p : CPoly ℚ) (hy : y ^ 2 = aeval x (toPoly p)) (hy0 : y ≠ 0)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (st : OStep) (h : stepOk p A D st = true) :
    toPoly st.2.2.2 ≠ 0 ∧
      (HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) ↔
        HasElementaryIntegral (aeval x (toPoly st.2.2.1) / (aeval x (toPoly st.2.2.2) * y))) := by
  obtain ⟨z, g, A', D'⟩ := st
  simp only [stepOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff] at h
  obtain ⟨⟨hD', hQ⟩, hid⟩ := h
  have hD'0 : toPoly D' ≠ 0 := fun h0 ↦ by simp [(isZero_iff _).mpr h0] at hD'
  have hQ0 : toPoly (orbQ p g) ≠ 0 := fun h0 ↦ by simp [(isZero_iff _).mpr h0] at hQ
  refine ⟨hD'0, ?_⟩
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hQe : toPoly (orbQ p g) = toPoly p - toPoly g * toPoly g := by
    rw [orbQ, toPoly_sub, toPoly_mul]
  have hNe : toPoly (orbN p g) = derivative (toPoly p) * toPoly g -
      2 * (derivative (toPoly g) * toPoly p) := by
    rw [orbN, toPoly_sub, toPoly_mul, toPoly_smul, toPoly_mul, toPoly_deriv, toPoly_deriv]
    simp [C_ofNat]
  obtain ⟨hm, hp, hlog⟩ := orbit_logDeriv x y hx (toPoly p) (toPoly g) hy hy0
    (by rw [← hQe]; exact hne _ hQ0)
  rw [← hQe, ← hNe] at hlog
  set u := (y - aeval x (toPoly g)) / (y + aeval x (toPoly g)) with hu
  have hu0 : u ≠ 0 := div_ne_zero hm hp
  -- the identity in `E`
  simp only [toPoly_mul, toPoly_add, toPoly_smul] at hid
  have hidE := congrArg (aeval x) hid
  simp only [map_mul, map_add, aeval_C, eq_ratCast] at hidE
  have hDE := hne _ hD
  have hD'E := hne _ hD'0
  have hQE := hne _ hQ0
  have hsplit : aeval x (toPoly A) / (aeval x (toPoly D) * y) =
      aeval x (toPoly A') / (aeval x (toPoly D') * y) + (z : E) * logDeriv u := by
    rw [hlog]
    field_simp
    linear_combination hidE
  have hin : HasElementaryIntegralIn ((z : E) * logDeriv u) := by
    have := hasElementaryIntegralIn_logDeriv₂ (z : E) 0 u 1 (deriv_ratCast_L z) (by simp) hu0
      one_ne_zero
    simpa using this
  rw [hsplit]
  constructor
  · intro h1
    have := h1.sub_in hin
    rwa [add_sub_cancel_right] at this
  · intro h1
    exact h1.add_in hin

lemma chainOk_spec (p : CPoly ℚ) (hy : y ^ 2 = aeval x (toPoly p)) (hy0 : y ≠ 0) :
    ∀ (sts : List OStep) (A D A' D' : CPoly ℚ), toPoly D ≠ 0 →
      chainOk p A D sts = some (A', D') →
      toPoly D' ≠ 0 ∧ (HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) ↔
        HasElementaryIntegral (aeval x (toPoly A') / (aeval x (toPoly D') * y)))
  | [], A, D, A', D', hD, h => by
    simp only [chainOk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hD, Iff.rfl⟩
  | st :: sts, A, D, A', D', hD, h => by
    simp only [chainOk] at h
    split_ifs at h with hs
    obtain ⟨h1, h2⟩ := stepOk_spec hC x y hx p hy hy0 A D hD st hs
    obtain ⟨h3, h4⟩ := chainOk_spec p hy hy0 sts _ _ A' D' h1 h
    exact ⟨h3, h2.trans h4⟩

omit hC hx in
/-- **Correctness of `ellDecideOrbit`.** -/
theorem ellDecideOrbit_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (fuel : ℕ) (ans : Bool) (h : ellDecideOrbit a b c A D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold ellDecideOrbit at h
  simp only at h
  split_ifs at h with hD
  split at h
  swap
  · exact absurd h (by simp)
  rename_i A' D' hch
  have hD0 : toPoly D ≠ 0 := fun h0 ↦ hD ((isZero_iff _).mpr h0)
  have hyp : y ^ 2 = aeval x (toPoly (pOf a b c)) := by
    rw [hy, toPoly_pOf]; simp
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hy0 : y ≠ 0 := by
    rintro rfl
    have hne := aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hsq.ne_zero)
    apply hne
    rw [aeval_map_algebraMap]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, eq_ratCast, Rat.cast_intCast]
    linear_combination -hy
  obtain ⟨-, hiff⟩ := chainOk_spec hC x y hx (pOf a b c) hyp hy0 _ A D A' D' hD0 hch
  rw [hiff]
  exact ellDecideEll_spec hC hCall x y hx a b c hsq hy hgen A' D' _ ans h

end Sound

end EllAlgo
