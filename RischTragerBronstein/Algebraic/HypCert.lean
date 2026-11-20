import RischTragerBronstein.Algebraic.HypDecide
import RischTragerBronstein.Computable.NullSpace

/-!
# Hyperelliptic integrals with finite poles: `∫ A(x) / (D(x) √p(x)) dx`

When the Hermite reduction absorbs all finite poles, `A / (D y) = (U y)′ + B₀ / y` with
`U = W / V ∈ ℚ(x)` and `deg B₀ ≤ deg p - 2`; this is a polynomial identity
`2 A V² = D (2 (W′V - WV′) p + W V p′ + 2 B₀ V²)`, checked by the kernel. Then
(`hyp_decides_cert`) `∫ A / (D y)` is elementary iff `B₀ = 0` (antiderivative `U y`).

`hypCertSolve` finds `W`, `B₀` (with `V = D`) by linear algebra (`nullBasis`); its output is
checked (`hypCertDecide`), so the decision `hypCertDecide p A D = some b` is always correct
(`hypCertDecide_spec`). It returns `none` when no such decomposition exists — exactly when the
integrand has a genuine simple-pole (logarithmic) part, whose decision needs the torsion test for
divisors on the curve (not formalised).
-/

open Polynomial

namespace Differential

section Cert

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

omit [Algebra Kc E] [Differential Kc] [DifferentialAlgebra Kc E] [CharZero Kc] in
/-- `A / (D y) = (W/V · y)′ + B₀ / y` from the polynomial identity. -/
lemma hyp_cert_identity (x y : E) (hx : x′ = 1) (p A D W V B0 : ℚ[X])
    (hy : y ^ 2 = aeval x p) (hy0 : y ≠ 0) (hD : aeval x D ≠ 0) (hV : aeval x V ≠ 0)
    (hid : A * 2 * V ^ 2 = D * (2 * (derivative W * V - W * derivative V) * p +
      W * V * derivative p + 2 * B0 * V ^ 2)) :
    aeval x A / (aeval x D * y) = (aeval x W / aeval x V * y)′ + aeval x B0 / y := by
  have hyd : y′ = aeval x (derivative p) / (2 * y) := by
    have := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul] at this
    rw [deriv_aeval_rat x hx] at this
    rw [eq_div_iff (mul_ne_zero two_ne_zero hy0)]
    linear_combination this
  have h2 := congrArg (aeval x) hid
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat] at h2
  rw [Derivation.leibniz, Derivation.leibniz_div, hyd, deriv_aeval_rat x hx,
    deriv_aeval_rat x hx]
  simp only [smul_eq_mul]
  rw [← hy] at h2
  field_simp
  linear_combination h2

/-- **Hyperelliptic integrals whose poles are absorbed by the Hermite reduction are decided**:
given a checked identity `A / (D y) = (W/V · y)′ + B₀ / y`, `∫ A / (D y)` is elementary iff
`B₀ = 0`. -/
theorem hyp_decides_cert (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (p : CPoly ℚ) (hp : Squarefree (CPoly.toPoly p)) (hodd : Odd (CPoly.toPoly p).natDegree)
    (hy : y ^ 2 = aeval x (CPoly.toPoly p)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D W V B0 : ℚ[X]) (hD : D ≠ 0) (hV : V ≠ 0)
    (hid : A * 2 * V ^ 2 = D * (2 * (derivative W * V - W * derivative V) * CPoly.toPoly p +
      W * V * derivative (CPoly.toPoly p) + 2 * B0 * V ^ 2))
    (hdeg : B0 = 0 ∨ B0.natDegree + 2 ≤ (CPoly.toPoly p).natDegree) :
    HasElementaryIntegral (aeval x A / (aeval x D * y)) ↔ B0 = 0 := by
  have hp0 : CPoly.toPoly p ≠ 0 := hp.ne_zero
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ P : ℚ[X], P ≠ 0 → aeval x P ≠ 0 := fun P hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hy0 : y ≠ 0 := by rintro rfl; apply hne _ hp0; rw [← hy]; ring
  rw [hyp_cert_identity x y hx _ A D W V B0 hy hy0 (hne D hD) (hne V hV) hid]
  constructor
  · exact hyp_no_elem hC hCall x y hx p hp hodd hy hgen _ B0 hdeg
  · intro h0
    rw [h0, map_zero, zero_div, add_zero]
    exact hasElementaryIntegral_of_deriv _

end Cert

end Differential

namespace CPoly

/-- The columns of the linear system for `2 A D = 2(W′D - WD′)p + WDp′ + 2B₀D²`. -/
def hypCols (p A D : CPoly ℚ) (dW nB : ℕ) : List (CPoly ℚ) :=
  mul [2] (mul A D) ::
    ((List.range (dW + 1)).map fun i ↦
      add (mul [2] (mul (sub (mul (deriv (monomial i 1)) D) (mul (monomial i 1) (deriv D))) p))
        (mul (mul (monomial i 1) D) (deriv p))) ++
    ((List.range nB).map fun j ↦ mul [2] (mul (monomial j 1) (mul D D)))

/-- **An untrusted solver**: `(W, V, B₀)` with `V = D`, or `none`. -/
def hypCertSolve (p A D : CPoly ℚ) : Option (CPoly ℚ × CPoly ℚ × CPoly ℚ) :=
  let n := (trim p).length - 1
  let nB := n - 1
  let dW := A.length + D.length
  match (nullBasis (hypCols p A D dW nB)).find? (fun u ↦ u.getD 0 0 ≠ 0) with
  | some u =>
    let c := fun k ↦ -(u.getD k 0) / u.getD 0 0
    some ((List.range (dW + 1)).map (fun i ↦ c (i + 1)), D,
      (List.range nB).map (fun j ↦ c (dW + 2 + j)))
  | none => none

/-- The kernel check of a decomposition. -/
def hypCertCheck (p A D W V B0 : CPoly ℚ) : Bool :=
  !isZero D && !isZero V && decide (B0.length + 1 ≤ (trim p).length - 1) &&
    beq (mul (mul A [2]) (mul V V))
      (mul D (add (add (mul (mul [2] (sub (mul (deriv W) V) (mul W (deriv V)))) p)
        (mul (mul W V) (deriv p))) (mul (mul [2] B0) (mul V V))))

/-- **The decision** (`some b`) or `none` (a genuine logarithmic part). -/
def hypCertDecide (p A D : CPoly ℚ) : Option Bool :=
  match hypCertSolve p A D with
  | some (W, V, B0) => if hypCertCheck p A D W V B0 then some (isZero B0) else none
  | none => none

lemma natDegree_toPoly_le_length {R : Type*} [CommRing R] (q : CPoly R) :
    (toPoly q).natDegree ≤ q.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_toPoly]
  exact List.getD_eq_default _ _ (by omega)

/-- **Specification of the decision.** -/
theorem hypCertDecide_spec (p A D : CPoly ℚ) (b : Bool) (h : hypCertDecide p A D = some b) :
    ∃ W V B0 : CPoly ℚ, toPoly D ≠ 0 ∧ toPoly V ≠ 0 ∧
      toPoly A * 2 * toPoly V ^ 2 = toPoly D * (2 * (derivative (toPoly W) * toPoly V -
        toPoly W * derivative (toPoly V)) * toPoly p + toPoly W * toPoly V * derivative (toPoly p) +
          2 * toPoly B0 * toPoly V ^ 2) ∧
      (toPoly B0 = 0 ∨ (toPoly B0).natDegree + 2 ≤ (toPoly p).natDegree) ∧
      (b = true ↔ toPoly B0 = 0) := by
  unfold hypCertDecide at h
  split at h
  · rename_i W V B0 _
    split_ifs at h with hc
    · simp only [Option.some.injEq] at h
      subst h
      simp only [hypCertCheck, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hD, hV⟩, hlen⟩, hbeq⟩ := hc
      refine ⟨W, V, B0, fun h0 ↦ ?_, fun h0 ↦ ?_, ?_, ?_, isZero_iff _⟩
      · rw [← isZero_iff] at h0; rw [h0] at hD; exact Bool.noConfusion hD
      · rw [← isZero_iff] at h0; rw [h0] at hV; exact Bool.noConfusion hV
      · have := (beq_iff _ _).mp hbeq
        simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv] at this
        have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
          rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
        rw [h2] at this
        linear_combination this
      · by_cases h0 : toPoly B0 = 0
        · exact Or.inl h0
        · right
          have hlen0 : 1 ≤ B0.length := by
            rcases B0 with _ | _
            · simp at h0
            · simp
          have := natDegree_toPoly_le_length B0
          by_cases htr : trim p = []
          · rw [htr] at hlen; simp at hlen
          · have := (natDegree_toPoly_of_trim_ne_nil htr).1
            omega
  · exact absurd h (by simp)

end CPoly
