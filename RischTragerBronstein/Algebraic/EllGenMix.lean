import RischTragerBronstein.Algebraic.EllAlgoMix
import RischTragerBronstein.Algebraic.EllGenTw

/-!
# General integrands with residues in two quadratic classes

`residuePtsMix` splits the non-zero Hermite residues `c_α` into the class of the first one
(`p(α) ∈ d₁ ℚ²`) and the rest, which must form one other class `d₂ ℚ²`; `ellDecideGenMix` runs
the kernel-checked Hermite identity and `ellDecideMix`. `ellDecideAll` tries `ellDecideAny`
(rational residues, then one twist class) and then `ellDecideGenMix`. Every answer is correct
(`ellDecideGenMix_spec`, `ellDecideAll_spec`).
-/

open Polynomial

namespace EllAlgo

open CPoly

/-- Membership of `α` in the class `d · ℚ²` (with a non-zero root). -/
def inCls (p : CPoly ℚ) (d : ℤ) (q : ℚ × ℚ) : Bool :=
  (qsqrt (residuePts.evalQ p q.1 / d)).isSome && qsqrt (residuePts.evalQ p q.1 / d) != some 0

/-- The residue data split into two classes: `(pts₁, pts₂, D′, d₁, d₂)`. -/
def residuePtsMix (p : CPoly ℚ) (αs cs : List ℚ) :
    Option (List (ℚ × ℚ × ℤ) × List (ℚ × ℚ × ℤ) × ℕ × ℤ × ℤ) :=
  let data := (αs.zip cs).filter fun q ↦ q.2 ≠ 0
  match data with
  | [] => none
  | q₀ :: _ =>
    let d₁ : ℤ := (residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den
    let cls₁ := data.filter (inCls p d₁)
    let rest := data.filter fun q ↦ !inCls p d₁ q
    match rest with
    | [] => none
    | r₀ :: _ =>
      let d₂ : ℤ := (residuePts.evalQ p r₀.1).num * (residuePts.evalQ p r₀.1).den
      if d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ rest.all (inCls p d₂) = true ∧ qsqrt ((d₁ * d₂ : ℤ) : ℚ) = none then
        let g := fun (d : ℤ) (q : ℚ × ℚ) ↦ (qsqrt (residuePts.evalQ p q.1 / d)).getD 1
        let rs₁ := cls₁.map fun q ↦ (q.1, g d₁ q, q.2 / (g d₁ q * d₁))
        let rs₂ := rest.map fun q ↦ (q.1, g d₂ q, q.2 / (g d₂ q * d₂))
        let D' := ((rs₁ ++ rs₂).map fun q ↦ q.2.2.den).foldr Nat.lcm 1
        some (rs₁.map fun q ↦ (q.1, q.2.1, (q.2.2 * (D' : ℚ)).num),
          rs₂.map fun q ↦ (q.1, q.2.1, (q.2.2 * (D' : ℚ)).num), D', d₁, d₂)
      else none

/-- **The general procedure with residues in two quadratic classes.** -/
def ellDecideGenMix (a b c : ℤ) (A D : CPoly ℚ) (fuel : ℕ) : Option Bool :=
  match ellHermiteRaw (pOf a b c) A D with
  | some (W, B₀, αs, cs) =>
    match residuePtsMix (pOf a b c) αs cs with
    | some (pts₁, pts₂, D', d₁, d₂) =>
      if genCheck (pOf a b c) A D W (fracG B₀ D' (twPts d₁ pts₁ ++ twPts d₂ pts₂)) then
        ellDecideMix a b c d₁ d₂ B₀ pts₁ pts₂ D' fuel
      else none
    | none => none
  | none => none

/-- **Dispatcher**: rational residues, one twist class, then two classes. -/
def ellDecideAll (a b c : ℤ) (A D : CPoly ℚ) (fuel : ℕ) : Option Bool :=
  match ellDecideAny a b c A D fuel with
  | some r => some r
  | none => ellDecideGenMix a b c A D fuel

lemma fracG_append (B : CPoly ℚ) (D : ℕ) {E : Type*} [Field E] [CharZero E] (x : E)
    (hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0) (l₁ l₂ : List (ℚ × ℚ × ℤ)) :
    aeval x (toPoly (fracG B D (l₁ ++ l₂)).1) / aeval x (toPoly (fracG B D (l₁ ++ l₂)).2) =
      aeval x (toPoly B) + (l₁.map fun q ↦ (((q.2.2 : ℚ) / D * q.2.1 : ℚ) : E) /
        (x - ((q.1 : ℚ) : E))).sum + (l₂.map fun q ↦ (((q.2.2 : ℚ) / D * q.2.1 : ℚ) : E) /
        (x - ((q.1 : ℚ) : E))).sum := by
  rw [(fracG_spec x hne B D _).2, List.map_append, List.sum_append, add_assoc]

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Correctness of `ellDecideGenMix`.** -/
theorem ellDecideGenMix_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (fuel : ℕ) (ans : Bool) (h : ellDecideGenMix a b c A D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hp : toPoly (pOf a b c) = X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) :=
    toPoly_pOf a b c
  have hy' : y ^ 2 = aeval x (toPoly (pOf a b c)) := by rw [hp, hy]; simp
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hne _ (show toPoly (pOf a b c) ≠ 0 by rw [hp]; exact hsq.ne_zero)
    rw [← hy']; ring
  unfold ellDecideGenMix at h
  split at h
  · rename_i W B₀ αs cs _
    split at h
    · rename_i pts₁ pts₂ D' d₁ d₂ _
      split_ifs at h with hchk
      have hans := ellDecideMix_spec hC hCall x y hx a b c hsq hy hgen d₁ d₂ B₀ pts₁ pts₂ D' fuel
        ans h
      unfold genCheck at hchk
      simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, isZero_iff] at hchk
      obtain ⟨⟨hD0, hG0⟩, hbeq⟩ := hchk
      have hid := (beq_iff _ _).mp hbeq
      have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
        rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
      simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, h2] at hid
      set G := fracG B₀ D' (twPts d₁ pts₁ ++ twPts d₂ pts₂)
      have e := gen_identity x y hx (toPoly (pOf a b c)) (toPoly A) (toPoly D) (toPoly W) (toPoly D)
        (toPoly G.1) (toPoly G.2) hy' hy0 (hne _ hD0) (hne _ hD0) (hne _ hG0)
        (by linear_combination hid)
      rw [e, hasElementaryIntegral_deriv_add_iff', fracG_append B₀ D' x hne, hans]
      simp only [twPts, List.map_map, Function.comp_def]
      push_cast
      simp only [mul_assoc]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **Correctness of `ellDecideAll`.** -/
theorem ellDecideAll_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (fuel : ℕ) (ans : Bool) (h : ellDecideAll a b c A D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold ellDecideAll at h
  split at h
  · rename_i r hr
    simp only [Option.some.injEq] at h
    subst h
    exact ellDecideAny_spec hC hCall x y hx a b c hsq hy hgen A D fuel r hr
  · exact ellDecideGenMix_spec hC hCall x y hx a b c hsq hy hgen A D fuel ans h

end Spec

end EllAlgo
