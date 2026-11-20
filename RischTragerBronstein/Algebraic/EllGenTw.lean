import RischTragerBronstein.Algebraic.EllGen
import RischTragerBronstein.Algebraic.EllCompleteTw

/-!
# General integrands with twisted residues

`ellDecideGenTw a b c A D fuel`: as `ellDecideGen`, but the residues `c_α` may sit at points with
irrational `y`: if all `p(α)` (with `c_α ≠ 0`) lie in one class `d · ℚ²`, the remainder is handed
to `ellDecideTw` (with `β = γ d`, `c_α = (z/D′) γ d`). `ellDecideGenTw_spec`: every answer is
correct.
-/

open Polynomial

namespace EllAlgo

open CPoly

/-- The twisted residue data `(pts, D′, d)`: `p(α) = d γ²`, `c_α = (z/D′) γ d`. -/
def residuePtsTw (p : CPoly ℚ) (αs cs : List ℚ) : Option (List (ℚ × ℚ × ℤ) × ℕ × ℤ) :=
  let data := (αs.zip cs).filter fun q ↦ q.2 ≠ 0
  match data with
  | [] => none
  | q₀ :: _ =>
    let v₀ := residuePts.evalQ p q₀.1
    let d : ℤ := v₀.num * v₀.den
    let gammas := data.map fun q ↦ qsqrt (residuePts.evalQ p q.1 / d)
    if d ≠ 0 ∧ gammas.all (fun o ↦ o.isSome && o != some 0) then
      let rs := (data.zip gammas).map fun q ↦
        (q.1.1, (q.2.getD 1), q.1.2 / (q.2.getD 1 * (d : ℚ)))
      let D' := (rs.map fun q ↦ q.2.2.den).foldr Nat.lcm 1
      some (rs.map fun q ↦ (q.1, q.2.1, (q.2.2 * (D' : ℚ)).num), D', d)
    else none

/-- The Hermite solve returning the raw residues. -/
def ellHermiteRaw (p A D : CPoly ℚ) : Option (CPoly ℚ × CPoly ℚ × List ℚ × List ℚ) :=
  let αs := (ratRootsQ D).dedup.filter fun α ↦ residuePts.evalQ D α == 0 &&
    residuePts.evalQ p α != 0
  let nB := (trim p).length - 2
  let dW := A.length + D.length
  match (nullBasis (genCols p A D αs dW nB)).find? (fun u ↦ u.getD 0 0 ≠ 0) with
  | some u =>
    let co := fun k ↦ -(u.getD k 0) / u.getD 0 0
    some ((List.range (dW + 1)).map fun i ↦ co (i + 1), (List.range nB).map fun j ↦ co (dW + 2 + j),
      αs, (List.range αs.length).map fun k ↦ co (dW + 2 + nB + k))
  | none => none

/-- `(pts with β := γ d)`, for `fracG`. -/
def twPts (d : ℤ) (pts : List (ℚ × ℚ × ℤ)) : List (ℚ × ℚ × ℤ) :=
  pts.map fun q ↦ (q.1, q.2.1 * d, q.2.2)

/-- **The general decision procedure with twisted residues.** -/
def ellDecideGenTw (a b c : ℤ) (A D : CPoly ℚ) (fuel : ℕ) : Option Bool :=
  match ellHermiteRaw (pOf a b c) A D with
  | some (W, B₀, αs, cs) =>
    match residuePtsTw (pOf a b c) αs cs with
    | some (pts, D', d) =>
      if genCheck (pOf a b c) A D W (fracG B₀ D' (twPts d pts)) then
        ellDecideTw a b c d B₀ pts D' fuel
      else none
    | none => none
  | none => none

/-- **Dispatcher**: rational residues first, else one twist class. -/
def ellDecideAny (a b c : ℤ) (A D : CPoly ℚ) (fuel : ℕ) : Option Bool :=
  match ellDecideGen a b c A D fuel with
  | some r => some r
  | none => ellDecideGenTw a b c A D fuel

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Correctness of `ellDecideGenTw`.** -/
theorem ellDecideGenTw_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (fuel : ℕ) (ans : Bool) (h : ellDecideGenTw a b c A D fuel = some ans) :
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
  unfold ellDecideGenTw at h
  split at h
  · rename_i W B₀ αs cs _
    split at h
    · rename_i pts D' d _
      split_ifs at h with hchk
      have hans := ellDecideTw_spec hC hCall x y hx a b c hsq hy hgen d B₀ pts D' fuel ans h
      unfold genCheck at hchk
      simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, isZero_iff] at hchk
      obtain ⟨⟨hD0, hG0⟩, hbeq⟩ := hchk
      have hid := (beq_iff _ _).mp hbeq
      have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
        rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
      simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, h2] at hid
      have e := gen_identity x y hx (toPoly (pOf a b c)) (toPoly A) (toPoly D) (toPoly W) (toPoly D)
        (toPoly (fracG B₀ D' (twPts d pts)).1) (toPoly (fracG B₀ D' (twPts d pts)).2) hy' hy0
        (hne _ hD0) (hne _ hD0) (hne _ hG0) (by linear_combination hid)
      obtain ⟨_, hfr⟩ := fracG_spec x hne B₀ D' (twPts d pts)
      rw [e, hasElementaryIntegral_deriv_add_iff', hfr, hans]
      simp only [twPts, List.map_map, Function.comp_def]
      push_cast
      simp only [mul_assoc]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **Correctness of the dispatcher.** -/
theorem ellDecideAny_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (fuel : ℕ) (ans : Bool) (h : ellDecideAny a b c A D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold ellDecideAny at h
  split at h
  · rename_i r hr
    simp only [Option.some.injEq] at h
    subst h
    exact ellDecideGen_spec hC hCall x y hx a b c hsq hy hgen A D fuel r hr
  · exact ellDecideGenTw_spec hC hCall x y hx a b c hsq hy hgen A D fuel ans h

end Spec

end EllAlgo
