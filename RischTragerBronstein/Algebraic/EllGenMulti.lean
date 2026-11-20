import RischTragerBronstein.Algebraic.EllAlgoMulti
import RischTragerBronstein.Algebraic.EllGenMix

/-!
# General integrands with residues in any number of quadratic classes

`groupCls` groups the non-zero Hermite residues by the square class of `p(α)` (the class of the
first remaining one, then recursively the rest); `residuePtsMulti` computes the twisted points and
the common denominator; `ellDecideGenMulti` runs the kernel-checked Hermite identity and
`ellDecideMulti`. `ellDecideEll` tries `ellDecideAll` first. Every answer is correct
(`ellDecideGenMulti_spec`, `ellDecideEll_spec`).
-/

open Polynomial

namespace EllAlgo

open CPoly

/-- Group the residue data by square class (`n`: fuel, the length suffices). -/
def groupCls (p : CPoly ℚ) : ℕ → List (ℚ × ℚ) → List (ℤ × List (ℚ × ℚ))
  | 0, _ => []
  | _, [] => []
  | n + 1, q₀ :: t =>
    let d : ℤ := (residuePts.evalQ p q₀.1).num * (residuePts.evalQ p q₀.1).den
    (d, (q₀ :: t).filter (inCls p d)) :: groupCls p n ((q₀ :: t).filter fun q ↦ !inCls p d q)

/-- The twisted points of one class, with numerators over `D′`. -/
def classPts (p : CPoly ℚ) (D' : ℕ) (d : ℤ) (qs : List (ℚ × ℚ)) : List (ℚ × ℚ × ℤ) :=
  qs.map fun q ↦ (q.1, (qsqrt (residuePts.evalQ p q.1 / d)).getD 1,
    (q.2 / ((qsqrt (residuePts.evalQ p q.1 / d)).getD 1 * d) * (D' : ℚ)).num)

/-- The residue data in classes, with the common denominator. -/
def residuePtsMulti (p : CPoly ℚ) (αs cs : List ℚ) : List (ℤ × List (ℚ × ℚ × ℤ)) × ℕ :=
  let data := (αs.zip cs).filter fun q ↦ q.2 ≠ 0
  let groups := groupCls p data.length data
  let D' := (groups.flatMap fun g ↦ g.2.map fun q ↦
    (q.2 / ((qsqrt (residuePts.evalQ p q.1 / g.1)).getD 1 * g.1)).den).foldr Nat.lcm 1
  (if groups = [] then [(1, [])] else groups.map fun g ↦ (g.1, classPts p D' g.1 g.2), D')

/-- All the points, twisted (`β = γ d`), for `fracG`. -/
def allTw (cls : List (ℤ × List (ℚ × ℚ × ℤ))) : List (ℚ × ℚ × ℤ) :=
  cls.flatMap fun g ↦ twPts g.1 g.2

/-- **The general procedure with residues in any number of quadratic classes.** -/
def ellDecideGenMulti (a b c : ℤ) (A D : CPoly ℚ) (fuel : ℕ) : Option Bool :=
  match ellHermiteRaw (pOf a b c) A D with
  | some (W, B₀, αs, cs) =>
    let r := residuePtsMulti (pOf a b c) αs cs
    if genCheck (pOf a b c) A D W (fracG B₀ r.2 (allTw r.1)) then
      ellDecideMulti a b c B₀ r.1 r.2 fuel
    else none
  | none => none

/-- **Dispatcher**: `ellDecideAll`, then any number of classes. -/
def ellDecideEll (a b c : ℤ) (A D : CPoly ℚ) (fuel : ℕ) : Option Bool :=
  match ellDecideAll a b c A D fuel with
  | some r => some r
  | none => ellDecideGenMulti a b c A D fuel

lemma sum_allTw {E : Type*} [Field E] (x : E) (D : ℕ) :
    ∀ cls : List (ℤ × List (ℚ × ℚ × ℤ)),
      ((allTw cls).map fun q ↦ (((q.2.2 : ℚ) / D * q.2.1 : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum =
        (cls.map fun g ↦ classSum x D g.1 g.2).sum
  | [] => by simp [allTw]
  | g :: t => by
    rw [List.map_cons, List.sum_cons, ← sum_allTw x D t]
    simp only [allTw, List.flatMap_cons, List.map_append, List.sum_append, twPts, List.map_map,
      Function.comp_def, classSum]
    congr 1
    congr 1
    refine List.map_congr_left fun q _ ↦ ?_
    push_cast; ring

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Correctness of `ellDecideGenMulti`.** -/
theorem ellDecideGenMulti_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (fuel : ℕ) (ans : Bool) (h : ellDecideGenMulti a b c A D fuel = some ans) :
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
  unfold ellDecideGenMulti at h
  split at h
  · rename_i W B₀ αs cs _
    dsimp only at h
    split_ifs at h with hchk
    set r := residuePtsMulti (pOf a b c) αs cs
    have hans := ellDecideMulti_spec hC hCall x y hx a b c hsq hy hgen B₀ r.1 r.2 fuel ans h
    unfold genCheck at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, isZero_iff] at hchk
    obtain ⟨⟨hD0, hG0⟩, hbeq⟩ := hchk
    have hid := (beq_iff _ _).mp hbeq
    have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
      rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
    simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, h2] at hid
    set G := fracG B₀ r.2 (allTw r.1)
    have e := gen_identity x y hx (toPoly (pOf a b c)) (toPoly A) (toPoly D) (toPoly W) (toPoly D)
      (toPoly G.1) (toPoly G.2) hy' hy0 (hne _ hD0) (hne _ hD0) (hne _ hG0)
      (by linear_combination hid)
    rw [e, hasElementaryIntegral_deriv_add_iff', (fracG_spec x hne B₀ r.2 _).2, sum_allTw, hans]
    rfl
  · exact absurd h (by simp)

/-- **Correctness of `ellDecideEll`.** -/
theorem ellDecideEll_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (fuel : ℕ) (ans : Bool) (h : ellDecideEll a b c A D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold ellDecideEll at h
  split at h
  · rename_i r hr
    simp only [Option.some.injEq] at h
    subst h
    exact ellDecideAll_spec hC hCall x y hx a b c hsq hy hgen A D fuel r hr
  · exact ellDecideGenMulti_spec hC hCall x y hx a b c hsq hy hgen A D fuel ans h

end Spec

end EllAlgo
