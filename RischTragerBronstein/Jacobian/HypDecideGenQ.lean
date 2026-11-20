import RischTragerBronstein.Jacobian.HypDecideR
import RischTragerBronstein.Algebraic.EllDecideGenQ
import RischTragerBronstein.Algebraic.HypLogSearch

/-!
# The Hermite front end in any genus

`hypDecideGenQ f g A D`: for `∫ A dx / (D √f)` (`f ∈ ℤ[x]`, degree `2g + 1`, `D ≠ 0` arbitrary):
1. Hermite reduction `A/(D y) = (W/D · y)′ + T/(S y)` by linear algebra (`colsG`, as in
   `ellDecideGenQ`), `S` the part of the squarefree part of `D` coprime to `f`;
2. partial fractions of `T/S` at the roots of `S` (`pfPts`): answered when every root is an
   integer `α` with `f(α)` a nonzero square `b²`; the decomposition is re-checked
   (`T · G_d = G_n · S`);
3. `hypDecideG` on the result.

`hypDecideGenQ_spec`: every answer is correct.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad

namespace Jac

/-- Integer square root, if exact. -/
def isqrtZ (c : ℤ) : Option ℤ :=
  if 0 ≤ c ∧ ((c.toNat.sqrt : ℕ) : ℤ) ^ 2 = c then some (c.toNat.sqrt : ℤ) else none

lemma isqrtZ_spec {c b : ℤ} (h : isqrtZ c = some b) : b ^ 2 = c := by
  unfold isqrtZ at h
  split_ifs at h with hc
  cases h; exact hc.2

/-- The partial-fraction points `(α, b, c_α / b)` of `T/S` (all roots rational, `f(α) = b²`). -/
def pfPtsR (f : List ℤ) (T S : CPoly ℚ) : Option (List (ℚ × ℚ × ℚ)) :=
  (ratRootsD S).mapM fun α ↦
    (qsqrt (evalC (f.map (Int.castRingHom ℚ)) α)).bind fun b ↦
      if b = 0 then none else some (α, b, evalC T α / evalC (deriv S) α / b)

/-- **The procedure.** -/
def hypDecideGenQ (f : List ℤ) (g : ℕ) (A D : CPoly ℚ) : Option Bool :=
  if isZero D then none
  else
    let p : CPoly ℚ := f.map (Int.castRingHom ℚ)
    let S := nbPart p D
    let dW := A.length + D.length
    let nT := A.length + 2 * D.length + S.length + f.length + 3
    match linSolve (colsG p D S dW nT) (mul [2] (mul (mul A D) S)) with
    | none => none
    | some cs =>
      let T := cs.drop dW
      match pfPtsR f T S with
      | none => none
      | some raw =>
        let keep := raw.filter fun t ↦ t.2.2 ≠ 0
        let N := (keep.map fun t ↦ t.2.2.den).foldr Nat.lcm 1
        let pts : List (ℚ × ℚ × ℤ) := keep.map fun t ↦ (t.1, t.2.1, (t.2.2 * (N : ℚ)).num)
        let B := (divMod T S).1
        if (CPoly.beq (CPoly.mul T (fracG B N pts).2) (CPoly.mul (fracG B N pts).1 S) &&
            decide (N ≠ 0)) = true then
          hypDecideR f g pts B N
        else none

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 3200000 in
/-- **Every answer of `hypDecideGenQ` is correct.** -/
theorem hypDecideGenQ_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {f : List ℤ} {g : ℕ} {A D : CPoly ℚ} {ans : Bool} (h : hypDecideGenQ f g A D = some ans)
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ)))
    (hgen : ∀ z : E, InHyp Kc x y z) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  classical
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hpf : toPoly (f.map (Int.castRingHom ℚ)) = (toPoly f).map (Int.castRingHom ℚ) :=
    toPoly_map_list _ _
  have hy' : y ^ 2 = aeval x (toPoly (f.map (Int.castRingHom ℚ))) := by rw [hpf]; exact hy
  unfold hypDecideGenQ at h
  split_ifs at h with hDz
  have hD : toPoly D ≠ 0 := fun h0 ↦ hDz ((isZero_iff D).mpr h0)
  simp only at h
  split at h
  · cases h
  rename_i cs hls
  split at h
  · cases h
  rename_i raw hraw
  split_ifs at h with hc
  set p : CPoly ℚ := f.map (Int.castRingHom ℚ)
  set S := nbPart p D
  set T := cs.drop (A.length + D.length)
  set keep := raw.filter fun t ↦ t.2.2 ≠ 0
  set N := (keep.map fun t ↦ t.2.2.den).foldr Nat.lcm 1
  set pts : List (ℚ × ℚ × ℤ) := keep.map fun t ↦ (t.1, t.2.1, (t.2.2 * (N : ℚ)).num)
  set B := (divMod T S).1
  have hc' := hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨h1, h7⟩ := hc'
  have W := hypDecideR_wf h
  have hp0 : toPoly p ≠ 0 := by rw [toPoly_map_list]; exact W.hsq.ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hne _ hp0
    rw [← hy']; ring
  have hid := hermite_of_linSolve _ _ _ _ _ _ _ hls
  have hM := nbPart_ne_zero p D hD
  have e := gen_identity x y hx (toPoly p) (toPoly A) (toPoly D)
    (toPoly (cs.take (A.length + D.length))) (toPoly D) (toPoly T) (toPoly S) hy' hy0
    (hne _ hD) (hne _ hD) (hne _ hM) (by unfold LDK at hid; linear_combination toPoly D * hid)
  rw [e, hasElementaryIntegral_deriv_add_iff', div_div]
  obtain ⟨hGd0, hfr⟩ := fracG_spec x hne B N pts
  have hcross := (beq_iff _ _).mp h1
  simp only [toPoly_mul] at hcross
  have hTS : aeval x (toPoly T) / aeval x (toPoly S) =
      aeval x (toPoly (fracG B N pts).1) / aeval x (toPoly (fracG B N pts).2) := by
    rw [div_eq_div_iff (hne _ hM) (hne _ hGd0)]
    have := congrArg (aeval x) hcross
    simp only [map_mul] at this
    linear_combination this
  rw [← div_div, hTS, hfr]
  exact hypDecideR_spec hC hCall x y hx h7 h hy hgen

end Spec

end Jac
