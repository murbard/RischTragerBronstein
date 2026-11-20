import RischTragerBronstein.Jacobian.Scale
import RischTragerBronstein.Jacobian.TorsionDecideU

/-!
# Torsion of divisors on rational points

`torsionDecideR f g Γ` (`Γ` on rational points of `y² = f(x)`, `f ∈ ℤ[x]`): with `d` the lcm of
the denominators of the abscissae, `(x, y) ↦ (d² x, d^{2g+1} y)` maps the curve to
`Y² = F(X)`, `F_k = f_k d^{2(2g+1−k)} ∈ ℤ[X]` (`scaleList`), and `Γ` to integral points
(checked). `torsionDecideU` decides there, and `principalMul_scale_iff` transports the answer
back (`torsionDecideR_spec`).
-/

open Polynomial CPoly CPoly.Kron

namespace Jac

/-- `F_k = f_k d^{2(2g+1−k)}`. -/
def scaleList (f : List ℤ) (g d : ℕ) : List ℤ :=
  (List.range (2 * g + 2)).map fun k ↦ f.getD k 0 * (d : ℤ) ^ (2 * (2 * g + 1 - k))

lemma toPoly_scaleList {f : List ℤ} {g d : ℕ} (hlen : f.length = 2 * g + 2) (hd : d ≠ 0) :
    (toPoly (scaleList f g d)).map (Int.castRingHom ℚ) =
      scaleF ((d : ℚ) ^ 2) ((d : ℚ) ^ (2 * g + 1)) ((toPoly f).map (Int.castRingHom ℚ)) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  ext k
  rw [coeff_map, coeff_toPoly, scaleF, coeff_C_mul, comp_C_mul_X_coeff, coeff_map, coeff_toPoly]
  by_cases hk : k < 2 * g + 2
  · rw [scaleList, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getElem_range]
    simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [inv_pow, ← pow_mul, ← pow_mul,
      show (2 * g + 1) * 2 = 2 * (2 * g + 1 - k) + 2 * k by omega, pow_add]
    field_simp
  · rw [List.getD_eq_default _ _ (by simp [scaleList]; omega),
      List.getD_eq_default _ _ (by omega)]
    simp

/-- The rescaled points, as integers. -/
def scaleΓInt (Γ : EDiv ℚ) (t e : ℚ) : EDiv ℤ :=
  Γ.map fun q ↦ ((t * q.1).num, (e * q.2.1).num, q.2.2)

/-- **Torsion decision for divisors on rational points** (`none`: the data is degenerate). -/
def torsionDecideR (f : List ℤ) (g : ℕ) (Γ : EDiv ℚ) : Option Bool :=
  let d : ℕ := (Γ.map fun q ↦ q.1.den).foldr Nat.lcm 1
  let t : ℚ := (d : ℚ) ^ 2
  let e : ℚ := (d : ℚ) ^ (2 * g + 1)
  let F := scaleList f g d
  let ΓI := scaleΓInt Γ t e
  let ok1 : Bool := Γ.all fun q ↦ (t * q.1).den == 1 && (e * q.2.1).den == 1
  let ok2 : Bool := decide (f.length = 2 * g + 2)
  let ok3 : Bool := decide (d ≠ 0)
  let ok4 : Bool := decide (F.length = 2 * g + 2)
  let ok5 : Bool := decide (F.getD (2 * g + 1) 0 ≠ 0)
  let ok6 : Bool := squarefreeCheck (F.map (Int.castRingHom ℚ))
  let ok7 : Bool := decide (∀ q ∈ ΓI, q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = evalC F q.1)
  let ok8 : Bool := decide (ΓI.Pairwise fun u v : ℤ × ℤ × ℕ ↦ u.1 ≠ v.1)
  if hc : (ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8) = true then
    some (torsionDecideU (f := F) (g := g) (Γ := ΓI) (by
      simp only [Bool.and_eq_true, ok4, ok5, ok6, ok7, ok8, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨-, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
      exact ⟨h4, h5, by
        have := squarefreeCheck_sound (s := F.map (Int.castRingHom ℚ)) h6
        rwa [toPoly_map_list] at this, h7, h8⟩))
  else none

/-- **Correctness of `torsionDecideR`.** -/
theorem torsionDecideR_spec {f : List ℤ} {g : ℕ} {Γ : EDiv ℚ} {b : Bool}
    (h : torsionDecideR f g Γ = some b) :
    b = true ↔ ∃ n, 1 ≤ n ∧ PrincipalMul ((toPoly f).map (Int.castRingHom ℚ)) g Γ n := by
  unfold torsionDecideR at h
  dsimp only at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  set d : ℕ := (Γ.map fun q ↦ q.1.den).foldr Nat.lcm 1
  set t : ℚ := (d : ℚ) ^ 2
  set e : ℚ := (d : ℚ) ^ (2 * g + 1)
  have hc' := hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc'
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast h3
  have ht : t ≠ 0 := pow_ne_zero _ hdq
  have he : e ≠ 0 := pow_ne_zero _ hdq
  rw [torsionDecideU_iff, toPoly_scaleList h2 h3]
  have hΓ : emap (Int.castRingHom ℚ) (scaleΓInt Γ t e) = scaleΓ t e Γ := by
    unfold emap scaleΓInt scaleΓ
    rw [List.map_map]
    refine List.map_congr_left fun q hq ↦ ?_
    obtain ⟨hx, hy⟩ := h1 q hq
    simp only [Function.comp_apply, eq_intCast, Prod.mk.injEq, and_true]
    exact ⟨Rat.coe_int_num_of_den_eq_one hx, Rat.coe_int_num_of_den_eq_one hy⟩
  rw [hΓ]
  exact exists_congr fun n ↦ and_congr_right fun _ ↦ principalMul_scale_iff ht he

end Jac
