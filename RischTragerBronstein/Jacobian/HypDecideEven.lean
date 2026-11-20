import RischTragerBronstein.Jacobian.HypDecideRat

/-!
# Even degree with a rational root

For `y² = q(x)`, `q ∈ ℚ[x]` squarefree of degree `2g + 2` with `q(e) = 0`, the substitution
`t = 1/(x − e)`, `Y = y t^{g+1}` gives `Y² = P(t)` with `P` of degree `2g + 1`
(`P(t) = t^{2g+1} R(1/t)`, `q(x + e) = x R(x)`). With the derivation rescaled by `−1/t²`,
`hypDecideEven` runs `hypDecideOdd` on the transformed integrand.

* `hypDecideEven_spec`: every answer is correct.
* `hypDecideEven_eventually`, `hypDecideEven_decides`: for all large bounds there is an answer.
-/

open Polynomial CPoly EllAlgo

namespace Jac

/-! ### Polynomial facts -/

lemma toPoly_reverse (L : CPoly ℚ) : toPoly L.reverse = reflect (L.length - 1) (toPoly L) := by
  rcases Nat.eq_zero_or_pos L.length with h0 | hpos
  · simp [List.length_eq_zero_iff.mp h0]
  ext i
  rw [coeff_toPoly, coeff_reflect, coeff_toPoly]
  by_cases hi : i < L.length
  · rw [revAt_le (N := L.length - 1) (i := i) (by omega), List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_reverse,
      List.getD_eq_getElem _ _ (by omega)]
  · rw [revAt_eq_self_of_lt (N := L.length - 1) (i := i) (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

lemma squarefree_reflect {R : ℚ[X]} (hsq : Squarefree R) : Squarefree (reflect R.natDegree R) := by
  set N := R.natDegree
  have hR0 : R ≠ 0 := hsq.ne_zero
  have hP0 : reflect N R ≠ 0 := by rwa [Ne, reflect_eq_zero_iff]
  have hc0 : (reflect N R).coeff 0 ≠ 0 := by
    rw [coeff_reflect, revAt_zero]; exact leadingCoeff_ne_zero.mpr hR0
  rintro a ⟨b, hb⟩
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul, zero_mul] at hb; exact hP0 hb
  have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hb; exact hP0 hb
  have hdeg : a.natDegree + a.natDegree + b.natDegree ≤ N := by
    have h1 : (reflect N R).natDegree ≤ max N R.natDegree := natDegree_reflect_le
    rw [hb, natDegree_mul (mul_ne_zero ha0 ha0) hb0, natDegree_mul ha0 ha0] at h1
    simpa [N] using h1
  set k := N - (a.natDegree + a.natDegree + b.natDegree)
  have hrefl : R = reflect a.natDegree a * reflect a.natDegree a *
      reflect (b.natDegree + k) b := by
    have := reflect_mul (a * a) b (F := a.natDegree + a.natDegree) (G := b.natDegree + k)
      (by rw [natDegree_mul ha0 ha0]) (by omega)
    rw [reflect_mul a a le_rfl le_rfl] at this
    rw [← this, ← hb, show a.natDegree + a.natDegree + (b.natDegree + k) = N by omega,
      reflect_reflect]
  have hu : IsUnit (reflect a.natDegree a) := hsq _ ⟨_, hrefl⟩
  obtain ⟨c, hc, hcC⟩ := Polynomial.isUnit_iff.mp hu
  have haX : a = C c * X ^ a.natDegree := by
    have := congrArg (reflect a.natDegree) hcC
    rw [reflect_reflect, reflect_C] at this
    exact this.symm
  rcases Nat.eq_zero_or_pos a.natDegree with h0 | hpos
  · rw [haX, h0, pow_zero, mul_one]; exact isUnit_C.mpr hc
  · exfalso
    apply hc0
    have : X ∣ reflect N R := by
      rw [hb, haX]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left
        (dvd_pow_self X hpos.ne') _) _) _
    exact X_dvd_iff.mp this

lemma squarefree_comp_add_C {f : ℚ[X]} (hsq : Squarefree f) (e : ℚ) :
    Squarefree (f.comp (X + C e)) := by
  have hsep : IsCoprime f (derivative f) := (PerfectField.separable_iff_squarefree.mpr hsq)
  apply Polynomial.Separable.squarefree
  have h2 := hsep.map (Polynomial.compRingHom (X + C e))
  show IsCoprime _ _
  rw [derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul]
  simpa using h2

/-! ### The procedure -/

/-- The transformed data `(P, Ã, D̃)`. -/
def evenData (q : CPoly ℚ) (e : ℚ) (A D : CPoly ℚ) : Option (CPoly ℚ × CPoly ℚ × CPoly ℚ) :=
  let s := trim (shiftPoly q e)
  let R := s.drop 1
  let g := (R.length - 2) / 2
  let sA := trim (shiftPoly A e)
  let sD := trim (shiftPoly D e)
  if s.getD 0 0 = 0 ∧ R.length = 2 * g + 2 ∧ sA ≠ [] ∧ sD ≠ [] then
    some (R.reverse, smul (-1) (mul sA.reverse (monomial (sD.length - 1 + g + 1) 1)),
      mul sD.reverse (monomial (sA.length - 1 + 2) 1))
  else none

/-- **Even degree with a rational root `e` of `q`.** -/
noncomputable def hypDecideEven (q : CPoly ℚ) (e : ℚ) (A D : CPoly ℚ) (B : ℕ) : Option Bool :=
  if trim A = [] then some true
  else
    match evenData q e A D with
    | some (P, An, Dn) => hypDecideOdd P An Dn B
    | none => none

lemma comp_add_C_ne_zero {F : ℚ[X]} (hF : F ≠ 0) (e : ℚ) : F.comp (X + C e) ≠ 0 := by
  intro h0
  apply hF
  apply Polynomial.funext
  intro a
  have := congrArg (eval (a - e)) h0
  simpa [eval_comp] using this

/-- **`hypDecideEven` answers for all large bounds** (`q` squarefree of degree `2g + 2`,
`q(e) = 0`, `D ≠ 0`). -/
theorem hypDecideEven_eventually (q : CPoly ℚ) {g : ℕ} (hdeg : (toPoly q).natDegree = 2 * g + 2)
    (hsq : Squarefree (toPoly q)) (e : ℚ) (he : (toPoly q).eval e = 0) (A D : CPoly ℚ)
    (hD : toPoly D ≠ 0) : ∃ B0, ∀ B, B0 ≤ B → hypDecideEven q e A D B ≠ none := by
  by_cases hA0 : trim A = []
  · exact ⟨0, fun B _ ↦ by simp [hypDecideEven, hA0]⟩
  set s := trim (shiftPoly q e) with hsdef
  set R := s.drop 1 with hRdef
  set sA := trim (shiftPoly A e)
  set sD := trim (shiftPoly D e)
  have hs : toPoly s = (toPoly q).comp (X + C e) := by rw [toPoly_trim, toPoly_shiftPoly]
  have hne : s ≠ [] := by
    rw [hsdef, Ne, trim_eq_nil_iff, toPoly_shiftPoly]
    exact comp_add_C_ne_zero hsq.ne_zero e
  have hslen : s.length = 2 * g + 3 := by
    rw [length_trim hne, toPoly_shiftPoly, natDegree_comp, natDegree_X_add_C, hdeg, mul_one]
  have hs0 : s.getD 0 0 = 0 := by
    rw [← coeff_toPoly, hs, coeff_zero_eq_eval_zero, eval_comp]
    simpa using he
  have hsplit : s = 0 :: R := by
    obtain ⟨c, L, hcL⟩ := List.exists_cons_of_ne_nil hne
    have hR : R = L := by simp only [R, hcL, List.drop_one, List.tail_cons]
    rw [hcL] at hs0
    simp only [List.getD_cons_zero] at hs0
    rw [hcL, hs0, hR]
  have hsR : toPoly s = X * toPoly R := by
    conv_lhs => rw [hsplit]
    simp
  have hssq : Squarefree (toPoly s) := hs ▸ squarefree_comp_add_C hsq e
  have hRsq : Squarefree (toPoly R) := (hsR ▸ hssq).of_mul_right
  have hR0 : (toPoly R).coeff 0 ≠ 0 := by
    intro h0
    have hX : X ∣ toPoly R := X_dvd_iff.mpr h0
    have : X * X ∣ toPoly s := by rw [hsR]; exact mul_dvd_mul_left X hX
    exact not_isUnit_X (hssq X this)
  have hRlen : R.length = 2 * g + 2 := by simp [R, hslen]
  have hRdeg : (toPoly R).natDegree = 2 * g + 1 := by
    have h1 : (toPoly s).natDegree = 2 * g + 2 := by rw [hs, natDegree_comp, natDegree_X_add_C, hdeg, mul_one]
    rw [hsR, natDegree_mul X_ne_zero hRsq.ne_zero, natDegree_X] at h1
    omega
  have hg : (R.length - 2) / 2 = g := by omega
  have hAne : sA ≠ [] := hA0 ∘ fun h ↦ by
    rw [trim_eq_nil_iff] at h ⊢
    rw [toPoly_shiftPoly] at h
    by_contra hA
    exact comp_add_C_ne_zero hA e h
  have hDne : sD ≠ [] := by
    rw [Ne, trim_eq_nil_iff, toPoly_shiftPoly]
    exact comp_add_C_ne_zero hD e
  -- the facts for `hypDecideOdd`
  have hPlen : R.reverse.length = 2 * g + 2 := by rw [List.length_reverse, hRlen]
  have hPlc : R.reverse.getD (2 * g + 1) 0 ≠ 0 := by
    rw [← coeff_toPoly, toPoly_reverse, coeff_reflect, hRlen, show 2 * g + 2 - 1 = 2 * g + 1 by omega,
      revAt_le le_rfl, Nat.sub_self]
    exact hR0
  have hPsq : Squarefree (toPoly R.reverse) := by
    rw [toPoly_reverse, hRlen, show 2 * g + 2 - 1 = (toPoly R).natDegree by omega]
    exact squarefree_reflect hRsq
  have hDn : toPoly (mul sD.reverse (monomial (sA.length - 1 + 2) 1)) ≠ 0 := by
    rw [toPoly_mul, toPoly_monomial, toPoly_reverse]
    refine mul_ne_zero ?_ (by simp)
    rw [Ne, reflect_eq_zero_iff, ← trim_eq_nil_iff]
    rw [trim_trim]; exact hDne
  obtain ⟨B0, hB0⟩ := hypDecideOdd_eventually R.reverse hPlen hPlc hPsq
    (smul (-1) (mul sA.reverse (monomial (sD.length - 1 + g + 1) 1)))
    (mul sD.reverse (monomial (sA.length - 1 + 2) 1)) hDn
  refine ⟨B0, fun B hB ↦ ?_⟩
  unfold hypDecideEven
  rw [if_neg hA0]
  unfold evenData
  simp only
  rw [← hsdef, ← hRdef, hg, if_pos ⟨hs0, by omega, hAne, hDne⟩]
  exact hB0 B hB

section Spec

open Differential IntermediateField EllAlgo

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `hypDecideEven`.** -/
theorem hypDecideEven_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly ℚ) (e : ℚ) (hy : y ^ 2 = aeval x (toPoly q))
    (hgen : ∀ z : E, InHyp Kc x y z) (A D : CPoly ℚ) (B : ℕ) (ans : Bool)
    (h : hypDecideEven q e A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold hypDecideEven at h
  split_ifs at h with hA0
  · cases h
    have : toPoly A = 0 := (trim_eq_nil_iff A).mp hA0
    simp only [this, map_zero, zero_div, true_iff]
    simpa using hasElementaryIntegral_of_deriv (0 : E)
  split at h
  swap
  · cases h
  rename_i P An Dn hQD
  unfold evenData at hQD
  simp only at hQD
  split_ifs at hQD with hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at hQD
  obtain ⟨hs0, hRlen, hAne, hDne⟩ := hcond
  obtain ⟨rfl, rfl, rfl⟩ := hQD
  set s := trim (shiftPoly q e)
  set R := s.drop 1
  set g := (R.length - 2) / 2
  set sA := trim (shiftPoly A e)
  set sD := trim (shiftPoly D e)
  -- `x` is not a constant
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hxe : x - (e : E) ≠ 0 := by
    intro h0
    have := congrArg (fun z : E ↦ z′) h0
    simp only [map_sub, hx, deriv_ratCast_L, sub_zero, map_zero] at this
    exact one_ne_zero this
  set t : E := 1 / (x - (e : E)) with ht
  have ht0 : t ≠ 0 := one_div_ne_zero hxe
  have hxt : x = 1 / t + (e : E) := by rw [ht]; field_simp; ring
  set Y : E := y * t ^ (g + 1) with hY
  -- `Y² = P(t)`
  have hsplit : s = 0 :: R := by
    have hne : s ≠ [] := by
      intro h0
      have : R = [] := by simp only [R, h0, List.drop_nil]
      rw [this] at hRlen; simp at hRlen
    obtain ⟨c, L, hcL⟩ := List.exists_cons_of_ne_nil hne
    have hR : R = L := by simp only [R, hcL, List.drop_one, List.tail_cons]
    rw [hcL] at hs0
    simp only [List.getD_cons_zero] at hs0
    rw [hcL, hs0, hR]
  have hYP : Y ^ 2 = aeval t (toPoly R.reverse) := by
    have h1 : aeval x (toPoly q) = aeval (1 / t) (toPoly s) := by
      rw [aeval_shift_trim, ← hxt]
    have h2 : aeval (1 / t) (toPoly s) = 1 / t * aeval (1 / t) (toPoly R) := by
      conv_lhs => rw [hsplit]
      simp
    have h3 := aeval_reverse t ht0 R (by intro h0; rw [h0] at hRlen; simp at hRlen)
    rw [hRlen, show 2 * g + 2 - 1 = 2 * g + 1 by omega] at h3
    rw [hY, mul_pow, hy, h1, h2, h3]
    field_simp
    ring
  -- the rescaled derivation
  have ht' : t′ = -t ^ 2 := by
    rw [ht, Derivation.leibniz_div, map_sub, hx, deriv_ratCast_L]
    simp only [Derivation.map_one_eq_zero, smul_eq_mul, mul_zero, sub_zero, mul_one, zero_sub]
    field_simp
  set τ : E := -t ^ 2 with hτ
  have hτ0 : τ ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ ht0)
  let d0 : Derivation ℤ E E := Differential.deriv
  have hd0 : ∀ z : E, d0 z = z′ := fun _ ↦ rfl
  have hconst : ∀ r : Kc, d0 (algebraMap Kc E r) = 0 := fun r ↦ hconstE r
  let D' : Differential E := rescale ⟨d0⟩ (1 / τ)
  have hT' : D'.deriv t = 1 := by
    show 1 / τ * d0 t = 1
    rw [hd0, ht']; exact one_div_mul_cancel hτ0
  have hDA' : @DifferentialAlgebra Kc E _ _ _ _ D' :=
    @DifferentialAlgebra.mk Kc E _ _ _ _ D' (fun r ↦ by
      show 1 / τ * d0 (algebraMap Kc E r) = algebraMap Kc E r′
      rw [hconst, hC, map_zero, mul_zero])
  have hCall' : ∀ z : E, D'.deriv z = 0 → z ∈ Set.range (algebraMap Kc E) := by
    intro z hz
    apply hCall
    have : 1 / τ * d0 z = 0 := hz
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (one_div_ne_zero hτ0)
    · exact h0
  have hgen' : ∀ z : E, InHyp Kc t Y z := by
    have hxX : Kc⟮x⟯ = Kc⟮t⟯ := by
      apply le_antisymm
      · rw [adjoin_simple_le_iff, hxt]
        exact add_mem (div_mem (one_mem _) (mem_adjoin_simple_self _ _))
          (ratCast_mem_adjoin _ _)
      · rw [adjoin_simple_le_iff, ht]
        exact div_mem (one_mem _) (sub_mem (mem_adjoin_simple_self _ _) (ratCast_mem_adjoin _ _))
    intro z
    obtain ⟨α, β, hα, hβ, rfl⟩ := hgen z
    refine ⟨α, β / t ^ (g + 1), hxX ▸ hα,
      div_mem (hxX ▸ hβ) (pow_mem (mem_adjoin_simple_self _ _) _), ?_⟩
    rw [hY]; field_simp
  have hspec := @hypDecideOdd_spec Kc E _ _ _ _ D' hDA' _ _ _ hC hCall' t Y hT' _ hYP hgen'
    _ _ B ans h
  rw [hspec]
  -- transfer back
  have hA := aeval_reverse t ht0 sA hAne
  have hD := aeval_reverse t ht0 sD hDne
  rw [aeval_shift_trim, ← hxt] at hA hD
  have hint : aeval t (toPoly (smul (-1) (mul sA.reverse (monomial (sD.length - 1 + g + 1) 1)))) /
      (aeval t (toPoly (mul sD.reverse (monomial (sA.length - 1 + 2) 1))) * Y) =
      1 / τ * (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
    simp only [toPoly_smul, toPoly_mul, toPoly_monomial, map_mul, map_neg, aeval_C, map_one,
      map_pow, aeval_X, eq_ratCast, hA, hD]
    rw [hY, hτ]
    push_cast
    field_simp
    ring
  rw [hint]
  exact hasElementaryIntegral_rescale_iff ⟨d0⟩ (1 / τ) _ (one_div_ne_zero hτ0)

/-- **The even-degree decision over `ℚ`**: for `q ∈ ℚ[x]` squarefree of degree `2g + 2` with a
rational root `e`, and `D ≠ 0`, `hypDecideEven` answers for all large bounds, correctly. -/
theorem hypDecideEven_decides [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly ℚ) {g : ℕ} (hdeg : (toPoly q).natDegree = 2 * g + 2) (hsq : Squarefree (toPoly q))
    (e : ℚ) (he : (toPoly q).eval e = 0) (hy : y ^ 2 = aeval x (toPoly q))
    (hgen : ∀ z : E, InHyp Kc x y z) (A D : CPoly ℚ) (hD : toPoly D ≠ 0) :
    ∃ B0, ∀ B, B0 ≤ B → ∃ ans, hypDecideEven q e A D B = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨B0, hB0⟩ := hypDecideEven_eventually q hdeg hsq e he A D hD
  refine ⟨B0, fun B hB ↦ ?_⟩
  obtain ⟨ans, h⟩ := Option.ne_none_iff_exists'.mp (hB0 B hB)
  exact ⟨ans, h, hypDecideEven_spec hC hCall x y hx q e hy hgen A D B ans h⟩

end Spec

end Jac
