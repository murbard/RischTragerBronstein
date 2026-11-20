import RischTragerBronstein.Jacobian.HypDecideNFCComplete
import RischTragerBronstein.Jacobian.HypDecideEven

/-!
# Even degree over a number field, with a root in the field

For `y² = q(x)`, `q ∈ K[x]` (`K = NF M`) of degree `2g + 2` with a root `e ∈ K`, the substitution
`t = 1/(x − e)`, `Y = y t^{g+1}` gives `Y² = P(t)` with `P ∈ K[t]` of degree `2g + 1`
(`evenDataK`, as `evenData` over `ℚ`). `hypDecideEvenK` runs `hypDecideNFC` on the transformed
integrand; `hypDecideEvenK_spec`: every answer is correct.
-/

open Polynomial CPoly EllAlgo EllQuad

namespace Jac

section Gen

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

lemma toPoly_reverseK (L : CPoly K) : toPoly L.reverse = reflect (L.length - 1) (toPoly L) := by
  rcases Nat.eq_zero_or_pos L.length with h0 | hpos
  · simp [List.length_eq_zero_iff.mp h0]
  ext i
  rw [coeff_toPoly, coeff_reflect, coeff_toPoly]
  by_cases hi : i < L.length
  · rw [revAt_le (N := L.length - 1) (i := i) (by omega),
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_reverse,
      List.getD_eq_getElem _ _ (by omega)]
  · rw [revAt_eq_self_of_lt (N := L.length - 1) (i := i) (by omega),
      List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma squarefree_reflectK {R : K[X]} (hsq : Squarefree R) : Squarefree (reflect R.natDegree R) := by
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

lemma squarefree_comp_add_CK {f : K[X]} (hsq : Squarefree f) (e : K) :
    Squarefree (f.comp (X + C e)) := by
  have hsep : IsCoprime f (derivative f) := (PerfectField.separable_iff_squarefree.mpr hsq)
  apply Polynomial.Separable.squarefree
  have h2 := hsep.map (Polynomial.compRingHom (X + C e))
  show IsCoprime _ _
  rw [derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul]
  simpa using h2

lemma natDegree_of_listK {f : CPoly K} {g : ℕ} (hlen : f.length = 2 * g + 2)
    (hlc : f.getD (2 * g + 1) 0 ≠ 0) : (toPoly f).natDegree = 2 * g + 1 := by
  have hcoef : ∀ n, (toPoly f).coeff n = f.getD n 0 := coeff_toPoly f
  refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hcoef]; exact hlc))
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [hcoef, List.getD_eq_default _ _ (by rw [hlen]; exact_mod_cast hn)]

/-- The transformed data `(P, Ã, D̃)` over `K`. -/
def evenDataK (q : CPoly K) (e : K) (A D : CPoly K) : Option (CPoly K × CPoly K × CPoly K) :=
  let s := trim (shiftPoly q e)
  let R := s.drop 1
  let g := (R.length - 2) / 2
  let sA := trim (shiftPoly A e)
  let sD := trim (shiftPoly D e)
  if s.getD 0 0 = 0 ∧ R.length = 2 * g + 2 ∧ sA ≠ [] ∧ sD ≠ [] then
    some (R.reverse, smul (-1) (mul sA.reverse (monomial (sD.length - 1 + g + 1) 1)),
      mul sD.reverse (monomial (sA.length - 1 + 2) 1))
  else none

section Eval

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [CharZero Kc] [CharZero E]

lemma evF_shift_trim (ι : K →+* Kc) (P : CPoly K) (e : K) (u : E) :
    evF ι u (trim (shiftPoly P e)) = evF ι (u + algebraMap Kc E (ι e)) P := by
  rw [evF, evF, toPoly_trim, toPoly_shiftPoly, Polynomial.map_comp, aeval_comp]
  simp

lemma evF_cons (ι : K →+* Kc) (c : K) (L : CPoly K) (u : E) :
    evF ι u (c :: L) = algebraMap Kc E (ι c) + u * evF ι u L := by
  simp [evF]

lemma evF_reverse (ι : K →+* Kc) (t : E) (ht : t ≠ 0) :
    ∀ L : CPoly K, L ≠ [] → evF ι t L.reverse = t ^ (L.length - 1) * evF ι (1 / t) L
  | [], h => absurd rfl h
  | [c], _ => by simp [evF]
  | c :: d :: L, _ => by
    have ih := evF_reverse ι t ht (d :: L) (List.cons_ne_nil _ _)
    rw [List.reverse_cons, evF, toPoly_append, Polynomial.map_add, map_add, ← evF, ih,
      evF_cons ι c (d :: L)]
    simp only [List.length_reverse, List.length_cons, toPoly_cons, toPoly_nil, mul_zero, add_zero,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, map_C, map_mul, map_pow, aeval_X,
      aeval_C, Polynomial.map_add]
    rw [show L.length + 1 + 1 - 1 = L.length + 1 by omega, show L.length + 1 - 1 = L.length by omega]
    field_simp
    ring

end Eval

end Gen

section NF

open NFC

variable (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]

/-- **Even degree over `K = NF M`, with a root `e ∈ K`.** -/
noncomputable def hypDecideEvenK (q : CPoly (NF M)) (e : NF M) (A D : CPoly (NF M)) (B : ℕ) :
    Option Bool :=
  if trim A = [] then some true
  else
    match evenDataK q e A D with
    | some (P, An, Dn) =>
      if P.length = 2 * ((P.length - 2) / 2) + 2 ∧ P.getD (2 * ((P.length - 2) / 2) + 1) 0 ≠ 0 ∧
          squarefreeCheck P = true then
        hypDecideNFC M P ((P.length - 2) / 2) An Dn B
      else none
    | none => none

section Spec

open Differential IntermediateField

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 3200000 in
/-- **Correctness of `hypDecideEvenK`.** -/
theorem hypDecideEvenK_spec (hMZ : ∀ q ∈ M, q.den = 1) (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly (NF M)) (e : NF M) (ι : NF M →+* Kc) (hy : y ^ 2 = evF ι x q)
    (hgen : ∀ z : E, InHyp Kc x y z) (A D : CPoly (NF M)) (B : ℕ) (ans : Bool)
    (h : hypDecideEvenK M q e A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (evF ι x A / (evF ι x D * y)) := by
  unfold hypDecideEvenK at h
  split_ifs at h with hA0
  · cases h
    have : toPoly A = 0 := (trim_eq_nil_iff A).mp hA0
    simp only [evF, this, Polynomial.map_zero, map_zero, zero_div, true_iff]
    simpa using hasElementaryIntegral_of_deriv (0 : E)
  split at h
  swap
  · cases h
  rename_i P An Dn hQD
  split_ifs at h with hchk
  obtain ⟨hPlen, hPlc, hPsq⟩ := hchk
  unfold evenDataK at hQD
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
  have hgP : (R.reverse.length - 2) / 2 = g := by rw [List.length_reverse]
  rw [hgP] at h hPlen hPlc
  set ce : E := algebraMap Kc E (ι e) with hce
  -- `x` is not a constant
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hxe : x - ce ≠ 0 := x_sub_const_ne hC x hx (ι e)
  set t : E := 1 / (x - ce) with ht
  have ht0 : t ≠ 0 := one_div_ne_zero hxe
  have hxt : x = 1 / t + ce := by rw [ht]; field_simp; ring
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
  have hYP : Y ^ 2 = aeval t ((toPoly R.reverse).map ι) := by
    have h1 : evF ι x q = evF ι (1 / t) s := by rw [evF_shift_trim, ← hxt]
    have h2 : evF ι (1 / t) s = 1 / t * evF ι (1 / t) R := by
      conv_lhs => rw [hsplit]
      rw [evF_cons, map_zero, map_zero, zero_add]
    have h3 := evF_reverse ι t ht0 R (by intro h0; rw [h0] at hRlen; simp at hRlen)
    rw [hRlen, show 2 * g + 2 - 1 = 2 * g + 1 by omega] at h3
    change Y ^ 2 = evF ι t R.reverse
    rw [hY, mul_pow, hy, h1, h2, h3]
    field_simp
    ring
  -- the rescaled derivation
  have ht' : t′ = -t ^ 2 := by
    rw [ht, Derivation.leibniz_div, map_sub, hx, hce, hconstE]
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
  have hcemem : ∀ w : E, ce ∈ Kc⟮w⟯ := fun w ↦ IntermediateField.algebraMap_mem _ _
  have hgen' : ∀ z : E, InHyp Kc t Y z := by
    have hxX : Kc⟮x⟯ = Kc⟮t⟯ := by
      apply le_antisymm
      · rw [adjoin_simple_le_iff, hxt]
        exact add_mem (div_mem (one_mem _) (mem_adjoin_simple_self _ _)) (hcemem _)
      · rw [adjoin_simple_le_iff, ht]
        exact div_mem (one_mem _) (sub_mem (mem_adjoin_simple_self _ _) (hcemem _))
    intro z
    obtain ⟨α, β, hα, hβ, rfl⟩ := hgen z
    refine ⟨α, β / t ^ (g + 1), hxX ▸ hα,
      div_mem (hxX ▸ hβ) (pow_mem (mem_adjoin_simple_self _ _) _), ?_⟩
    rw [hY]; field_simp
  have hdegP : (toPoly R.reverse).natDegree = 2 * g + 1 := natDegree_of_listK hPlen hPlc
  have hspec := @hypDecideNFC_spec M _ Kc E _ _ _ _ D' hDA' _ _ hMZ hC hCall' t Y hT' _ g
    (squarefreeCheck_sound hPsq) hdegP ι hYP hgen' _ _ B ans h
  rw [hspec]
  -- transfer back
  have hA := evF_reverse ι t ht0 sA hAne
  have hD := evF_reverse ι t ht0 sD hDne
  rw [evF_shift_trim, ← hxt] at hA hD
  have hint : evF ι t (smul (-1) (mul sA.reverse (monomial (sD.length - 1 + g + 1) 1))) /
      (evF ι t (mul sD.reverse (monomial (sA.length - 1 + 2) 1)) * Y) =
      1 / τ * (evF ι x A / (evF ι x D * y)) := by
    have hsm : ∀ (c : NF M) (L : CPoly (NF M)), evF ι t (smul c L) =
        algebraMap Kc E (ι c) * evF ι t L := fun c L ↦ by simp [evF, toPoly_smul]
    have hml : ∀ L L' : CPoly (NF M), evF ι t (mul L L') = evF ι t L * evF ι t L' :=
      fun L L' ↦ by simp [evF, toPoly_mul]
    have hmo : ∀ k : ℕ, evF ι t (monomial k (1 : NF M)) = t ^ k := fun k ↦ by
      simp [evF, toPoly_monomial]
    rw [hsm, hml, hml, hmo, hmo, hA, hD, hY, hτ]
    simp only [map_neg, map_one]
    field_simp
    ring
  rw [hint]
  exact hasElementaryIntegral_rescale_iff ⟨d0⟩ (1 / τ) _ (one_div_ne_zero hτ0)

end Spec

end NF

end Jac
