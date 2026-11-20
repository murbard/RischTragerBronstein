import RischTragerBronstein.Algebraic.HypGlue
import RischTragerBronstein.Algebraic.HypRed
import RischTragerBronstein.Elementary.Sum
import RischTragerBronstein.Liouville.Transcendence

/-!
# Hyperelliptic integrals `∫ B(x) / √p(x) dx`: the decision theorem

Let `E = Kc(x)(y)` be a differential field with constants `Kc`, `x′ = 1`, `y² = p(x)` with
`p ∈ ℚ[x]` squarefree of odd degree (a hyperelliptic curve of genus `(deg p - 1)/2`, or a conic when
`deg p = 1`). For every `B ∈ ℚ[x]` (`hyp_decides`):

  `∫ B(x) / y dx` is elementary  ↔  the remainder `B₀` of `hypRed p B` is zero,

and then `∫ B / y dx = C(x) y` with `C = (hypRed p B).1` (`hyp_antiderivative`). The reduction
`B = C′ p + C p′/2 + B₀` (`deg B₀ ≤ deg p - 2`) is exact integration of `(C y)′`; the remainder
`B₀ dx / y` is a differential with no residues, and `hyp_glue` shows that a non-zero one has no
elementary integral (no logarithmic part can occur, and `v` would have to be a polynomial in
`x, y`). Examples: `∫ dx / √(x³ + 1)`, `∫ x dx / √(x³ + 1)` are not elementary.
-/

open Polynomial IntermediateField

namespace Differential

section Rat

variable {L : Type*} [Field L] [CharZero L] [Differential L]

lemma deriv_ratCast_L (q : ℚ) : ((q : L))′ = 0 := by
  have hd : ((q.den : ℤ) : L) ≠ 0 := by exact_mod_cast q.den_nz
  have e : (q : L) * ((q.den : ℤ) : L) = ((q.num : ℤ) : L) := by
    rw [← Rat.cast_intCast, ← Rat.cast_intCast, ← Rat.cast_mul]
    congr 1
    exact_mod_cast Rat.mul_den_eq_num q
  have := congrArg (fun z : L ↦ z′) e
  simp only [Derivation.leibniz, Derivation.map_intCast, smul_eq_mul, mul_zero, zero_add] at this
  exact (mul_eq_zero.mp this).resolve_left hd

/-- `(P(x))′ = P′(x)` for `P ∈ ℚ[X]` when `x′ = 1`. -/
lemma deriv_aeval_rat (x : L) (hx : x′ = 1) (P : ℚ[X]) :
    (aeval x P)′ = aeval x (derivative P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, derivative_add, map_add, hP, hQ]
  | monomial n a =>
    simp only [aeval_monomial, derivative_monomial, eq_ratCast, Derivation.leibniz, smul_eq_mul,
      deriv_ratCast_L, mul_zero, add_zero]
    rcases n with _ | n
    · simp
    · rw [Derivation.leibniz_pow, hx]
      simp only [smul_eq_mul, nsmul_eq_mul, mul_one, Nat.add_sub_cancel]
      push_cast
      ring

/-- **The exact part**: `(C(x) y)′ = (C′ p + C p′ / 2)(x) / y` when `y² = p(x)`. -/
lemma deriv_C_mul_y (x y : L) (hx : x′ = 1) (p C0 : ℚ[X]) (hy : y ^ 2 = aeval x p) (hy0 : y ≠ 0) :
    (aeval x C0 * y)′ =
      aeval x (derivative C0 * p + Polynomial.C (1 / 2 : ℚ) * (C0 * derivative p)) / y := by
  have hyd : 2 * y * y′ = aeval x (derivative p) := by
    have := congrArg (fun z : L ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul] at this
    rw [deriv_aeval_rat x hx] at this
    linear_combination this
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, deriv_aeval_rat x hx]
  simp only [map_add, map_mul, aeval_C, eq_ratCast]
  rw [eq_div_iff hy0]
  have : y′ = aeval x (derivative p) / (2 * y) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hy0)]; linear_combination hyd
  rw [this, ← hy]
  push_cast
  field_simp
  ring

end Rat

section Decide

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The antiderivative**: `∫ B / y dx = C y + ∫ B₀ / y dx` with `(C, B₀) = hypRed p B`. -/
theorem hyp_antiderivative (x y : E) (hx : x′ = 1) (p B : CPoly ℚ)
    (hp1 : 1 ≤ (CPoly.toPoly p).natDegree) (hy : y ^ 2 = aeval x (CPoly.toPoly p)) (hy0 : y ≠ 0) :
    aeval x (CPoly.toPoly B) / y = (aeval x (CPoly.toPoly (CPoly.hypRed p B).1) * y)′ +
      aeval x (CPoly.toPoly (CPoly.hypRed p B).2) / y := by
  rw [deriv_C_mul_y x y hx _ _ hy hy0, (CPoly.hypRed_spec p B hp1).1]
  simp only [map_add]
  ring

/-- **The non-elementary direction**: if `g′ + B₀(x) / y` (`g ∈ E`, `deg B₀ ≤ deg p - 2`) has an
elementary integral, then `B₀ = 0`. -/
theorem hyp_no_elem (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (p : CPoly ℚ) (hp : Squarefree (CPoly.toPoly p)) (hodd : Odd (CPoly.toPoly p).natDegree)
    (hy : y ^ 2 = aeval x (CPoly.toPoly p)) (hgen : ∀ z : E, InHyp Kc x y z) (g : E) (B0 : ℚ[X])
    (hB0deg : B0 = 0 ∨ B0.natDegree + 2 ≤ (CPoly.toPoly p).natDegree)
    (h : HasElementaryIntegral (g′ + aeval x B0 / y)) : B0 = 0 := by
  obtain ⟨L, _, _, _, _, hE, g0, hg⟩ := h
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
  obtain ⟨ι, s, c, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g0 hg
  let Cc := constants L
  let _ : Differential Cc := ⟨0⟩
  have hDAc : DifferentialAlgebra Cc L := ⟨fun c ↦ c.2⟩
  have hcharC : CharZero Cc := ⟨fun a b h ↦ by
    have := congrArg (fun z : Cc ↦ (z : L)) h
    simpa using this⟩
  set j := algebraMap E L with hjdef
  have hj : ∀ z : E, (j z)′ = j z′ := fun z ↦ deriv_algebraMap z
  have hCc : ∀ c : Cc, c′ = 0 := fun _ ↦ rfl
  have hxL : (j x)′ = 1 := by rw [hj, hx, map_one]
  have htr : Transcendental Cc (j x) :=
    transcendental_of_deriv_ne_zero hCc (by rw [hxL]; exact one_ne_zero)
  have hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap Cc L) := fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩
  set pC := (CPoly.toPoly p).map (algebraMap ℚ Cc) with hpC
  have haev : ∀ P : ℚ[X], aeval (j x) (P.map (algebraMap ℚ Cc)) = j (aeval x P) := by
    intro P
    rw [aeval_map_algebraMap, aeval_def, aeval_def, hom_eval₂]
    congr 1
    exact RingHom.ext_rat _ _
  have hyL : j y ^ 2 = aeval (j x) pC := by rw [hpC, haev, ← hy, map_pow]
  have hpsq : Squarefree pC := by
    have hsep : (CPoly.toPoly p).Separable := (PerfectField.separable_iff_squarefree).mpr hp
    exact (hsep.map).squarefree
  have hdeg : pC.natDegree = (CPoly.toPoly p).natDegree :=
    natDegree_map_eq_of_injective (algebraMap ℚ Cc).injective _
  have hoddC : Odd pC.natDegree := hdeg ▸ hodd
  -- `C(x)` over the constants of `L` contains the image of `Kc(x)`
  have hKx : ∀ z : E, z ∈ Kc⟮x⟯ → j z ∈ Cc⟮j x⟯ := by
    let T : IntermediateField Kc E :=
      { carrier := {w | j w ∈ Cc⟮j x⟯}
        mul_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢; exact mul_mem ha hb
        one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact one_mem _
        add_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢; exact add_mem ha hb
        zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact zero_mem _
        algebraMap_mem' := fun c ↦ by
          simp only [Set.mem_setOf_eq]
          have hd : (j (algebraMap Kc E c))′ = 0 := by
            rw [hj, deriv_algebraMap, hC, map_zero, map_zero]
          obtain ⟨c', hc'⟩ := hconst _ hd
          rw [← hc']
          exact IntermediateField.algebraMap_mem _ _
        inv_mem' := fun a ha ↦ by
          simp only [Set.mem_setOf_eq, map_inv₀] at ha ⊢; exact inv_mem ha }
    have hle : Kc⟮x⟯ ≤ T := by
      rw [adjoin_simple_le_iff]
      exact mem_adjoin_simple_self Cc (j x)
    exact fun z hz ↦ hle hz
  -- the field `C(x)(y)` in `L` contains `constField E L`
  set S := hypField (j x) (j y) htr pC hoddC hyL with hS
  have hEs : ∀ e : E, j e ∈ S := by
    intro e
    obtain ⟨α, β, hα, hβ, rfl⟩ := hgen e
    exact ⟨j α, j β, hKx α hα, hKx β hβ, by rw [map_add, map_mul]⟩
  have hcf : ∀ z ∈ constField E L, InHyp Cc (j x) (j y) z := by
    let N : IntermediateField E L :=
      { S with algebraMap_mem' := hEs }
    have : constField E L ≤ N := adjoin_le_iff.mpr fun z hz ↦ by
      obtain ⟨c', rfl⟩ := hconst z hz
      exact ⟨algebraMap Cc L c', 0, IntermediateField.algebraMap_mem _ _, zero_mem _, by ring⟩
    exact fun z hz ↦ this hz
  -- the identity for `B₀`
  have hB0 : aeval (j x) (B0.map (algebraMap ℚ Cc)) / j y =
      (v - j g)′ + ∑ i ∈ s, c i * logDeriv (u i) := by
    have hg' := heq
    rw [map_add, ← hj, map_div₀] at hg'
    rw [haev, map_sub]
    linear_combination hg'
  have hmain := hyp_glue (j x) (j y) hCc hxL htr hconst pC hpsq hoddC hyL
    (B0.map (algebraMap ℚ Cc)) (by
      rcases hB0deg with h | h
      · left; rw [h, Polynomial.map_zero]
      · right; rw [natDegree_map_eq_of_injective (algebraMap ℚ Cc).injective, hdeg]; exact h)
    s c u (v - j g)
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hcf _ (hdata i hi).2.1⟩)
    (by
      obtain ⟨α, β, hα, hβ, hvα⟩ := hcf v hv
      obtain ⟨α', β', hα', hβ', hg1⟩ := hEs g
      refine ⟨α - α', β - β', sub_mem hα hα', sub_mem hβ hβ', ?_⟩
      rw [hvα, hg1]; ring)
    hB0
  exact (Polynomial.map_eq_zero_iff (algebraMap ℚ Cc).injective).mp hmain

/-- `hyp_no_elem` with a remainder `B₀` whose coefficients are arbitrary constants. -/
theorem hyp_no_elemK (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (p : CPoly ℚ) (hp : Squarefree (CPoly.toPoly p)) (hodd : Odd (CPoly.toPoly p).natDegree)
    (hy : y ^ 2 = aeval x (CPoly.toPoly p)) (hgen : ∀ z : E, InHyp Kc x y z) (g : E) (B0 : Kc[X])
    (hB0deg : B0 = 0 ∨ B0.natDegree + 2 ≤ (CPoly.toPoly p).natDegree)
    (h : HasElementaryIntegral (g′ + aeval x B0 / y)) : B0 = 0 := by
  obtain ⟨L, _, _, _, _, hE, g0, hg⟩ := h
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
  obtain ⟨ι, s, c, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g0 hg
  let Cc := constants L
  let _ : Differential Cc := ⟨0⟩
  have hDAc : DifferentialAlgebra Cc L := ⟨fun c ↦ c.2⟩
  have hcharC : CharZero Cc := ⟨fun a b h ↦ by
    have := congrArg (fun z : Cc ↦ (z : L)) h
    simpa using this⟩
  set j := algebraMap E L with hjdef
  have hj : ∀ z : E, (j z)′ = j z′ := fun z ↦ deriv_algebraMap z
  have hCc : ∀ c : Cc, c′ = 0 := fun _ ↦ rfl
  have hxL : (j x)′ = 1 := by rw [hj, hx, map_one]
  have htr : Transcendental Cc (j x) :=
    transcendental_of_deriv_ne_zero hCc (by rw [hxL]; exact one_ne_zero)
  have hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap Cc L) := fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩
  let κ : Kc →+* Cc := (j.comp (algebraMap Kc E)).codRestrict (constants L) fun c ↦ by
    rw [mem_constants, RingHom.comp_apply, hj, deriv_algebraMap, hC, map_zero, map_zero]
  have haevK : ∀ P : Kc[X], aeval (j x) (P.map κ) = j (aeval x P) := by
    intro P
    rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
    rfl
  set pC := (CPoly.toPoly p).map (algebraMap ℚ Cc) with hpC
  have haev : ∀ P : ℚ[X], aeval (j x) (P.map (algebraMap ℚ Cc)) = j (aeval x P) := by
    intro P
    rw [aeval_map_algebraMap, aeval_def, aeval_def, hom_eval₂]
    congr 1
    exact RingHom.ext_rat _ _
  have hyL : j y ^ 2 = aeval (j x) pC := by rw [hpC, haev, ← hy, map_pow]
  have hpsq : Squarefree pC := by
    have hsep : (CPoly.toPoly p).Separable := (PerfectField.separable_iff_squarefree).mpr hp
    exact (hsep.map).squarefree
  have hdeg : pC.natDegree = (CPoly.toPoly p).natDegree :=
    natDegree_map_eq_of_injective (algebraMap ℚ Cc).injective _
  have hoddC : Odd pC.natDegree := hdeg ▸ hodd
  -- `C(x)` over the constants of `L` contains the image of `Kc(x)`
  have hKx : ∀ z : E, z ∈ Kc⟮x⟯ → j z ∈ Cc⟮j x⟯ := by
    let T : IntermediateField Kc E :=
      { carrier := {w | j w ∈ Cc⟮j x⟯}
        mul_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢; exact mul_mem ha hb
        one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact one_mem _
        add_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢; exact add_mem ha hb
        zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact zero_mem _
        algebraMap_mem' := fun c ↦ by
          simp only [Set.mem_setOf_eq]
          have hd : (j (algebraMap Kc E c))′ = 0 := by
            rw [hj, deriv_algebraMap, hC, map_zero, map_zero]
          obtain ⟨c', hc'⟩ := hconst _ hd
          rw [← hc']
          exact IntermediateField.algebraMap_mem _ _
        inv_mem' := fun a ha ↦ by
          simp only [Set.mem_setOf_eq, map_inv₀] at ha ⊢; exact inv_mem ha }
    have hle : Kc⟮x⟯ ≤ T := by
      rw [adjoin_simple_le_iff]
      exact mem_adjoin_simple_self Cc (j x)
    exact fun z hz ↦ hle hz
  -- the field `C(x)(y)` in `L` contains `constField E L`
  set S := hypField (j x) (j y) htr pC hoddC hyL with hS
  have hEs : ∀ e : E, j e ∈ S := by
    intro e
    obtain ⟨α, β, hα, hβ, rfl⟩ := hgen e
    exact ⟨j α, j β, hKx α hα, hKx β hβ, by rw [map_add, map_mul]⟩
  have hcf : ∀ z ∈ constField E L, InHyp Cc (j x) (j y) z := by
    let N : IntermediateField E L :=
      { S with algebraMap_mem' := hEs }
    have : constField E L ≤ N := adjoin_le_iff.mpr fun z hz ↦ by
      obtain ⟨c', rfl⟩ := hconst z hz
      exact ⟨algebraMap Cc L c', 0, IntermediateField.algebraMap_mem _ _, zero_mem _, by ring⟩
    exact fun z hz ↦ this hz
  -- the identity for `B₀`
  have hB0 : aeval (j x) (B0.map κ) / j y =
      (v - j g)′ + ∑ i ∈ s, c i * logDeriv (u i) := by
    have hg' := heq
    rw [map_add, ← hj, map_div₀] at hg'
    rw [haevK, map_sub]
    linear_combination hg'
  have hmain := hyp_glue (j x) (j y) hCc hxL htr hconst pC hpsq hoddC hyL
    (B0.map κ) (by
      rcases hB0deg with h | h
      · left; rw [h, Polynomial.map_zero]
      · right; rw [natDegree_map_eq_of_injective κ.injective, hdeg]; exact h)
    s c u (v - j g)
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hcf _ (hdata i hi).2.1⟩)
    (by
      obtain ⟨α, β, hα, hβ, hvα⟩ := hcf v hv
      obtain ⟨α', β', hα', hβ', hg1⟩ := hEs g
      refine ⟨α - α', β - β', sub_mem hα hα', sub_mem hβ hβ', ?_⟩
      rw [hvα, hg1]; ring)
    hB0
  exact (Polynomial.map_eq_zero_iff κ.injective).mp hmain

/-- **Hyperelliptic integrals `∫ B(x) dx / √p(x)` are decided** (`p` squarefree of odd degree):
elementary if and only if the remainder of the reduction vanishes. -/
theorem hyp_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (p : CPoly ℚ) (hp : Squarefree (CPoly.toPoly p)) (hodd : Odd (CPoly.toPoly p).natDegree)
    (hy : y ^ 2 = aeval x (CPoly.toPoly p)) (hgen : ∀ z : E, InHyp Kc x y z) (B : CPoly ℚ) :
    HasElementaryIntegral (aeval x (CPoly.toPoly B) / y) ↔
      CPoly.isZero (CPoly.hypRed p B).2 = true := by
  have hp0 : CPoly.toPoly p ≠ 0 := hp.ne_zero
  have hp1 : 1 ≤ (CPoly.toPoly p).natDegree := by obtain ⟨k, hk⟩ := hodd; omega
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hpx : aeval x (CPoly.toPoly p) ≠ 0 := by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hp0)
  have hy0 : y ≠ 0 := by rintro rfl; apply hpx; rw [← hy]; ring
  rw [hyp_antiderivative x y hx p B hp1 hy hy0, CPoly.isZero_iff]
  set C0 := (CPoly.hypRed p B).1
  set B0 := (CPoly.hypRed p B).2
  have hB0deg := (CPoly.hypRed_spec p B hp1).2
  constructor
  · intro h
    exact hyp_no_elem hC hCall x y hx p hp hodd hy hgen _ _ hB0deg h
  · intro h0
    rw [h0, map_zero, zero_div, add_zero]
    exact hasElementaryIntegral_of_deriv _

end Decide

end Differential
