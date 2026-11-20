import RischTragerBronstein.Elementary.Rescale
import RischTragerBronstein.Rational.IntegrableIn
import RischTragerBronstein.Algebraic.HypGlue
import RischTragerBronstein.Elementary.SqrtExt
import RischTragerBronstein.Differential.Constants

/-!
# Genus zero: `∫ R(x, √(ax² + bx + c)) dx` is always elementary

In a differential field `E = Kc(x, y)` with constants `Kc`, `x′ = 1`, `y² = ax² + bx + c`
(`a, b, c ∈ Kc`, `b² − 4ac ≠ 0`) and `√a ∈ Kc`, **every** element has an elementary integral
(`genus0_elementary`). Euler's substitution `t = y − √a x` gives `E = Kc(t)`
(`x = (c − t²)/(2√a t − b)`); rescaling the derivation by `1/t′` (`hasElementaryIntegral_rescale_iff`)
makes `t` a variable with derivative `1`, and rational functions of `t` are elementary-integrable
(`hasElementaryIntegral_rational_in`). E.g. `∫ dx / √(x² + 1) = log(x + √(x² + 1))`.
-/

open Polynomial IntermediateField

namespace Differential

section Genus0

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Every element of a genus-zero function field has an elementary integral.** -/
theorem genus0_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c s : Kc) (hs : s ^ 2 = a) (hdisc : b ^ 2 - 4 * a * c ≠ 0)
    (hy : y ^ 2 = algebraMap Kc E a * x ^ 2 + algebraMap Kc E b * x + algebraMap Kc E c)
    (hgen : ∀ z : E, InHyp Kc x y z) (f : E) : HasElementaryIntegral f := by
  set A := algebraMap Kc E a
  set B := algebraMap Kc E b
  set Cc := algebraMap Kc E c
  set S := algebraMap Kc E s
  have hconst : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hSA : S ^ 2 = A := by rw [← map_pow, hs]
  -- `x` is not a constant
  have hxnc : ∀ r : Kc, x ≠ algebraMap Kc E r := by
    intro r h; have := congrArg (fun z : E ↦ z′) h; simp [hx, hconst] at this
  set t := y - S * x with ht
  -- `x (2 S t − B) = C − t²`
  have hrel : x * (2 * S * t - B) = Cc - t ^ 2 := by
    rw [ht]; linear_combination hy - x ^ 2 * hSA
  have hden : 2 * S * t - B ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hrel
    -- then `t` is constant: `t² = C`, and `2 S t = B`, so `b² = 4ac`
    have ht2 : t ^ 2 - Cc = 0 := by linear_combination hrel
    have h4 : B ^ 2 - 4 * A * Cc = 0 := by
      linear_combination (-(B + 2 * S * t)) * h0 + 4 * t ^ 2 * hSA + 4 * A * ht2
    apply hdisc
    apply (algebraMap Kc E).injective
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero]
    exact h4
  have hxt : x = (Cc - t ^ 2) / (2 * S * t - B) := by rw [← hrel]; field_simp
  -- `E = Kc(t)`
  have hxmem : x ∈ Kc⟮t⟯ := by
    rw [hxt]
    refine div_mem (sub_mem (IntermediateField.algebraMap_mem _ _) (pow_mem (mem_adjoin_simple_self _ _) _))
      (sub_mem (mul_mem (mul_mem (by simpa using IntermediateField.algebraMap_mem Kc⟮t⟯ (2 : Kc))
        (IntermediateField.algebraMap_mem _ _)) (mem_adjoin_simple_self _ _)) (IntermediateField.algebraMap_mem _ _))
  have hymem : y ∈ Kc⟮t⟯ := by
    have : y = t + S * x := by rw [ht]; ring
    rw [this]
    exact add_mem (mem_adjoin_simple_self _ _) (mul_mem (IntermediateField.algebraMap_mem _ _) hxmem)
  have hle : Kc⟮x⟯ ≤ Kc⟮t⟯ := adjoin_simple_le_iff.mpr hxmem
  have hfmem : ∀ z : E, z ∈ Kc⟮t⟯ := by
    intro z
    obtain ⟨α, β, hα, hβ, rfl⟩ := hgen z
    exact add_mem (hle hα) (mul_mem (hle hβ) hymem)
  -- `t′ ≠ 0`
  have ht' : t′ ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := hCall t h0
    apply hxnc (((c - r ^ 2) / (2 * s * r - b)))
    rw [hxt, ← hr]
    simp only [map_div₀, map_sub, map_pow, map_mul, map_ofNat, A, B, Cc, S]
  -- rescale by `1/t′`
  have hfτ : 1 / t′ * f ∈ Kc⟮t⟯ := hfmem _
  set τ := t′ with hτ
  let d0 : Derivation ℤ E E := Differential.deriv
  have hd0 : ∀ z : E, d0 z = z′ := fun _ ↦ rfl
  have hc0 : ∀ r : Kc, d0 (algebraMap Kc E r) = 0 := fun r ↦ hconst r
  let D' : Differential E := rescale ⟨d0⟩ (1 / τ)
  have hD't : D'.deriv t = 1 := by
    show 1 / τ * d0 t = 1
    rw [hd0, ← hτ]; exact one_div_mul_cancel ht'
  have hDA' : @DifferentialAlgebra Kc E _ _ _ _ D' :=
    @DifferentialAlgebra.mk Kc E _ _ _ _ D' (fun r ↦ by
      show 1 / τ * d0 (algebraMap Kc E r) = algebraMap Kc E r′
      rw [hc0, hC, map_zero, mul_zero])
  have key : @HasElementaryIntegral E _ D' (1 / τ * f) := by
    obtain ⟨P, Q, hPQ⟩ := (mem_adjoin_simple_iff (F := Kc) (α := t) _).mp hfτ
    by_cases hQ : Q = 0
    · rw [hPQ, hQ, map_zero, div_zero]
      have := @hasElementaryIntegral_of_deriv E _ D' 0
      rwa [show D'.deriv 0 = 0 from map_zero _] at this
    · have := @hasElementaryIntegral_rational_in Kc E _ _ _ _ D' _ hDA' hC t hD't P Q hQ 0
      rw [show D'.deriv 0 = 0 from map_zero _, zero_add] at this
      rw [hPQ]
      exact this
  exact (hasElementaryIntegral_rescale_iff ⟨d0⟩ (1 / τ) f (one_div_ne_zero ht')).mp key

/-- **`∫ dx / √(x² + 1)` is elementary** (`= log (x + √(x² + 1))`). -/
theorem asinh_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 2 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral (1 / y) :=
  genus0_elementary hC hCall x y hx 1 0 1 1 (by ring) (by norm_num) (by simp [hy]) hgen _

end Genus0

section Rational

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Rational function fields**: if a non-constant `t` generates `E` over the constants `Kc`,
every element of `E` has an elementary integral (rescale by `1/t′`, then integrate rational
functions of `t`). -/
theorem hasElementaryIntegral_of_generated (hC : ∀ c : Kc, c′ = 0) (t : E) (ht' : t′ ≠ 0)
    (hgen : ∀ z : E, z ∈ Kc⟮t⟯) (f : E) : HasElementaryIntegral f := by
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hfτ : 1 / t′ * f ∈ Kc⟮t⟯ := hgen _
  set τ := t′ with hτ
  let d0 : Derivation ℤ E E := Differential.deriv
  have hd0 : ∀ z : E, d0 z = z′ := fun _ ↦ rfl
  have hc0 : ∀ r : Kc, d0 (algebraMap Kc E r) = 0 := fun r ↦ hconstE r
  let D' : Differential E := rescale ⟨d0⟩ (1 / τ)
  have hD't : D'.deriv t = 1 := by
    show 1 / τ * d0 t = 1
    rw [hd0, ← hτ]; exact one_div_mul_cancel ht'
  have hDA' : @DifferentialAlgebra Kc E _ _ _ _ D' :=
    @DifferentialAlgebra.mk Kc E _ _ _ _ D' (fun r ↦ by
      show 1 / τ * d0 (algebraMap Kc E r) = algebraMap Kc E r′
      rw [hc0, hC, map_zero, mul_zero])
  have key : @HasElementaryIntegral E _ D' (1 / τ * f) := by
    obtain ⟨P, Q, hPQ⟩ := (mem_adjoin_simple_iff (F := Kc) (α := t) _).mp hfτ
    by_cases hQ : Q = 0
    · rw [hPQ, hQ, map_zero, div_zero]
      have := @hasElementaryIntegral_of_deriv E _ D' 0
      rwa [show D'.deriv 0 = 0 from map_zero _] at this
    · have := @hasElementaryIntegral_rational_in Kc E _ _ _ _ D' _ hDA' hC t hD't P Q hQ 0
      rw [show D'.deriv 0 = 0 from map_zero _, zero_add] at this
      rw [hPQ]
      exact this
  exact (hasElementaryIntegral_rescale_iff ⟨d0⟩ (1 / τ) f (one_div_ne_zero ht')).mp key

/-- **Genus zero with a rational root**: `y² = a (x − e)(x − e')` (`e ≠ e'` in `Kc`, `a ≠ 0`):
every element of `Kc(x, y)` has an elementary integral (`t = y/(x − e)`). -/
theorem genus0_elementary_root (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a e e' : Kc) (ha : a ≠ 0) (hee : e ≠ e')
    (hy : y ^ 2 = algebraMap Kc E a * (x - algebraMap Kc E e) * (x - algebraMap Kc E e'))
    (hgen : ∀ z : E, InHyp Kc x y z) (f : E) : HasElementaryIntegral f := by
  set A := algebraMap Kc E a
  set Ee := algebraMap Kc E e
  set Ee' := algebraMap Kc E e'
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hxnc : ∀ r : Kc, x ≠ algebraMap Kc E r := by
    intro r h; have := congrArg (fun z : E ↦ z′) h; simp [hx, hconstE] at this
  have hxe : x - Ee ≠ 0 := sub_ne_zero.mpr (hxnc e)
  have hA0 : A ≠ 0 := (_root_.map_ne_zero _).mpr ha
  set t := y / (x - Ee) with ht
  -- `t² = A (x − e')/(x − e)`, so `x (t² − A) = t² e − A e'`
  have ht2 : t ^ 2 * (x - Ee) = A * (x - Ee') := by
    rw [ht, div_pow, hy]; field_simp
  have hden : t ^ 2 - A ≠ 0 := by
    intro h0
    have : A * (x - Ee) = A * (x - Ee') := by
      rw [← ht2, show t ^ 2 = A by linear_combination h0]
    have := mul_left_cancel₀ hA0 this
    exact hee ((algebraMap Kc E).injective (by linear_combination -this))
  have hxt : x = (t ^ 2 * Ee - A * Ee') / (t ^ 2 - A) := by
    rw [eq_div_iff hden]; linear_combination ht2
  have hQmem : ∀ r : Kc, algebraMap Kc E r ∈ Kc⟮t⟯ := fun r ↦ IntermediateField.algebraMap_mem _ _
  have hxmem : x ∈ Kc⟮t⟯ := by
    rw [hxt]
    exact div_mem (sub_mem (mul_mem (pow_mem (mem_adjoin_simple_self _ _) _) (hQmem _))
      (mul_mem (hQmem _) (hQmem _))) (sub_mem (pow_mem (mem_adjoin_simple_self _ _) _) (hQmem _))
  have hymem : y ∈ Kc⟮t⟯ := by
    have : y = t * (x - Ee) := by rw [ht]; field_simp
    rw [this]
    exact mul_mem (mem_adjoin_simple_self _ _) (sub_mem hxmem (hQmem _))
  have hle : Kc⟮x⟯ ≤ Kc⟮t⟯ := adjoin_simple_le_iff.mpr hxmem
  have hfmem : ∀ z : E, z ∈ Kc⟮t⟯ := by
    intro z
    obtain ⟨α, β, hα, hβ, rfl⟩ := hgen z
    exact add_mem (hle hα) (mul_mem (hle hβ) hymem)
  have ht' : t′ ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := hCall t h0
    apply hxnc ((r ^ 2 * e - a * e') / (r ^ 2 - a))
    rw [hxt, ← hr]
    simp only [map_div₀, map_sub, map_pow, map_mul, A, Ee, Ee']
  exact hasElementaryIntegral_of_generated hC t ht' hfmem f

/-- **`∫ dx / √(1 − x²)` is elementary** (arcsine; via `t = y/(x − 1)`, no `√−1` needed in `Kc`). -/
theorem arcsin_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = 1 - x ^ 2) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral (1 / y) :=
  genus0_elementary_root hC hCall x y hx (-1) 1 (-1) (by norm_num) (by norm_num)
    (by rw [hy]; simp; ring) hgen _

/-- **Genus zero, in general**: in `Kc(x, y)`, `y² = ax² + bx + c` (`a ≠ 0`, `b² ≠ 4ac`), every
element has an elementary integral — no condition on `a` (`√a` is adjoined, an elementary
extension, and `t = y − √a x` generates over the constants of `E(√a)`). -/
theorem genus0_elementary_gen (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (a b c : Kc) (ha : a ≠ 0) (hdisc : b ^ 2 - 4 * a * c ≠ 0)
    (hy : y ^ 2 = algebraMap Kc E a * x ^ 2 + algebraMap Kc E b * x + algebraMap Kc E c)
    (hgen : ∀ z : E, InHyp Kc x y z) (f : E) : HasElementaryIntegral f := by
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  obtain ⟨E', _, _, _, _, hEE', s, hs2, hs', hrep⟩ := exists_sqrt_ext (algebraMap Kc E a)
    (hconstE a) ((_root_.map_ne_zero _).mpr ha)
  have : CharZero E' := charZero_of_injective_algebraMap (algebraMap E E').injective
  -- the constants of `E'`
  let R := constants E'
  let _ : Differential R := ⟨0⟩
  have hDAR : DifferentialAlgebra R E' := ⟨fun c ↦ c.2⟩
  have hcharR : CharZero R := ⟨fun a b h ↦ by
    have := congrArg (fun z : R ↦ (z : E')) h
    simpa using this⟩
  have hR : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  set j := algebraMap E E'
  have hjd : ∀ z : E, (j z)′ = j z′ := fun z ↦ deriv_algebraMap z
  have hK : ∀ r : Kc, (j (algebraMap Kc E r))′ = 0 := fun r ↦ by rw [hjd, hconstE, map_zero]
  have hKmem : ∀ r : Kc, j (algebraMap Kc E r) ∈ R⟮(0 : E')⟯ := fun r ↦ by
    have : j (algebraMap Kc E r) = algebraMap R E' ⟨_, hK r⟩ := rfl
    rw [this]; exact IntermediateField.algebraMap_mem _ _
  set A := j (algebraMap Kc E a)
  set B := j (algebraMap Kc E b)
  set Cc := j (algebraMap Kc E c)
  set X' := j x
  set Y' := j y
  have hSA : s ^ 2 = A := hs2
  have hY : Y' ^ 2 = A * X' ^ 2 + B * X' + Cc := by
    simp only [Y', X', A, B, Cc, ← map_pow, hy, map_add, map_mul]
  set t := Y' - s * X' with ht
  have hrel : X' * (2 * s * t - B) = Cc - t ^ 2 := by
    rw [ht]; linear_combination hY - X' ^ 2 * hSA
  have hden : 2 * s * t - B ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hrel
    have ht2 : t ^ 2 - Cc = 0 := by linear_combination hrel
    have h4 : B ^ 2 - 4 * A * Cc = 0 := by
      linear_combination (-(B + 2 * s * t)) * h0 + 4 * t ^ 2 * hSA + 4 * A * ht2
    apply hdisc
    apply (algebraMap Kc E).injective
    apply j.injective
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero]
    exact h4
  have hxt : X' = (Cc - t ^ 2) / (2 * s * t - B) := by rw [← hrel]; field_simp
  -- constants of `E'` used below
  have hsR : s ∈ Set.range (algebraMap R E') := ⟨⟨s, hs'⟩, rfl⟩
  have hKR : ∀ r : Kc, j (algebraMap Kc E r) ∈ Set.range (algebraMap R E') :=
    fun r ↦ ⟨⟨_, hK r⟩, rfl⟩
  have memR : ∀ z : E', z ∈ Set.range (algebraMap R E') → z ∈ R⟮t⟯ := by
    rintro z ⟨r, rfl⟩; exact IntermediateField.algebraMap_mem _ _
  have hxmem : X' ∈ R⟮t⟯ := by
    rw [hxt]
    refine div_mem (sub_mem (memR _ (hKR c)) (pow_mem (mem_adjoin_simple_self _ _) _))
      (sub_mem (mul_mem (mul_mem ?_ (memR _ hsR)) (mem_adjoin_simple_self _ _)) (memR _ (hKR b)))
    rw [show (2 : E') = algebraMap R E' 2 from (map_ofNat _ 2).symm]
    exact IntermediateField.algebraMap_mem _ _
  have hymem : Y' ∈ R⟮t⟯ := by
    have : Y' = t + s * X' := by rw [ht]; ring
    rw [this]
    exact add_mem (mem_adjoin_simple_self _ _) (mul_mem (memR _ hsR) hxmem)
  -- the image of `Kc(x)` lies in `R(t)`
  have hKx : ∀ w : E, w ∈ Kc⟮x⟯ → j w ∈ R⟮t⟯ := by
    let T : IntermediateField Kc E :=
      { carrier := {w | j w ∈ R⟮t⟯}
        mul_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢; exact mul_mem ha hb
        one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact one_mem _
        add_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢; exact add_mem ha hb
        zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact zero_mem _
        algebraMap_mem' := fun r ↦ memR _ (hKR r)
        inv_mem' := fun a ha ↦ by
          simp only [Set.mem_setOf_eq, map_inv₀] at ha ⊢; exact inv_mem ha }
    have hle : Kc⟮x⟯ ≤ T := by
      rw [adjoin_simple_le_iff]
      exact hxmem
    exact fun w hw ↦ hle hw
  have hall : ∀ z : E', z ∈ R⟮t⟯ := by
    intro z
    obtain ⟨u, v, rfl⟩ := hrep z
    have hE : ∀ w : E, j w ∈ R⟮t⟯ := by
      intro w
      obtain ⟨α, β, hα, hβ, rfl⟩ := hgen w
      rw [map_add, map_mul]
      exact add_mem (hKx α hα) (mul_mem (hKx β hβ) hymem)
    exact add_mem (hE u) (mul_mem (hE v) (memR _ hsR))
  -- `t` is not a constant
  have ht' : t′ ≠ 0 := by
    intro h0
    have hX'd : X'′ = 1 := by rw [hjd, hx, map_one]
    have hB : B′ = 0 := hK b
    have hC' : Cc′ = 0 := hK c
    have h2 : (2 : E')′ = 0 := by
      rw [show (2 : E') = 1 + 1 by norm_num, map_add, Derivation.map_one_eq_zero, add_zero]
    have : X'′ = 0 := by
      rw [hxt, Derivation.leibniz_div, map_sub, map_sub, Derivation.leibniz_pow, h0, hC',
        Derivation.leibniz, Derivation.leibniz, hs', h0, hB]
      simp [h2]
    rw [hX'd] at this
    exact one_ne_zero this
  have hmain := hasElementaryIntegral_of_generated (Kc := R) (E := E') hR t ht' hall (j f)
  exact HasElementaryIntegral.of_extension hEE' hmain

/-- **`∫ dx / √(3 − 2x²)` is elementary** (no square root of `−2` or rational root needed). -/
theorem ex_genus0_general (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = 3 - 2 * x ^ 2) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral (1 / y) :=
  genus0_elementary_gen hC x y hx (-2) 0 3 (by norm_num) (by norm_num)
    (by rw [hy]; simp only [map_neg, map_ofNat, map_zero]; ring)
    hgen _

end Rational

end Differential
