import RischTragerBronstein.Algebraic.Genus0
import RischTragerBronstein.Computable.NestXExample

/-!
# Transcendental towers over a genus-zero base

Over `Kc(x, √(x²+1))` the Euler variable `t = x + √(x²+1)` generates, and after rescaling the
derivation by `1/t′` the tower `Kc(x, y, log(x + y))` becomes the transcendental tower
`Kc(t, log t)` with `t′ = 1`, decided by `nestX_decides`. Example:
**`∫ log(x + √(x² + 1)) / x dx` (`∫ asinh(x)/x dx`) is not elementary**.
-/

open Polynomial Differential IntermediateField

namespace Tower.Genus0Tower

open Tower Tower.PrimN Tower.NestP Tower.NestM Tower.NestX Tower.NestX.Examples

/-- `t₀ = log t` (`t₀′ = 1/t`). -/
def ksG : (m : ℕ) → KindN m
  | 0 => .prim (r [1] [0, 1])
  | m + 1 => .exp (constC (m + 2) 0)

/-- `t₀ (1 + t²)/(t³ − t)`. -/
def AG : Code 2 := ([zero₁, r [1, 0, 1] [0, -1, 0, 1]], [one₁])

set_option maxRecDepth 100000

theorem certG : certX ksG lvA 1 = true := by decide +kernel
theorem ansG : elemNX ksG lvA 1 AG = false := by decide +kernel

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

omit [DifferentialAlgebra Kc E] [CharZero E] in
lemma evN_oneC (x : E) (ts : ℕ → E) : ∀ m, evN Kc x ts m (oneC (m + 1)) = 1
  | 0 => by simp [evN, PrimN.evx, oneC, CPoly.toPoly]
  | m + 1 => by
    change (List.foldr (fun a acc ↦ evN Kc x ts m a + ts m * acc) 0 [oneC (m + 1)]) /
      (List.foldr (fun a acc ↦ evN Kc x ts m a + ts m * acc) 0 [oneC (m + 1)]) = 1
    simp only [List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
    rw [evN_oneC x ts m, div_one]

omit [DifferentialAlgebra Kc E] [CharZero E] in
lemma evN_constC (x : E) (ts : ℕ → E) (c : ℚ) : ∀ m, evN Kc x ts m (constC (m + 1) c) = (c : E)
  | 0 => by simp [evN, PrimN.evx, constC, oneC, CPoly.toPoly]
  | m + 1 => by
    change (List.foldr (fun a acc ↦ evN Kc x ts m a + ts m * acc) 0 [constC (m + 1) c]) /
      (List.foldr (fun a acc ↦ evN Kc x ts m a + ts m * acc) 0 [oneC (m + 1)]) = (c : E)
    simp only [List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
    rw [evN_constC x ts c m, evN_oneC x ts m, div_one]

/-- **`∫ log(x + √(x² + 1)) / x dx` is not elementary.** -/
theorem asinh_div_x_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y θ : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 2 + 1) (hθ : θ′ = (x + y)′ / (x + y))
    (hgen : ∀ z : E, z ∈ IntermediateField.adjoin Kc ({x, y, θ} : Set E)) :
    ¬HasElementaryIntegral (θ / x) := by
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hy
    have h1 := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul, hx, map_add, Derivation.map_one_eq_zero,
      mul_zero, add_zero, zero_mul, map_zero, mul_one] at h1
    have hx0 : x = 0 := by
      have : (2 : E) * x = 0 := by linear_combination -h1
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero
    rw [hx0] at hy; norm_num at hy
  set t := x + y with ht
  have ht0 : t ≠ 0 := by
    intro h0
    have : y = -x := by linear_combination h0
    rw [this] at hy; norm_num at hy
  have hyd : y′ = x / y := by
    have h1 := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul, hx, map_add, Derivation.map_one_eq_zero,
      add_zero, mul_one] at h1
    field_simp
    linear_combination h1 / 2
  have htd : t′ = t / y := by
    rw [ht, map_add, hx, hyd]; field_simp; ring
  have hθ' : θ′ = 1 / y := by
    rw [hθ, htd]; field_simp
  have hxt : x = (t ^ 2 - 1) / (2 * t) := by
    have : (y - x) * t = 1 := by rw [ht]; linear_combination hy
    field_simp; linear_combination -this + t * ht
  have hyt : y = (t ^ 2 + 1) / (2 * t) := by
    have : (y - x) * t = 1 := by rw [ht]; linear_combination hy
    field_simp; linear_combination this + t * ht
  -- rescale
  set τ := t / y with hτ
  have hτ0 : τ ≠ 0 := div_ne_zero ht0 hy0
  let d0 : Derivation ℤ E E := Differential.deriv
  have hd0 : ∀ z : E, d0 z = z′ := fun _ ↦ rfl
  have hc0 : ∀ r : Kc, d0 (algebraMap Kc E r) = 0 := fun r ↦ by
    rw [hd0, deriv_algebraMap, hC, map_zero]
  let D' : Differential E := rescale ⟨d0⟩ (1 / τ)
  have hD't : D'.deriv t = 1 := by
    show 1 / τ * d0 t = 1
    rw [hd0, htd]; exact one_div_mul_cancel hτ0
  have hD'θ : D'.deriv θ = 1 / t := by
    show 1 / τ * d0 θ = 1 / t
    rw [hd0, hθ', hτ]; field_simp
  have hDA' : @DifferentialAlgebra Kc E _ _ _ _ D' :=
    @DifferentialAlgebra.mk Kc E _ _ _ _ D' (fun r ↦ by
      show 1 / τ * d0 (algebraMap Kc E r) = algebraMap Kc E r′
      rw [hc0, hC, map_zero, mul_zero])
  have hCall' : ∀ z : E, D'.deriv z = 0 → z ∈ Set.range (algebraMap Kc E) := by
    intro z hz
    apply hCall
    have : 1 / τ * d0 z = 0 := hz
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (one_div_ne_zero hτ0)
    · exact h0
  -- the tower `Kc(t, log t)` for `D'`
  let ts : ℕ → E := fun m ↦ if m = 0 then θ else 1
  let T : @NestMTower Kc E _ _ _ _ D' _ ksG :=
    { x := t
      ts := ts
      hC := hC
      hx := hD't
      ht := fun m ↦ by
        rcases m with _ | m
        · show D'.deriv θ = _
          rw [hD'θ]
          simp [kder, ksG, evN, PrimN.evx, r, CPoly.toPoly]
        · show D'.deriv 1 = _
          simp only [kder, ksG, evN_constC, Rat.cast_zero, map_zero, zero_mul,
            Derivation.map_one_eq_zero]
      hts0 := fun m a hk ↦ by
        rcases m with _ | m
        · simp [ksG] at hk
        · simp [ts]
      hCall := hCall' }
  -- `E = Kc(t, θ)`
  have hF0 : ∀ z : E, z ∈ Kc⟮t⟯ → z ∈ T.F 1 := by
    intro z hz
    rw [T.mem_F_succ]
    exact IntermediateField.algebraMap_mem (IntermediateField.adjoin (T.F 0) {T.ts 0})
      (⟨z, hz⟩ : T.F 0)
  have hQm : ∀ r : Kc, algebraMap Kc E r ∈ Kc⟮t⟯ := fun r ↦ IntermediateField.algebraMap_mem _ _
  have htm : t ∈ Kc⟮t⟯ := mem_adjoin_simple_self _ _
  have hxm : x ∈ Kc⟮t⟯ := by
    rw [hxt]
    refine div_mem (sub_mem (pow_mem htm _) (one_mem _)) (mul_mem ?_ htm)
    simpa using hQm 2
  have hym : y ∈ Kc⟮t⟯ := by
    rw [hyt]
    refine div_mem (add_mem (pow_mem htm _) (one_mem _)) (mul_mem ?_ htm)
    simpa using hQm 2
  have hθm : θ ∈ T.F 1 := by
    rw [T.mem_F_succ]
    exact mem_adjoin_simple_self _ _
  have hgenT : T.F 1 = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hle : IntermediateField.adjoin Kc ({x, y, θ} : Set E) ≤ T.F 1 := by
      rw [IntermediateField.adjoin_le_iff]
      intro w hw
      rcases hw with rfl | rfl | rfl
      · exact hF0 _ hxm
      · exact hF0 _ hym
      · exact hθm
    exact hle (hgen z)
  have hdec := T.nestX_decides lvA 1 hgenT certG AG
  have hval : (((T.MP 1 (T.xspecs lvA 1 certG).hyp.tr).sem AG : T.F 1) : E) =
      1 / τ * (θ / x) := by
    refine (T.sem_MP 1 _ _).trans ?_
    simp only [evN, PrimN.evx, AG, one₁, zero₁, r, CPoly.toPoly, List.foldr, ts, if_true]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      map_add, map_mul, map_neg, aeval_C, aeval_X, eq_ratCast, mul_zero, add_zero,
      Polynomial.map_zero, map_zero, zero_add, Rat.cast_one, Rat.cast_zero, Rat.cast_neg,
      map_one, mul_one, one_mul]
    have hTx : T.x = t := rfl
    have hTts : T.ts 0 = θ := rfl
    simp only [hTx, hTts, Polynomial.map_one, Polynomial.map_neg, map_neg, map_one]
    have ht1 : t ^ 2 - 1 ≠ 0 := by
      intro h0
      have : x = 0 := by rw [hxt, h0, zero_div]
      rw [this] at hyd hx
      exact one_ne_zero (hx.symm.trans (by simp))
    have ht1' : -1 + t ^ 2 ≠ 0 := by rw [add_comm, ← sub_eq_add_neg]; exact ht1
    have ht3 : t * -1 + t ^ 3 ≠ 0 := by
      rw [show t * -1 + t ^ 3 = t * (t ^ 2 - 1) by ring]; exact mul_ne_zero ht0 ht1
    rw [hτ, hxt, hyt]
    field_simp
    ring
  intro h
  have h' := (hasElementaryIntegral_rescale_iff ⟨d0⟩ (1 / τ) (θ / x) (one_div_ne_zero hτ0)).mpr h
  rw [← hval] at h'
  have := hdec.mp h'
  rw [ansG] at this
  exact Bool.false_ne_true this

end Tower.Genus0Tower
