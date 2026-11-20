import RischTragerBronstein.Computable.ExpFullDecision
import RischTragerBronstein.Computable.PrimNElem

/-!
# One exponential over an arbitrary base: the structure of elementary integrals

`K = F₀(t)`, `t′ = η t`. The base `F₀` is arbitrary. What the proofs need from the base, inside an
elementary extension `E ⊇ K` with constants `C = Const(E)`, is a **lift**: an intermediate field
`F₁ ⊇ F₀` of `E` over `C`, closed under the derivation, over which `t` stays transcendental. For
`F₀ = R(x)` this is `C(x)`; for the function field of a curve, `C(x, y)`.

* `residue_of_lift`: an elementary integral of `B / (sd tᵏ)` forces the residue test;
* `laurent_rde_of_lift`: an elementary integral of `Λ(t) / tⁿ` forces the Risch equations
  `y′ + (j − n) η y = Λⱼ` (`j ≠ n`) to be solvable in `F₁`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential CPoly

section Lift

variable {F₀ K : Type*} [Field F₀] [Field K] [Algebra F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

/-- **Residues from a lift.** -/
theorem residue_of_lift (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K)) (η : F₀)
    (ht0 : t ≠ 0) (ht : t′ = algebraMap F₀ K η * t)
    (Bn b sd r : F₀[X]) (k : ℕ) (hsd : Squarefree sd) (hX : ¬X ∣ sd) (hBn : sd ∣ Bn - b * X ^ k)
    (hr : sd ∣ r * (mapCoeffs sd + C η * X * derivative sd) - b)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    (hE : IsElementaryExtension K E) (g : E)
    (hg : g′ = algebraMap K E (aeval t Bn / (aeval t sd * t ^ k)))
    (F₁ : IntermediateField (constants E) E) (hcl : DerivClosed F₁)
    (hF₀ : ∀ f : F₀, algebraMap K E (algebraMap F₀ K f) ∈ F₁)
    (htr : Transcendental F₁ (algebraMap K E t)) :
    sd ∣ residueTest r sd := by
  classical
  set ψ := algebraMap K E with hψ
  have hcharE : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hcharF₀ : CharZero F₀ := ⟨fun m n h ↦ by
    have := congrArg (algebraMap F₀ K) h
    simpa using this⟩
  let Cc := constants E
  let _ : Differential Cc := ⟨0⟩
  have hDAc : DifferentialAlgebra Cc E := ⟨fun c ↦ c.2⟩
  letI : Differential F₁ := differentialOfDerivClosed hcl
  have hDA1E : DifferentialAlgebra F₁ E := differentialAlgebra_of_derivClosed hcl
  -- `F₀ → F₁`
  let j₀ : F₀ →+* E := ψ.comp (algebraMap F₀ K)
  have hj₀' : ∀ f : F₀, (j₀ f)′ = j₀ f′ := fun f ↦ by
    change (ψ (algebraMap F₀ K f))′ = ψ (algebraMap F₀ K f′)
    rw [hψ, deriv_algebraMap, deriv_algebraMap]
  let j : F₀ →+* F₁ := j₀.codRestrict _ hF₀
  have hjE : ∀ f : F₀, algebraMap F₁ E (j f) = j₀ f := fun _ ↦ rfl
  have hj : ∀ a : F₀, j a′ = (j a)′ := fun a ↦ Subtype.ext (hj₀' a).symm
  set η₁ : F₁ := j η with hη₁
  set tE := ψ t with htE
  have htE0 : tE ≠ 0 := (map_ne_zero ψ).mpr ht0
  have htE'' : tE′ = algebraMap F₁ E η₁ * tE := by
    rw [htE, hψ, deriv_algebraMap, ht, map_mul]
    rfl
  -- all constants of `E` lie in `F₁`
  have hconstF : ∀ z : E, z′ = 0 → z ∈ F₁ := fun z hz ↦ F₁.algebraMap_mem (⟨z, hz⟩ : Cc)
  have hconst1 : ∀ z ∈ F₁⟮tE⟯, z′ = 0 → z ∈ Set.range (algebraMap F₁ E) :=
    fun z _ hz ↦ ⟨⟨z, hconstF z hz⟩, rfl⟩
  -- the strong Liouville theorem
  obtain ⟨κ, s, c, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g hg
  set B : IntermediateField F₁ E := F₁⟮tE⟯ with hB
  have hBconst : ∀ z : E, z′ = 0 → z ∈ B := fun z hz ↦ B.algebraMap_mem ⟨z, hconstF z hz⟩
  have hBt : tE ∈ B := mem_adjoin_simple_self _ tE
  let T : IntermediateField F₀ K :=
    { carrier := {k | ψ k ∈ B}
      mul_mem' := fun {k l} hk hl ↦ by
        change ψ (k * l) ∈ B; rw [map_mul]; exact mul_mem hk hl
      one_mem' := by change ψ 1 ∈ B; rw [map_one]; exact one_mem _
      add_mem' := fun {k l} hk hl ↦ by
        change ψ (k + l) ∈ B; rw [map_add]; exact add_mem hk hl
      zero_mem' := by change ψ 0 ∈ B; rw [map_zero]; exact zero_mem _
      algebraMap_mem' := fun f ↦ B.algebraMap_mem (j f)
      inv_mem' := fun k hk ↦ by
        change ψ k⁻¹ ∈ B; rw [map_inv₀]; exact inv_mem hk }
  have hT' : T = ⊤ := by
    rw [eq_top_iff, ← hgen, adjoin_le_iff]
    rintro k rfl
    exact hBt
  have hKB : ∀ k : K, ψ k ∈ B := fun k ↦ by
    have : k ∈ T := hT' ▸ IntermediateField.mem_top
    exact this
  have hcf : ∀ z ∈ constField K E, z ∈ B := by
    let N : IntermediateField K E := { B.toSubfield with algebraMap_mem' := hKB }
    have : constField K E ≤ N := adjoin_le_iff.mpr fun z hz ↦ hBconst z hz
    exact fun z hz ↦ this hz
  let c' : κ → F₁ := fun i ↦ if hi : i ∈ s then ⟨c i, hconstF _ (hdata i hi).1⟩ else 0
  have hc' : ∀ i ∈ s, (c' i)′ = 0 := fun i hi ↦ by
    simp only [c', dif_pos hi]
    exact Subtype.ext (hdata i hi).1
  have haev : ∀ P : F₀[X], aeval tE (P.map j) = ψ (aeval t P) := fun P ↦ by
    rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
    rfl
  have hcharF₁ : CharZero F₁ := ⟨fun m n h ↦ by
    have := congrArg (fun z : F₁ ↦ (z : E)) h
    simpa using this⟩
  have hsd₁ : Squarefree (sd.map j) :=
    ((PerfectField.separable_iff_squarefree.mpr hsd).map).squarefree
  have hr₁ : sd.map j ∣ r.map j * (mapCoeffs (sd.map j) + C η₁ * X * derivative (sd.map j)) -
      b.map j := by
    have := Polynomial.map_dvd j hr
    rwa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, map_C, map_X, mapCoeffs_map j hj, ← derivative_map] at this
  have hX₁ : ¬X ∣ sd.map j := fun hd ↦ hX (by
    rwa [← Polynomial.map_X j, Polynomial.map_dvd_map' j] at hd)
  have hB₁ : sd.map j ∣ Bn.map j - b.map j * X ^ k := by
    have := Polynomial.map_dvd j hBn
    rwa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X] at this
  have hdvd := residueTest_step_exponential (F := F₁) tE htr η₁ htE'' hconst1 s c' u
    (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) hc' v (hcf _ hv) (Bn.map j) (b.map j)
    (sd.map j) (r.map j) k hsd₁ hX₁ hB₁ hr₁ (by
      rw [haev, haev, ← map_pow, ← map_mul, ← map_div₀, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)
  rwa [← residueTest_map j hj, Polynomial.map_dvd_map' j] at hdvd

/-- **Risch equations from a lift**: an elementary integral of the Laurent polynomial `Λ(t) / tⁿ`
forces every `y′ + (j − n) η y = Λⱼ`, `j ≠ n`, to be solvable in `F₁`. -/
theorem laurent_rde_of_lift (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (η : F₀) (ht0 : t ≠ 0) (ht : t′ = algebraMap F₀ K η * t) (Λ : F₀[X]) (n : ℕ)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    (hE : IsElementaryExtension K E) (g : E)
    (hg : g′ = algebraMap K E (aeval t Λ / t ^ n))
    (F₁ : IntermediateField (constants E) E) (hcl : DerivClosed F₁)
    (hF₀ : ∀ f : F₀, algebraMap K E (algebraMap F₀ K f) ∈ F₁)
    (htr : Transcendental F₁ (algebraMap K E t)) (jj : ℕ) (hjj : jj ≠ n) :
    ∃ y : E, y ∈ F₁ ∧ y′ + ((jj : E) - n) * algebraMap K E (algebraMap F₀ K η) * y =
      algebraMap K E (algebraMap F₀ K (Λ.coeff jj)) := by
  classical
  set ψ := algebraMap K E with hψ
  have hcharE : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hcharF₀ : CharZero F₀ := ⟨fun m n h ↦ by
    have := congrArg (algebraMap F₀ K) h
    simpa using this⟩
  let Cc := constants E
  let _ : Differential Cc := ⟨0⟩
  have hDAc : DifferentialAlgebra Cc E := ⟨fun c ↦ c.2⟩
  letI : Differential F₁ := differentialOfDerivClosed hcl
  have hDA1E : DifferentialAlgebra F₁ E := differentialAlgebra_of_derivClosed hcl
  -- `F₀ → F₁`
  let j₀ : F₀ →+* E := ψ.comp (algebraMap F₀ K)
  have hj₀' : ∀ f : F₀, (j₀ f)′ = j₀ f′ := fun f ↦ by
    change (ψ (algebraMap F₀ K f))′ = ψ (algebraMap F₀ K f′)
    rw [hψ, deriv_algebraMap, deriv_algebraMap]
  let j : F₀ →+* F₁ := j₀.codRestrict _ hF₀
  have hjE : ∀ f : F₀, algebraMap F₁ E (j f) = j₀ f := fun _ ↦ rfl
  have hj : ∀ a : F₀, j a′ = (j a)′ := fun a ↦ Subtype.ext (hj₀' a).symm
  set η₁ : F₁ := j η with hη₁
  set tE := ψ t with htE
  have htE0 : tE ≠ 0 := (map_ne_zero ψ).mpr ht0
  have htE'' : tE′ = algebraMap F₁ E η₁ * tE := by
    rw [htE, hψ, deriv_algebraMap, ht, map_mul]
    rfl
  -- all constants of `E` lie in `F₁`
  have hconstF : ∀ z : E, z′ = 0 → z ∈ F₁ := fun z hz ↦ F₁.algebraMap_mem (⟨z, hz⟩ : Cc)
  have hconst1 : ∀ z ∈ F₁⟮tE⟯, z′ = 0 → z ∈ Set.range (algebraMap F₁ E) :=
    fun z _ hz ↦ ⟨⟨z, hconstF z hz⟩, rfl⟩
  -- the strong Liouville theorem
  obtain ⟨κ, s, c, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g hg
  set B : IntermediateField F₁ E := F₁⟮tE⟯ with hB
  have hBconst : ∀ z : E, z′ = 0 → z ∈ B := fun z hz ↦ B.algebraMap_mem ⟨z, hconstF z hz⟩
  have hBt : tE ∈ B := mem_adjoin_simple_self _ tE
  let T : IntermediateField F₀ K :=
    { carrier := {k | ψ k ∈ B}
      mul_mem' := fun {k l} hk hl ↦ by
        change ψ (k * l) ∈ B; rw [map_mul]; exact mul_mem hk hl
      one_mem' := by change ψ 1 ∈ B; rw [map_one]; exact one_mem _
      add_mem' := fun {k l} hk hl ↦ by
        change ψ (k + l) ∈ B; rw [map_add]; exact add_mem hk hl
      zero_mem' := by change ψ 0 ∈ B; rw [map_zero]; exact zero_mem _
      algebraMap_mem' := fun f ↦ B.algebraMap_mem (j f)
      inv_mem' := fun k hk ↦ by
        change ψ k⁻¹ ∈ B; rw [map_inv₀]; exact inv_mem hk }
  have hT' : T = ⊤ := by
    rw [eq_top_iff, ← hgen, adjoin_le_iff]
    rintro k rfl
    exact hBt
  have hKB : ∀ k : K, ψ k ∈ B := fun k ↦ by
    have : k ∈ T := hT' ▸ IntermediateField.mem_top
    exact this
  have hcf : ∀ z ∈ constField K E, z ∈ B := by
    let N : IntermediateField K E := { B.toSubfield with algebraMap_mem' := hKB }
    have : constField K E ≤ N := adjoin_le_iff.mpr fun z hz ↦ hBconst z hz
    exact fun z hz ↦ this hz
  let c' : κ → F₁ := fun i ↦ if hi : i ∈ s then ⟨c i, hconstF _ (hdata i hi).1⟩ else 0
  have haev : ∀ P : F₀[X], aeval tE (P.map j) = ψ (aeval t P) := fun P ↦ by
    rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
    rfl
  obtain ⟨y, hy⟩ := (rde_step_exponential_laurent (F := F₁) tE htr η₁ htE'' hconst1 s c' u
    (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) v (hcf _ hv) (Λ.map j) n (by
      rw [haev, htE, ← map_pow, ← map_div₀, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)).1 jj hjj
  refine ⟨(y : E), y.2, ?_⟩
  have := congrArg (algebraMap F₁ E) hy
  rw [map_add, map_mul, map_mul, map_sub, map_natCast, map_natCast, coeff_map] at this
  exact this

end Lift

section Decide

universe u

variable {F₀ : Type*} {K : Type u} [Field F₀] [Field K] [Algebra F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

/-- **The lift property of the base**: in every elementary extension `E` of `K`, a field `F₁ ⊇ F₀`
over the constants of `E`, closed under the derivation, over which `t` is transcendental, and from
which solutions of the Risch equations `y′ + m η y = f` (`m ≠ 0`, `f ∈ F₀` with `P f`) descend to
`F₀`. -/
def ExpLift (F₀ : Type*) [Field F₀] [Algebra F₀ K] [Differential F₀] (t : K) (η : F₀)
    (P : F₀ → Prop) : Prop :=
  ∀ (E : Type u) (_ : Field E) (_ : Differential E) (_ : Algebra K E) (_ : DifferentialAlgebra K E),
    IsElementaryExtension K E →
    ∃ (F₁ : IntermediateField (constants E) E) (_ : DerivClosed F₁),
      (∀ f : F₀, algebraMap K E (algebraMap F₀ K f) ∈ F₁) ∧
      Transcendental F₁ (algebraMap K E t) ∧
      ∀ (m : ℤ), m ≠ 0 → ∀ f : F₀, P f →
        (∃ y : E, y ∈ F₁ ∧ y′ + (m : E) * algebraMap K E (algebraMap F₀ K η) * y =
          algebraMap K E (algebraMap F₀ K f)) →
        ∃ y : F₀, y′ + (m : F₀) * η * y = f

/-- The Laurent part `Λ(t) / tⁿ` as its constant term plus the other powers. -/
lemma laurent_split (t : K) (ht0 : t ≠ 0) (Λ : F₀[X]) (n : ℕ) :
    aeval t Λ / t ^ n = algebraMap F₀ K (Λ.coeff n) +
      ∑ j ∈ (Finset.range (Λ.natDegree + n + 1)).erase n,
        algebraMap F₀ K (Λ.coeff j) * t ^ j / t ^ n := by
  have htn : t ^ n ≠ 0 := pow_ne_zero _ ht0
  rw [aeval_eq_sum_range' (n := Λ.natDegree + n + 1) (by omega), Finset.sum_div,
    ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : n < Λ.natDegree + n + 1))]
  congr 1
  · rw [Algebra.smul_def, mul_div_assoc, div_self htn, mul_one]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def]

/-- **One exponential over a base with the lift property.** `f = g′ + Λ(t)/tⁿ + b(t)/sd(t)` has an
elementary integral iff the residue test passes, every `y′ + (j − n) η y = Λⱼ` (`j ≠ n`) is
solvable in `F₀`, and the constant term `Λₙ` has an elementary integral (given that such an
integral persists in every extension, `hasc`). -/
theorem expGen_decides (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K)) (η : F₀)
    (ht0 : t ≠ 0) (ht : t′ = algebraMap F₀ K η * t) (P : F₀ → Prop) (hlift : ExpLift F₀ t η P)
    (g : K) (Λ : F₀[X]) (n : ℕ) (hΛP : ∀ j, j ≠ n → P (Λ.coeff j)) (b sd r : F₀[X]) (hsd : Squarefree sd) (hX : ¬X ∣ sd)
    (hdeg : b.degree < sd.degree) (hst : aeval t sd ≠ 0)
    (hr : sd ∣ r * (mapCoeffs sd + C η * X * derivative sd) - b)
    (hasc : HasElementaryIntegral (algebraMap F₀ K (Λ.coeff n)) →
      HasElementaryIntegralIn (algebraMap F₀ K (Λ.coeff n))) :
    HasElementaryIntegral (g′ + aeval t Λ / t ^ n + aeval t b / aeval t sd) ↔
      sd ∣ residueTest r sd ∧ (∀ j, j ≠ n → ∃ y : F₀, y′ + ((j : F₀) - n) * η * y = Λ.coeff j) ∧
        HasElementaryIntegral (algebraMap F₀ K (Λ.coeff n)) := by
  classical
  have hcharF₀ : CharZero F₀ := ⟨fun m n h ↦ by
    have := congrArg (algebraMap F₀ K) h
    simpa using this⟩
  have htn : t ^ n ≠ 0 := pow_ne_zero _ ht0
  have hsep : sd.Separable := PerfectField.separable_iff_squarefree.mpr hsd
  have hlogIn : sd ∣ residueTest r sd → HasElementaryIntegralIn (aeval t b / aeval t sd) :=
    fun hT ↦ hasElementaryIntegralIn_of_residueTest t 0 η (by rw [ht, map_zero, zero_add]) t ht0
      (by rw [logDeriv, ht, mul_div_assoc, div_self ht0, mul_one]) sd b r hsep hst hdeg
      (by rwa [C_0, zero_add]) hT
  -- the antiderivative of the non-constant powers
  have hW : ∀ y : ℕ → F₀, (∀ j, j ≠ n → (y j)′ + ((j : F₀) - n) * η * y j = Λ.coeff j) →
      (∑ j ∈ (Finset.range (Λ.natDegree + n + 1)).erase n,
        algebraMap F₀ K (y j) * t ^ j / t ^ n)′ =
      ∑ j ∈ (Finset.range (Λ.natDegree + n + 1)).erase n,
        algebraMap F₀ K (Λ.coeff j) * t ^ j / t ^ n := fun y hy ↦ by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [deriv_mul_pow_div_pow _ t _ ht0 ht, deriv_algebraMap, ← hy j (Finset.ne_of_mem_erase hj)]
    simp only [map_add, map_mul, map_sub, map_natCast]
  constructor
  · intro hf
    have h1 : HasElementaryIntegral (aeval t Λ / t ^ n + aeval t b / aeval t sd) := by
      have := hf.sub_in (hasElementaryIntegralIn_deriv g)
      rwa [show g′ + aeval t Λ / t ^ n + aeval t b / aeval t sd - g′ =
        aeval t Λ / t ^ n + aeval t b / aeval t sd by ring] at this
    -- the residue test
    have hT : sd ∣ residueTest r sd := by
      obtain ⟨E, _, _, _, _, hE, gE, hgE⟩ := h1
      obtain ⟨F₁, hcl, hF₀, htr, -⟩ := hlift E inferInstance inferInstance inferInstance inferInstance hE
      refine residue_of_lift t hgen η ht0 ht (Λ * sd + b * X ^ n) b sd r n hsd hX ⟨Λ, by ring⟩ hr
        E hE gE ?_ F₁ hcl hF₀ htr
      rw [hgE]
      congr 1
      rw [map_add, map_mul, map_mul, map_pow, aeval_X]
      field_simp
    have h2 : HasElementaryIntegral (aeval t Λ / t ^ n) := by
      have := h1.sub_in (hlogIn hT)
      rwa [add_sub_cancel_right] at this
    -- the Risch equations
    have hRDE : ∀ j, j ≠ n → ∃ y : F₀, y′ + ((j : F₀) - n) * η * y = Λ.coeff j := by
      intro j hj
      obtain ⟨E, _, _, _, _, hE, gE, hgE⟩ := h2
      obtain ⟨F₁, hcl, hF₀, htr, htrans⟩ := hlift E inferInstance inferInstance inferInstance inferInstance hE
      obtain ⟨yE, hyF, hyE⟩ := laurent_rde_of_lift t hgen η ht0 ht Λ n E hE gE hgE F₁ hcl hF₀ htr
        j hj
      have hm : ((j : ℤ) - n : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
      obtain ⟨y, hy⟩ := htrans _ hm (Λ.coeff j) (hΛP j hj) ⟨yE, hyF, by
        rw [← hyE]; push_cast; ring⟩
      exact ⟨y, by rw [← hy]; push_cast; ring⟩
    refine ⟨hT, hRDE, ?_⟩
    -- the constant term
    have hex : ∀ j, ∃ y : F₀, j ≠ n → y′ + ((j : F₀) - n) * η * y = Λ.coeff j := fun j ↦ by
      by_cases hj : j ≠ n
      · obtain ⟨y, hy⟩ := hRDE j hj; exact ⟨y, fun _ ↦ hy⟩
      · exact ⟨0, fun h ↦ absurd h hj⟩
    choose y hy using hex
    have := h2.sub_in (hasElementaryIntegralIn_deriv
      (∑ j ∈ (Finset.range (Λ.natDegree + n + 1)).erase n, algebraMap F₀ K (y j) * t ^ j / t ^ n))
    rwa [hW y hy, laurent_split t ht0 Λ n, add_sub_cancel_right] at this
  · rintro ⟨hT, hRDE, hc⟩
    have hex : ∀ j, ∃ y : F₀, j ≠ n → y′ + ((j : F₀) - n) * η * y = Λ.coeff j := fun j ↦ by
      by_cases hj : j ≠ n
      · obtain ⟨y, hy⟩ := hRDE j hj; exact ⟨y, fun _ ↦ hy⟩
      · exact ⟨0, fun h ↦ absurd h hj⟩
    choose y hy using hex
    have hL := (hasc hc).hasElementaryIntegral.add_in (hasElementaryIntegralIn_deriv
      (∑ j ∈ (Finset.range (Λ.natDegree + n + 1)).erase n, algebraMap F₀ K (y j) * t ^ j / t ^ n))
    rw [hW y hy, ← laurent_split t ht0 Λ n] at hL
    have := (hL.add_in (hlogIn hT)).add_in (hasElementaryIntegralIn_deriv g)
    rwa [show aeval t Λ / t ^ n + aeval t b / aeval t sd + g′ =
      g′ + aeval t Λ / t ^ n + aeval t b / aeval t sd by ring] at this

/-- **Sufficiency, over every extension**: the three conditions of `expGen_decides`, with the
constant term integrable over every extension, give an elementary integral over every extension. -/
theorem expGen_suff_in (t : K) (η : F₀) (ht0 : t ≠ 0) (ht : t′ = algebraMap F₀ K η * t)
    (g : K) (Λ : F₀[X]) (n : ℕ) (b sd r : F₀[X]) (hsd : Squarefree sd)
    (hdeg : b.degree < sd.degree) (hst : aeval t sd ≠ 0)
    (hr : sd ∣ r * (mapCoeffs sd + C η * X * derivative sd) - b)
    (hT : sd ∣ residueTest r sd)
    (hRDE : ∀ j, j ≠ n → ∃ y : F₀, y′ + ((j : F₀) - n) * η * y = Λ.coeff j)
    (hc : HasElementaryIntegralIn (algebraMap F₀ K (Λ.coeff n))) :
    HasElementaryIntegralIn (g′ + aeval t Λ / t ^ n + aeval t b / aeval t sd) := by
  classical
  have hcharF₀ : CharZero F₀ := ⟨fun m n h ↦ by
    have := congrArg (algebraMap F₀ K) h
    simpa using this⟩
  have hsep : sd.Separable := PerfectField.separable_iff_squarefree.mpr hsd
  have hlogIn : HasElementaryIntegralIn (aeval t b / aeval t sd) :=
    hasElementaryIntegralIn_of_residueTest t 0 η (by rw [ht, map_zero, zero_add]) t ht0
      (by rw [logDeriv, ht, mul_div_assoc, div_self ht0, mul_one]) sd b r hsep hst hdeg
      (by rwa [C_0, zero_add]) hT
  have hex : ∀ j, ∃ y : F₀, j ≠ n → y′ + ((j : F₀) - n) * η * y = Λ.coeff j := fun j ↦ by
    by_cases hj : j ≠ n
    · obtain ⟨y, hy⟩ := hRDE j hj; exact ⟨y, fun _ ↦ hy⟩
    · exact ⟨0, fun h ↦ absurd h hj⟩
  choose y hy using hex
  have hW : (∑ j ∈ (Finset.range (Λ.natDegree + n + 1)).erase n,
        algebraMap F₀ K (y j) * t ^ j / t ^ n)′ =
      ∑ j ∈ (Finset.range (Λ.natDegree + n + 1)).erase n,
        algebraMap F₀ K (Λ.coeff j) * t ^ j / t ^ n := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [deriv_mul_pow_div_pow _ t _ ht0 ht, deriv_algebraMap, ← hy j (Finset.ne_of_mem_erase hj)]
    simp only [map_add, map_mul, map_sub, map_natCast]
  have hL := ((hc.add (hasElementaryIntegralIn_deriv
    (∑ j ∈ (Finset.range (Λ.natDegree + n + 1)).erase n, algebraMap F₀ K (y j) * t ^ j / t ^ n))).add
    hlogIn).add (hasElementaryIntegralIn_deriv g)
  rw [hW, ← laurent_split t ht0 Λ n] at hL
  rwa [show aeval t Λ / t ^ n + aeval t b / aeval t sd + g′ =
    g′ + aeval t Λ / t ^ n + aeval t b / aeval t sd by ring] at hL

end Decide

end Curves
