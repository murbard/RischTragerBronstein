import RischTragerBronstein.Mixed.ExpGen

/-!
# One primitive over an arbitrary base: the structure of elementary integrals

`K = F₀(t)`, `t′ = η ∈ F₀`. As for exponentials (`ExpGen`), the proofs only need a **lift**: inside
an elementary extension `E ⊇ K` with constants `C`, an intermediate field `F₁ ⊇ F₀` of `E` over
`C`, closed under the derivation, over which `t` stays transcendental.

* `liouville_of_lift`: the strong Liouville theorem, with data in `F₁(t)`;
* `residue_of_lift_prim`: an elementary integral of `A(t) + b(t) / sd(t)` forces the residue test;
* `poly_of_lift_prim`: an elementary integral `g` of the polynomial `A(t)` gives `pⱼ ∈ F₁` with
  `pⱼ′ + (j + 1) η pⱼ₊₁ = Aⱼ` (`j ≥ 1`), `p_{d+1}` constant, and `g − ∑ pⱼ tʲ` an integral of
  `A₀ − η p₁`;
* `isElementaryExtension_log'`: `K = F₀(t)`, `t = log u`, is elementary over `F₀`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential CPoly

section Sum

variable {L : Type*} [Field L] [Differential L]

/-- **The derivative of `∑ pⱼ tʲ`** for a primitive `t` and coefficients satisfying the
recurrence: all powers but the constant term match. -/
lemma prim_sum_deriv (t η : L) (ht : t′ = η) (a p : ℕ → L) (d : ℕ)
    (hrec : ∀ j, 1 ≤ j → j ≤ d → (p j)′ + ((j + 1 : ℕ) : L) * η * p (j + 1) = a j)
    (htop : (p (d + 1))′ = 0) :
    (∑ j ∈ Finset.range (d + 1), p (j + 1) * t ^ (j + 1))′ =
      ∑ j ∈ Finset.range (d + 1), a j * t ^ j - a 0 + η * p 1 := by
  have key : (∑ j ∈ Finset.range (d + 1), p (j + 1) * t ^ (j + 1))′ =
      ∑ j ∈ Finset.range (d + 1), ((p (j + 1))′ * t ^ (j + 1) +
        ((j + 1 : ℕ) : L) * p (j + 1) * η * t ^ j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Derivation.leibniz, Derivation.leibniz_pow, ht]
    simp only [smul_eq_mul, Nat.add_sub_cancel]
    push_cast
    ring
  have hstep : ∀ j ∈ Finset.range d, (p (j + 1))′ * t ^ (j + 1) +
      ((j + 1 + 1 : ℕ) : L) * p (j + 1 + 1) * η * t ^ (j + 1) = a (j + 1) * t ^ (j + 1) := by
    intro j hj
    have := hrec (j + 1) (by omega) (by simp at hj; omega)
    rw [← this]
    ring
  have hsplit : ∑ j ∈ Finset.range d, a (j + 1) * t ^ (j + 1) =
      ∑ j ∈ Finset.range d, (p (j + 1))′ * t ^ (j + 1) +
        ∑ j ∈ Finset.range d, ((j + 1 + 1 : ℕ) : L) * p (j + 1 + 1) * η * t ^ (j + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj ↦ (hstep j hj).symm
  rw [key, Finset.sum_add_distrib, Finset.sum_range_succ (fun j ↦ (p (j + 1))′ * t ^ (j + 1)),
    htop, Finset.sum_range_succ' (fun j ↦ ((j + 1 : ℕ) : L) * p (j + 1) * η * t ^ j),
    Finset.sum_range_succ' (fun j ↦ a j * t ^ j), hsplit]
  simp only [zero_mul, add_zero, zero_add, Nat.cast_one, one_mul, pow_zero, mul_one]
  ring

end Sum

section Lift

variable {F₀ K : Type*} [Field F₀] [Field K] [Algebra F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]

/-- **The strong Liouville theorem with data in a lift** `F₁(t)`. -/
theorem liouville_of_lift (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    (hE : IsElementaryExtension K E) (f : K) (g : E) (hg : g′ = algebraMap K E f)
    (F₁ : IntermediateField (constants E) E) (hcl : DerivClosed F₁)
    (hF₀ : ∀ f : F₀, algebraMap K E (algebraMap F₀ K f) ∈ F₁) :
    letI : Differential F₁ := differentialOfDerivClosed hcl
    ∃ (ι : Type) (s : Finset ι) (c : ι → F₁) (u : ι → E) (v : E),
      (∀ i ∈ s, u i ∈ F₁⟮algebraMap K E t⟯ ∧ u i ≠ 0) ∧ (∀ i ∈ s, (c i)′ = 0) ∧
      v ∈ F₁⟮algebraMap K E t⟯ ∧
      algebraMap K E f = ∑ i ∈ s, algebraMap F₁ E (c i) * logDeriv (u i) + v′ := by
  classical
  letI : Differential F₁ := differentialOfDerivClosed hcl
  set ψ := algebraMap K E with hψ
  have hcharE : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let Cc := constants E
  have hconstF : ∀ z : E, z′ = 0 → z ∈ F₁ := fun z hz ↦ F₁.algebraMap_mem (⟨z, hz⟩ : Cc)
  let j₀ : F₀ →+* E := ψ.comp (algebraMap F₀ K)
  let j : F₀ →+* F₁ := j₀.codRestrict _ hF₀
  set tE := ψ t with htE
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
  refine ⟨κ, s, c', u, v, fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩,
    fun i hi ↦ ?_, hcf _ hv, ?_⟩
  · simp only [c', dif_pos hi]
    exact Subtype.ext (hdata i hi).1
  · rw [heq]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [c', dif_pos hi]
    rfl

/-- **Residues from a lift** (primitive case): an elementary integral of `A(t) + b(t) / sd(t)`
forces the residue test. -/
theorem residue_of_lift_prim (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (η : F₀) (ht : t′ = algebraMap F₀ K η)
    (A b sd r : F₀[X]) (hsd : Squarefree sd)
    (hr : sd ∣ r * (mapCoeffs sd + C η * derivative sd) - b)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    (hE : IsElementaryExtension K E) (g : E)
    (hg : g′ = algebraMap K E (aeval t A + aeval t b / aeval t sd)) (hst : aeval t sd ≠ 0)
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
  let _ : Differential (constants E) := ⟨0⟩
  have hDAc : DifferentialAlgebra (constants E) E := ⟨fun c ↦ c.2⟩
  letI : Differential F₁ := differentialOfDerivClosed hcl
  have hDA1E : DifferentialAlgebra F₁ E := differentialAlgebra_of_derivClosed hcl
  let j₀ : F₀ →+* E := ψ.comp (algebraMap F₀ K)
  have hj₀' : ∀ f : F₀, (j₀ f)′ = j₀ f′ := fun f ↦ by
    change (ψ (algebraMap F₀ K f))′ = ψ (algebraMap F₀ K f′)
    rw [hψ, deriv_algebraMap, deriv_algebraMap]
  let j : F₀ →+* F₁ := j₀.codRestrict _ hF₀
  have hj : ∀ a : F₀, j a′ = (j a)′ := fun a ↦ Subtype.ext (hj₀' a).symm
  set η₁ : F₁ := j η with hη₁
  set tE := ψ t with htE
  have htE'' : tE′ = algebraMap F₁ E η₁ := by
    rw [htE, hψ, deriv_algebraMap, ht]
    rfl
  have hconstF : ∀ z : E, z′ = 0 → z ∈ F₁ := fun z hz ↦
    F₁.algebraMap_mem (⟨z, hz⟩ : constants E)
  have hconst1 : ∀ z ∈ F₁⟮tE⟯, z′ = 0 → z ∈ Set.range (algebraMap F₁ E) :=
    fun z _ hz ↦ ⟨⟨z, hconstF z hz⟩, rfl⟩
  obtain ⟨κ, s, c, u, v, hu, hc, hv, heq⟩ :=
    liouville_of_lift t hgen E hE _ g hg F₁ hcl hF₀
  have haev : ∀ P : F₀[X], aeval tE (P.map j) = ψ (aeval t P) := fun P ↦ by
    rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
    rfl
  have hcharF₁ : CharZero F₁ := ⟨fun m n h ↦ by
    have := congrArg (fun z : F₁ ↦ (z : E)) h
    simpa using this⟩
  have hsd₁ : Squarefree (sd.map j) :=
    ((PerfectField.separable_iff_squarefree.mpr hsd).map).squarefree
  -- the full numerator `A sd + b`
  have hr₁ : sd.map j ∣ r.map j * (mapCoeffs (sd.map j) + C η₁ * derivative (sd.map j)) -
      (A * sd + b).map j := by
    have h2 : sd ∣ r * (mapCoeffs sd + C η * derivative sd) - (A * sd + b) := by
      have : r * (mapCoeffs sd + C η * derivative sd) - (A * sd + b) =
          (r * (mapCoeffs sd + C η * derivative sd) - b) - A * sd := by ring
      rw [this]; exact dvd_sub hr (dvd_mul_left _ _)
    have := Polynomial.map_dvd j h2
    rwa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_mul, map_C,
      mapCoeffs_map j hj, ← derivative_map] at this
  have hdvd := residueTest_step_primitive (F := F₁) tE htr η₁ htE'' hconst1 s c u hu hc v hv
    ((A * sd + b).map j) (sd.map j) (r.map j) hsd₁ hr₁ (by
      rw [haev, haev, ← map_div₀, ← heq]
      congr 1
      have hst' : aeval t sd ≠ 0 := hst
      rw [map_add, map_mul]
      field_simp)
  rwa [← residueTest_map j hj, Polynomial.map_dvd_map' j] at hdvd

/-- **The polynomial part from a lift** (primitive case). -/
theorem poly_of_lift_prim (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (η : F₀) (ht : t′ = algebraMap F₀ K η) (A : F₀[X]) (d : ℕ) (hd : A.natDegree ≤ d)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    (hE : IsElementaryExtension K E) (g : E) (hg : g′ = algebraMap K E (aeval t A))
    (F₁ : IntermediateField (constants E) E) (hcl : DerivClosed F₁)
    (hF₀ : ∀ f : F₀, algebraMap K E (algebraMap F₀ K f) ∈ F₁)
    (htr : Transcendental F₁ (algebraMap K E t)) :
    ∃ p : ℕ → E, (∀ j, p j ∈ F₁) ∧
      (∀ j, 1 ≤ j → (p j)′ + ((j + 1 : ℕ) : E) * algebraMap K E (algebraMap F₀ K η) * p (j + 1) =
        algebraMap K E (algebraMap F₀ K (A.coeff j))) ∧ (p (d + 1))′ = 0 ∧
      (g - ∑ j ∈ Finset.range (d + 1), p (j + 1) * algebraMap K E t ^ (j + 1))′ =
        algebraMap K E (algebraMap F₀ K (A.coeff 0)) -
          algebraMap K E (algebraMap F₀ K η) * p 1 := by
  classical
  set ψ := algebraMap K E with hψ
  have hcharE : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let _ : Differential (constants E) := ⟨0⟩
  have hDAc : DifferentialAlgebra (constants E) E := ⟨fun c ↦ c.2⟩
  letI : Differential F₁ := differentialOfDerivClosed hcl
  have hDA1E : DifferentialAlgebra F₁ E := differentialAlgebra_of_derivClosed hcl
  let j₀ : F₀ →+* E := ψ.comp (algebraMap F₀ K)
  have hj₀' : ∀ f : F₀, (j₀ f)′ = j₀ f′ := fun f ↦ by
    change (ψ (algebraMap F₀ K f))′ = ψ (algebraMap F₀ K f′)
    rw [hψ, deriv_algebraMap, deriv_algebraMap]
  let j : F₀ →+* F₁ := j₀.codRestrict _ hF₀
  set η₁ : F₁ := j η with hη₁
  set tE := ψ t with htE
  have htE'' : tE′ = algebraMap F₁ E η₁ := by
    rw [htE, hψ, deriv_algebraMap, ht]
    rfl
  have hconstF : ∀ z : E, z′ = 0 → z ∈ F₁ := fun z hz ↦
    F₁.algebraMap_mem (⟨z, hz⟩ : constants E)
  have hconst1 : ∀ z ∈ F₁⟮tE⟯, z′ = 0 → z ∈ Set.range (algebraMap F₁ E) :=
    fun z _ hz ↦ ⟨⟨z, hconstF z hz⟩, rfl⟩
  obtain ⟨κ, s, c, u, v, hu, -, hv, heq⟩ :=
    liouville_of_lift t hgen E hE _ g hg F₁ hcl hF₀
  have haev : ∀ P : F₀[X], aeval tE (P.map j) = ψ (aeval t P) := fun P ↦ by
    rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
    rfl
  obtain ⟨p, hrec, htop⟩ := coeffs_step_primitive (F := F₁) tE htr η₁ htE'' hconst1 s c u hu v hv
    (A.map j) (by rw [haev, heq])
  have hdj : (A.map j).natDegree ≤ d := (natDegree_map_le).trans hd
  have hcoef : ∀ i, algebraMap F₁ E ((A.map j).coeff i) = ψ (algebraMap F₀ K (A.coeff i)) :=
    fun i ↦ by rw [coeff_map]; rfl
  have hrecE : ∀ i, 1 ≤ i → ((p i : F₁) : E)′ + ((i + 1 : ℕ) : E) * ψ (algebraMap F₀ K η) *
      (p (i + 1) : E) = ψ (algebraMap F₀ K (A.coeff i)) := fun i hi ↦ by
    have := congrArg (algebraMap F₁ E) (hrec i hi)
    rw [map_add, map_mul, map_mul, map_natCast, hcoef] at this
    exact this
  have htopE : ((p (d + 1) : F₁) : E)′ = 0 := by
    have := congrArg (algebraMap F₁ E) (htop d hdj)
    rw [map_zero] at this
    exact this
  refine ⟨fun i ↦ (p i : E), fun i ↦ (p i).2, hrecE, htopE, ?_⟩
  have hsum := prim_sum_deriv tE (ψ (algebraMap F₀ K η)) (by rw [htE, hψ, deriv_algebraMap, ht])
    (fun i ↦ ψ (algebraMap F₀ K (A.coeff i))) (fun i ↦ (p i : E)) d
    (fun i hi _ ↦ hrecE i hi) htopE
  have hA : ψ (aeval t A) = ∑ i ∈ Finset.range (d + 1), ψ (algebraMap F₀ K (A.coeff i)) * tE ^ i := by
    rw [aeval_eq_sum_range' (n := d + 1) (by omega), map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, map_mul, map_pow]
  rw [map_sub, hsum, hg, hA]
  ring

end Lift

section Log

variable {F₀ K : Type*} [Field F₀] [Field K] [Algebra F₀ K] [Differential F₀] [Differential K]

/-- **A logarithm generates an elementary extension.** -/
lemma isElementaryExtension_log' (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (u : K) (hu : u ∈ Set.range (algebraMap F₀ K)) (hu0 : u ≠ 0) (ht : t′ = logDeriv u) :
    IsElementaryExtension F₀ K := by
  have h := IsElementaryTower.adjoin (⊥ : IntermediateField F₀ K) t IsElementaryTower.base
    (Or.inr (Or.inl ⟨u, by obtain ⟨f, rfl⟩ := hu; exact IntermediateField.algebraMap_mem _ f,
      hu0, ht⟩))
  unfold IsElementaryExtension
  rwa [hgen, bot_sup_eq] at h

end Log

end Curves
