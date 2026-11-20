import RischTragerBronstein.Algebraic.HypCore
import RischTragerBronstein.Algebraic.QIndep
import RischTragerBronstein.Liouville.SimpleTranscendental

/-!
# Hyperelliptic integrals without logarithmic part: from a Liouville identity to `hyp_core`

In a differential field `L ⊇ C(x)(y)` (`x′ = 1`, `x` transcendental over the constants `C`,
`y² = p(x)`, `p` squarefree of odd degree), every element of `C(x)(y)` is `α + β y` with
`α, β ∈ C(x)` uniquely (`y ∉ C(x)`). `hyp_glue`: an identity
`B₀(x) / y = v′ + ∑ cᵢ uᵢ′ / uᵢ` with `v, uᵢ ∈ C(x)(y)` and constant `cᵢ` forces `B₀ = 0` when
`deg B₀ ≤ deg p - 2`: after making the `cᵢ` `ℚ`-independent (`logSum_qindep`) and normalising
`uᵢ = λᵢ (aᵢ + bᵢ y)` (`aᵢ, bᵢ ∈ C[x]` coprime, `λᵢ ∈ C(x)`), the `y`-components give the identity
of `hyp_core`.
-/

open Polynomial IntermediateField

namespace Differential

section Glue

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

/-- `z = α + β y` with `α, β ∈ C(x)`. -/
def InHyp (C : Type*) [Field C] [Algebra C L] (x y z : L) : Prop :=
  ∃ α β : L, α ∈ C⟮x⟯ ∧ β ∈ C⟮x⟯ ∧ z = α + β * y

variable (x y : L)

omit [Differential C] [Differential L] [DifferentialAlgebra C L] in
/-- `y ∉ C(x)` when `y² = p(x)` with `p` of odd degree and `x` transcendental. -/
lemma not_mem_of_sq_odd (htr : Transcendental C x) (p : C[X]) (hodd : Odd p.natDegree)
    (hy : y ^ 2 = aeval x p) : y ∉ C⟮x⟯ := by
  intro hmem
  letI := algebraAdjoinSimple (F := C) x
  haveI := isFractionRing_adjoin_simple x htr
  have hcoe : ∀ P : C[X], ((algebraMap C[X] C⟮x⟯ P : C⟮x⟯) : L) = aeval x P :=
    algebraMap_adjoinSimple x
  have hinj : Function.Injective (algebraMap C[X] C⟮x⟯) := IsFractionRing.injective _ _
  obtain ⟨P, Q, hQ, hPQ⟩ := IsFractionRing.div_surjective (A := C[X]) (⟨y, hmem⟩ : C⟮x⟯)
  have hQ0 : Q ≠ 0 := nonZeroDivisors.ne_zero hQ
  have hφQ : algebraMap C[X] C⟮x⟯ Q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hQ0
  have h2 : algebraMap C[X] C⟮x⟯ (P ^ 2) = algebraMap C[X] C⟮x⟯ (p * Q ^ 2) := by
    apply Subtype.ext
    have hyv : y = ((algebraMap C[X] C⟮x⟯ P / algebraMap C[X] C⟮x⟯ Q : C⟮x⟯) : L) := by
      rw [hPQ]
    rw [map_pow, map_mul, map_pow, IntermediateField.coe_pow, IntermediateField.coe_mul,
      IntermediateField.coe_pow, hcoe, hcoe, hcoe, ← hy]
    rw [hyv, IntermediateField.coe_div, hcoe, hcoe]
    have : aeval x Q ≠ 0 := by rw [← hcoe]; exact fun h0 ↦ hφQ (Subtype.ext h0)
    field_simp
  have h3 := hinj h2
  have hp0 : p ≠ 0 := by rintro rfl; simp at hodd
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at h3
    exact mul_ne_zero hp0 (pow_ne_zero _ hQ0) h3.symm
  have := congrArg natDegree h3
  rw [natDegree_pow, natDegree_mul hp0 (pow_ne_zero _ hQ0), natDegree_pow] at this
  obtain ⟨k, hk⟩ := hodd
  omega

omit [Differential C] [Differential L] [DifferentialAlgebra C L] in
/-- **The field `C(x)(y)`**, as the elements `α + β y`. -/
noncomputable def hypField (htr : Transcendental C x) (p : C[X]) (hodd : Odd p.natDegree)
    (hy : y ^ 2 = aeval x p) : Subfield L where
  carrier := {z | InHyp C x y z}
  zero_mem' := ⟨0, 0, zero_mem _, zero_mem _, by simp⟩
  one_mem' := ⟨1, 0, one_mem _, zero_mem _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨α, β, hα, hβ, rfl⟩ ⟨γ, δ, hγ, hδ, rfl⟩
    exact ⟨α + γ, β + δ, add_mem hα hγ, add_mem hβ hδ, by ring⟩
  neg_mem' := by
    rintro _ ⟨α, β, hα, hβ, rfl⟩
    exact ⟨-α, -β, neg_mem hα, neg_mem hβ, by ring⟩
  mul_mem' := by
    rintro _ _ ⟨α, β, hα, hβ, rfl⟩ ⟨γ, δ, hγ, hδ, rfl⟩
    have hp : aeval x p ∈ C⟮x⟯ := by
      rw [← algebraMap_adjoinSimple (F := C) x p]; exact SetLike.coe_mem _
    refine ⟨α * γ + β * δ * aeval x p, α * δ + β * γ,
      add_mem (mul_mem hα hγ) (mul_mem (mul_mem hβ hδ) hp),
      add_mem (mul_mem hα hδ) (mul_mem hβ hγ), ?_⟩
    rw [← hy]; ring
  inv_mem' := by
    rintro _ ⟨α, β, hα, hβ, rfl⟩
    have hp : aeval x p ∈ C⟮x⟯ := by
      rw [← algebraMap_adjoinSimple (F := C) x p]; exact SetLike.coe_mem _
    have hny := not_mem_of_sq_odd x y htr p hodd hy
    set N := α ^ 2 - β ^ 2 * aeval x p with hN
    by_cases hN0 : N = 0
    · -- then `β = 0` and `α = 0`
      have hβ0 : β = 0 := by
        by_contra hβ0
        apply hny
        have hsq : (α / β) ^ 2 = y ^ 2 := by
          rw [hy, div_pow]; field_simp; linear_combination hN0
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
        · rw [← h]; exact div_mem hα hβ
        · rw [show y = -(α / β) by rw [h]; ring]; exact neg_mem (div_mem hα hβ)
      have hα0 : α = 0 := by
        rw [hN, hβ0] at hN0
        simpa using hN0
      exact ⟨0, 0, zero_mem _, zero_mem _, by simp [hα0, hβ0]⟩
    · refine ⟨α / N, -β / N, div_mem hα (sub_mem (pow_mem hα 2) (mul_mem (pow_mem hβ 2) hp)),
        div_mem (neg_mem hβ) (sub_mem (pow_mem hα 2) (mul_mem (pow_mem hβ 2) hp)), ?_⟩
      have hne : α + β * y ≠ 0 := by
        intro h0
        apply hN0
        rw [hN, ← hy, show α = -β * y by linear_combination h0]
        ring
      field_simp
      rw [hN, ← hy]
      ring

omit [CharZero C] [CharZero L] [Differential C] [Differential L] [DifferentialAlgebra C L] in
lemma aeval_mem_adj (P : C[X]) : aeval x P ∈ C⟮x⟯ := by
  rw [← algebraMap_adjoinSimple (F := C) x P]; exact SetLike.coe_mem _

omit [CharZero C] [CharZero L] [Differential C] [Differential L] [DifferentialAlgebra C L] in
lemma aeval_ne_zero_of_tr (htr : Transcendental C x) {P : C[X]} (hP : P ≠ 0) : aeval x P ≠ 0 :=
  fun h ↦ htr ⟨P, hP, h⟩

omit [CharZero C] [CharZero L] in
lemma deriv_aeval_x (hC : ∀ c : C, c′ = 0) (hx : x′ = 1) (P : C[X]) :
    (aeval x P)′ = aeval x (derivative P) := by
  rw [deriv_aeval_eq_implicitDeriv x 1 (by rw [hx, map_one]) P, implicitDeriv_one_of_trivial hC]

omit [CharZero C] [Algebra C L] [Differential C] [DifferentialAlgebra C L] in
/-- The logarithmic derivative of `a + b y` (`y² = P`, `y′ = r y`), split into components. -/
lemma logDeriv_ab (a b P r : L) (hy : y ^ 2 = P) (hyd : y′ = r * y)
    (hN : a ^ 2 - b ^ 2 * P ≠ 0) :
    logDeriv (a + b * y) = (a * a′ - b * (b′ + b * r) * P) / (a ^ 2 - b ^ 2 * P) +
      ((a * (b′ + b * r) - a′ * b) / (a ^ 2 - b ^ 2 * P)) * y := by
  have hne : a + b * y ≠ 0 := by
    intro h0; apply hN
    rw [← hy, show a = -(b * y) by linear_combination h0]; ring
  unfold logDeriv
  rw [div_eq_iff hne, map_add, Derivation.leibniz, hyd]
  simp only [smul_eq_mul]
  field_simp
  linear_combination (a′ * b ^ 2 - a * b * (b′ + b * r)) * hy

omit [CharZero C] [CharZero L] [Differential C] [Differential L] [DifferentialAlgebra C L] in
/-- Uniqueness of the `y`-component. -/
lemma ycomp_unique (hny : y ∉ C⟮x⟯) {α β α' β' : L} (hα : α ∈ C⟮x⟯) (hβ : β ∈ C⟮x⟯)
    (hα' : α' ∈ C⟮x⟯) (hβ' : β' ∈ C⟮x⟯) (h : α + β * y = α' + β' * y) : β = β' := by
  by_contra hne
  apply hny
  have : y = (α' - α) / (β - β') := by
    rw [eq_div_iff (sub_ne_zero.mpr hne)]; linear_combination h
  rw [this]
  exact div_mem (sub_mem hα' hα) (sub_mem hβ hβ')

omit [Differential C] [Differential L] [DifferentialAlgebra C L] in
/-- **Normalisation**: `α + β y = λ (a + b y)` with `a, b ∈ C[x]` coprime and `a² - b² p ≠ 0`. -/
lemma hyp_normalize (htr : Transcendental C x) (p : C[X]) (hodd : Odd p.natDegree)
    (hy : y ^ 2 = aeval x p) {α β : L} (hα : α ∈ C⟮x⟯) (hβ : β ∈ C⟮x⟯) (h0 : α + β * y ≠ 0) :
    ∃ (lam : L) (a b : C[X]), lam ∈ C⟮x⟯ ∧ lam ≠ 0 ∧ IsCoprime a b ∧
      a ^ 2 - b ^ 2 * p ≠ 0 ∧ α + β * y = lam * (aeval x a + aeval x b * y) := by
  classical
  letI := algebraAdjoinSimple (F := C) x
  haveI := isFractionRing_adjoin_simple x htr
  have hcoe : ∀ P : C[X], ((algebraMap C[X] C⟮x⟯ P : C⟮x⟯) : L) = aeval x P :=
    algebraMap_adjoinSimple x
  have hny := not_mem_of_sq_odd x y htr p hodd hy
  obtain ⟨A1, D1, hD1, hαe⟩ := IsFractionRing.div_surjective (A := C[X]) (⟨α, hα⟩ : C⟮x⟯)
  obtain ⟨B1, D2, hD2, hβe⟩ := IsFractionRing.div_surjective (A := C[X]) (⟨β, hβ⟩ : C⟮x⟯)
  have hD10 : D1 ≠ 0 := nonZeroDivisors.ne_zero hD1
  have hD20 : D2 ≠ 0 := nonZeroDivisors.ne_zero hD2
  have hαv : α = aeval x A1 / aeval x D1 := by
    have := congrArg Subtype.val hαe
    rw [IntermediateField.coe_div, hcoe, hcoe] at this; exact this.symm
  have hβv : β = aeval x B1 / aeval x D2 := by
    have := congrArg Subtype.val hβe
    rw [IntermediateField.coe_div, hcoe, hcoe] at this; exact this.symm
  have hx1 := aeval_ne_zero_of_tr x htr hD10
  have hx2 := aeval_ne_zero_of_tr x htr hD20
  set A := A1 * D2
  set B := B1 * D1
  have hsum : α + β * y = (aeval x A + aeval x B * y) / aeval x (D1 * D2) := by
    rw [hαv, hβv]; simp only [A, B, map_mul]; field_simp
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_contra h; push_neg at h
    apply h0; rw [hsum, h.1, h.2]; simp
  set g := gcd A B with hg
  have hg0 : g ≠ 0 := by
    intro h; rw [gcd_eq_zero_iff] at h; tauto
  set a := A / g
  set b := B / g
  have hAa : A = g * a := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left A B)).symm
  have hBb : B = g * b := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right A B)).symm
  have hcop : IsCoprime a b := isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  have hxg := aeval_ne_zero_of_tr x htr hg0
  have hsum' : α + β * y = aeval x g / aeval x (D1 * D2) * (aeval x a + aeval x b * y) := by
    rw [hsum, hAa, hBb, map_mul, map_mul]; ring
  have hab0 : aeval x a + aeval x b * y ≠ 0 := by
    intro h; apply h0; rw [hsum', h, mul_zero]
  refine ⟨aeval x g / aeval x (D1 * D2), a, b, div_mem (aeval_mem_adj x g) (aeval_mem_adj x _),
    div_ne_zero hxg (by rw [map_mul]; exact mul_ne_zero hx1 hx2), hcop, fun hN ↦ ?_, hsum'⟩
  -- `a² = b² p` would put `y` in `C(x)` or make `a + b y = 0`
  have hN' : (aeval x a - aeval x b * y) * (aeval x a + aeval x b * y) = 0 := by
    have := congrArg (aeval x) hN
    simp only [map_sub, map_mul, map_pow, map_zero] at this
    rw [← hy] at this
    linear_combination this
  have hdiff := (mul_eq_zero.mp hN').resolve_right hab0
  by_cases hb : b = 0
  · apply hab0
    have : aeval x a = 0 := by rw [hb, map_zero, zero_mul, sub_zero] at hdiff; exact hdiff
    rw [this, hb, map_zero]; ring
  · apply hny
    have hxb := aeval_ne_zero_of_tr x htr hb
    have : y = aeval x a / aeval x b := by
      rw [eq_div_iff hxb]; linear_combination -hdiff
    rw [this]; exact div_mem (aeval_mem_adj x a) (aeval_mem_adj x b)

set_option maxHeartbeats 1600000 in
/-- **Hyperelliptic integrals without logarithmic part**: in `L ⊇ C(x)(y)`, an identity
`B₀(x) / y = v′ + ∑ cᵢ uᵢ′ / uᵢ` with `v, uᵢ ∈ C(x)(y)`, constant `cᵢ` and
`deg B₀ ≤ deg p - 2` forces `B₀ = 0`. -/
theorem hyp_glue (hC : ∀ c : C, c′ = 0) (hx : x′ = 1) (htr : Transcendental C x)
    (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (p : C[X]) (hp : Squarefree p) (hodd : Odd p.natDegree) (hy : y ^ 2 = aeval x p)
    (B0 : C[X]) (hB : B0 = 0 ∨ B0.natDegree + 2 ≤ p.natDegree)
    {ι : Type*} (s : Finset ι) (c u : ι → L) (v : L)
    (hc : ∀ i ∈ s, (c i)′ = 0) (hu : ∀ i ∈ s, u i ≠ 0 ∧ InHyp C x y (u i))
    (hv : InHyp C x y v)
    (heq : aeval x B0 / y = v′ + ∑ i ∈ s, c i * logDeriv (u i)) : B0 = 0 := by
  classical
  set S := hypField x y htr p hodd hy
  obtain ⟨k, d, w, ⟨hd, hw, hind⟩, hsum⟩ :=
    logSum_qindep S s c u hc (fun i hi ↦ ⟨(hu i hi).1, (hu i hi).2⟩)
  rw [hsum] at heq
  have hκ : ∀ j < k, ∃ κ : C, algebraMap C L κ = d j := fun j hj ↦ hconst _ (hd j hj)
  choose! κ hκ using hκ
  obtain ⟨α, e, hα, he, rfl⟩ := hv
  have hwd : ∀ j < k, ∃ (lam : L) (a b : C[X]), lam ∈ C⟮x⟯ ∧ lam ≠ 0 ∧ IsCoprime a b ∧
      a ^ 2 - b ^ 2 * p ≠ 0 ∧ w j = lam * (aeval x a + aeval x b * y) := by
    intro j hj
    obtain ⟨hw0, α', β', hα', hβ', hwe⟩ := hw j hj
    rw [hwe] at hw0 ⊢
    exact hyp_normalize x y htr p hodd hy hα' hβ' hw0
  choose! lam a b hlam hlam0 hab hN0 hwj using hwd
  -- basic facts
  have hny := not_mem_of_sq_odd x y htr p hodd hy
  have hp0 : p ≠ 0 := hp.ne_zero
  have hP0 : (aeval x p) ≠ 0 := aeval_ne_zero_of_tr x htr hp0
  have hy0 : y ≠ 0 := by rintro rfl; apply hP0; rw [← hy]; ring
  set r := aeval x (derivative p) / (2 * (aeval x p)) with hr
  have hyd : y′ = r * y := by
    have h1 := congrArg (fun z : L ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul] at h1
    rw [deriv_aeval_x x hC hx] at h1
    rw [hr, ← hy]
    field_simp
    linear_combination h1
  have hDC : DerivClosed C⟮x⟯ := derivClosed_adjoin_simple x 1 (by rw [hx, map_one])
  have hmem : ∀ Q : C[X], aeval x Q ∈ C⟮x⟯ := aeval_mem_adj x
  have hrmem : r ∈ C⟮x⟯ := div_mem (hmem _) (mul_mem (by simpa using hmem 2) (hmem p))
  -- the components of each logarithmic derivative
  set Y : ℕ → L := fun j ↦ (aeval x (a j) * ((aeval x (b j))′ + aeval x (b j) * r) -
    (aeval x (a j))′ * aeval x (b j)) / (aeval x (a j) ^ 2 - aeval x (b j) ^ 2 * (aeval x p)) with hY
  set Xc : ℕ → L := fun j ↦ logDeriv (lam j) + (aeval x (a j) * (aeval x (a j))′ -
    aeval x (b j) * ((aeval x (b j))′ + aeval x (b j) * r) * (aeval x p)) /
      (aeval x (a j) ^ 2 - aeval x (b j) ^ 2 * (aeval x p)) with hXc
  have hNx : ∀ j < k, aeval x (a j) ^ 2 - aeval x (b j) ^ 2 * (aeval x p) ≠ 0 := by
    intro j hj
    have := aeval_ne_zero_of_tr x htr (hN0 j hj)
    simpa using this
  have hld : ∀ j < k, logDeriv (w j) = Xc j + Y j * y := by
    intro j hj
    have hab0 : aeval x (a j) + aeval x (b j) * y ≠ 0 := by
      intro h0; apply (hw j hj).1; rw [hwj j hj, h0, mul_zero]
    rw [hwj j hj, logDeriv_mul _ _ (hlam0 j hj) hab0,
      logDeriv_ab y _ _ _ r hy hyd (hNx j hj)]
    simp only [hXc, hY]
    ring
  have hmemD : ∀ Q : C[X], (aeval x Q)′ ∈ C⟮x⟯ := fun Q ↦ hDC _ (hmem Q)
  have hYmem : ∀ j, Y j ∈ C⟮x⟯ := fun j ↦ div_mem (sub_mem (mul_mem (hmem _) (add_mem
    (hmemD _) (mul_mem (hmem _) hrmem))) (mul_mem (hmemD _) (hmem _)))
    (sub_mem (pow_mem (hmem _) 2) (mul_mem (pow_mem (hmem _) 2) (hmem _)))
  have hXmem : ∀ j < k, Xc j ∈ C⟮x⟯ := fun j hj ↦ add_mem (div_mem (hDC _ (hlam j hj)) (hlam j hj))
    (div_mem (sub_mem (mul_mem (hmem _) (hmemD _)) (mul_mem (mul_mem (hmem _) (add_mem
      (hmemD _) (mul_mem (hmem _) hrmem))) (hmem _)))
      (sub_mem (pow_mem (hmem _) 2) (mul_mem (pow_mem (hmem _) 2) (hmem _))))
  have hdmem : ∀ j < k, d j ∈ C⟮x⟯ := fun j hj ↦ hκ j hj ▸ IntermediateField.algebraMap_mem _ _
  -- compare the `y`-components
  have hS : ∑ j ∈ Finset.range k, d j * logDeriv (w j) = ∑ j ∈ Finset.range k, d j * Xc j +
      (∑ j ∈ Finset.range k, d j * Y j) * y := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj ↦ by rw [hld j (Finset.mem_range.mp hj)]; ring
  have hsplit : 0 + aeval x B0 / (aeval x p) * y = (α′ + ∑ j ∈ Finset.range k, d j * Xc j) +
      ((e′ + e * r) + ∑ j ∈ Finset.range k, d j * Y j) * y := by
    have lhs : aeval x B0 / (aeval x p) * y = aeval x B0 / y := by
      rw [← hy]; field_simp
    rw [zero_add, lhs, heq, map_add, Derivation.leibniz, hyd, hS]
    simp only [smul_eq_mul]
    ring
  have hycomp := ycomp_unique x y hny (zero_mem _) (div_mem (hmem _) (hmem _))
    (add_mem (hDC _ hα) (Subring.sum_mem _ fun j hj ↦
      mul_mem (hdmem j (Finset.mem_range.mp hj)) (hXmem j (Finset.mem_range.mp hj))))
    (add_mem (add_mem (hDC _ he) (mul_mem he hrmem)) (Subring.sum_mem _ fun j hj ↦
      mul_mem (hdmem j (Finset.mem_range.mp hj)) (hYmem j))) hsplit
  -- the identity in `L`
  have hL : aeval x (2 * B0) = aeval x (2 * p) * e′ + aeval x (derivative p) * e +
      ∑ j ∈ Finset.range k, algebraMap C L (κ j) *
        (aeval x (hM p (a j) (b j)) / aeval x (hN p (a j) (b j))) := by
    have e1 : ∀ j ∈ Finset.range k, algebraMap C L (κ j) *
        (aeval x (hM p (a j) (b j)) / aeval x (hN p (a j) (b j))) = 2 * (aeval x p) * (d j * Y j) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [hκ j hj', hY]
      simp only [hM, hN, map_add, map_sub, map_mul, map_pow, map_ofNat]
      rw [deriv_aeval_x x hC hx, deriv_aeval_x x hC hx]
      have := hNx j hj'
      rw [hr]
      field_simp
      ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    have key : ∑ j ∈ Finset.range k, d j * Y j = aeval x B0 / (aeval x p) - (e′ + e * r) := by
      rw [hycomp]; ring
    rw [key, hr, map_mul, map_mul, map_ofNat]
    field_simp
    ring
  -- transport to `K = C(x)` and apply the core theorem
  letI := algebraAdjoinSimple (F := C) x
  haveI := isFractionRing_adjoin_simple x htr
  letI : Differential C[X] := polynomialOfDeriv 1
  letI : Differential C⟮x⟯ := differentialOfDerivClosed hDC
  haveI : DifferentialAlgebra C[X] C⟮x⟯ := differentialAlgebra_adjoin_simple x 1 (by rw [hx, map_one])
  have hcoe : ∀ Q : C[X], ((algebraMap C[X] C⟮x⟯ Q : C⟮x⟯) : L) = aeval x Q :=
    algebraMap_adjoinSimple x
  have hder : ∀ Q : C[X], Q′ = derivative Q := fun Q ↦ implicitDeriv_one_of_trivial hC Q
  refine hyp_core (K := C⟮x⟯) hder p hp hodd B0 hB ⟨e, he⟩ (Finset.range k) κ
    (fun g hg j hj ↦ hind g (by
      have := congrArg (algebraMap C L) hg
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [map_mul, map_ratCast, hκ j (Finset.mem_range.mp hj)]) j (Finset.mem_range.mp hj))
    a b (fun j hj ↦ hab j (Finset.mem_range.mp hj)) (fun j hj ↦ hN0 j (Finset.mem_range.mp hj)) ?_
  apply Subtype.ext
  rw [IntermediateField.coe_add, IntermediateField.coe_add, IntermediateField.coe_mul,
    IntermediateField.coe_mul, coe_deriv_of_derivClosed, AddSubmonoidClass.coe_finset_sum,
    hcoe, hcoe, hcoe, hL]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [IntermediateField.coe_mul, IntermediateField.coe_div, hcoe, hcoe, hcoe, aeval_C]

end Glue

end Differential
