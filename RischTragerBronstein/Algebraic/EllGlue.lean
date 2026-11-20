import RischTragerBronstein.Algebraic.HypGlue
import RischTragerBronstein.Algebraic.EllResidue

/-!
# Hyperelliptic integrals with rational residues: from a Liouville form to residue data

`ell_glue`: if `(B(x) + ∑ rᵢ βᵢ / (x − αᵢ)) / y = v′ + ∑ cₖ uₖ′ / uₖ` in `L ⊇ C(x)(y)`, then there
are `ℚ`-independent constants `κⱼ` and coprime `aⱼ, bⱼ ∈ C[x]` with the residue data of
`ell_core`: `2 rᵢ = −∑ⱼ κⱼ mᵢⱼ εᵢⱼ`, and the norms `aⱼ² − bⱼ² p` have no zeros besides the `αᵢ` and
simple roots of `p`.
-/

open Polynomial IntermediateField

namespace Differential

section Glue

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

variable (x y : L)

set_option maxHeartbeats 3200000 in
/-- **The residue data of a Liouville form** for `f = G / y`,
`G = B(x) + ∑ rᵢ βᵢ / (x − αᵢ)`: after reduction to `ℚ`-independent constants `κⱼ` and normalised
`uⱼ = λⱼ (aⱼ + bⱼ y)`, the conclusions of `ell_core` hold. -/
theorem ell_glue (hC : ∀ c : C, c′ = 0) (hx : x′ = 1) (htr : Transcendental C x)
    (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (p : C[X]) (hp : Squarefree p) (hodd : Odd p.natDegree) (hy : y ^ 2 = aeval x p)
    (Bp : C[X]) {ιP : Type*} (sP : Finset ιP) (αP βP rP : ιP → C) (hinjP : Set.InjOn αP sP)
    (hβP : ∀ i ∈ sP, βP i ≠ 0) (hpαP : ∀ i ∈ sP, p.eval (αP i) = βP i ^ 2)
    {ι : Type*} (s : Finset ι) (c u : ι → L) (v : L)
    (hc : ∀ i ∈ s, (c i)′ = 0) (hu : ∀ i ∈ s, u i ≠ 0 ∧ InHyp C x y (u i))
    (hv : InHyp C x y v)
    (heq : (aeval x Bp + ∑ i ∈ sP, algebraMap C L (rP i * βP i) / (x - algebraMap C L (αP i))) / y =
      v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ (t : Finset ℕ) (κ : ℕ → C) (a b : ℕ → C[X]),
      (∀ g : ℕ → ℚ, ∑ j ∈ t, (g j : C) * κ j = 0 → ∀ j ∈ t, g j = 0) ∧
      (∀ j ∈ t, IsCoprime (a j) (b j)) ∧ (∀ j ∈ t, hN p (a j) (b j) ≠ 0) ∧
      (∀ j ∈ t, ∀ q : C[X], Irreducible q → q ∣ hN p (a j) (b j) →
        (∃ i ∈ sP, q ∣ X - Polynomial.C (αP i)) ∨ (q ∣ p ∧ ¬q ^ 2 ∣ hN p (a j) (b j))) ∧
      ∀ i ∈ sP, ∃ (m : ℕ → ℕ) (ε : ℕ → ℤ), (∀ j ∈ t, (ε j = 1 ∨ ε j = -1) ∧
        (X - Polynomial.C (αP i)) ^ m j ∣ hN p (a j) (b j) ∧
        ¬(X - Polynomial.C (αP i)) ^ (m j + 1) ∣ hN p (a j) (b j) ∧
        (0 < m j → (a j).eval (αP i) = ε j * βP i * (b j).eval (αP i))) ∧
        2 * rP i = -∑ j ∈ t, κ j * ((m j : C) * ε j) := by
  classical
  set Gv := aeval x Bp + ∑ i ∈ sP, algebraMap C L (rP i * βP i) / (x - algebraMap C L (αP i))
    with hGv
  have hGmem : Gv ∈ C⟮x⟯ := by
    refine add_mem (aeval_mem_adj x Bp) (sum_mem fun i _ ↦ div_mem
      (IntermediateField.algebraMap_mem _ _) ?_)
    have : x - algebraMap C L (αP i) = aeval x (X - Polynomial.C (αP i)) := by simp
    rw [this]; exact aeval_mem_adj x _
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
  have hsplit : 0 + Gv / (aeval x p) * y = (α′ + ∑ j ∈ Finset.range k, d j * Xc j) +
      ((e′ + e * r) + ∑ j ∈ Finset.range k, d j * Y j) * y := by
    have lhs : Gv / (aeval x p) * y = Gv / y := by
      rw [← hy]; field_simp
    rw [zero_add, lhs, heq, map_add, Derivation.leibniz, hyd, hS]
    simp only [smul_eq_mul]
    ring
  have hycomp := ycomp_unique x y hny (zero_mem _) (div_mem hGmem (hmem _))
    (add_mem (hDC _ hα) (Subring.sum_mem _ fun j hj ↦
      mul_mem (hdmem j (Finset.mem_range.mp hj)) (hXmem j (Finset.mem_range.mp hj))))
    (add_mem (add_mem (hDC _ he) (mul_mem he hrmem)) (Subring.sum_mem _ fun j hj ↦
      mul_mem (hdmem j (Finset.mem_range.mp hj)) (hYmem j))) hsplit
  -- the identity in `L`
  have hL : 2 * Gv = aeval x (2 * p) * e′ + aeval x (derivative p) * e +
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
    have key : ∑ j ∈ Finset.range k, d j * Y j = Gv / (aeval x p) - (e′ + e * r) := by
      rw [hycomp]; ring
    rw [key, hr, map_mul, map_ofNat]
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
  have hκind : ∀ g : ℕ → ℚ, ∑ j ∈ Finset.range k, (g j : C) * κ j = 0 →
      ∀ j ∈ Finset.range k, g j = 0 := fun g hg j hj ↦ hind g (by
    have := congrArg (algebraMap C L) hg
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [map_mul, map_ratCast, hκ j (Finset.mem_range.mp hj)]) j (Finset.mem_range.mp hj)
  have hab' : ∀ j ∈ Finset.range k, IsCoprime (a j) (b j) := fun j hj ↦
    hab j (Finset.mem_range.mp hj)
  have hN0' : ∀ j ∈ Finset.range k, hN p (a j) (b j) ≠ 0 := fun j hj ↦
    hN0 j (Finset.mem_range.mp hj)
  have hidK : algebraMap C[X] C⟮x⟯ (2 * Bp) + ∑ i ∈ sP,
      algebraMap C[X] C⟮x⟯ (Polynomial.C (2 * rP i * βP i)) /
        algebraMap C[X] C⟮x⟯ (X - Polynomial.C (αP i)) =
      algebraMap C[X] C⟮x⟯ (2 * p) * (⟨e, he⟩ : C⟮x⟯)′ +
        algebraMap C[X] C⟮x⟯ (derivative p) * ⟨e, he⟩ +
        ∑ j ∈ Finset.range k, algebraMap C[X] C⟮x⟯ (Polynomial.C (κ j)) *
          (algebraMap C[X] C⟮x⟯ (hM p (a j) (b j)) / algebraMap C[X] C⟮x⟯ (hN p (a j) (b j))) := by
    apply Subtype.ext
    rw [IntermediateField.coe_add, IntermediateField.coe_add, IntermediateField.coe_add,
      IntermediateField.coe_mul, IntermediateField.coe_mul, coe_deriv_of_derivClosed,
      AddSubmonoidClass.coe_finset_sum, AddSubmonoidClass.coe_finset_sum, hcoe, hcoe, hcoe]
    have hl : aeval x (2 * Bp) + ∑ i ∈ sP, ((algebraMap C[X] C⟮x⟯ (Polynomial.C (2 * rP i * βP i)) /
        algebraMap C[X] C⟮x⟯ (X - Polynomial.C (αP i)) : C⟮x⟯) : L) = 2 * Gv := by
      rw [hGv, mul_add, Finset.mul_sum]
      congr 1
      · rw [map_mul, map_ofNat]
      · refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [IntermediateField.coe_div, hcoe, hcoe]
        simp only [aeval_C, map_mul, map_ofNat, aeval_sub, aeval_X]
        ring
    rw [hl, hL]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_div, hcoe, hcoe, hcoe, aeval_C]
  obtain ⟨h1, h2⟩ := ell_core (K := C⟮x⟯) hder p hp Bp sP αP βP rP hinjP hβP hpαP ⟨e, he⟩
    (Finset.range k) κ hκind a b hab' hN0' hidK
  exact ⟨Finset.range k, κ, a, b, hκind, hab', hN0', h1, h2⟩

end Glue

end Differential
