import RischTragerBronstein.Algebraic.SuperExp
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum

/-!
# Integrality on a superelliptic curve

* `conj_sum`: `σ_ζ(∑ aₖ yᵏ) = ∑ aₖ ζᵏ yᵏ`;
* `fourier`: `∑ⱼ ζ^{(n−i)j} σ_{ζʲ}(w) = n aᵢ yⁱ` for a primitive `n`-th root of unity `ζ`;
* `integral_of_regular`: if `w` has non-negative order at every non-branch point and at every
  branch point (over an algebraically closed `K ⊇ C`), then `w = ∑ Pᵢ(x) yⁱ` with polynomials `Pᵢ`.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K]

variable (S : SuperData C L)

/-- The constant `c` as an element of `C⟮x⟯⟮y⟯`. -/
def cst (c : C) : C⟮S.x⟯⟮S.y⟯ := ⟨algebraMap C L c, S.const_mem c⟩

lemma cst_eq (c : C) : S.cst c = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯
    ⟨algebraMap C L c, IntermediateField.algebraMap_mem _ c⟩ := rfl

lemma conj_cst (ζ : C) (hζ : ζ ^ S.n = 1) (c : C) : S.conj ζ hζ (S.cst c) = S.cst c := by
  rw [cst_eq, conj_algebraMap]

lemma cst_mul (c d : C) : S.cst (c * d) = S.cst c * S.cst d := Subtype.ext (by simp [cst])
lemma cst_pow (c : C) (k : ℕ) : S.cst (c ^ k) = S.cst c ^ k := Subtype.ext (by simp [cst])
lemma cst_natCast (k : ℕ) : S.cst (k : C) = (k : C⟮S.x⟯⟮S.y⟯) := Subtype.ext (by simp [cst])

/-- `σ_ζ(∑ aₖ yᵏ) = ∑ aₖ ζᵏ yᵏ`. -/
lemma conj_sum (ζ : C) (hζ : ζ ^ S.n = 1) (a : Fin S.n → C⟮S.x⟯) :
    S.conj ζ hζ (∑ k : Fin S.n, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a k) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (k : ℕ)) =
      ∑ k : Fin S.n, S.cst (ζ ^ (k : ℕ)) * (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a k) *
        AdjoinSimple.gen C⟮S.x⟯ S.y ^ (k : ℕ)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, map_pow, S.conj_algebraMap, S.conj_gen, mul_pow, S.cst_pow,
    show S.cst ζ = ⟨algebraMap C L ζ, S.const_mem ζ⟩ from rfl]
  ring

lemma cst_sum {ι : Type*} (t : Finset ι) (c : ι → C) :
    S.cst (∑ j ∈ t, c j) = ∑ j ∈ t, S.cst (c j) := Subtype.ext (by simp [cst])

/-- The orthogonality of roots of unity. -/
lemma root_sum (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) (i k : Fin S.n) :
    ∑ j : Fin S.n, (ζ ^ (j : ℕ)) ^ (S.n - i) * (ζ ^ (j : ℕ)) ^ (k : ℕ) =
      if k = i then (S.n : C) else 0 := by
  have e : ∀ j : Fin S.n, (ζ ^ (j : ℕ)) ^ (S.n - i) * (ζ ^ (j : ℕ)) ^ (k : ℕ) =
      (ζ ^ (S.n - i + k)) ^ (j : ℕ) := fun j ↦ by
    rw [← pow_add, ← pow_mul, ← pow_mul, mul_comm]
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ (ζ ^ (S.n - i + k)) ^ j)]
  split_ifs with hki
  · rw [hki, Nat.sub_add_cancel i.2.le, hζ.pow_eq_one]
    simp
  · have hne : ζ ^ (S.n - i + k) ≠ 1 := by
      intro h1
      obtain ⟨c, hc⟩ := hζ.dvd_of_pow_eq_one _ h1
      have hi := i.2
      have hk := k.2
      have hik : (i : ℕ) ≠ k := fun h ↦ hki (Fin.ext h.symm)
      rcases c with _ | _ | c
      · omega
      · omega
      · have h2 : 2 * S.n ≤ S.n * (c + 1 + 1) := by nlinarith
        omega
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

/-- **Fourier inversion** over the conjugates. -/
theorem fourier (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) (a : Fin S.n → C⟮S.x⟯) (i : Fin S.n) :
    ∑ j : Fin S.n, S.cst ((ζ ^ (j : ℕ)) ^ (S.n - i)) *
      S.conj (ζ ^ (j : ℕ)) (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
        (∑ k : Fin S.n, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a k) *
          AdjoinSimple.gen C⟮S.x⟯ S.y ^ (k : ℕ)) =
      (S.n : C⟮S.x⟯⟮S.y⟯) * (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
        AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) := by
  simp_rw [S.conj_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  set Y : Fin S.n → C⟮S.x⟯⟮S.y⟯ := fun k ↦
    algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a k) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (k : ℕ)
  have key : ∀ k : Fin S.n, ∑ j : Fin S.n, S.cst ((ζ ^ (j : ℕ)) ^ (S.n - i)) *
      (S.cst ((ζ ^ (j : ℕ)) ^ (k : ℕ)) * Y k) =
      S.cst (if k = i then (S.n : C) else 0) * Y k := by
    intro k
    rw [← S.root_sum ζ hζ i k, S.cst_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [S.cst_mul, mul_assoc]
  refine (Finset.sum_congr rfl fun k _ ↦ key k).trans ?_
  rw [Finset.sum_eq_single i (fun k _ hki ↦ by
      rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hki), show S.cst 0 = 0 from Subtype.ext (by simp [cst]), zero_mul])
    (fun h ↦ absurd (Finset.mem_univ i) h), ite_eq_left_iff.mpr (fun h ↦ absurd rfl h), S.cst_natCast]


lemma orderTop_C_mul_nonneg (c : K) (f : LaurentSeries K) (hf : 0 ≤ f.orderTop) :
    0 ≤ (HahnSeries.C c * f).orderTop := by
  refine le_trans ?_ HahnSeries.orderTop_add_le_mul
  rw [HahnSeries.C_apply]
  exact add_nonneg HahnSeries.orderTop_single_le hf

lemma embXY_cst (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (c : C) : S.embXY α β hβ hβp (S.cst c) = HahnSeries.C (algebraMap C K c) :=
  S.embXY_const α β hβ hβp c

lemma root_ne_zero (ζ : C) (hζ : ζ ^ S.n = 1) : algebraMap C K ζ ≠ 0 := fun h ↦ by
  have : (algebraMap C K ζ) ^ S.n = 1 := by rw [← map_pow, hζ, map_one]
  rw [h, zero_pow S.hn.ne'] at this; exact zero_ne_one this

/-- **Regularity at a non-branch point**: if every branch of `∑ aᵢ yⁱ` above `α` has
non-negative order, every `aᵢ` is regular at `α`. -/
theorem nonbranch_regular (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) (a : Fin S.n → C⟮S.x⟯)
    (h : ∀ (β' : K) (hβ' : β' ≠ 0) (hβp' : β' ^ S.n = (S.p.map (algebraMap C K)).eval α),
      0 ≤ (S.embXY α β' hβ' hβp' (∑ k, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a k) *
        AdjoinSimple.gen C⟮S.x⟯ S.y ^ (k : ℕ))).orderTop) :
    ∀ i, a i ≠ 0 → 0 ≤ (embX S.x S.htr α (a i)).order := by
  intro i hi
  set W := ∑ k, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a k) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (k : ℕ)
  have hF := congrArg (S.embXY α β hβ hβp) (S.fourier ζ hζ a i)
  have hL : 0 ≤ (S.embXY α β hβ hβp (∑ j : Fin S.n, S.cst ((ζ ^ (j : ℕ)) ^ (S.n - i)) *
      S.conj (ζ ^ (j : ℕ)) (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) W)).orderTop := by
    rw [map_sum]
    refine LaurentSeries.le_orderTop_sum _ _ _ fun j _ ↦ ?_
    rw [map_mul, S.embXY_cst, ← RingHom.comp_apply (S.embXY α β hβ hβp), S.embXY_conj]
    exact orderTop_C_mul_nonneg _ _ (h _ _ _)
  rw [hF, map_mul, map_mul, map_pow, map_natCast, S.embXY_algebraMap, S.embXY_gen] at hL
  have hE : embX S.x S.htr α (a i) ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hi
  have hB : branchY S.n S.hn (S.hnK K) S.p α β hβ hβp ≠ 0 := fun h0 ↦ hβ (by
    rw [← branchY_const S.n S.hn (S.hnK K) S.p α β hβ hβp, h0, map_zero])
  have hY : ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p α β hβ hβp) ≠ 0 := fun h0 ↦
    hB (HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm))
  have hN : ((S.n : ℕ) : LaurentSeries K) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := K))]
    exact fun h0 ↦ (S.hnK K)
      (HahnSeries.C_injective (h0.trans (map_zero _).symm))
  have hP := mul_ne_zero hN (mul_ne_zero hE (pow_ne_zero (i : ℕ) hY))
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hP, HahnSeries.order_mul hN (mul_ne_zero hE
    (pow_ne_zero _ hY)), HahnSeries.order_mul hE (pow_ne_zero _ hY), HahnSeries.order_pow,
    order_ofPS_unit _ (by rw [branchY_const]; exact hβ),
    ← map_natCast (HahnSeries.C (Γ := ℤ) (R := K)), HahnSeries.order_C] at hL
  simpa using hL

/-- **Integrality from regularity**: over an algebraically closed `K ⊇ C` (and with a primitive
`n`-th root of unity in `C`), an element of `C⟮x⟯⟮y⟯` without poles at the finite places is
`∑ Pᵢ(x) yⁱ` with polynomials `Pᵢ`. -/
theorem integral_of_regular [IsAlgClosed K] (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)
    (w : C⟮S.x⟯⟮S.y⟯)
    (hreg : ∀ (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α),
      0 ≤ (S.embXY α β hβ hβp w).orderTop)
    (hbr : ∀ (e γ : K) (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
      (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e),
      0 ≤ (S.embB e γ he hγ hγp w).orderTop) :
    ∃ a : Fin S.n → C⟮S.x⟯, w = ∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ) ∧ ∀ i, ∃ P : C[X], (a i : L) = aeval S.x P := by
  obtain ⟨a, ha⟩ := S.power_repr w
  refine ⟨a, ha, fun i ↦ exists_poly_of_regular (K := K) S.x S.htr (a i) fun α hi ↦ ?_⟩
  subst ha
  by_cases hα : (S.p.map (algebraMap C K)).eval α = 0
  · have hsep : S.p.Separable := PerfectField.separable_iff_squarefree.mpr S.hsq
    have hd : (Polynomial.derivative (S.p.map (algebraMap C K))).eval α ≠ 0 := by
      rw [derivative_map, eval_map_algebraMap]
      exact hsep.aeval_derivative_ne_zero (by rwa [← eval_map_algebraMap])
    obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq
      ((Polynomial.derivative (S.p.map (algebraMap C K))).eval α) S.hn
    have hγ0 : γ ≠ 0 := fun h0 ↦ hd (by rw [← hγ, h0, zero_pow S.hn.ne'])
    exact S.branch_regular α γ hα hγ0 hγ a (hbr α γ hα hγ0 hγ) i hi
  · obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq ((S.p.map (algebraMap C K)).eval α) S.hn
    have hβ0 : β ≠ 0 := fun h0 ↦ hα (by rw [← hβ, h0, zero_pow S.hn.ne'])
    exact S.nonbranch_regular ζ hζ α β hβ0 hβ a (fun β' hβ' hβp' ↦ hreg α β' hβ' hβp') i hi

end SuperData

end Differential
