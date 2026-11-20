import RischTragerBronstein.Mixed.NKExactT2

/-!
# The exact part in the basis `w = T θ`, for any exact test in a basis

`exactTG wex`: `exactT` with the exact test in a basis `wex` as a parameter; `exactTG_correct`
holds for every `wex` meeting the specification `WexSpec` (an answer decides the existence of an
antiderivative in the basis it is given, whatever its derivation matrix).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test in the basis `w = T θ`**, for any exact test `wex` in a basis. -/
def exactTG (m : ℕ) (wex : ℕ → List (List (LC (m + 1))) → List (LC (m + 1)) → Option Bool)
    (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) : Option Bool :=
  let O1 := MOr Fc ks (m + 1)
  let N := P.length - 1
  let tm : ℕ → ℕ → LC (m + 1) := fun i j ↦ (Tc.getD i []).getD j O1.zero
  let ti : ℕ → ℕ → LC (m + 1) := fun i j ↦ (Ti.getD i []).getD j O1.zero
  if !(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || N = 0 ||
    !(prodIdC Fc ks m N tm ti && prodIdC Fc ks m N ti tm) then none else
  match dThetaC O1 P with
  | none => none
  | some dθ =>
    let mθ : ℕ → ℕ → LC (m + 1) := fun i j ↦ (dPowC O1 P dθ i).getD j O1.zero
    let Mw := (List.range N).map fun i ↦ (List.range N).map fun j ↦
      lsumC O1 ((List.range N).map fun l ↦ O1.mul (O1.add (O1.deriv (tm i l))
        (lsumC O1 ((List.range N).map fun k ↦ O1.mul (tm i k) (mθ k l)))) (ti l j))
    let fw := (List.range N).map fun j ↦
      lsumC O1 ((List.range N).map fun k ↦ O1.mul (f.getD k O1.zero) (ti k j))
    wex N Mw fw

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ)

/-- **Specification of an exact test in a basis.** -/
def WexSpec (h1 : T.Tr (m + 1))
    (wex : ℕ → List (List (LC (m + 1))) → List (LC (m + 1)) → Option Bool) : Prop :=
  ∀ (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (θw : ℕ → L),
    (∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j) →
    (∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 → ∀ j < N, a j = 0) →
    ∀ res, wex N Mc f = some res →
      (res = true ↔ ∃ Y : ℕ → T.F (m + 1),
        (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
          ∑ j ∈ Finset.range N,
            ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)

set_option maxHeartbeats 3200000 in
/-- **Correctness of the generic exact-part test in the basis `w = T θ`.** -/
theorem exactTG_correct (h1 : T.Tr (m + 1))
    (wex : ℕ → List (List (LC (m + 1))) → List (LC (m + 1)) → Option Bool) (hwex : T.WexSpec m h1 wex)
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTG Fc ks m wex P Tc Ti f = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range (P.length - 1),
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j := by
  classical
  unfold exactTG at hres
  simp only at hres
  split_ifs at hres with hPc0
  split at hres
  · exact absurd hres (by simp)
  rename_i dθ hd
  have hPc : ¬((!(MOr Fc ks (m + 1)).isZero ((MOr Fc ks (m + 1)).add
      (P.getD (P.length - 1) (MOr Fc ks (m + 1)).zero) ((MOr Fc ks (m + 1)).neg
        (MOr Fc ks (m + 1)).one)) || decide (P.length - 1 = 0)) = true) := by
    intro h; apply hPc0; simp only [Bool.or_eq_true] at h ⊢; exact Or.inl h
  have hok : ((prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero) &&
      prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero)) = true) := by
    by_contra h; apply hPc0; simp only [Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
    right; simpa using h
  set O1 := MOr Fc ks (m + 1) with hO1
  set M1 := T.MPr (m + 1) h1 with hM1
  -- `P` is monic of degree `(P.length - 1)`
  have hPc' : O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) = true ∧ (P.length - 1) ≠ 0 := by
    revert hPc
    cases O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) <;> simp
  have hlead : M1.sem (P.getD (P.length - 1) O1.zero) = 1 := by
    have := (M1.isZero_iff _).mp hPc'.1
    rw [M1.sem_add, M1.sem_neg, M1.sem_one, add_neg_eq_zero] at this
    exact this
  have hPlen : P.length = (P.length - 1) + 1 := by
    have : P ≠ [] := fun h0' ↦ by rw [h0'] at hPc'; exact hPc'.2 rfl
    have := List.length_pos_of_ne_nil this
    omega
  have hPdeg : (GPoly.toPoly M1 P).natDegree = (P.length - 1) := by
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_toPoly_sem, List.getD_eq_default _ _ (by
        have : (P.length - 1) < k := by exact_mod_cast hk
        omega), M1.sem_zero]
    · exact le_natDegree_of_ne_zero (by rw [coeff_toPoly_sem, hlead]; exact one_ne_zero)
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [Monic, leadingCoeff, hPdeg, coeff_toPoly_sem, hlead]
  set N := P.length - 1 with hN
  have hN0 : N ≠ 0 := hPc'.2
  have hok' : prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
      (fun i j ↦ (Ti.getD i []).getD j O1.zero) = true ∧
      prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
      (fun i j ↦ (Tc.getD i []).getD j O1.zero) = true := by
    revert hok
    cases prodIdC Fc ks m N (fun i j ↦ (Tc.getD i []).getD j O1.zero)
      (fun i j ↦ (Ti.getD i []).getD j O1.zero) <;>
    cases prodIdC Fc ks m N (fun i j ↦ (Ti.getD i []).getD j O1.zero)
      (fun i j ↦ (Tc.getD i []).getD j O1.zero) <;> simp
  -- the values
  set t : ℕ → ℕ → L := fun i j ↦ (M1.sem ((Tc.getD i []).getD j O1.zero) : L) with ht
  set s : ℕ → ℕ → L := fun i j ↦ (M1.sem ((Ti.getD i []).getD j O1.zero) : L) with hs
  have hts := T.prodIdC_sound m h1 N _ _ hok'.1
  have hst := T.prodIdC_sound m h1 N _ _ hok'.2
  set w : ℕ → L := fun i ↦ ∑ k ∈ Finset.range N, t i k * θ ^ k with hw
  have hθw : ∀ l < N, θ ^ l = ∑ j ∈ Finset.range N, s l j * w j := fun l hl ↦
    (sum_inv_basis N t s (fun k ↦ θ ^ k) hst l hl).symm
  have hθd := fun i ↦ T.deriv_θ_pow_sum m h1 θ P hP hPm dθ hd i
  rw [hPdeg] at hθd
  -- the derivation matrix of `w`
  have hwd : ∀ i < N, (w i)′ = ∑ j ∈ Finset.range N,
      ((M1.sem ((((List.range N).map fun i ↦ (List.range N).map fun j ↦
        lsumC O1 ((List.range N).map fun l ↦ O1.mul (O1.add (O1.deriv ((Tc.getD i []).getD l O1.zero))
          (lsumC O1 ((List.range N).map fun k ↦ O1.mul ((Tc.getD i []).getD k O1.zero)
            ((dPowC O1 P dθ k).getD l O1.zero)))) ((Ti.getD l []).getD j O1.zero))).getD i []).getD
              j O1.zero) : T.F (m + 1)) : L) * w j := by
    intro i hi
    have hA : (w i)′ = ∑ l ∈ Finset.range N, (((M1.sem ((Tc.getD i []).getD l O1.zero))′ : T.F (m + 1)) +
        ∑ k ∈ Finset.range N, t i k * (T.Mθ m h1 P dθ k l : L)) * θ ^ l := by
      rw [hw, map_sum]
      simp only [Derivation.leibniz, smul_eq_mul]
      rw [Finset.sum_add_distrib]
      simp only [add_mul, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_comm]; rfl
      · rw [Finset.sum_congr rfl fun k hk ↦ by rw [hθd k, Finset.mul_sum], Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [hA]
    refine (Finset.sum_congr rfl fun l hl ↦ by rw [hθw l (Finset.mem_range.mp hl)]).trans ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ (Finset.mem_range.mp hj),
      T.sem_lsum_range m h1]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [hO1, (T.MPr (m + 1) h1).sem_mul, (T.MPr (m + 1) h1).sem_add,
      (T.MPr (m + 1) h1).sem_deriv, T.sem_lsum_range m h1,
      IntermediateField.coe_mul, IntermediateField.coe_add, AddSubmonoidClass.coe_finsetSum,
      MTower.coe_deriv, Mθ, ht, hs, Finset.sum_mul]
    ring
  -- independence of `w`
  have hindw : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * w j = 0 →
      ∀ j < N, a j = 0 := by
    intro a ha j hj
    have h0 : ∑ k ∈ Finset.range N, ((∑ i ∈ Finset.range N, a i * M1.sem ((Tc.getD i []).getD k O1.zero) :
        T.F (m + 1)) : L) * θ ^ k = 0 := by
      rw [← ha, hw]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hz := hind _ h0
    have := coords_inv N t s (fun i ↦ (a i : L)) hts j hj
    apply Subtype.ext
    change (a j : L) = 0
    rw [← this]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have := congrArg (fun z : T.F (m + 1) ↦ (z : L)) (hz k (Finset.mem_range.mp hk))
    push_cast at this
    simp only [ht]
    rw [this, zero_mul]
  -- the coordinates of `f`
  have hfw : ∀ Y : ℕ → T.F (m + 1),
      ((∑ i ∈ Finset.range N, (Y i : L) * w i)′ = ∑ j ∈ Finset.range N,
        ((M1.sem ((((List.range N).map fun j ↦ lsumC O1 ((List.range N).map fun k ↦
          O1.mul (f.getD k O1.zero) ((Ti.getD k []).getD j O1.zero)))).getD j O1.zero) :
            T.F (m + 1)) : L) * w j) ↔
      ((∑ i ∈ Finset.range N, (Y i : L) * w i)′ = ∑ k ∈ Finset.range N,
        ((M1.sem (f.getD k O1.zero) : T.F (m + 1)) : L) * θ ^ k) := by
    intro Y
    have e : ∑ j ∈ Finset.range N,
        ((M1.sem ((((List.range N).map fun j ↦ lsumC O1 ((List.range N).map fun k ↦
          O1.mul (f.getD k O1.zero) ((Ti.getD k []).getD j O1.zero)))).getD j O1.zero) :
            T.F (m + 1)) : L) * w j = ∑ k ∈ Finset.range N,
        ((M1.sem (f.getD k O1.zero) : T.F (m + 1)) : L) * θ ^ k := by
      refine (Finset.sum_congr rfl fun j hj ↦ by
        rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hj), T.sem_lsum_range m h1]).trans ?_
      symm
      refine (Finset.sum_congr rfl fun k hk ↦ by rw [hθw k (Finset.mem_range.mp hk)]).trans ?_
      push_cast
      simp only [hO1, (T.MPr (m + 1) h1).sem_mul, IntermediateField.coe_mul, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    rw [e]
  have hW := hwex N _ _ w hwd hindw res hres
  rw [hW]
  constructor
  · rintro ⟨Y, hY⟩
    rw [hfw] at hY
    refine ⟨fun k ↦ ∑ i ∈ Finset.range N, Y i * M1.sem ((Tc.getD i []).getD k O1.zero), ?_⟩
    rw [← hY]
    congr 1
    rw [hw]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  · rintro ⟨Y', hY'⟩
    refine ⟨fun j ↦ ∑ k ∈ Finset.range N, Y' k * M1.sem ((Ti.getD k []).getD j O1.zero), ?_⟩
    rw [hfw, ← hY']
    congr 1
    symm
    refine (Finset.sum_congr rfl fun k hk ↦ by
      rw [hθw k (Finset.mem_range.mp hk), Finset.mul_sum]).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ ↦ by ring

end MTower

end Curves.MT
