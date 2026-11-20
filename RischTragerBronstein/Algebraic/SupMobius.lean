import RischTragerBronstein.Algebraic.SupFrontSpec
import RischTragerBronstein.Jacobian.HypDecideEvenK

/-!
# Superelliptic curves with `n ∣ deg f`: moving a branch point to infinity

For `yⁿ = f(x)` with `f` squarefree of degree `d = n m` (so infinity is not a branch point) and a
root `e` of `f`, the substitution `t = 1/(x − e)`, `w = y tᵐ` gives `wⁿ = P(t)` with
`P(t) = t^{d-1} R(1/t)` (`f(x + e) = x R(x)`) of degree `d − 1`, coprime to `n`. With the
derivation rescaled by `−1/t²` (`hasElementaryIntegral_rescale_iff`), the integrand
`∑ Aⱼ(x)/D(x) yʲ` becomes `∑ Ãⱼ(t)/D̃(t) wʲ` (`mobData`), and `superFrontMob` runs `superFront`
on the transformed curve. Roots and `n`-th roots come from untrusted functions and are checked.

* `superFrontMob_spec`: every answer is correct.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac

namespace Sup

section Data

variable {F : Type*} [Field F] [DecidableEq F]

/-- The exponent needed by the `j`-th numerator: `ℓⱼ + 2 + m j` (`0` if `Aⱼ = 0`). -/
def mobExp (e : F) (A : List (CPoly F)) (m j : ℕ) : ℕ :=
  if trim (shiftPoly (A.getD j []) e) = [] then 0
  else (trim (shiftPoly (A.getD j []) e)).length - 1 + 2 + m * j

/-- The largest needed exponent. -/
def mobNeed (e : F) (A : List (CPoly F)) (m : ℕ) : ℕ :=
  ((List.range A.length).map (mobExp e A m)).foldr max 0

/-- The `j`-th transformed numerator `−t^{δ + N − ℓⱼ − 2 − m j} rev(Aⱼ(x + e))`. -/
def mobNum (e : F) (A : List (CPoly F)) (sD : CPoly F) (m N j : ℕ) : CPoly F :=
  let sA := trim (shiftPoly (A.getD j []) e)
  if sA = [] then []
  else smul (-1) (mul sA.reverse (monomial (sD.length - 1 + N - (sA.length - 1) - 2 - m * j) 1))

/-- **The transformed data** `(P, Ã, D̃)` at a root `e` of `f`. -/
def mobData (f : CPoly F) (n : ℕ) (e : F) (A : List (CPoly F)) (D : CPoly F) :
    Option (CPoly F × List (CPoly F) × CPoly F) :=
  let s := trim (shiftPoly f e)
  let R := s.drop 1
  let m := R.length / n
  let sD := trim (shiftPoly D e)
  let N := mobNeed e A m - (sD.length - 1)
  if s.getD 0 0 = 0 ∧ R.length = n * m ∧ sD ≠ [] then
    some (R.reverse, (List.range n).map (mobNum e A sD m N), mul sD.reverse (monomial N 1))
  else none

lemma le_mobNeed (e : F) (A : List (CPoly F)) (m : ℕ) {j : ℕ} (hj : j < A.length) :
    mobExp e A m j ≤ mobNeed e A m :=
  le_foldr_max (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

lemma natDegree_of_last {P : CPoly F} (h : P.getD (P.length - 1) 0 ≠ 0) :
    (toPoly P).natDegree = P.length - 1 := by
  refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [coeff_toPoly]; exact h))
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_toPoly, List.getD_eq_default _ _ (by have : P.length - 1 < k := by exact_mod_cast hk
                                                 omega)]

end Data

section Proc

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- **The procedure for `n ∣ deg f`**, at a root `e` of `f`: transform, find the non-branch
points of the new denominator (`rootsF`, `nthF`: untrusted, checked), run `superFront`. -/
def superFrontMob (f : CPoly F) (n : ℕ) (ζ : F)
    (torsF : CPoly F → List (F × F × ℕ) → Option (Option ℕ)) (rootsF : CPoly F → List F)
    (nthF : F → F) (e : F) (A : List (CPoly F)) (D : CPoly F) : Option Bool :=
  match mobData f n e A D with
  | none => none
  | some (P, A', D') =>
    let as := (rootsF (nbPartK P D')).dedup
    let a : Fin as.length → F := fun i ↦ as.get i
    let bs := as.map fun α ↦ nthF (evalC P α)
    let b : Fin as.length → F := fun i ↦ bs.getD i 0
    if squarefreeCheck P && decide (P.getD (P.length - 1) 0 ≠ 0) && decide (0 < P.length - 1) &&
        decide (Nat.Coprime n (P.length - 1)) &&
        (List.finRange as.length).all (fun i ↦ decide (b i ≠ 0 ∧ b i ^ n = evalC P (a i))) then
      superFront P n ζ (torsF P) A' D' a b
    else none

end Proc

section Spec

open Differential IntermediateField

universe u

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 3200000 in
/-- **Correctness of `superFrontMob`**: every answer is correct. -/
theorem superFrontMob_spec (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : F →+* Kc)
    (f : CPoly F) {n : ℕ} (hn : 0 < n) (hy : y ^ n = aeval x ((toPoly f).map ι))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (torsF : CPoly F → List (F × F × ℕ) → Option (Option ℕ))
    (htors : ∀ P : CPoly F, Squarefree (toPoly P) → Nat.Coprime n (P.length - 1) →
      TorsSpecN P n (torsF P))
    (rootsF : CPoly F → List F) (nthF : F → F) (e : F) (A : List (CPoly F)) (D : CPoly F)
    (ans : Bool) (h : superFrontMob f n ζ torsF rootsF nthF e A D = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map ι) / aeval x ((toPoly D).map ι) * y ^ j) := by
  unfold superFrontMob at h
  split at h
  · cases h
  rename_i P A' D' hmob
  simp only at h
  split_ifs at h with hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at hchk
  obtain ⟨⟨⟨⟨hPsq, hPlc⟩, hPpd⟩, hPcop⟩, hab⟩ := hchk
  unfold mobData at hmob
  simp only at hmob
  split_ifs at hmob with hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at hmob
  obtain ⟨hs0, hRlen, hDne⟩ := hcond
  obtain ⟨rfl, rfl, rfl⟩ := hmob
  set s := trim (shiftPoly f e)
  set R := s.drop 1
  set m := R.length / n
  set sD := trim (shiftPoly D e)
  set N := mobNeed e A m - (sD.length - 1) with hN
  set ce : E := algebraMap Kc E (ι e) with hce
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hxe : x - ce ≠ 0 := x_sub_const_ne hC x hx (ι e)
  set t : E := 1 / (x - ce) with ht
  have ht0 : t ≠ 0 := one_div_ne_zero hxe
  have hxt : x = 1 / t + ce := by rw [ht]; field_simp; ring
  set w : E := y * t ^ m with hw
  have hRne : R ≠ [] := by
    intro h0
    rw [h0] at hPpd
    simp at hPpd
  have hsplit : s = 0 :: R := by
    have hne : s ≠ [] := by
      intro h0
      exact hRne (by simp only [R, h0, List.drop_nil])
    obtain ⟨c, L, hcL⟩ := List.exists_cons_of_ne_nil hne
    have hR : R = L := by simp only [R, hcL, List.drop_one, List.tail_cons]
    rw [hcL] at hs0
    simp only [List.getD_cons_zero] at hs0
    rw [hcL, hs0, hR]
  -- `wⁿ = P(t)`
  have hwP : w ^ n = aeval t ((toPoly R.reverse).map ι) := by
    have h1 : evF ι x f = evF ι (1 / t) s := by rw [evF_shift_trim, ← hxt]
    have h2 : evF ι (1 / t) s = 1 / t * evF ι (1 / t) R := by
      conv_lhs => rw [hsplit]
      rw [evF_cons, map_zero, map_zero, zero_add]
    have h3 := evF_reverse ι t ht0 R hRne
    change w ^ n = evF ι t R.reverse
    have hy' : y ^ n = evF ι x f := hy
    have hRl : R.length - 1 + 1 = n * m := by
      have : 0 < R.length := List.length_pos_of_ne_nil hRne
      omega
    rw [hw, mul_pow, hy', h1, h2, h3, ← pow_mul, mul_comm m n, ← hRl]
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
  -- generation
  have hgen' : ∀ z : E, z ∈ Kc⟮t⟯⟮w⟯ := by
    intro z
    have hz := hgen z
    rw [← IntermediateField.mem_restrictScalars Kc, adjoin_simple_adjoin_simple] at hz ⊢
    refine (adjoin_le_iff.mpr ?_) hz
    have htm : t ∈ Kc⟮t, w⟯ := subset_adjoin _ _ (by simp)
    have hwm : w ∈ Kc⟮t, w⟯ := subset_adjoin _ _ (by simp)
    intro v hv
    rcases hv with hv | hv
    · rw [hv, hxt]
      exact add_mem (div_mem (one_mem _) htm) (IntermediateField.algebraMap_mem _ _)
    · rw [Set.mem_singleton_iff] at hv
      have : y = w / t ^ m := by rw [hw]; field_simp
      rw [hv, this]
      exact div_mem hwm (pow_mem htm _)
  -- the checks
  have hsqP : Squarefree (toPoly R.reverse) := squarefreeCheck_sound hPsq
  have hdegP : (toPoly R.reverse).natDegree = R.reverse.length - 1 := natDegree_of_last hPlc
  have hDne' : toPoly (mul sD.reverse (monomial N (1 : F))) ≠ 0 := by
    rw [toPoly_mul, toPoly_monomial, mul_ne_zero_iff]
    refine ⟨?_, by simp⟩
    rw [toPoly_reverseK]
    intro h0
    rw [reflect_eq_zero_iff, toPoly_trim] at h0
    exact hDne ((trim_eq_nil_iff _).mpr h0)
  set as := (rootsF (nbPartK R.reverse (mul sD.reverse (monomial N 1)))).dedup
  have hinj : Function.Injective fun i : Fin as.length ↦ as.get i :=
    fun i j hij ↦ (List.Nodup.get_inj_iff (List.nodup_dedup _)).mp hij
  have hspec := @superFront_spec F _ _ _ _ Kc E _ _ _ _ D' hDA' _ _ hC t w hT' ι R.reverse n hn
    hsqP hdegP hPpd hPcop hwP hgen' ζ hζ (torsF R.reverse) (htors _ hsqP hPcop) _ _ hDne'
    as.length (fun i ↦ as.get i) (fun i ↦ (as.map fun α ↦ nthF (evalC R.reverse α)).getD i 0) hinj
    (fun i ↦ (hab i).1) (fun i ↦ by rw [← evalC_eq]; exact (hab i).2) ans h
  rw [hspec]
  -- transfer back
  have hD := evF_reverse ι t ht0 sD hDne
  rw [evF_shift_trim, ← hxt] at hD
  have hml : ∀ L L' : CPoly F, evF ι t (mul L L') = evF ι t L * evF ι t L' :=
    fun L L' ↦ by simp [evF, toPoly_mul]
  have hmo : ∀ k : ℕ, evF ι t (monomial k (1 : F)) = t ^ k := fun k ↦ by
    simp [evF, toPoly_monomial]
  have hsm : ∀ (c : F) (L : CPoly F), evF ι t (smul c L) = algebraMap Kc E (ι c) * evF ι t L :=
    fun c L ↦ by simp [evF, toPoly_smul]
  have hterm : ∀ j ∈ Finset.range n,
      evF ι t (((List.range n).map (mobNum e A sD m N)).getD j []) /
          evF ι t (mul sD.reverse (monomial N 1)) * w ^ j =
        1 / τ * (evF ι x (A.getD j []) / evF ι x D * y ^ j) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    rw [List.getD_eq_getElem _ _ (by simpa using hjn), List.getElem_map, List.getElem_range]
    unfold mobNum
    simp only
    set sA := trim (shiftPoly (A.getD j []) e) with hsA
    have hAx : evF ι (1 / t) sA = evF ι x (A.getD j []) := by rw [hsA, evF_shift_trim, ← hxt]
    split_ifs with hA0
    · have : evF ι x (A.getD j []) = 0 := by
        rw [← hAx, hA0]; simp [evF]
      rw [this]
      simp [evF]
    · have hjA : j < A.length := by
        by_contra hc
        apply hA0
        rw [hsA, List.getD_eq_default _ _ (by omega)]
        rfl
      have hle := le_mobNeed e A m hjA
      rw [mobExp, if_neg (show ¬ trim (shiftPoly (A.getD j []) e) = [] by rw [← hsA]; exact hA0), ← hsA] at hle
      set k := sD.length - 1 + N - (sA.length - 1) - 2 - m * j with hkdef
      have hA := evF_reverse ι t ht0 sA hA0
      rw [hsm, hml, hml, hmo, hmo, hA, hD, hAx, hw, hτ]
      have hk : sD.length - 1 + N = k + (sA.length - 1) + m * j + 2 := by omega
      have e1 : t ^ (sD.length - 1) * t ^ N = t ^ k * t ^ (sA.length - 1) * (t ^ m) ^ j * t ^ 2 := by
        rw [← pow_add, ← pow_mul, ← pow_add, ← pow_add, ← pow_add, hk]
      by_cases hDx : evF ι x D = 0
      · rw [hDx]; simp
      simp only [map_neg, map_one]
      rw [show t ^ (sD.length - 1) * evF ι x D * t ^ N =
        evF ι x D * (t ^ (sD.length - 1) * t ^ N) by ring, e1, mul_pow]
      field_simp
  have hsum : (∑ j ∈ Finset.range n, evF ι t (((List.range n).map (mobNum e A sD m N)).getD j []) /
        evF ι t (mul sD.reverse (monomial N 1)) * w ^ j) =
      1 / τ * ∑ j ∈ Finset.range n, evF ι x (A.getD j []) / evF ι x D * y ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  change HasElementaryIntegral (∑ j ∈ Finset.range n,
      evF ι t (((List.range n).map (mobNum e A sD m N)).getD j []) /
        evF ι t (mul sD.reverse (monomial N 1)) * w ^ j) ↔ _
  rw [hsum]
  exact hasElementaryIntegral_rescale_iff ⟨d0⟩ (1 / τ) _ (one_div_ne_zero hτ0)

end Spec

end Sup
