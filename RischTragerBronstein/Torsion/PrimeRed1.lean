import RischTragerBronstein.Torsion.GoodPrime
import RischTragerBronstein.Torsion.NonSpec7

/-!
# Checks at a prime from characteristic zero (1): base points

For a certified reduction `R` (`RedValid`, through `φ : K → ℚ_p`) and `p`-integral data, the checks
on the base points hold modulo `p` once they hold over `K`:

* `nsCheck_red`, `detCheck_red`: the non-speciality and determinant certificates reduce;
* `evalB_red_zero`, `evalB_red_ne_zero`: equations `W(x, y) = 0` reduce, and so do inequalities whose
  inverse is `p`-integral (the lifts are units of `ℤ_p`).

The lifts `zL` to `ℤ_p` carry each identity over `K` (injectivity of `ℤ_p → ℚ_p`) to `𝔽_p`.
-/

open Polynomial

namespace Curves

open CPoly Sup GTors

section Red

variable {K : Type*} [Field K] [DecidableEq K]
variable {p : ℕ} [hp : Fact p.Prime] (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)

include hR in
lemma red_zero_of (h0 : R.ok 0 = true) : R.red 0 = 0 := by
  have := psiRed_atom φ R hR h0
  rw [show atom φ R hR h0 = 0 from Subtype.ext rfl, map_zero] at this
  exact this.symm

lemma ok_getD {l : List K} (hl : ∀ c ∈ l, R.ok c = true) (h0 : R.ok 0 = true) (i : ℕ) :
    R.ok (l.getD i 0) = true := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]; exact hl _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; exact h0

lemma okB_getD {Bc : List (BPoly K)} (hB : ∀ W ∈ Bc, ∀ P ∈ W, ∀ c ∈ P, R.ok c = true) (j : ℕ) :
    ∀ P ∈ Bc.getD j [], ∀ c ∈ P, R.ok c = true := by
  by_cases hj : j < Bc.length
  · rw [List.getD_eq_getElem _ _ hj]; exact hB _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; simp

lemma okLL_getD {ys : List (List K)} (hy : ∀ l ∈ ys, ∀ c ∈ l, R.ok c = true) (i : ℕ) :
    ∀ c ∈ ys.getD i [], R.ok c = true := by
  by_cases hi : i < ys.length
  · rw [List.getD_eq_getElem _ _ hi]; exact hy _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; simp

lemma getD_red (hr0 : R.red 0 = 0) (l : List K) (i : ℕ) :
    (l.map R.red).getD i 0 = R.red (l.getD i 0) := by
  rw [← hr0, List.getD_map]

lemma getD_redLL (hr0 : R.red 0 = 0) (ys : List (List K)) (i k : ℕ) :
    ((ys.map (·.map R.red)).getD i []).getD k 0 = R.red ((ys.getD i []).getD k 0) := by
  rw [show ([] : List (ZMod p)) = ([] : List K).map R.red from rfl, List.getD_map, getD_red R hr0]

lemma getD_redB (Bc : List (BPoly K)) (j : ℕ) :
    (Bc.map (redBL R)).getD j [] = redBL R (Bc.getD j []) := by
  rw [show ([] : BPoly (ZMod p)) = redBL R [] from rfl, List.getD_map]

include hR in
/-- **Identities reduce.** -/
lemma toZMod_eq_zero_of {A : K} {Z : ℤ_[p]} (hZ : algebraMap ℤ_[p] ℚ_[p] Z = φ A) (hA : A = 0) :
    PadicInt.toZMod Z = 0 := by
  have : Z = 0 := algZ_injective (by rw [hZ, hA, map_zero, map_zero])
  rw [this, map_zero]

include hR in
/-- **Inequalities with an integral inverse reduce.** -/
lemma toZMod_ne_zero_of {A : K} {Z : ℤ_[p]} (hZ : algebraMap ℤ_[p] ℚ_[p] Z = φ A) (hA : A ≠ 0)
    (hinv : R.ok A⁻¹ = true) : PadicInt.toZMod Z ≠ 0 := by
  have e : Z * zL R φ hR A⁻¹ = 1 := algZ_injective (by
    rw [map_mul, hZ, zL_map R φ hR hinv, ← map_mul, mul_inv_cancel₀ hA, map_one, map_one])
  intro h
  have := congrArg PadicInt.toZMod e
  rw [map_mul, h, zero_mul, map_one] at this
  exact zero_ne_one this

variable (h0 : R.ok 0 = true)

/-- The lifted row entry. -/
noncomputable def nsRowZ (Bc : List (BPoly K)) (xs : List K) (ys : List (List K)) (i k j d : ℕ) :
    ℤ_[p] :=
  zL R φ hR (xs.getD i 0) ^ d * evalW (toB (liftBL R φ hR (Bc.getD j []))) (zL R φ hR (xs.getD i 0))
    (zL R φ hR ((ys.getD i []).getD k 0))

variable {Bc : List (BPoly K)} {xs : List K} {ys : List (List K)}
variable (hB : ∀ W ∈ Bc, ∀ P ∈ W, ∀ c ∈ P, R.ok c = true) (hx : ∀ c ∈ xs, R.ok c = true)
  (hy : ∀ l ∈ ys, ∀ c ∈ l, R.ok c = true)

include φ hR h0 hB hx hy in
lemma map_nsRowZ (i k j d : ℕ) :
    algebraMap ℤ_[p] ℚ_[p] (nsRowZ R φ hR Bc xs ys i k j d) = φ (nsRow Bc xs ys i k j d) := by
  rw [nsRowZ, nsRow, map_mul, map_pow, map_mul, map_pow, zL_map R φ hR (ok_getD R hx h0 i),
    map_evalW_lift R φ hR _ (okB_getD R hB j) _ _ _ _ (zL_map R φ hR (ok_getD R hx h0 i))
      (zL_map R φ hR (ok_getD R (okLL_getD R hy i) h0 k))]

include φ hR h0 hB hx hy in
lemma red_nsRowZ (i k j d : ℕ) :
    PadicInt.toZMod (nsRowZ R φ hR Bc xs ys i k j d) =
      nsRow (Bc.map (redBL R)) (xs.map R.red) (ys.map (·.map R.red)) i k j d := by
  have hr0 := red_zero_of R φ hR h0
  rw [nsRowZ, nsRow, map_mul, map_pow, toZMod_evalW_lift R φ hR _ (okB_getD R hB j),
    zL_red R φ hR (ok_getD R hx h0 i), zL_red R φ hR (ok_getD R (okLL_getD R hy i) h0 k),
    getD_red R hr0, getD_redLL R hr0, getD_redB]

include φ hR h0 hB hx hy in
/-- **The non-speciality certificate reduces.** -/
theorem nsCheck_red {n g : ℕ} {δL : List ℕ} {lam : List (List K)}
    (hl : ∀ l ∈ lam, ∀ c ∈ l, R.ok c = true) (h : nsCheck n g δL Bc xs ys lam = true) :
    nsCheck n g δL (Bc.map (redBL R)) (xs.map R.red) (ys.map (·.map R.red))
      (lam.map (·.map R.red)) = true := by
  have hr0 := red_zero_of R φ hR h0
  simp only [nsCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq] at h ⊢
  intro i0 hi0 j hj d hd
  rcases h i0 hi0 j hj d hd with h1 | h1
  · exact Or.inl h1
  right
  set lamZ : ℕ → ℕ → ℤ_[p] := fun i k ↦
    if k = 0 then 0 else zL R φ hR ((lam.getD i0 []).getD (i * n + k) 0)
  have hlok : ∀ m, R.ok ((lam.getD i0 []).getD m 0) = true := ok_getD R (okLL_getD R hl i0) h0
  set Z := nsRowZ R φ hR Bc xs ys i0 0 j d -
    ∑ i ∈ Finset.range g, ∑ k ∈ Finset.range n, lamZ i k * nsRowZ R φ hR Bc xs ys i k j d
  have hZ : algebraMap ℤ_[p] ℚ_[p] Z = φ (nsRow Bc xs ys i0 0 j d - ∑ i ∈ Finset.range g,
      ∑ k ∈ Finset.range n, (if k = 0 then 0 else (lam.getD i0 []).getD (i * n + k) 0) *
        nsRow Bc xs ys i k j d) := by
    simp only [Z, map_sub, map_sum, map_mul, map_nsRowZ R φ hR h0 hB hx hy, lamZ]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, ite_false, zL_map R φ hR (hlok _)]
  have := toZMod_eq_zero_of R φ hR hZ (sub_eq_zero.mpr h1)
  simp only [Z, map_sub, map_sum, map_mul, red_nsRowZ R φ hR h0 hB hx hy, sub_eq_zero] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : k = 0
  · simp [hk, lamZ]
  · simp only [hk, ite_false, lamZ, zL_red R φ hR (hlok _)]
    rw [show ([] : List (ZMod p)) = ([] : List K).map R.red from rfl, List.getD_map,
      getD_red R hr0]

include φ hR h0 hB hx hy in
/-- **The determinant certificates reduce.** -/
theorem detCheck_red {n g : ℕ} {Ls : List (List (List K))}
    (hl : ∀ L ∈ Ls, ∀ l ∈ L, ∀ c ∈ l, R.ok c = true) (h : detCheck n g Bc xs ys Ls = true) :
    detCheck n g (Bc.map (redBL R)) (xs.map R.red) (ys.map (·.map R.red))
      (Ls.map (·.map (·.map R.red))) = true := by
  have hr0 := red_zero_of R φ hR h0
  simp only [detCheck, leftInvCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h ⊢
  intro i hi a ha b hb
  have hLi : ∀ l ∈ Ls.getD i [], ∀ c ∈ l, R.ok c = true := by
    by_cases hi' : i < Ls.length
    · rw [List.getD_eq_getElem _ _ hi']; exact hl _ (List.getElem_mem hi')
    · rw [List.getD_eq_default _ _ (by omega)]; simp
  have hok : ∀ r, R.ok (((Ls.getD i []).getD a []).getD r 0) = true :=
    ok_getD R (okLL_getD R hLi a) h0
  set Z := ∑ r ∈ Finset.range n, zL R φ hR (((Ls.getD i []).getD a []).getD r 0) *
    nsRowZ R φ hR Bc xs ys i r b 0 - if a = b then 1 else 0
  have hZ : algebraMap ℤ_[p] ℚ_[p] Z = φ ((∑ r ∈ Finset.range n,
      ((Ls.getD i []).getD a []).getD r 0 * detMat Bc xs ys i r b) - if a = b then 1 else 0) := by
    simp only [Z, map_sub, map_sum, map_mul, zL_map R φ hR (hok _),
      map_nsRowZ R φ hR h0 hB hx hy, detMat, nsRow, pow_zero, one_mul]
    split_ifs <;> simp
  have := toZMod_eq_zero_of R φ hR hZ (sub_eq_zero.mpr (h i hi a ha b hb))
  simp only [Z, map_sub, map_sum, map_mul, red_nsRowZ R φ hR h0 hB hx hy, zL_red R φ hR (hok _),
    sub_eq_zero, nsRow, pow_zero, one_mul] at this
  rw [show (if a = b then (1 : ZMod p) else 0) = PadicInt.toZMod (if a = b then 1 else 0) by
    split_ifs <;> simp, ← this]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [detMat, show ([] : List (List (ZMod p))) = ([] : List (List K)).map (·.map R.red) from rfl,
    List.getD_map, getD_redLL R hr0]

end Red

end Curves
