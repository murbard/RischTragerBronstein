import RischTragerBronstein.Mixed.NKConstBasis

/-!
# Codes for logarithmic integral bases of constant curves

* `dThetaC_isSome`: `θ′` is computable (`dThetaC` answers) when `P` is coprime to `P′`;
* `prodIdC_of_sem`: the product check passes for semantically inverse matrices;
* `polyQ`, `fracQ`, `matQ`: codes of rational functions over `ℚ` (`sem_fracQ`);
* **`exactTR_exists`**: for a constant curve `F₀(t, θ) = 0` over a primitive level there are
  matrices `T`, `T⁻¹` of rational functions over `ℚ` and shifts `r` for which `exactTR` answers
  (from `const_logBasis` and `exactTR_isSome`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

section Generic

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

/-- `dThetaC` answers when `P′` and `P` are coprime. -/
lemma dThetaC_isSome (P : GPoly α)
    (hcop : IsCoprime (derivative (GPoly.toPoly M P)) (GPoly.toPoly M P)) :
    (dThetaC O P).isSome := by
  set e := GPoly.egcd O (GPoly.derivX O P) P with he
  obtain ⟨h1, h2⟩ := GPoly.egcd_dvd M (GPoly.derivX O P) P
  rw [GPoly.toPoly_derivX] at h1
  have hu : IsUnit (GPoly.toPoly M e.1) := hcop.isUnit_of_dvd' h1 h2
  have hne : GPoly.toPoly M e.1 ≠ 0 := hu.ne_zero
  have hdeg : (GPoly.toPoly M e.1).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  have htr : GPoly.trim O e.1 ≠ [] := fun h0 ↦ hne ((GPoly.trim_eq_nil_iff M _).mp h0)
  have hlen : (GPoly.trim O e.1).length = 1 := by rw [GPoly.length_trim M htr, hdeg]
  unfold dThetaC
  simp only [← he]
  rw [if_pos hlen]
  rfl

end Generic

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- A polynomial over `ℚ` as a code of level `m`. -/
def polyQ (m : ℕ) (A : ℚ[X]) : GPoly (LC m) :=
  (List.range (A.natDegree + 1)).map fun i ↦ mcst Fc ks m (A.coeff i)

/-- A quotient of polynomials over `ℚ` as a code of level `m + 1`. -/
def fracQ (m : ℕ) (A B : ℚ[X]) : LC (m + 1) := (polyQ Fc ks m A, polyQ Fc ks m B)

/-- A matrix of quotients of polynomials over `ℚ`. -/
def matQ (m : ℕ) (A B : ℕ → ℕ → ℚ[X]) (n : ℕ) : List (List (LC (m + 1))) :=
  (List.range n).map fun i ↦ (List.range n).map fun k ↦ fracQ Fc ks m (A i k) (B i k)

/-- Extension of a `Fin n`-indexed matrix by a default value. -/
def ext2 (n : ℕ) (A : Fin n → Fin n → ℚ[X]) (d : ℚ[X]) : ℕ → ℕ → ℚ[X] :=
  fun i k ↦ if h : i < n ∧ k < n then A ⟨i, h.1⟩ ⟨k, h.2⟩ else d

/-- Extension of `Fin n`-indexed shifts by `0`. -/
def extR (n : ℕ) (r : Fin n → ℕ) : ℕ → ℤ := fun k ↦ if h : k < n then (r ⟨k, h⟩ : ℤ) else 0

lemma ext2_of_lt (n : ℕ) (A : Fin n → Fin n → ℚ[X]) (d : ℚ[X]) (i k : ℕ) (hi : i < n) (hk : k < n) :
    ext2 n A d i k = A ⟨i, hi⟩ ⟨k, hk⟩ := by
  simp [ext2, hi, hk]

lemma extR_of_lt (n : ℕ) (r : Fin n → ℕ) (k : ℕ) (hk : k < n) : extR n r k = (r ⟨k, hk⟩ : ℤ) := by
  simp [extR, hk]

lemma matQ_getD (m : ℕ) (A B : ℕ → ℕ → ℚ[X]) (n i k : ℕ) (hi : i < n) (hk : k < n) :
    ((matQ Fc ks m A B n).getD i []).getD k (MOr Fc ks (m + 1)).zero = fracQ Fc ks m (A i k) (B i k) := by
  rw [matQ, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ hk]

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma toPoly_polyQ (m : ℕ) (h : T.Tr m) (A : ℚ[X]) :
    GPoly.toPoly (T.MP m h) (polyQ Fc ks m A) = A.map (algebraMap ℚ (T.F m)) := by
  refine Polynomial.ext fun k ↦ ?_
  rw [coeff_toPoly_sem, coeff_map]
  by_cases hk : k < A.natDegree + 1
  · rw [polyQ, NestTower.getD_range_map _ _ hk, T.sem_mcst m h]; rfl
  · rw [List.getD_eq_default _ _ (by simpa [polyQ] using hk), (T.MP m h).sem_zero,
      coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

lemma sem_fracQ (m : ℕ) (h1 : T.Tr (m + 1)) (A B : ℚ[X]) :
    (T.MPr (m + 1) h1).sem (fracQ Fc ks m A B) =
      T.phi m (A.map (algebraMap ℚ (T.F m))) / T.phi m (B.map (algebraMap ℚ (T.F m))) := by
  rw [MPr_sem, T.sem_MP_succ]
  change T.phi m (GPoly.toPoly (T.MP m _) (polyQ Fc ks m A)) /
    T.phi m (GPoly.toPoly (T.MP m _) (polyQ Fc ks m B)) = _
  rw [T.toPoly_polyQ, T.toPoly_polyQ]

lemma coe_sem_fracQ (m : ℕ) (h1 : T.Tr (m + 1)) (A B : ℚ[X]) :
    (((T.MPr (m + 1) h1).sem (fracQ Fc ks m A B) : T.F (m + 1)) : L) =
      aeval (T.ts m) A / aeval (T.ts m) B := by
  rw [T.sem_fracQ m h1, IntermediateField.coe_div, coe_phi, coe_phi, aeval_map_algebraMap,
    aeval_map_algebraMap]

/-- The product check passes for semantically inverse matrices. -/
lemma prodIdC_of_sem (m : ℕ) (h1 : T.Tr (m + 1)) (N : ℕ) (A B : ℕ → ℕ → LC (m + 1))
    (h : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, (T.MPr (m + 1) h1).sem (A i k) *
      (T.MPr (m + 1) h1).sem (B k j) = if i = j then 1 else 0) :
    prodIdC Fc ks m N A B = true := by
  unfold prodIdC
  simp only [List.all_eq_true, List.mem_range]
  intro i hi j hj
  refine ((T.MPr (m + 1) h1).isZero_iff _).mpr ?_
  rw [(T.MPr (m + 1) h1).sem_add, (T.MPr (m + 1) h1).sem_neg, T.sem_lsum_range m h1]
  simp only [(T.MPr (m + 1) h1).sem_mul]
  rw [h i hi j hj]
  split_ifs
  · rw [(T.MPr (m + 1) h1).sem_one, add_neg_cancel]
  · rw [(T.MPr (m + 1) h1).sem_zero, neg_zero, add_zero]

/-- The polynomial of a code `P` whose coefficients are those of `F₀ ∈ ℚ[t][Y]`. -/
lemma toPoly_P_const (m : ℕ) (h1 : T.Tr (m + 1)) (F0 : ℚ[X][X]) (P : GPoly (LC (m + 1)))
    (hPsem : ∀ i, (T.MPr (m + 1) h1).sem (P.getD i (MOr Fc ks (m + 1)).zero) =
      T.phi m ((F0.coeff i).map (algebraMap ℚ (T.F m)))) :
    (GPoly.toPoly (T.MPr (m + 1) h1) P).map (algebraMap (T.F (m + 1)) L) =
      F0.map (aeval (T.ts m)).toRingHom := by
  refine Polynomial.ext fun k ↦ ?_
  rw [coeff_map, coeff_map, coeff_toPoly_sem, hPsem]
  show ((T.phi m ((F0.coeff k).map (algebraMap ℚ (T.F m))) : T.F (m + 1)) : L) = _
  rw [coe_phi, aeval_map_algebraMap]; rfl

/-- **The code `P` of a constant curve is separable** (it is the minimal polynomial of `θ`). -/
lemma sep_P_const (m : ℕ) (h1 : T.Tr (m + 1)) (P : GPoly (LC (m + 1)))
    (hPm : (GPoly.toPoly (T.MPr (m + 1) h1) P).Monic) (n : ℕ)
    (hdeg : (GPoly.toPoly (T.MPr (m + 1) h1) P).natDegree = n) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range n, (a j : L) * θ ^ j = 0 →
      ∀ j < n, a j = 0) :
    IsCoprime (derivative (GPoly.toPoly (T.MPr (m + 1) h1) P))
      (GPoly.toPoly (T.MPr (m + 1) h1) P) := by
  set Q := GPoly.toPoly (T.MPr (m + 1) h1) P with hQ
  have hint : IsIntegral (T.F (m + 1)) θ := ⟨Q, hPm, by rw [← aeval_def]; exact hP⟩
  set μ := minpoly (T.F (m + 1)) θ with hμ
  have hμd : μ ∣ Q := minpoly.dvd _ _ hP
  -- `deg μ ≥ n`
  have hμn : n ≤ μ.natDegree := by
    by_contra hlt
    push Not at hlt
    have h0 := hind (fun j ↦ μ.coeff j) (by
      have := minpoly.aeval (T.F (m + 1)) θ
      rw [aeval_eq_sum_range' (n := n) (by omega)] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Algebra.smul_def]; rfl) μ.natDegree hlt
    have := (minpoly.monic hint).leadingCoeff
    rw [leadingCoeff, h0] at this
    exact zero_ne_one this
  have hQμ : Q = μ := by
    obtain ⟨c, hc⟩ := hμd
    have hc0 : c ≠ 0 := fun h0 ↦ hPm.ne_zero (by rw [hc, h0, mul_zero])
    have hdc : c.natDegree = 0 := by
      have := congrArg natDegree hc
      rw [natDegree_mul (show μ ≠ 0 from minpoly.ne_zero hint) hc0, hdeg] at this
      omega
    have hcm : c.Monic := by
      have := congrArg leadingCoeff hc
      rw [leadingCoeff_mul, (minpoly.monic hint).leadingCoeff, one_mul, hPm.leadingCoeff] at this
      exact this.symm
    rw [hc, eq_one_of_monic_natDegree_zero hcm hdc, mul_one]
  have hirr : Irreducible Q := by rw [hQμ]; exact minpoly.irreducible hint
  exact (hirr.separable).symm

set_option maxHeartbeats 3200000 in
/-- **`exactTR` answers for a suitable integral basis of a constant curve.** -/
theorem exactTR_exists (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m}
    (hk : ks m = .prim η) (htr : Transcendental (T.F m) (T.ts m))
    (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h1.of_succ) lim)
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h1.of_succ).sem η)
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (hn : F0.natDegree ≠ 0)
    (P : GPoly (LC (m + 1))) (hPlen : P.length = F0.natDegree + 1)
    (hPsem : ∀ i, (T.MPr (m + 1) h1).sem (P.getD i (MOr Fc ks (m + 1)).zero) =
      T.phi m ((F0.coeff i).map (algebraMap ℚ (T.F m))))
    (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 →
      ∀ j < F0.natDegree, a j = 0) (f : List (LC (m + 1))) :
    ∃ (A B Ai Bi : ℕ → ℕ → ℚ[X]) (r : ℕ → ℤ),
      (exactTR Fc ks m η lim r P (matQ Fc ks m A B F0.natDegree)
        (matQ Fc ks m Ai Bi F0.natDegree) f).isSome := by
  classical
  set n := F0.natDegree with hn'
  set M1 := T.MPr (m + 1) h1 with hM1
  have hN : P.length - 1 = n := by omega
  have hsemn : M1.sem (P.getD n (MOr Fc ks (m + 1)).zero) = 1 := by
    rw [hPsem, hF0.coeff_natDegree, Polynomial.map_one, map_one]
  have hPc : (MOr Fc ks (m + 1)).isZero ((MOr Fc ks (m + 1)).add
      (P.getD (P.length - 1) (MOr Fc ks (m + 1)).zero)
      ((MOr Fc ks (m + 1)).neg (MOr Fc ks (m + 1)).one)) = true := by
    rw [hN]
    refine (M1.isZero_iff _).mpr ?_
    rw [M1.sem_add, M1.sem_neg, M1.sem_one, hsemn, add_neg_cancel]
  have hPmap := T.toPoly_P_const m h1 F0 P hPsem
  have htrQ : Transcendental ℚ (T.ts m) := Transcendental.of_tower_top ℚ htr
  have hPdeg : (GPoly.toPoly M1 P).natDegree = n := by
    have := congrArg natDegree hPmap
    rw [natDegree_map_eq_of_injective (algebraMap (T.F (m + 1)) L).injective,
      natDegree_map_eq_of_injective (transcendental_iff_injective.mp htrQ)] at this
    exact this
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [Monic, leadingCoeff, hPdeg, coeff_toPoly_sem, hsemn]
  have hroot : (F0.map (aeval (T.ts m)).toRingHom).eval θ = 0 := by
    rw [← hPmap, eval_map, ← aeval_def]; exact hP
  have hcop := T.sep_P_const m h1 P hPm n hPdeg θ hP hind
  obtain ⟨dθ, hd⟩ := Option.isSome_iff_exists.mp (dThetaC_isSome M1 P hcop)
  obtain ⟨A, B, Ai, Bi, r, S0, Pm, hB, hBi, hTTi, hTiT, hS0, hsq, hder, hdeg⟩ :=
    T.const_logBasis m h1 hm hk htr hη F0 hF0 θ hroot hind
  set t := T.ts m with ht
  set ηL : L := (((T.MP m h1.of_succ).sem η : T.F m) : L) with hηL
  have hηF0 : (T.MP m h1.of_succ).sem η ≠ 0 := fun h0 ↦ hη 0 (by rw [Derivation.map_zero, h0])
  have hS0t : aeval t S0 ≠ 0 := fun h0 ↦ hS0 (transcendental_iff_injective.mp htrQ (by rw [h0, map_zero]))
  set A' := ext2 n A 0 with hA'
  set B' := ext2 n B 1 with hB'
  set Ai' := ext2 n Ai 0 with hAi'
  set Bi' := ext2 n Bi 1 with hBi'
  set Pm' := ext2 n Pm 0 with hPm'
  set r' := extR n r with hr'
  have eA : ∀ i k (hi : i < n) (hk : k < n), A' i k = A ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n A 0 i k hi hk
  have eB : ∀ i k (hi : i < n) (hk : k < n), B' i k = B ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n B 1 i k hi hk
  have eAi : ∀ i k (hi : i < n) (hk : k < n), Ai' i k = Ai ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n Ai 0 i k hi hk
  have eBi : ∀ i k (hi : i < n) (hk : k < n), Bi' i k = Bi ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n Bi 1 i k hi hk
  have ePm : ∀ i k (hi : i < n) (hk : k < n), Pm' i k = Pm ⟨i, hi⟩ ⟨k, hk⟩ := fun i k hi hk ↦
    ext2_of_lt n Pm 0 i k hi hk
  have er : ∀ k (hk : k < n), r' k = (r ⟨k, hk⟩ : ℤ) := fun k hk ↦ extR_of_lt n r k hk
  set Tc := matQ Fc ks m A' B' n with hTc
  set Ti := matQ Fc ks m Ai' Bi' n with hTi
  -- the values of the matrices
  have sT : ∀ i (hi : i < n) k (hk : k < n),
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
        aeval t (A ⟨i, hi⟩ ⟨k, hk⟩) / aeval t (B ⟨i, hi⟩ ⟨k, hk⟩) := fun i hi k hk ↦ by
    rw [hTc, matQ_getD _ _ m _ _ n i k hi hk, T.coe_sem_fracQ m h1, eA i k hi hk, eB i k hi hk]
  have sTi : ∀ i (hi : i < n) k (hk : k < n),
      ((M1.sem ((Ti.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
        aeval t (Ai ⟨i, hi⟩ ⟨k, hk⟩) / aeval t (Bi ⟨i, hi⟩ ⟨k, hk⟩) := fun i hi k hk ↦ by
    rw [hTi, matQ_getD _ _ m _ _ n i k hi hk, T.coe_sem_fracQ m h1, eAi i k hi hk, eBi i k hi hk]
  -- range sums as `Fin` sums
  have hfin : ∀ (g : ℕ → L), ∑ k ∈ Finset.range n, g k = ∑ k : Fin n, g k := fun g ↦
    (Fin.sum_univ_eq_sum_range g n).symm
  -- the product checks
  have hok : prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true ∧
      prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true := by
    rw [hN]
    refine ⟨T.prodIdC_of_sem m h1 n _ _ fun i hi j hj ↦ ?_, T.prodIdC_of_sem m h1 n _ _ fun i hi j hj ↦ ?_⟩
    · apply Subtype.ext
      push_cast
      rw [hfin (fun k ↦ ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) *
        ((M1.sem ((Ti.getD k []).getD j (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L))]
      rw [Finset.sum_congr rfl fun k _ ↦ by rw [sT i hi k k.2, sTi k k.2 j hj], hTTi ⟨i, hi⟩ ⟨j, hj⟩]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Fin.ext_iff]
    · apply Subtype.ext
      push_cast
      rw [hfin (fun k ↦ ((M1.sem ((Ti.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) *
        ((M1.sem ((Tc.getD k []).getD j (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L))]
      rw [Finset.sum_congr rfl fun k _ ↦ by rw [sTi i hi k k.2, sT k k.2 j hj], hTiT ⟨i, hi⟩ ⟨j, hj⟩]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Fin.ext_iff]
  -- the derivation matrix
  set ηF : T.F (m + 1) := T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem η)) with hηF
  set S0F : (T.F m)[X] := S0.map (algebraMap ℚ (T.F m)) with hS0F
  set Mval : ℕ → ℕ → T.F (m + 1) := fun i j ↦
    ηF * T.phi m ((Pm' i j).map (algebraMap ℚ (T.F m))) / T.phi m S0F with hMvaldef
  have hηFL : (ηF : L) = ηL := by rw [hηF, coe_phi, aeval_C]; rfl
  have hS0FL : ((T.phi m S0F : T.F (m + 1)) : L) = aeval t S0 := by
    rw [hS0F, coe_phi, aeval_map_algebraMap]
  have hMvalL : ∀ i j (hi : i < n) (hj : j < n), (Mval i j : L) =
      ηL * aeval t (Pm ⟨i, hi⟩ ⟨j, hj⟩) / aeval t S0 := fun i j hi hj ↦ by
    rw [hMvaldef]
    push_cast
    rw [hηFL, hS0FL, coe_phi, aeval_map_algebraMap, ePm i j hi hj]
  -- `w = T θ`
  have hwL : ∀ i (hi : i < n), ∑ k ∈ Finset.range n,
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k =
      ∑ k : Fin n, aeval t (A ⟨i, hi⟩ k) / aeval t (B ⟨i, hi⟩ k) * θ ^ (k : ℕ) := fun i hi ↦ by
    rw [hfin]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [sT i hi k k.2]
  have hMval : ∀ i < P.length - 1, (∑ k ∈ Finset.range (P.length - 1),
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k)′ =
      ∑ j ∈ Finset.range (P.length - 1), (Mval i j : L) *
        ∑ k ∈ Finset.range (P.length - 1), ((M1.sem ((Tc.getD j []).getD k
          (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k := by
    rw [hN]
    intro i hi
    rw [hwL i hi, ← Fin.sum_univ_eq_sum_range (fun j ↦ (Mval i j : L) * ∑ k ∈ Finset.range n,
      ((M1.sem ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k) n]
    have hR : ∑ j : Fin n, (Mval i j : L) * ∑ k ∈ Finset.range n,
        ((M1.sem ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k =
        ∑ j : Fin n, ηL * aeval t (Pm ⟨i, hi⟩ j) / aeval t S0 *
          ∑ k : Fin n, aeval t (A j k) / aeval t (B j k) * θ ^ (k : ℕ) :=
      Finset.sum_congr rfl fun j _ ↦ by rw [hwL j j.2, hMvalL i j hi j.2]
    rw [hR]
    have hd := hder ⟨i, hi⟩
    rw [← mul_div_cancel_right₀ ((∑ k : Fin n, aeval t (A ⟨i, hi⟩ k) / aeval t (B ⟨i, hi⟩ k) *
      θ ^ (k : ℕ))′) hS0t, hd, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hsqF : Squarefree S0F :=
    ((PerfectField.separable_iff_squarefree.mpr hsq).map (f := algebraMap ℚ (T.F m))).squarefree
  have hsq' : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A S : (T.F m)[X], Squarefree S ∧
      Mval i j = T.phi m A / T.phi m S := by
    intro i _ j _
    refine ⟨Polynomial.C ((T.MP m h1.of_succ).sem η) * (Pm' i j).map (algebraMap ℚ (T.F m)), S0F,
      hsqF, ?_⟩
    rw [hMvaldef, map_mul]
  have hτ : T.tau m ≠ 0 := T.tau_ne_zero m htr
  have hφS0 : T.phi m S0F ≠ 0 := fun h0 ↦ hS0t (by rw [← hS0FL, h0]; rfl)
  have hprop' : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A B : (T.F m)[X], B ≠ 0 ∧
      A.degree < B.degree ∧
      Mval i j * T.tau m ^ (r' j - r' i) - (if i = j then (r' i : T.F (m + 1)) *
        T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem η)) / T.tau m else 0) =
        T.phi m A / T.phi m B := by
    rw [hN]
    intro i hi j hj
    set Q : ℚ[X] := X ^ (r ⟨j, hj⟩ + 1) * Pm ⟨i, hi⟩ ⟨j, hj⟩ -
      (if (⟨i, hi⟩ : Fin n) = ⟨j, hj⟩ then Polynomial.C (r ⟨i, hi⟩ : ℚ) * X ^ r ⟨i, hi⟩ * S0 else 0)
      with hQ
    have hQd := hdeg ⟨i, hi⟩ ⟨j, hj⟩
    set B0 : ℚ[X] := X ^ (r ⟨i, hi⟩ + 1) * S0 with hB0
    have hB0d : B0.natDegree = r ⟨i, hi⟩ + 1 + S0.natDegree := by
      rw [hB0, natDegree_mul (pow_ne_zero _ X_ne_zero) hS0, natDegree_X_pow]
    have hB00 : B0 ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS0
    refine ⟨Polynomial.C ((T.MP m h1.of_succ).sem η) * Q.map (algebraMap ℚ (T.F m)),
      B0.map (algebraMap ℚ (T.F m)), (Polynomial.map_ne_zero_iff (algebraMap ℚ (T.F m)).injective).mpr
        hB00, ?_, ?_⟩
    · refine (degree_le_natDegree).trans_lt ?_
      rw [degree_map_eq_of_injective (algebraMap ℚ (T.F m)).injective, degree_eq_natDegree hB00,
        hB0d, Nat.cast_lt]
      have := (natDegree_C_mul_le ((T.MP m h1.of_succ).sem η) (Q.map (algebraMap ℚ (T.F m)))).trans
        (natDegree_map_le (f := algebraMap ℚ (T.F m)))
      have hQd' : Q.natDegree ≤ r ⟨i, hi⟩ + S0.natDegree := hQd
      exact lt_of_le_of_lt (this.trans hQd') (by omega)
    · simp only [hMvaldef, er i hi, er j hj, ePm i j hi hj]
      simp only [hQ, hB0, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        map_mul, map_sub, map_pow]
      have hX : T.phi m X = T.tau m := rfl
      rw [hX, zpow_sub₀ hτ, zpow_natCast, zpow_natCast]
      by_cases hij : i = j
      · subst hij
        simp only [if_true, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
          Polynomial.map_X, map_mul, map_pow, hX, eq_ratCast, map_natCast]
        have hc : T.phi m (Polynomial.C ((r ⟨i, hi⟩ : ℚ) : T.F m)) = ((r ⟨i, hi⟩ : ℕ) : T.F (m + 1)) := by
          rw [show ((r ⟨i, hi⟩ : ℚ) : T.F m) = ((r ⟨i, hi⟩ : ℕ) : T.F m) by push_cast; rfl,
            Polynomial.C_eq_natCast, map_natCast]
        simp only [Polynomial.map_C, eq_ratCast, hηF]
        have hφS : T.phi m (S0.map (algebraMap ℚ (T.F m))) ≠ 0 := hφS0
        have hrr : r ⟨i, hj⟩ = r ⟨i, hi⟩ := rfl
        rw [hrr]
        simp only [hS0F, Polynomial.map_natCast, map_natCast]
        field_simp
        push_cast
        ring
      · have hij' : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h ↦ hij (Fin.mk.inj_iff.mp h)
        simp only [hij, hij', if_false, sub_zero, Polynomial.map_zero, map_zero, hηF]
        have hφS : T.phi m (S0.map (algebraMap ℚ (T.F m))) ≠ 0 := hφS0
        field_simp
        ring
  refine ⟨A', B', Ai', Bi', r', ?_⟩
  exact T.exactTR_isSome h1 hm hk htr lim hlim hη r' P θ hP hPc (by omega) (by rw [hN]; exact hind)
    dθ hd Tc Ti hok f Mval hMval hsq' hprop'

end MTower

end Curves.MT
