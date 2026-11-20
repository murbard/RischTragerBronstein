import RischTragerBronstein.Computable.NestXRdeP1

/-!
# The Risch equation over a primitive monomial: generic lemmas

`t′ = η` (the derivation of `F[t]` is `implicitDeriv (C η)`), `η` not a derivative in `F`:

* the degree bounds for `A Y′ + B Y = r` from the two top coefficients;
* `limN` finds the only `n` with `z′ + n η = ρ` solvable;
* values at infinity (`InfVal`) commute with the derivation, and the balanced case: if
  `F₁ / F₂ = h′ + ∑ cᵢ wᵢ′ / wᵢ - Q′ / Q` with `deg F₁ = deg F₂`, then the polynomial part of `h`
  is `h₀ + h₁ t` with `h₁` constant and `lc F₁ / lc F₂ = h₀′ + h₁ η + ∑ cᵢ lc(wᵢ)′ / lc(wᵢ)`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.NestX

open Tower.NestP Tower.NestM

section DegPrim

variable {F0 : Type*} [Field F0] [CharZero F0] [Differential F0] (η : F0)

omit [CharZero F0] in
lemma natDegree_DprimXP (Y : F0[X]) : (implicitDeriv (C η) Y).natDegree ≤ Y.natDegree :=
  (primShape η).deg Y _ le_rfl

omit [CharZero F0] in
lemma coeff_Dprim_topXP (Y : F0[X]) (n : ℕ) (hY : Y.natDegree ≤ n) :
    (implicitDeriv (C η) Y).coeff n = (Y.coeff n)′ := by
  have := (primShape η).top Y n hY
  simpa [primShape] using this

omit [CharZero F0] in
lemma coeff_Dprim_predXP (Y : F0[X]) (n : ℕ) (hn : 1 ≤ n) :
    (implicitDeriv (C η) Y).coeff (n - 1) = (Y.coeff (n - 1))′ + η * (Y.coeff n * n) := by
  rw [coeff_implicitDeriv_C, Nat.sub_add_cancel hn]
  push_cast [Nat.cast_sub hn]
  ring

omit [CharZero F0] [Differential F0] in
lemma coeff_mul_predXP (P Z : F0[X]) (d n : ℕ) (hP : P.natDegree ≤ d) (hZ : Z.natDegree ≤ n)
    (hn : 1 ≤ n) : (P * Z).coeff (d + n - 1) =
      P.coeff d * Z.coeff (n - 1) + (if d = 0 then 0 else P.coeff (d - 1)) * Z.coeff n := by
  set z := Z.coeff n
  set Z1 := Z - C z * X ^ n with hZ1
  have hZ1d : Z1.natDegree ≤ n - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    have hi' : n - 1 < i := by exact_mod_cast hi
    rw [hZ1, coeff_sub, coeff_C_mul_X_pow]
    by_cases hin : i = n
    · subst hin; simp [z]
    · rw [if_neg hin, coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
  have hZe : Z = Z1 + C z * X ^ n := by rw [hZ1]; ring
  have e1 : (P * Z1).coeff (d + n - 1) = P.coeff d * Z.coeff (n - 1) := by
    rw [show d + n - 1 = d + (n - 1) by omega, coeff_mul_add_eq_of_natDegree_le hP hZ1d, hZ1,
      coeff_sub, coeff_C_mul_X_pow, if_neg (by omega), sub_zero]
  have e2 : (P * (C z * X ^ n)).coeff (d + n - 1) =
      (if d = 0 then 0 else P.coeff (d - 1)) * z := by
    rw [← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
    split_ifs with h1 h2 h2 <;> first | omega | (rw [show d + n - 1 - n = d - 1 by omega]) | simp
  conv_lhs => rw [hZe, mul_add, coeff_add, e1, e2]

variable {η}

/-- **`A` dominates** (`B = 0` or `deg B + 1 < deg A`): `deg Y ≤ R - deg A + 1`. -/
lemma natDegree_le_of_rdePrim_AXP (hnd : ∀ y : F0, y′ ≠ η) (A B Y r : F0[X]) (R : ℕ)
    (hr : r.natDegree ≤ R) (hA0 : A ≠ 0) (hBA : B = 0 ∨ B.natDegree + 1 < A.natDegree)
    (heq : A * implicitDeriv (C η) Y + B * Y = r) : Y.natDegree ≤ R - A.natDegree + 1 := by
  by_contra hlt
  push Not at hlt
  set d := A.natDegree
  set n := Y.natDegree with hn
  have hY0 : Y ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hn; omega
  have hn1 : 1 ≤ n := by omega
  have hBd : B.natDegree ≤ d := by rcases hBA with h | h <;> [simp [h]; omega]
  have hBc : B.coeff d = 0 := by
    rcases hBA with h | h
    · simp [h]
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hBc' : (if d = 0 then 0 else B.coeff (d - 1)) = 0 := by
    split_ifs with hd
    · rfl
    · rcases hBA with h | h
      · simp [h]
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hDY := natDegree_DprimXP η Y
  -- the top coefficient: `Yₙ′ = 0`
  have hAd : A.natDegree ≤ d := le_rfl
  have hYd : Y.natDegree ≤ n := le_rfl
  have htop : A.coeff d * (Y.coeff n)′ = 0 := by
    have e := congrArg (fun P : F0[X] ↦ P.coeff (d + n)) heq
    have c1 := coeff_mul_add_eq_of_natDegree_le hAd hDY
    have c2 := coeff_mul_add_eq_of_natDegree_le hBd hYd
    simp only [coeff_add] at e
    rw [c1, c2, hBc, zero_mul, add_zero, coeff_Dprim_topXP η Y n le_rfl,
      coeff_eq_zero_of_natDegree_lt (show r.natDegree < d + n by omega)] at e
    exact e
  have hlcA : A.coeff d ≠ 0 := leadingCoeff_ne_zero.mpr hA0
  have hYn : (Y.coeff n)′ = 0 := (mul_eq_zero.mp htop).resolve_left hlcA
  -- the next coefficient
  have hpred : A.coeff d * ((Y.coeff (n - 1))′ + η * (Y.coeff n * n)) = 0 := by
    have e := congrArg (fun P : F0[X] ↦ P.coeff (d + n - 1)) heq
    have c1 := coeff_mul_predXP _ _ d n hAd hDY hn1
    have c2 := coeff_mul_predXP _ _ d n hBd hYd hn1
    simp only [coeff_add] at e
    rw [c1, c2, hBc, hBc', coeff_Dprim_topXP η Y n le_rfl, hYn, coeff_Dprim_predXP η Y n hn1,
      coeff_eq_zero_of_natDegree_lt (show r.natDegree < d + n - 1 by omega)] at e
    linear_combination e
  have hy0 : Y.coeff n ≠ 0 := leadingCoeff_ne_zero.mpr hY0
  have hnF : (n : F0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  apply hnd (-(Y.coeff (n - 1)) / (n * Y.coeff n))
  have h2 := (mul_eq_zero.mp hpred).resolve_left hlcA
  rw [Derivation.leibniz_div, Derivation.leibniz, hYn, show ((n : F0))′ = 0 by
    simpa using deriv_ratCastK (K := F0) (n : ℚ)]
  simp only [smul_eq_mul, mul_zero, zero_mul, add_zero, sub_zero, map_neg]
  field_simp
  linear_combination -h2

/-- **`B` dominates** (`deg A < deg B`): `Y = 0` or `deg Y + deg B ≤ R`. -/
lemma natDegree_le_of_rdePrim_BXP (A B Y r : F0[X]) (R : ℕ) (hr : r.natDegree ≤ R) (hB0 : B ≠ 0)
    (hAB : A.natDegree < B.natDegree) (heq : A * implicitDeriv (C η) Y + B * Y = r) :
    Y = 0 ∨ Y.natDegree + B.natDegree ≤ R := by
  by_contra hne
  push Not at hne
  obtain ⟨hY0, hlt⟩ := hne
  have hDY := natDegree_DprimXP η Y
  have e := congrArg (fun P : F0[X] ↦ P.coeff (B.natDegree + Y.natDegree)) heq
  have c1 := coeff_mul_add_eq_of_natDegree_le hAB.le hDY
  have c2 := coeff_mul_add_eq_of_natDegree_le (le_refl B.natDegree) (le_refl Y.natDegree)
  simp only [coeff_add] at e
  rw [c1, c2, coeff_eq_zero_of_natDegree_lt hAB, zero_mul, zero_add,
    coeff_eq_zero_of_natDegree_lt (show r.natDegree < B.natDegree + Y.natDegree by omega)] at e
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hB0) (leadingCoeff_ne_zero.mpr hY0) e

/-- **`deg B + 1 = deg A`**: `deg Y ≤ R - deg A + 1`, or `z′ + n η = -lc B / lc A` is solvable
(`n = deg Y`). -/
lemma natDegree_le_of_rdePrim_subXP (A B Y r : F0[X]) (R : ℕ) (hr : r.natDegree ≤ R)
    (hA0 : A ≠ 0) (hAB : B.natDegree + 1 = A.natDegree)
    (heq : A * implicitDeriv (C η) Y + B * Y = r) :
    Y.natDegree ≤ R - A.natDegree + 1 ∨
      ∃ z : F0, z′ + (Y.natDegree : F0) * η = -(B.leadingCoeff / A.leadingCoeff) := by
  by_cases hle : Y.natDegree ≤ R - A.natDegree + 1
  · exact Or.inl hle
  right
  push Not at hle
  set d := A.natDegree
  set n := Y.natDegree with hn
  have hY0 : Y ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hn; omega
  have hn1 : 1 ≤ n := by omega
  have hBd : B.natDegree ≤ d := by omega
  have hBc : B.coeff d = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hBc' : (if d = 0 then 0 else B.coeff (d - 1)) = B.leadingCoeff := by
    rw [if_neg (by omega), leadingCoeff, show d - 1 = B.natDegree by omega]
  have hDY := natDegree_DprimXP η Y
  have hAd : A.natDegree ≤ d := le_rfl
  have hYd : Y.natDegree ≤ n := le_rfl
  have htop : A.coeff d * (Y.coeff n)′ = 0 := by
    have e := congrArg (fun P : F0[X] ↦ P.coeff (d + n)) heq
    have c1 := coeff_mul_add_eq_of_natDegree_le hAd hDY
    have c2 := coeff_mul_add_eq_of_natDegree_le hBd hYd
    simp only [coeff_add] at e
    rw [c1, c2, hBc, zero_mul, add_zero, coeff_Dprim_topXP η Y n le_rfl,
      coeff_eq_zero_of_natDegree_lt (show r.natDegree < d + n by omega)] at e
    exact e
  have hlcA : A.coeff d ≠ 0 := leadingCoeff_ne_zero.mpr hA0
  have hYn : (Y.coeff n)′ = 0 := (mul_eq_zero.mp htop).resolve_left hlcA
  have hpred : A.coeff d * ((Y.coeff (n - 1))′ + η * (Y.coeff n * n)) +
      B.leadingCoeff * Y.coeff n = 0 := by
    have e := congrArg (fun P : F0[X] ↦ P.coeff (d + n - 1)) heq
    have c1 := coeff_mul_predXP _ _ d n hAd hDY hn1
    have c2 := coeff_mul_predXP _ _ d n hBd hYd hn1
    simp only [coeff_add] at e
    rw [c1, c2, hBc, hBc', coeff_Dprim_topXP η Y n le_rfl, hYn, coeff_Dprim_predXP η Y n hn1,
      coeff_eq_zero_of_natDegree_lt (show r.natDegree < d + n - 1 by omega)] at e
    linear_combination e
  have hy0 : Y.coeff n ≠ 0 := leadingCoeff_ne_zero.mpr hY0
  refine ⟨Y.coeff (n - 1) / Y.coeff n, ?_⟩
  rw [Derivation.leibniz_div, hYn]
  simp only [smul_eq_mul, mul_zero, sub_zero]
  change _ = -(B.leadingCoeff / A.coeff d)
  field_simp
  linear_combination hpred

/-- **Balanced** (`deg A = deg B`): `deg Y ≤ R - deg A + 1`, or `z′ + n η = β` is solvable with
`β = -(A_{d-1} (-lc B / lc A) + B_{d-1}) / lc A` (`n = deg Y`, `d = deg A`). -/
lemma natDegree_le_of_rdePrim_balXP (A B Y r : F0[X]) (R : ℕ) (hr : r.natDegree ≤ R)
    (hA0 : A ≠ 0) (hAB : A.natDegree = B.natDegree)
    (heq : A * implicitDeriv (C η) Y + B * Y = r) :
    Y.natDegree ≤ R - A.natDegree + 1 ∨
      ∃ z : F0, z′ + (Y.natDegree : F0) * η =
        -(((if A.natDegree = 0 then 0 else A.coeff (A.natDegree - 1)) *
            (-(B.leadingCoeff / A.leadingCoeff)) +
          (if A.natDegree = 0 then 0 else B.coeff (A.natDegree - 1))) / A.leadingCoeff) := by
  by_cases hle : Y.natDegree ≤ R - A.natDegree + 1
  · exact Or.inl hle
  right
  push Not at hle
  set d := A.natDegree
  set n := Y.natDegree with hn
  have hY0 : Y ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hn; omega
  have hn1 : 1 ≤ n := by omega
  have hBd : B.natDegree ≤ d := hAB.ge
  have hDY := natDegree_DprimXP η Y
  set Am := if d = 0 then 0 else A.coeff (d - 1) with hAm
  set Bm := if d = 0 then 0 else B.coeff (d - 1) with hBm
  have hlB : B.coeff d = B.leadingCoeff := by rw [leadingCoeff, hAB]
  have hlA : A.coeff d = A.leadingCoeff := rfl
  have hAd : A.natDegree ≤ d := le_rfl
  have hYd : Y.natDegree ≤ n := le_rfl
  have htop : A.leadingCoeff * (Y.coeff n)′ + B.leadingCoeff * Y.coeff n = 0 := by
    have e := congrArg (fun P : F0[X] ↦ P.coeff (d + n)) heq
    have c1 := coeff_mul_add_eq_of_natDegree_le hAd hDY
    have c2 := coeff_mul_add_eq_of_natDegree_le hBd hYd
    simp only [coeff_add] at e
    rw [c1, c2, coeff_Dprim_topXP η Y n le_rfl, hlB,
      coeff_eq_zero_of_natDegree_lt (show r.natDegree < d + n by omega)] at e
    exact e
  have hpred : A.leadingCoeff * ((Y.coeff (n - 1))′ + η * (Y.coeff n * n)) + Am * (Y.coeff n)′ +
      (B.leadingCoeff * Y.coeff (n - 1) + Bm * Y.coeff n) = 0 := by
    have e := congrArg (fun P : F0[X] ↦ P.coeff (d + n - 1)) heq
    have c1 := coeff_mul_predXP _ _ d n hAd hDY hn1
    have c2 := coeff_mul_predXP _ _ d n hBd hYd hn1
    simp only [coeff_add] at e
    rw [c1, c2, coeff_Dprim_topXP η Y n le_rfl, coeff_Dprim_predXP η Y n hn1, hlB,
      coeff_eq_zero_of_natDegree_lt (show r.natDegree < d + n - 1 by omega)] at e
    exact e
  have hy0 : Y.coeff n ≠ 0 := leadingCoeff_ne_zero.mpr hY0
  have hlcA : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA0
  refine ⟨Y.coeff (n - 1) / Y.coeff n, ?_⟩
  have hYn' : (Y.coeff n)′ = -(B.leadingCoeff / A.leadingCoeff) * Y.coeff n := by
    field_simp; linear_combination htop
  have key : (Y.coeff (n - 1))′ = (-(η * (Y.coeff n * n)) * A.leadingCoeff - Am * (Y.coeff n)′ -
      B.leadingCoeff * Y.coeff (n - 1) - Bm * Y.coeff n) / A.leadingCoeff := by
    field_simp; linear_combination hpred
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul]
  rw [key, hYn']
  field_simp
  ring

end DegPrim

section LimN

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
variable (ι : Cs →+* K) {O : COps α} (M : CField α K O)

lemma le_limN_foldrXP (g : List ℚ × α → ℕ) :
    ∀ (L : List (List ℚ × α)) (x : List ℚ × α), x ∈ L → x.1.getD 0 0 ≠ 0 →
      (natOfQ (-(x.1.getD 1 0) / x.1.getD 0 0)).getD 0 ≤ L.foldr (fun r acc ↦
        if r.1.getD 0 0 ≠ 0 then max acc ((natOfQ (-(r.1.getD 1 0) / r.1.getD 0 0)).getD 0)
        else acc) 0
  | [], _, hx, _ => by simp at hx
  | y :: L, x, hx, h0 => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [if_pos h0]; exact le_max_right _ _
    · have := le_limN_foldrXP g L x hx h0
      split_ifs
      · exact this.trans (le_max_left _ _)
      · exact this

/-- **`limN` is an upper bound** for the `n` with `z′ + n η = ρ` solvable, when `η` is not a
derivative. -/
lemma le_limNXP (lim : List α → List (List ℚ × α)) (hlim : LimSpec ι M lim) (ρ η : α)
    (hnd : ∀ y : K, y′ ≠ M.sem η) (n : ℕ) (z : K) (hz : z′ + n * M.sem η = M.sem ρ) :
    n ≤ limN lim ρ η := by
  classical
  set L := lim [ρ, η] with hL
  have hsC : sC ι M [(1 : Cs), -(n : Cs)] [ρ, η] = z′ := by
    simp only [sC, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_zero, List.getD_cons_succ, zero_add, map_one, map_neg, map_natCast, one_mul]
    linear_combination -hz
  obtain ⟨β, hβc, -⟩ := hlim.complete [ρ, η] [(1 : Cs), -(n : Cs)] (fun i hi ↦ by
    simp only [List.length_cons, List.length_nil] at hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    simp) z hsC.symm
  have h1 := hβc 0
  simp only [List.getD_cons_zero] at h1
  rw [← hL] at h1
  obtain ⟨k, hk, hk0⟩ : ∃ k < L.length, (L.getD k ([], O.zero)).1.getD 0 0 ≠ 0 := by
    by_contra hne
    push Not at hne
    rw [Finset.sum_eq_zero fun k hk ↦ by rw [hne k (Finset.mem_range.mp hk)]; simp] at h1
    exact one_ne_zero h1
  set x := L.getD k ([], O.zero) with hx
  have hxL : x ∈ L := by rw [hx, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
  have hs := hlim.sound [ρ, η] x hxL
  simp only [sQ, List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ, zero_add] at hs
  set r0 := x.1.getD 0 0
  set r1 := x.1.getD 1 0
  have hr0 : (r0 : K) ≠ 0 := by exact_mod_cast hk0
  have hq : ((-r1 / r0 : ℚ) : K) = (n : K) := by
    by_contra hne
    have hc : ∀ q : ℚ, ((q : K))′ = 0 := deriv_ratCastK
    have hdiv : ∀ (a : K) (c : ℚ), (a / (c : K))′ = a′ / c := by
      intro a c
      rw [div_eq_mul_inv, Derivation.leibniz, show ((c : K)⁻¹)′ = 0 by
        rw [← Rat.cast_inv]; exact hc _]
      simp only [smul_eq_mul, mul_zero, zero_add, div_eq_mul_inv]
      ring
    have hsub : (((-r1 / r0 - n : ℚ)) : K) ≠ 0 := by
      rw [Rat.cast_sub, Rat.cast_natCast]; exact sub_ne_zero.mpr hne
    apply hnd ((z - M.sem x.2 / (r0 : K)) / ((-r1 / r0 - n : ℚ) : K))
    rw [hdiv, map_sub, hdiv, hs, show z′ = M.sem ρ - n * M.sem η by linear_combination hz,
      div_eq_iff hsub]
    push_cast
    field_simp
    ring
  have hqn : (-r1 / r0 : ℚ) = n := by exact_mod_cast hq
  have := le_limN_foldrXP (fun _ ↦ 0) L x hxL hk0
  rw [hqn, natOfQ_natCast] at this
  exact this

end LimN

section InfPrim

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

variable {η : F} (hDp : ∀ P : F[X], P′ = implicitDeriv (C η) P)
include hDp

omit [CharZero F] in
lemma deriv_div_eqXP (P R : F[X]) (hR : R ≠ 0) :
    (φ P / φ R)′ = φ (implicitDeriv (C η) P * R - P * implicitDeriv (C η) R) / φ (R * R) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have h1 : φ R ≠ 0 := (map_ne_zero_iff _ hinj).mpr hR
  rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hDp, hDp]
  simp only [smul_eq_mul, map_sub, map_mul]
  field_simp

omit [CharZero F] in
/-- Values at infinity commute with the derivation of a primitive extension. -/
lemma infVal_derivXP {z : K} {c : F} (hz : InfVal z c) : InfVal z′ c′ := by
  obtain ⟨P, R, hR, hPR, rfl, hc⟩ := hz
  rw [deriv_div_eqXP (K := K) hDp P R hR]
  have hDP := (natDegree_DprimXP η P).trans hPR
  have hDR := natDegree_DprimXP η R
  refine ⟨_, R * R, mul_ne_zero hR hR, ?_, rfl, ?_⟩
  · rw [natDegree_mul hR hR]
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans (add_le_add hDP le_rfl))
      (natDegree_mul_le.trans (add_le_add hPR hDR)))
  · rw [natDegree_mul hR hR, coeff_sub, coeff_mul_add_eq_of_natDegree_le hDP le_rfl,
      coeff_mul_add_eq_of_natDegree_le hPR hDR, coeff_Dprim_topXP η P _ hPR,
      coeff_Dprim_topXP η R _ le_rfl, hc, leadingCoeff_mul, ← leadingCoeff, Derivation.leibniz]
    simp only [smul_eq_mul]
    ring

omit [CharZero F] in
lemma infVal_logDerivXP (Q : F[X]) (hQ : Q ≠ 0) :
    InfVal ((φ Q)′ / φ Q) (Q.leadingCoeff′ / Q.leadingCoeff) := by
  rw [deriv_algebraMap, hDp]
  have hlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  refine ⟨_, Q, hQ, natDegree_DprimXP η Q, rfl, ?_⟩
  rw [coeff_Dprim_topXP η Q _ le_rfl, ← leadingCoeff]
  field_simp

omit [CharZero F] in
lemma infVal_logSumXP {ι : Type*} (s : Finset ι) (c : ι → F) (Nw Dw : ι → F[X])
    (hND : ∀ i ∈ s, Nw i ≠ 0 ∧ Dw i ≠ 0) :
    InfVal (∑ i ∈ s, φ (C (c i)) * logDeriv (φ (Nw i) / φ (Dw i)))
      (∑ i ∈ s, c i * ((Nw i).leadingCoeff′ / (Nw i).leadingCoeff -
        (Dw i).leadingCoeff′ / (Dw i).leadingCoeff)) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  refine infVal_sum _ _ _ fun i hi ↦ infVal_C_mul ?_ _
  have hN0 : φ (Nw i) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (hND i hi).1
  have hD0 : φ (Dw i) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (hND i hi).2
  rw [logDeriv_div _ _ hN0 hD0, logDeriv, logDeriv]
  exact infVal_sub (infVal_logDerivXP (K := K) hDp _ (hND i hi).1)
    (infVal_logDerivXP (K := K) hDp _ (hND i hi).2)

omit hDp [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
/-- A polynomial with a value at infinity is a constant. -/
lemma eq_C_of_infValXP (P : F[X]) (c : F) (h : InfVal (φ P) c) : P = C c := by
  obtain ⟨P', R', hR', hle, hz, hc⟩ := h
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hφR : φ R' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hR'
  have hPR : P * R' = P' := hinj (by rw [map_mul, hz]; field_simp)
  by_cases hP : P = 0
  · subst hP
    rw [zero_mul] at hPR
    subst hPR
    rw [coeff_zero] at hc
    have : c = 0 := by
      rcases mul_eq_zero.mp hc.symm with h | h
      · exact h
      · exact absurd (leadingCoeff_eq_zero.mp h) hR'
    rw [this, C_0]
  · have hdeg := natDegree_mul hP hR'
    rw [hPR] at hdeg
    have h0 : P.natDegree = 0 := by omega
    rw [eq_C_of_natDegree_eq_zero h0]
    congr 1
    rw [← hPR, eq_C_of_natDegree_eq_zero h0, coeff_C_mul, ← leadingCoeff] at hc
    exact mul_right_cancel₀ (leadingCoeff_ne_zero.mpr hR') hc

/-- **The balanced case over a primitive**: if `F₁ / F₂ = h′ + ∑ cᵢ wᵢ′ / wᵢ - Q′ / Q` (`Q` monic,
`h = q + rr / hd`, `deg rr < deg hd`) with `deg F₁ = deg F₂`, then `deg q ≤ 1`, `q₁` is a
constant and `lc F₁ / lc F₂ = q₀′ + η q₁ + ∑ cᵢ (lc Nᵢ′ / lc Nᵢ - lc Dᵢ′ / lc Dᵢ)`. -/
theorem bal_coreXP (hnd : ∀ y : F, y′ ≠ η) (hn hd q rr Q F1 F2 : F[X]) (hd0 : hd ≠ 0)
    (hdiv : hn = q * hd + rr) (hrr : rr.degree < hd.degree) (hQ : Q.Monic) (hF2 : F2 ≠ 0)
    (hdeg : F1.natDegree = F2.natDegree) {ι : Type*} (s : Finset ι) (c : ι → F)
    (Nw Dw : ι → F[X]) (hND : ∀ i ∈ s, Nw i ≠ 0 ∧ Dw i ≠ 0)
    (hF : φ F1 / φ F2 = (φ hn / φ hd)′ + ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (Nw i) / φ (Dw i)) -
      (φ Q)′ / φ Q) :
    q.natDegree ≤ 1 ∧ (q.coeff 1)′ = 0 ∧ F1.leadingCoeff / F2.leadingCoeff =
      (q.coeff 0)′ + η * q.coeff 1 + ∑ i ∈ s, c i * ((Nw i).leadingCoeff′ / (Nw i).leadingCoeff -
        (Dw i).leadingCoeff′ / (Dw i).leadingCoeff) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hφd : φ hd ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
  have hsplit : φ hn / φ hd = φ q + φ rr / φ hd := by
    rw [hdiv, map_add, map_mul]; field_simp
  have hq' : (φ q)′ = φ (implicitDeriv (C η) q) := by rw [deriv_algebraMap, hDp]
  have hrrle : rr.natDegree ≤ hd.natDegree := natDegree_le_natDegree hrr.le
  have hrrc : rr.coeff hd.natDegree = 0 :=
    coeff_eq_zero_of_degree_lt (by rwa [← degree_eq_natDegree hd0])
  have hV1 : InfVal (φ F1 / φ F2 : K) (F1.leadingCoeff / F2.leadingCoeff) := by
    have := infVal_of (K := K) F1 F2 hF2 hdeg.le
    rwa [← hdeg] at this
  have hV2 : InfVal ((φ rr / φ hd : K))′ (0 : F) := by
    have := infVal_derivXP (K := K) hDp (infVal_of (K := K) rr hd hd0 hrrle)
    rwa [hrrc, zero_div, Derivation.map_zero] at this
  have hV3 := infVal_logSumXP (K := K) hDp s c Nw Dw hND
  have hV4 : InfVal ((φ Q)′ / φ Q : K) (0 : F) := by
    have := infVal_logDerivXP (K := K) hDp Q hQ.ne_zero
    rwa [hQ.leadingCoeff, Derivation.map_one_eq_zero, zero_div] at this
  set ℓ := ∑ i ∈ s, c i * ((Nw i).leadingCoeff′ / (Nw i).leadingCoeff -
    (Dw i).leadingCoeff′ / (Dw i).leadingCoeff) with hℓ
  have hq : φ (implicitDeriv (C η) q) = φ F1 / φ F2 - (φ rr / φ hd)′ -
      ∑ i ∈ s, φ (C (c i)) * logDeriv (φ (Nw i) / φ (Dw i)) + (φ Q)′ / φ Q := by
    rw [hF, hsplit, map_add, hq']; ring
  have hV := infVal_add (infVal_sub (infVal_sub hV1 hV2) hV3) hV4
  rw [← hq] at hV
  have hC := eq_C_of_infValXP (K := K) _ _ hV
  set v := F1.leadingCoeff / F2.leadingCoeff - 0 - ℓ + 0 with hv
  -- the coefficients of `q′ = C v`
  have hco : ∀ k, 1 ≤ k → (q.coeff k)′ + η * (q.coeff (k + 1) * (k + 1)) = 0 := fun k hk ↦ by
    have := congrArg (fun P : F[X] ↦ P.coeff k) hC
    simp only [coeff_implicitDeriv_C, coeff_C, if_neg (by omega : k ≠ 0)] at this
    exact this
  have hq1 : q.natDegree ≤ 1 := by
    by_contra hlt
    push Not at hlt
    set d := q.natDegree with hd
    have hq0 : q ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hd; omega
    have htop := hco d (by omega)
    rw [coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < d + 1), zero_mul, mul_zero,
      add_zero] at htop
    have hpred := hco (d - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ d)] at hpred
    have hlc : q.coeff d ≠ 0 := leadingCoeff_ne_zero.mpr hq0
    have hdF : ((d : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    apply hnd (-(q.coeff (d - 1)) / (d * q.coeff d))
    rw [Derivation.leibniz_div, Derivation.leibniz, htop, show (((d : ℕ) : F))′ = 0 by
      simpa using deriv_ratCastK (K := F) (d : ℚ)]
    simp only [smul_eq_mul, mul_zero, zero_mul, add_zero, sub_zero, map_neg]
    have hdc : (((d - 1 : ℕ) : F) + 1) = d := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel (by omega : 1 ≤ d)]
    rw [hdc] at hpred
    field_simp
    linear_combination -hpred
  have hc1 : (q.coeff 1)′ = 0 := by
    have := hco 1 le_rfl
    rwa [coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < 1 + 1), zero_mul, mul_zero,
      add_zero] at this
  refine ⟨hq1, hc1, ?_⟩
  have h0 := congrArg (fun P : F[X] ↦ P.coeff 0) hC
  simp only [coeff_implicitDeriv_C, coeff_C_zero, zero_add, Nat.cast_zero] at h0
  rw [hv] at h0
  linear_combination -h0

end InfPrim

end Tower.NestX
