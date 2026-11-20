import RischTragerBronstein.Algebraic.HermiteExist
import RischTragerBronstein.Algebraic.HypGlue

/-!
# The Hermite decomposition on `y² = p(x)` over any field of constants

`hermite_existsK` is `hermite_exists` for `p, A, D ∈ K[X]` (`K` a field of characteristic zero,
`D` split over `K`), inside a differential field `E ⊇ K` in which `K` consists of constants.
-/

open Polynomial

namespace Differential

section HermiteK

section Hermite

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] [Differential K]
variable {E : Type*} [Field E] [CharZero E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
variable (x : E) (p : K[X])

omit [CharZero K] [DecidableEq K] [CharZero E] in
lemma deriv_algK (hC : ∀ c : K, c′ = 0) (c : K) : (algebraMap K E c)′ = 0 := by
  rw [deriv_algebraMap, hC, map_zero]

/-- `L(U) = U′ p(x) + U p′(x)/2`. -/
noncomputable def LopK (U : E) : E := U′ * aeval x p + U * aeval x (derivative p) / 2

lemma Lop_addK (U V : E) : LopK x p (U + V) = LopK x p U + LopK x p V := by
  unfold LopK; rw [map_add]; ring

/-- A simple-pole part supported on roots of `D` which are not roots of `p`. -/
def SimplePartK (R : E) (D : K[X]) : Prop :=
  ∃ (T : Finset K) (c : K → K), (∀ α ∈ T, D.IsRoot α ∧ ¬ p.IsRoot α) ∧
    R = ∑ α ∈ T, (algebraMap K E (c α)) / (x - (algebraMap K E (α)))

/-- The Hermite decomposition of `G` with denominator `D`. -/
def DecompK (G : E) (D : K[X]) : Prop :=
  ∃ (W B₀ : K[X]) (R : E), SimplePartK x p R D ∧ (B₀ = 0 ∨ B₀.natDegree + 2 ≤ p.natDegree) ∧
    G = LopK x p (aeval x W / aeval x D) + aeval x B₀ + R

variable {x p}

lemma simplePart_zeroK (D : K[X]) : SimplePartK x p 0 D :=
  ⟨∅, fun _ ↦ 0, by simp, by simp⟩

lemma simplePart_addK {R₁ R₂ : E} {D : K[X]} (h₁ : SimplePartK x p R₁ D) (h₂ : SimplePartK x p R₂ D) :
    SimplePartK x p (R₁ + R₂) D := by
  classical
  obtain ⟨T₁, c₁, hT₁, rfl⟩ := h₁
  obtain ⟨T₂, c₂, hT₂, rfl⟩ := h₂
  refine ⟨T₁ ∪ T₂, fun α ↦ (if α ∈ T₁ then c₁ α else 0) + (if α ∈ T₂ then c₂ α else 0), ?_, ?_⟩
  · intro α hα
    rcases Finset.mem_union.mp hα with h | h
    · exact hT₁ α h
    · exact hT₂ α h
  · simp only [map_add, add_div, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_subset Finset.subset_union_left (fun α _ hα ↦ by simp [hα])]
      exact Finset.sum_congr rfl fun α hα ↦ by simp [hα]
    · rw [← Finset.sum_subset Finset.subset_union_right (fun α _ hα ↦ by simp [hα])]
      exact Finset.sum_congr rfl fun α hα ↦ by simp [hα]

lemma simplePart_monoK {R : E} {D D' : K[X]} (h : SimplePartK x p R D) (hDD : D ∣ D') :
    SimplePartK x p R D' := by
  obtain ⟨T, c, hT, rfl⟩ := h
  refine ⟨T, c, fun α hα ↦ ⟨?_, (hT α hα).2⟩, rfl⟩
  obtain ⟨Q, rfl⟩ := hDD
  simp [IsRoot, (hT α hα).1.eq_zero]

variable (hne : ∀ Q : K[X], Q ≠ 0 → aeval x Q ≠ 0)
include hne

lemma decomp_monoK {G : E} {D D' : K[X]} (hD' : D' ≠ 0) (h : DecompK x p G D) (hDD : D ∣ D') :
    DecompK x p G D' := by
  obtain ⟨W, B₀, R, hR, hB, rfl⟩ := h
  obtain ⟨Q, rfl⟩ := hDD
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hD'
  have hD : D ≠ 0 := left_ne_zero_of_mul hD'
  refine ⟨W * Q, B₀, R, simplePart_monoK hR (dvd_mul_right _ _), hB, ?_⟩
  rw [map_mul, map_mul, mul_div_mul_right _ _ (hne Q hQ)]

lemma decomp_addK {G₁ G₂ : E} {D : K[X]} (hD : D ≠ 0) (h₁ : DecompK x p G₁ D)
    (h₂ : DecompK x p G₂ D) : DecompK x p (G₁ + G₂) D := by
  obtain ⟨W₁, B₁, R₁, hR₁, hB₁, rfl⟩ := h₁
  obtain ⟨W₂, B₂, R₂, hR₂, hB₂, rfl⟩ := h₂
  refine ⟨W₁ + W₂, B₁ + B₂, R₁ + R₂, simplePart_addK hR₁ hR₂, ?_, ?_⟩
  · rcases hB₁ with h | h
    · rw [h, zero_add]; exact hB₂
    rcases hB₂ with h' | h'
    · rw [h', add_zero]; exact Or.inr h
    by_cases h0 : B₁ + B₂ = 0
    · exact Or.inl h0
    · have := natDegree_add_le B₁ B₂
      exact Or.inr (by rw [Nat.max_def] at this; split_ifs at this <;> omega)
  · rw [map_add, add_div, Lop_addK, map_add]; ring

omit hne in
/-- **The polynomial case** (`hypRed`). -/
lemma decomp_polyK (hC : ∀ c : K, c′ = 0) (hx : x′ = 1) (hp1 : 1 ≤ p.natDegree) (A : K[X]) :
    DecompK x p (aeval x A) 1 := by
  set Ac : CPoly K := (List.range (A.natDegree + 1)).map A.coeff
  have hAc : CPoly.toPoly Ac = A := by
    rcases eq_or_ne A 0 with h | h
    · exact EllAlgo.toPoly_range_coeff A _ (Or.inl h)
    · exact EllAlgo.toPoly_range_coeff A _ (Or.inr (by omega))
  set pc : CPoly K := (List.range (p.natDegree + 1)).map p.coeff
  have hpc : CPoly.toPoly pc = p :=
    EllAlgo.toPoly_range_coeff p _ (Or.inr (by omega))
  have hp1' : 1 ≤ (CPoly.toPoly pc).natDegree := by rw [hpc]; exact hp1
  obtain ⟨h1, h2⟩ := CPoly.hypRed_spec pc Ac hp1'
  rw [hpc, hAc] at h1
  rw [hpc] at h2
  refine ⟨CPoly.toPoly (CPoly.hypRed pc Ac).1, CPoly.toPoly (CPoly.hypRed pc Ac).2, 0,
    simplePart_zeroK 1, h2, ?_⟩
  rw [map_one, div_one, add_zero]
  unfold LopK
  rw [deriv_aeval_x x hC hx]
  conv_lhs => rw [h1]
  simp only [map_add, map_mul, aeval_C, one_div, map_inv₀, map_ofNat]
  ring

end Hermite


section Main

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] [Differential K]
variable {E : Type*} [Field E] [CharZero E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
variable {x : E} {p : K[X]}
variable (hC : ∀ c : K, c′ = 0)
variable (hne : ∀ Q : K[X], Q ≠ 0 → aeval x Q ≠ 0) (hx : x′ = 1) (hsq : Squarefree p)
  (hp1 : 1 ≤ p.natDegree)
include hC hne hx

lemma aeval_linK (r : K) : aeval x (X - C r) = x - (algebraMap K E (r)) := by simp

lemma x_sub_neK (r : K) : x - (algebraMap K E (r)) ≠ 0 := by
  rw [← aeval_linK hC hne hx]; exact hne _ (X_sub_C_ne_zero r)

/-- `L(W/D)` is `L` of the value, with a pure-power `W`-term: `L(h/(x−r)^j)`. -/
lemma Lop_powK (r h : K) (j : ℕ) :
    LopK x p ((algebraMap K E (h)) / (x - (algebraMap K E (r))) ^ j) =
      (algebraMap K E (h)) * (-(j : E) * aeval x p + (x - (algebraMap K E (r))) * aeval x (derivative p) / 2) /
        (x - (algebraMap K E (r))) ^ (j + 1) := by
  have hr := x_sub_neK hC hne hx r
  unfold LopK
  have hd : ((x - (algebraMap K E (r))) ^ j)′ = (j : E) * (x - (algebraMap K E (r))) ^ (j - 1) := by
    rw [Derivation.leibniz_pow, map_sub, hx, (deriv_algK hC), sub_zero, smul_eq_mul, mul_one]
    push_cast; ring
  rw [Derivation.leibniz_div, hd, (deriv_algK hC)]
  simp only [smul_eq_mul, mul_zero, zero_sub]
  rcases j with _ | j
  · simp; field_simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    ring

omit hC hne hx in
lemma decomp_LopK (W D : K[X]) : DecompK x p (LopK x p (aeval x W / aeval x D)) D :=
  ⟨W, 0, 0, simplePart_zeroK D, Or.inl rfl, by simp⟩

include hsq hp1

/-- **The pure-power case** `A/(x − r)^k`. -/
lemma decomp_powK (r : K) (k : ℕ) : ∀ (A : K[X]),
    DecompK x p (aeval x A / (x - (algebraMap K E (r))) ^ k) ((X - C r) ^ k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro A
  rcases k with _ | k
  · simpa using decomp_polyK hC hx hp1 A
  · have decomp_powK' := fun j (hj : j < k + 1) ↦ ih j hj
    have hr := x_sub_neK hC hne hx r
    have hDk : (X - C r) ^ (k + 1) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero r)
    have hdvd : (X - C r) ^ k ∣ (X - C r) ^ (k + 1) := pow_dvd_pow _ (Nat.le_succ k)
    -- `A = A(r) + (X − r) A₁`
    set lam := A.eval r
    set A₁ := A /ₘ (X - C r)
    have hA : A = C lam + (X - C r) * A₁ := by
      have := modByMonic_add_div A (X - C r)
      rw [modByMonic_X_sub_C_eq_C_eval] at this
      exact this.symm
    have hsplit : aeval x A / (x - (algebraMap K E (r))) ^ (k + 1) =
        (algebraMap K E (lam)) / (x - (algebraMap K E (r))) ^ (k + 1) + aeval x A₁ / (x - (algebraMap K E (r))) ^ k := by
      conv_lhs => rw [hA]
      simp only [map_add, map_mul, aeval_C, aeval_linK hC hne hx]
      field_simp
      ring
    rw [hsplit]
    refine decomp_addK hne hDk ?_ (decomp_monoK hne hDk (decomp_powK' k (Nat.lt_succ_self k) A₁) hdvd)
    -- the leading term `λ/(x − r)^{k+1}`
    have hlin := aeval_linK hC hne hx r
    by_cases hpr : p.eval r = 0
    · -- a branch point: lower with `L(h/(x − r)^{k+1})`
      have hsep : p.Separable := (PerfectField.separable_iff_squarefree).mpr hsq
      have hp'r : (derivative p).eval r ≠ 0 := by
        intro h0
        rw [Polynomial.separable_def] at hsep
        obtain ⟨u1, u2, huv⟩ := hsep
        have := congrArg (eval r) huv
        simp only [eval_add, eval_mul, eval_one, hpr, h0, mul_zero, add_zero] at this
        exact zero_ne_one this
      set q := p /ₘ (X - C r)
      have hpq : p = (X - C r) * q := by
        have := modByMonic_add_div p (X - C r)
        rw [modByMonic_X_sub_C_eq_C_eval, hpr, C_0, zero_add] at this
        exact this.symm
      have hqr : q.eval r = (derivative p).eval r := by
        rw [hpq, derivative_mul]; simp
      set h : K := -lam / ((k + 1 / 2 : K) * (derivative p).eval r)
      have hk2 : (k + 1 / 2 : K) ≠ 0 := by
        have h' : ((2 * k + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast (show 2 * k + 1 ≠ 0 by omega)
        rw [show (k + 1 / 2 : K) = ((2 * k + 1 : ℕ) : K) / 2 by push_cast; ring]
        exact div_ne_zero h' two_ne_zero
      have h2k : (1 + (k : K) * 2) ≠ 0 := by
        have h' : ((2 * k + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast (show 2 * k + 1 ≠ 0 by omega)
        rw [show (1 + (k : K) * 2) = ((2 * k + 1 : ℕ) : K) by push_cast; ring]; exact h'
      set M : K[X] := C lam + C (h * (k + 1)) * q - C (h / 2) * derivative p
      have hMr : M.eval r = 0 := by
        simp only [M, eval_add, eval_sub, eval_mul, eval_C, hqr, h]
        have hinv : (1 + (k : K) * 2) * (1 + (k : K) * 2)⁻¹ = 1 := mul_inv_cancel₀ h2k
        field_simp
        linear_combination (-lam) * hinv
      set P₁ := M /ₘ (X - C r)
      have hM : M = (X - C r) * P₁ := by
        have := modByMonic_add_div M (X - C r)
        rw [modByMonic_X_sub_C_eq_C_eval, hMr, C_0, zero_add] at this
        exact this.symm
      have hid : (algebraMap K E (lam)) / (x - (algebraMap K E (r))) ^ (k + 1) =
          LopK x p (aeval x (C h) / aeval x ((X - C r) ^ (k + 1))) +
            aeval x P₁ / (x - (algebraMap K E (r))) ^ k := by
        rw [aeval_C, map_pow, hlin, Lop_powK hC hne hx]
        have e1 := congrArg (aeval x) hM
        have e2 := congrArg (aeval x) hpq
        simp only [M, map_add, map_sub, map_mul, aeval_C, hlin] at e1 e2
        have eP : aeval x P₁ = ((algebraMap K E (lam)) + algebraMap K E (h * (k + 1)) * aeval x q -
            (algebraMap K E (h / 2)) * aeval x (derivative p)) / (x - (algebraMap K E (r))) := by
          rw [eq_div_iff hr]; simp only [map_mul, map_add, map_natCast, map_one, map_div₀, map_ofNat] at e1 ⊢; linear_combination -e1
        rw [eP, e2]
        simp only [map_mul, map_add, map_div₀, map_ofNat, map_natCast, map_one, map_sub, Nat.cast_add, Nat.cast_one]
        field_simp
        ring
      rw [hid]
      exact decomp_addK hne hDk (decomp_LopK _ _)
        (decomp_monoK hne hDk (decomp_powK' k (Nat.lt_succ_self k) P₁) hdvd)
    · rcases k with _ | k
      · -- a simple pole at a non-branch point: a residue
        refine ⟨0, 0, (algebraMap K E (lam)) / (x - (algebraMap K E (r))) ^ (0 + 1),
          ⟨{r}, fun _ ↦ lam, by simp [IsRoot, hpr], by simp⟩, Or.inl rfl, ?_⟩
        simp [LopK]
      · -- a pole of order `k + 2 ≥ 2` at a non-branch point
        set h : K := -lam / ((k + 1 : K) * p.eval r)
        have hk1 : (k + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        set M : K[X] := C lam + C (h * (k + 1)) * p - C (h / 2) * ((X - C r) * derivative p)
        have hMr : M.eval r = 0 := by
          simp only [M, eval_add, eval_sub, eval_mul, eval_C, eval_X, sub_self, zero_mul, h]
          field_simp
          ring
        set P₁ := M /ₘ (X - C r)
        have hM : M = (X - C r) * P₁ := by
          have := modByMonic_add_div M (X - C r)
          rw [modByMonic_X_sub_C_eq_C_eval, hMr, C_0, zero_add] at this
          exact this.symm
        have hid : (algebraMap K E (lam)) / (x - (algebraMap K E (r))) ^ (k + 1 + 1) =
            LopK x p (aeval x (C h * (X - C r)) / aeval x ((X - C r) ^ (k + 1 + 1))) +
              aeval x P₁ / (x - (algebraMap K E (r))) ^ (k + 1) := by
          have e0 : aeval x (C h * (X - C r)) / aeval x ((X - C r) ^ (k + 1 + 1)) =
              (algebraMap K E (h)) / (x - (algebraMap K E (r))) ^ (k + 1) := by
            rw [map_mul, aeval_C, map_pow, hlin]
            field_simp
            ring
          rw [e0, Lop_powK hC hne hx]
          have e1 := congrArg (aeval x) hM
          simp only [M, map_add, map_sub, map_mul, aeval_C, hlin] at e1
          have eP : aeval x P₁ = ((algebraMap K E (lam)) + algebraMap K E (h * (k + 1)) * aeval x p -
              (algebraMap K E (h / 2)) * ((x - (algebraMap K E (r))) * aeval x (derivative p))) /
                (x - (algebraMap K E (r))) := by
            rw [eq_div_iff hr]; simp only [map_mul, map_add, map_natCast, map_one, map_div₀, map_ofNat] at e1 ⊢; linear_combination -e1
          rw [eP]
          simp only [map_mul, map_add, map_div₀, map_ofNat, map_natCast, map_one, map_sub, Nat.cast_add, Nat.cast_one]
          field_simp
          ring
        rw [hid]
        exact decomp_addK hne hDk (decomp_LopK _ _)
          (decomp_monoK hne hDk (decomp_powK' (k + 1) (Nat.lt_succ_self _) P₁) hdvd)

/-- **Existence of the Hermite decomposition** for a split denominator. -/
theorem hermite_existsK (n : ℕ) : ∀ (D : K[X]), D.natDegree = n → D ≠ 0 → D.Splits →
    ∀ A : K[X], DecompK x p (aeval x A / aeval x D) D := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D hn hD hsplit A
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- a constant denominator
    rw [← hn] at h0
    obtain ⟨d, rfl⟩ : ∃ d, D = C d := ⟨D.coeff 0, eq_C_of_natDegree_eq_zero h0⟩
    have hd : d ≠ 0 := by rintro rfl; exact hD (by simp)
    have h1 := decomp_polyK (x := x) (p := p) hC hx hp1 (C (1 / d) * A)
    have := decomp_monoK hne (hD) h1 (by exact one_dvd _)
    convert this using 1
    simp only [aeval_C, map_mul, map_one, div_one]
    push_cast
    field_simp
  · -- a root `r` of multiplicity `k ≥ 1`
    obtain ⟨r, hr⟩ := hsplit.exists_eval_eq_zero (by
      rw [degree_eq_natDegree hD, hn]; exact_mod_cast hpos.ne')
    obtain ⟨D₂, hDD, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd D hD r
    set k := D.rootMultiplicity r
    have hk : 1 ≤ k := (rootMultiplicity_pos hD).mpr hr
    have hD₂ : D₂ ≠ 0 := by rintro rfl; rw [mul_zero] at hDD; exact hD hDD
    have hcop : IsCoprime ((X - C r) ^ k) D₂ :=
      ((Polynomial.irreducible_X_sub_C r).coprime_iff_not_dvd.mpr hnd).pow_left
    obtain ⟨a, b, hab⟩ := hcop
    have hdeg₂ : D₂.natDegree < n := by
      have := congrArg natDegree hDD
      rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero r)) hD₂, natDegree_pow,
        natDegree_X_sub_C, mul_one] at this
      omega
    have hsplit₂ : D₂.Splits := hsplit.of_dvd hD (by rw [hDD]; exact dvd_mul_left _ _)
    -- `A/D = A b/(x − r)^k + A a/D₂`
    have hpow0 : aeval x ((X - C r) ^ k) ≠ 0 := hne _ (pow_ne_zero _ (X_sub_C_ne_zero r))
    have hD₂0 := hne _ hD₂
    have hsplitA : aeval x A / aeval x D = aeval x (A * b) / (x - (algebraMap K E (r))) ^ k +
        aeval x (A * a) / aeval x D₂ := by
      have e := congrArg (aeval x) hab
      simp only [map_add, map_mul, map_one, map_pow, aeval_linK hC hne hx] at e
      rw [hDD, map_mul, map_pow, aeval_linK hC hne hx]
      rw [map_pow, aeval_linK hC hne hx] at hpow0
      rw [map_mul, map_mul]
      field_simp
      linear_combination (-(aeval x A)) * e
    rw [hsplitA]
    refine decomp_addK hne hD ?_ ?_
    · exact decomp_monoK hne hD (decomp_powK hC hne hx hsq hp1 r k (A * b))
        (by rw [hDD]; exact dvd_mul_right _ _)
    · exact decomp_monoK hne hD (ih _ (by omega) D₂ rfl hD₂ hsplit₂ (A * a))
        (by rw [hDD]; exact dvd_mul_left _ _)

end Main

end HermiteK

end Differential
