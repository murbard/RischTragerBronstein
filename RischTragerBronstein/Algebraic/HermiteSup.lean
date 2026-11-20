import RischTragerBronstein.Algebraic.HermiteExistK

/-!
# The Hermite decomposition on a superelliptic curve

For `λ ∈ K` not a positive integer and `L_λ(U) = U′ p(x) + λ U p′(x)` (so that
`(U yʲ)′ = L_{j/n}(U) yʲ / p` on `yⁿ = p(x)`), and `A, D ∈ K[X]` with `D` split:

  `A/D = L_λ(W/D) + P + ∑_{α ∈ T} c_α/(x − α)`

with `W, P ∈ K[X]` and `T` a set of roots of `D` that are **not** roots of `p`
(`hermite_existsS`). As in `hermite_existsK` (the case `λ = 1/2` with a reduced polynomial part):
a pole of order `k + 1` at a branch point is lowered by `L_λ(h/(x − r)^{k+1})` (leading coefficient
`(λ − (k + 1)) p′(r) h ≠ 0`), a pole of order `≥ 2` at a non-branch point by `L_λ(h/(x − r)^k)`.
-/

open Polynomial

namespace Differential

section HermiteS

section Hermite

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] [Differential K]
variable {E : Type*} [Field E] [CharZero E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
variable (x : E) (p : K[X])

variable (μ : K)

/-- `L_λ(U) = U′ p(x) + λ U p′(x)`. -/
noncomputable def LopS (U : E) : E := U′ * aeval x p + algebraMap K E μ * U * aeval x (derivative p)

lemma Lop_addS (U V : E) : LopS x p μ (U + V) = LopS x p μ U + LopS x p μ V := by
  unfold LopS; rw [map_add]; ring

/-- The Hermite decomposition of `G` with denominator `D` (any polynomial part). -/
def DecompS (G : E) (D : K[X]) : Prop :=
  ∃ (W B₀ : K[X]) (R : E), SimplePartK x p R D ∧
    G = LopS x p μ (aeval x W / aeval x D) + aeval x B₀ + R

variable {x p μ}

variable (hne : ∀ Q : K[X], Q ≠ 0 → aeval x Q ≠ 0)
include hne

lemma decomp_monoS {G : E} {D D' : K[X]} (hD' : D' ≠ 0) (h : DecompS x p μ G D) (hDD : D ∣ D') :
    DecompS x p μ G D' := by
  obtain ⟨W, B₀, R, hR, rfl⟩ := h
  obtain ⟨Q, rfl⟩ := hDD
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hD'
  refine ⟨W * Q, B₀, R, simplePart_monoK hR (dvd_mul_right _ _), ?_⟩
  rw [map_mul, map_mul, mul_div_mul_right _ _ (hne Q hQ)]

omit hne in
lemma decomp_addS {G₁ G₂ : E} {D : K[X]} (h₁ : DecompS x p μ G₁ D)
    (h₂ : DecompS x p μ G₂ D) : DecompS x p μ (G₁ + G₂) D := by
  obtain ⟨W₁, B₁, R₁, hR₁, rfl⟩ := h₁
  obtain ⟨W₂, B₂, R₂, hR₂, rfl⟩ := h₂
  refine ⟨W₁ + W₂, B₁ + B₂, R₁ + R₂, simplePart_addK hR₁ hR₂, ?_⟩
  rw [map_add, add_div, Lop_addS, map_add]; ring

omit hne in
/-- **The polynomial case.** -/
lemma decomp_polyS (A : K[X]) : DecompS x p μ (aeval x A) 1 :=
  ⟨0, A, 0, simplePart_zeroK 1, by simp [LopS]⟩

end Hermite


section Main

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] [Differential K]
variable {E : Type*} [Field E] [CharZero E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
variable {x : E} {p : K[X]} {μ : K}
variable (hC : ∀ c : K, c′ = 0)
variable (hne : ∀ Q : K[X], Q ≠ 0 → aeval x Q ≠ 0) (hx : x′ = 1) (hsq : Squarefree p)
  (hμ : ∀ k : ℕ, μ ≠ k + 1)
include hC hne hx

/-- `L_μ(h/(x − r)^j)`. -/
lemma Lop_powS (r h : K) (j : ℕ) :
    LopS x p μ ((algebraMap K E (h)) / (x - (algebraMap K E (r))) ^ j) =
      (algebraMap K E (h)) * (-(j : E) * aeval x p +
        algebraMap K E μ * (x - (algebraMap K E (r))) * aeval x (derivative p)) /
        (x - (algebraMap K E (r))) ^ (j + 1) := by
  have hr := x_sub_neK hC hne hx r
  unfold LopS
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
lemma decomp_LopS (W D : K[X]) : DecompS x p μ (LopS x p μ (aeval x W / aeval x D)) D :=
  ⟨W, 0, 0, simplePart_zeroK D, by simp⟩

include hsq hμ

/-- **The pure-power case** `A/(x − r)^k`. -/
lemma decomp_powS (r : K) (k : ℕ) : ∀ (A : K[X]),
    DecompS x p μ (aeval x A / (x - (algebraMap K E (r))) ^ k) ((X - C r) ^ k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro A
  rcases k with _ | k
  · simpa using decomp_polyS (x := x) (p := p) (μ := μ) A
  · have decomp_powS' := fun j (hj : j < k + 1) ↦ ih j hj
    have hr := x_sub_neK hC hne hx r
    have hDk : (X - C r) ^ (k + 1) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero r)
    have hdvd : (X - C r) ^ k ∣ (X - C r) ^ (k + 1) := pow_dvd_pow _ (Nat.le_succ k)
    set lam := A.eval r
    set A₁ := A /ₘ (X - C r)
    have hA : A = C lam + (X - C r) * A₁ := by
      have := modByMonic_add_div A (X - C r)
      rw [modByMonic_X_sub_C_eq_C_eval] at this
      exact this.symm
    have hsplit : aeval x A / (x - (algebraMap K E (r))) ^ (k + 1) =
        (algebraMap K E (lam)) / (x - (algebraMap K E (r))) ^ (k + 1) +
          aeval x A₁ / (x - (algebraMap K E (r))) ^ k := by
      conv_lhs => rw [hA]
      simp only [map_add, map_mul, aeval_C, aeval_linK hC hne hx]
      field_simp
      ring
    rw [hsplit]
    refine decomp_addS ?_ (decomp_monoS hne hDk (decomp_powS' k (Nat.lt_succ_self k) A₁) hdvd)
    have hlin := aeval_linK hC hne hx r
    by_cases hpr : p.eval r = 0
    · -- a branch point
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
      have hk2 : ((k : K) + 1 - μ) ≠ 0 := fun h0 ↦ hμ k (by linear_combination -h0)
      set h : K := -lam / (((k : K) + 1 - μ) * (derivative p).eval r)
      set M : K[X] := C lam + C (h * (k + 1)) * q - C (h * μ) * derivative p
      have hh : h * (((k : K) + 1 - μ) * (derivative p).eval r) = -lam := by
        simp only [h]; field_simp
      have hMr : M.eval r = 0 := by
        simp only [M, eval_add, eval_sub, eval_mul, eval_C, hqr]
        linear_combination hh
      set P₁ := M /ₘ (X - C r)
      have hM : M = (X - C r) * P₁ := by
        have := modByMonic_add_div M (X - C r)
        rw [modByMonic_X_sub_C_eq_C_eval, hMr, C_0, zero_add] at this
        exact this.symm
      have hid : (algebraMap K E (lam)) / (x - (algebraMap K E (r))) ^ (k + 1) =
          LopS x p μ (aeval x (C h) / aeval x ((X - C r) ^ (k + 1))) +
            aeval x P₁ / (x - (algebraMap K E (r))) ^ k := by
        rw [aeval_C, map_pow, hlin, Lop_powS hC hne hx]
        have e1 := congrArg (aeval x) hM
        have e2 := congrArg (aeval x) hpq
        simp only [M, map_add, map_sub, map_mul, aeval_C, hlin] at e1 e2
        have eP : aeval x P₁ = ((algebraMap K E (lam)) + algebraMap K E (h * (k + 1)) * aeval x q -
            (algebraMap K E (h * μ)) * aeval x (derivative p)) / (x - (algebraMap K E (r))) := by
          rw [eq_div_iff hr]; simp only [map_mul, map_add, map_natCast, map_one] at e1 ⊢; linear_combination -e1
        rw [eP, e2]
        simp only [map_mul, map_add, map_natCast, map_one]
        field_simp
        push_cast
        ring
      rw [hid]
      exact decomp_addS (decomp_LopS _ _)
        (decomp_monoS hne hDk (decomp_powS' k (Nat.lt_succ_self k) P₁) hdvd)
    · rcases k with _ | k
      · refine ⟨0, 0, (algebraMap K E (lam)) / (x - (algebraMap K E (r))) ^ (0 + 1),
          ⟨{r}, fun _ ↦ lam, by simp [IsRoot, hpr], by simp⟩, ?_⟩
        simp [LopS]
      · set h : K := -lam / ((k + 1 : K) * p.eval r)
        have hk1 : (k + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        set M : K[X] := C lam + C (h * (k + 1)) * p - C (h * μ) * ((X - C r) * derivative p)
        have hpr' : p.eval r ≠ 0 := hpr
        have hh : h * ((k + 1 : K) * p.eval r) = -lam := by
          simp only [h]; field_simp
        have hMr : M.eval r = 0 := by
          simp only [M, eval_add, eval_sub, eval_mul, eval_C, eval_X, sub_self, zero_mul, mul_zero,
            sub_zero]
          linear_combination hh
        set P₁ := M /ₘ (X - C r)
        have hM : M = (X - C r) * P₁ := by
          have := modByMonic_add_div M (X - C r)
          rw [modByMonic_X_sub_C_eq_C_eval, hMr, C_0, zero_add] at this
          exact this.symm
        have hid : (algebraMap K E (lam)) / (x - (algebraMap K E (r))) ^ (k + 1 + 1) =
            LopS x p μ (aeval x (C h * (X - C r)) / aeval x ((X - C r) ^ (k + 1 + 1))) +
              aeval x P₁ / (x - (algebraMap K E (r))) ^ (k + 1) := by
          have e0 : aeval x (C h * (X - C r)) / aeval x ((X - C r) ^ (k + 1 + 1)) =
              (algebraMap K E (h)) / (x - (algebraMap K E (r))) ^ (k + 1) := by
            rw [map_mul, aeval_C, map_pow, hlin]
            field_simp
            ring
          rw [e0, Lop_powS hC hne hx]
          have e1 := congrArg (aeval x) hM
          simp only [M, map_add, map_sub, map_mul, aeval_C, hlin] at e1
          have eP : aeval x P₁ = ((algebraMap K E (lam)) + algebraMap K E (h * (k + 1)) * aeval x p -
              (algebraMap K E (h * μ)) * ((x - (algebraMap K E (r))) * aeval x (derivative p))) /
                (x - (algebraMap K E (r))) := by
            rw [eq_div_iff hr]; simp only [map_mul, map_add, map_natCast, map_one] at e1 ⊢; linear_combination -e1
          rw [eP]
          simp only [map_mul, map_add, map_natCast, map_one]
          field_simp
          push_cast
          ring
        rw [hid]
        exact decomp_addS (decomp_LopS _ _)
          (decomp_monoS hne hDk (decomp_powS' (k + 1) (Nat.lt_succ_self _) P₁) hdvd)

/-- **Existence of the superelliptic Hermite decomposition** for a split denominator. -/
theorem hermite_existsS (n : ℕ) : ∀ (D : K[X]), D.natDegree = n → D ≠ 0 → D.Splits →
    ∀ A : K[X], DecompS x p μ (aeval x A / aeval x D) D := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D hn hD hsplit A
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [← hn] at h0
    obtain ⟨d, rfl⟩ : ∃ d, D = C d := ⟨D.coeff 0, eq_C_of_natDegree_eq_zero h0⟩
    have hd : d ≠ 0 := by rintro rfl; exact hD (by simp)
    have h1 := decomp_polyS (x := x) (p := p) (μ := μ) (C (1 / d) * A)
    have := decomp_monoS hne hD h1 (by exact one_dvd _)
    convert this using 1
    simp only [aeval_C, map_mul, map_one, div_one]
    push_cast
    field_simp
  · obtain ⟨r, hr⟩ := hsplit.exists_eval_eq_zero (by
      rw [degree_eq_natDegree hD, hn]; exact_mod_cast hpos.ne')
    obtain ⟨D₂, hDD, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd D hD r
    set k := D.rootMultiplicity r
    have hD₂ : D₂ ≠ 0 := by rintro rfl; rw [mul_zero] at hDD; exact hD hDD
    have hcop : IsCoprime ((X - C r) ^ k) D₂ :=
      ((Polynomial.irreducible_X_sub_C r).coprime_iff_not_dvd.mpr hnd).pow_left
    obtain ⟨a, b, hab⟩ := hcop
    have hk : 1 ≤ k := (rootMultiplicity_pos hD).mpr hr
    have hdeg₂ : D₂.natDegree < n := by
      have := congrArg natDegree hDD
      rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero r)) hD₂, natDegree_pow,
        natDegree_X_sub_C, mul_one] at this
      omega
    have hsplit₂ : D₂.Splits := hsplit.of_dvd hD (by rw [hDD]; exact dvd_mul_left _ _)
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
    refine decomp_addS ?_ ?_
    · exact decomp_monoS hne hD (decomp_powS hC hne hx hsq hμ r k (A * b))
        (by rw [hDD]; exact dvd_mul_right _ _)
    · exact decomp_monoS hne hD (ih _ (by omega) D₂ rfl hD₂ hsplit₂ (A * a))
        (by rw [hDD]; exact dvd_mul_left _ _)

end Main

end HermiteS

end Differential
