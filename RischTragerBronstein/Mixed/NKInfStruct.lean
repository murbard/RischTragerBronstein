import RischTragerBronstein.Mixed.NKInfLead
import RischTragerBronstein.Mixed.IntBasisLogW

/-!
# The derivation at the single place at infinity of a non-constant curve

`S : CurveData C L` of weighted shape (single place at infinity), over a differential field `C`
with `x′ = η ∈ C` (a primitive level: `C = Fₘ`, `x = t`). For elements `wᵢ = Wᵢ(x, y)/Qᵢ(x)` of
distinct weights `vᵢ = wt(Wᵢ) − n deg Qᵢ ∈ (−n, 0]` with `wᵢ′ = ∑ⱼ (Pᵢⱼ/Rᵢ)(x) wⱼ`,
`deg Pᵢⱼ ≤ deg Rᵢ`, the limit `Λᵢⱼ = lim Pᵢⱼ/Rᵢ` at infinity satisfies (`nk_inf_struct`):

* `Λᵢⱼ ≠ 0 → vⱼ ≤ vᵢ` (triangular in the order of the weights);
* `Λᵢᵢ = βᵢ′/βᵢ + (j₀/n) c′/c`, `βᵢ = lc(b_{j₀})/lc(Qᵢ)` the leading coefficient of `wᵢ`,
  `c = lc(a₀)`;
* the expansion coefficients `Aᵢₖ` (`k < N`) along a branch `x = s⁻ᴺ` have independent rows and
  `A′ = Λ A` — so the limit system is gauge-trivial over the algebraic closure.

Along the branch the derivation is `δ + s d/ds` with `s = −(η/N) s^{N+1}`, which acts on the first
`N` coefficients as the coefficient derivation `δ`.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Laurent

variable {C K : Type*} [Field C] [CharZero C] [Field K] [Algebra C K]

/-- `P(s⁻ᴺ)/R(s⁻ᴺ) − lim P/R` starts at `sᴺ` when `deg P ≤ deg R`. -/
lemma lowerBd_infSub_div (N : ℕ) (hN : 0 < N) (P R : C[X]) (hR : R ≠ 0)
    (hPR : P.natDegree ≤ R.natDegree) :
    LowerBd (infSub (K := K) N P * (infSub (K := K) N R)⁻¹ -
      HahnSeries.C (algebraMap C K (P.coeff R.natDegree / R.leadingCoeff))) N := by
  set lam0 := P.coeff R.natDegree / R.leadingCoeff with hlam
  have hR0 := infSub_ne_zero (K := K) N hN R hR
  have e : infSub (K := K) N P * (infSub (K := K) N R)⁻¹ -
      HahnSeries.C (algebraMap C K lam0) =
      infSub (K := K) N (P - Polynomial.C lam0 * R) * (infSub (K := K) N R)⁻¹ := by
    rw [map_sub, map_mul, SuperData.infSub_C, sub_mul, mul_assoc, mul_inv_cancel₀ hR0, mul_one]
  rw [e]
  by_cases h0 : P - Polynomial.C lam0 * R = 0
  · rw [h0, map_zero, zero_mul]; exact lowerBd_zero _
  have hdeg : (P - Polynomial.C lam0 * R).natDegree < R.natDegree := by
    have hlc : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR
    have hR1 : 0 < R.natDegree ∨ R.natDegree = 0 := by omega
    rcases hR1 with hR1 | hR1
    · refine lt_of_le_of_ne ?_ ?_
      · refine (natDegree_sub_le _ _).trans (max_le hPR ?_)
        exact (natDegree_C_mul_le _ _)
      · intro heq
        have hc : (P - Polynomial.C lam0 * R).coeff R.natDegree = 0 := by
          rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hlam, ← Polynomial.leadingCoeff, div_mul_cancel₀ _ hlc, sub_self]
        rw [← heq] at hc
        exact h0 (leadingCoeff_eq_zero.mp hc)
    · exfalso
      apply h0
      have hP0 : P.natDegree = 0 := by omega
      rw [eq_C_of_natDegree_eq_zero hP0, eq_C_of_natDegree_eq_zero hR1, hlam, hR1, ← C_mul,
        Polynomial.leadingCoeff, hR1, div_mul_cancel₀ _ (by rwa [Polynomial.leadingCoeff, hR1] at hlc),
        sub_self]
  have h1 := order_infSub (K := K) N hN _ h0
  have hinv := lowerBd_inv (infSub (K := K) N R) hR0
  rw [order_infSub N hN R hR] at hinv
  have h2 : LowerBd (infSub (K := K) N (P - Polynomial.C lam0 * R))
      (-((N : ℤ) * (P - Polynomial.C lam0 * R).natDegree)) := by
    intro k hk
    exact HahnSeries.coeff_eq_zero_of_lt_order (by rw [h1]; exact hk)
  have := h2.mul hinv
  refine this.mono ?_
  have : (P - Polynomial.C lam0 * R).natDegree + 1 ≤ R.natDegree := hdeg
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  push_cast
  nlinarith

end Laurent

section Speed

variable {C K : Type*} [Field C] [CharZero C] [Field K] [CharZero K] [Algebra C K] [Differential C]
  [Differential K]

/-- The speed of the branch `x = s⁻ᴺ` for `x′ = η`: `−(η/N) s^{N+1}`. -/
noncomputable def infSpeed (η : C) (N : ℕ) : LaurentSeries K :=
  single ((N : ℤ) + 1) (-(algebraMap C K η) / N)

lemma dS_infSpeed (η : C) (N : ℕ) (hN : 0 < N) :
    dS (infSpeed (K := K) η N) (single (-(N : ℤ)) 1) =
      substHom (single (-(N : ℤ)) (1 : K)) (Polynomial.C η) := by
  have hN' : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  rw [SuperData.substHom_C, dS_apply, coefDeriv_single, Differential.deriv.map_one_eq_zero,
    HahnSeries.single_eq_zero, zero_add]
  have hd : derivative K (single (-(N : ℤ)) (1 : K)) = single (-(N : ℤ) - 1) (-(N : K)) := by
    have := Differential.derivation_single (K := K) (-(N : ℤ))
    rw [LaurentSeries.derivation_apply] at this
    rw [this]; push_cast; rfl
  rw [hd, infSpeed, HahnSeries.single_mul_single]
  have e : (N : ℤ) + 1 + (-(N : ℤ) - 1) = 0 := by ring
  rw [e, ← HahnSeries.C_apply]
  congr 1
  field_simp

lemma lowerBd_infSpeed (η : C) (N : ℕ) : LowerBd (infSpeed (K := K) η N) ((N : ℤ) + 1) :=
  lowerBd_single _ _

end Speed

section Lead

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Order and leading coefficient of an element above infinity** (single place at infinity):
for `z Q(x) = W(x, y)`, `n · ord z = −N (wt W − n deg Q)` and the leading coefficient is
`(lc b_{j₀}/lc Q) γ^{j₀}`. -/
theorem embG_lead_inf (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d) (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0) (z : C⟮S.x⟯⟮S.y⟯) (W : C[X][X]) (Q : C[X])
    (hQ : Q ≠ 0) (hWQ : (z : L) * aeval S.x Q = S.evXY W) (hW0 : W ≠ 0)
    (hWn : W.natDegree < n) :
    S.embG (infSub N) (infSub_injective N hN) r hr z ≠ 0 ∧
      (n : ℤ) * (S.embG (infSub N) (infSub_injective N hN) r hr z).order =
        -((N : ℤ) * ((wtW n d W : ℤ) - n * Q.natDegree)) ∧
      ∃ j0 < n, W.coeff j0 ≠ 0 ∧ wtW n d W = n * (W.coeff j0).natDegree + j0 * d ∧
        (S.embG (infSub N) (infSub_injective N hN) r hr z).leadingCoeff =
          algebraMap C K ((W.coeff j0).leadingCoeff / Q.leadingCoeff) * r.leadingCoeff ^ j0 := by
  obtain ⟨j0, hj0n, hj0, hwt, hne, hord, hlc⟩ := eval_lead_inf S.F S.monic n d N hn hn0 hN ha0 hd hw
    hcop r hr W hW0 hWn
  have he := S.eval_W_branch (infSub N) (infSub_injective N hN) r hr z W Q hWQ
  set E := S.embG (infSub N) (infSub_injective N hN) r hr z with hE
  have hQ0 := infSub_ne_zero (K := K) N hN Q hQ
  have hE0 : E ≠ 0 := fun h ↦ hne (by rw [he, h, zero_mul])
  refine ⟨hE0, ?_, j0, hj0n, hj0, hwt, ?_⟩
  · rw [he, HahnSeries.order_mul hE0 hQ0, order_infSub N hN Q hQ] at hord
    linear_combination hord
  · rw [he, HahnSeries.leadingCoeff_mul, leadingCoeff_infSub N hN Q hQ] at hlc
    have hlQ : algebraMap C K Q.leadingCoeff ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap C K).injective).mpr (leadingCoeff_ne_zero.mpr hQ)
    rw [map_div₀, div_mul_eq_mul_div, eq_div_iff hlQ, ← hlc]

end CurveData

end Lead

section Gauge

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential C] [Differential K]

/-- **Non-degeneracy of a gauge-trivial limit system**: if the rows of `A` (over a differential
extension `K`) are independent and `A′ = Λ A`, then no non-zero solution `c` over `C` of
`cⱼ′ + ∑ᵢ Λᵢⱼ cᵢ = 0` has `η c` in the image of the same operator, unless `η` is a derivative in
`K`. -/
theorem nondeg_of_gauge (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
    {ι : Type*} [Fintype ι] (Λ : ι → ι → C) (A : ι → ℤ → K) (p : ℤ → Prop)
    (hind : ∀ c : ι → K, (∀ k, p k → ∑ i, c i * A i k = 0) → ∀ i, c i = 0)
    (hA : ∀ i k, p k → (A i k)′ = ∑ j, algebraMap C K (Λ i j) * A j k)
    (η : C) (hη : ∀ a : K, a′ ≠ algebraMap C K η)
    (c : ι → C) (hc : c ≠ 0) (hhom : ∀ j, (c j)′ + ∑ i, Λ i j * c i = 0) :
    ¬∃ y : ι → C, ∀ j, (y j)′ + ∑ i, Λ i j * y i = η * c j := by
  classical
  rintro ⟨y, hy⟩
  have hvd : ∀ (z : ι → C) (g : ι → C), (∀ j, (z j)′ + ∑ i, Λ i j * z i = g j) → ∀ k, p k →
      (∑ i, algebraMap C K (z i) * A i k)′ = ∑ j, algebraMap C K (g j) * A j k := by
    intro z g hz k hk
    have hg : ∀ j, g j = (z j)′ + ∑ i, Λ i j * z i := fun j ↦ (hz j).symm
    simp only [hg, map_sum, Derivation.leibniz, smul_eq_mul, hK, hA _ k hk, map_add, map_mul,
      add_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun i _ ↦ by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- a coefficient where the combination does not vanish
  have hcK : (fun i ↦ algebraMap C K (c i)) ≠ 0 := by
    intro h
    apply hc
    funext i
    have := congrFun h i
    exact (algebraMap C K).injective (by simpa using this)
  have : ∃ k, p k ∧ ∑ i, algebraMap C K (c i) * A i k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hcK (funext (hind _ hcon))
  obtain ⟨k, hk, hv0⟩ := this
  have hv' := hvd c 0 (fun j ↦ by rw [hhom j]; rfl) k hk
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at hv'
  have hu' := hvd y (fun j ↦ η * c j) hy k hk
  apply hη ((∑ i, algebraMap C K (y i) * A i k) / ∑ i, algebraMap C K (c i) * A i k)
  rw [Derivation.leibniz_div, hv', hu', smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_zero, sub_zero]
  simp only [map_mul, mul_assoc, ← Finset.mul_sum]
  field_simp

end Gauge

namespace CurveData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]

variable (S : CurveData C L) (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **Along a branch above infinity the derivation acts on the first `N` coefficients as the
coefficient derivation.** -/
lemma coeff_embG_deriv_inf (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0) (z : C⟮S.x⟯⟮S.y⟯)
    (hz : LowerBd (S.embG (infSub N) (infSub_injective N hN) r hr z) 0) (k : ℤ) (hk : k < N) :
    (S.embG (infSub N) (infSub_injective N hN) r hr
      ⟨(z : L)′, S.derivClosedXYW' (Polynomial.C η) hx z z.2⟩).coeff k =
      ((S.embG (infSub N) (infSub_injective N hN) r hr z).coeff k)′ := by
  have hd := S.embG_dSW' (Polynomial.C η) hx hK (infSpeed η N) (single (-(N : ℤ)) 1)
    (dS_infSpeed η N hN) (infSub N) (infSub_injective N hN)
    (fun P ↦ by rw [SuperData.infSub_eq_subst]) r hr (z : L) z.2
  simp only [Subtype.coe_eta] at hd
  rw [hd, dS_apply, HahnSeries.coeff_add, coeff_coefDeriv]
  have h2 := (lowerBd_infSpeed (K := K) η N).mul hz.derivative
  rw [h2 k (by omega), add_zero]

include hx hK in
/-- `γ′ = γ c′/(n c)` for the leading coefficient `γ` of a root above infinity (`γⁿ = −c`). -/
lemma deriv_root_lead (n : ℕ) (hn0 : 0 < n) (γ : K) (c : C) (hc : c ≠ 0)
    (hγ : γ ^ n = -algebraMap C K c) (j : ℕ) :
    (γ ^ j)′ = (j : K) * γ ^ j * algebraMap C K (c′ / (n * c)) := by
  have hn' : (n : K) ≠ 0 := by exact_mod_cast hn0.ne'
  have hcK : algebraMap C K c ≠ 0 := (map_ne_zero_iff _ (algebraMap C K).injective).mpr hc
  have hγ0 : γ ≠ 0 := by
    intro h0; rw [h0, zero_pow hn0.ne'] at hγ; exact hcK (neg_eq_zero.mp hγ.symm)
  have h1 : (γ ^ n)′ = -algebraMap C K c′ := by rw [hγ, map_neg, hK]
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at h1
  have hγ' : γ′ = γ * algebraMap C K (c′ / (n * c)) := by
    rw [map_div₀, map_mul, map_natCast]
    have hpow : γ ^ n = γ * γ ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    field_simp
    have h2 : (n : K) * γ ^ (n - 1) * γ′ * γ = -algebraMap C K c′ * γ := by rw [← h1]; ring
    have h3 : (n : K) * γ′ * γ ^ n = -algebraMap C K c′ * γ := by rw [hpow, ← h2]; ring
    rw [hγ] at h3
    linear_combination -h3
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, hγ']
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have : γ ^ j = γ ^ (j - 1) * γ := by rw [← pow_succ]; congr 1; omega
    rw [this]; ring

include hx hK in
/-- **The limit of the derivation matrix at the single place at infinity.** -/
theorem nk_inf_struct (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d) (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → C⟮S.x⟯⟮S.y⟯) (W : ι → C[X][X]) (Q : ι → C[X]) (hQ : ∀ i, Q i ≠ 0)
    (hWQ : ∀ i, (w i : L) * aeval S.x (Q i) = S.evXY (W i)) (hW0 : ∀ i, W i ≠ 0)
    (hWn : ∀ i, (W i).natDegree < n)
    (hwin : ∀ i, -(n : ℤ) < (wtW n d (W i) : ℤ) - n * (Q i).natDegree ∧
      (wtW n d (W i) : ℤ) - n * (Q i).natDegree ≤ 0)
    (hdist : ∀ i j, (wtW n d (W i) : ℤ) - n * (Q i).natDegree =
      (wtW n d (W j) : ℤ) - n * (Q j).natDegree → i = j)
    (R : ι → C[X]) (hR : ∀ i, R i ≠ 0) (P : ι → ι → C[X])
    (hPR : ∀ i j, (P i j).natDegree ≤ (R i).natDegree)
    (hD : ∀ i, (w i : L)′ * aeval S.x (R i) = ∑ j, aeval S.x (P i j) * (w j : L)) :
    (∀ i j, (P i j).coeff (R i).natDegree / (R i).leadingCoeff ≠ 0 →
      (wtW n d (W j) : ℤ) - n * (Q j).natDegree ≤ (wtW n d (W i) : ℤ) - n * (Q i).natDegree) ∧
    (∀ i, ∃ j0 < n, (W i).coeff j0 ≠ 0 ∧
      wtW n d (W i) = n * ((W i).coeff j0).natDegree + j0 * d ∧
      (P i i).coeff (R i).natDegree / (R i).leadingCoeff =
        (((W i).coeff j0).leadingCoeff / (Q i).leadingCoeff)′ /
          (((W i).coeff j0).leadingCoeff / (Q i).leadingCoeff) +
        (j0 : C) * ((S.F.coeff 0).leadingCoeff′ / (n * (S.F.coeff 0).leadingCoeff))) ∧
    ∃ A : ι → ℤ → K, (∀ c : ι → K, (∀ k : ℤ, 0 ≤ k → k < N → ∑ i, c i * A i k = 0) →
        ∀ i, c i = 0) ∧
      ∀ i, ∀ k : ℤ, 0 ≤ k → k < N →
        (A i k)′ = ∑ j, algebraMap C K ((P i j).coeff (R i).natDegree / (R i).leadingCoeff) *
          A j k := by
  classical
  set Λ : ι → ι → C := fun i j ↦ (P i j).coeff (R i).natDegree / (R i).leadingCoeff with hΛ
  set v : ι → ℤ := fun i ↦ (wtW n d (W i) : ℤ) - n * (Q i).natDegree with hv
  set E : ι → LaurentSeries K := fun i ↦ S.embG (infSub N) (infSub_injective N hN) r hr (w i)
    with hE
  have hlead := fun i ↦ S.embG_lead_inf n d hn hn0 ha0 hd hw hcop N hN r hr (w i) (W i) (Q i) (hQ i)
    (hWQ i) (hW0 i) (hWn i)
  have hE0 : ∀ i, E i ≠ 0 := fun i ↦ (hlead i).1
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  -- the orders `oᵢ ∈ [0, N)`
  set o : ι → ℤ := fun i ↦ (E i).order with ho
  have hno : ∀ i, (n : ℤ) * o i = -((N : ℤ) * v i) := fun i ↦ (hlead i).2.1
  have ho0 : ∀ i, 0 ≤ o i := fun i ↦ by
    have := hno i; have := (hwin i).2; nlinarith
  have hoN : ∀ i, o i < N := fun i ↦ by
    have := hno i; have := (hwin i).1; nlinarith
  have hoinj : ∀ i j, o i = o j → i = j := fun i j hij ↦ by
    refine hdist i j ?_
    have h1 := hno i; have h2 := hno j
    rw [hij] at h1
    have : (N : ℤ) * v i = N * v j := by linarith
    exact mul_left_cancel₀ hNpos.ne' this
  have hvo : ∀ i j, v j ≤ v i ↔ o i ≤ o j := fun i j ↦ by
    have h1 := hno i; have h2 := hno j
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hLB : ∀ i, LowerBd (E i) 0 := fun i k hk ↦
    HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk (ho0 i))
  have hlc : ∀ i, (E i).coeff (o i) ≠ 0 := fun i ↦ by
    rw [ho]; dsimp only
    rw [← HahnSeries.leadingCoeff_eq]
    exact HahnSeries.leadingCoeff_ne_zero.mpr (hE0 i)
  have hbelow : ∀ i k, k < o i → (E i).coeff k = 0 := fun i k hk ↦
    HahnSeries.coeff_eq_zero_of_lt_order hk
  -- the key identity
  have hkey : ∀ i, ∀ k : ℤ, 0 ≤ k → k < N →
      ((E i).coeff k)′ = ∑ j, algebraMap C K (Λ i j) * (E j).coeff k := by
    intro i k hk0 hkN
    have hmem := S.derivClosedXYW' (Polynomial.C η) hx (w i) (w i).2
    have hid : (⟨(w i : L)′, hmem⟩ : C⟮S.x⟯⟮S.y⟯) * ⟨aeval S.x (R i), S.aeval_mem _⟩ =
        ∑ j, ⟨aeval S.x (P i j), S.aeval_mem _⟩ * w j := Subtype.ext (by
      push_cast
      exact hD i)
    have hemb := congrArg (S.embG (infSub N) (infSub_injective N hN) r hr) hid
    rw [map_mul, map_sum, S.embG_polyX] at hemb
    simp only [map_mul, S.embG_polyX] at hemb
    have hR0 := infSub_ne_zero (K := K) N hN (R i) (hR i)
    have hdiv : S.embG (infSub N) (infSub_injective N hN) r hr ⟨(w i : L)′, hmem⟩ =
        ∑ j, (infSub N (P i j) * (infSub N (R i))⁻¹) * E j := by
      have : S.embG (infSub N) (infSub_injective N hN) r hr ⟨(w i : L)′, hmem⟩ =
          (∑ j, infSub N (P i j) * E j) * (infSub N (R i))⁻¹ := by
        rw [← hemb, mul_assoc, mul_inv_cancel₀ hR0, mul_one]
      rw [this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hL := S.coeff_embG_deriv_inf η hx hK N hN r hr (w i) (hLB i) k hkN
    rw [← hL, hdiv, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hρ := lowerBd_infSub_div (K := K) N hN (P i j) (R i) (hR i) (hPR i j)
    have e : infSub N (P i j) * (infSub N (R i))⁻¹ * E j =
        HahnSeries.C (algebraMap C K (Λ i j)) * E j +
        (infSub N (P i j) * (infSub N (R i))⁻¹ -
          HahnSeries.C (algebraMap C K (Λ i j))) * E j := by ring
    rw [e, HahnSeries.coeff_add, LaurentSeries.coeff_C_mul, (hρ.mul (hLB j)) k (by omega), add_zero]
  -- triangularity
  have htri : ∀ i j, Λ i j ≠ 0 → o i ≤ o j := by
    intro i j hij
    by_contra hcon
    have hlt : o j < o i := by push Not at hcon; exact hcon
    -- the nonzero entry of least order
    set J := Finset.univ.filter fun j ↦ Λ i j ≠ 0 with hJ
    have hJne : J.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
    obtain ⟨j1, hj1J, hj1min⟩ := J.exists_min_image o hJne
    have hj1 : Λ i j1 ≠ 0 := (Finset.mem_filter.mp hj1J).2
    have hle : o j1 ≤ o j := hj1min j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
    have h := hkey i (o j1) (ho0 j1) (hoN j1)
    rw [hbelow i (o j1) (by omega), Derivation.map_zero (Differential.deriv (R := K)),
      Finset.sum_eq_single j1] at h
    · exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap C K).injective).mpr hj1) (hlc j1) h.symm
    · intro j2 _ hj2
      by_cases h2 : Λ i j2 = 0
      · rw [h2, map_zero, zero_mul]
      · have h3 : o j1 ≤ o j2 := hj1min j2 (by simp [hJ, h2])
        have h4 : o j1 < o j2 := lt_of_le_of_ne h3 fun h5 ↦ hj2 (hoinj _ _ h5).symm
        rw [hbelow j2 _ h4, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j1) h
  -- the expansion matrix
  refine ⟨fun i j hij ↦ (hvo i j).mpr (htri i j hij), ?_, fun i k ↦ (E i).coeff k, ?_,
    fun i k hk0 hkN ↦ hkey i k hk0 hkN⟩
  · -- the diagonal
    intro i
    obtain ⟨-, -, j0, hj0n, hj0, hwt, hlcE⟩ := hlead i
    refine ⟨j0, hj0n, hj0, hwt, ?_⟩
    obtain ⟨β, hβ⟩ : ∃ β : C, β = ((W i).coeff j0).leadingCoeff / (Q i).leadingCoeff := ⟨_, rfl⟩
    rw [← hβ] at hlcE ⊢
    have hβ0 : β ≠ 0 := hβ ▸ div_ne_zero (leadingCoeff_ne_zero.mpr hj0) (leadingCoeff_ne_zero.mpr (hQ i))
    set c : C := (S.F.coeff 0).leadingCoeff with hc
    have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr ha0
    have hγ := root_lead_inf S.F S.monic n d N hn hn0 hN ha0 hd hw r hr
    have h := hkey i (o i) (ho0 i) (hoN i)
    rw [Finset.sum_eq_single i] at h
    · have hEi : (E i).coeff (o i) = algebraMap C K β * r.leadingCoeff ^ j0 := by
        rw [← hlcE, HahnSeries.leadingCoeff_eq]
      rw [hEi, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hK,
        S.deriv_root_lead η hx hK n hn0 r.leadingCoeff c hc0 hγ j0] at h
      have hγ0 : r.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr
        (root_order_inf S.F S.monic n d N hn hn0 hN ha0 hd hw r hr).1
      have hβK : algebraMap C K β ≠ 0 := (map_ne_zero_iff _ (algebraMap C K).injective).mpr hβ0
      apply (algebraMap C K).injective
      have hpow : r.leadingCoeff ^ j0 ≠ 0 := pow_ne_zero _ hγ0
      have h' : algebraMap C K (Λ i i) * (algebraMap C K β * r.leadingCoeff ^ j0) =
          (algebraMap C K (β′ / β + (j0 : C) * (c′ / (n * c)))) *
            (algebraMap C K β * r.leadingCoeff ^ j0) := by
        rw [← h]
        simp only [map_add, map_div₀, map_mul, map_natCast]
        field_simp
        ring
      exact mul_right_cancel₀ (mul_ne_zero hβK hpow) h'
    · intro j _ hji
      by_cases h2 : Λ i j = 0
      · rw [h2, map_zero, zero_mul]
      · have h3 := htri i j h2
        have h4 : o i < o j := lt_of_le_of_ne h3 fun h5 ↦ hji (hoinj _ _ h5).symm
        rw [hbelow j _ h4, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  · -- independence of the rows
    intro c hc
    by_contra hcon
    push Not at hcon
    obtain ⟨i1, hi1⟩ := hcon
    set I := Finset.univ.filter fun i ↦ c i ≠ 0 with hI
    have hIne : I.Nonempty := ⟨i1, by simp [hI, hi1]⟩
    obtain ⟨i0, hi0I, hi0min⟩ := I.exists_min_image o hIne
    have hi0 : c i0 ≠ 0 := (Finset.mem_filter.mp hi0I).2
    have h := hc (o i0) (ho0 i0) (hoN i0)
    rw [Finset.sum_eq_single i0] at h
    · exact mul_ne_zero hi0 (hlc i0) h
    · intro i2 _ hi2
      by_cases h2 : c i2 = 0
      · rw [h2, zero_mul]
      · have h3 : o i0 ≤ o i2 := hi0min i2 (by simp [hI, h2])
        have h4 : o i0 < o i2 := lt_of_le_of_ne h3 fun h5 ↦ hi2 (hoinj _ _ h5).symm
        show c i2 * (E i2).coeff (o i0) = 0
        rw [hbelow i2 _ h4, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i0) h

end CurveData

end Curves
