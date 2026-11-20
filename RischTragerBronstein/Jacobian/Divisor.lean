import RischTragerBronstein.Jacobian.HFun
import RischTragerBronstein.Jacobian.KernelTorsion

/-!
# Effective divisors with distinct abscissae, and the structure lemma

An effective divisor is a list `Γ` of triples `(x_Q, y_Q, k_Q)` (point `Q = (x_Q, y_Q)` with
multiplicity `k_Q`) whose abscissae are pairwise distinct. `Vanishes f ψ Γ`: `ψ` vanishes on `Γ`;
`wpoly Γ = ∏ (x − x_Q)^{k_Q}` has degree `deg Γ = ∑ k_Q`.

`structure_lemma` (over a field, `deg f = 2g + 1`): if `γ ≠ 0` has pole order `≤ deg Γ` and
vanishes on `Γ`, then every `χ` with pole order `≤ 2g + deg Γ` vanishing on `Γ` and at the `g`
points `σPᵢ = (xᵢ, −yᵢ)` (abscissae distinct and not on `Γ`) is `c · u · γ`, `u = ∏ (x − xᵢ)`.
-/

open Polynomial

namespace Jac

variable {R : Type*} [CommRing R]

/-- An effective divisor: points with multiplicities. -/
abbrev EDiv (R : Type*) := List (R × R × ℕ)

/-- `ψ` vanishes on the divisor `Γ`. -/
def Vanishes (f : R[X]) (ψ : R[X] × R[X]) (Γ : EDiv R) : Prop :=
  ∀ q ∈ Γ, VanishAt f ψ.1 ψ.2 q.1 q.2.1 q.2.2

/-- The degree of a divisor. -/
def edeg (Γ : EDiv R) : ℕ := (Γ.map fun q ↦ q.2.2).sum

/-- The conjugate divisor. -/
def econj (Γ : EDiv R) : EDiv R := Γ.map fun q ↦ (q.1, -q.2.1, q.2.2)

/-- `∏ (x − x_Q)^{k_Q}`. -/
noncomputable def wpoly (Γ : EDiv R) : R[X] := (Γ.map fun q ↦ (X - C q.1) ^ q.2.2).prod

/-- The points lie on the curve and are not branch points. -/
def OnCurve (f : R[X]) (Γ : EDiv R) : Prop :=
  ∀ q ∈ Γ, IsUnit (2 * q.2.1) ∧ q.2.1 ^ 2 = f.eval q.1

lemma edeg_econj (Γ : EDiv R) : edeg (econj Γ) = edeg Γ := by
  simp [edeg, econj, Function.comp_def]

lemma wpoly_econj (Γ : EDiv R) : wpoly (econj Γ) = wpoly Γ := by
  simp [wpoly, econj, Function.comp_def]

lemma Vanishes.hconj {f : R[X]} {ψ : R[X] × R[X]} {Γ : EDiv R} (h : Vanishes f ψ Γ) :
    Vanishes f (hconj ψ) (econj Γ) := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  exact (h q' hq').hconj

lemma OnCurve.econj {f : R[X]} {Γ : EDiv R} (h : OnCurve f Γ) : OnCurve f (econj Γ) := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  obtain ⟨h1, h2⟩ := h q' hq'
  refine ⟨?_, by simpa using h2⟩
  simp only [mul_neg]; exact h1.neg

lemma wpoly_monic (Γ : EDiv R) : (wpoly Γ).Monic := by
  unfold wpoly
  induction Γ with
  | nil => simp
  | cons q Γ ih =>
    rw [List.map_cons, List.prod_cons]
    exact ((monic_X_sub_C _).pow _).mul ih

lemma natDegree_wpoly [IsDomain R] (Γ : EDiv R) : (wpoly Γ).natDegree = edeg Γ := by
  unfold wpoly edeg
  induction Γ with
  | nil => simp
  | cons q Γ ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons,
      Monic.natDegree_mul ((monic_X_sub_C _).pow _) (by exact wpoly_monic Γ), natDegree_pow,
      natDegree_X_sub_C, mul_one, ih]

section Field

variable {k : Type*} [Field k]

/-- `wpoly Γ` divides every polynomial divisible by each `(x − x_Q)^{k_Q}` (distinct `x_Q`). -/
lemma wpoly_dvd {Γ : EDiv k} (hΓ : (Γ.map Prod.fst).Nodup) {P : k[X]}
    (h : ∀ q ∈ Γ, (X - C q.1) ^ q.2.2 ∣ P) : wpoly Γ ∣ P := by
  unfold wpoly
  induction Γ with
  | nil => simp
  | cons q Γ ih =>
    rw [List.map_cons, List.nodup_cons] at hΓ
    rw [List.map_cons, List.prod_cons]
    refine IsCoprime.mul_dvd ?_ (h q List.mem_cons_self)
      (ih hΓ.2 fun q' hq' ↦ h q' (List.mem_cons_of_mem _ hq'))
    have hcop : ∀ L : EDiv k, (∀ q' ∈ L, q'.1 ≠ q.1) →
        IsCoprime ((X - C q.1) ^ q.2.2) (L.map fun q ↦ (X - C q.1) ^ q.2.2).prod := by
      intro L hL
      induction L with
      | nil => exact isCoprime_one_right
      | cons r L ihL =>
        rw [List.map_cons, List.prod_cons]
        refine IsCoprime.mul_right ?_ (ihL fun q' hq' ↦ hL q' (List.mem_cons_of_mem _ hq'))
        refine IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub ?_)
        exact (sub_ne_zero.mpr (hL r List.mem_cons_self).symm).isUnit
    exact hcop Γ fun q' hq' he ↦ hΓ.1 (he ▸ List.mem_map_of_mem hq')

lemma dvd_hnorm_of_vanishes {f : k[X]} {ψ : k[X] × k[X]} {Γ : EDiv k}
    (hΓ : (Γ.map Prod.fst).Nodup) (h : Vanishes f ψ Γ) : wpoly Γ ∣ hnorm f ψ :=
  wpoly_dvd hΓ fun q hq ↦ (h q hq).dvd_hnorm

lemma wpoly_dvd_of_vanish_both {f : k[X]} {ψ : k[X] × k[X]} {Γ : EDiv k}
    (hΓ : (Γ.map Prod.fst).Nodup) (hon : OnCurve f Γ) (h : Vanishes f ψ Γ)
    (h' : Vanishes f ψ (econj Γ)) : wpoly Γ ∣ ψ.1 ∧ wpoly Γ ∣ ψ.2 := by
  have hq : ∀ q ∈ Γ, (X - C q.1) ^ q.2.2 ∣ ψ.1 ∧ (X - C q.1) ^ q.2.2 ∣ ψ.2 := fun q hq ↦
    dvd_of_vanish_both (hon q hq).1 (h q hq)
      (h' (q.1, -q.2.1, q.2.2) (List.mem_map_of_mem hq))
  exact ⟨wpoly_dvd hΓ fun q h ↦ (hq q h).1, wpoly_dvd hΓ fun q h ↦ (hq q h).2⟩

/-- Pole bound of a quotient by a polynomial in `x`. -/
lemma PoleLE.of_hsmul {g : ℕ} {w : k[X]} (hw : w ≠ 0) {ψ : k[X] × k[X]} {N : ℕ}
    (h : PoleLE g (hsmul w ψ) N) : PoleLE g ψ (N - 2 * w.natDegree) := by
  obtain ⟨ha, hb⟩ := h
  simp only [hsmul] at ha hb
  constructor
  · by_cases h0 : ψ.1 = 0
    · simp [h0]
    rw [natDegree_mul hw h0] at ha; omega
  · rcases hb with hb | hb
    · left; exact (mul_eq_zero.mp hb).resolve_left hw
    · by_cases h0 : ψ.2 = 0
      · left; exact h0
      right; rw [natDegree_mul hw h0] at hb; omega

lemma eval_wpoly_ne_zero {Γ : EDiv k} {z : k} (h : ∀ q ∈ Γ, q.1 ≠ z) : (wpoly Γ).eval z ≠ 0 := by
  unfold wpoly
  induction Γ with
  | nil => simp
  | cons q Γ ih =>
    rw [List.map_cons, List.prod_cons, eval_mul]
    refine mul_ne_zero ?_ (ih fun q' hq' ↦ h q' (List.mem_cons_of_mem _ hq'))
    rw [eval_pow, eval_sub, eval_X, eval_C]
    exact pow_ne_zero _ (sub_ne_zero.mpr (h q List.mem_cons_self).symm)

/-- The value of `a + b y` at a point is the constant term of its jet. -/
lemma jet_coeff_zero {f a b V : k[X]} {x₀ Y₀ : k} {n : ℕ} (hV : IsBranch f x₀ Y₀ n V) :
    (jet a b x₀ V).coeff 0 = a.eval x₀ + b.eval x₀ * Y₀ := by
  simp only [jet, coeff_add, coeff_zero_eq_eval_zero, eval_mul, eval_comp, eval_add, eval_X,
    eval_C, zero_add]
  rw [← hV.1, coeff_zero_eq_eval_zero]

/-- **The structure lemma.** -/
theorem structure_lemma {f : k[X]} {g : ℕ} (hf : f.natDegree = 2 * g + 1) {Γ : EDiv k}
    (hΓ : (Γ.map Prod.fst).Nodup) (hon : OnCurve f Γ) {x y : Fin g → k}
    (hx : Function.Injective x) (hxΓ : ∀ i, ∀ q ∈ Γ, q.1 ≠ x i) (hy : ∀ i, IsUnit (2 * y i))
    (hyf : ∀ i, y i ^ 2 = f.eval (x i))
    {γ χ : k[X] × k[X]} (hγ0 : γ ≠ (0, 0)) (hγp : PoleLE g γ (edeg Γ)) (hγ : Vanishes f γ Γ)
    (hχp : PoleLE g χ (2 * g + edeg Γ)) (hχ : Vanishes f χ Γ)
    (hχσ : ∀ i, VanishAt f χ.1 χ.2 (x i) (-y i) 1) :
    ∃ c : k, χ = hsmul (C c * ∏ i, (X - C (x i))) γ := by
  classical
  have hfo : Odd f.natDegree := ⟨g, by omega⟩
  -- the norm of `γ` is `c₀ · wpoly Γ`
  have hN0 := hnorm_ne_zero hfo hγ0
  obtain ⟨q0, hq0⟩ := dvd_hnorm_of_vanishes hΓ hγ
  have hw0 : wpoly Γ ≠ 0 := (wpoly_monic Γ).ne_zero
  have hq00 : q0 ≠ 0 := by rintro rfl; rw [mul_zero] at hq0; exact hN0 hq0
  have hdegN : (hnorm f γ).natDegree ≤ edeg Γ := by
    obtain ⟨ha, hb⟩ := hγp
    unfold hnorm
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_pow]; omega
    · rcases hb with hb | hb
      · simp [hb]
      · refine natDegree_mul_le.trans ?_
        rw [natDegree_pow, hf]; omega
  have hq0d : q0.natDegree = 0 := by
    have := congrArg natDegree hq0
    rw [natDegree_mul hw0 hq00, natDegree_wpoly] at this
    omega
  set c0 := q0.coeff 0
  have hq0C : q0 = C c0 := eq_C_of_natDegree_eq_zero hq0d
  have hc0 : c0 ≠ 0 := by intro h; rw [hq0C, h, C_0] at hq00; exact hq00 rfl
  -- `Φ = χ · γ̄` is divisible by `wpoly Γ`
  set Φ := hmul f χ (hconj γ)
  have hΦ1 : Vanishes f Φ Γ := fun q hq ↦ by
    have := VanishAt.hmul (ψ := χ) (φ := hconj γ) (k' := 0) (hon q hq).1 (hon q hq).2 (hχ q hq)
      (by obtain ⟨V, hV⟩ := exists_branch (hon q hq).1 (hon q hq).2 0; exact ⟨V, hV, by simp⟩)
    simpa using this
  have hΦ2 : Vanishes f Φ (econj Γ) := fun q hq ↦ by
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    have hon' := (hon.econj) _ hq
    have := VanishAt.hmul (ψ := χ) (φ := hconj γ) (k := 0) hon'.1 hon'.2
      (by obtain ⟨V, hV⟩ := exists_branch hon'.1 hon'.2 0; exact ⟨V, hV, by simp⟩)
      ((hγ q' hq').hconj)
    simpa using this
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := wpoly_dvd_of_vanish_both hΓ hon hΦ1 hΦ2
  -- `c₀ χ = (A + B y) γ`
  have key : hsmul (C c0) χ = hmul f (A, B) γ := by
    have e1 : hmul f Φ γ = hsmul (hnorm f γ) χ := by
      simp only [Φ, Jac.hmul, hconj, hsmul, hnorm]
      exact Prod.ext (by ring) (by ring)
    have e2 : hmul f Φ γ = hsmul (wpoly Γ) (hmul f (A, B) γ) := by
      have hΦe : Φ = hsmul (wpoly Γ) (A, B) := Prod.ext hA hB
      rw [hΦe]; simp only [Jac.hmul, hsmul]
      exact Prod.ext (by ring) (by ring)
    rw [e2, hq0, hq0C] at e1
    have k1 := congrArg Prod.fst e1
    have k2 := congrArg Prod.snd e1
    simp only [hsmul] at k1 k2
    refine Prod.ext ?_ ?_
    · exact mul_left_cancel₀ hw0 (by simp only [hsmul]; rw [k1]; ring)
    · exact mul_left_cancel₀ hw0 (by simp only [hsmul]; rw [k2]; ring)
  -- pole bounds force `B = 0`, `deg A ≤ g`
  have hΦp : PoleLE g Φ (2 * g + edeg Γ + edeg Γ) :=
    PoleLE.hmul (by omega) hχp hγp.hconj
  have hΦe : hsmul (wpoly Γ) (A, B) = Φ := (Prod.ext hA hB).symm
  have hABp : PoleLE g (A, B) (2 * g + edeg Γ + edeg Γ - 2 * (wpoly Γ).natDegree) :=
    PoleLE.of_hsmul hw0 (hΦe ▸ hΦp)
  rw [natDegree_wpoly] at hABp
  obtain ⟨hAd, hBd⟩ := hABp
  have hB0 : B = 0 := hBd.resolve_right (by simp only; omega)
  have hAd' : A.natDegree ≤ g := by simp only at hAd; omega
  -- `A` vanishes at every `xᵢ`
  have hAx : ∀ i, A.eval (x i) = 0 := by
    intro i
    obtain ⟨V, hV, hj⟩ := hχσ i
    have hon_i : IsUnit (2 * -y i) := by rw [mul_neg]; exact (hy i).neg
    -- value of `c₀ χ` at `σPᵢ`
    have h1 : (jet χ.1 χ.2 (x i) V).coeff 0 = 0 := by
      rw [pow_one, X_dvd_iff] at hj; exact hj
    rw [jet_coeff_zero hV] at h1
    have h2 : c0 * (χ.1.eval (x i) + χ.2.eval (x i) * -y i) =
        A.eval (x i) * (γ.1.eval (x i) + γ.2.eval (x i) * -y i) := by
      have := congrArg (fun ψ : k[X] × k[X] ↦ ψ.1.eval (x i) + ψ.2.eval (x i) * -y i) key
      simp only [hsmul, Jac.hmul, hB0, eval_mul, eval_add, eval_C, eval_zero, zero_mul,
        add_zero] at this
      linear_combination this
    rw [h1, mul_zero] at h2
    have hγv : γ.1.eval (x i) + γ.2.eval (x i) * -y i ≠ 0 := by
      intro h0
      have hNx : (hnorm f γ).eval (x i) = 0 := by
        simp only [hnorm, eval_sub, eval_pow, eval_mul, ← hyf i]
        linear_combination (γ.1.eval (x i) + γ.2.eval (x i) * y i) * h0
      rw [hq0, hq0C, eval_mul, eval_C] at hNx
      exact mul_ne_zero (eval_wpoly_ne_zero fun q hq ↦ hxΓ i q hq) hc0 hNx
    exact (mul_eq_zero.mp h2.symm).resolve_right hγv
  -- hence `A = c · u`
  have hu : (∏ i, (X - C (x i))) ∣ A := by
    have := prod_pow_dvd hx 1 (fun i ↦ by rw [pow_one]; exact dvd_iff_isRoot.mpr (hAx i))
    rwa [pow_one] at this
  obtain ⟨qA, hqA⟩ := hu
  have hU0 : (∏ i, (X - C (x i))) ≠ 0 :=
    (monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)).ne_zero
  have hdegU : (∏ i, (X - C (x i))).natDegree = g := by
    have := natDegree_prod_pow x 1; rwa [pow_one, mul_one] at this
  have hqAC : qA = C (qA.coeff 0) := by
    by_cases hqA0 : qA = 0
    · rw [hqA0]; simp
    apply eq_C_of_natDegree_eq_zero
    have := congrArg natDegree hqA
    rw [natDegree_mul hU0 hqA0, hdegU] at this
    omega
  refine ⟨qA.coeff 0 / c0, ?_⟩
  simp only [hsmul, Jac.hmul, hB0, Prod.mk.injEq] at key
  obtain ⟨k1, k2⟩ := key
  have hc0' : C c0 ≠ 0 := by simpa using hc0
  have hcc : C c0 * C (qA.coeff 0 / c0) = C (qA.coeff 0) := by
    rw [← C_mul, mul_div_cancel₀ _ hc0]
  refine Prod.ext ?_ ?_
  · simp only [hsmul]
    apply mul_left_cancel₀ hc0'
    rw [k1, hqA]
    nth_rewrite 1 [hqAC]
    linear_combination (-(∏ i, (X - C (x i))) * γ.1) * hcc
  · simp only [hsmul]
    apply mul_left_cancel₀ hc0'
    rw [k2, hqA]
    nth_rewrite 1 [hqAC]
    linear_combination (-(∏ i, (X - C (x i))) * γ.2) * hcc

end Field

end Jac
