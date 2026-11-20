import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Abel's theorem for elliptic curves, norm form

For `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` over a field `K` of characteristic zero, `f` squarefree,
with Dedekind coordinate ring `R`: if `u = A + B y` (`A, B` coprime) has norm
`A² − B² f = λ ∏ (X − αᵢ)^{mᵢ} · g` (`g ∣ f`) and vanishes at `Pᵢ = (αᵢ, βᵢ)` (`βᵢ ≠ 0`), then
`(u) = ∏ ⟨X − αᵢ, Y − βᵢ⟩^{mᵢ} · ⟨g, Y⟩` and `⟨g, Y⟩² = (g)`, hence
`2 • ∑ mᵢ • Pᵢ = 0` (`abel_two_torsion`).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped nonZeroDivisors Polynomial.Bivariate

namespace EllAbel

variable {K : Type*} [Field K] (a₂ a₄ a₆ : K)

/-- `y² = x³ + a₂x² + a₄x + a₆`. -/
def W : WeierstrassCurve K := ⟨0, a₂, 0, a₄, a₆⟩

/-- `f = x³ + a₂x² + a₄x + a₆`. -/
noncomputable def f : K[X] := X ^ 3 + C a₂ * X ^ 2 + C a₄ * X + C a₆

set_option quotPrecheck false in
local notation "R" => WeierstrassCurve.Affine.CoordinateRing (W a₂ a₄ a₆).toAffine

/-- `K[X] → R`. -/
noncomputable abbrev ι : K[X] →+* R := algebraMap K[X] R

/-- `y ∈ R`. -/
noncomputable abbrev yR : R := mk (W a₂ a₄ a₆).toAffine Y

lemma ι_eq (p : K[X]) : ι a₂ a₄ a₆ p = mk (W a₂ a₄ a₆).toAffine (C p) := rfl

lemma yR_sq : yR a₂ a₄ a₆ ^ 2 = ι a₂ a₄ a₆ (f a₂ a₄ a₆) := by
  rw [ι_eq, ← map_pow]
  exact AdjoinRoot.mk_eq_mk.mpr ⟨1, by simp [Affine.polynomial, W, f]⟩

lemma ι_injective : Function.Injective (ι a₂ a₄ a₆) :=
  FaithfulSMul.algebraMap_injective K[X] R

/-- `(A + B y)(A − B y) = A² − B² f`. -/
lemma conj_mul (A B : K[X]) :
    (ι a₂ a₄ a₆ A + ι a₂ a₄ a₆ B * yR a₂ a₄ a₆) * (ι a₂ a₄ a₆ A - ι a₂ a₄ a₆ B * yR a₂ a₄ a₆) =
      ι a₂ a₄ a₆ (A ^ 2 - B ^ 2 * f a₂ a₄ a₆) := by
  have := yR_sq a₂ a₄ a₆
  simp only [map_sub, map_mul, map_pow]
  linear_combination (-(ι a₂ a₄ a₆ B) ^ 2) * this

variable {a₂ a₄ a₆}

/-- Evaluation at a point of the curve. -/
noncomputable def evP {α β : K} (h : (W a₂ a₄ a₆).toAffine.Equation α β) : R →+* K :=
  AdjoinRoot.lift (Polynomial.evalRingHom α) β (by
    rw [equation_iff] at h
    simp only [Affine.polynomial, W] at h ⊢
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, coe_evalRingHom,
      eval_add, eval_mul, eval_pow, eval_X, eval_C]
    linear_combination h)

lemma evP_ι {α β : K} (h : (W a₂ a₄ a₆).toAffine.Equation α β) (p : K[X]) :
    evP h (ι a₂ a₄ a₆ p) = p.eval α := by
  rw [ι_eq, evP, AdjoinRoot.lift_mk]; simp

lemma evP_y {α β : K} (h : (W a₂ a₄ a₆).toAffine.Equation α β) : evP h (yR a₂ a₄ a₆) = β := by
  rw [evP, AdjoinRoot.lift_mk]; simp

lemma XYIdeal_le_ker {α β : K} (h : (W a₂ a₄ a₆).toAffine.Equation α β) :
    XYIdeal (W a₂ a₄ a₆).toAffine α (C β) ≤ RingHom.ker (evP h) := by
  rw [XYIdeal, Ideal.span_le]
  rintro z (rfl | rfl)
  · change evP h (mk _ (C (X - C α))) = 0
    rw [← ι_eq, evP_ι]; simp
  · change evP h (mk _ (Y - C (C β))) = 0
    rw [map_sub, ← ι_eq, map_sub, evP_ι]
    change evP h (yR a₂ a₄ a₆) - _ = 0
    rw [evP_y]; simp

lemma XYIdeal_isMaximal {α β : K} (h : (W a₂ a₄ a₆).toAffine.Equation α β) :
    (XYIdeal (W a₂ a₄ a₆).toAffine α (C β)).IsMaximal := by
  have e := quotientXYIdealEquiv (W' := (W a₂ a₄ a₆).toAffine) (x := α) (y := C β) (by
    simpa [Affine.Equation, evalEval] using h)
  exact Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField (Field.toIsField K) e.toMulEquiv)

/-- A function not vanishing at `P` generates an ideal coprime to `⟨X − α, Y − β⟩`. -/
lemma isCoprime_XYIdeal {α β : K} (h : (W a₂ a₄ a₆).toAffine.Equation α β) (w : R)
    (hw : evP h w ≠ 0) : IsCoprime (XYIdeal (W a₂ a₄ a₆).toAffine α (C β)) (Ideal.span {w}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  have hmax := XYIdeal_isMaximal h
  have heq := hmax.eq_of_le hne le_sup_left
  have hwm : w ∈ XYIdeal (W a₂ a₄ a₆).toAffine α (C β) := by
    rw [heq]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self w)
  exact hw (XYIdeal_le_ker h hwm)

/-- `I ⊔ J = ⊤` and `K' J ≤ I` give `K' ≤ I`. -/
lemma le_of_isCoprime_of_mul_le {S : Type*} [CommRing S] {I J K' : Ideal S} (h : IsCoprime I J)
    (hK : K' * J ≤ I) : K' ≤ I := by
  have := h.sup_eq
  calc K' = K' * ⊤ := (Ideal.mul_top K').symm
    _ = K' * (I ⊔ J) := by rw [this]
    _ = K' * I ⊔ K' * J := Ideal.mul_sup _ _ _
    _ ≤ I := sup_le (Ideal.mul_le.mpr fun _ _ _ hb ↦ Ideal.mul_mem_left _ _ hb) hK

variable (a₂ a₄ a₆)

/-- `⟨g, y⟩`. -/
noncomputable def Qi (g : K[X]) : Ideal R := Ideal.span {ι a₂ a₄ a₆ g, yR a₂ a₄ a₆}

/-- `∏ ⟨X − αᵢ, Y − βᵢ⟩^{mᵢ}`. -/
noncomputable def Mi {ι' : Type*} (s : Finset ι') (α β : ι' → K) (m : ι' → ℕ) : Ideal R :=
  ∏ i ∈ s, XYIdeal (W a₂ a₄ a₆).toAffine (α i) (C (β i)) ^ m i

/-- `⟨g, y⟩² = (g)` for `g ∣ f`, `f` squarefree. -/
lemma Qi_sq (hsq : Squarefree (f a₂ a₄ a₆)) {g : K[X]} (hg : g ∣ f a₂ a₄ a₆) :
    Qi a₂ a₄ a₆ g * Qi a₂ a₄ a₆ g = Ideal.span {ι a₂ a₄ a₆ g} := by
  obtain ⟨h, hh⟩ := hg
  have hcop : IsCoprime g h := by
    rw [hh] at hsq; exact (squarefree_mul_iff.mp hsq).1.isCoprime
  obtain ⟨s', t', hst⟩ := hcop
  have hy2 : yR a₂ a₄ a₆ * yR a₂ a₄ a₆ = ι a₂ a₄ a₆ g * ι a₂ a₄ a₆ h := by
    rw [← sq, yR_sq, hh, map_mul]
  apply le_antisymm
  · rw [Qi, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    · exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    · exact Ideal.mem_span_singleton.mpr (dvd_mul_left _ _)
    · rw [hy2]; exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  · rw [Ideal.span_singleton_le_iff_mem]
    have e : ι a₂ a₄ a₆ g = ι a₂ a₄ a₆ s' * (ι a₂ a₄ a₆ g * ι a₂ a₄ a₆ g) +
        ι a₂ a₄ a₆ t' * (yR a₂ a₄ a₆ * yR a₂ a₄ a₆) := by
      rw [hy2]
      have := congrArg (ι a₂ a₄ a₆ · * ι a₂ a₄ a₆ g) hst
      simp only [map_add, map_mul, map_one, one_mul] at this
      linear_combination -this
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul ?_ ?_))
      (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul ?_ ?_))
    all_goals first
      | exact Ideal.subset_span (Set.mem_insert _ _)
      | exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

variable {a₂ a₄ a₆}

/-- **The divisor inclusion**: `(A + B y) ⊆ ∏ ⟨X − αᵢ, Y − βᵢ⟩^{mᵢ} · ⟨g, y⟩`. -/
lemma span_le [CharZero K] (hsq : Squarefree (f a₂ a₄ a₆)) (A B : K[X]) (hAB : IsCoprime A B)
    {ι' : Type*} (s : Finset ι') (α β : ι' → K)
    (hP : ∀ i, (W a₂ a₄ a₆).toAffine.Equation (α i) (β i)) (hβ : ∀ i ∈ s, β i ≠ 0)
    (m : ι' → ℕ) (g : K[X]) (hg : g ∣ f a₂ a₄ a₆) (lam : K)
    (hfac : A ^ 2 - B ^ 2 * f a₂ a₄ a₆ = C lam * (∏ i ∈ s, (X - C (α i)) ^ m i) * g)
    (hvan : ∀ i ∈ s, 0 < m i → A.eval (α i) + B.eval (α i) * β i = 0) :
    Ideal.span {ι a₂ a₄ a₆ A + ι a₂ a₄ a₆ B * yR a₂ a₄ a₆} ≤
      Mi a₂ a₄ a₆ s α β m * Qi a₂ a₄ a₆ g := by
  -- the norm lies in `M`
  have hN : ι a₂ a₄ a₆ (A ^ 2 - B ^ 2 * f a₂ a₄ a₆) ∈ Mi a₂ a₄ a₆ s α β m := by
    rw [hfac, map_mul, map_mul, mul_comm (ι a₂ a₄ a₆ (C lam)), mul_assoc]
    refine Ideal.mul_mem_right _ _ ?_
    unfold Mi
    rw [map_prod]
    refine Ideal.prod_mem_prod fun i _ ↦ ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    exact Ideal.subset_span (Set.mem_insert _ _)
  -- `(ι a₂ a₄ a₆ A - ι a₂ a₄ a₆ B * yR a₂ a₄ a₆)` does not vanish at the `Pᵢ` (with `mᵢ > 0`)
  have hcopM : IsCoprime (Mi a₂ a₄ a₆ s α β m) (Ideal.span {(ι a₂ a₄ a₆ A - ι a₂ a₄ a₆ B * yR a₂ a₄ a₆)}) := by
    unfold Mi
    refine IsCoprime.prod_left fun i hi ↦ ?_
    rcases Nat.eq_zero_or_pos (m i) with h0 | h0
    · rw [h0, pow_zero]; exact isCoprime_one_left
    refine (isCoprime_XYIdeal (hP i) (ι a₂ a₄ a₆ A - ι a₂ a₄ a₆ B * yR a₂ a₄ a₆) ?_).pow_left
    rw [map_sub, map_mul, evP_ι, evP_ι, evP_y]
    have h1 := hvan i hi h0
    have hB : B.eval (α i) ≠ 0 := by
      intro hB0
      rw [hB0, zero_mul, add_zero] at h1
      obtain ⟨s', t', hst⟩ := hAB
      have := congrArg (Polynomial.eval (α i)) hst
      simp [h1, hB0] at this
    intro h2
    have : 2 * (B.eval (α i) * β i) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp this with h | h
    · norm_num at h
    · exact (mul_ne_zero hB (hβ i hi)) h
  have hleM : Ideal.span {ι a₂ a₄ a₆ A + ι a₂ a₄ a₆ B * yR a₂ a₄ a₆} ≤ Mi a₂ a₄ a₆ s α β m := by
    refine le_of_isCoprime_of_mul_le hcopM ?_
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_iff_mem, conj_mul]
    exact hN
  -- `u ∈ ⟨g, y⟩`
  have hgA : g ∣ A := by
    have hsqg : Squarefree g := hsq.squarefree_of_dvd hg
    refine (hsqg.dvd_pow_iff_dvd two_ne_zero).mp ?_
    have : A ^ 2 = B ^ 2 * f a₂ a₄ a₆ + C lam * (∏ i ∈ s, (X - C (α i)) ^ m i) * g := by
      rw [← hfac]; ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right hg _) (dvd_mul_left _ _)
  have hleQ : Ideal.span {ι a₂ a₄ a₆ A + ι a₂ a₄ a₆ B * yR a₂ a₄ a₆} ≤ Qi a₂ a₄ a₆ g := by
    rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨A1, rfl⟩ := hgA
    rw [map_mul]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  have hcopQ : IsCoprime (Mi a₂ a₄ a₆ s α β m) (Qi a₂ a₄ a₆ g) := by
    unfold Mi
    refine IsCoprime.prod_left fun i hi ↦ ?_
    rcases Nat.eq_zero_or_pos (m i) with h0 | h0
    · rw [h0, pow_zero]; exact isCoprime_one_left
    refine IsCoprime.pow_left ?_
    have hc := isCoprime_XYIdeal (hP i) (yR a₂ a₄ a₆) (by rw [evP_y]; exact hβ i hi)
    rw [Ideal.isCoprime_iff_sup_eq] at hc ⊢
    refine top_le_iff.mp (hc ▸ sup_le_sup_left ?_ _)
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  rw [← Ideal.inf_eq_mul_of_isCoprime hcopQ]
  exact le_inf hleM hleQ

lemma negY_W (x y : K) : (W a₂ a₄ a₆).toAffine.negY x y = -y := by simp [negY, W]

/-- `(A² − B² f) = ∏ ⟨X − αᵢ, Y + βᵢ⟩^{mᵢ} · ∏ ⟨X − αᵢ, Y − βᵢ⟩^{mᵢ} · ⟨g, y⟩²`. -/
lemma span_norm (hsq : Squarefree (f a₂ a₄ a₆)) (A B : K[X]) {ι' : Type*} (s : Finset ι')
    (α β : ι' → K) (hP : ∀ i, (W a₂ a₄ a₆).toAffine.Nonsingular (α i) (β i)) (m : ι' → ℕ)
    (g : K[X]) (hg : g ∣ f a₂ a₄ a₆) (lam : K) (hlam : lam ≠ 0)
    (hfac : A ^ 2 - B ^ 2 * f a₂ a₄ a₆ = C lam * (∏ i ∈ s, (X - C (α i)) ^ m i) * g) :
    Ideal.span {ι a₂ a₄ a₆ (A ^ 2 - B ^ 2 * f a₂ a₄ a₆)} =
      Mi a₂ a₄ a₆ s α β m * Mi a₂ a₄ a₆ s α (fun i ↦ -β i) m *
        (Qi a₂ a₄ a₆ g * Qi a₂ a₄ a₆ g) := by
  rw [Qi_sq a₂ a₄ a₆ hsq hg, hfac, map_mul, map_mul, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton]
  have hu : Ideal.span {ι a₂ a₄ a₆ (C lam)} = ⊤ :=
    Ideal.span_singleton_eq_top.mpr ((isUnit_C.mpr (Ne.isUnit hlam)).map _)
  rw [hu, Ideal.top_mul, map_prod, ← Ideal.prod_span_singleton]
  have hpt : ∀ i ∈ s, Ideal.span {ι a₂ a₄ a₆ ((X - C (α i)) ^ m i)} =
      XYIdeal (W a₂ a₄ a₆).toAffine (α i) (C (β i)) ^ m i *
        XYIdeal (W a₂ a₄ a₆).toAffine (α i) (C (-β i)) ^ m i := by
    intro i _
    rw [map_pow, ← Ideal.span_singleton_pow, ← mul_pow]
    congr 1
    have := XYIdeal_neg_mul (hP i)
    rw [negY_W] at this
    rw [mul_comm, this]
    rfl
  rw [Finset.prod_congr rfl hpt, Finset.prod_mul_distrib, Mi, Mi]

/-- **The divisor of `A + B y`**: `(A + B y) = ∏ ⟨X − αᵢ, Y − βᵢ⟩^{mᵢ} · ⟨g, y⟩`. -/
theorem span_eq [CharZero K] [IsDedekindDomain R] (hsq : Squarefree (f a₂ a₄ a₆)) (A B : K[X])
    (hAB : IsCoprime A B) {ι' : Type*} (s : Finset ι') (α β : ι' → K)
    (hP : ∀ i, (W a₂ a₄ a₆).toAffine.Nonsingular (α i) (β i)) (hβ : ∀ i ∈ s, β i ≠ 0)
    (m : ι' → ℕ) (g : K[X]) (hg : g ∣ f a₂ a₄ a₆) (lam : K) (hlam : lam ≠ 0)
    (hfac : A ^ 2 - B ^ 2 * f a₂ a₄ a₆ = C lam * (∏ i ∈ s, (X - C (α i)) ^ m i) * g)
    (hvan : ∀ i ∈ s, 0 < m i → A.eval (α i) + B.eval (α i) * β i = 0) :
    Ideal.span {ι a₂ a₄ a₆ A + ι a₂ a₄ a₆ B * yR a₂ a₄ a₆} =
      Mi a₂ a₄ a₆ s α β m * Qi a₂ a₄ a₆ g := by
  have h1 := span_le hsq A B hAB s α β (fun i ↦ (hP i).1) hβ m g hg lam hfac hvan
  have hP' : ∀ i, (W a₂ a₄ a₆).toAffine.Equation (α i) (-β i) := fun i ↦ by
    have := (equation_neg (α i) (β i)).mpr (hP i).1
    rwa [negY_W] at this
  have h2 := span_le hsq A (-B) hAB.neg_right s α (fun i ↦ -β i) hP'
    (fun i hi ↦ neg_ne_zero.mpr (hβ i hi)) m g hg lam (by rw [neg_sq]; exact hfac)
    (fun i hi h0 ↦ by have := hvan i hi h0; simp only [eval_neg]; linear_combination this)
  rw [map_neg, neg_mul, ← sub_eq_add_neg] at h2
  obtain ⟨I3, hI3⟩ := (Ideal.dvd_iff_le).mpr h1
  obtain ⟨I4, hI4⟩ := (Ideal.dvd_iff_le).mpr h2
  have hprod := span_norm hsq A B s α β hP m g hg lam hlam hfac
  rw [← conj_mul, ← Ideal.span_singleton_mul_span_singleton, hI3, hI4] at hprod
  have hne : Mi a₂ a₄ a₆ s α β m * Mi a₂ a₄ a₆ s α (fun i ↦ -β i) m *
      (Qi a₂ a₄ a₆ g * Qi a₂ a₄ a₆ g) ≠ 0 := by
    rw [← span_norm hsq A B s α β hP m g hg lam hlam hfac, ne_eq, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot, map_eq_zero_iff _ (ι_injective a₂ a₄ a₆), hfac]
    refine mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hlam)
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _))) ?_
    rintro rfl
    have hf0 : f a₂ a₄ a₆ ≠ 0 := hsq.ne_zero
    exact hf0 (zero_dvd_iff.mp hg)
  have h34 : I3 * I4 = 1 := by
    refine mul_left_cancel₀ hne ?_
    have e : Mi a₂ a₄ a₆ s α β m * Qi a₂ a₄ a₆ g * I3 *
        (Mi a₂ a₄ a₆ s α (fun i ↦ -β i) m * Qi a₂ a₄ a₆ g * I4) =
        Mi a₂ a₄ a₆ s α β m * Mi a₂ a₄ a₆ s α (fun i ↦ -β i) m *
          (Qi a₂ a₄ a₆ g * Qi a₂ a₄ a₆ g) * (I3 * I4) := by ring
    rw [mul_one, ← e, hprod]
  have hI : I3 = ⊤ := top_le_iff.mp (by
    rw [← Ideal.one_eq_top, ← h34]; exact Ideal.mul_le_left)
  rw [hI3, hI, Ideal.mul_top]

/-- **Abel's theorem, norm form**: a function `A + B y` whose norm has the zeros `Pᵢ` (with
multiplicity `mᵢ`) and otherwise only ramified factors gives the relation `2 • ∑ mᵢ Pᵢ = 0`. -/
theorem abel_two_torsion [DecidableEq K] [CharZero K] [IsDedekindDomain R]
    (hsq : Squarefree (f a₂ a₄ a₆)) (A B : K[X]) (hAB : IsCoprime A B) {ι' : Type*}
    (s : Finset ι') (α β : ι' → K) (hP : ∀ i, (W a₂ a₄ a₆).toAffine.Nonsingular (α i) (β i))
    (hβ : ∀ i ∈ s, β i ≠ 0) (_hinj : Set.InjOn α s) (m : ι' → ℕ) (g : K[X])
    (hg : g ∣ f a₂ a₄ a₆) (lam : K) (hlam : lam ≠ 0)
    (hfac : A ^ 2 - B ^ 2 * f a₂ a₄ a₆ = C lam * (∏ i ∈ s, (X - C (α i)) ^ m i) * g)
    (hvan : ∀ i ∈ s, 0 < m i → A.eval (α i) + B.eval (α i) * β i = 0) :
    2 • ∑ i ∈ s, m i • (Point.some _ _ (hP i) : (W a₂ a₄ a₆).toAffine.Point) = 0 := by
  apply Point.toClass_injective
  rw [map_zero]
  apply Additive.toMul.injective
  rw [map_nsmul, map_sum, toMul_nsmul, toMul_zero, toMul_sum]
  simp only [map_nsmul, toMul_nsmul, Point.toClass_some]
  change (∏ i ∈ s, ClassGroup.mk (W a₂ a₄ a₆).toAffine.FunctionField
    (CoordinateRing.XYIdeal' (hP i)) ^ m i) ^ 2 = 1
  rw [← map_one (ClassGroup.mk (W a₂ a₄ a₆).toAffine.FunctionField)]
  simp only [← map_pow, ← map_prod]
  have hg0 : g ≠ 0 := by
    rintro rfl; exact hsq.ne_zero (zero_dvd_iff.mp hg)
  have hu0 : ι a₂ a₄ a₆ A + ι a₂ a₄ a₆ B * yR a₂ a₄ a₆ ≠ 0 := by
    intro h0
    have e : ι a₂ a₄ a₆ A + ι a₂ a₄ a₆ B * yR a₂ a₄ a₆ =
        A • (1 : R) + B • mk (W a₂ a₄ a₆).toAffine Y := by
      rw [CoordinateRing.smul, CoordinateRing.smul, mul_one]; rfl
    rw [e] at h0
    obtain ⟨hA, hB⟩ := smul_basis_eq_zero h0
    rw [hA, hB] at hAB
    exact not_isCoprime_zero_zero hAB
  refine (ClassGroup.mk_eq_mk_of_coe_ideal (I' := Mi a₂ a₄ a₆ s α β m ^ 2) (J' := 1) ?_ ?_).mpr
    ⟨ι a₂ a₄ a₆ g, (ι a₂ a₄ a₆ B * yR a₂ a₄ a₆ + ι a₂ a₄ a₆ A) ^ 2,
      (map_ne_zero_iff _ (ι_injective a₂ a₄ a₆)).mpr hg0, pow_ne_zero _ (by rwa [add_comm]), ?_⟩
  · have key : ((∏ i ∈ s, CoordinateRing.XYIdeal' (hP i) ^ m i :
        (FractionalIdeal R⁰ (W a₂ a₄ a₆).toAffine.FunctionField)ˣ) :
          FractionalIdeal R⁰ (W a₂ a₄ a₆).toAffine.FunctionField) =
        FractionalIdeal.coeIdealHom R⁰ (W a₂ a₄ a₆).toAffine.FunctionField
          (Mi a₂ a₄ a₆ s α β m) := by
      rw [Units.coe_prod, Mi, map_prod]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [Units.val_pow_eq_pow_val, map_pow, CoordinateRing.XYIdeal'_eq]
      rfl
    rw [Units.val_pow_eq_pow_val, key, FractionalIdeal.coeIdeal_pow]
    rfl
  · rw [Units.val_one, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top]
  · rw [mul_one, add_comm, ← Ideal.span_singleton_pow,
      span_eq hsq A B hAB s α β hP hβ m g hg lam hlam hfac hvan, mul_pow,
      ← Qi_sq a₂ a₄ a₆ hsq hg]
    ring

end EllAbel
