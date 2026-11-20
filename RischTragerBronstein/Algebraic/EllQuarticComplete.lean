import RischTragerBronstein.Algebraic.EllQuartic
import RischTragerBronstein.Algebraic.EllCubicComplete

/-!
# Completeness of `ellDecideQuartic`

For a squarefree quartic `q ∈ ℚ[x]` with a rational root `e`, `A, D ≠ 0` and `D` split over `ℚ`,
`ellDecideQuartic` answers. Ingredients: reversal
preserves squarefreeness (non-zero constant term) and splitting; `sepCheck` is complete.
-/

open Polynomial

namespace EllAlgo

open CPoly

/-! ### Reversal -/

lemma reverse_reverse_of {f : ℚ[X]} (h0 : f.coeff 0 ≠ 0) : f.reverse.reverse = f := by
  have ht : f.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr h0)
  have hd : f.reverse.natDegree = f.natDegree := by rw [reverse_natDegree, ht, Nat.sub_zero]
  ext n
  rw [coeff_reverse, coeff_reverse, hd, revAt_invol]

lemma coeff_zero_ne_of_dvd {f g : ℚ[X]} (hg : g ∣ f) (h0 : f.coeff 0 ≠ 0) : g.coeff 0 ≠ 0 := by
  obtain ⟨h, rfl⟩ := hg
  rw [mul_coeff_zero] at h0
  exact left_ne_zero_of_mul h0

lemma squarefree_reverse {f : ℚ[X]} (hf : Squarefree f) (h0 : f.coeff 0 ≠ 0) :
    Squarefree f.reverse := by
  intro g ⟨h, hgh⟩
  have hf0 : f ≠ 0 := hf.ne_zero
  have hrev0 : f.reverse.coeff 0 ≠ 0 := by
    rw [coeff_zero_reverse]; exact leadingCoeff_ne_zero.mpr hf0
  have hg0 : g.coeff 0 ≠ 0 := coeff_zero_ne_of_dvd ⟨g * h, by rw [hgh]; ring⟩ hrev0
  have e : f = g.reverse * g.reverse * h.reverse := by
    rw [← reverse_reverse_of h0, hgh, reverse_mul_of_domain, reverse_mul_of_domain]
  have hu : IsUnit g.reverse := hf _ ⟨h.reverse, e⟩
  have hgt : g.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr hg0)
  have hdeg : g.natDegree = 0 := by
    have := natDegree_eq_zero_of_isUnit hu
    rwa [reverse_natDegree, hgt, Nat.sub_zero] at this
  rw [eq_C_of_natDegree_eq_zero hdeg]
  exact isUnit_C.mpr (Ne.isUnit hg0)

lemma reverse_X_add_C (a : ℚ) : (X + C a).reverse = C a * X + 1 := by
  have hd : (X + C a).natDegree = 1 := natDegree_X_add_C a
  ext n
  rw [coeff_reverse, hd]
  rcases n with _ | _ | n
  · rw [revAt_le (by omega)]; simp
  · rw [revAt_le (by omega)]; simp [coeff_one]
  · rw [revAt_eq_self_of_lt (by omega)]
    simp [coeff_X, coeff_one]

lemma splits_reverse {f : ℚ[X]} (hf : f.Splits) : f.reverse.Splits := by
  induction hf using Submonoid.closure_induction with
  | mem g hg =>
    rcases hg with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [reverse_C]; exact Splits.C a
    · rw [reverse_X_add_C]
      by_cases ha : a = 0
      · subst ha; simp
      · rw [show C a * X + 1 = C a * (X + C a⁻¹) by
          rw [mul_add, ← C_mul, mul_inv_cancel₀ ha, C_1]]
        exact (Splits.X_add_C _).C_mul a
  | one => rw [← C_1, reverse_C]; exact Splits.C 1
  | mul g h _ _ hg hh => rw [reverse_mul_of_domain]; exact hg.mul hh

/-- The list reversal is the polynomial reversal when the top entry is non-zero. -/
lemma toPoly_reverse (L : CPoly ℚ) (h : (toPoly L).natDegree + 1 = L.length) :
    toPoly L.reverse = (toPoly L).reverse := by
  ext n
  rw [coeff_reverse, coeff_toPoly, coeff_toPoly, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge n L.length with hn | hn
  · rw [List.getElem?_reverse hn, revAt_le (by omega)]
    congr 2; omega
  · rw [List.getElem?_eq_none (by simp; omega), revAt_eq_self_of_lt (by omega),
      List.getElem?_eq_none (by omega)]

/-! ### The separability check is complete -/

lemma sepCheck_complete {P : CPoly ℚ} (h : (toPoly P).Separable) : sepCheck P = true := by
  obtain ⟨h1, h2⟩ := egcd_dvd P (deriv P)
  rw [toPoly_deriv] at h2
  have hu : IsUnit (toPoly (egcd P (deriv P)).1) := IsCoprime.isUnit_of_dvd' h h1 h2
  have hne : trim (egcd P (deriv P)).1 ≠ [] := fun h0 ↦
    hu.ne_zero ((trim_eq_nil_iff _).mp h0)
  rw [sepCheck, beq_iff_eq, length_trim hne, natDegree_eq_zero_of_isUnit hu]

/-! ### The quartic data -/

lemma toPoly_shift_trim (P : CPoly ℚ) (e : ℚ) :
    toPoly (trim (shiftPoly P e)) = (toPoly P).comp (X + C e) := by
  rw [toPoly_trim, toPoly_shiftPoly]

lemma comp_X_add_C_ne_zero {P : ℚ[X]} (hP : P ≠ 0) (e : ℚ) : P.comp (X + C e) ≠ 0 := by
  intro h
  apply hP
  have := congrArg (fun F ↦ F.comp (X - C e)) h
  simp only [comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X, zero_comp] at this
  exact this

lemma natDegree_comp_X_add_C (P : ℚ[X]) (e : ℚ) : (P.comp (X + C e)).natDegree = P.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

lemma squarefree_comp_X_add_C {f : ℚ[X]} (hsq : Squarefree f) (e : ℚ) :
    Squarefree (f.comp (X + C e)) := by
  have hsep : f.Separable := (PerfectField.separable_iff_squarefree).mpr hsq
  have hsep' : IsCoprime f (derivative f) := hsep
  have h1 : IsCoprime (f.comp (X + C e)) ((derivative f).comp (X + C e)) :=
    hsep'.map (Polynomial.compRingHom (X + C e))
  have hcomp : (f.comp (X + C e)).Separable := by
    show IsCoprime (f.comp (X + C e)) (derivative (f.comp (X + C e)))
    rw [derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul]
    exact h1
  exact hcomp.squarefree

lemma toPoly_trim_reverse (g : CPoly ℚ) (hg : trim g ≠ []) :
    toPoly (trim g).reverse = (toPoly g).reverse := by
  rw [toPoly_reverse _ (by rw [toPoly_trim, length_trim hg]), toPoly_trim]

/-- Enough fuel for `ellDecideQuartic`. -/
def fuelQuartic (q : CPoly ℚ) (e : ℚ) (A D : CPoly ℚ) : ℕ :=
  match quarticData q e A D with
  | some (P, _, Dn) => fuelCubic P Dn
  | none => 0

/-- **Completeness of `ellDecideQuartic`.** -/
theorem ellDecideQuartic_ne_none (q : CPoly ℚ) (e : ℚ) (A D : CPoly ℚ)
    (hq4 : (toPoly q).natDegree = 4) (hsq : Squarefree (toPoly q)) (he : (toPoly q).eval e = 0)
    (hA : toPoly A ≠ 0) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (fuel : ℕ) (hfuel : fuelQuartic q e A D ≤ fuel) :
    ellDecideQuartic q e A D fuel ≠ none := by
  set s := trim (shiftPoly q e) with hs
  set Q := (toPoly q).comp (X + C e) with hQ
  have hsQ : toPoly s = Q := toPoly_shift_trim q e
  have hq0 : toPoly q ≠ 0 := hsq.ne_zero
  have hQ0 : Q ≠ 0 := comp_X_add_C_ne_zero hq0 e
  have hQd : Q.natDegree = 4 := by rw [hQ, natDegree_comp_X_add_C, hq4]
  have hsne : s ≠ [] := fun h ↦ hQ0 (by rw [← hsQ, h]; rfl)
  have hs5 : s.length = 5 := by rw [hs, length_trim hsne, toPoly_shiftPoly, ← hQ, hQd]
  have hs0 : s.getD 0 0 = 0 := by
    rw [← coeff_toPoly, hsQ, coeff_zero_eq_eval_zero, hQ, eval_comp]; simpa using he
  obtain ⟨s0, t, hst⟩ : ∃ s0 t, s = s0 :: t := by
    cases h : s with
    | nil => exact absurd h hsne
    | cons a t => exact ⟨a, t, rfl⟩
  have hs00 : s0 = 0 := by rw [hst] at hs0; simpa using hs0
  set R := toPoly t with hR
  have hQR : Q = X * R := by rw [← hsQ, hst, hs00, toPoly_cons, hR]; simp
  have hR0 : R ≠ 0 := fun h ↦ hQ0 (by rw [hQR, h, mul_zero])
  have hRd : R.natDegree = 3 := by
    have := hQd; rw [hQR, natDegree_mul X_ne_zero hR0, natDegree_X] at this; omega
  have htl : t.length = 4 := by rw [hst] at hs5; simpa using hs5
  have hQsq : Squarefree Q := squarefree_comp_X_add_C hsq e
  have hRsq : Squarefree R := hQsq.squarefree_of_dvd ⟨X, by rw [hQR, mul_comm]⟩
  have hR00 : R.coeff 0 ≠ 0 := by
    intro h
    obtain ⟨R', hR'⟩ := X_dvd_iff.mpr h
    have : X * X ∣ Q := ⟨R', by rw [hQR, hR', mul_assoc]⟩
    exact not_isUnit_X (hQsq X this)
  set P := t.reverse with hP
  have hPR : toPoly P = R.reverse := toPoly_reverse t (by rw [← hR, hRd, htl])
  have hPsq : Squarefree (toPoly P) := by rw [hPR]; exact squarefree_reverse hRsq hR00
  have hsep : sepCheck P = true :=
    sepCheck_complete ((PerfectField.separable_iff_squarefree).mpr hPsq)
  have hdrop : s.drop 1 = t := by rw [hst]; rfl
  set sA := trim (shiftPoly A e) with hsA
  set sD := trim (shiftPoly D e) with hsD
  have hsA0 : sA ≠ [] := fun h ↦ comp_X_add_C_ne_zero hA e (by
    rw [← toPoly_shift_trim, ← hsA, h]; rfl)
  have hsD0 : sD ≠ [] := fun h ↦ comp_X_add_C_ne_zero hD e (by
    rw [← toPoly_shift_trim, ← hsD, h]; rfl)
  have hQD : quarticData q e A D = some (P, smul (-1) (mul sA.reverse (monomial (sD.length - 1) 1)),
      mul sD.reverse (monomial (sA.length - 1) 1)) := by
    unfold quarticData
    simp only
    rw [← hs, ← hsA, ← hsD, hdrop, if_pos ⟨hs5, hs0, hsep, hsA0, hsD0⟩]
  unfold fuelQuartic at hfuel
  rw [hQD] at hfuel
  dsimp only at hfuel
  unfold ellDecideQuartic
  rw [hQD]
  dsimp only
  set m := sA.length - 1 with hm
  have hDt : toPoly (mul sD.reverse (monomial m 1)) = toPoly sD.reverse * X ^ m := by
    rw [toPoly_mul, toPoly_monomial, C_1, one_mul]
  have hsDr : toPoly sD.reverse = ((toPoly D).comp (X + C e)).reverse := by
    rw [hsD, toPoly_trim_reverse _ hsD0, toPoly_shiftPoly]
  refine ellDecideCubic_ne_none P _ _ hPsq (by rw [hP, List.length_reverse, htl]) ?_ ?_ ?_
    fuel hfuel
  · rw [← coeff_toPoly, hPR, coeff_reverse, hRd, revAt_le le_rfl, Nat.sub_self]; exact hR00
  · rw [hDt, hsDr]
    exact mul_ne_zero (fun h ↦ comp_X_add_C_ne_zero hD e (reverse_eq_zero.mp h))
      (pow_ne_zero _ X_ne_zero)
  · rw [hDt, hsDr]
    exact (splits_reverse (hsplit.comp_X_add_C e)).mul (by simpa using Splits.C_mul_X_pow (1 : ℚ) m)

section Decision

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem for `∫ A / (D √q)`, `q` a squarefree quartic over `ℚ` with a rational
root `e`** (`A, D ≠ 0`, `D` split over `ℚ`). -/
theorem ellDecideQuartic_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly ℚ) (e : ℚ) (hy : y ^ 2 = aeval x (toPoly q)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (hq4 : (toPoly q).natDegree = 4) (hsq : Squarefree (toPoly q))
    (he : (toPoly q).eval e = 0) (hA : toPoly A ≠ 0) (hD : toPoly D ≠ 0)
    (hsplit : (toPoly D).Splits) :
    ∃ ans : Bool, ellDecideQuartic q e A D (fuelQuartic q e A D) = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp
    (ellDecideQuartic_ne_none q e A D hq4 hsq he hA hD hsplit _ le_rfl)
  exact ⟨ans, hans, ellDecideQuartic_spec hC hCall x y hx q e hy hgen A D _ ans hans⟩

end Decision

end EllAlgo
