import RischTragerBronstein.Mixed.KQMulti
import RischTragerBronstein.Mixed.KXSym

/-!
# Several residue classes, for `x′ = ω(x)` with bad places

`kxm_core`: the generalization of `kqm_core` (logarithms are rational combinations of the class
divisors `Δ_k`) to `x′ = ω(x)`, valid at the good places.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Classical

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

section GenMulti

variable (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (bad : K → Prop) (hgood : ∀ α : K, ¬ bad α → α′ ≠ (ω.map (algebraMap C K)).eval α)
  (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
  {r nk : ℕ} (c β : Fin r → C) (hc : Function.Injective c)
  (hbadc : ∀ q, ¬ bad (algebraMap C K (c q)))
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (cl : Fin r → Fin nk)
  (ρ : Fin nk → C)
  (P : C[X]) (l : ℕ) (b : L) (hb : b ∈ C⟮S.x⟯)
  (D : C[X]) (R : Fin r → C[X]) (hDR : ∀ q, D = (X - Polynomial.C (c q)) * R q)
  (hRne : ∀ q, (R q).eval (c q) ≠ 0)
  (hDoff : ∀ α : K, ¬ bad α → (∀ q, α ≠ algebraMap C K (c q)) → (D.map (algebraMap C K)).eval α ≠ 0)
  (hbP : b * aeval S.x (D * S.p ^ l) = aeval S.x P)
  (hres : ∀ q, P.eval (c q) * β q = m q * ρ (cl q) * (ω.eval (c q) - (c q)′) *
    (R q * S.p ^ l).eval (c q))

include hx hK hgood hbadc hconstC hc hβ hb hDR hRne hDoff hbP hres in
/-- **The logarithms are rational combinations of the class divisors `Δ_k`.** -/
theorem kxm_core (hn2 : S.n = 2) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ (k : ℕ) (d : ℕ → C) (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0),
      b * S.y = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) ∧
      (∀ j < k, (algebraMap C L (d j))′ = 0) ∧
      (∀ t : ℕ → ℚ, ∑ j ∈ Finset.range k, (t j : C) * d j = 0 → ∀ j < k, t j = 0) ∧
      ∃ lam : Fin nk → ℕ → ℚ,
        (∀ j (hj : j < k), ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α → ¬ bad α →
          (S.ordAt K ⟨w j, (hw j hj).1⟩ α β' : ℚ) = ∑ kk, lam kk j * dK c β m cl kk (α, β')) ∧
        ∀ kk, (∃ q, cl q = kk ∧ m q ≠ 0) →
          ∑ j ∈ Finset.range k, (lam kk j : C) * d j = ρ kk := by
  classical
  have hpc : ∀ q, S.p.eval (c q) ≠ 0 := fun q h0 ↦ by
    have := (hβ q).2
    rw [h0] at this
    exact (hβ q).1 (pow_eq_zero_iff S.hn.ne' |>.mp this)
  obtain ⟨k, d, w, hw, hind, heq', hdc, hzero, hraw⟩ :=
    S.kx_prep0 ω hx hK bad hgood hconstC c hbadc P l b hb D R hDR hRne hDoff hbP hpc (by omega) hbm
      s cs u hcs hu v hv heq
  refine ⟨k, d, w, hw, heq', hdc, hind, ?_⟩
  have hindK : ∀ t : ℕ → ℚ, ∑ j ∈ Finset.range k, algebraMap C K (d j) * (t j : K) = 0 →
      ∀ j < k, t j = 0 := by
    intro t ht
    apply hind t
    apply (algebraMap C K).injective
    rw [map_zero, ← ht, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_ratCast, mul_comm]
  have hvP : ∀ q, (algebraMap C K (β q)) ^ S.n =
      (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) := fun q ↦ by
    rw [eval_map, eval₂_at_apply, ← (hβ q).2, map_pow]
  have hvM : ∀ q, (-algebraMap C K (β q)) ^ S.n =
      (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) := fun q ↦ by
    rw [hn2, neg_sq, ← hn2]; exact hvP q
  set oP : Fin r → ℕ → ℤ := fun q j ↦ if h : j < k then
    S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) (algebraMap C K (β q)) else 0 with hoP
  set oM : Fin r → ℕ → ℤ := fun q j ↦ if h : j < k then
    S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) (-algebraMap C K (β q)) else 0 with hoM
  have hE : ∀ q, algebraMap C K ((ω.eval (c q) - (c q)′) * (R q * S.p ^ l).eval (c q)) ≠ 0 :=
      fun q ↦ by
    refine (_root_.map_ne_zero _).mpr (mul_ne_zero (fun h0 ↦ ?_) ?_)
    · apply hgood (algebraMap C K (c q)) (hbadc q)
      rw [hK, eval_map, eval₂_at_apply, sub_eq_zero.mp h0]
    · rw [eval_mul, eval_pow]
      exact mul_ne_zero (hRne q) (pow_ne_zero _ (hpc q))
  have hsP : ∀ q, ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oP q j : ℚ) : K) =
      algebraMap C K (m q * ρ (cl q)) := fun q ↦ by
    have h := hraw q _ (hvP q)
    refine mul_right_cancel₀ (hE q) ?_
    have e1 : ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oP q j : ℚ) : K) =
        ∑ j ∈ Finset.range k, algebraMap C K (d j) * (if h : j < k then
          (S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) (algebraMap C K (β q)) : K) else 0) :=
      Finset.sum_congr rfl fun j _ ↦ by simp only [hoP]; split_ifs <;> simp
    rw [e1, h, ← map_mul, ← map_mul, hres q]
    ring_nf
  have hsM : ∀ q, ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oM q j : ℚ) : K) =
      -algebraMap C K (m q * ρ (cl q)) := fun q ↦ by
    have h := hraw q _ (hvM q)
    refine mul_right_cancel₀ (hE q) ?_
    have e1 : ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oM q j : ℚ) : K) =
        ∑ j ∈ Finset.range k, algebraMap C K (d j) * (if h : j < k then
          (S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) (-algebraMap C K (β q)) : K) else 0) :=
      Finset.sum_congr rfl fun j _ ↦ by simp only [hoM]; split_ifs <;> simp
    rw [e1, h, mul_neg, neg_mul, ← map_mul, ← map_mul, hres q]
    ring_nf
  -- the coefficients of the classes
  set lam : Fin nk → ℕ → ℚ := fun kk j ↦ if h : ∃ q, cl q = kk ∧ m q ≠ 0 then
    (oP h.choose j : ℚ) / m h.choose else 0 with hlam
  have hsl : ∀ kk (h : ∃ q, cl q = kk ∧ m q ≠ 0),
      ∑ j ∈ Finset.range k, algebraMap C K (d j) * (lam kk j : K) = algebraMap C K (ρ kk) := by
    intro kk h
    have hq0 := h.choose_spec
    have hq0K : ((m h.choose : ℚ) : K) ≠ 0 := by exact_mod_cast hq0.2
    have hs := hsP h.choose
    rw [hq0.1, map_mul, map_natCast] at hs
    have : ∑ j ∈ Finset.range k, algebraMap C K (d j) * (lam kk j : K) =
        (∑ j ∈ Finset.range k, algebraMap C K (d j) * ((oP h.choose j : ℚ) : K)) / (m h.choose : K) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [hlam, dif_pos h, Rat.cast_div, Rat.cast_natCast]
      ring
    have hq0K' : (m h.choose : K) ≠ 0 := by exact_mod_cast hq0.2
    rw [this, hs, mul_div_cancel_left₀ _ hq0K']
  have hcoef : ∀ q, ∀ j < k, (oP q j : ℚ) = m q * lam (cl q) j ∧
      (oM q j : ℚ) = -(m q * lam (cl q) j) := by
    intro q j hj
    by_cases hmq : m q = 0
    · have hP := hindK (fun j ↦ (oP q j : ℚ)) (by rw [hsP q, hmq]; simp) j hj
      have hM := hindK (fun j ↦ (oM q j : ℚ)) (by rw [hsM q, hmq]; simp) j hj
      rw [hP, hM, hmq]; simp
    · have hex : ∃ q', cl q' = cl q ∧ m q' ≠ 0 := ⟨q, rfl, hmq⟩
      have hs := hsl (cl q) hex
      have hmul : ∑ j ∈ Finset.range k, algebraMap C K (d j) * ((m q : K) * (lam (cl q) j : K)) =
          (m q : K) * ∑ j ∈ Finset.range k, algebraMap C K (d j) * (lam (cl q) j : K) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
      have hP := hindK (fun j ↦ (oP q j : ℚ) - m q * lam (cl q) j) (by
        simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, mul_sub, Finset.sum_sub_distrib]
        rw [hsP q, hmul, hs, map_mul, map_natCast, sub_self]) j hj
      have hM := hindK (fun j ↦ (oM q j : ℚ) + m q * lam (cl q) j) (by
        simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, mul_add, Finset.sum_add_distrib]
        rw [hsM q, hmul, hs, map_mul, map_natCast, neg_add_cancel]) j hj
      constructor <;> linarith
  refine ⟨lam, fun j hj α β' hv hbα ↦ ?_, fun kk h ↦ ?_⟩
  · by_cases hα : ∃ q, α = algebraMap C K (c q)
    · obtain ⟨q, rfl⟩ := hα
      have hsum : ∀ sgn : ℚ, ∑ kk, lam kk j * (sgn * (mK m cl kk q : ℚ)) = sgn * (m q * lam (cl q) j) := by
        intro sgn
        rw [Finset.sum_eq_single (cl q)]
        · simp [mK]; ring
        · intro kk _ hkk; simp [mK, Ne.symm hkk]
        · simp
      rcases S.over_cq c β hβ hn2 q β' hv with rfl | rfl
      · have e := (hcoef q j hj).1
        simp only [hoP, dif_pos hj] at e
        rw [e]
        simp only [dK_plus S c β hc hβ m cl _ q]
        have := hsum 1
        simp only [one_mul] at this
        rw [this]
      · have e := (hcoef q j hj).2
        simp only [hoM, dif_pos hj] at e
        rw [e]
        simp only [dK_minus S c β hc hβ m cl _ q]
        have := hsum (-1)
        simp only [neg_one_mul] at this
        rw [← this]
    · push Not at hα
      rw [hzero j hj α β' hv hbα hα]
      simp [dK_off c β m cl _ α β' hα]
  · have := hsl kk h
    apply (algebraMap C K).injective
    rw [← this, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_ratCast, mul_comm]


end GenMulti

end SuperData

end Differential
