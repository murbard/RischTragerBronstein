import RischTragerBronstein.Algebraic.SuperOrd

/-!
# The algebraic core of Abel's direction on a superelliptic curve

`IsPrincipalS Γ m`: the divisor `m (Γ − deg Γ · ∞)` is principal, i.e. some integral `w ≠ 0`
has order exactly `m Γ(Q)` at every finite point `Q` (its pole at infinity is then forced by the
degree theorem).

`abel_core`: if `w₀ ≠ 0` has order `z(Q)` at every non-branch point `Q` (with the points of
negative `z` in a finite set), then `n Γ` is principal, where `Γ(Q) = z(Q) + ∑ |z(Q')|` over the
points `Q'` of negative `z` above the same abscissa. The witness is
`w₀ⁿ · ∏ₑ (x − e)^{−ord_{e} w₀} · ∏_{Q'} (x − x(Q'))^{n |z(Q')|}`.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

/-- `m (Γ − deg Γ · ∞)` is principal. -/
def IsPrincipalS (K : Type*) [Field K] [Algebra C K] [IsAlgClosed K]
    (Γ : K × K → ℕ) (m : ℕ) : Prop :=
  ∃ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 ∧ S.IsIntegralS K w ∧
    ∀ Q : K × K, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 →
      S.ordAt K w Q.1 Q.2 = m * Γ Q

open Classical in
lemma ordAt_X_sub (c : C) (α β : K) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K (S.polyX (X - Polynomial.C c)) α β =
      if α = algebraMap C K c then (if β = 0 then (S.n : ℤ) else 1) else 0 := by
  rw [S.ordAt_polyX _ (X_sub_C_ne_zero c) α β hv, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, rootMultiplicity_X_sub_C]
  split_ifs <;> simp

open Classical in
/-- **The core of Abel's direction.** -/
theorem abel_core (w₀ : C⟮S.x⟯⟮S.y⟯) (hw₀ : w₀ ≠ 0) (z : K × K → ℤ)
    (hz : ∀ Q : K × K, Q.2 ≠ 0 → Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 →
      S.ordAt K w₀ Q.1 Q.2 = z Q)
    (Sneg : Finset (K × K)) (hSneg : ∀ Q ∈ Sneg, Q.2 ≠ 0 ∧
      Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1)
    (hneg : ∀ Q : K × K, Q.2 ≠ 0 → Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 → z Q < 0 →
      Q ∈ Sneg)
    (hsplit : ∀ e : K, (S.p.map (algebraMap C K)).eval e = 0 → e ∈ Set.range (algebraMap C K))
    (hSx : ∀ Q ∈ Sneg, Q.1 ∈ Set.range (algebraMap C K)) :
    S.IsPrincipalS K (fun Q ↦ if Q.2 = 0 then 0 else
      (z Q + ∑ Q' ∈ Sneg with Q'.1 = Q.1, |z Q'|).toNat) S.n := by
  set R := (S.p.map (algebraMap C K)).roots.toFinset
  have hRroot : ∀ e ∈ R, (S.p.map (algebraMap C K)).eval e = 0 := fun e he ↦
    isRoot_of_mem_roots (Multiset.mem_toFinset.mp he)
  have hpm : S.p.map (algebraMap C K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr S.hsq.ne_zero
  set ce : K → C := fun e ↦ if h : e ∈ Set.range (algebraMap C K) then Classical.choose h else 0
  have hce : ∀ e ∈ R, algebraMap C K (ce e) = e := fun e he ↦ by
    have h := hsplit e (hRroot e he)
    simp only [ce, dif_pos h]
    exact Classical.choose_spec h
  set aq : K × K → C := fun Q ↦ if h : Q.1 ∈ Set.range (algebraMap C K) then Classical.choose h
    else 0
  have haq : ∀ Q ∈ Sneg, algebraMap C K (aq Q) = Q.1 := fun Q hQ ↦ by
    have h := hSx Q hQ
    simp only [aq, dif_pos h]
    exact Classical.choose_spec h
  set A : C⟮S.x⟯⟮S.y⟯ := ∏ e ∈ R, S.polyX (X - Polynomial.C (ce e)) ^ (-S.ordAt K w₀ e 0)
  set B : C⟮S.x⟯⟮S.y⟯ := ∏ Q ∈ Sneg, S.polyX (X - Polynomial.C (aq Q)) ^ (S.n * (z Q).natAbs)
  have hX : ∀ c : C, S.polyX (X - Polynomial.C c) ≠ 0 := fun c ↦ S.polyX_ne_zero (X_sub_C_ne_zero c)
  have hA0 : A ≠ 0 := Finset.prod_ne_zero_iff.mpr fun e _ ↦ zpow_ne_zero _ (hX _)
  have hB0 : B ≠ 0 := Finset.prod_ne_zero_iff.mpr fun Q _ ↦ pow_ne_zero _ (hX _)
  set w := w₀ ^ S.n * A * B
  have hw0 : w ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hw₀) hA0) hB0
  -- the order of `w` at any point
  have hord : ∀ Q : K × K, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 →
      S.ordAt K w Q.1 Q.2 = S.n * S.ordAt K w₀ Q.1 Q.2 +
        ∑ e ∈ R, -S.ordAt K w₀ e 0 *
          (if Q.1 = e then (if Q.2 = 0 then (S.n : ℤ) else 1) else 0) +
        ∑ Q' ∈ Sneg, ((S.n * (z Q').natAbs : ℕ) : ℤ) *
          (if Q.1 = Q'.1 then (if Q.2 = 0 then (S.n : ℤ) else 1) else 0) := by
    intro Q hv
    rw [S.ordAt_mul hv (mul_ne_zero (pow_ne_zero _ hw₀) hA0) hB0,
      S.ordAt_mul hv (pow_ne_zero _ hw₀) hA0, S.ordAt_pow hv,
      S.ordAt_prod hv _ _ (fun e _ ↦ zpow_ne_zero _ (hX _)),
      S.ordAt_prod hv _ _ (fun Q' _ ↦ pow_ne_zero _ (hX _))]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun e he ↦ ?_
      rw [S.ordAt_zpow hv, S.ordAt_X_sub _ _ _ hv, hce e he]
    · refine Finset.sum_congr rfl fun Q' hQ' ↦ ?_
      rw [S.ordAt_pow hv, S.ordAt_X_sub _ _ _ hv, haq Q' hQ']
  have hform : ∀ Q : K × K, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 →
      S.ordAt K w Q.1 Q.2 = S.n * ((fun Q : K × K ↦ if Q.2 = 0 then 0 else
        (z Q + ∑ Q' ∈ Sneg with Q'.1 = Q.1, |z Q'|).toNat) Q : ℕ) := by
    intro Q hv
    rw [hord Q hv]
    by_cases hβ : Q.2 = 0
    · have he : (S.p.map (algebraMap C K)).eval Q.1 = 0 := by rw [← hv, hβ, zero_pow S.hn.ne']
      have hQR : Q.1 ∈ R := Multiset.mem_toFinset.mpr ((mem_roots hpm).mpr he)
      have e1 : ∑ e ∈ R, -S.ordAt K w₀ e 0 *
          (if Q.1 = e then (if Q.2 = 0 then (S.n : ℤ) else 1) else 0) =
          -S.ordAt K w₀ Q.1 0 * S.n := by
        rw [Finset.sum_eq_single Q.1 (fun e _ hne ↦ by rw [if_neg (Ne.symm hne), mul_zero])
          (fun h ↦ absurd hQR h), if_pos rfl, if_pos hβ]
      have e2 : ∑ Q' ∈ Sneg, ((S.n * (z Q').natAbs : ℕ) : ℤ) *
          (if Q.1 = Q'.1 then (if Q.2 = 0 then (S.n : ℤ) else 1) else 0) = 0 :=
        Finset.sum_eq_zero fun Q' hQ' ↦ by
          rw [if_neg, mul_zero]
          intro h
          obtain ⟨h1, h2⟩ := hSneg Q' hQ'
          rw [← h, he] at h2
          exact h1 ((pow_eq_zero_iff S.hn.ne').mp h2)
      rw [e1, e2]
      simp only [hβ, ↓reduceIte, CharP.cast_eq_zero, mul_zero]
      ring
    · have hne : ∀ e ∈ R, Q.1 ≠ e := fun e he h ↦ by
        have := hRroot e he
        rw [← h, ← hv] at this
        exact hβ ((pow_eq_zero_iff S.hn.ne').mp this)
      have e1 : ∑ e ∈ R, -S.ordAt K w₀ e 0 *
          (if Q.1 = e then (if Q.2 = 0 then (S.n : ℤ) else 1) else 0) = 0 :=
        Finset.sum_eq_zero fun e he ↦ by rw [if_neg (hne e he), mul_zero]
      have e2 : ∑ Q' ∈ Sneg, ((S.n * (z Q').natAbs : ℕ) : ℤ) *
          (if Q.1 = Q'.1 then (if Q.2 = 0 then (S.n : ℤ) else 1) else 0) =
          S.n * ∑ Q' ∈ Sneg with Q'.1 = Q.1, |z Q'| := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun Q' _ ↦ ?_
        by_cases h : Q.1 = Q'.1
        · rw [if_pos h, if_pos h.symm, if_neg hβ]; push_cast; ring
        · rw [if_neg h, if_neg (Ne.symm h)]; ring
      have hnonneg : 0 ≤ z Q + ∑ Q' ∈ Sneg with Q'.1 = Q.1, |z Q'| := by
        by_cases hzQ : z Q < 0
        · have hQS : Q ∈ Sneg.filter (fun Q' : K × K ↦ Q'.1 = Q.1) :=
            Finset.mem_filter.mpr ⟨hneg Q hβ hv hzQ, rfl⟩
          have h1 := Finset.single_le_sum (f := fun Q' : K × K ↦ |z Q'|)
            (fun Q' _ ↦ abs_nonneg (z Q')) hQS
          have h2 := neg_abs_le (z Q)
          linarith
        · exact add_nonneg (not_lt.mp hzQ) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
      rw [e1, e2, hz Q hβ hv]
      simp only [hβ, ↓reduceIte]
      rw [Int.toNat_of_nonneg hnonneg]
      ring
  refine ⟨w, hw0, fun α β hv ↦ ?_, hform⟩
  rw [hform (α, β) hv]
  positivity

end SuperData

end Differential
