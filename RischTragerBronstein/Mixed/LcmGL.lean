import RischTragerBronstein.Mixed.NKExactCodes

/-!
# The executable lcm

`lcmG a b = a · (b div gcd(a, b))` and its monic list version `lcmGL`. For non-zero inputs:

* `lcmGL` is monic and divisible by every element (`lcmGL_spec`), so the `cofC` divisibility checks
  against it pass (`cofC_fst`) and the cofactors are exact (`cofC_snd`);
* it is squarefree when every element is (`lcmG` of squarefree polynomials is squarefree: a square
  `p²` dividing `a (b / g)` forces `p ∣ a` and `p ∣ b / g`, so `p ∣ g` and `p² ∣ b`).
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Curves.MT

open Tower.NestM

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

/-- Semantics of `lcmG`. -/
lemma lcmG_spec (a b : GPoly α) (ha : GPoly.toPoly M a ≠ 0) (hb : GPoly.toPoly M b ≠ 0) :
    GPoly.toPoly M (lcmG O a b) ≠ 0 ∧ GPoly.toPoly M a ∣ GPoly.toPoly M (lcmG O a b) ∧
      GPoly.toPoly M b ∣ GPoly.toPoly M (lcmG O a b) ∧
      (Squarefree (GPoly.toPoly M a) → Squarefree (GPoly.toPoly M b) →
        Squarefree (GPoly.toPoly M (lcmG O a b))) := by
  set g := (GPoly.egcd O a b).1
  obtain ⟨hga, hgb⟩ := GPoly.egcd_dvd M a b
  have hg0 : GPoly.toPoly M g ≠ 0 := fun h0 ↦ hb (zero_dvd_iff.mp (h0 ▸ hgb))
  have hbq := GPoly.div_mul_of_dvd M b g hg0 hgb
  set c := (GPoly.divMod O b g).1
  have hc0 : GPoly.toPoly M c ≠ 0 := fun h0 ↦ hb (by rw [hbq, h0, zero_mul])
  have e : GPoly.toPoly M (lcmG O a b) = GPoly.toPoly M a * GPoly.toPoly M c := by
    rw [lcmG, GPoly.toPoly_mul]
  rw [e]
  refine ⟨mul_ne_zero ha hc0, dvd_mul_right _ _, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hga
    rw [hbq, hk]
    exact ⟨k, by ring⟩
  · intro hsa hsb
    rw [squarefree_iff_no_irreducibles (mul_ne_zero ha hc0)]
    intro p hp hpp
    have hpr := hp.prime
    by_cases hpa : p ∣ GPoly.toPoly M a
    · obtain ⟨a', ha'⟩ := hpa
      have hpa' : ¬ p ∣ a' := fun h ↦ by
        obtain ⟨r, hr⟩ := h
        exact hp.not_isUnit (hsa p ⟨r, by rw [ha', hr]; ring⟩)
      have h1 : p ∣ a' * GPoly.toPoly M c := by
        rw [ha', mul_assoc] at hpp
        exact (mul_dvd_mul_iff_left hp.ne_zero).mp hpp
      have hpc : p ∣ GPoly.toPoly M c := (hpr.dvd_or_dvd h1).resolve_left hpa'
      have hpb : p ∣ GPoly.toPoly M b := by rw [hbq]; exact dvd_mul_of_dvd_left hpc _
      have hpg : p ∣ GPoly.toPoly M g := GPoly.dvd_egcd M a b ⟨a', ha'⟩ hpb
      exact hp.not_isUnit (hsb p (by rw [hbq]; exact mul_dvd_mul hpc hpg))
    · have h1 : p * p ∣ GPoly.toPoly M c := by
        obtain ⟨r, hr⟩ := hpp
        have : p ∣ GPoly.toPoly M a * GPoly.toPoly M c := ⟨p * r, by rw [hr]; ring⟩
        have hpc : p ∣ GPoly.toPoly M c := (hpr.dvd_or_dvd this).resolve_left hpa
        obtain ⟨s, hs⟩ := hpc
        have h2 : p ∣ GPoly.toPoly M a * s := by
          refine ⟨r, mul_left_cancel₀ hp.ne_zero ?_⟩
          linear_combination hr - GPoly.toPoly M a * hs
        obtain ⟨u, hu⟩ := (hpr.dvd_or_dvd h2).resolve_left hpa
        exact ⟨u, by rw [hs, hu]; ring⟩
      exact hp.not_isUnit (hsb p (by rw [hbq]; exact dvd_mul_of_dvd_left h1 _))

/-- Semantics of the fold. -/
lemma foldr_lcmG_spec (ds : List (GPoly α)) (hd : ∀ d ∈ ds, GPoly.toPoly M d ≠ 0) :
    GPoly.toPoly M (ds.foldr (lcmG O) [O.one]) ≠ 0 ∧
      (∀ d ∈ ds, GPoly.toPoly M d ∣ GPoly.toPoly M (ds.foldr (lcmG O) [O.one])) ∧
      ((∀ d ∈ ds, Squarefree (GPoly.toPoly M d)) →
        Squarefree (GPoly.toPoly M (ds.foldr (lcmG O) [O.one]))) := by
  induction ds with
  | nil =>
    have e : GPoly.toPoly M [O.one] = 1 := by simp [GPoly.toPoly, M.sem_one]
    simp only [List.foldr_nil, e]
    exact ⟨one_ne_zero, by simp, fun _ ↦ squarefree_one⟩
  | cons d ds ih =>
    obtain ⟨h0, hdv, hsq⟩ := ih fun x hx ↦ hd x (List.mem_cons_of_mem _ hx)
    obtain ⟨l0, la, lb, ls⟩ := lcmG_spec M d _ (hd d List.mem_cons_self) h0
    simp only [List.foldr_cons]
    refine ⟨l0, fun x hx ↦ ?_, fun hs ↦ ls (hs d List.mem_cons_self)
      (hsq fun x hx ↦ hs x (List.mem_cons_of_mem _ hx))⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact la
    · exact (hdv x hx).trans lb

/-- **Semantics of `lcmGL`**: monic, a multiple of each element, squarefree if they all are. -/
theorem lcmGL_spec (ds : List (GPoly α)) (hd : ∀ d ∈ ds, GPoly.toPoly M d ≠ 0) :
    (GPoly.toPoly M (lcmGL O ds)).Monic ∧
      (∀ d ∈ ds, GPoly.toPoly M d ∣ GPoly.toPoly M (lcmGL O ds)) ∧
      ((∀ d ∈ ds, Squarefree (GPoly.toPoly M d)) → Squarefree (GPoly.toPoly M (lcmGL O ds))) := by
  obtain ⟨h0, hdv, hsq⟩ := foldr_lcmG_spec M ds hd
  obtain ⟨e, hmon⟩ := toPoly_monicG M _ h0
  have hu : IsUnit (C (GPoly.toPoly M (ds.foldr (lcmG O) [O.one])).leadingCoeff⁻¹) :=
    isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr h0)).isUnit
  refine ⟨hmon, fun d hd' ↦ ?_, fun hs ↦ ?_⟩
  · rw [lcmGL, e]; exact Dvd.dvd.mul_left (hdv d hd') _
  · rw [lcmGL, e]
    exact (squarefree_mul_iff.mpr ⟨hu.isRelPrime_left, hu.squarefree, hsq hs⟩)

/-- A prime factor of `lcmG a b` divides `a` or `b`. -/
lemma lcmG_prime (a b : GPoly α) (_ha : GPoly.toPoly M a ≠ 0) (hb : GPoly.toPoly M b ≠ 0)
    (p : K[X]) (hp : Prime p) (hpl : p ∣ GPoly.toPoly M (lcmG O a b)) :
    p ∣ GPoly.toPoly M a ∨ p ∣ GPoly.toPoly M b := by
  set g := (GPoly.egcd O a b).1
  obtain ⟨-, hgb⟩ := GPoly.egcd_dvd M a b
  have hg0 : GPoly.toPoly M g ≠ 0 := fun h0 ↦ hb (zero_dvd_iff.mp (h0 ▸ hgb))
  have hbq := GPoly.div_mul_of_dvd M b g hg0 hgb
  have e : GPoly.toPoly M (lcmG O a b) = GPoly.toPoly M a * GPoly.toPoly M (GPoly.divMod O b g).1 := by
    rw [lcmG, GPoly.toPoly_mul]
  rw [e] at hpl
  rcases hp.dvd_or_dvd hpl with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [hbq]; exact dvd_mul_of_dvd_left h _)

/-- **A prime factor of `lcmGL ds` divides an element of `ds`.** -/
theorem lcmGL_prime (ds : List (GPoly α)) (hd : ∀ d ∈ ds, GPoly.toPoly M d ≠ 0)
    (p : K[X]) (hp : Prime p) (hpl : p ∣ GPoly.toPoly M (lcmGL O ds)) :
    ∃ d ∈ ds, p ∣ GPoly.toPoly M d := by
  have hf : p ∣ GPoly.toPoly M (ds.foldr (lcmG O) [O.one]) := by
    obtain ⟨h0, -, -⟩ := foldr_lcmG_spec M ds hd
    obtain ⟨e, -⟩ := toPoly_monicG M _ h0
    rw [lcmGL, e] at hpl
    have hu : IsUnit (C (GPoly.toPoly M (ds.foldr (lcmG O) [O.one])).leadingCoeff⁻¹) :=
      isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr h0)).isUnit
    rcases hp.dvd_or_dvd hpl with h | h
    · exact absurd (isUnit_of_dvd_unit h hu) hp.not_isUnit
    · exact h
  clear hpl
  induction ds with
  | nil =>
    have e : GPoly.toPoly M [O.one] = 1 := by simp [GPoly.toPoly, M.sem_one]
    simp only [List.foldr_nil, e] at hf
    exact absurd (isUnit_of_dvd_one hf) hp.not_isUnit
  | cons d ds ih =>
    have hd' : ∀ x ∈ ds, GPoly.toPoly M x ≠ 0 := fun x hx ↦ hd x (List.mem_cons_of_mem _ hx)
    obtain ⟨h0, -, -⟩ := foldr_lcmG_spec M ds hd'
    simp only [List.foldr_cons] at hf
    rcases lcmG_prime M d _ (hd d List.mem_cons_self) h0 p hp hf with h | h
    · exact ⟨d, List.mem_cons_self, h⟩
    · obtain ⟨x, hx, hpx⟩ := ih hd' h
      exact ⟨x, List.mem_cons_of_mem _ hx, hpx⟩

/-- `isMonicC` recognizes monic polynomials. -/
lemma isMonicC_of_monic (p : GPoly α) (hp : (GPoly.toPoly M p).Monic) : isMonicC O p = true := by
  have hne : GPoly.toPoly M p ≠ 0 := hp.ne_zero
  simp only [isMonicC, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨?_, ?_⟩
  · cases h : GPoly.isZero O p
    · rfl
    · exact absurd ((GPoly.isZero_iff M p).mp h) hne
  · rw [M.isZero_iff, M.sem_add, M.sem_neg, M.sem_one, add_neg_eq_zero, leadG,
      ← GPoly.leadingCoeff_toPoly M hne]
    exact hp

/-- The `cofC` check passes on a divisor. -/
lemma cofC_fst (q d : GPoly α) (hd : GPoly.toPoly M d ≠ 0)
    (hdq : GPoly.toPoly M d ∣ GPoly.toPoly M q) : (cofC O q d).1 = true := by
  simp only [cofC]
  exact (GPoly.isZero_iff M _).mpr (GPoly.divMod_exact M q d hd hdq)

/-- The `cofC` cofactor is exact. -/
lemma cofC_snd (q d : GPoly α) (hd : GPoly.toPoly M d ≠ 0)
    (hdq : GPoly.toPoly M d ∣ GPoly.toPoly M q) :
    GPoly.toPoly M q = GPoly.toPoly M (cofC O q d).2 * GPoly.toPoly M d :=
  GPoly.div_mul_of_dvd M q d hd hdq

end Curves.MT
