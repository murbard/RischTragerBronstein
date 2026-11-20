import RischTragerBronstein.Torsion.SubRoot

/-!
# Reduction at large primes (2): the ring of `p`-integral elements of `NF M`

`ratSub p`: the rationals with denominator prime to `p`. When the coefficients of `M` and the
inverse of its leading coefficient are `p`-integral, the normal form modulo `M` preserves
`p`-integrality (`norm_lifts`), so the elements of `NF M` with `p`-integral representatives form a
subring **`nfIntSub`** — exactly the elements passing the test `pIntL p` of `nfRedAt`
(`mem_nfIntSub_iff`). With `rep_coeff_mem`, all coefficients of certified representatives are then
`p`-integral (**`rep_coeff_ok`**), at every precision.
-/

open Polynomial Filter

namespace Curves

open CPoly Sup

section RatSub

variable (p : ℕ) [hp : Fact p.Prime]

/-- The rationals with denominator prime to `p`. -/
def ratSub : Subring ℚ where
  carrier := {c | c.den % p ≠ 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    intro h
    rcases (hp.out.dvd_mul.mp (dvd_trans (Nat.dvd_of_mod_eq_zero h) (Rat.mul_den_dvd a b))) with h1 | h1
    · exact ha (Nat.mod_eq_zero_of_dvd h1)
    · exact hb (Nat.mod_eq_zero_of_dvd h1)
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Rat.den_ofNat]
    rw [Nat.mod_eq_of_lt hp.out.one_lt]; exact one_ne_zero
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    intro h
    rcases (hp.out.dvd_mul.mp (dvd_trans (Nat.dvd_of_mod_eq_zero h) (Rat.add_den_dvd a b))) with h1 | h1
    · exact ha (Nat.mod_eq_zero_of_dvd h1)
    · exact hb (Nat.mod_eq_zero_of_dvd h1)
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Rat.den_zero]
    rw [Nat.mod_eq_of_lt hp.out.one_lt]; exact one_ne_zero
  neg_mem' {a} ha := by simpa using ha

lemma pIntL_iff (l : CPoly ℚ) : Jac.pIntL p l = true ↔ ∀ c ∈ l, c ∈ ratSub p := by
  simp only [Jac.pIntL, List.all_eq_true, bne_iff_ne, ne_eq]
  rfl

/-- `p`-integrality of a list through its polynomial. -/
lemma mem_iff_lifts (l : CPoly ℚ) :
    (∀ c ∈ l, c ∈ ratSub p) ↔ toPoly l ∈ lifts (ratSub p).subtype := by
  rw [lifts_iff_coeff_lifts]
  constructor
  · intro h n
    rw [coeff_toPoly]
    by_cases hn : n < l.length
    · rw [List.getD_eq_getElem _ _ hn]; exact ⟨⟨_, h _ (List.getElem_mem hn)⟩, rfl⟩
    · rw [List.getD_eq_default _ _ (by omega)]; exact ⟨0, rfl⟩
  · intro h c hc
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨c', hc'⟩ := h n
    rw [coeff_toPoly, List.getD_eq_getElem _ _ hn] at hc'
    rw [← hc']; exact c'.2

end RatSub

section NormInt

variable {p : ℕ} [Fact p.Prime] {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

/-- **The normal form preserves `p`-integrality.** -/
lemma norm_lifts (hM : toPoly M ∈ lifts (ratSub p).subtype)
    (hlc : (toPoly M).leadingCoeff⁻¹ ∈ ratSub p) {l : CPoly ℚ}
    (hl : toPoly l ∈ lifts (ratSub p).subtype) :
    toPoly (NFC.norm M l) ∈ lifts (ratSub p).subtype := by
  set A := ratSub p
  have hM0 : toPoly M ≠ 0 := NFC.f_ne_zero M
  set M' := Polynomial.C (toPoly M).leadingCoeff⁻¹ * toPoly M with hM'
  have hM'l : M' ∈ lifts A.subtype := (lifts A.subtype).mul_mem (C_mem_lifts (ratSub p).subtype ⟨_, hlc⟩) hM
  have hM'm : M'.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀
    (leadingCoeff_ne_zero.mpr hM0))
  obtain ⟨MA, hMA, hMAd, hMAm⟩ := lifts_and_degree_eq_and_monic hM'l hM'm
  obtain ⟨lA, hlA⟩ := hl
  -- the remainder over `A`
  have hr : (lA %ₘ MA).map A.subtype = toPoly l %ₘ M' := by
    rw [Polynomial.map_modByMonic _ hMAm, hMA]; exact congrArg (· %ₘ M') hlA
  have hdeg : ((toPoly l %ₘ M').degree) < (toPoly M).degree := by
    have := degree_modByMonic_lt (toPoly l) hM'm
    rwa [hM', degree_C_mul (inv_ne_zero (leadingCoeff_ne_zero.mpr hM0))] at this
  have hdvd : toPoly M ∣ toPoly (NFC.norm M l) - toPoly l %ₘ M' := by
    have h1 := NFC.norm_dvd M l
    have h2 : toPoly M ∣ toPoly l - toPoly l %ₘ M' := by
      have e := modByMonic_add_div (toPoly l) M'
      rw [show toPoly l - toPoly l %ₘ M' = M' * (toPoly l /ₘ M') by linear_combination -e]
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this
  have heq : toPoly (NFC.norm M l) = toPoly l %ₘ M' := by
    refine sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt hdvd ?_)
    exact (degree_sub_le _ _).trans_lt (max_lt (NFC.norm_degree M l) hdeg)
  rw [heq, ← hr]
  exact ⟨_, rfl⟩

variable (p M)

/-- The ring of `p`-integral elements of `NF M` (for `M` `p`-integral with a unit leading
coefficient). -/
def nfIntSub (hM : toPoly M ∈ lifts (ratSub p).subtype)
    (hlc : (toPoly M).leadingCoeff⁻¹ ∈ ratSub p) : Subring (NFC.NF M) where
  carrier := {x | toPoly x.1 ∈ lifts (ratSub p).subtype}
  mul_mem' {x y} hx hy := by
    change toPoly (NFC.norm M (mul x.1 y.1)) ∈ lifts (ratSub p).subtype
    exact norm_lifts hM hlc (by rw [toPoly_mul]; exact (lifts _).mul_mem hx hy)
  one_mem' := by
    change toPoly (NFC.norm M [1]) ∈ lifts (ratSub p).subtype
    exact norm_lifts hM hlc ((mem_iff_lifts p _).mp (by simpa using (ratSub p).one_mem))
  add_mem' {x y} hx hy := by
    change toPoly (NFC.norm M (add x.1 y.1)) ∈ lifts (ratSub p).subtype
    exact norm_lifts hM hlc (by rw [toPoly_add]; exact (lifts _).add_mem hx hy)
  zero_mem' := by
    change toPoly (NFC.norm M []) ∈ lifts (ratSub p).subtype
    exact norm_lifts hM hlc ((mem_iff_lifts p _).mp (by simp))
  neg_mem' {x} hx := by
    change toPoly (NFC.norm M (smul (-1) x.1)) ∈ lifts (ratSub p).subtype
    refine norm_lifts hM hlc ?_
    rw [toPoly_smul]
    exact (lifts _).mul_mem (C_mem_lifts (ratSub p).subtype ⟨-1, (ratSub p).neg_mem (ratSub p).one_mem⟩) hx

lemma mem_nfIntSub_iff (hM : toPoly M ∈ lifts (ratSub p).subtype)
    (hlc : (toPoly M).leadingCoeff⁻¹ ∈ ratSub p) (x : NFC.NF M) :
    x ∈ nfIntSub p M hM hlc ↔ Jac.pIntL p x.1 = true := by
  rw [pIntL_iff, mem_iff_lifts]; rfl

end NormInt

section Ev

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

/-- The minimal polynomial is `p`-integral with a unit leading coefficient at all large `p`. -/
theorem ev_nfM : ∀ᶠ p in atTop, ∀ _ : Fact p.Prime,
    toPoly M ∈ lifts (ratSub p).subtype ∧ (toPoly M).leadingCoeff⁻¹ ∈ ratSub p := by
  refine eventually_atTop.mpr ⟨(M.map (·.den)).sum + ((toPoly M).leadingCoeff⁻¹).den + 1,
    fun p hp _ ↦ ⟨(mem_iff_lifts p M).mp fun c hc ↦ ?_, ?_⟩⟩
  · have := Jac.den_le_sum hc
    show c.den % p ≠ 0
    rw [Nat.mod_eq_of_lt (by omega)]; exact c.den_nz
  · show _ % p ≠ 0
    rw [Nat.mod_eq_of_lt (by omega)]; exact Rat.den_nz _

variable {p : ℕ} [Fact p.Prime]

/-- **All coefficients of certified representatives are integral** (at a prime where `M` is
integral), whatever the precision. -/
theorem rep_coeff_ok (R : RedFns p (NFC.NF M)) (hR : NFRed p R)
    (hM : toPoly M ∈ lifts (ratSub p).subtype) (hlc : (toPoly M).leadingCoeff⁻¹ ∈ ratSub p)
    {Fc : BPoly (NFC.NF M)} (hF : ∀ P ∈ Fc, ∀ c ∈ P, R.ok c = true) {a : NFC.NF M}
    (ha : R.ok a = true) {e prec : ℕ} {y : CPoly (NFC.NF M)} (hy : ∀ c ∈ y, R.ok c = true)
    (h : rootCheck Fc a e prec y = true)
    (hu : R.ok ((bivEval (derivYB Fc) (shiftC a e) y).getD
      (ordC (bivEval (derivYB Fc) (shiftC a e) y)) 0)⁻¹ = true)
    (ρ : PowerSeries (NFC.NF M)) (hρ : (repEq (RingHom.id _) Fc a e).eval ρ = 0)
    (hd : (PowerSeries.X : PowerSeries (NFC.NF M)) ^ prec ∣ ρ - thetaT (RingHom.id _) (toPoly y)) :
    ∀ i, R.ok (PowerSeries.coeff i ρ) = true := by
  have hO : ∀ x, x ∈ nfIntSub p M hM hlc ↔ R.ok x = true := fun x ↦ by
    rw [mem_nfIntSub_iff, hR]
  intro i
  refine (hO _).mp (rep_coeff_mem (nfIntSub p M hM hlc) (fun P hP c hc ↦ (hO c).mpr (hF P hP c hc))
    ((hO a).mpr ha) (fun c hc ↦ (hO c).mpr (hy c hc)) h ((hO _).mpr hu) ρ hρ hd i)

end Ev

end Curves
