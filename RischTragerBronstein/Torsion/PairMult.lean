import Mathlib.Data.Nat.Factorization.Basic

/-!
# The multiplier for the two-prime torsion test

If some multiple `M Γ` is principal, the prime steps at `p` and `q` make `(m_p pᵛ) Γ` and
`(m_q q^w) Γ` principal for some `v, w`, hence also their gcd. **`dvd_pairMult`**: that gcd divides
`pairMult p q m_p m_q = gcd(m_p p^E, m_q q^E)` (`E = m_p + m_q`), whatever `v` and `w` are. So the
test can be run at `pairMult` instead of `m_p m_q` (for example `m₁₃ = 3`, `m₃₇ = 2` give `1`
instead of `6`).
-/

namespace Curves

/-- The multiplier `gcd(m_p p^E, m_q q^E)`, `E = m_p + m_q`. -/
def pairMult (p q mp mq : ℕ) : ℕ := Nat.gcd (mp * p ^ (mp + mq)) (mq * q ^ (mp + mq))

/-- One side: `gcd(m_p pᵛ, m_q q^w)` divides `m_p p^E` (`p ≠ q` primes, `E ≥ m_q`). -/
lemma gcd_dvd_side {p q mp mq : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hmq : 0 < mq)
    (E : ℕ) (hE : mq ≤ E) (v w : ℕ) : Nat.gcd (mp * p ^ v) (mq * q ^ w) ∣ mp * p ^ E := by
  set d := Nat.gcd (mp * p ^ v) (mq * q ^ w) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact (Nat.gcd_pos_of_pos_right _ (Nat.mul_pos hmq (pow_pos hq.pos _))).ne'
  have h1 : d ∣ mp * p ^ v := Nat.gcd_dvd_left _ _
  have h2 : d ∣ mq * q ^ w := Nat.gcd_dvd_right _ _
  rw [← Nat.ordProj_mul_ordCompl_eq_self d p, mul_comm (mp)]
  refine Nat.mul_dvd_mul ?_ ?_
  · -- the `p`-part divides `m_q`, hence is at most `p^E`
    have hpp : ordProj[p] d ∣ mq * q ^ w := (Nat.ordProj_dvd d p).trans h2
    have hcop : Nat.Coprime (ordProj[p] d) (q ^ w) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)
    have hmq' : ordProj[p] d ∣ mq := hcop.dvd_of_dvd_mul_right hpp
    refine pow_dvd_pow p ?_
    have hle : p ^ d.factorization p ≤ mq := Nat.le_of_dvd hmq hmq'
    have hlt : d.factorization p < p ^ d.factorization p := Nat.lt_pow_self hp.one_lt
    omega
  · -- the `p`-free part divides `m_p`
    have hcop : Nat.Coprime (ordCompl[p] d) (p ^ v) :=
      Nat.Coprime.pow_right _ (Nat.coprime_comm.mp (Nat.coprime_ordCompl hp hd0))
    exact hcop.dvd_of_dvd_mul_right ((Nat.ordCompl_dvd d p).trans h1)

/-- **The gcd of the two principal multiples divides `pairMult`.** -/
theorem dvd_pairMult {p q mp mq : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hmp : 0 < mp)
    (hmq : 0 < mq) (v w : ℕ) : Nat.gcd (mp * p ^ v) (mq * q ^ w) ∣ pairMult p q mp mq := by
  refine Nat.dvd_gcd (gcd_dvd_side hp hq hpq hmq _ (by omega) v w) ?_
  rw [Nat.gcd_comm]
  exact gcd_dvd_side hq hp (Ne.symm hpq) hmp _ (by omega) w v

lemma pairMult_pos {p q mp mq : ℕ} (hp : p.Prime) (hmp : 0 < mp) : 0 < pairMult p q mp mq :=
  Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hmp (pow_pos hp.pos _))

/-- `pairMult` divides the old multiplier `m_p m_q`. -/
lemma pairMult_dvd_mul {p q mp mq : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hmp : 0 < mp)
    (hmq : 0 < mq) : pairMult p q mp mq ∣ mp * mq := by
  have := dvd_pairMult hp hq hpq hmp hmq 0 0
  simp only [pow_zero, mul_one] at this
  -- `pairMult` divides `m_p p^E` and `m_q q^E`; its `p`-part divides `m_q`, the rest `m_p`
  set G := pairMult p q mp mq with hG
  have hG0 : G ≠ 0 := (pairMult_pos hp hmp).ne'
  have h1 : G ∣ mp * p ^ (mp + mq) := Nat.gcd_dvd_left _ _
  have h2 : G ∣ mq * q ^ (mp + mq) := Nat.gcd_dvd_right _ _
  rw [← Nat.ordProj_mul_ordCompl_eq_self G p, mul_comm mp]
  refine Nat.mul_dvd_mul ?_ ?_
  · have hcop : Nat.Coprime (ordProj[p] G) (q ^ (mp + mq)) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)
    exact hcop.dvd_of_dvd_mul_right ((Nat.ordProj_dvd G p).trans h2)
  · have hcop : Nat.Coprime (ordCompl[p] G) (p ^ (mp + mq)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_comm.mp (Nat.coprime_ordCompl hp hG0))
    exact hcop.dvd_of_dvd_mul_right ((Nat.ordCompl_dvd G p).trans h1)

end Curves
