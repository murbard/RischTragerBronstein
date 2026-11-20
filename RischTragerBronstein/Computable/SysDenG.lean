import RischTragerBronstein.Computable.SysNorm
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

/-!
# Coupled Risch systems: the global denominator bound

For `Y′ + (A₀ / q) Y = G₀ / h` over `K(t)` (`t′ = w0 + b t`) with `q` squarefree and normal
(`IsCoprime q (D q)`), write a solution as `Y = Z / d` (`SysSol`, the cleared equation). At an
irreducible `p` with `d = pᵉ u`, `h = pˢ h₁` (and `Z` reduced at `p`):
* `p ∤ q`, `p` normal: `e ≤ s` (`sys_den_normal`);
* `p ∣ q`: `e ≤ s` or `e` is an indicial root, `p ∣ det(A₀ − e D(q) I)` (`sys_den_pole`);
* `p` special (`p ∣ D p`, then `p ∣ t` by hypothesis): no bound here (degree bounds treat `t`).
Hence, if every indicial root is `≤ B`, `d ∣ h q^B t^N Zᵢ` (`sys_den_bound`): every solution has
the form `W / (h q^B t^N)` with `W` polynomial.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K] (w0 b : K) {n : ℕ}

lemma DzL_mul (P Q : K[X]) : DzL w0 b (P * Q) = P * DzL w0 b Q + Q * DzL w0 b P := by
  have := Derivation.leibniz (implicitDeriv (C w0 + C b * X)) P Q
  simpa [smul_eq_mul] using this

lemma DzL_pow (P : K[X]) (e : ℕ) : DzL w0 b (P ^ (e + 1)) = ((e + 1 : ℕ) : K[X]) * P ^ e * DzL w0 b P := by
  have := Derivation.leibniz_pow (implicitDeriv (C w0 + C b * X)) P (e + 1)
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.add_sub_cancel] at this
  rw [DzL, this]
  ring

/-- **The cleared system**: `Y = Z / d` solves `Y′ + (A₀ / q) Y = G₀ / h`. -/
def SysSol (q h : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) (G0 : Fin n → K[X]) (Z : Fin n → K[X])
    (d : K[X]) : Prop :=
  ∀ i, q * h * (d * DzL w0 b (Z i) - DzL w0 b d * Z i) + h * d * ∑ j, A0 i j * Z j =
    q * d ^ 2 * G0 i

/-- Common factors cancel. -/
lemma sysSol_cancel (q h : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) (G0 : Fin n → K[X])
    (Z : Fin n → K[X]) (d c : K[X]) (hc : c ≠ 0)
    (hs : SysSol w0 b q h A0 G0 (fun i ↦ c * Z i) (c * d)) : SysSol w0 b q h A0 G0 Z d := by
  intro i
  have h1 := hs i
  simp only [DzL_mul] at h1
  have e : ∑ j, A0 i j * (c * Z j) = c * ∑ j, A0 i j * Z j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [e] at h1
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  apply mul_left_cancel₀ hc2
  linear_combination h1

/-- Scaling a solution. -/
lemma sysSol_scale (q h : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) (G0 : Fin n → K[X])
    (Z : Fin n → K[X]) (d c : K[X]) (hs : SysSol w0 b q h A0 G0 Z d) :
    SysSol w0 b q h A0 G0 (fun i ↦ c * Z i) (c * d) := by
  intro i
  have h1 := hs i
  simp only [DzL_mul]
  have e : ∑ j, A0 i j * (c * Z j) = c * ∑ j, A0 i j * Z j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [e]
  linear_combination c ^ 2 * h1

/-- Split off the full power of a non-unit. -/
lemma exists_pow_mul_not_dvd (p d : K[X]) (hp : Irreducible p) (hd : d ≠ 0) :
    ∃ e u, d = p ^ e * u ∧ ¬ p ∣ u := by
  classical
  have hdeg := natDegree_pos_of_irreducible hp
  have hex : ∃ f, ¬ p ^ (f + 1) ∣ d := ⟨d.natDegree, fun h ↦ by
    have := natDegree_le_of_dvd h hd
    rw [natDegree_pow] at this
    nlinarith⟩
  set f := Nat.find hex
  have hf : p ^ f ∣ d := by
    rcases Nat.eq_zero_or_pos f with h0 | hpos
    · rw [h0, pow_zero]; exact one_dvd _
    · have := Nat.find_min hex (show f - 1 < f by omega)
      rw [not_not, show f - 1 + 1 = f by omega] at this
      exact this
  obtain ⟨u, hu⟩ := hf
  refine ⟨f, u, hu, fun ⟨v, hv⟩ ↦ Nat.find_spec hex ⟨v, hu.trans (by rw [hv, pow_succ]; ring)⟩⟩
where natDegree_pos_of_irreducible {p : K[X]} (hp : Irreducible p) : 0 < p.natDegree :=
  natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hp)

lemma le_of_pow_dvd_pow_mul (p u : K[X]) (hp : Irreducible p) (hu : ¬ p ∣ u) (k m : ℕ)
    (h : p ^ k ∣ p ^ m * u) : k ≤ m := by
  by_contra hkm
  push Not at hkm
  have h1 : p ^ m * p ∣ p ^ m * u := by
    rw [← pow_succ]; exact (pow_dvd_pow p (by omega)).trans h
  exact hu ((mul_dvd_mul_iff_left (pow_ne_zero m hp.ne_zero)).mp h1)

/-- **Normal place outside `q`**: the pole order is at most that of the right-hand side. -/
theorem sys_den_normal (q : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) (G0 : Fin n → K[X])
    (p : K[X]) (hp : Irreducible p) (hpn : ¬ p ∣ DzL w0 b p) (hpq : ¬ p ∣ q)
    (Z : Fin n → K[X]) (hZ : ∃ i, ¬ p ∣ Z i) (e s : ℕ) (u h1 : K[X]) (hu : ¬ p ∣ u)
    (hh1 : ¬ p ∣ h1) (hs : SysSol w0 b q (p ^ s * h1) A0 G0 Z (p ^ e * u)) : e ≤ s := by
  by_contra hes
  push Not at hes
  obtain ⟨t, rfl⟩ : ∃ t, e = s + t + 1 := ⟨e - s - 1, by omega⟩
  obtain ⟨i, hi⟩ := hZ
  have hpr := hp.prime
  apply hi
  have key : ((s + t + 1 : ℕ) : K[X]) * q * h1 * u * DzL w0 b p * Z i = p * (q * h1 *
      (u * DzL w0 b (Z i) - DzL w0 b u * Z i) + h1 * u * ∑ j, A0 i j * Z j -
      q * p ^ (t + 1) * u ^ 2 * G0 i) := by
    have h := hs i
    rw [DzL_mul, show s + t + 1 = (s + t) + 1 by ring, DzL_pow] at h
    apply mul_left_cancel₀ (pow_ne_zero (2 * s + t) hp.ne_zero)
    linear_combination (-1 : K[X]) * h
  have hdvd : p ∣ ((s + t + 1 : ℕ) : K[X]) * q * h1 * u * DzL w0 b p * Z i := ⟨_, key⟩
  have hunit : IsUnit ((s + t + 1 : ℕ) : K[X]) := by
    rw [← C_eq_natCast]; exact isUnit_C.mpr (Ne.isUnit (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)))
  rcases hpr.dvd_or_dvd hdvd with h | h
  · rcases hpr.dvd_or_dvd h with h | h
    · rcases hpr.dvd_or_dvd h with h | h
      · rcases hpr.dvd_or_dvd h with h | h
        · rcases hpr.dvd_or_dvd h with h | h
          · exact absurd (isUnit_of_dvd_unit h hunit) hp.not_isUnit
          · exact absurd h hpq
        · exact absurd h hh1
      · exact absurd h hu
    · exact absurd h hpn
  · exact h

/-- **Place of `q`**: beyond the right-hand side, the pole order is an indicial root. -/
theorem sys_den_pole (r : K[X]) (A0 : Matrix (Fin n) (Fin n) K[X]) (G0 : Fin n → K[X])
    (p : K[X]) (hp : Irreducible p) (Z : Fin n → K[X]) (hZ : ∃ i, ¬ p ∣ Z i) (e s : ℕ)
    (u h1 : K[X]) (hu : ¬ p ∣ u) (hh1 : ¬ p ∣ h1) (hes : s < e)
    (hs : SysSol w0 b (p * r) (p ^ s * h1) A0 G0 Z (p ^ e * u)) :
    p ∣ (Matrix.of fun i j ↦ A0 i j - if i = j then C (e : K) * DzL w0 b (p * r) else 0).det := by
  obtain ⟨t, rfl⟩ : ∃ t, e = s + t + 1 := ⟨e - s - 1, by omega⟩
  have hpr := hp.prime
  refine den_local p r hp (DzL w0 b) (by rw [DzL_mul]; ring) Z hZ _ A0 fun i ↦ ?_
  have key : h1 * u * (r * p * DzL w0 b (Z i) - ((s + t + 1 : ℕ) : K[X]) * r * DzL w0 b p * Z i +
      ∑ j, A0 i j * Z j) = p * (r * p ^ (t + 1) * u ^ 2 * G0 i + r * h1 * DzL w0 b u * Z i) := by
    have h := hs i
    rw [DzL_mul, show s + t + 1 = (s + t) + 1 by ring, DzL_pow] at h
    apply mul_left_cancel₀ (pow_ne_zero (2 * s + t + 1) hp.ne_zero)
    linear_combination h
  have hdvd : p ∣ h1 * u * (r * p * DzL w0 b (Z i) - ((s + t + 1 : ℕ) : K[X]) * r * DzL w0 b p * Z i +
      ∑ j, A0 i j * Z j) := ⟨_, key⟩
  rcases hpr.dvd_or_dvd hdvd with h | h
  · rcases hpr.dvd_or_dvd h with h | h
    · exact absurd h hh1
    · exact absurd h hu
  · exact h

/-- **The global denominator bound for systems**: if every indicial root at a factor of `q` is
`≤ B`, every solution `Z / d` has denominator dividing `h q^B S`. -/
theorem sys_den_bound (q h : K[X]) (hh : h ≠ 0) (A0 : Matrix (Fin n) (Fin n) K[X])
    (G0 : Fin n → K[X]) (B : ℕ)
    (hind : ∀ (p : K[X]) (e : ℕ), Irreducible p → p ∣ q →
      p ∣ (Matrix.of fun i j ↦ A0 i j - if i = j then C (e : K) * DzL w0 b q else 0).det → e ≤ B)
    (Z : Fin n → K[X]) (d : K[X]) (hd : d ≠ 0) (hs : SysSol w0 b q h A0 G0 Z d) (S : K[X])
    (hS : ∀ (p : K[X]) (e : ℕ), Irreducible p → p ∣ DzL w0 b p → p ^ e ∣ d → p ^ e ∣ S) (i : Fin n) :
    d ∣ h * q ^ B * S * Z i := by
  classical
  set Den := h * q ^ B * S with hDen
  suffices H : ∀ x, x ∣ d → ∀ i, x ∣ Den * Z i from H d dvd_rfl i
  intro x
  induction x using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => intro h0; exact absurd (zero_dvd_iff.mp h0) hd
  | h1 hu => intro _ i; exact hu.dvd
  | hcp hxy hx hy =>
    intro hdv i
    exact hxy.isCoprime.mul_dvd (hx (dvd_of_mul_right_dvd hdv) i) (hy (dvd_of_mul_left_dvd hdv) i)
  | hpr k hpp =>
    rename_i p
    intro hkd i
    have hirr := hpp.irreducible
    -- the common power of `p` in `d` and `Z`
    obtain ⟨e0, u0, hd0, hu0⟩ := exists_pow_mul_not_dvd p d hirr hd
    have hex : ∃ f, ¬ (p ^ (f + 1) ∣ d ∧ ∀ i, p ^ (f + 1) ∣ Z i) :=
      ⟨e0, fun h ↦ absurd (le_of_pow_dvd_pow_mul p u0 hirr hu0 _ _ (hd0 ▸ h.1)) (by omega)⟩
    set f0 := Nat.find hex
    have hf0 : p ^ f0 ∣ d ∧ ∀ i, p ^ f0 ∣ Z i := by
      rcases Nat.eq_zero_or_pos f0 with h0 | hpos
      · rw [h0, pow_zero]; exact ⟨one_dvd _, fun _ ↦ one_dvd _⟩
      · have := Nat.find_min hex (show f0 - 1 < f0 by omega)
        rw [not_not, show f0 - 1 + 1 = f0 by omega] at this
        exact this
    obtain ⟨d1, hd1⟩ := hf0.1
    choose Z1 hZ1 using hf0.2
    have hs1 : SysSol w0 b q h A0 G0 Z1 d1 := by
      refine sysSol_cancel w0 b q h A0 G0 Z1 d1 (p ^ f0) (pow_ne_zero _ hirr.ne_zero) ?_
      have : (fun i ↦ p ^ f0 * Z1 i) = Z := funext fun i ↦ (hZ1 i).symm
      rw [this, ← hd1]; exact hs
    have hred : ¬ (p ∣ d1 ∧ ∀ i, p ∣ Z1 i) := by
      rintro ⟨⟨v, hv⟩, hZv⟩
      refine Nat.find_spec hex ⟨⟨v, hd1.trans (by rw [hv, pow_succ]; ring)⟩, fun i ↦ ?_⟩
      obtain ⟨w, hw⟩ := hZv i
      exact ⟨w, (hZ1 i).trans (by rw [hw, pow_succ]; ring)⟩
    have hd1ne : d1 ≠ 0 := by rintro rfl; exact hd (by rw [hd1, mul_zero])
    obtain ⟨e, u, hde, hu⟩ := exists_pow_mul_not_dvd p d1 hirr hd1ne
    obtain ⟨s, h1, hhs, hh1⟩ := exists_pow_mul_not_dvd p h hirr hh
    -- the bound at `p`
    have hpe : p ^ e ∣ Den := by
      rcases Nat.eq_zero_or_pos e with he0 | hepos
      · rw [he0, pow_zero]; exact one_dvd _
      have hZ : ∃ i, ¬ p ∣ Z1 i := by
        by_contra hc
        push Not at hc
        exact hred ⟨hde ▸ dvd_mul_of_dvd_left (dvd_pow_self p hepos.ne') u, hc⟩
      have hs2 : SysSol w0 b q (p ^ s * h1) A0 G0 Z1 (p ^ e * u) := by
        rw [← hhs, ← hde]; exact hs1
      have hph : p ^ s ∣ Den := by
        rw [hDen, hhs]; exact Dvd.intro (h1 * q ^ B * S) (by ring)
      by_cases hpq : p ∣ q
      · obtain ⟨r, hr⟩ := hpq
        by_cases hes : e ≤ s
        · exact (pow_dvd_pow p hes).trans hph
        push Not at hes
        have hdet := sys_den_pole w0 b r A0 G0 p hirr Z1 hZ e s u h1 hu hh1 hes (hr ▸ hs2)
        rw [← hr] at hdet
        have heB := hind p e hirr ⟨r, hr⟩ hdet
        refine (pow_dvd_pow p heB).trans ((pow_dvd_pow_of_dvd ⟨r, hr⟩ B).trans ?_)
        exact Dvd.intro (h * S) (by rw [hDen]; ring)
      · by_cases hpn : p ∣ DzL w0 b p
        · have hdv : p ^ e ∣ d := ⟨p ^ f0 * u, by rw [hd1, hde]; ring⟩
          exact (hS p e hirr hpn hdv).trans (Dvd.intro_left (h * q ^ B) rfl)
        · exact (pow_dvd_pow p (sys_den_normal w0 b q A0 G0 p hirr hpn hpq Z1 hZ e s u h1 hu hh1
            hs2)).trans hph
    have hk : k ≤ f0 + e :=
      le_of_pow_dvd_pow_mul p u hirr hu _ _ (by rw [pow_add, mul_assoc, ← hde, ← hd1]; exact hkd)
    obtain ⟨c, hc⟩ := hpe
    refine (pow_dvd_pow p hk).trans ⟨c * Z1 i, ?_⟩
    rw [hc, hZ1 i, pow_add]; ring

end Tower.Sys
