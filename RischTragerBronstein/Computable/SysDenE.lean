import RischTragerBronstein.Computable.SysDenG

/-!
# Coupled Risch systems: denominators at an exponential level

For `t′ = b t` (`w0 = 0`) the place `t = 0` is special (`t ∣ D t`). If `A₀` vanishes at `t = 0`,
`q(0) ≠ 0`, and no nonzero `z` has `z′ + j b z = 0` for an integer `j ≠ 0` (true at an
exponential level), the pole order at `t` of a solution is at most that of the right-hand side
(`sys_den_zero`). `sys_den_bound'` is `sys_den_bound` with the special places handled by such a
local argument (`hspec`), so that the denominator divides `h q^B`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K] (w0 b : K) {n : ℕ}

lemma DzL_X (w0 b : K) : DzL w0 b X = C w0 + C b * X := by
  simp [DzL, implicitDeriv]

lemma coeff_zero_DzL_exp (b : K) (P : K[X]) : (DzL 0 b P).coeff 0 = (P.coeff 0)′ := by
  rw [coeff_DzL]; simp

/-- **The special place `t = 0` of an exponential level.** -/
theorem sys_den_zero (b : K) (q : K[X]) (hq0 : q.coeff 0 ≠ 0) (A0 : Matrix (Fin n) (Fin n) K[X])
    (hA0 : ∀ i j, (A0 i j).coeff 0 = 0) (G0 : Fin n → K[X])
    (hom : ∀ z : K, z ≠ 0 → ∀ j : ℤ, j ≠ 0 → z′ + (j : K) * b * z ≠ 0)
    (Z : Fin n → K[X]) (hZ : ∃ i, (Z i).coeff 0 ≠ 0) (e s : ℕ) (u h1 : K[X])
    (hu : u.coeff 0 ≠ 0) (hh1 : h1.coeff 0 ≠ 0)
    (hs : SysSol 0 b q (X ^ s * h1) A0 G0 Z (X ^ e * u)) : e ≤ s := by
  by_contra hes
  push Not at hes
  obtain ⟨t, rfl⟩ : ∃ t, e = s + t + 1 := ⟨e - s - 1, by omega⟩
  obtain ⟨i, hi⟩ := hZ
  have hDX : DzL 0 b (X : K[X]) = C b * X := by rw [DzL_X]; simp
  have hDXe : DzL 0 b ((X : K[X]) ^ (s + t + 1)) = C (((s + t + 1 : ℕ) : K) * b) * X ^ (s + t + 1) := by
    rw [DzL_pow, hDX, C_mul, ← C_eq_natCast]; ring
  have key : q * h1 * (u * DzL 0 b (Z i) - (C (((s + t + 1 : ℕ) : K) * b) * u + DzL 0 b u) * Z i) +
      h1 * u * ∑ j, A0 i j * Z j = q * X ^ (t + 1) * u ^ 2 * G0 i := by
    have h := hs i
    rw [DzL_mul, hDXe] at h
    apply mul_left_cancel₀ (pow_ne_zero (2 * s + t + 1) (X_ne_zero : (X : K[X]) ≠ 0))
    linear_combination h
  have h0 := congrArg (fun P : K[X] ↦ P.coeff 0) key
  simp only [mul_coeff_zero, coeff_add, coeff_sub, finsetSum_coeff, coeff_C_zero,
    coeff_zero_DzL_exp, hA0, zero_mul, Finset.sum_const_zero, mul_zero, add_zero, coeff_X_pow,
    if_neg (show 0 ≠ t + 1 by omega), zero_mul] at h0
  -- `y = Z(0)/u(0)` satisfies `y′ = e b y`
  set z := (Z i).coeff 0
  set u0 := u.coeff 0
  have hrel : u0 * z′ - (((s + t + 1 : ℕ) : K) * b * u0 + u0′) * z = 0 := by
    have hqh : q.coeff 0 * h1.coeff 0 ≠ 0 := mul_ne_zero hq0 hh1
    exact (mul_eq_zero.mp h0).resolve_left hqh
  have hy : (z / u0)′ + ((-(s + t + 1 : ℤ) : ℤ) : K) * b * (z / u0) = 0 := by
    rw [Derivation.leibniz_div]
    simp only [smul_eq_mul]
    field_simp
    push_cast at hrel ⊢
    linear_combination hrel
  exact hom (z / u0) (div_ne_zero hi hu) (-(s + t + 1 : ℤ)) (by omega) hy

/-- **The global denominator bound with special places handled locally**: if every indicial root
at a factor of `q` is `≤ B` and at every special place the pole order is at most that of the
right-hand side, every solution `Z / d` has denominator dividing `h q^B`. -/
theorem sys_den_bound' (q h : K[X]) (hh : h ≠ 0) (A0 : Matrix (Fin n) (Fin n) K[X])
    (G0 : Fin n → K[X]) (B : ℕ)
    (hind : ∀ (p : K[X]) (e : ℕ), Irreducible p → p ∣ q →
      p ∣ (Matrix.of fun i j ↦ A0 i j - if i = j then C (e : K) * DzL w0 b q else 0).det → e ≤ B)
    (Z : Fin n → K[X]) (d : K[X]) (hd : d ≠ 0) (hs : SysSol w0 b q h A0 G0 Z d)
    (hspec : ∀ (p : K[X]), Irreducible p → p ∣ DzL w0 b p → ∀ (Z : Fin n → K[X]) (e s : ℕ)
      (u h1 : K[X]), (∃ i, ¬ p ∣ Z i) → ¬ p ∣ u → ¬ p ∣ h1 →
      SysSol w0 b q (p ^ s * h1) A0 G0 Z (p ^ e * u) → e ≤ s) (i : Fin n) :
    d ∣ h * q ^ B * Z i := by
  classical
  set Den := h * q ^ B with hDen
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
        rw [hDen, hhs]; exact Dvd.intro (h1 * q ^ B) (by ring)
      by_cases hpq : p ∣ q
      · obtain ⟨r, hr⟩ := hpq
        by_cases hes : e ≤ s
        · exact (pow_dvd_pow p hes).trans hph
        push Not at hes
        have hdet := sys_den_pole w0 b r A0 G0 p hirr Z1 hZ e s u h1 hu hh1 hes (hr ▸ hs2)
        rw [← hr] at hdet
        have heB := hind p e hirr ⟨r, hr⟩ hdet
        refine (pow_dvd_pow p heB).trans ((pow_dvd_pow_of_dvd ⟨r, hr⟩ B).trans ?_)
        exact Dvd.intro h (by rw [hDen]; ring)
      · by_cases hpn : p ∣ DzL w0 b p
        · exact (pow_dvd_pow p (hspec p hirr hpn Z1 e s u h1 hZ hu hh1 hs2)).trans hph
        · exact (pow_dvd_pow p (sys_den_normal w0 b q A0 G0 p hirr hpn hpq Z1 hZ e s u h1 hu hh1
            hs2)).trans hph
    have hk : k ≤ f0 + e :=
      le_of_pow_dvd_pow_mul p u hirr hu _ _ (by rw [pow_add, mul_assoc, ← hde, ← hd1]; exact hkd)
    obtain ⟨c, hc⟩ := hpe
    refine (pow_dvd_pow p hk).trans ⟨c * Z1 i, ?_⟩
    rw [hc, hZ1 i, pow_add]; ring

end Tower.Sys
