import RischTragerBronstein.Weil.Stepanov2
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Stepanov's method, step 3: the independence lemma

Over `F = 𝔽_p` (`p` odd), let `f ≠ 0` have an irreducible factor `P` of odd multiplicity and put
`c = (p − 1)/2`. If `∑_{j<J} (rⱼ + sⱼ f^c) X^{jp} = 0` with `deg f + 2 deg rⱼ < p` and
`deg f + 2 deg sⱼ < p`, then all `rⱼ = sⱼ = 0` (`indep`).

Proof: with `A = ∑ rⱼ X^{jp}`, `B = ∑ sⱼ X^{jp}`, `A = −f^c B` gives `f A² = f^p B² = f(X^p) B²`.
Reading `X^p` as a new variable `Y` (`eval_X_pow_eq_zero`: base-`p` digits of degree `< p` are
unique) gives `f(X) Ah² = f(Y) Bh²` in `F[X][Y]`; the irreducible `P(X)` divides the left side to an
odd power and the right side to an even power unless `Bh = 0`.
-/

open Polynomial

namespace Stepanov

section Digits

variable {R : Type*} [CommRing R]

/-- The coefficient of `X^{kq+i}` of `Ah(X, X^q)` is the `i`-th coefficient of `Ah_k`. -/
lemma coeff_eval_X_pow (q : ℕ) (Ah : R[X][X]) (hdeg : ∀ k, (Ah.coeff k).natDegree < q ∨ Ah.coeff k = 0)
    (k i : ℕ) (hi : i < q) : (Ah.eval (X ^ q)).coeff (k * q + i) = (Ah.coeff k).coeff i := by
  classical
  rw [eval_eq_sum, sum_def, finset_sum_coeff]
  have hterm : ∀ l, ((Ah.coeff l) * (X ^ q) ^ l).coeff (k * q + i) =
      if l = k then (Ah.coeff k).coeff i else 0 := by
    intro l
    rw [← pow_mul, coeff_mul_X_pow']
    by_cases hlk : l = k
    · subst hlk
      rw [if_pos (by rw [mul_comm]; omega), if_pos rfl]
      congr 1; rw [mul_comm]; omega
    · rw [if_neg hlk]
      split_ifs with h1
      · rcases lt_or_gt_of_ne hlk with hlt | hgt
        · apply coeff_eq_zero_of_natDegree_lt
          have : q * l + q ≤ k * q := by nlinarith
          rcases hdeg l with hd | hz
          · omega
          · rw [hz, natDegree_zero]; omega
        · exfalso
          have : k * q + q ≤ q * l := by nlinarith
          omega
      · rfl
  rw [Finset.sum_congr rfl fun l _ ↦ hterm l, Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · rw [notMem_support_iff.mp hk, coeff_zero]

/-- **Base-`q` digits are unique**: if the coefficients of `Ah` have degree `< q`, then
`Ah(X, X^q) = 0` forces `Ah = 0`. -/
lemma eq_zero_of_eval_X_pow (q : ℕ) (hq : 0 < q) (Ah : R[X][X])
    (hdeg : ∀ k, (Ah.coeff k).natDegree < q ∨ Ah.coeff k = 0) (h : Ah.eval (X ^ q) = 0) : Ah = 0 := by
  ext k i
  rw [coeff_zero, coeff_zero]
  by_cases hi : i < q
  · rw [← coeff_eval_X_pow q Ah hdeg k i hi, h, coeff_zero]
  · rcases hdeg k with hd | hz
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
    · rw [hz, coeff_zero]

/-- Coefficientwise degree bounds multiply. -/
lemma coeff_mul_natDegree_le (U V : R[X][X]) (a b : ℕ) (hU : ∀ k, (U.coeff k).natDegree ≤ a)
    (hV : ∀ k, (V.coeff k).natDegree ≤ b) (k : ℕ) : ((U * V).coeff k).natDegree ≤ a + b := by
  rw [coeff_mul]
  refine natDegree_sum_le_of_forall_le _ _ fun ij _ ↦ ?_
  exact (natDegree_mul_le).trans (Nat.add_le_add (hU _) (hV _))

end Digits

section Parity

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Exponents of a prime agree on both sides of `π^a X = π^b Y` when `π ∤ X, Y`. -/
lemma pow_eq_of_mul_eq {π X Y : R} (hπ : Prime π) (hX : ¬ π ∣ X) (hY : ¬ π ∣ Y) {a b : ℕ}
    (h : π ^ a * X = π ^ b * Y) : a = b := by
  by_contra hab
  have hπ0 : π ≠ 0 := hπ.ne_zero
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [pow_add, pow_add, mul_assoc, mul_assoc] at h
    have := mul_left_cancel₀ (pow_ne_zero a hπ0) h
    exact hX ⟨π ^ t * Y, by rw [this, pow_succ]; ring⟩
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    rw [pow_add, pow_add, mul_assoc, mul_assoc] at h
    have := mul_left_cancel₀ (pow_ne_zero b hπ0) h
    exact hY ⟨π ^ t * X, by rw [← this, pow_succ]; ring⟩

end Parity

variable {p : ℕ} [hp : Fact p.Prime]

local notation "F" => ZMod p

/-- `Ah = ∑_{j<J} rⱼ Yʲ`. -/
noncomputable def bivOf (J : ℕ) (r : ℕ → F[X]) : F[X][X] :=
  ∑ j ∈ Finset.range J, monomial j (r j)

lemma coeff_bivOf (J : ℕ) (r : ℕ → F[X]) (k : ℕ) :
    (bivOf J r).coeff k = if k < J then r k else 0 := by
  classical
  rw [bivOf, finsetSum_coeff]
  simp only [coeff_monomial]
  simp [Finset.sum_ite_eq', Finset.mem_range]

lemma eval_bivOf (J : ℕ) (r : ℕ → F[X]) :
    (bivOf J r).eval (X ^ p) = ∑ j ∈ Finset.range J, r j * X ^ (j * p) := by
  rw [bivOf, eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [eval_monomial, ← pow_mul, mul_comm p j]

/-- **The independence lemma.** -/
theorem indep (hp2 : p ≠ 2) (f : F[X]) (hf0 : f ≠ 0) (P : F[X]) (hP : Irreducible P) (e : ℕ)
    (he : Odd e) (hPe : P ^ e ∣ f) (hPe1 : ¬ P ^ (e + 1) ∣ f) (J : ℕ) (r s : ℕ → F[X])
    (hr : ∀ j < J, f.natDegree + 2 * (r j).natDegree < p)
    (hs : ∀ j < J, f.natDegree + 2 * (s j).natDegree < p)
    (h : ∑ j ∈ Finset.range J, (r j + s j * f ^ ((p - 1) / 2)) * X ^ (j * p) = 0) :
    ∀ j < J, r j = 0 ∧ s j = 0 := by
  classical
  set c := (p - 1) / 2 with hc
  have hp1 : 2 * c + 1 = p := by
    have := hp.out.eq_one_or_self_of_dvd 2
    have hodd : p % 2 = 1 := (Nat.Prime.eq_one_or_self_of_dvd hp.out 2 |> fun _ ↦
      Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2))
    omega
  set Ah := bivOf J r with hAh
  set Bh := bivOf J s with hBh
  set A := ∑ j ∈ Finset.range J, r j * X ^ (j * p) with hA
  set B := ∑ j ∈ Finset.range J, s j * X ^ (j * p) with hB
  have hAB : A = -(f ^ c * B) := by
    rw [hA, hB, eq_neg_iff_add_eq_zero, ← h, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  -- `f A² = f(X^p) B²`
  have hkey : f * A ^ 2 = expand F p f * B ^ 2 := by
    have e : f ^ p = f ^ (2 * c + 1) := congrArg (fun n ↦ f ^ n) hp1.symm
    rw [ZMod.expand_card, hAB, e]; ring
  -- in two variables
  set D : F[X][X] := C f * Ah ^ 2 - f.map C * Bh ^ 2 with hD
  have hDeval : D.eval (X ^ p) = 0 := by
    rw [hD, eval_sub, eval_mul, eval_mul, eval_pow, eval_pow, eval_C, eval_map, ← coe_expand,
      hAh, hBh, eval_bivOf, eval_bivOf, ← hA, ← hB, hkey, sub_self]
  -- the coefficients have degree `< p`
  set br := (Finset.range J).sup fun j ↦ (r j).natDegree with hbr
  set bs := (Finset.range J).sup fun j ↦ (s j).natDegree with hbs
  have hbrJ : ∀ k, ((bivOf J r).coeff k).natDegree ≤ br := fun k ↦ by
    rw [coeff_bivOf]; split_ifs with hk
    · exact Finset.le_sup (f := fun j ↦ (r j).natDegree) (Finset.mem_range.mpr hk)
    · simp
  have hbsJ : ∀ k, ((bivOf J s).coeff k).natDegree ≤ bs := fun k ↦ by
    rw [coeff_bivOf]; split_ifs with hk
    · exact Finset.le_sup (f := fun j ↦ (s j).natDegree) (Finset.mem_range.mpr hk)
    · simp
  have hbr' : f.natDegree + 2 * br < p ∨ J = 0 := by
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · exact Or.inr hJ
    · left
      obtain ⟨j, hj, hjm⟩ := Finset.exists_mem_eq_sup (Finset.range J)
        (Finset.nonempty_range_iff.mpr (by omega)) fun j ↦ (r j).natDegree
      rw [hbr, hjm]; exact hr j (Finset.mem_range.mp hj)
  have hbs' : f.natDegree + 2 * bs < p ∨ J = 0 := by
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · exact Or.inr hJ
    · left
      obtain ⟨j, hj, hjm⟩ := Finset.exists_mem_eq_sup (Finset.range J)
        (Finset.nonempty_range_iff.mpr (by omega)) fun j ↦ (s j).natDegree
      rw [hbs, hjm]; exact hs j (Finset.mem_range.mp hj)
  rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
  · intro j hj; omega
  have hbr'' := hbr'.resolve_right (by omega)
  have hbs'' := hbs'.resolve_right (by omega)
  have hDdeg : ∀ k, (D.coeff k).natDegree < p ∨ D.coeff k = 0 := by
    intro k
    left
    have h1 : ((C f * Ah ^ 2).coeff k).natDegree ≤ f.natDegree + (br + br) := by
      refine coeff_mul_natDegree_le _ _ _ _ (fun k ↦ ?_) (fun k ↦ ?_) k
      · rw [coeff_C]; split_ifs <;> simp
      · rw [pow_two]; exact coeff_mul_natDegree_le _ _ _ _ hbrJ hbrJ k
    have h2 : ((f.map C * Bh ^ 2).coeff k).natDegree ≤ 0 + (bs + bs) := by
      refine coeff_mul_natDegree_le _ _ _ _ (fun k ↦ ?_) (fun k ↦ ?_) k
      · rw [coeff_map]; simp
      · rw [pow_two]; exact coeff_mul_natDegree_le _ _ _ _ hbsJ hbsJ k
    rw [hD, coeff_sub]
    have := natDegree_sub_le ((C f * Ah ^ 2).coeff k) ((f.map C * Bh ^ 2).coeff k)
    omega
  have hD0 := eq_zero_of_eval_X_pow p hp.out.pos D hDdeg hDeval
  have hEq : C f * Ah ^ 2 = f.map C * Bh ^ 2 := sub_eq_zero.mp (by rw [← hD]; exact hD0)
  have hmap0 : f.map C ≠ 0 := (Polynomial.map_ne_zero_iff C_injective).mpr hf0
  -- `Bh = 0`
  have hB0 : Bh = 0 := by
    by_contra hBne
    have hAne : Ah ≠ 0 := by
      intro hA0
      rw [hA0, zero_pow two_ne_zero, mul_zero] at hEq
      exact mul_ne_zero hmap0 (pow_ne_zero 2 hBne) hEq.symm
    have hPprime : Prime P := hP.prime
    have hπ : Prime (C P : F[X][X]) := prime_C_iff.mpr hPprime
    -- `π ∤ f(Y)`
    have hπf : ¬ (C P : F[X][X]) ∣ f.map C := by
      rintro ⟨Q, hQ⟩
      apply hf0
      ext i
      have hc := congrArg (fun G : F[X][X] ↦ G.coeff i) hQ
      simp only [coeff_map, coeff_C_mul] at hc
      -- `P ∣ C (f.coeff i)` with `P` non-constant
      have hdvd : P ∣ C (f.coeff i) := ⟨Q.coeff i, hc⟩
      by_contra hne
      have hu : IsUnit (C (f.coeff i)) := isUnit_C.mpr (Ne.isUnit hne)
      exact hP.not_isUnit (isUnit_of_dvd_unit hdvd hu)
    obtain ⟨f', hf'⟩ := hPe
    have hf'P : ¬ P ∣ f' := by
      rintro ⟨g, rfl⟩; exact hPe1 ⟨g, by rw [hf']; ring⟩
    have hπf' : ¬ (C P : F[X][X]) ∣ C f' := by
      rintro ⟨Q, hQ⟩
      apply hf'P
      have := congrArg (fun G : F[X][X] ↦ G.coeff 0) hQ
      simp only [coeff_C_zero, coeff_C_mul] at this
      exact ⟨Q.coeff 0, this⟩
    obtain ⟨u, Ah', hAh'd, hAh'⟩ := WfDvdMonoid.max_power_factor hAne hπ.irreducible
    obtain ⟨v, Bh', hBh'd, hBh'⟩ := WfDvdMonoid.max_power_factor hBne hπ.irreducible
    have hX : ¬ (C P : F[X][X]) ∣ C f' * Ah' ^ 2 := by
      intro hd
      rcases hπ.dvd_or_dvd hd with h1 | h1
      · exact hπf' h1
      · exact hAh'd (hπ.dvd_of_dvd_pow h1)
    have hY : ¬ (C P : F[X][X]) ∣ f.map C * Bh' ^ 2 := by
      intro hd
      rcases hπ.dvd_or_dvd hd with h1 | h1
      · exact hπf h1
      · exact hBh'd (hπ.dvd_of_dvd_pow h1)
    have hEq' : (C P) ^ (e + 2 * u) * (C f' * Ah' ^ 2) = (C P) ^ (2 * v) * (f.map C * Bh' ^ 2) := by
      have : C f = C P ^ e * C f' := by rw [hf', C_mul, C_pow]
      rw [this, hAh', hBh'] at hEq
      rw [pow_add, pow_mul, pow_mul]
      linear_combination hEq
    have := pow_eq_of_mul_eq hπ hX hY hEq'
    obtain ⟨t, rfl⟩ := he
    omega
  have hA0 : Ah = 0 := by
    rw [hB0, zero_pow two_ne_zero, mul_zero] at hEq
    rcases mul_eq_zero.mp hEq with h1 | h1
    · exact absurd (C_eq_zero.mp h1) hf0
    · exact pow_eq_zero_iff two_ne_zero |>.mp h1
  intro j hj
  constructor
  · have := congrArg (fun G : F[X][X] ↦ G.coeff j) hA0
    simpa [hAh, coeff_bivOf, hj] using this
  · have := congrArg (fun G : F[X][X] ↦ G.coeff j) hB0
    simpa [hBh, coeff_bivOf, hj] using this

end Stepanov
