import RischTragerBronstein.Jacobian.TorsionDecide
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Good primes exist

* `squarefreeCheck_complete`: the executable squarefreeness test succeeds on separable inputs;
* `exists_bezout_int`: a squarefree `f ∈ ℚ[x]` coming from `ℤ[x]` has `P f + Q f′ = d ≠ 0` over
  `ℤ`, so `f` stays squarefree modulo every prime not dividing `d`;
* `isSquare_of_modEq_one`: an integer `c` is a square modulo every prime `p ≡ 1 (mod 8|c|)`
  (quadratic reciprocity).
-/

open Polynomial CPoly CPoly.Kron

namespace Jac

theorem squarefreeCheck_complete {R : Type*} [Field R] [DecidableEq R] {s : CPoly R}
    (h : IsCoprime (toPoly s) (derivative (toPoly s))) : squarefreeCheck s = true := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨h1, h2⟩ := egcd_dvd s (deriv s)
  rw [toPoly_deriv] at h2
  have hG1 : toPoly (egcd s (deriv s)).1 ∣ 1 :=
    hab ▸ dvd_add (dvd_mul_of_dvd_right h1 a) (dvd_mul_of_dvd_right h2 b)
  have hG0 : toPoly (egcd s (deriv s)).1 ≠ 0 := fun h0 ↦ by
    rw [h0, zero_dvd_iff] at hG1; exact one_ne_zero hG1
  have hdeg := natDegree_eq_zero_of_isUnit (isUnit_of_dvd_one hG1)
  have hne : trim (egcd s (deriv s)).1 ≠ [] := fun h ↦ hG0 ((trim_eq_nil_iff _).mp h)
  rw [squarefreeCheck, beq_iff_eq, length_trim hne, hdeg]

/-- Clearing denominators in a Bézout identity for `f` and `f′`. -/
theorem exists_bezout_int {f : ℤ[X]} (hsq : Squarefree (f.map (Int.castRingHom ℚ))) :
    ∃ (P Q : ℤ[X]) (d : ℤ), d ≠ 0 ∧ P * f + Q * derivative f = C d := by
  have hsep : Separable (f.map (Int.castRingHom ℚ)) :=
    (PerfectField.separable_iff_squarefree).mpr hsq
  obtain ⟨a, b, hab⟩ := hsep
  obtain ⟨da, hda, ha⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) a
  obtain ⟨db, hdb, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors ℤ) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors ℤ) b
  have eA : A.map (Int.castRingHom ℚ) = C (da : ℚ) * a := by
    change A.map (algebraMap ℤ ℚ) = _
    rw [ha, ← smul_eq_C_mul]; exact (Int.cast_smul_eq_zsmul ℚ da a).symm
  have eB : B.map (Int.castRingHom ℚ) = C (db : ℚ) * b := by
    change B.map (algebraMap ℤ ℚ) = _
    rw [hb, ← smul_eq_C_mul]; exact (Int.cast_smul_eq_zsmul ℚ db b).symm
  have hda0 : da ≠ 0 := nonZeroDivisors.ne_zero hda
  have hdb0 : db ≠ 0 := nonZeroDivisors.ne_zero hdb
  refine ⟨C db * A, C da * B, da * db, mul_ne_zero hda0 hdb0, ?_⟩
  apply map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, eA, eB,
    derivative_map]
  rw [derivative_map] at hab
  simp only [eq_intCast, Int.cast_mul, C_mul]
  linear_combination (C (da : ℚ) * C (db : ℚ)) * hab

section QR

variable {p : ℕ} [hp : Fact p.Prime]

lemma isSquare_natCast_of_dvd {M : ℕ} (hM : M ≠ 0) (hpM : p ≡ 1 [MOD 8 * M]) :
    ∀ n, n ∣ M → IsSquare ((n : ℕ) : ZMod p) := by
  have hp8 : p % 8 = 1 := Nat.ModEq.of_mul_right M hpM
  have hp4 : p % 4 = 1 := by omega
  have hp2 : p ≠ 2 := by omega
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd (Nat.eq_zero_of_zero_dvd h) hM
  | one => intro _; exact ⟨1, by simp⟩
  | prime ℓ hℓ =>
    intro hℓM
    by_cases h2 : ℓ = 2
    · subst h2
      have := (ZMod.exists_sq_eq_two_iff hp2).mpr (Or.inl hp8)
      exact_mod_cast this
    · have : Fact ℓ.Prime := ⟨hℓ⟩
      rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hp4 h2]
      have h1 : ((p : ℕ) : ZMod ℓ) = 1 := by
        rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
        exact Nat.ModEq.of_dvd (dvd_trans hℓM (Dvd.intro_left 8 rfl)) hpM
      rw [h1]; exact ⟨1, by simp⟩
  | mul a b ha hb =>
    intro hab
    have := (ha (dvd_trans (dvd_mul_right a b) hab)).mul (hb (dvd_trans (dvd_mul_left b a) hab))
    rwa [← Nat.cast_mul] at this

/-- **`c` is a square modulo `p` when `p ≡ 1 (mod 8M)` and `|c| ∣ M`.** -/
lemma isSquare_intCast_of_dvd {M : ℕ} (hM : M ≠ 0) (hpM : p ≡ 1 [MOD 8 * M]) {c : ℤ}
    (hc : c.natAbs ∣ M) : IsSquare ((c : ℤ) : ZMod p) := by
  have h := isSquare_natCast_of_dvd hM hpM c.natAbs hc
  have hp4 : p % 4 = 1 := by have := Nat.ModEq.of_mul_right M hpM; unfold Nat.ModEq at this; omega
  rcases Int.natAbs_eq c with hc' | hc'
  · rw [hc', Int.cast_natCast]; exact h
  · rw [hc', Int.cast_neg, Int.cast_natCast, ← neg_one_mul]
    exact (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)).mul h

end QR

lemma not_dvd_of_natAbs_lt {p : ℕ} {n : ℤ} (hn : n ≠ 0) (h : n.natAbs < p) : ¬ (p : ℤ) ∣ n := by
  intro hd
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.natAbs_dvd_natAbs.mpr hd)
  simp at this; omega

/-- `g` distinct integers where `f` does not vanish, away from the abscissae of `Γ`. -/
lemma exists_E0_ints {f : List ℤ} (hf : toPoly f ≠ 0) (Γ : EDiv ℤ) (g : ℕ) :
    ∃ as : List ℤ, as.length = g ∧ as.Nodup ∧ ∀ a ∈ as, evalC f a ≠ 0 ∧ a ∉ Γ.map Prod.fst := by
  classical
  set S : Set ℤ := {a | evalC f a ≠ 0 ∧ a ∉ Γ.map Prod.fst}
  have hSc : Sᶜ.Finite := by
    have h1 : {a : ℤ | IsRoot (toPoly f) a}.Finite := Polynomial.finite_setOfPred_isRoot hf
    have h2 : {a : ℤ | a ∈ Γ.map Prod.fst}.Finite := (Γ.map Prod.fst).finite_toSet
    refine (h1.union h2).subset fun a ha ↦ ?_
    simp only [S, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_not, evalC_eq] at ha
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr ha
  have hS : S.Infinite := hSc.infinite_compl.mono (by simp)
  obtain ⟨t, hts, htc⟩ := hS.exists_subset_card_eq g
  exact ⟨t.toList, by rw [Finset.length_toList, htc], Finset.nodup_toList t,
    fun a ha ↦ hts (Finset.mem_toList.mp ha)⟩

/-- **Good primes exist**, arbitrarily large. -/
theorem exists_goodPrime {f : List ℤ} {g : ℕ} {Γ : EDiv ℤ} (hlen : f.length = 2 * g + 2)
    (hlc : f.getD (2 * g + 1) 0 ≠ 0) (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hΓ : ∀ q ∈ Γ, q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = evalC f q.1)
    (hΓd : Γ.Pairwise fun u v ↦ u.1 ≠ v.1) (N : ℕ) :
    ∃ p, ∃ hp : p.Prime, N < p ∧ ∃ xs ys, @goodPrime p ⟨hp⟩ f g Γ xs ys := by
  classical
  have hf0 : toPoly f ≠ 0 := by
    intro h; apply hlc
    have := congrArg (fun P ↦ P.coeff (2 * g + 1)) h
    simpa [coeff_toPoly] using this
  obtain ⟨as, hasl, hasnd, has⟩ := exists_E0_ints hf0 Γ g
  obtain ⟨P, Q, d, hd0, hPQ⟩ := exists_bezout_int hsq
  set M := (as.map fun a ↦ (evalC f a).natAbs).prod
  have hM : M ≠ 0 := by
    simp only [M, ne_eq, List.prod_eq_zero_iff, List.mem_map, not_exists, not_and]
    intro a ha h0; exact (has a ha).1 (Int.natAbs_eq_zero.mp h0)
  set TΓ := (Γ.map fun q ↦ q.1.natAbs + (2 * q.2.1).natAbs).sum
  set Ta := (as.map fun a ↦ a.natAbs + (evalC f a).natAbs).sum
  set S := N + 3 + (f.getD (2 * g + 1) 0).natAbs + d.natAbs + TΓ + Ta
  obtain ⟨p, hp, hpS, hpM⟩ := Nat.exists_prime_gt_modEq_one (2 * S) (by positivity : 8 * M ≠ 0)
  have : Fact p.Prime := ⟨hp⟩
  have key : ∀ n : ℤ, n ≠ 0 → n.natAbs ≤ 2 * S → ¬ (p : ℤ) ∣ n := fun n hn hle ↦
    not_dvd_of_natAbs_lt hn (by omega)
  have hqΓ : ∀ q ∈ Γ, q.1.natAbs + (2 * q.2.1).natAbs ≤ TΓ := fun q hq ↦
    List.le_sum_of_mem (List.mem_map_of_mem (f := fun q : ℤ × ℤ × ℕ ↦
      q.1.natAbs + (2 * q.2.1).natAbs) hq)
  have haa : ∀ a ∈ as, a.natAbs + (evalC f a).natAbs ≤ Ta := fun a ha ↦
    List.le_sum_of_mem (List.mem_map_of_mem (f := fun a ↦ a.natAbs + (evalC f a).natAbs) ha)
  have hsqr : ∀ a ∈ as, IsSquare ((evalC f a : ℤ) : ZMod p) := fun a ha ↦
    isSquare_intCast_of_dvd hM hpM (List.dvd_prod (List.mem_map_of_mem
      (f := fun a ↦ (evalC f a).natAbs) ha))
  have hy0 : ∀ a ∈ as, ∃ y : ℤ, (p : ℤ) ∣ y ^ 2 - evalC f a ∧ ¬ (p : ℤ) ∣ y := by
    intro a ha
    obtain ⟨r, hr⟩ := hsqr a ha
    have e : (((r.val : ℕ) : ℤ) : ZMod p) = r := by simp
    have hcn : ¬ (p : ℤ) ∣ evalC f a := key _ (has a ha).1 (by have := haa a ha; omega)
    refine ⟨(r.val : ℤ), ?_, ?_⟩
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
      rw [show ((r.val : ℕ) : ZMod p) = r by simp, hr]; ring
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, e]; intro h0; apply hcn
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hr, h0, zero_mul]
  let yOf : ℤ → ℤ := fun a ↦
    if h : ∃ y : ℤ, (p : ℤ) ∣ y ^ 2 - evalC f a ∧ ¬ (p : ℤ) ∣ y then h.choose else 0
  have hy : ∀ a ∈ as, (p : ℤ) ∣ yOf a ^ 2 - evalC f a ∧ ¬ (p : ℤ) ∣ yOf a := by
    intro a ha
    simp only [yOf, dif_pos (hy0 a ha)]
    exact (hy0 a ha).choose_spec
  refine ⟨p, hp, by omega, as, as.map yOf, ⟨by omega, hlen, ?_, hasl,
    by simp [hasl], ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact key _ hlc (by omega)
  · intro i hi
    have hi' : i < as.length := by rw [hasl]; exact List.mem_range.mp hi
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi',
      List.getElem_map]
    exact hy _ (List.getElem_mem hi')
  · refine hasnd.imp_of_mem fun {u v} hu hv huv ↦ key _ (sub_ne_zero.mpr huv) ?_
    have := Int.natAbs_sub_le u v
    have := haa u hu; have := haa v hv
    omega
  · intro q hq
    refine ⟨key _ (mul_ne_zero two_ne_zero (hΓ q hq).1) (by have := hqΓ q hq; omega),
      (hΓ q hq).2, fun x hx ↦ key _ (sub_ne_zero.mpr ?_) ?_⟩
    · rintro rfl; exact (has _ hx).2 (List.mem_map_of_mem hq)
    · have := Int.natAbs_sub_le q.1 x
      have := hqΓ q hq; have := haa x hx
      omega
  · refine hΓd.imp_of_mem fun {u v} hu hv huv ↦ key _ (sub_ne_zero.mpr huv) ?_
    have := Int.natAbs_sub_le u.1 v.1
    have := hqΓ u hu; have := hqΓ v hv
    omega
  · apply squarefreeCheck_complete
    rw [castL_eq, derivative_map]
    set φ := Int.castRingHom (ZMod p)
    have hmap := congrArg (Polynomial.map φ) hPQ
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hmap
    have hd : φ d ≠ 0 := by
      rw [eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact key _ hd0 (by omega)
    refine ⟨C (φ d)⁻¹ * P.map φ, C (φ d)⁻¹ * Q.map φ, ?_⟩
    have : C (φ d)⁻¹ * C (φ d) = (1 : (ZMod p)[X]) := by rw [← C_mul, inv_mul_cancel₀ hd, C_1]
    linear_combination C (φ d)⁻¹ * hmap + this

end Jac
