import RischTragerBronstein.Jacobian.CertCheck
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A genus-two integral with a logarithmic part, proved non-elementary

On `C : y² = x⁵ − 2x² − 3x + 1` (genus 2) the integrand `1 / (x y)` has residues `±1` at
`P = (0, 1)` and `σP = (0, −1)`. By Abel's direction (`hyp_principal_of_elementary`), if
`∫ dx / (x √(x⁵ − 2x² − 3x + 1))` were elementary, the divisor `[P] − [σP]` would be torsion in
the Jacobian. Modulo `7` its order is exactly `7`, modulo `11` exactly `13` (certificates checked
by the kernel over `𝔽₇`, `𝔽₁₁`); since `7 · 7ᶜ ≠ 13 · 11ᵈ`, the divisor is not torsion
(`not_torsion_of_orders`, built on the kernel-of-reduction theorem `kernel_no_torsion`).

`genus2_not_elementary`: `∫ dx / (x √(x⁵ − 2x² − 3x + 1))` is **not elementary**.
-/

open Polynomial CPoly

namespace Jac.Genus2Example


instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- `x⁵ − 2x² − 3x + 1` modulo `p`. -/
def fC (p : ℕ) : CPoly (ZMod p) := [1, -3, -2, 0, 0, 1]

/-- `7 ([P] − [σP])` is principal modulo `7`. -/
lemma cert7 : principalCert (fC 7) 2 [(0, 1, 14)] [1, 6, 0, 0, 5, 1, 2, 4] [6, 3, 5, 5, 4]
    [[1, 2, 4, 6, 1, 6, 1, 3, 6, 6, 4, 0, 4, 0]] = true := by
  decide +kernel

/-- `13 ([P] − [σP])` is principal modulo `11`. -/
lemma cert11 : principalCert (fC 11) 2 [(0, 1, 26)] [1, 4, 3, 7, 0, 9, 9, 7, 3, 4, 5, 0, 10, 4]
    [10, 0, 10, 0, 10, 10, 8, 6, 5, 10, 5]
    [[1, 4, 2, 3, 8, 1, 3, 6, 1, 0, 5, 3, 9, 1, 7, 7, 2, 0, 0, 3, 10, 5, 6, 4, 8, 5]] = true := by
  decide +kernel

lemma toPoly_listMap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (l : List R) :
    CPoly.toPoly (l.map φ) = (CPoly.toPoly l).map φ := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The coefficient list of `x⁵ − 2x² − 3x + 1`. -/
def fL (R : Type*) [Ring R] : List R := [1, -3, -2, 0, 0, 1]

lemma fL_map {R S : Type*} [Ring R] [Ring S] (φ : R →+* S) : (fL R).map φ = fL S := by
  simp [fL]; exact ⟨map_ofNat φ 3, map_ofNat φ 2⟩

lemma toPoly_fL (R : Type*) [CommRing R] :
    CPoly.toPoly (fL R) = X ^ 5 + C (-2) * X ^ 2 + C (-3) * X + C 1 := by
  simp only [fL, CPoly.toPoly_cons, CPoly.toPoly_nil, map_one, map_neg, map_zero, mul_zero,
    add_zero, zero_add]
  rw [show (C (3 : R)) = 3 from map_ofNat C 3, show (C (2 : R)) = 2 from map_ofNat C 2]
  ring

lemma natDegree_fL (R : Type*) [CommRing R] [Nontrivial R] :
    (CPoly.toPoly (fL R)).natDegree = 2 * 2 + 1 := by
  rw [toPoly_fL]; compute_degree!

lemma leadingCoeff_fL (R : Type*) [CommRing R] [Nontrivial R] :
    (CPoly.toPoly (fL R)).leadingCoeff = 1 := by
  rw [leadingCoeff, natDegree_fL, toPoly_fL]
  simp [coeff_X_pow, coeff_one]

lemma eval_fL {R : Type*} [CommRing R] (t : R) :
    (CPoly.toPoly (fL R)).eval t = t ^ 5 - 2 * t ^ 2 - 3 * t + 1 := by
  simp [fL, CPoly.toPoly]; ring

section Local

variable (p : ℕ) [hp : Fact p.Prime]

/-- The local data at `p`: the curve, the divisor `2P`, and the transport of a certificate. -/
lemma residue_principal {m : ℕ} (hcert : ∃ ψ : (ZMod p)[X] × (ZMod p)[X], ψ ≠ (0, 0) ∧
      PoleLE 2 ψ (m * 2) ∧ Vanishes (CPoly.toPoly (fL (ZMod p))) ψ [(0, 1, m * 2)]) :
    PrincipalMul ((CPoly.toPoly (fL ℤ_[p])).map (IsLocalRing.residue ℤ_[p])) 2
      (emap (IsLocalRing.residue ℤ_[p]) [((0 : ℤ_[p]), (1 : ℤ_[p]), 2)]) m := by
  apply principal_residue_of_zmod
  rw [← toPoly_listMap, fL_map,
    show emap (PadicInt.toZMod (p := p)) [((0 : ℤ_[p]), (1 : ℤ_[p]), 2)] = [(0, 1, 2)] by
      simp [emap]]
  obtain ⟨ψ, h0, hp', hv⟩ := hcert
  refine ⟨ψ, h0, by simpa [edeg] using hp', ?_⟩
  simpa [escale] using hv

lemma residue_not_principal_one (hp2 : p ≠ 2) :
    ¬ PrincipalMul ((CPoly.toPoly (fL ℤ_[p])).map (IsLocalRing.residue ℤ_[p])) 2
      (emap (IsLocalRing.residue ℤ_[p]) [((0 : ℤ_[p]), (1 : ℤ_[p]), 2)]) 1 := by
  have h2 : IsUnit (2 : ℤ_[p]) := isUnit_intCast (k := 2) (by
    intro h
    have := Int.le_of_dvd (by norm_num) h
    have hp3 : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
    omega)
  simp only [emap, List.map_cons, List.map_nil, map_zero, map_one]
  refine not_principal_double (by norm_num) ?_
  rw [mul_one]
  have := h2.map (IsLocalRing.residue ℤ_[p]); rwa [map_ofNat] at this

end Local

/-- **`[P] − [σP]` is not torsion in the Jacobian of `y² = x⁵ − 2x² − 3x + 1`.** -/
theorem not_torsion :
    ∀ n, 1 ≤ n → ¬ PrincipalMul (CPoly.toPoly (fL ℚ)) 2 [((0 : ℚ), (1 : ℚ), 2)] n := by
  -- the square roots in `ℤ₇` and `ℤ₁₁`
  have h7 : (7 : ℕ) ≠ 2 := by norm_num
  have h11 : (11 : ℕ) ≠ 2 := by norm_num
  obtain ⟨y7, hy7, hy7u, -⟩ := exists_sqrt (p := 7) h7 (-3) 2
    (isUnit_intCast (k := 2) (by decide)) (by
      rw [show (2 : ℤ_[7]) ^ 2 - -3 = ((7 : ℤ) : ℤ_[7]) by push_cast; ring]
      exact (PadicInt.norm_int_lt_one_iff_dvd 7).mpr (by decide))
  obtain ⟨y11, hy11, hy11u, -⟩ := exists_sqrt (p := 11) h11 3061 5
    (isUnit_intCast (k := 5) (by decide)) (by
      rw [show (5 : ℤ_[11]) ^ 2 - 3061 = ((-3036 : ℤ) : ℤ_[11]) by push_cast; ring]
      exact (PadicInt.norm_int_lt_one_iff_dvd (-3036)).mpr (by decide))
  have hfQ : (CPoly.toPoly (fL ℚ)).natDegree = 2 * 2 + 1 := natDegree_fL ℚ
  -- common facts
  have hmapf : ∀ (q : ℕ) [Fact q.Prime], (CPoly.toPoly (fL ℚ)).map (algebraMap ℚ ℚ_[q]) =
      (CPoly.toPoly (fL ℤ_[q])).map (algebraMap ℤ_[q] ℚ_[q]) := by
    intro q _
    rw [← toPoly_listMap, ← toPoly_listMap, fL_map, fL_map]
  have hmapΓ : ∀ (q : ℕ) [Fact q.Prime], emap (algebraMap ℚ ℚ_[q]) [((0 : ℚ), (1 : ℚ), 2)] =
      emap (algebraMap ℤ_[q] ℚ_[q]) [((0 : ℤ_[q]), (1 : ℤ_[q]), 2)] := by
    intro q _; simp [emap]
  have hon : ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 →
      OnCurve (CPoly.toPoly (fL ℤ_[q])) [((0 : ℤ_[q]), (1 : ℤ_[q]), 2)] := by
    intro q hq hq2 r hr
    rw [List.mem_singleton] at hr; subst hr
    refine ⟨?_, by rw [eval_fL]; norm_num⟩
    rw [mul_one]
    exact isUnit_intCast (k := 2) fun h ↦ by
      have := Int.le_of_dvd (by norm_num) h
      have := hq.out.two_le
      omega
  -- the data at `7`
  have hx7 : ∀ i j : Fin 2, i ≠ j →
      IsUnit ((![-1, 1] : Fin 2 → ℤ_[7]) i - (![-1, 1] : Fin 2 → ℤ_[7]) j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
        Matrix.cons_val_one]
      rw [show (-1 : ℤ_[7]) - 1 = ((-2 : ℤ) : ℤ_[7]) by push_cast; ring]
      exact isUnit_intCast (by decide)
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
        Matrix.cons_val_one]
      rw [show (1 : ℤ_[7]) - -1 = ((2 : ℤ) : ℤ_[7]) by push_cast; ring]
      exact isUnit_intCast (by decide)
    · exact absurd rfl hij
  have hy7f : ∀ i : Fin 2, (![1, y7] : Fin 2 → ℤ_[7]) i ^ 2 =
      (CPoly.toPoly (fL ℤ_[7])).eval ((![-1, 1] : Fin 2 → ℤ_[7]) i) := by
    intro i; fin_cases i
    · simp [eval_fL]; ring
    · simp [eval_fL, hy7]; ring
  have hy7u' : ∀ i : Fin 2, IsUnit ((![1, y7] : Fin 2 → ℤ_[7]) i) := by
    intro i; fin_cases i
    · simp
    · simpa using hy7u
  have hE7 : ∀ r ∈ [((0 : ℤ_[7]), (1 : ℤ_[7]), 2)], ∀ i : Fin 2,
      IsUnit (r.1 - (![-1, 1] : Fin 2 → ℤ_[7]) i) := by
    intro r hr i
    rw [List.mem_singleton] at hr; subst hr
    fin_cases i
    · simp
    · simp
  -- the data at `11`
  have hx11 : ∀ i j : Fin 2, i ≠ j →
      IsUnit ((![-1, 5] : Fin 2 → ℤ_[11]) i - (![-1, 5] : Fin 2 → ℤ_[11]) j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · have := isUnit_intCast (p := 11) (k := -6) (by decide); push_cast at this ⊢
      convert this using 1; norm_num
    · have := isUnit_intCast (p := 11) (k := 6) (by decide); push_cast at this ⊢
      convert this using 1; norm_num
    · exact absurd rfl hij
  have hy11f : ∀ i : Fin 2, (![1, y11] : Fin 2 → ℤ_[11]) i ^ 2 =
      (CPoly.toPoly (fL ℤ_[11])).eval ((![-1, 5] : Fin 2 → ℤ_[11]) i) := by
    intro i; fin_cases i
    · simp [eval_fL]; ring
    · simp [eval_fL, hy11]; norm_num
  have hy11u' : ∀ i : Fin 2, IsUnit ((![1, y11] : Fin 2 → ℤ_[11]) i) := by
    intro i; fin_cases i
    · simp
    · simpa using hy11u
  have hE11 : ∀ r ∈ [((0 : ℤ_[11]), (1 : ℤ_[11]), 2)], ∀ i : Fin 2,
      IsUnit (r.1 - (![-1, 5] : Fin 2 → ℤ_[11]) i) := by
    intro r hr i
    rw [List.mem_singleton] at hr; subst hr
    fin_cases i
    · simp
    · have := isUnit_intCast (p := 11) (k := -5) (by decide); push_cast at this ⊢
      convert this using 1; norm_num
  -- the certificates
  have hres7 := residue_principal 7 (m := 7) (by
    obtain ⟨ψ, h0, hp, hv⟩ := principalCert_sound cert7
    exact ⟨ψ, h0, by simpa [edeg] using hp, by simpa [fC, fL] using hv⟩)
  have hres11 := residue_principal 11 (m := 13) (by
    obtain ⟨ψ, h0, hp, hv⟩ := principalCert_sound cert11
    exact ⟨ψ, h0, by simpa [edeg] using hp, by simpa [fC, fL] using hv⟩)
  have hdegk : ∀ (q : ℕ) [Fact q.Prime], ((CPoly.toPoly (fL ℤ_[q])).map
      (IsLocalRing.residue ℤ_[q])).natDegree = 2 * 2 + 1 := by
    intro q _
    have hlc : (IsLocalRing.residue ℤ_[q]) (CPoly.toPoly (fL ℤ_[q])).leadingCoeff ≠ 0 := by
      rw [leadingCoeff_fL, map_one]; exact one_ne_zero
    rw [natDegree_map_of_leadingCoeff_ne_zero _ hlc, natDegree_fL]
  have hmin7 := exact_order (hdegk 7) (OnCurve.map (hon 7 h7)) (by simp [emap]) hres7
    (fun r hr hrd ↦ by
      rw [(Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hrd, Nat.div_self (by norm_num)]
      exact residue_not_principal_one 7 h7)
  have hmin11 := exact_order (hdegk 11) (OnCurve.map (hon 11 h11)) (by simp [emap]) hres11
    (fun r hr hrd ↦ by
      rw [(Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hrd, Nat.div_self (by norm_num)]
      exact residue_not_principal_one 11 h11)
  have hΓK : ∀ r ∈ [((0 : ℚ), (1 : ℚ), 2)], 2 * r.2.1 ≠ 0 ∧
      r.2.1 ^ 2 = (CPoly.toPoly (fL ℚ)).eval r.1 := by
    intro r hr
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨by norm_num, by rw [eval_fL]; norm_num⟩
  exact not_torsion_of_orders (p := 7) (q := 11) h7 h11 (algebraMap ℚ ℚ_[7])
    (algebraMap ℚ ℚ_[11]) (CPoly.toPoly (fL ℚ)) hfQ [((0 : ℚ), (1 : ℚ), 2)] hΓK (by simp)
    (CPoly.toPoly (fL ℤ_[7])) (natDegree_fL _) (by rw [leadingCoeff_fL]; exact isUnit_one)
    (hmapf 7) ![-1, 1] ![1, y7] hy7u' hy7f hx7
    [((0 : ℤ_[7]), (1 : ℤ_[7]), 2)] (hmapΓ 7) (hon 7 h7) (List.pairwise_singleton _ _) hE7
    7 (by norm_num) hres7 hmin7
    (CPoly.toPoly (fL ℤ_[11])) (natDegree_fL _) (by rw [leadingCoeff_fL]; exact isUnit_one)
    (hmapf 11) ![-1, 5] ![1, y11] hy11u' hy11f hx11
    [((0 : ℤ_[11]), (1 : ℤ_[11]), 2)] (hmapΓ 11) (hon 11 h11) (List.pairwise_singleton _ _)
    hE11 13 (by norm_num) hres11 hmin11
    (ne_of_prime_pow_right (r := 13) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))

section Final

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ dx / (x √(x⁵ − 2x² − 3x + 1))` is not elementary** (genus two). -/
theorem genus2_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 5 - 2 * x ^ 2 - 3 * x + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    ¬ HasElementaryIntegral (1 / (x * y)) := by
  intro h
  have hsq : Squarefree (CPoly.toPoly (fL ℚ)) :=
    CPoly.squarefreeCheck_sound (by decide +kernel)
  have hy' : y ^ 2 = aeval x (CPoly.toPoly (fL ℚ)) := by
    rw [toPoly_fL, hy]; simp; ring
  obtain ⟨Λ, hΛ1⟩ := Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : Kc) ≠ 0)
  have h' : HasElementaryIntegral ((aeval x (0 : Kc[X]) + ∑ i ∈ (Finset.univ : Finset Unit),
      algebraMap Kc E ((fun _ ↦ (1 : Kc)) i * algebraMap ℚ Kc ((fun _ ↦ (1 : ℚ)) i)) /
        (x - algebraMap Kc E (algebraMap ℚ Kc ((fun _ ↦ (0 : ℚ)) i)))) / y) := by
    convert h using 1
    simp only [map_zero, Finset.univ_unique, Finset.sum_singleton, map_one, mul_one, sub_zero,
      zero_add, one_div, mul_inv_rev]
    rw [div_eq_mul_inv, mul_comm]
  obtain ⟨n, hn1, hn⟩ := hyp_principal_of_elementary hC hCall x y hx (g := 2)
    (CPoly.toPoly (fL ℚ)) hsq (natDegree_fL ℚ) hy' hgen (algebraMap ℚ Kc)
    (Finset.univ : Finset Unit) (fun _ ↦ 0) (fun _ ↦ 1) (fun _ _ ↦ one_ne_zero)
    (fun _ _ ↦ by simp [eval_fL]) (fun _ _ _ _ _ ↦ Subsingleton.elim _ _) 0 (fun _ ↦ 1) h' Λ
    (fun _ ↦ 1) 1 one_ne_zero (fun _ _ ↦ by simp [hΛ1])
  have hmapid : (CPoly.toPoly (fL ℚ)).map (algebraMap ℚ ℚ) = CPoly.toPoly (fL ℚ) := by
    rw [Algebra.algebraMap_self, Polynomial.map_id]
  have hres : resDiv (Finset.univ : Finset Unit) (fun _ ↦ (0 : ℚ)) (fun _ ↦ 1) (fun _ ↦ 1) =
      [((0 : ℚ), (1 : ℚ), 2)] := by
    simp [resDiv, Finset.univ_unique]
  rw [hmapid, hres] at hn
  exact not_torsion n hn1 hn

end Final

end Jac.Genus2Example
