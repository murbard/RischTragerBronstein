import RischTragerBronstein.Jacobian.Jets
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# No prime-to-`p` torsion in the kernel of reduction (hyperelliptic Jacobians)

Let `O` be a discrete valuation ring with uniformiser `ϖ` and `2 ∈ Oˣ`, and `y² = f(x)` a curve
over `O`. Fix `g` points `Pᵢ = (xᵢ, yᵢ)` with the `xᵢ` pairwise distinct modulo `ϖ` and the `yᵢ`
units (a non-special divisor `E₀`, also after reduction), and points `Qᵢ = (xᵢ + tᵢ, Yᵢ)` reducing
to `Pᵢ`. With `ℓ = m + 1` a unit, a function `a + b y` with `deg a ≤ gℓ`, `deg b < gℓ − g`
vanishing to order `ℓ` at every `Qᵢ` and every `σPᵢ = (xᵢ, −yᵢ)` is a witness that the divisor
`ℓ (∑ Qᵢ − ∑ Pᵢ)` is principal. `kernel_no_torsion`: then every `tᵢ = 0`, i.e. the class
`∑ Qᵢ − ∑ Pᵢ` of the kernel of reduction is not a non-trivial `ℓ`-torsion point.

The proof is elementary: modulo `ϖ` the function is `c ūˡ` (`u = ∏ (x − xᵢ)`); peeling off
`ϖ`-adic layers up to the level `n` of `t`, the next layer satisfies the tangent equation over the
residue field, whose only solution is `t ≡ 0 (mod ϖⁿ⁺¹)` (`tangent_jet`, since `ℓ` is a unit).
-/

open Polynomial

namespace Jac

section Taylor

variable {R : Type*} [CommRing R]

lemma X_add_C_pow (t : R) (m : ℕ) : ∃ E : R[X],
    (X + C t) ^ (m + 1) = X ^ (m + 1) + C ((m + 1 : R) * t) * X ^ m + C (t ^ 2) * E := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨E, hE⟩ := ih
    refine ⟨C ((m + 1 : R)) * X ^ m + (X + C t) * E, ?_⟩
    rw [pow_succ, hE]
    simp only [map_mul, map_add, map_natCast, map_one, map_pow]
    push_cast
    ring

/-- **The jet of `uˡ` at a moved point.** -/
lemma u_pow_comp {g : ℕ} (x : Fin g → R) (i : Fin g) (t : R) (m : ℕ) :
    ∃ R₁ R₂ : R[X], ((∏ j, (X - C (x j))) ^ (m + 1)).comp (X + C (x i + t)) =
      X ^ (m + 1) * R₁ +
        C ((m + 1 : R) * t * (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1)) * X ^ m +
        C (t ^ 2) * R₂ := by
  classical
  set G : R[X] := ∏ j ∈ Finset.univ.erase i, (X + C (x i + t - x j))
  have hcomp : (∏ j, (X - C (x j))).comp (X + C (x i + t)) = (X + C t) * G := by
    rw [prod_comp, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [sub_comp, X_comp, C_comp, G]
    congr 1
    · rw [add_sub_assoc, ← C_sub, add_sub_cancel_left]
    · refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [add_sub_assoc, ← C_sub]
  obtain ⟨E, hE⟩ := X_add_C_pow t m
  obtain ⟨H, hH⟩ := X_dvd_sub_C (p := G ^ (m + 1))
  set c : R := ∏ j ∈ Finset.univ.erase i, (x i - x j)
  -- the constant term of `Gˡ` is `cˡ + t r`
  have hG0 : ∃ r, (G ^ (m + 1)).coeff 0 = c ^ (m + 1) + t * r := by
    set Q : R[X] := (∏ j ∈ Finset.univ.erase i, (C (x i - x j) + X)) ^ (m + 1)
    obtain ⟨r, hr⟩ := sub_dvd_eval_sub t 0 Q
    refine ⟨r, ?_⟩
    have h1 : (G ^ (m + 1)).coeff 0 = Q.eval t := by
      rw [coeff_zero_eq_eval_zero]
      simp only [G, Q, eval_pow, eval_prod, eval_add, eval_X, eval_C, zero_add]
      congr 1
      exact Finset.prod_congr rfl fun j _ ↦ by ring
    have h2 : Q.eval 0 = c ^ (m + 1) := by
      simp only [Q, c, eval_pow, eval_prod, eval_add, eval_C, eval_X, add_zero]
    rw [h1, ← h2]; rw [sub_zero] at hr; linear_combination hr
  obtain ⟨r, hr⟩ := hG0
  refine ⟨C (c ^ (m + 1) + t * r) + X * H + C ((m + 1 : R) * t) * H,
    C ((m + 1 : R) * r) * X ^ m + E * (C (c ^ (m + 1) + t * r) + X * H), ?_⟩
  rw [pow_comp, hcomp, mul_pow, hE]
  have hG : G ^ (m + 1) = C (c ^ (m + 1) + t * r) + X * H := by
    rw [← hr]; linear_combination hH
  rw [hG]
  simp only [map_mul, map_add, map_pow, map_natCast, map_one]
  ring

end Taylor

section Field

variable {k : Type*} [Field k]

lemma prod_pow_dvd {g : ℕ} {x : Fin g → k} (hx : Function.Injective x) (e : ℕ) {P : k[X]}
    (h : ∀ i, (X - C (x i)) ^ e ∣ P) : (∏ i, (X - C (x i))) ^ e ∣ P := by
  rw [← Finset.prod_pow]
  exact Finset.prod_dvd_of_coprime
    (fun i _ j _ hij ↦ ((pairwise_coprime_X_sub_C hx) hij).pow) fun i _ ↦ h i

lemma natDegree_prod_pow {g : ℕ} (x : Fin g → k) (e : ℕ) :
    ((∏ i, (X - C (x i))) ^ e).natDegree = g * e := by
  rw [(monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)).natDegree_pow,
    natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)]
  simp [mul_comm]

lemma eq_zero_of_prod_pow_dvd {g : ℕ} {x : Fin g → k} (hx : Function.Injective x) {e : ℕ}
    {P : k[X]} (h : ∀ i, (X - C (x i)) ^ e ∣ P) (hP : P.degree < (g * e : ℕ)) : P = 0 := by
  by_contra h0
  have := natDegree_le_of_dvd (prod_pow_dvd hx e h) h0
  rw [natDegree_prod_pow] at this
  rw [degree_eq_natDegree h0] at hP
  exact absurd hP (not_lt.mpr (by exact_mod_cast this))

/-- Over the residue field: vanishing to order `ℓ` at all `Pᵢ` and `σPᵢ` forces `b = 0`,
`a = c uˡ`. -/
lemma structure_mod {f α β : k[X]} {g m : ℕ} {x y : Fin g → k} (hx : Function.Injective x)
    (h2y : ∀ i, IsUnit (2 * y i)) (hα : α.natDegree ≤ g * (m + 1)) (hβ : β.degree < (g * m : ℕ))
    (h₁ : ∀ i, VanishAt f α β (x i) (y i) (m + 1)) (h₂ : ∀ i, VanishAt f α β (x i) (-y i) (m + 1)) :
    β = 0 ∧ ∃ c, α = C c * (∏ i, (X - C (x i))) ^ (m + 1) := by
  have hd := fun i ↦ dvd_of_vanish_both (h2y i) (h₁ i) (h₂ i)
  have hβ0 : β = 0 := eq_zero_of_prod_pow_dvd hx (fun i ↦ (hd i).2)
    (hβ.trans_le (by exact_mod_cast Nat.mul_le_mul_left g (Nat.le_succ m)))
  refine ⟨hβ0, ?_⟩
  obtain ⟨q, hq⟩ := prod_pow_dvd hx (m + 1) fun i ↦ (hd i).1
  by_cases hq0 : q = 0
  · exact ⟨0, by rw [hq, hq0]; simp⟩
  have hU0 : (∏ i, (X - C (x i))) ^ (m + 1) ≠ 0 :=
    ((monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)).pow _).ne_zero
  have hdeg : q.natDegree = 0 := by
    have := congrArg natDegree hq
    rw [natDegree_mul hU0 hq0, natDegree_prod_pow] at this
    omega
  refine ⟨q.coeff 0, ?_⟩
  rw [hq, mul_comm]; congr 1; exact eq_C_of_natDegree_eq_zero hdeg

end Field

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

lemma res_eq_zero_iff {ϖ : O} (hϖ : Irreducible ϖ) (z : O) :
    IsLocalRing.residue O z = 0 ↔ ϖ ∣ z := by
  rw [IsLocalRing.residue_eq_zero_iff,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton]

lemma C_dvd_iff_map {ϖ : O} (hϖ : Irreducible ϖ) (P : O[X]) :
    C ϖ ∣ P ↔ P.map (IsLocalRing.residue O) = 0 := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h; ext n; rw [coeff_map, coeff_zero, res_eq_zero_iff hϖ]; exact h n
  · intro h n; rw [← res_eq_zero_iff hϖ, ← coeff_map, h, coeff_zero]

/-- **The kernel of reduction has no `ℓ`-torsion for `ℓ` prime to the residue characteristic.** -/
theorem kernel_no_torsion {ϖ : O} (hϖ : Irreducible ϖ) (h2 : IsUnit (2 : O)) (f : O[X])
    {g m : ℕ} (hℓ : IsUnit ((m + 1 : ℕ) : O))
    (x y t Y : Fin g → O) (hyu : ∀ i, IsUnit (y i)) (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (ht : ∀ i, ϖ ∣ t i) (hYy : ∀ i, ϖ ∣ Y i - y i)
    (a b : O[X]) (hab : ¬ (C ϖ ∣ a ∧ C ϖ ∣ b))
    (ha : a.natDegree ≤ g * (m + 1)) (hb : b.degree < (g * m : ℕ))
    (hQ : ∀ i, VanishAt f a b (x i + t i) (Y i) (m + 1))
    (hS : ∀ i, VanishAt f a b (x i) (-y i) (m + 1)) :
    ∀ i, t i = 0 := by
  classical
  set ρ := IsLocalRing.residue O
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  by_contra hne
  push_neg at hne
  obtain ⟨j0, hj0⟩ := hne
  -- the level `n` of `t`
  have hex : ∃ n, ¬ ∀ i, ϖ ^ (n + 1) ∣ t i := by
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hj0 hϖ
    refine ⟨n, fun h ↦ ?_⟩
    have h1 := h j0
    rw [hv, pow_succ, mul_comm (ϖ ^ n)] at h1
    have h3 : ϖ ∣ (v : O) := (mul_dvd_mul_iff_right (pow_ne_zero n hϖ0)).mp h1
    exact hϖ.not_isUnit (isUnit_of_dvd_unit h3 v.isUnit)
  set n := Nat.find hex with hndef
  have hn1 : ¬ ∀ i, ϖ ^ (n + 1) ∣ t i := Nat.find_spec hex
  have hn : ∀ i, ϖ ^ n ∣ t i := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · intro i; rw [h0, pow_zero]; exact one_dvd _
    · have := Nat.find_min hex (show n - 1 < n by omega)
      push_neg at this
      rwa [Nat.sub_add_cancel hpos] at this
  have hn0 : 1 ≤ n := by
    by_contra h0
    push_neg at h0
    apply hn1
    rw [Nat.lt_one_iff.mp h0, zero_add, pow_one]; exact ht
  choose τ hτ using hn
  -- data over the residue field
  set u : O[X] := ∏ j, (X - C (x j))
  have hmap_u : u.map ρ = ∏ j, (X - C (ρ (x j))) := by
    simp [u, Polynomial.map_prod]
  have hxk : Function.Injective fun i ↦ ρ (x i) := by
    intro i j hij
    by_contra hne
    have := (hx i j hne).map ρ
    rw [map_sub, show ρ (x i) = ρ (x j) from hij, sub_self] at this
    exact not_isUnit_zero this
  have h2k : IsUnit (2 : IsLocalRing.ResidueField O) := by
    have := h2.map ρ; rwa [map_ofNat] at this
  have h2y : ∀ i, IsUnit (2 * ρ (y i)) := fun i ↦ h2k.mul ((hyu i).map ρ)
  have hρt : ∀ i, ρ (t i) = 0 := fun i ↦ (res_eq_zero_iff hϖ _).mpr (ht i)
  have hρY : ∀ i, ρ (Y i) = ρ (y i) := fun i ↦ by
    rw [← sub_eq_zero, ← map_sub]; exact (res_eq_zero_iff hϖ _).mpr (hYy i)
  have hU : ∀ i, ∃ R₁ R₂ : O[X], (u ^ (m + 1)).comp (X + C (x i + t i)) = X ^ (m + 1) * R₁ +
      C ((m + 1 : O) * t i * (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1)) * X ^ m +
      C (t i ^ 2) * R₂ := fun i ↦ u_pow_comp x i (t i) m
  have hU0 : ∀ i, X ^ (m + 1) ∣ (u ^ (m + 1)).comp (X + C (x i)) := fun i ↦ by
    obtain ⟨R₁, R₂, h⟩ := u_pow_comp x i 0 m
    rw [add_zero] at h
    rw [h]; simp
  -- the jets of `C c * uˡ + C (ϖ^r) * α` split
  have hsplit : ∀ (c : O) (α β : O[X]) (r : ℕ) (z : O) (V : O[X]),
      jet (C c * u ^ (m + 1) + C (ϖ ^ r) * α) (C (ϖ ^ r) * β) z V =
        C c * (u ^ (m + 1)).comp (X + C z) + C (ϖ ^ r) * jet α β z V := by
    intro c α β r z V
    simp only [jet, add_comp, mul_comp, C_comp]; ring
  have hdegU : (u ^ (m + 1)).natDegree = g * (m + 1) := by
    rw [(monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)).natDegree_pow,
      natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)]
    simp [mul_comm]
  -- peeling off the layers
  have layers : ∀ r ≤ n, ∃ (c : O) (α β : O[X]), a = C c * u ^ (m + 1) + C (ϖ ^ r) * α ∧
      b = C (ϖ ^ r) * β ∧ α.natDegree ≤ g * (m + 1) ∧ β.degree < (g * m : ℕ) := by
    intro r
    induction r with
    | zero => intro _; exact ⟨0, a, b, by simp, by simp, ha, hb⟩
    | succ r ih =>
      intro hr
      obtain ⟨c, α, β, hae, hbe, hαd, hβd⟩ := ih (by omega)
      -- the reduced layer vanishes at all `Pᵢ` and `σPᵢ`
      have hvQ : ∀ i, VanishAt (f.map ρ) (α.map ρ) (β.map ρ) (ρ (x i)) (ρ (y i)) (m + 1) := by
        intro i
        obtain ⟨V, hV, hj⟩ := hQ i
        obtain ⟨R₁, R₂, hUi⟩ := hU i
        rw [hae, hbe, hsplit, hUi, hτ i] at hj
        have e : C c * (X ^ (m + 1) * R₁ + C ((m + 1 : O) * (ϖ ^ n * τ i) *
            (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1)) * X ^ m +
            C ((ϖ ^ n * τ i) ^ 2) * R₂) + C (ϖ ^ r) * jet α β (x i + ϖ ^ n * τ i) V =
            X ^ (m + 1) * (C c * R₁) + C (ϖ ^ r) * (jet α β (x i + ϖ ^ n * τ i) V +
              C (ϖ ^ (n - r)) * (C (c * ((m + 1 : O) * τ i *
                (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1))) * X ^ m +
                C (c * ϖ ^ n * τ i ^ 2) * R₂)) := by
          have hpow : (ϖ : O) ^ n = ϖ ^ r * ϖ ^ (n - r) := by
            rw [← pow_add]; congr 1; omega
          rw [hpow]; simp only [map_mul, map_pow, map_add]; ring
        rw [e] at hj
        have hj2 := X_pow_dvd_of_C_mul (pow_ne_zero r hϖ0)
          ((dvd_add_right (dvd_mul_right _ _)).mp hj)
        have hj3 := Polynomial.map_dvd ρ hj2
        have hz : ρ (ϖ ^ (n - r)) = 0 := by
          rw [res_eq_zero_iff hϖ]; exact dvd_pow_self ϖ (by omega)
        simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hz, map_zero, zero_mul,
          add_zero, Polynomial.map_pow, Polynomial.map_X] at hj3
        have hzn : ρ (ϖ ^ n) = 0 := by
          rw [res_eq_zero_iff hϖ]; exact dvd_pow_self ϖ (by omega)
        rw [jet_map, map_add, map_mul, hzn, zero_mul, add_zero] at hj3
        refine ⟨V.map ρ, ?_, hj3⟩
        have hb := hV.map ρ
        rwa [map_add, hρt i, add_zero, hρY] at hb
      have hvS : ∀ i, VanishAt (f.map ρ) (α.map ρ) (β.map ρ) (ρ (x i)) (-ρ (y i)) (m + 1) := by
        intro i
        obtain ⟨W, hW, hj⟩ := hS i
        rw [hae, hbe, hsplit] at hj
        have hj2 := X_pow_dvd_of_C_mul (pow_ne_zero r hϖ0)
          ((dvd_add_right (Dvd.dvd.mul_left (hU0 i) _)).mp hj)
        refine ⟨W.map ρ, ?_, by rw [← jet_map]; simpa using Polynomial.map_dvd ρ hj2⟩
        have := hW.map ρ
        rwa [map_neg] at this
      obtain ⟨hβ0, c', hc'⟩ := structure_mod hxk h2y
        ((natDegree_map_le).trans hαd) ((degree_map_le).trans_lt hβd) hvQ hvS
      obtain ⟨c'', hc''⟩ := IsLocalRing.residue_surjective c'
      have hα' : C ϖ ∣ α - C c'' * u ^ (m + 1) := by
        rw [C_dvd_iff_map hϖ, Polynomial.map_sub, hc', Polynomial.map_mul, map_C, hc'',
          Polynomial.map_pow, hmap_u, sub_self]
      have hβ' : C ϖ ∣ β := by rw [C_dvd_iff_map hϖ]; exact hβ0
      obtain ⟨α', hα'e⟩ := hα'
      obtain ⟨β', hβ'e⟩ := hβ'
      refine ⟨c + ϖ ^ r * c'', α', β', ?_, ?_, ?_, ?_⟩
      · rw [hae, show α = C c'' * u ^ (m + 1) + C ϖ * α' by rw [← hα'e]; ring]
        simp only [map_add, map_mul, map_pow]; ring
      · rw [hbe, hβ'e]; simp only [map_mul, map_pow]; ring
      · have h1 : (C ϖ * α').natDegree = α'.natDegree := natDegree_C_mul hϖ0
        rw [← h1, ← hα'e]
        refine (natDegree_sub_le _ _).trans (max_le hαd ?_)
        exact (natDegree_C_mul_le _ _).trans hdegU.le
      · rw [hβ'e, degree_C_mul hϖ0] at hβd; exact hβd
  obtain ⟨c, α, β, hae, hbe, hαd, hβd⟩ := layers n le_rfl
  -- `c` is a unit
  have hc : ρ c ≠ 0 := by
    intro hc0
    apply hab
    refine ⟨?_, ?_⟩
    · rw [hae]
      exact dvd_add ((_root_.map_dvd C ((res_eq_zero_iff hϖ _).mp hc0)).mul_right _)
        ((_root_.map_dvd C (dvd_pow_self ϖ (by omega))).mul_right _)
    · rw [hbe]
      exact (_root_.map_dvd C (dvd_pow_self ϖ (by omega))).mul_right _
  -- the tangent equations over the residue field
  have htan : ∀ i, (X - C (ρ (x i))) ^ m ∣ β.map ρ ∧
      (β.map ρ = 0 → ρ (c * ((m + 1 : O) * τ i *
        (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1))) = 0) := by
    intro i
    obtain ⟨V, hV, hj⟩ := hQ i
    obtain ⟨W, hW, hjS⟩ := hS i
    obtain ⟨R₁, R₂, hUi⟩ := hU i
    set κ : O := c * ((m + 1 : O) * τ i * (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1))
    rw [hae, hbe, hsplit, hUi, hτ i] at hj
    have e : C c * (X ^ (m + 1) * R₁ + C ((m + 1 : O) * (ϖ ^ n * τ i) *
        (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1)) * X ^ m +
        C ((ϖ ^ n * τ i) ^ 2) * R₂) + C (ϖ ^ n) * jet α β (x i + ϖ ^ n * τ i) V =
        X ^ (m + 1) * (C c * R₁) + C (ϖ ^ n) * (jet α β (x i + ϖ ^ n * τ i) V -
          C (-κ) * X ^ m + C (c * ϖ ^ n * τ i ^ 2) * R₂) := by
      simp only [κ, map_mul, map_pow, map_add, map_neg]; ring
    rw [e] at hj
    have hj2 := X_pow_dvd_of_C_mul (pow_ne_zero n hϖ0)
      ((dvd_add_right (dvd_mul_right _ _)).mp hj)
    have hj3 := Polynomial.map_dvd ρ hj2
    have hz : ρ (ϖ ^ n) = 0 := by rw [res_eq_zero_iff hϖ]; exact dvd_pow_self ϖ (by omega)
    have hz2 : ρ (c * ϖ ^ n * τ i ^ 2) = 0 := by rw [map_mul, map_mul, hz, mul_zero, zero_mul]
    rw [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, map_C,
      map_C, hz2, map_zero, zero_mul, add_zero, Polynomial.map_pow, Polynomial.map_X, jet_map,
      map_add, map_mul, hz, zero_mul, add_zero, Polynomial.map_pow, Polynomial.map_X] at hj3
    have hVk := hV.map ρ
    rw [map_add, hρt i, add_zero, hρY] at hVk
    rw [hae, hbe, hsplit] at hjS
    have hjS2 := X_pow_dvd_of_C_mul (pow_ne_zero n hϖ0)
      ((dvd_add_right (Dvd.dvd.mul_left (hU0 i) _)).mp hjS)
    have hjS3 : X ^ (m + 1) ∣ jet (α.map ρ) (β.map ρ) (ρ (x i)) (W.map ρ) := by
      rw [← jet_map]; simpa using Polynomial.map_dvd ρ hjS2
    have hWk := hW.map ρ
    rw [map_neg] at hWk
    obtain ⟨-, hβd', hlam⟩ := tangent_jet (f := f.map ρ) (a := α.map ρ) (b := β.map ρ)
      (V := V.map ρ) (W := W.map ρ) (x₀ := ρ (x i)) (Y₀ := ρ (y i)) (lam := ρ (-κ)) (m := m)
      (h2y i) hVk hWk hj3 hjS3
    refine ⟨hβd', fun h0 ↦ ?_⟩
    have := hlam h0
    rw [map_neg, neg_eq_zero] at this
    exact this
  have hβ0 : β.map ρ = 0 := eq_zero_of_prod_pow_dvd hxk (fun i ↦ (htan i).1)
    ((degree_map_le).trans_lt hβd)
  apply hn1
  intro i
  have h1 := (htan i).2 hβ0
  have hℓk : ρ ((m + 1 : ℕ) : O) ≠ 0 := (hℓ.map ρ).ne_zero
  have hck : ρ (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1) ≠ 0 := by
    refine pow_ne_zero _ (IsUnit.ne_zero ?_)
    refine IsUnit.map ρ ?_
    exact (IsUnit.prod_iff.mpr fun j hj ↦ hx i j (Finset.ne_of_mem_erase hj).symm)
  push_cast at hℓk
  simp only [map_mul, map_pow] at h1
  have hτ0 : ρ (τ i) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hc
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hℓk
        · exact h
      · exact absurd h (by rw [← map_pow]; exact hck)
  rw [hτ i, pow_succ]
  exact mul_dvd_mul_left _ ((res_eq_zero_iff hϖ _).mp hτ0)

end Main

end Jac
