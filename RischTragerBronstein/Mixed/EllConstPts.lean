import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.CubicDiscriminant

/-!
# A constant elliptic curve has no non-constant points over `k(t)`

Over an algebraically closed field `k` of characteristic `0`, with `e₁, e₂, e₃` distinct: if
`R² = ∏ (P − eᵢ D²)` with `P, D` coprime, then `P′ D = 2 P D′`, i.e. `(P/D²)′ = 0`.

Proof: `Lᵢ = P − eᵢ D²` are pairwise coprime and `W = P′D − 2PD′ = D Lᵢ′ − 2 D′ Lᵢ`; at a root `a`
of `Lᵢ` of multiplicity `2ν` (`R² = ∏ L`), `W` vanishes to order `≥ 2ν − 1 ≥ ν`, so `R ∣ W`
(`dvd_W`); and `deg W < deg R` (`natDegree_W_lt`), so `W = 0` (`cubic_const`).
-/

open Polynomial

namespace EllConst

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

/-- The factors `Lᵢ` are pairwise coprime. -/
lemma coprime_L (P D : k[X]) (hPD : IsCoprime P D) (a b : k) (hab : a ≠ b) :
    IsCoprime (P - C a * D ^ 2) (P - C b * D ^ 2) := by
  have h1 : IsCoprime (P - C a * D ^ 2) (D ^ 2) := by
    have : IsCoprime P (D ^ 2) := hPD.pow_right
    have h := this.add_mul_right_left (-C a)
    convert h using 1; ring
  have e : P - C b * D ^ 2 = (P - C a * D ^ 2) + C (a - b) * D ^ 2 := by
    rw [C_sub]; ring
  have hu : IsCoprime (P - C a * D ^ 2) (C (a - b)) :=
    ⟨0, C (a - b)⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), C_1]⟩
  have h2 := (hu.mul_right h1).add_mul_left_right 1
  rw [e]; convert h2 using 1; ring

lemma W_eq (P D : k[X]) (a : k) : derivative P * D - 2 * P * derivative D =
    D * derivative (P - C a * D ^ 2) - 2 * derivative D * (P - C a * D ^ 2) := by
  simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add, derivative_pow]
  simp only [map_ofNat, Nat.cast_ofNat]; ring

lemma not_both_root {p q : k[X]} (h : IsCoprime p q) (a : k) (hp : p.IsRoot a) (hq : q.IsRoot a) :
    False := by
  obtain ⟨u, v, huv⟩ := h
  have := congrArg (eval a) huv
  simp only [eval_add, eval_mul, hp.eq_zero, hq.eq_zero, mul_zero, add_zero, eval_one] at this
  exact zero_ne_one this

/-- **`R ∣ W`.** -/
lemma dvd_W (e : Fin 3 → k) (he : Function.Injective e) (P D R : k[X]) (hPD : IsCoprime P D)
    (h : R ^ 2 = ∏ i, (P - C (e i) * D ^ 2)) (hR : R ≠ 0) :
    R ∣ derivative P * D - 2 * P * derivative D := by
  classical
  set W := derivative P * D - 2 * P * derivative D with hW
  by_cases hW0 : W = 0
  · rw [hW0]; exact dvd_zero _
  set L : Fin 3 → k[X] := fun i ↦ P - C (e i) * D ^ 2 with hL
  have hcop : ∀ i j, i ≠ j → IsCoprime (L i) (L j) := fun i j hij ↦
    coprime_L P D hPD _ _ (fun h ↦ hij (he h))
  have hprod : R ^ 2 = L 0 * L 1 * L 2 := by rw [h, Fin.prod_univ_three]
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  refine Splits.dvd_of_roots_le_roots (IsAlgClosed.splits R) hR (Multiset.le_iff_count.mpr fun a ↦ ?_)
  rw [count_roots, count_roots]
  set ν := rootMultiplicity a R with hν
  by_cases hν0 : ν = 0
  · rw [hν0]; exact Nat.zero_le _
  have h2ν : rootMultiplicity a (R ^ 2) = 2 * ν := by
    rw [sq, rootMultiplicity_mul (by rw [← sq]; exact hR2)]; ring
  have h01 : L 0 * L 1 ≠ 0 := left_ne_zero_of_mul (hprod ▸ hR2)
  have hsum : rootMultiplicity a (L 0) + rootMultiplicity a (L 1) + rootMultiplicity a (L 2) =
      2 * ν := by
    rw [← h2ν, hprod, rootMultiplicity_mul (hprod ▸ hR2), rootMultiplicity_mul h01]
  have hL3 : L 0 * L 1 * L 2 ≠ 0 := hprod ▸ hR2
  have hLne : ∀ i, L i ≠ 0 := fun i ↦ by
    have h0 := left_ne_zero_of_mul (left_ne_zero_of_mul hL3)
    have h1 := right_ne_zero_of_mul (left_ne_zero_of_mul hL3)
    have h2 := right_ne_zero_of_mul hL3
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  -- the unique factor vanishing at `a`
  have hroot : ∀ i, 0 < rootMultiplicity a (L i) → (L i).IsRoot a := fun i hi ↦
    (rootMultiplicity_pos (hLne i)).mp hi
  obtain ⟨i₀, hi₀, hoth⟩ : ∃ i₀, rootMultiplicity a (L i₀) = 2 * ν ∧ True := by
    have hz : ∀ i j, i ≠ j → rootMultiplicity a (L i) = 0 ∨ rootMultiplicity a (L j) = 0 :=
      fun i j hij ↦ by
        by_contra hc; push Not at hc
        exact not_both_root (hcop i j hij) a (hroot i (Nat.pos_of_ne_zero hc.1))
          (hroot j (Nat.pos_of_ne_zero hc.2))
    rcases Nat.eq_zero_or_pos (rootMultiplicity a (L 0)) with h0 | h0
    · rcases Nat.eq_zero_or_pos (rootMultiplicity a (L 1)) with h1 | h1
      · exact ⟨2, by omega, trivial⟩
      · have := (hz 1 2 (by decide)).resolve_left (by omega); exact ⟨1, by omega, trivial⟩
    · have a1 := (hz 0 1 (by decide)).resolve_left (by omega)
      have a2 := (hz 0 2 (by decide)).resolve_left (by omega)
      exact ⟨0, by omega, trivial⟩
  have hrt : (L i₀).IsRoot a := hroot i₀ (by omega)
  have hder : rootMultiplicity a (derivative (L i₀)) = 2 * ν - 1 := by
    rw [derivative_rootMultiplicity_of_root hrt, hi₀]
  have hd1 : (X - C a) ^ (2 * ν - 1) ∣ derivative (L i₀) := by
    rw [← hder]; exact pow_rootMultiplicity_dvd _ _
  have hd2 : (X - C a) ^ (2 * ν - 1) ∣ L i₀ := by
    refine (pow_dvd_pow _ (by omega : 2 * ν - 1 ≤ 2 * ν)).trans ?_
    rw [← hi₀]; exact pow_rootMultiplicity_dvd _ _
  have hdW : (X - C a) ^ ν ∣ W := by
    refine (pow_dvd_pow _ (by omega : ν ≤ 2 * ν - 1)).trans ?_
    rw [hW, W_eq P D (e i₀)]
    exact dvd_sub (dvd_mul_of_dvd_right hd1 _) (dvd_mul_of_dvd_right hd2 _)
  exact (le_rootMultiplicity_iff hW0).mpr hdW

lemma natDegree_W_le (D L : k[X]) :
    (D * derivative L - 2 * derivative D * L).natDegree ≤ D.natDegree + L.natDegree - 1 := by
  have h1 : (D * derivative L).natDegree ≤ D.natDegree + L.natDegree - 1 := by
    by_cases hL : L.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hL, derivative_C, mul_zero, natDegree_zero]; exact Nat.zero_le _
    · exact (natDegree_mul_le).trans (by have := natDegree_derivative_le L; omega)
  have h2 : (2 * derivative D * L).natDegree ≤ D.natDegree + L.natDegree - 1 := by
    by_cases hD : D.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hD, derivative_C, mul_zero, zero_mul, natDegree_zero]
      exact Nat.zero_le _
    · refine (natDegree_mul_le).trans ?_
      have := natDegree_derivative_le D
      have h2c : (2 * derivative D).natDegree ≤ (derivative D).natDegree :=
        (natDegree_mul_le).trans (by simp)
      omega
  exact (natDegree_sub_le _ _).trans (max_le h1 h2)

lemma natDegree_L_pair (P D : k[X]) (hD : D ≠ 0) (a b : k) (hab : a ≠ b) :
    max P.natDegree (2 * D.natDegree) ≤
      max (P - C a * D ^ 2).natDegree (P - C b * D ^ 2).natDegree := by
  have hdiff : (P - C a * D ^ 2) - (P - C b * D ^ 2) = C (b - a) * D ^ 2 := by rw [C_sub]; ring
  have hdeg : (C (b - a) * D ^ 2).natDegree = 2 * D.natDegree := by
    rw [natDegree_C_mul (sub_ne_zero.mpr hab.symm), natDegree_pow, mul_comm]
  have h2d : 2 * D.natDegree ≤ max (P - C a * D ^ 2).natDegree (P - C b * D ^ 2).natDegree := by
    rw [← hdeg, ← hdiff]; exact natDegree_sub_le _ _
  refine max_le ?_ h2d
  by_cases hp : P.natDegree ≤ 2 * D.natDegree
  · exact hp.trans h2d
  · push Not at hp
    have hlt : (C a * D ^ 2).natDegree < P.natDegree := by
      refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
      rw [natDegree_pow]; omega
    rw [natDegree_sub_eq_left_of_natDegree_lt hlt]; exact le_max_left _ _

/-- **The main lemma**: `P′ D = 2 P D′`. -/
theorem cubic_const (e : Fin 3 → k) (he : Function.Injective e) (P D R : k[X]) (hD : D ≠ 0)
    (hPD : IsCoprime P D) (h : R ^ 2 = ∏ i, (P - C (e i) * D ^ 2)) :
    derivative P * D = 2 * P * derivative D := by
  classical
  set L : Fin 3 → k[X] := fun i ↦ P - C (e i) * D ^ 2 with hL
  by_contra hW
  have hW0 : derivative P * D - 2 * P * derivative D ≠ 0 := sub_ne_zero.mpr hW
  have hprod : R ^ 2 = L 0 * L 1 * L 2 := by rw [h, Fin.prod_univ_three]
  by_cases hR : R = 0
  · -- some `Lᵢ = 0`: `P = eᵢ D²`, `D` a unit, everything constant
    exfalso
    rw [hR, zero_pow two_ne_zero] at hprod
    have : ∃ i, L i = 0 := by
      rcases mul_eq_zero.mp hprod.symm with h01 | h2
      · rcases mul_eq_zero.mp h01 with h0 | h1
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
    obtain ⟨i, hi⟩ := this
    have hP : P = C (e i) * D ^ 2 := sub_eq_zero.mp hi
    have hu : IsUnit D := by
      rw [hP] at hPD
      have h1 : IsCoprime (D ^ 2) D := hPD.of_mul_left_right
      rw [sq] at h1
      exact isCoprime_self.mp h1.of_mul_left_left
    obtain ⟨c, hc⟩ := Polynomial.isUnit_iff.mp hu
    apply hW
    rw [hP, ← hc.2]; simp
  have hdvd := dvd_W e he P D R hPD h hR
  have hle := natDegree_le_of_dvd hdvd hW0
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  have hL3 : L 0 * L 1 * L 2 ≠ 0 := hprod ▸ hR2
  have hL0 := left_ne_zero_of_mul (left_ne_zero_of_mul hL3)
  have hL1 := right_ne_zero_of_mul (left_ne_zero_of_mul hL3)
  have hL2 := right_ne_zero_of_mul hL3
  have hdegR : 2 * R.natDegree = (L 0).natDegree + (L 1).natDegree + (L 2).natDegree := by
    rw [← natDegree_pow, hprod, natDegree_mul (left_ne_zero_of_mul hL3) hL2, natDegree_mul hL0 hL1]
  set M := max P.natDegree (2 * D.natDegree)
  have p01 := natDegree_L_pair P D hD (e 0) (e 1) (fun h ↦ absurd (he h) (by decide))
  have p02 := natDegree_L_pair P D hD (e 0) (e 2) (fun h ↦ absurd (he h) (by decide))
  have p12 := natDegree_L_pair P D hD (e 1) (e 2) (fun h ↦ absurd (he h) (by decide))
  -- `M ≥ 1`
  have hM : 1 ≤ M := by
    by_contra hM0
    have hp0 : P.natDegree = 0 := by omega
    have hd0 : D.natDegree = 0 := by omega
    apply hW
    rw [eq_C_of_natDegree_eq_zero hp0, eq_C_of_natDegree_eq_zero hd0]; simp
  have hWi : ∀ i, (derivative P * D - 2 * P * derivative D).natDegree ≤
      D.natDegree + (L i).natDegree - 1 := fun i ↦ by
    rw [W_eq P D (e i)]; exact natDegree_W_le D (L i)
  have w0 := hWi 0
  have w1 := hWi 1
  have w2 := hWi 2
  simp only [L] at p01 p02 p12 hdegR w0 w1 w2
  have hMd : 2 * D.natDegree ≤ M := le_max_right _ _
  omega

/-- `a³ ∣ b²` forces `a ∣ b` (over an algebraically closed field). -/
lemma dvd_of_cube_dvd_sq (a b : k[X]) (ha : a ≠ 0) (hb : b ≠ 0) (h : a ^ 3 ∣ b ^ 2) : a ∣ b := by
  classical
  refine Splits.dvd_of_roots_le_roots (IsAlgClosed.splits a) ha (Multiset.le_iff_count.mpr fun r ↦ ?_)
  rw [count_roots, count_roots]
  have h0 : (X - C r) ^ (3 * rootMultiplicity r a) ∣ a ^ 3 := by
    rw [pow_mul']; exact pow_dvd_pow_of_dvd (pow_rootMultiplicity_dvd a r) 3
  have h1 := h0.trans h
  have h2 := (le_rootMultiplicity_iff (pow_ne_zero 2 hb)).mpr h1
  rw [sq, rootMultiplicity_mul (mul_ne_zero hb hb)] at h2
  omega

/-- **Constant points, algebraically closed field.** -/
theorem const_of_cubic_closed (num den r s : k[X]) (c : k) (e : Fin 3 → k)
    (he : Function.Injective e) (hc : c ≠ 0) (hden : den ≠ 0) (hs : s ≠ 0)
    (h1 : IsCoprime num den) (h2 : IsCoprime r s)
    (h : r ^ 2 * den ^ 3 = C c * s ^ 2 * ∏ i, (num - C (e i) * den)) :
    num.natDegree = 0 ∧ den.natDegree = 0 := by
  set F := ∏ i, (num - C (e i) * den) with hF
  have hFd : IsCoprime F den := IsCoprime.prod_left fun i _ ↦ by
    have := h1.add_mul_right_left (-C (e i)); convert this using 1; ring
  -- `s² ∣ den³` and `den³ ∣ s²`
  have hsd : s ^ 2 ∣ den ^ 3 := by
    have : s ^ 2 ∣ r ^ 2 * den ^ 3 := ⟨C c * F, by rw [h]; ring⟩
    exact (h2.pow.symm).dvd_of_dvd_mul_left this
  have hds : den ^ 3 ∣ s ^ 2 := by
    have h3 : den ^ 3 ∣ C c * s ^ 2 * F := ⟨r ^ 2, by rw [← h]; ring⟩
    have hFd3 : IsCoprime (den ^ 3) F := hFd.symm.pow_left
    have hc3 : IsCoprime (den ^ 3) (C c) :=
      ⟨0, C c⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hc, C_1]⟩
    have h4 := hFd3.dvd_of_dvd_mul_right h3
    exact hc3.dvd_of_dvd_mul_left h4
  obtain ⟨t, ht⟩ := dvd_of_cube_dvd_sq den s hden hs hds
  have ht0 : t ≠ 0 := by rintro rfl; exact hs (by rw [ht, mul_zero])
  -- `den ∼ t²`
  have htd : t ^ 2 ∣ den := by
    have : den ^ 2 * t ^ 2 ∣ den ^ 2 * den := by
      rw [← mul_pow, ← ht, ← pow_succ]; exact hsd
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hden)).mp this
  have hdt : den ∣ t ^ 2 := by
    have : den ^ 2 * den ∣ den ^ 2 * t ^ 2 := by
      rw [← mul_pow, ← ht, ← pow_succ]; exact hds
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hden)).mp this
  obtain ⟨w, hw⟩ := associated_of_dvd_dvd htd hdt
  obtain ⟨v, hv, hvw⟩ := Polynomial.isUnit_iff.mp w.isUnit
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq v two_pos
  set D := C z * t with hD
  have hdenD : den = D ^ 2 := by
    rw [← hw, ← hvw, hD, mul_pow, ← C_pow, hz]; ring
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0, zero_pow two_ne_zero] at hz; exact hv.ne_zero hz.symm
  have hD0 : D ≠ 0 := mul_ne_zero (C_ne_zero.mpr hz0) ht0
  have hnD : IsCoprime num D := by
    rw [hdenD, sq] at h1; exact h1.of_mul_right_left
  -- `R² = ∏ (num − eᵢ D²)`
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (v / c) two_pos
  have hFR : (C y * r) ^ 2 = ∏ i, (num - C (e i) * D ^ 2) := by
    rw [← hdenD]
    have e1 : r ^ 2 * den ^ 3 = den ^ 2 * (r ^ 2 * den) := by ring
    have e2 : C c * s ^ 2 * F = den ^ 2 * (C c * t ^ 2 * F) := by rw [ht]; ring
    rw [e1, e2] at h
    have h' := mul_left_cancel₀ (pow_ne_zero 2 hden) h
    rw [hdenD, hD, mul_pow, ← C_pow, hz] at h'
    have h'' : t ^ 2 * (C v * r ^ 2) = t ^ 2 * (C c * F) := by
      have : r ^ 2 * (C v * t ^ 2) = C c * t ^ 2 * F := by
        rw [← h']
      linear_combination this
    have h3 := mul_left_cancel₀ (pow_ne_zero 2 ht0) h''
    rw [mul_pow, ← C_pow, hy]
    have hcF : F = C (v / c) * r ^ 2 := by
      have := congrArg (fun q ↦ C c⁻¹ * q) h3
      rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul] at this
      rw [← this, div_eq_inv_mul, C_mul]
    rw [← hcF]
  have hmain := cubic_const e he num D (C y * r) hD0 hnD hFR
  -- `D′ = 0`, then `num′ = 0`
  have hDD : D ∣ 2 * derivative D := by
    have : D ∣ num * (2 * derivative D) := by
      refine ⟨derivative num, ?_⟩
      rw [show num * (2 * derivative D) = 2 * num * derivative D by ring, ← hmain, mul_comm]
    exact hnD.symm.dvd_of_dvd_mul_left this
  have hD' : derivative D = 0 := by
    by_contra hne
    have hdvd : D ∣ derivative D := by
      have h2u : IsUnit (2 : k[X]) := by
        rw [show (2 : k[X]) = C 2 from (map_ofNat C 2).symm]
        exact isUnit_C.mpr (two_ne_zero (α := k)).isUnit
      exact (h2u.dvd_mul_left).mp hDD
    have hle := natDegree_le_of_dvd hdvd hne
    have hlt := natDegree_derivative_lt (p := D) (fun h0 ↦ by
      rw [eq_C_of_natDegree_eq_zero h0, derivative_C] at hne; exact hne rfl)
    omega
  have hnum' : derivative num = 0 := by
    rw [hD', mul_zero] at hmain
    exact (mul_eq_zero.mp hmain).resolve_right hD0
  refine ⟨?_, ?_⟩
  · rw [eq_C_of_derivative_eq_zero hnum']; exact natDegree_C _
  · rw [hdenD, eq_C_of_derivative_eq_zero hD', ← C_pow]; exact natDegree_C _

omit [IsAlgClosed k] in
/-- Base change to an algebraically closed extension. -/
theorem const_of_cubic_map {K' : Type*} [Field K'] [IsAlgClosed K'] [CharZero K'] (φ : k →+* K')
    (num den r s : k[X]) (c : k) (e : Fin 3 → k)
    (he : Function.Injective e) (hc : c ≠ 0) (hden : den ≠ 0) (hs : s ≠ 0)
    (h1 : IsCoprime num den) (h2 : IsCoprime r s)
    (h : r ^ 2 * den ^ 3 = C c * s ^ 2 * ∏ i, (num - C (e i) * den)) :
    num.natDegree = 0 ∧ den.natDegree = 0 := by
  have hφ : Function.Injective φ := φ.injective
  have hm : (r.map φ) ^ 2 * (den.map φ) ^ 3 =
      C (φ c) * (s.map φ) ^ 2 * ∏ i, (num.map φ - C (φ (e i)) * den.map φ) := by
    have := congrArg (Polynomial.map φ) h
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_C] using this
  have hc1 : IsCoprime (num.map φ) (den.map φ) := h1.map (Polynomial.mapRingHom φ)
  have hc2 : IsCoprime (r.map φ) (s.map φ) := h2.map (Polynomial.mapRingHom φ)
  have hinj : Function.Injective fun i ↦ φ (e i) := fun i j hij ↦ he (hφ hij)
  have hc0 : φ c ≠ 0 := (map_ne_zero_iff _ hφ).mpr hc
  have hd0 : den.map φ ≠ 0 := Polynomial.map_ne_zero hden
  have hs0 : s.map φ ≠ 0 := Polynomial.map_ne_zero hs
  obtain ⟨t1, t2⟩ := const_of_cubic_closed (num.map φ) (den.map φ) (r.map φ) (s.map φ) (φ c)
    (fun i ↦ φ (e i)) hinj hc0 hd0 hs0 hc1 hc2 hm
  rw [natDegree_map_eq_of_injective hφ] at t1 t2
  exact ⟨t1, t2⟩

omit [IsAlgClosed k] in
/-- **Constant points over any field of characteristic `0`.** -/
theorem const_of_cubic (num den r s : k[X]) (c : k) (e : Fin 3 → k)
    (he : Function.Injective e) (hc : c ≠ 0) (hden : den ≠ 0) (hs : s ≠ 0)
    (h1 : IsCoprime num den) (h2 : IsCoprime r s)
    (h : r ^ 2 * den ^ 3 = C c * s ^ 2 * ∏ i, (num - C (e i) * den)) :
    num.natDegree = 0 ∧ den.natDegree = 0 :=
  haveI : CharZero (AlgebraicClosure k) :=
    charZero_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective
  const_of_cubic_map (algebraMap k (AlgebraicClosure k)) num den r s c e he hc hden hs h1 h2 h

omit [IsAlgClosed k] in
/-- **A constant elliptic curve has no non-constant points over `k(t)`**: if
`y² = c (x − e₁)(x − e₂)(x − e₃)` in `k(t)` (`eᵢ` distinct, `c ≠ 0`), then `x ∈ k`. -/
theorem ratFunc_const (x y : RatFunc k) (c : k) (e : Fin 3 → k) (he : Function.Injective e)
    (hc : c ≠ 0) (h : y ^ 2 = RatFunc.C c * ∏ i, (x - RatFunc.C (e i))) :
    ∃ a : k, x = RatFunc.C a := by
  set ι := algebraMap k[X] (RatFunc k)
  have hinj : Function.Injective ι := IsFractionRing.injective k[X] (RatFunc k)
  have hx := RatFunc.num_div_denom x
  have hy := RatFunc.num_div_denom y
  have hd : x.denom ≠ 0 := x.denom_ne_zero
  have hs : y.denom ≠ 0 := y.denom_ne_zero
  have hιd : ι x.denom ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd
  have hιs : ι y.denom ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs
  have key : y.num ^ 2 * x.denom ^ 3 = C c * y.denom ^ 2 * ∏ i, (x.num - C (e i) * x.denom) := by
    apply hinj
    simp only [map_mul, map_pow, map_prod, map_sub, ι, RatFunc.algebraMap_C]
    rw [← hx, ← hy] at h
    have hD' : algebraMap k[X] (RatFunc k) x.denom ≠ 0 := hιd
    have hS' : algebraMap k[X] (RatFunc k) y.denom ≠ 0 := hιs
    generalize algebraMap k[X] (RatFunc k) x.num = X at h ⊢
    generalize algebraMap k[X] (RatFunc k) y.num = Y at h ⊢
    generalize algebraMap k[X] (RatFunc k) x.denom = D at h hD' ⊢
    generalize algebraMap k[X] (RatFunc k) y.denom = S at h hS' ⊢
    rw [Fin.prod_univ_three] at h ⊢
    field_simp at h
    linear_combination h
  obtain ⟨hn0, hd0⟩ := const_of_cubic x.num x.denom y.num y.denom c e he hc hd hs
    (RatFunc.isCoprime_num_denom x) (RatFunc.isCoprime_num_denom y) key
  have hd1 : x.denom = 1 := by
    have hm := RatFunc.monic_denom x
    rw [eq_C_of_natDegree_eq_zero hd0] at hm ⊢
    rw [Monic, leadingCoeff_C] at hm
    rw [hm, C_1]
  refine ⟨x.num.coeff 0, ?_⟩
  conv_lhs => rw [← hx]
  rw [hd1, map_one, div_one]
  conv_lhs => rw [eq_C_of_natDegree_eq_zero hn0]
  rw [RatFunc.algebraMap_C]

set_option maxHeartbeats 800000 in
omit [IsAlgClosed k] in
/-- **Constant points of a Weierstrass curve** `y² = x³ + a x + b` (`4a³ + 27b² ≠ 0`), polynomial form. -/
theorem poly_const_weierstrass (a b : k) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (num den r s : k[X])
    (hden : den ≠ 0) (hs : s ≠ 0) (h1 : IsCoprime num den) (h2 : IsCoprime r s)
    (h : r ^ 2 * den ^ 3 = s ^ 2 * (num ^ 3 + C a * num * den ^ 2 + C b * den ^ 3)) :
    num.natDegree = 0 ∧ den.natDegree = 0 := by
  haveI : CharZero (AlgebraicClosure k) :=
    charZero_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective
  set φ := algebraMap k (AlgebraicClosure k)
  have hφ : Function.Injective φ := φ.injective
  set P : Cubic k := ⟨1, 0, a, b⟩
  have ha : P.a ≠ 0 := one_ne_zero
  obtain ⟨x0, y0, z0, h3⟩ := (Cubic.splits_iff_roots_eq_three (φ := φ) ha).mp (IsAlgClosed.splits _)
  have hdisc : P.discr ≠ 0 := by
    simp only [Cubic.discr, P]; intro h0; apply hΔ; linear_combination -h0
  obtain ⟨hxy, hxz, hyz⟩ := (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdisc
  have hσ1 := Cubic.b_eq_three_roots ha h3
  have hσ2 := Cubic.c_eq_three_roots ha h3
  have hσ3 := Cubic.d_eq_three_roots ha h3
  simp only [P, map_one, map_zero, one_mul] at hσ1 hσ2 hσ3
  set e : Fin 3 → AlgebraicClosure k := ![x0, y0, z0]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [e]
  set n := num.map φ
  set d := den.map φ
  have hm : (r.map φ) ^ 2 * d ^ 3 = C 1 * (s.map φ) ^ 2 * ∏ i, (n - C (e i) * d) := by
    have hh := congrArg (Polynomial.map φ) h
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C] at hh
    rw [hh, Fin.prod_univ_three, C_1, one_mul]
    rw [show e 0 = x0 from rfl, show e 1 = y0 from rfl, show e 2 = z0 from rfl]
    have k1 : C x0 + C y0 + C z0 = (0 : (AlgebraicClosure k)[X]) := by
      rw [← C_add, ← C_add, show x0 + y0 + z0 = 0 by linear_combination hσ1, C_0]
    have k2 : C x0 * C y0 + C x0 * C z0 + C y0 * C z0 = C (φ a) := by
      rw [← C_mul, ← C_mul, ← C_mul, ← C_add, ← C_add, hσ2]
    have k3 : C x0 * C y0 * C z0 = -C (φ b) := by
      rw [← C_mul, ← C_mul, ← C_neg, hσ3, neg_neg]
    linear_combination (s.map φ) ^ 2 * ((n ^ 2 * d) * k1 - (n * d ^ 2) * k2 + d ^ 3 * k3)
  obtain ⟨t1, t2⟩ := const_of_cubic_closed n d (r.map φ) (s.map φ) 1 e he one_ne_zero
    (Polynomial.map_ne_zero hden) (Polynomial.map_ne_zero hs)
    (h1.map (Polynomial.mapRingHom φ)) (h2.map (Polynomial.mapRingHom φ)) hm
  rw [natDegree_map_eq_of_injective hφ] at t1 t2
  exact ⟨t1, t2⟩

omit [IsAlgClosed k] in
/-- **No non-constant points on a constant Weierstrass curve over `k(t)`.** -/
theorem weierstrass_const (a b : k) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (x y : RatFunc k)
    (h : y ^ 2 = x ^ 3 + RatFunc.C a * x + RatFunc.C b) : ∃ c : k, x = RatFunc.C c := by
  set ι := algebraMap k[X] (RatFunc k)
  have hinj : Function.Injective ι := IsFractionRing.injective k[X] (RatFunc k)
  have hx := RatFunc.num_div_denom x
  have hy := RatFunc.num_div_denom y
  have hd : x.denom ≠ 0 := x.denom_ne_zero
  have hs : y.denom ≠ 0 := y.denom_ne_zero
  have hιd : ι x.denom ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd
  have hιs : ι y.denom ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs
  have key : y.num ^ 2 * x.denom ^ 3 =
      y.denom ^ 2 * (x.num ^ 3 + C a * x.num * x.denom ^ 2 + C b * x.denom ^ 3) := by
    apply hinj
    simp only [map_mul, map_pow, map_add, ι, RatFunc.algebraMap_C]
    rw [← hx, ← hy] at h
    have hD' : algebraMap k[X] (RatFunc k) x.denom ≠ 0 := hιd
    have hS' : algebraMap k[X] (RatFunc k) y.denom ≠ 0 := hιs
    generalize algebraMap k[X] (RatFunc k) x.num = X at h ⊢
    generalize algebraMap k[X] (RatFunc k) y.num = Y at h ⊢
    generalize algebraMap k[X] (RatFunc k) x.denom = D at h hD' ⊢
    generalize algebraMap k[X] (RatFunc k) y.denom = S at h hS' ⊢
    field_simp at h
    linear_combination h
  obtain ⟨hn0, hd0⟩ := poly_const_weierstrass a b hΔ x.num x.denom y.num y.denom hd hs
    (RatFunc.isCoprime_num_denom x) (RatFunc.isCoprime_num_denom y) key
  have hd1 : x.denom = 1 := by
    have hm := RatFunc.monic_denom x
    rw [eq_C_of_natDegree_eq_zero hd0] at hm ⊢
    rw [Monic, leadingCoeff_C] at hm
    rw [hm, C_1]
  refine ⟨x.num.coeff 0, ?_⟩
  conv_lhs => rw [← hx]
  rw [hd1, map_one, div_one]
  conv_lhs => rw [eq_C_of_natDegree_eq_zero hn0]
  rw [RatFunc.algebraMap_C]

end EllConst

