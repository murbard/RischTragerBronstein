import RischTragerBronstein.Computable.NestMRdeLoop
import RischTragerBronstein.Computable.NestMBasics
import RischTragerBronstein.RDE.NestedBounds

/-!
# The parametric Risch equation over `ℚ(x)`: soundness and completeness

`prde0 h W` returns a basis of the pairs `(c, y)` with `y′ + h′ y = ∑ cᵢ wᵢ`, `y ∈ Kc(x)`:

* soundness: every returned `(e, Y / D)` solves the equation (the null-space relation is the
  polynomial equation `A Y′ + B Y = ∑ eᵢ Cᵢ`, which is the Risch equation times the non-zero
  factor `F₂ P D`);
* completeness: every solution has denominator dividing `D = gcd(e, e′)` (`rde_pole_bound` at
  every prime; `h′` has no simple pole), numerator of degree at most the bound, hence is a
  constant combination of the null-space basis.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP CPoly

/-- `toPoly` of a list given by its coefficients. -/
lemma toPoly_range_map (f : ℕ → ℚ) : ∀ L : ℕ,
    CPoly.toPoly ((List.range L).map f) = ∑ k ∈ Finset.range L, Polynomial.C (f k) * X ^ k
  | 0 => by simp
  | L + 1 => by
    rw [List.range_succ, List.map_append, toPoly_append, toPoly_range_map f L,
      Finset.sum_range_succ]
    simp [List.length_map, List.length_range]

/-- The null-space relation of `prde0B` is the polynomial Risch equation. -/
lemma prde0B_rel (Cs ys : List (CPoly ℚ)) (A B : CPoly ℚ)
    (hys : ∀ k < ys.length, ys.getD k [] = colY A B k) (u : CPoly ℚ)
    (hu : lcomb u (Cs.map CPoly.neg ++ ys) = 0) :
    CPoly.toPoly A * derivative (∑ k ∈ Finset.range ys.length,
        Polynomial.C (u.getD (Cs.length + k) 0) * X ^ k) +
      CPoly.toPoly B * (∑ k ∈ Finset.range ys.length,
        Polynomial.C (u.getD (Cs.length + k) 0) * X ^ k) =
    ∑ i ∈ Finset.range Cs.length, Polynomial.C (u.getD i 0) * CPoly.toPoly (Cs.getD i []) := by
  rw [lcomb, zipWith_sum_getD (fun (c : ℚ) (v : CPoly ℚ) ↦ Polynomial.C c * CPoly.toPoly v) 0 []
    (by simp), List.length_append, List.length_map, Finset.sum_range_add] at hu
  have e1 : ∀ i ∈ Finset.range Cs.length, Polynomial.C (u.getD i 0) *
      CPoly.toPoly ((Cs.map CPoly.neg ++ ys).getD i []) =
      -(Polynomial.C (u.getD i 0) * CPoly.toPoly (Cs.getD i [])) := fun i hi ↦ by
    have hi' := Finset.mem_range.mp hi
    rw [List.getD_append _ _ _ _ (by simpa using hi'), NestTower.getD_map' _ _ [] [] hi',
      CPoly.toPoly_neg]
    ring
  have e2 : ∀ k ∈ Finset.range ys.length, Polynomial.C (u.getD (Cs.length + k) 0) *
      CPoly.toPoly ((Cs.map CPoly.neg ++ ys).getD (Cs.length + k) []) =
      CPoly.toPoly A * derivative (Polynomial.C (u.getD (Cs.length + k) 0) * X ^ k) +
        CPoly.toPoly B * (Polynomial.C (u.getD (Cs.length + k) 0) * X ^ k) := fun k hk ↦ by
    have hk' := Finset.mem_range.mp hk
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_map, Nat.add_sub_cancel_left,
      hys k hk', colY, CPoly.toPoly_add, CPoly.toPoly_mul, CPoly.toPoly_mul, CPoly.toPoly_deriv,
      toPoly_monomial]
    simp only [derivative_C_mul, map_one, one_mul]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_neg_distrib,
    Finset.sum_add_distrib] at hu
  rw [derivative_sum, Finset.mul_sum, Finset.mul_sum]
  linear_combination hu

/-! ### The data of `prde0B` -/

def p0Dc (D : CPoly ℚ) : GFrac ℚ := (D, [1])
def p0F (hc : GFrac ℚ) (D : CPoly ℚ) : GFrac ℚ :=
  cleanQ ((ops₁g ℚ).add ((ops₁g ℚ).deriv (cleanQ hc)) ((ops₁g ℚ).neg ((ops₁g ℚ).mul
    ((ops₁g ℚ).deriv (p0Dc D)) ((ops₁g ℚ).inv (p0Dc D)))))
def p0Rs (Wc : List (GFrac ℚ)) (D : CPoly ℚ) : List (GFrac ℚ) :=
  Wc.map fun w ↦ cleanQ ((ops₁g ℚ).mul (p0Dc D) w)
def p0P (Wc : List (GFrac ℚ)) (D : CPoly ℚ) : CPoly ℚ := prodD CPoly.mul [1] (p0Rs Wc D)
def p0A (hc : GFrac ℚ) (Wc : List (GFrac ℚ)) (D : CPoly ℚ) : CPoly ℚ :=
  CPoly.mul (p0F hc D).2 (p0P Wc D)
def p0B (hc : GFrac ℚ) (Wc : List (GFrac ℚ)) (D : CPoly ℚ) : CPoly ℚ :=
  CPoly.mul (p0F hc D).1 (p0P Wc D)
def p0Cs (hc : GFrac ℚ) (Wc : List (GFrac ℚ)) (D : CPoly ℚ) : List (CPoly ℚ) :=
  (cross CPoly.mul [1] (p0Rs Wc D)).map (CPoly.mul (p0F hc D).2)

/-! ### Common denominators over `ℚ` -/

lemma divMod_exact_Q (p d : CPoly ℚ) (hd : CPoly.toPoly d ≠ 0)
    (hdvd : CPoly.toPoly d ∣ CPoly.toPoly p) :
    CPoly.toPoly p = CPoly.toPoly (CPoly.divMod p d).1 * CPoly.toPoly d := by
  have hspec := CPoly.divMod_spec p d
  have hrem : CPoly.toPoly d ∣ CPoly.toPoly (CPoly.divMod p d).2 := by
    have : CPoly.toPoly (CPoly.divMod p d).2 =
        CPoly.toPoly p - CPoly.toPoly (CPoly.divMod p d).1 * CPoly.toPoly d := by
      rw [hspec]; ring
    rw [this]
    exact dvd_sub hdvd (Dvd.intro_left _ rfl)
  have h0 := eq_zero_of_dvd_of_degree_lt hrem (CPoly.divMod_degree_lt p d hd)
  rw [hspec, h0, add_zero]

lemma lcmQ_spec (a b : CPoly ℚ) (ha : CPoly.toPoly a ≠ 0) (hb : CPoly.toPoly b ≠ 0) :
    CPoly.toPoly a ∣ CPoly.toPoly (lcmQ a b) ∧ CPoly.toPoly b ∣ CPoly.toPoly (lcmQ a b) ∧
      CPoly.toPoly (lcmQ a b) ≠ 0 := by
  obtain ⟨hga, hgb⟩ := CPoly.egcd_dvd a b
  set g := (CPoly.egcd a b).1 with hg
  have hg0 : CPoly.toPoly g ≠ 0 := fun h0 ↦ hb (zero_dvd_iff.mp (h0 ▸ hgb))
  have hbq := divMod_exact_Q b g hg0 hgb
  set bq := CPoly.toPoly (CPoly.divMod b g).1 with hbqd
  have hlcm : CPoly.toPoly (lcmQ a b) = CPoly.toPoly a * bq := by rw [lcmQ, CPoly.toPoly_mul]
  have hbq0 : bq ≠ 0 := fun h0 ↦ hb (by rw [hbq, h0, zero_mul])
  obtain ⟨a', ha'⟩ := hga
  exact ⟨⟨bq, hlcm⟩, ⟨a', by rw [hlcm, ha', hbq]; ring⟩, by rw [hlcm]; exact mul_ne_zero ha hbq0⟩

lemma lcm_fold_spec : ∀ Wc : List (GFrac ℚ), (∀ w ∈ Wc, CPoly.toPoly w.2 ≠ 0) →
    (∀ w ∈ Wc, CPoly.toPoly w.2 ∣ CPoly.toPoly (Wc.foldr (fun w acc ↦ lcmQ w.2 acc) [1])) ∧
      CPoly.toPoly (Wc.foldr (fun w acc ↦ lcmQ w.2 acc) [1]) ≠ 0
  | [], _ => ⟨by simp, by simp [CPoly.toPoly]⟩
  | w :: Wc, h0 => by
    obtain ⟨ih1, ih2⟩ := lcm_fold_spec Wc fun v hv ↦ h0 v (List.mem_cons_of_mem _ hv)
    obtain ⟨h1, h2, h3⟩ := lcmQ_spec w.2 _ (h0 w List.mem_cons_self) ih2
    refine ⟨fun v hv ↦ ?_, h3⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h1
    · exact (ih1 v hv).trans h2

lemma cleanQ_den_ne' (w : GFrac ℚ) : CPoly.toPoly (cleanQ w).2 ≠ 0 := by
  unfold cleanQ
  split_ifs with hz
  · simp [CPoly.toPoly]
  · rwa [Ne, ← CPoly.isZero_iff]

/-! ### The degree bound over `Kc[x]` -/

section DegBound

variable {Kc : Type*} [Field Kc] [CharZero Kc]

/-- **The degree bound** for `a Y′ + b Y = r` (`deg r ≤ R`): `deg Y ≤ max (R + 1) q`, where `q`
bounds the only cancelling degree (`deg b = deg a - 1`, `N lc a + lc b = 0`). -/
lemma natDegree_le_of_rde0 (a b Y r : Kc[X]) (R q : ℕ) (hr : r.natDegree ≤ R) (ha : a ≠ 0)
    (heq : a * derivative Y + b * Y = r)
    (hq : b ≠ 0 → b.natDegree + 1 = a.natDegree → ∀ N : ℕ,
      (N : Kc) * a.leadingCoeff + b.leadingCoeff = 0 → N ≤ q) :
    Y.natDegree ≤ max (R + 1) q := by
  by_contra hlt
  push_neg at hlt
  set N0 := Y.natDegree with hN0
  have hNR : R + 1 < N0 := lt_of_le_of_lt (le_max_left _ _) hlt
  have hNq : q < N0 := lt_of_le_of_lt (le_max_right _ _) hlt
  have hY0 : Y ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hN0; omega
  have hN1 : 1 ≤ N0 := by omega
  have hN0c : (N0 : Kc) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlcY : Y.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hY0
  have hlca : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha
  set dA := a.natDegree with hdA
  have hdY : (derivative Y).natDegree ≤ N0 - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_derivative, coeff_eq_zero_of_natDegree_lt (by
      have : N0 - 1 < i := by exact_mod_cast hi
      omega), zero_mul]
  have hcY' : (derivative Y).coeff (N0 - 1) = Y.leadingCoeff * N0 := by
    rw [coeff_derivative, show N0 - 1 + 1 = N0 by omega, leadingCoeff]
    push_cast [Nat.cast_sub hN1]
    ring
  have haY : (a * derivative Y).coeff (dA + (N0 - 1)) = a.leadingCoeff * (Y.leadingCoeff * N0) := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl hdY, hcY']
    rfl
  have haYdeg : (a * derivative Y).natDegree ≤ dA + (N0 - 1) :=
    natDegree_mul_le.trans (add_le_add le_rfl hdY)
  have hrc : ∀ d, R < d → r.coeff d = 0 := fun d hd ↦
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hr hd)
  by_cases hb : b = 0
  · have := congrArg (fun P : Kc[X] ↦ P.coeff (dA + (N0 - 1))) heq
    simp only [hb, zero_mul, add_zero, haY] at this
    rw [hrc _ (by omega)] at this
    exact mul_ne_zero hlca (mul_ne_zero hlcY hN0c) this
  set dB := b.natDegree with hdB
  have hlcb : b.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hb
  have hbY : (b * Y).coeff (dB + N0) = b.leadingCoeff * Y.leadingCoeff := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl le_rfl, leadingCoeff, leadingCoeff]
  have hbYdeg : (b * Y).natDegree ≤ dB + N0 := natDegree_mul_le
  rcases lt_trichotomy (dB + 1) dA with h1 | h1 | h1
  · -- `a Y′` dominates
    have := congrArg (fun P : Kc[X] ↦ P.coeff (dA + (N0 - 1))) heq
    have hz : (b * Y).coeff (dA + (N0 - 1)) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hbYdeg (by omega))
    simp only [coeff_add, haY, hz, add_zero] at this
    rw [hrc _ (by omega)] at this
    exact mul_ne_zero hlca (mul_ne_zero hlcY hN0c) this
  · -- balanced
    have := congrArg (fun P : Kc[X] ↦ P.coeff (dB + N0)) heq
    rw [show dB + N0 = dA + (N0 - 1) by omega] at this
    simp only [coeff_add, haY] at this
    rw [show dA + (N0 - 1) = dB + N0 by omega, hbY, hrc _ (by omega)] at this
    have hN : (N0 : Kc) * a.leadingCoeff + b.leadingCoeff = 0 := by
      have h2 : Y.leadingCoeff * ((N0 : Kc) * a.leadingCoeff + b.leadingCoeff) = 0 := by
        linear_combination this
      exact (mul_eq_zero.mp h2).resolve_left hlcY
    have := hq hb h1 N0 hN
    omega
  · -- `b Y` dominates
    have := congrArg (fun P : Kc[X] ↦ P.coeff (dB + N0)) heq
    have hz : (a * derivative Y).coeff (dB + N0) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt haYdeg (by omega))
    simp only [coeff_add, hbY, hz, zero_add] at this
    rw [hrc _ (by omega)] at this
    exact mul_ne_zero hlcb hlcY this

end DegBound

/-- **Coordinates from the null-space basis**: a relation with constant coefficients is a
constant combination of the basis vectors, coordinatewise. -/
lemma nullBasis_coeffs {Kc : Type*} [Field Kc] [CharZero Kc] (cols : List (CPoly ℚ))
    (cv : List Kc) (hl : cv.length = cols.length) (h0 : lcombS (algebraMap ℚ Kc) cv cols = 0) :
    ∃ β : List Kc, ∀ j, cv.getD j 0 = ∑ k ∈ Finset.range (nullBasis cols).length,
      β.getD k 0 * algebraMap ℚ Kc (((nullBasis cols).getD k []).getD j 0) := by
  obtain ⟨β, hβ, heq⟩ := nullBasis_complete (algebraMap ℚ Kc) cols cv hl h0
  refine ⟨β, fun j ↦ ?_⟩
  have hsnd : (nsItems cols).map Prod.snd = (List.range cv.length).map unitL := by
    simp only [nsItems, List.map_map]
    rw [← hl]
    rfl
  rw [hsnd, NestTower.lcombS_range_unitL] at heq
  have := congrArg (fun P : Kc[X] ↦ P.coeff j) heq
  simp only [coeff_toPoly] at this
  rw [this, NestTower.coeff_lcombS, NestTower.zipWith_sum_range _ 0 [] _ _ hβ, hβ]

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

/-- A polynomial over `ℚ` in `F 0`. -/
noncomputable def σ0 (p : CPoly ℚ) : T.F 0 := T.phi0 ((CPoly.toPoly p).map (algebraMap ℚ Kc))

lemma σ0_mul (a b : CPoly ℚ) : T.σ0 (CPoly.mul a b) = T.σ0 a * T.σ0 b := by
  simp [σ0]

lemma σ0_one : T.σ0 [1] = 1 := by simp [σ0, CPoly.toPoly]

lemma sem0 (h0 : T.Tr 0) (q : GFrac ℚ) : (T.MP 0 h0).sem q = T.σ0 q.1 / T.σ0 q.2 :=
  T.model0_sem_eq q

lemma σ0_eq_zero_iff (p : CPoly ℚ) : T.σ0 p = 0 ↔ CPoly.isZero p = true := by
  rw [CPoly.isZero_iff, σ0, map_eq_zero_iff _ T.phi0_injective,
    Polynomial.map_eq_zero_iff (algebraMap ℚ Kc).injective]

lemma sem0_cleanQ (h0 : T.Tr 0) (w : GFrac ℚ) :
    (T.MP 0 h0).sem (cleanQ w) = (T.MP 0 h0).sem w := by
  unfold cleanQ
  split_ifs with hz
  · rw [T.sem0, T.sem0, (T.σ0_eq_zero_iff w.2).mpr hz]
    simp [σ0, CPoly.toPoly]
  · rfl

lemma σ0_cleanQ_ne (w : GFrac ℚ) : T.σ0 (cleanQ w).2 ≠ 0 := by
  unfold cleanQ
  split_ifs with hz
  · rw [T.σ0_one]; exact one_ne_zero
  · rw [Ne, T.σ0_eq_zero_iff]; exact hz

lemma deriv_σ0 (p : CPoly ℚ) :
    (T.σ0 p)′ = T.phi0 (derivative ((CPoly.toPoly p).map (algebraMap ℚ Kc))) := by
  rw [σ0, T.deriv_phi0, implicitDeriv_one_of_trivial T.hC]

/-- **Soundness of `prde0`.** -/
theorem prde0_sound (h0 : T.Tr 0) (hc : GFrac ℚ) (W : List (GFrac ℚ)) :
    ∀ r ∈ prde0 hc W, ((T.MP 0 h0).sem r.2)′ + ((T.MP 0 h0).sem hc)′ * (T.MP 0 h0).sem r.2 =
      sQ (T.MP 0 h0) r.1 W := by
  intro r hr
  set M := T.MP 0 h0 with hM
  set hv := M.sem hc with hhv
  simp only [prde0] at hr
  split_ifs at hr with hDz
  · simp at hr
  set Wc := W.map cleanQ with hWc
  set e := Wc.foldr (fun w acc ↦ lcmQ w.2 acc) [1] with he
  set D := (CPoly.egcd e (CPoly.deriv e)).1 with hD
  have hσD : T.σ0 D ≠ 0 := by rw [Ne, T.σ0_eq_zero_iff]; simpa using hDz
  simp only [prde0B] at hr
  set O := ops₁g ℚ with hO
  set Dc : GFrac ℚ := (D, [1]) with hDc
  set F := cleanQ (O.add (O.deriv (cleanQ hc)) (O.neg (O.mul (O.deriv Dc) (O.inv Dc)))) with hF
  set Rs := Wc.map fun w ↦ cleanQ (O.mul Dc w) with hRs
  set P := prodD CPoly.mul [1] Rs with hP
  set A := CPoly.mul F.2 P with hA
  set B := CPoly.mul F.1 P with hB
  set Cs := (cross CPoly.mul [1] Rs).map (CPoly.mul F.2) with hCs
  set ys : List (CPoly ℚ) := (List.range (degBoundU A B ((Cs.map cdeg).foldr max 0) + 1)).map
    (colY A B) with hys
  obtain ⟨u, hu, hru⟩ := List.mem_map.mp hr
  have hlen : Cs.length = W.length := by simp [hCs, length_cross, hRs, hWc]
  have hysD : ∀ k < ys.length, ys.getD k [] = colY A B k := by
    intro k hk
    rw [hys] at hk ⊢
    exact NestTower.getD_range_map _ _ (by simpa using hk)
  have hrel := prde0B_rel Cs ys A B hysD u (nullBasis_sound _ u hu)
  rw [hlen] at hrel
  -- the relation, in `F 0`
  set Yq := ∑ k ∈ Finset.range ys.length, Polynomial.C (u.getD (W.length + k) 0) * X ^ k with hYq
  have hYlist : CPoly.toPoly ((List.range ys.length).map fun k ↦ u.getD (W.length + k) 0) = Yq :=
    toPoly_range_map _ _
  have hσ := congrArg (fun p : ℚ[X] ↦ T.phi0 (p.map (algebraMap ℚ Kc))) hrel
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_C,
    derivative_map, map_add, map_mul, map_sum] at hσ
  -- the facts about the codes
  have hadd : ∀ a b, M.sem (O.add a b) = M.sem a + M.sem b := M.sem_add
  have hneg : ∀ a, M.sem (O.neg a) = -M.sem a := M.sem_neg
  have hmul : ∀ a b, M.sem (O.mul a b) = M.sem a * M.sem b := M.sem_mul
  have hinv : ∀ a, M.sem (O.inv a) = (M.sem a)⁻¹ := M.sem_inv
  have hder : ∀ a, M.sem (O.deriv a) = (M.sem a)′ := M.sem_deriv
  have hDcv : M.sem Dc = T.σ0 D := by rw [T.sem0 h0 Dc, hDc]; simp [T.σ0_one]
  have hsF : M.sem F = (M.sem hc)′ - (T.σ0 D)′ / T.σ0 D := by
    rw [hF, T.sem0_cleanQ, hadd, hder, T.sem0_cleanQ, hneg, hmul, hder, hinv, hDcv]
    ring
  have hF2 : T.σ0 F.2 ≠ 0 := T.σ0_cleanQ_ne _
  have hRs2 : ∀ p ∈ Rs, T.σ0 p.2 ≠ 0 := fun p hp ↦ by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
    exact T.σ0_cleanQ_ne _
  have hsum := sum_cross CPoly.mul [1] T.σ0 T.σ0_mul T.σ0_one Rs
    ((List.range W.length).map fun i ↦ (algebraMap ℚ (T.F 0) (u.getD i 0))) hRs2
  have hP0 : T.σ0 P ≠ 0 := σ_prodD_ne_zero CPoly.mul [1] T.σ0 T.σ0_mul T.σ0_one Rs hRs2
  have hlW : Wc.length = W.length := by simp [hWc]
  have hlR : Rs.length = W.length := by simp [hRs, hWc]
  have hq : ∀ q : ℚ, T.phi0 (C (algebraMap ℚ Kc q)) = (q : T.F 0) := fun q ↦ by
    rw [T.phi0_C, ← map_ratCast (algebraMap Kc (T.F 0)), ← map_ratCast (algebraMap ℚ Kc)]
    rfl
  have hqa : ∀ q : ℚ, algebraMap ℚ (T.F 0) q = (q : T.F 0) := fun q ↦ by simp
  set yv := T.phi0 (Yq.map (algebraMap ℚ Kc)) with hyv
  have hyv' : (T.phi0 (Yq.map (algebraMap ℚ Kc)))′ =
      T.phi0 ((derivative Yq).map (algebraMap ℚ Kc)) := by
    rw [T.deriv_phi0, implicitDeriv_one_of_trivial T.hC, derivative_map]
  -- the right-hand side, cleared of denominators
  have hRsv : ∀ i < W.length, T.σ0 (Rs.getD i ([], [])).1 / T.σ0 (Rs.getD i ([], [])).2 =
      T.σ0 D * M.sem (W.getD i (opsM ks 0).zero) := fun i hi ↦ by
    have hRi : Rs.getD i ([], []) = cleanQ (O.mul Dc (cleanQ (W.getD i (opsM ks 0).zero))) := by
      simp only [List.getD_eq_getElem?_getD, hRs, hWc, List.getElem?_map,
        List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
      rw [show W.getD i (opsM ks 0).zero = W[i] from List.getD_eq_getElem _ _ hi]
    rw [hRi, ← T.sem0 h0, T.sem0_cleanQ, hmul, hDcv, T.sem0_cleanQ]
  have hRHS : ∑ i ∈ Finset.range W.length, T.phi0 (C (algebraMap ℚ Kc (u.getD i 0))) *
      T.phi0 ((CPoly.toPoly (Cs.getD i [])).map (algebraMap ℚ Kc)) =
      T.σ0 F.2 * T.σ0 P * (T.σ0 D * ∑ i ∈ Finset.range W.length, ((u.getD i 0 : ℚ) : T.F 0) *
        M.sem (W.getD i (opsM ks 0).zero)) := by
    have e1 : ∀ i ∈ Finset.range W.length, T.phi0 (C (algebraMap ℚ Kc (u.getD i 0))) *
        T.phi0 ((CPoly.toPoly (Cs.getD i [])).map (algebraMap ℚ Kc)) =
        T.σ0 F.2 * (((u.getD i 0 : ℚ) : T.F 0) * T.σ0 ((cross CPoly.mul [1] Rs).getD i [])) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [hq, hCs, NestTower.getD_map' _ _ [] [] (by rw [length_cross, hlR]; exact hi')]
      change _ * T.σ0 (CPoly.mul F.2 _) = _
      rw [T.σ0_mul]
      ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    have e2 : ∑ i ∈ Finset.range W.length, ((u.getD i 0 : ℚ) : T.F 0) *
        T.σ0 ((cross CPoly.mul [1] Rs).getD i []) =
        (List.zipWith (fun c y ↦ c * T.σ0 y) ((List.range W.length).map fun i ↦
          algebraMap ℚ (T.F 0) (u.getD i 0)) (cross CPoly.mul [1] Rs)).sum := by
      rw [NestTower.zipWith_sum_range _ 0 [] _ _ (by rw [length_cross, hlR]; simp)]
      rw [List.length_map, List.length_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi), hqa]
    have e3 : (List.zipWith (fun c p ↦ c * (T.σ0 p.1 / T.σ0 p.2)) ((List.range W.length).map
        fun i ↦ algebraMap ℚ (T.F 0) (u.getD i 0)) Rs).sum =
        T.σ0 D * ∑ i ∈ Finset.range W.length, ((u.getD i 0 : ℚ) : T.F 0) *
          M.sem (W.getD i (opsM ks 0).zero) := by
      rw [NestTower.zipWith_sum_range _ 0 ([], []) _ _ (by rw [hlR]; simp), Finset.mul_sum]
      rw [List.length_map, List.length_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi), hqa,
        hRsv i (Finset.mem_range.mp hi)]
      ring
    rw [e2, hsum, e3]
    ring
  rw [hRHS] at hσ
  have hA' : T.phi0 ((CPoly.toPoly A).map (algebraMap ℚ Kc)) = T.σ0 F.2 * T.σ0 P := T.σ0_mul _ _
  have hB' : T.phi0 ((CPoly.toPoly B).map (algebraMap ℚ Kc)) = T.σ0 F.1 * T.σ0 P := T.σ0_mul _ _
  rw [hA', hB', ← hyv'] at hσ
  have hF12 : T.σ0 F.1 / T.σ0 F.2 = M.sem F := (T.sem0 h0 F).symm
  -- the equation for `yv`
  have hyeq : yv′ + ((M.sem hc)′ - (T.σ0 D)′ / T.σ0 D) * yv =
      T.σ0 D * ∑ i ∈ Finset.range W.length, ((u.getD i 0 : ℚ) : T.F 0) *
        M.sem (W.getD i (opsM ks 0).zero) := by
    rw [← hsF, ← hF12]
    have hne : T.σ0 F.2 * T.σ0 P ≠ 0 := mul_ne_zero hF2 hP0
    calc yv′ + T.σ0 F.1 / T.σ0 F.2 * yv
        = (T.σ0 F.2 * T.σ0 P * yv′ + T.σ0 F.1 * T.σ0 P * yv) / (T.σ0 F.2 * T.σ0 P) := by
          field_simp
      _ = _ := by rw [hσ]; field_simp
  -- the solution `Y / D`
  have hL : T.σ0 ((List.range ys.length).map fun k ↦ u.getD (W.length + k) 0) = yv := by
    rw [σ0, hYlist]
  have hsol : M.sem r.2 = yv / T.σ0 D := by
    rw [← hru]
    refine (T.sem0 h0 _).trans ?_
    dsimp only
    rw [hlW]
    exact congrArg (· / T.σ0 D) hL
  have hr1 : r.1 = (List.range Wc.length).map fun x ↦ u.getD x 0 := by rw [← hru]
  rw [hsol]
  unfold sQ
  rw [hr1]
  have e4 : ∀ i ∈ Finset.range W.length,
      ((((List.range Wc.length).map fun x ↦ u.getD x 0).getD i 0 : ℚ) : T.F 0) *
        M.sem (W.getD i (opsM ks 0).zero) =
      ((u.getD i 0 : ℚ) : T.F 0) * M.sem (W.getD i (opsM ks 0).zero) := fun i hi ↦ by
    rw [NestTower.getD_range_map _ _ (by rw [hlW]; exact Finset.mem_range.mp hi)]
  refine Eq.trans ?_ (Finset.sum_congr rfl e4).symm
  have key : yv′ = T.σ0 D * ∑ i ∈ Finset.range W.length, ((u.getD i 0 : ℚ) : T.F 0) *
      M.sem (W.getD i (opsM ks 0).zero) - ((M.sem hc)′ - (T.σ0 D)′ / T.σ0 D) * yv := by
    linear_combination hyeq
  rw [Derivation.leibniz_div, key]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- The model of `ℚ(x)`, typed with `GFrac ℚ`. -/
noncomputable abbrev M0 (h0 : T.Tr 0) : CField (GFrac ℚ) (T.F 0) (ops₁g ℚ) := T.MP 0 h0

lemma sem0' (h0 : T.Tr 0) (q : GFrac ℚ) : (T.M0 h0).sem q = T.σ0 q.1 / T.σ0 q.2 := T.sem0 h0 q

lemma sem0_cleanQ' (h0 : T.Tr 0) (w : GFrac ℚ) : (T.M0 h0).sem (cleanQ w) = (T.M0 h0).sem w :=
  T.sem0_cleanQ h0 w

/-- **The identity behind `prde0`**: the polynomial equation is the Risch equation for
`Y / D` times the non-zero factor `F₂ P D`. -/
lemma prde0_identity (h0 : T.Tr 0) (hc : GFrac ℚ) (Wc : List (GFrac ℚ))
    (hWc : ∀ w ∈ Wc, CPoly.toPoly w.2 ≠ 0) (D : CPoly ℚ) (hσD : T.σ0 D ≠ 0) (Y : Kc[X])
    (c : ℕ → Kc) :
    T.phi0 ((CPoly.toPoly (p0A hc Wc D)).map (algebraMap ℚ Kc) * derivative Y +
      (CPoly.toPoly (p0B hc Wc D)).map (algebraMap ℚ Kc) * Y -
      ∑ i ∈ Finset.range Wc.length, C (c i) *
        (CPoly.toPoly ((p0Cs hc Wc D).getD i [])).map (algebraMap ℚ Kc)) =
    T.σ0 (p0F hc D).2 * T.σ0 (p0P Wc D) * T.σ0 D *
      ((T.phi0 Y / T.σ0 D)′ + ((T.M0 h0).sem hc)′ * (T.phi0 Y / T.σ0 D) -
        ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F 0) (c i) *
          (T.M0 h0).sem (Wc.getD i (ops₁g ℚ).zero)) := by
  set M := T.M0 h0 with hM
  set hv := M.sem hc with hhv
  have hadd : ∀ a b, M.sem ((ops₁g ℚ).add a b) = M.sem a + M.sem b := M.sem_add
  have hneg : ∀ a, M.sem ((ops₁g ℚ).neg a) = -M.sem a := M.sem_neg
  have hmul : ∀ a b, M.sem ((ops₁g ℚ).mul a b) = M.sem a * M.sem b := M.sem_mul
  have hinv : ∀ a, M.sem ((ops₁g ℚ).inv a) = (M.sem a)⁻¹ := M.sem_inv
  have hder : ∀ a, M.sem ((ops₁g ℚ).deriv a) = (M.sem a)′ := M.sem_deriv
  have hDcv : M.sem (p0Dc D) = T.σ0 D := by rw [T.sem0' h0, p0Dc]; simp [T.σ0_one]
  have hsF : T.σ0 (p0F hc D).1 / T.σ0 (p0F hc D).2 = hv′ - (T.σ0 D)′ / T.σ0 D := by
    rw [← T.sem0' h0, p0F, T.sem0_cleanQ' h0, hadd, hder, T.sem0_cleanQ' h0, hneg, hmul, hder, hinv, hDcv]
    ring
  have hF2 : T.σ0 (p0F hc D).2 ≠ 0 := T.σ0_cleanQ_ne _
  have hRs2 : ∀ p ∈ p0Rs Wc D, T.σ0 p.2 ≠ 0 := fun p hp ↦ by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
    exact T.σ0_cleanQ_ne _
  have hlR : (p0Rs Wc D).length = Wc.length := by simp [p0Rs]
  have hP0 : T.σ0 (p0P Wc D) ≠ 0 :=
    σ_prodD_ne_zero CPoly.mul [1] T.σ0 T.σ0_mul T.σ0_one _ hRs2
  have hsum := sum_cross CPoly.mul [1] T.σ0 T.σ0_mul T.σ0_one (p0Rs Wc D)
    ((List.range Wc.length).map fun i ↦ algebraMap Kc (T.F 0) (c i)) hRs2
  have hRsv : ∀ i < Wc.length, T.σ0 ((p0Rs Wc D).getD i ([], [])).1 /
      T.σ0 ((p0Rs Wc D).getD i ([], [])).2 = T.σ0 D * M.sem (Wc.getD i (ops₁g ℚ).zero) := by
    intro i hi
    have hRi : (p0Rs Wc D).getD i ([], []) = cleanQ ((ops₁g ℚ).mul (p0Dc D) (Wc.getD i (ops₁g ℚ).zero)) := by
      simp only [List.getD_eq_getElem?_getD, p0Rs, List.getElem?_map,
        List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
    rw [hRi, ← T.sem0' h0, T.sem0_cleanQ' h0, hmul, hDcv]
  -- the right-hand side
  have hRHS : ∑ i ∈ Finset.range Wc.length, T.phi0 (C (c i)) *
      T.phi0 ((CPoly.toPoly ((p0Cs hc Wc D).getD i [])).map (algebraMap ℚ Kc)) =
      T.σ0 (p0F hc D).2 * T.σ0 (p0P Wc D) * (T.σ0 D * ∑ i ∈ Finset.range Wc.length,
        algebraMap Kc (T.F 0) (c i) * M.sem (Wc.getD i (ops₁g ℚ).zero)) := by
    have e1 : ∀ i ∈ Finset.range Wc.length, T.phi0 (C (c i)) *
        T.phi0 ((CPoly.toPoly ((p0Cs hc Wc D).getD i [])).map (algebraMap ℚ Kc)) =
        T.σ0 (p0F hc D).2 * (algebraMap Kc (T.F 0) (c i) *
          T.σ0 ((cross CPoly.mul [1] (p0Rs Wc D)).getD i [])) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [T.phi0_C, p0Cs, NestTower.getD_map' _ _ [] [] (by rw [length_cross, hlR]; exact hi')]
      change _ * T.σ0 (CPoly.mul (p0F hc D).2 _) = _
      rw [T.σ0_mul]
      ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    have e2 : ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F 0) (c i) *
        T.σ0 ((cross CPoly.mul [1] (p0Rs Wc D)).getD i []) =
        (List.zipWith (fun c y ↦ c * T.σ0 y) ((List.range Wc.length).map fun i ↦
          algebraMap Kc (T.F 0) (c i)) (cross CPoly.mul [1] (p0Rs Wc D))).sum := by
      rw [NestTower.zipWith_sum_range _ 0 [] _ _ (by rw [length_cross, hlR]; simp)]
      rw [List.length_map, List.length_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi)]
    have e3 : (List.zipWith (fun c p ↦ c * (T.σ0 p.1 / T.σ0 p.2)) ((List.range Wc.length).map
        fun i ↦ algebraMap Kc (T.F 0) (c i)) (p0Rs Wc D)).sum =
        T.σ0 D * ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F 0) (c i) *
          M.sem (Wc.getD i (ops₁g ℚ).zero) := by
      rw [NestTower.zipWith_sum_range _ 0 ([], []) _ _ (by rw [hlR]; simp), Finset.mul_sum]
      rw [List.length_map, List.length_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi), hRsv i (Finset.mem_range.mp hi)]
      ring
    rw [e2, hsum, e3]
    change T.σ0 (p0F hc D).2 * (_ * T.σ0 (p0P Wc D)) = _
    ring
  have hA' : T.phi0 ((CPoly.toPoly (p0A hc Wc D)).map (algebraMap ℚ Kc)) =
      T.σ0 (p0F hc D).2 * T.σ0 (p0P Wc D) := T.σ0_mul _ _
  have hB' : T.phi0 ((CPoly.toPoly (p0B hc Wc D)).map (algebraMap ℚ Kc)) =
      T.σ0 (p0F hc D).1 * T.σ0 (p0P Wc D) := T.σ0_mul _ _
  have hY' : T.phi0 (derivative Y) = (T.phi0 Y)′ := by
    rw [T.deriv_phi0, implicitDeriv_one_of_trivial T.hC]
  simp only [map_sub, map_add, map_mul, map_sum]
  rw [hA', hB', hY', hRHS, Derivation.leibniz_div]
  simp only [smul_eq_mul]
  have hF1 : T.σ0 (p0F hc D).1 = (hv′ - (T.σ0 D)′ / T.σ0 D) * T.σ0 (p0F hc D).2 := by
    rw [← hsF]; field_simp
  rw [hF1]
  field_simp
  ring

lemma σ_prodD_ne_zero' (l : List (GFrac ℚ)) (h : ∀ p ∈ l, T.σ0 p.2 ≠ 0) :
    T.σ0 (prodD CPoly.mul [1] l) ≠ 0 :=
  σ_prodD_ne_zero CPoly.mul [1] T.σ0 T.σ0_mul T.σ0_one l h

lemma phi0_eq_algebraMap (P : Kc[X]) : T.phi0 P = algebraMap Kc[X] (T.F 0) P := rfl

set_option maxHeartbeats 1600000 in
/-- **Completeness of `prde0`**: every solution with constant coefficients is a constant
combination of the returned pairs. -/
theorem prde0_complete (h0 : T.Tr 0) (hc : GFrac ℚ) (W : List (GFrac ℚ)) (c : List Kc)
    (hcl : ∀ i, W.length ≤ i → c.getD i 0 = 0) (y : T.F 0)
    (hy : y′ + ((T.M0 h0).sem hc)′ * y = sC (algebraMap Kc (T.F 0)) (T.M0 h0) c W) :
    ∃ β : List Kc,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range (prde0 hc W).length,
        β.getD k 0 * algebraMap ℚ Kc (((prde0 hc W).getD k ([], (ops₁g ℚ).zero)).1.getD i 0)) ∧
      y = ∑ k ∈ Finset.range (prde0 hc W).length, algebraMap Kc (T.F 0) (β.getD k 0) *
        (T.M0 h0).sem ((prde0 hc W).getD k ([], (ops₁g ℚ).zero)).2 := by
  classical
  set M := T.M0 h0 with hM
  set hv := M.sem hc with hhv
  set ι := algebraMap Kc (T.F 0) with hι
  set aq := algebraMap ℚ Kc with haq
  have hsem : ∀ q : GFrac ℚ, M.sem q = T.σ0 q.1 / T.σ0 q.2 := T.sem0 h0
  have hsemc : ∀ q : GFrac ℚ, M.sem (cleanQ q) = M.sem q := T.sem0_cleanQ h0
  obtain ⟨Wc, hWc⟩ : ∃ Wc, Wc = W.map cleanQ := ⟨_, rfl⟩
  have hWc0 : ∀ w ∈ Wc, CPoly.toPoly w.2 ≠ 0 := fun w hw ↦ by
    rw [hWc] at hw
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hw
    exact cleanQ_den_ne' v
  have hlW : Wc.length = W.length := by simp [hWc]
  obtain ⟨e, he⟩ : ∃ e, e = Wc.foldr (fun w acc ↦ lcmQ w.2 acc) [1] := ⟨_, rfl⟩
  obtain ⟨hediv, he0⟩ := lcm_fold_spec Wc hWc0
  rw [← he] at hediv he0
  obtain ⟨D, hD⟩ : ∃ D, D = (CPoly.egcd e (CPoly.deriv e)).1 := ⟨_, rfl⟩
  have hDe : CPoly.toPoly D ∣ CPoly.toPoly e := hD ▸ (CPoly.egcd_dvd e (CPoly.deriv e)).1
  have hD0 : CPoly.toPoly D ≠ 0 := fun h ↦ he0 (zero_dvd_iff.mp (h ▸ hDe))
  have hDz : CPoly.isZero D = false := by
    rw [Bool.eq_false_iff, Ne, CPoly.isZero_iff]; exact hD0
  have hσD : T.σ0 D ≠ 0 := by rw [Ne, T.σ0_eq_zero_iff, hDz]; exact Bool.false_ne_true
  have hout : prde0 hc W = prde0B hc Wc D := by
    simp only [prde0, ← hWc, ← he, ← hD, hDz, Bool.false_eq_true, if_false]
  rw [hout]
  -- the Kc-polynomials
  obtain ⟨ek, hek⟩ : ∃ ek, ek = (CPoly.toPoly e).map aq := ⟨_, rfl⟩
  obtain ⟨Dk, hDk⟩ : ∃ Dk, Dk = (CPoly.toPoly D).map aq := ⟨_, rfl⟩
  have hek0 : ek ≠ 0 := by rw [hek]; exact (Polynomial.map_ne_zero_iff aq.injective).mpr he0
  have hbezK : Dk = (CPoly.toPoly (CPoly.egcd e (CPoly.deriv e)).2.1).map aq * ek +
      (CPoly.toPoly (CPoly.egcd e (CPoly.deriv e)).2.2).map aq * derivative ek := by
    have := congrArg (Polynomial.map aq) (CPoly.egcd_spec e (CPoly.deriv e))
    simp only [Polynomial.map_add, Polynomial.map_mul, CPoly.toPoly_deriv] at this
    rw [hDk, hD, ← this, hek, derivative_map]
  letI : Differential Kc[X] := polynomialOfDeriv 1
  haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
  have hD' : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
  obtain ⟨g, hg⟩ : ∃ g, g = sC ι M c W := ⟨_, rfl⟩
  -- `g ek` has no pole
  have hgreg : ∀ (p : Kc[X]) (hp : Irreducible p),
      g * algebraMap Kc[X] (T.F 0) ek ∈ regularAt (T.F 0) p hp.prime := by
    intro p hp
    rw [hg]
    unfold sC
    rw [Finset.sum_mul]
    refine Subring.sum_mem _ fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    have hwi : W.getD i (ops₁g ℚ).zero ∈ W := by
      rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem _
    have hcw : cleanQ (W.getD i (ops₁g ℚ).zero) ∈ Wc := by
      rw [hWc]; exact List.mem_map.mpr ⟨_, hwi, rfl⟩
    obtain ⟨q, hq⟩ := hediv _ hcw
    rw [mul_assoc, ← hsemc, hsem]
    refine mul_mem ?_ ?_
    · rw [hι, ← T.phi0_C, T.phi0_eq_algebraMap]
      exact algebraMap_mem_regularAt _ _
    · have hden : T.σ0 (cleanQ (W.getD i (ops₁g ℚ).zero)).2 ≠ 0 := T.σ0_cleanQ_ne _
      have : T.σ0 (cleanQ (W.getD i (ops₁g ℚ).zero)).1 /
          T.σ0 (cleanQ (W.getD i (ops₁g ℚ).zero)).2 * algebraMap Kc[X] (T.F 0) ek =
          algebraMap Kc[X] (T.F 0) ((CPoly.toPoly (cleanQ (W.getD i (ops₁g ℚ).zero)).1).map aq *
            q.map aq) := by
        rw [hek, hq, Polynomial.map_mul, map_mul, map_mul, ← T.phi0_eq_algebraMap,
          ← T.phi0_eq_algebraMap, ← T.phi0_eq_algebraMap]
        change T.σ0 _ / T.σ0 _ * (T.σ0 _ * T.phi0 _) = T.σ0 _ * T.phi0 _
        field_simp
      rw [this]
      exact algebraMap_mem_regularAt _ _
  -- the pole bound at every prime
  have hreg : ∀ (p : Kc[X]) (_ : p.Monic) (hp : Irreducible p),
      y * algebraMap Kc[X] (T.F 0) Dk ∈ regularAt (T.F 0) p hp.prime := by
    intro p _ hp
    have hnorm : ¬p ∣ p′ := fun hdvd ↦ by
      rw [hD'] at hdvd
      have hpos : p.natDegree ≠ 0 := hp.natDegree_pos.ne'
      have hne : derivative p ≠ 0 := fun h0' ↦ hpos (derivative_eq_zero.mp h0')
      exact absurd (natDegree_derivative_lt hpos) (not_lt.mpr (natDegree_le_of_dvd hdvd hne))
    obtain ⟨j, e1, he1, hej⟩ := exists_pow_mul_not_dvd hp.prime hek0
    have hunit : IsUnitAt (T.F 0) p (algebraMap Kc[X] (T.F 0) e1) :=
      ⟨e1, 1, he1, hp.prime.not_dvd_one, by simp⟩
    have hgj : g * algebraMap Kc[X] (T.F 0) p ^ j ∈ regularAt (T.F 0) p hp.prime := by
      have h1 := mul_mem (hgreg p hp) (hunit.inv_mem_regularAt hp.prime)
      have hne : algebraMap Kc[X] (T.F 0) e1 ≠ 0 := map_ne_zero_of_not_dvd hp.prime he1
      rw [hej, map_mul, map_pow] at h1
      rwa [mul_assoc, mul_assoc, mul_inv_cancel₀ hne, mul_one] at h1
    have hrde : y′ + hv′ * y = g := by rw [hg]; exact hy
    cases j with
    | zero =>
      have := rde_pole_bound hp.prime hnorm (not_dvd_natCast_polynomial hp.prime) hv y g 0
        (by rw [zero_add, pow_one]; simpa using mul_mem hgj (algebraMap_mem_regularAt _ p)) hrde
      rw [pow_zero, mul_one] at this
      exact mul_mem this (algebraMap_mem_regularAt _ _)
    | succ E =>
      have hyE := rde_pole_bound hp.prime hnorm (not_dvd_natCast_polynomial hp.prime) hv y g E hgj
        hrde
      have hpe : p ^ E ∣ ek := ⟨p * e1, by rw [hej]; ring⟩
      have hpe' : p ^ E ∣ derivative ek := by
        rw [hej, derivative_mul, derivative_pow]
        exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by
          rw [Nat.add_sub_cancel]; exact dvd_mul_left _ _) _) _)
          (dvd_mul_of_dvd_left (pow_dvd_pow p (Nat.le_succ E)) _)
      have hpD : p ^ E ∣ Dk := by
        rw [hbezK]
        exact dvd_add (dvd_mul_of_dvd_right hpe _) (dvd_mul_of_dvd_right hpe' _)
      obtain ⟨q, hq⟩ := hpD
      rw [hq, map_mul, map_pow, ← mul_assoc]
      exact mul_mem hyE (algebraMap_mem_regularAt _ _)
  obtain ⟨Yv, hYv⟩ := exists_polynomial_of_regularAt (y * algebraMap Kc[X] (T.F 0) Dk) hreg
  have hσDk : T.σ0 D = algebraMap Kc[X] (T.F 0) Dk := by rw [σ0, hDk]; rfl
  have hyY : y = T.phi0 Yv / T.σ0 D := by
    have hDk0 : algebraMap Kc[X] (T.F 0) Dk ≠ 0 := hσDk ▸ hσD
    rw [T.phi0_eq_algebraMap, ← hYv, hσDk]
    field_simp
  -- the polynomial equation
  set A := p0A hc Wc D with hA
  set B := p0B hc Wc D with hB
  set Cs := p0Cs hc Wc D with hCs
  set a := (CPoly.toPoly A).map aq with ha
  set b := (CPoly.toPoly B).map aq with hb
  set r := ∑ i ∈ Finset.range Wc.length, C (c.getD i 0) * (CPoly.toPoly (Cs.getD i [])).map aq
    with hr
  have hlCs : Cs.length = Wc.length := by simp [hCs, p0Cs, length_cross, p0Rs]
  have hpoly : a * derivative Yv + b * Yv = r := by
    have hid := T.prde0_identity h0 hc Wc hWc0 D hσD Yv (fun i ↦ c.getD i 0)
    have hsum0 : ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F 0) (c.getD i 0) *
        M.sem (Wc.getD i (ops₁g ℚ).zero) = g := by
      rw [hg, hlW]
      unfold sC
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' := Finset.mem_range.mp hi
      congr 1
      rw [hWc, List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, hsemc,
        List.getD_eq_getElem _ _ hi']
    rw [hsum0, ← hyY] at hid
    have hz : y′ + hv′ * y - g = 0 := by rw [hg]; rw [hy]; ring
    rw [hz, mul_zero] at hid
    have := T.phi0_injective (hid.trans (map_zero _).symm)
    rw [hlCs.symm] at this
    rw [hr, ← hlCs]
    linear_combination this
  -- the degree bound
  set R := (Cs.map cdeg).foldr max 0 with hR
  have hcdeg : ∀ p : CPoly ℚ, (CPoly.toPoly p).natDegree ≤ cdeg p := fun p ↦ by
    by_cases h : CPoly.trim p = []
    · rw [(CPoly.trim_eq_nil_iff p).mp h]; simp
    · rw [(natDegree_toPoly_of_trim_ne_nil h).1]; rfl
  have hrdeg : r.natDegree ≤ R := by
    rw [hr]
    refine (natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_map]
    have hi' := Finset.mem_range.mp hi
    refine (hcdeg _).trans (le_foldr_max _ _ (List.mem_map.mpr ⟨_, ?_, rfl⟩))
    rw [List.getD_eq_getElem _ _ (by rw [hlCs]; exact hi')]
    exact List.getElem_mem _
  have hA0 : CPoly.toPoly A ≠ 0 := by
    rw [hA, p0A, CPoly.toPoly_mul]
    refine mul_ne_zero (cleanQ_den_ne' _) ?_
    intro h0
    have := T.σ_prodD_ne_zero' (p0Rs Wc D) (fun p hp ↦ by
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
      exact T.σ0_cleanQ_ne _)
    exact this (by rw [σ0, ← p0P, h0]; simp)
  have hlead : ∀ p : CPoly ℚ, CPoly.toPoly p ≠ 0 →
      ((CPoly.toPoly p).map aq).leadingCoeff = aq (clead p) ∧
        ((CPoly.toPoly p).map aq).natDegree = cdeg p := fun p hp ↦ by
    refine ⟨by rw [leadingCoeff_map, CPoly.leadingCoeff_toPoly hp]; rfl, ?_⟩
    rw [natDegree_map]
    have hne : CPoly.trim p ≠ [] := fun h ↦ hp ((CPoly.trim_eq_nil_iff p).mp h)
    rw [(natDegree_toPoly_of_trim_ne_nil hne).1]; rfl
  set N := degBoundU A B R with hN
  have hqq : b ≠ 0 → b.natDegree + 1 = a.natDegree → ∀ N' : ℕ,
      (N' : Kc) * a.leadingCoeff + b.leadingCoeff = 0 →
      N' ≤ (if !CPoly.isZero B && decide (cdeg B + 1 = cdeg A) then
        ((natOfQ (-(clead B / clead A))).getD 0) else 0) := by
    intro hb0 hdb N' hN'
    have hB0 : CPoly.toPoly B ≠ 0 := fun h0 ↦ hb0 (by rw [hb, h0, Polynomial.map_zero])
    obtain ⟨hla, hda⟩ := hlead A hA0
    obtain ⟨hlb, hdb'⟩ := hlead B hB0
    rw [hla, hlb] at hN'
    rw [hda, hdb'] at hdb
    have hq : ((N' : ℚ)) = -(clead B / clead A) := by
      have hca : aq (clead A) ≠ 0 := by
        rw [← hla]
        exact leadingCoeff_ne_zero.mpr ((Polynomial.map_ne_zero_iff aq.injective).mpr hA0)
      have hca' : clead A ≠ 0 := fun h ↦ hca (by rw [h, map_zero])
      apply aq.injective
      rw [map_natCast, map_neg, map_div₀]
      field_simp
      linear_combination hN'
    have hBz : CPoly.isZero B = false := by
      rw [Bool.eq_false_iff, Ne, CPoly.isZero_iff]; exact hB0
    simp only [hBz, Bool.not_false, Bool.true_and, decide_eq_true_eq, hdb, if_true]
    rw [← hq, natOfQ]
    simp
  have hdeg : Yv.natDegree ≤ N :=
    natDegree_le_of_rde0 a b Yv r R _ hrdeg ((Polynomial.map_ne_zero_iff aq.injective).mpr hA0)
      hpoly hqq
  -- the relation over `Kc`
  set ys := (List.range (N + 1)).map (colY A B) with hys
  set cols := Cs.map CPoly.neg ++ ys with hcols
  set n := Wc.length with hn
  have hYsum : Yv = ∑ k ∈ Finset.range (N + 1), C (Yv.coeff k) * X ^ k := by
    ext j
    rw [finset_sum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hj
    · rfl
    · exact coeff_eq_zero_of_natDegree_lt (by simp at hj; omega)
  set cv := (List.range n).map (fun i ↦ c.getD i 0) ++ (List.range (N + 1)).map Yv.coeff with hcv
  have hlcols : cols.length = n + (N + 1) := by simp [hcols, hys, hlCs, hn]
  have hlcv : cv.length = cols.length := by rw [hlcols]; simp [hcv]
  have h0 : lcombS aq cv cols = 0 := by
    rw [lcombS, NestTower.zipWith_sum_range _ 0 [] _ _ hlcv, hlcv, hlcols, Finset.sum_range_add]
    have e1 : ∀ i ∈ Finset.range n, C (cv.getD i 0) * (CPoly.toPoly (cols.getD i [])).map aq =
        -(C (c.getD i 0) * (CPoly.toPoly (Cs.getD i [])).map aq) := fun i hi ↦ by
      have hi' := Finset.mem_range.mp hi
      rw [hcv, List.getD_append _ _ _ _ (by simpa using hi'), NestTower.getD_range_map _ _ hi',
        hcols, List.getD_append _ _ _ _ (by simpa [hlCs] using hi'),
        NestTower.getD_map' _ _ [] [] (by rw [hlCs]; exact hi'), CPoly.toPoly_neg,
        Polynomial.map_neg]
      ring
    have e2 : ∀ k ∈ Finset.range (N + 1), C (cv.getD (n + k) 0) *
        (CPoly.toPoly (cols.getD (n + k) [])).map aq =
        a * derivative (C (Yv.coeff k) * X ^ k) + b * (C (Yv.coeff k) * X ^ k) := fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      rw [hcv, List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range,
        Nat.add_sub_cancel_left, NestTower.getD_range_map _ _ hk', hcols,
        List.getD_append_right _ _ _ _ (by simp [hlCs]), List.length_map, hlCs,
        Nat.add_sub_cancel_left, hys, NestTower.getD_range_map _ _ hk', colY, CPoly.toPoly_add,
        CPoly.toPoly_mul, CPoly.toPoly_mul, CPoly.toPoly_deriv, CPoly.toPoly_monomial]
      simp only [Polynomial.map_add, Polynomial.map_mul, derivative_map, Polynomial.map_C,
        map_one, one_mul, Polynomial.map_pow, map_X, derivative_C_mul, ha, hb]
      rw [← derivative_map, Polynomial.map_pow, map_X]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_neg_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← derivative_sum, ← hYsum,
      hpoly, hr]
    ring
  obtain ⟨β, hβ⟩ := nullBasis_coeffs cols cv hlcv h0
  set NB := nullBasis cols with hNB
  have hout2 : prde0B hc Wc D = NB.map fun u ↦ ((List.range n).map (u.getD · 0),
      (((List.range ys.length).map fun k ↦ u.getD (n + k) 0), D)) := rfl
  rw [hout2]
  have hget : ∀ k < NB.length, (NB.map fun u ↦ ((List.range n).map (u.getD · 0),
      (((List.range ys.length).map fun k ↦ u.getD (n + k) 0), D))).getD k ([], (ops₁g ℚ).zero) =
      ((List.range n).map ((NB.getD k []).getD · 0),
        (((List.range ys.length).map fun j ↦ (NB.getD k []).getD (n + j) 0), D)) :=
    fun k hk ↦ NestTower.getD_map' _ _ [] _ hk
  refine ⟨β, fun i ↦ ?_, ?_⟩
  · rw [List.length_map]
    have e : ∀ k ∈ Finset.range NB.length, β.getD k 0 * aq (((NB.map fun u ↦
        ((List.range n).map (u.getD · 0), (((List.range ys.length).map fun k ↦ u.getD (n + k) 0),
          D))).getD k ([], (ops₁g ℚ).zero)).1.getD i 0) =
        β.getD k 0 * aq (if i < n then (NB.getD k []).getD i 0 else 0) := fun k hk ↦ by
      rw [hget k (Finset.mem_range.mp hk)]
      dsimp only
      split_ifs with hi
      · rw [NestTower.getD_range_map _ _ hi]
      · rw [List.getD_eq_default ((List.range n).map ((NB.getD k []).getD · 0)) 0
          (by rw [List.length_map, List.length_range]; omega)]
    rw [Finset.sum_congr rfl e]
    by_cases hi : i < n
    · simp only [if_pos hi]
      rw [← hβ i, hcv, List.getD_append _ _ _ _ (by simpa using hi), NestTower.getD_range_map _ _ hi]
    · simp only [if_neg hi, map_zero, mul_zero, Finset.sum_const_zero]
      exact hcl i (by rw [← hlW]; omega)
  · rw [List.length_map, hyY]
    have e : ∀ k ∈ Finset.range NB.length, ι (β.getD k 0) * M.sem ((NB.map fun u ↦
        ((List.range n).map (u.getD · 0), (((List.range ys.length).map fun k ↦ u.getD (n + k) 0),
          D))).getD k ([], (ops₁g ℚ).zero)).2 =
        ι (β.getD k 0) * T.phi0 (∑ j ∈ Finset.range (N + 1),
          C (aq ((NB.getD k []).getD (n + j) 0)) * X ^ j) / T.σ0 D := fun k hk ↦ by
      rw [hget k (Finset.mem_range.mp hk), hsem]
      dsimp only
      rw [σ0, toPoly_range_map, hys, List.length_map, List.length_range]
      simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
        map_X]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.sum_div]
    congr 1
    rw [hYsum, map_sum]
    simp only [map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hYj : Yv.coeff j = cv.getD (n + j) 0 := by
      rw [hcv, List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range,
        Nat.add_sub_cancel_left, NestTower.getD_range_map _ _ (Finset.mem_range.mp hj)]
    rw [hYj, hβ, map_mul, T.phi0_C, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [map_mul, T.phi0_C, hι]
    ring

end NestMTower

end Tower.NestM
