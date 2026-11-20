import RischTragerBronstein.Algebraic.EllFunctional

/-!
# An irrational-residue elliptic integral proved non-elementary

`∫ (4x + 4) dx / ((x² − 2) √(x³ + x² + 1))`: the poles `x = ±√2` lie under the points
`P = (√2, 1 + √2)` and `σP = (−√2, 1 − √2)` of `E : y² = x³ + x² + 1` over `ℚ(√2)`, with the
**irrational** residues `√2` and `−√2`. For the `ℚ`-linear functional "coefficient of `√2`",
`ell_torsion_functional` would force `P − σP = (−1/2, −(3/4)√2)` to be torsion; the verified
torsion test over `ℚ(√2)` (`torsionTestK` at `p = 7`, where `3² ≡ 2`, bound `#Ẽ(𝔽₇) + 1 = 11`)
shows it is not. Hence the integral is **not elementary** (whenever the constants contain `√2`).
-/

open Polynomial Differential WeierstrassCurve WeierstrassCurve.Affine

namespace EllAlgo.IrrationalExample

open EllDV CPoly

/-- `x² − 2`. -/
def fq : CPoly ℚ := [-2, 0, 1]

lemma toPoly_fq : toPoly fq = X ^ 2 - C 2 := by
  simp [fq, CPoly.toPoly]; ring

lemma irr_fq : Irreducible (toPoly fq) := by
  rw [toPoly_fq]
  refine irreducible_of_degree_le_three_of_not_isRoot (by
    rw [natDegree_X_pow_sub_C]; decide) fun q hq ↦ ?_
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hq
  have h2 : ((q : ℝ)) ^ 2 = 2 := by exact_mod_cast hq
  apply irrational_sqrt_two
  refine ⟨|q|, ?_⟩
  push_cast
  rw [← Real.sqrt_sq_eq_abs, h2]

instance : Fact (Irreducible (toPoly fq)) := ⟨irr_fq⟩

local notation "K" => AdjoinRoot (toPoly fq)

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The integral model of `x² − 2`. -/
noncomputable def fZ : ℤ[X] := X ^ 2 - C 2

lemma hfZ : toPoly fq = fZ.map (Int.castRingHom ℚ) := by
  rw [toPoly_fq, fZ]; simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]; rfl

/-- The point data `(x, y)`. -/
def Pd : Option (CPoly ℚ × CPoly ℚ) := some ([0, 1], [1, 1])
def mσPd : Option (CPoly ℚ × CPoly ℚ) := some ([0, -1], [-1, 1])
def Qd : Option (CPoly ℚ × CPoly ℚ) := addPt fq 1 0 1 Pd mσPd

lemma hΔ : (W K 1 0 1).Δ ≠ 0 := by
  have h0 : (W0 1 0 1).Δ = -496 := by
    simp only [W0, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    norm_num
  rw [W, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, h0]
  simp only [map_neg, map_ofNat]
  norm_num

/-- A point from a checked equation. -/
lemma ns_of_check (x y : CPoly ℚ)
    (h : eqMod fq (mul y y) (add (add (mul x (mul x x)) (mul x x)) [1]) = true) :
    (W K 1 0 1).toAffine.Nonsingular (ev fq x) (ev fq y) := by
  rw [← (equation_iff_nonsingular_of_Δ_ne_zero hΔ), equation_W]
  unfold OnCurve
  have := (ev_eq_iff _ _).mpr h
  simp only [ev_mul, ev_add, ev_const] at this
  push_cast
  linear_combination this

lemma hP : (W K 1 0 1).toAffine.Nonsingular (ev fq [0, 1]) (ev fq [1, 1]) :=
  ns_of_check _ _ (by decide +kernel)
lemma hσP : (W K 1 0 1).toAffine.Nonsingular (ev fq [0, -1]) (ev fq [1, -1]) :=
  ns_of_check _ _ (by decide +kernel)
lemma hmσP : (W K 1 0 1).toAffine.Nonsingular (ev fq [0, -1]) (ev fq [-1, 1]) :=
  ns_of_check _ _ (by decide +kernel)

lemma rep_P : Rep (f := fq) 1 0 1 Pd (Point.some _ _ hP) := ⟨hP, rfl⟩

lemma rep_mσP : Rep (f := fq) 1 0 1 mσPd (-Point.some _ _ hσP) := by
  refine ⟨hmσP, ?_⟩
  rw [Point.neg_some]
  apply some_congr
  · rfl
  · rw [negY_W, ← (ev_eq_iff _ _).mpr (show eqMod fq (smul (-1) [1, -1]) [-1, 1] = true by decide +kernel),
      ev_smul]
    push_cast; ring

/-- **`P − σP` has infinite order.** -/
lemma not_torsion : ¬IsOfFinAddOrder (Point.some _ _ hP - Point.some _ _ hσP) := by
  have hrep : Rep (f := fq) 1 0 1 Qd (Point.some _ _ hP + -Point.some _ _ hσP) :=
    addPt_spec 1 0 1 rep_P rep_mσP
  rw [sub_eq_add_neg]
  intro ht
  have := (torsionTestK_spec (p := 7) (f := fq) 1 0 1 fZ hfZ 3 (by
      simp [fZ]; decide) (by simp [fZ]; decide) (by norm_num) (by decide) hrep 11
      (by
        rw [Fintype.card_option, Fintype.card_congr' (show RedPts 7 1 0 1 =
          {st : ZMod 7 × ZMod 7 // st.2 ^ 2 = st.1 ^ 3 + ((1 : ℤ) : ZMod 7) * st.1 ^ 2 +
            ((0 : ℤ) : ZMod 7) * st.1 + ((1 : ℤ) : ZMod 7)} from rfl), Fintype.card_subtype]
        decide)).mpr ht
  rw [show torsionTestK fq 1 0 1 Qd 11 = false by decide +kernel] at this
  exact Bool.false_ne_true this

lemma ev_ne_zero (q : CPoly ℚ) (h : eqMod fq q [] = false) : ev fq q ≠ 0 := by
  intro h0
  have : ev fq q = ev fq [] := by rw [h0]; simp [ev, CPoly.toPoly]
  rw [(ev_eq_iff _ _).mp this] at h
  exact Bool.noConfusion h

lemma ev_root : ev fq [0, 1] = AdjoinRoot.root (toPoly fq) := by
  simp [ev, CPoly.toPoly, AdjoinRoot.mk_X]

lemma ev_neg_root : ev fq [0, -1] = -AdjoinRoot.root (toPoly fq) := by
  rw [← ev_root, ← (ev_eq_iff _ _).mpr (show eqMod fq (smul (-1) [0, 1]) [0, -1] = true by
    decide +kernel), ev_smul]
  push_cast; ring

lemma hfq0 : toPoly fq ≠ 0 := irr_fq.ne_zero

/-- The power basis `1, √2`. -/
noncomputable def pb : PowerBasis ℚ K := AdjoinRoot.powerBasis hfq0

lemma pb_dim : pb.dim = 2 := by
  rw [pb, AdjoinRoot.powerBasis_dim, toPoly_fq, natDegree_X_pow_sub_C]

/-- The coefficient of `√2`. -/
noncomputable def Λ : K →ₗ[ℚ] ℚ := pb.basis.coord ⟨1, by rw [pb_dim]; norm_num⟩

lemma Λ_root : Λ (AdjoinRoot.root (toPoly fq)) = 1 := by
  have hg : AdjoinRoot.root (toPoly fq) = pb.basis ⟨1, by rw [pb_dim]; norm_num⟩ := by
    rw [PowerBasis.coe_basis]; simp [pb, AdjoinRoot.powerBasis_gen]
  rw [Λ, hg, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ (4x + 4) dx / ((x² − 2) √(x³ + x² + 1))` is not elementary** (constants containing `√2`). -/
theorem ex_irrational_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + x ^ 2 + 1) (hgen : ∀ z : E, InHyp Kc x y z)
    (s2 : Kc) (hs2 : s2 ^ 2 = 2) :
    ¬HasElementaryIntegral ((4 * x + 4) / ((x ^ 2 - 2) * y)) := by
  classical
  have hsq : Squarefree (X ^ 3 + C ((1 : ℤ) : ℚ) * X ^ 2 + C ((0 : ℤ) : ℚ) * X + C ((1 : ℤ) : ℚ)) := by
    have h := CPoly.squarefreeCheck_sound (s := EllAlgo.pOf 1 0 1) (by decide +kernel)
    rwa [EllAlgo.toPoly_pOf] at h
  let ιK : K →+* Kc := AdjoinRoot.lift (algebraMap ℚ Kc) s2 (by
    rw [toPoly_fq]; simp [hs2])
  have hιroot : ιK (AdjoinRoot.root (toPoly fq)) = s2 := AdjoinRoot.lift_root _
  let α : Fin 2 → K := ![ev fq [0, 1], ev fq [0, -1]]
  let β : Fin 2 → K := ![ev fq [1, 1], ev fq [1, -1]]
  let r : Fin 2 → K := ![ev fq [0, 1], ev fq [0, -1]]
  have hPs : ∀ i, (W K 1 0 1).toAffine.Nonsingular (α i) (β i) := by
    intro i; fin_cases i
    · exact hP
    · exact hσP
  have hβ : ∀ i ∈ (Finset.univ : Finset (Fin 2)), β i ≠ 0 := by
    intro i _; fin_cases i
    · exact ev_ne_zero _ (by decide +kernel)
    · exact ev_ne_zero _ (by decide +kernel)
  have hinj : Set.InjOn α (Finset.univ : Finset (Fin 2)) := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso; exact (show ev fq [0, 1] ≠ ev fq [0, -1] from fun h ↦ by
        have := (ev_eq_iff _ _).mp h; revert this; decide +kernel) hij
    · exfalso; exact (show ev fq [0, -1] ≠ ev fq [0, 1] from fun h ↦ by
        have := (ev_eq_iff _ _).mp h; revert this; decide +kernel) hij
    · rfl
  let z : Fin 2 → ℤ := ![1, -1]
  have hΛ : ∀ i ∈ (Finset.univ : Finset (Fin 2)), Λ (r i) = (z i : ℚ) / (1 : ℕ) := by
    intro i _; fin_cases i
    · simp [r, z, ev_root, Λ_root]
    · simp [r, z, ev_neg_root, map_neg, Λ_root]
  have hnt : ¬IsOfFinAddOrder (∑ i ∈ (Finset.univ : Finset (Fin 2)), z i •
      (Point.some _ _ (hPs i) : (W K 1 0 1).toAffine.Point)) := by
    rw [Fin.sum_univ_two]
    simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one, one_zsmul, neg_one_zsmul]
    rw [← sub_eq_add_neg]
    exact not_torsion
  have hmain := not_elem_of_nontorsion hC hCall x y hx 1 0 1 hsq (by rw [hy]; push_cast; ring) hgen
    ιK 0 Finset.univ α β r hPs hβ hinj Λ z 1 one_ne_zero hΛ hnt
  -- the integrand
  set S : E := algebraMap Kc E s2 with hS
  have hS2 : S ^ 2 = 2 := by rw [hS, ← map_pow, hs2, map_ofNat]
  have hSd : S′ = 0 := by rw [hS, deriv_algebraMap, hC, map_zero]
  have hxS : x - S ≠ 0 := fun h0 ↦ by
    have := congrArg (fun t : E ↦ t′) h0
    simp only [map_sub, hx, hSd, sub_zero, map_zero] at this
    exact one_ne_zero this
  have hxS' : x + S ≠ 0 := fun h0 ↦ by
    have := congrArg (fun t : E ↦ t′) h0
    simp only [map_add, hx, hSd, add_zero, map_zero] at this
    exact one_ne_zero this
  have hval : ∀ q : CPoly ℚ, ιK (ev fq q) = aeval s2 (toPoly q) := by
    intro q
    simp only [ιK, ev, AdjoinRoot.lift_mk, aeval_def]
  have e : (4 * x + 4) / ((x ^ 2 - 2) * y) = (aeval x (0 : ℚ[X]) + ∑ i ∈ (Finset.univ : Finset (Fin 2)),
      algebraMap Kc E (ιK (r i * β i)) / (x - algebraMap Kc E (ιK (α i)))) / y := by
    rw [Fin.sum_univ_two]
    simp only [α, β, r, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, hval]
    simp only [CPoly.toPoly, map_add, map_mul, aeval_C, aeval_X, map_zero, add_zero, zero_add,
      eq_ratCast, Rat.cast_one, Rat.cast_neg, Rat.cast_zero, mul_one, mul_zero, zero_mul]
    push_cast
    rw [← hS]
    have hx2 : x ^ 2 - 2 = (x - S) * (x + S) := by rw [← hS2]; ring
    rw [hx2, ← div_div, show x - S * -1 = x + S by ring]
    congr 1
    field_simp
    linear_combination (-(2 : E) * x - 2) * hS2
  rw [e]
  exact hmain

end EllAlgo.IrrationalExample
