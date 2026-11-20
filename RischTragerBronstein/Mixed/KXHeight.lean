import RischTragerBronstein.Mixed.KXAbel
import RischTragerBronstein.Mixed.EllBaseChange

/-!
# From the coefficient field to the height pairing (step 3)

When the coefficient field `C` of `θ² = c₃t³ + c₂t² + c₁t + c₀` is a rational function field
(`φ : C ≃+* k(X)`, e.g. the top level `Kₘ = Kₘ₋₁(tₘ₋₁)` of a tower or the base `ℚ(x)`), Mathlib's
model `W'(C)` embeds by an **injective group homomorphism** into the short curve
`y² = x³ + A x + B` over `k(X)` with `A, B ∈ k[X]` (`toShort`: base change along `φ`, translation
`X ↦ X + a₂/3` (`EllTrans`), scaling to polynomial coefficients (`EllScale`)).
`hgrpC_of_indep`: independence of the images (e.g. by `EllNT.ell_indep`) gives the group hypothesis
of `kxe_norel_group`, through `hgrp_of_C`.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Differential

namespace SuperData

open scoped Classical

variable {C : Type*} [Field C] [CharZero C]

/-- **Relations from independence**: if an injective homomorphism `ψ` carries `D, Z` to points
without relations, then `2N D + 2μ Z ≠ 0` for `N > 0`. -/
theorem hgrp_of_indep {G H : Type*} [AddCommGroup G] [AddCommGroup H] (ψ : G →+ H)
    (hψ : Function.Injective ψ) (D Z : G)
    (hind : ∀ m n : ℤ, m • ψ D = n • ψ Z → m = 0 ∧ n = 0) :
    ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • D + (2 * μ) • Z ≠ 0 := by
  intro N hN μ h
  have h' : (2 * (N : ℤ)) • ψ D = (-(2 * μ)) • ψ Z := by
    rw [← map_zsmul, ← map_zsmul, neg_smul]
    congr 1
    exact eq_neg_of_add_eq_zero_left h
  have := (hind _ _ h').1
  omega

variable {k : Type*} [Field k] [CharZero k] (φ : C ≃+* RatFunc k)

/-- The map `W'(C) → W'(k(X))` along `φ`, landing on the long form with mapped coefficients. -/
noncomputable def alongφ (c3 c2 c1 c0 : C) :
    (WG c3 c2 c1 c0).Point →+ (FFHeight.longF (φ c2) (φ (c1 * c3)) (φ (c0 * c3 ^ 2))).toAffine.Point :=
  letI : Algebra C (RatFunc k) := φ.toRingHom.toAlgebra
  have hself : WG c3 c2 c1 c0 = ((WG c3 c2 c1 c0)⁄C) := by
    simp [WG, FFHeight.longF, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have hbc : ((WG c3 c2 c1 c0)⁄(RatFunc k)) =
      (FFHeight.longF (φ c2) (φ (c1 * c3)) (φ (c0 * c3 ^ 2))).toAffine := by
    simp [WG, FFHeight.longF, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map,
      RingHom.algebraMap_toAlgebra]
  (FFHeight.castHom hbc).comp ((Point.map (W' := WG c3 c2 c1 c0) (Algebra.ofId C (RatFunc k))).comp
    (FFHeight.castHom hself))

lemma alongφ_injective (c3 c2 c1 c0 : C) : Function.Injective (alongφ φ c3 c2 c1 c0) := by
  letI : Algebra C (RatFunc k) := φ.toRingHom.toAlgebra
  unfold alongφ
  exact (FFHeight.castHom_injective _).comp ((Point.map_injective _).comp
    (FFHeight.castHom_injective _))

/-- **The embedding into the polynomial short curve** `y² = x³ + A x + B` over `k(X)`. -/
noncomputable def toShort (c3 c2 c1 c0 : C) (u : RatFunc k) (hu : u ≠ 0) (A B : k[X])
    (hA : algebraMap k[X] (RatFunc k) A =
      u ^ 4 * (φ (c1 * c3) - φ c2 ^ 2 / 3))
    (hB : algebraMap k[X] (RatFunc k) B =
      u ^ 6 * (φ (c0 * c3 ^ 2) - φ c2 * φ (c1 * c3) / 3 + 2 * φ c2 ^ 3 / 27)) :
    (WG c3 c2 c1 c0).Point →+ (FFHeight.shortW A B).toAffine.Point :=
  (FFHeight.scaleHomEq _ _ _ _ u hu hA hB).comp
    ((FFHeight.transHom (φ c2) (φ (c1 * c3)) (φ (c0 * c3 ^ 2))).comp (alongφ φ c3 c2 c1 c0))

lemma toShort_injective (c3 c2 c1 c0 : C) (u : RatFunc k) (hu : u ≠ 0) (A B : k[X]) (hA hB) :
    Function.Injective (toShort φ c3 c2 c1 c0 u hu A B hA hB) := by
  unfold toShort
  exact (FFHeight.scaleHomEq_injective _ _ _ _ _ _ _ _).comp
    ((FFHeight.transHom_injective _ _ _).comp (alongφ_injective φ c3 c2 c1 c0))

lemma alongφ_some (c3 c2 c1 c0 x y : C) (h : (WG c3 c2 c1 c0).Nonsingular x y) :
    ∃ h', alongφ φ c3 c2 c1 c0 (WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some (φ x) (φ y) h' := by
  letI : Algebra C (RatFunc k) := φ.toRingHom.toAlgebra
  unfold alongφ
  simp only [AddMonoidHom.comp_apply]
  erw [FFHeight.castHom_some]
  refine ⟨?w, ?e⟩
  case e => rfl
  case w =>
    have := (Affine.map_nonsingular (W := (WG c3 c2 c1 c0)) (f := φ.toRingHom) φ.injective x y).mpr h
    convert this using 1
    · simp [WG, FFHeight.longF, Affine.map, WeierstrassCurve.map]
    · rfl
    · rfl

/-- **Coordinates of `toShort`**: `(X, Y) ↦ (u²(φX + φc₂/3), u³ φY)`. -/
lemma toShort_some (c3 c2 c1 c0 : C) (u : RatFunc k) (hu : u ≠ 0) (A B : k[X]) (hA hB)
    (x y : C) (h : (WG c3 c2 c1 c0).Nonsingular x y) :
    ∃ h', toShort φ c3 c2 c1 c0 u hu A B hA hB (WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some (u ^ 2 * (φ x + φ c2 / 3)) (u ^ 3 * φ y) h' := by
  obtain ⟨h1, e1⟩ := alongφ_some φ c3 c2 c1 c0 x y h
  have hc : toShort φ c3 c2 c1 c0 u hu A B hA hB (WeierstrassCurve.Affine.Point.some x y h) =
      FFHeight.scaleHomEq _ _ _ _ u hu hA hB (FFHeight.transHom (φ c2) (φ (c1 * c3)) (φ (c0 * c3 ^ 2))
        (alongφ φ c3 c2 c1 c0 (WeierstrassCurve.Affine.Point.some x y h))) := rfl
  rw [hc, e1, FFHeight.transHom_apply]
  simp only [FFHeight.transP]
  obtain ⟨h2, e2⟩ := FFHeight.scaleHomEq_some _ _ _ _ u hu hA hB
    (FFHeight.ns_trans (φ c2) (φ (c1 * c3)) (φ (c0 * c3 ^ 2)) _ _ h1)
  exact ⟨h2, e2⟩

/-- **The group hypothesis of `kxe_norel_group` from a height certificate.** With the points
defined over `C ≃ k(X)`, a height certificate (`EllNT.ell_indep`) for the images of
`D = ∑ m_q P_q` and `P₊` in `y² = x³ + Ax + B` gives `2N D + 2μ P₊ ≠ 0` in `W'(K)`. -/
theorem hgrp_of_height {K : Type*} [Differential C] [Field K] [CharZero K] [Algebra C K]
    [Differential K] [IsAlgClosed K]
    {r nk : ℕ} (c β : Fin r → C) (m : Fin r → ℕ) (cl : Fin r → Fin nk) (k0 : Fin nk)
    (c3 c2 c1 c0 b₀ : C)
    (hnsC : ∀ q, (WG c3 c2 c1 c0).Nonsingular (c3 * c q) (c3 * β q))
    (hns0C : (WG c3 c2 c1 c0).Nonsingular (c3 * 0) (c3 * b₀))
    (u : RatFunc k) (hu : u ≠ 0) (A B : k[X])
    (hA : algebraMap k[X] (RatFunc k) A = u ^ 4 * (φ (c1 * c3) - φ c2 ^ 2 / 3))
    (hB : algebraMap k[X] (RatFunc k) B =
      u ^ 6 * (φ (c0 * c3 ^ 2) - φ c2 * φ (c1 * c3) / 3 + 2 * φ c2 ^ 3 / 27))
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (kk : ℕ)
    (hgap : let P := (toShort φ c3 c2 c1 c0 u hu A B hA hB
        (∑ q, (mK m cl k0 q : ℤ) • Point.some _ _ (hnsC q)))
      let Q := (toShort φ c3 c2 c1 c0 u hu A B hA hB (Point.some _ _ hns0C))
      let Cc : ℝ := 11 * (max A.natDegree B.natDegree : ℕ)
      let h := FFHeight.hR A B
      let d := MWPair.dbl (G := (FFHeight.shortW A B).toAffine.Point)
      Cc / 3 / 4 ^ kk * (|h (d^[kk] P) / 4 ^ kk| + |h (d^[kk] Q) / 4 ^ kk| + Cc / 3 / 4 ^ kk) +
        3 * (Cc / 3 / 4 ^ kk) / 2 * (|h (d^[kk] (P + Q)) / 4 ^ kk - h (d^[kk] P) / 4 ^ kk -
          h (d^[kk] Q) / 4 ^ kk| + 3 * (Cc / 3 / 4 ^ kk) / 2) <
      |h (d^[kk] P) / 4 ^ kk * (h (d^[kk] Q) / 4 ^ kk) - ((h (d^[kk] (P + Q)) / 4 ^ kk -
          h (d^[kk] P) / 4 ^ kk - h (d^[kk] Q) / 4 ^ kk) / 2) ^ 2|)
    (hnsq : ∀ q, (WG (algebraMap C K c3) (algebraMap C K c2) (algebraMap C K c1)
      (algebraMap C K c0)).Nonsingular (algebraMap C K c3 * algebraMap C K (c q))
      (algebraMap C K c3 * algebraMap C K (β q)))
    (hns0 : (WG (algebraMap C K c3) (algebraMap C K c2) (algebraMap C K c1)
      (algebraMap C K c0)).Nonsingular (algebraMap C K c3 * 0) (algebraMap C K c3 * algebraMap C K b₀)) :
    ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
      (2 * (N : ℤ)) • (∑ q, (mK m cl k0 q : ℤ) • Point.some _ _ (hnsq q)) +
        (2 * μ) • Point.some _ _ hns0 ≠ 0 :=
  hgrp_of_C (K := K) c β m cl k0 c3 c2 c1 c0 b₀ hnsC hns0C
    (hgrp_of_indep (toShort φ c3 c2 c1 c0 u hu A B hA hB)
      (toShort_injective φ c3 c2 c1 c0 u hu A B hA hB) _ _
      (fun m' n' h ↦ FFHeight.ell_indep A B hΔ _ _ kk hgap m' n' h)) hnsq hns0

/-- **The group condition from an executable certificate**: certificate points over `k₀` whose
images under `mapE` (along `j : k₀ → k`) are the `toShort`-images of `D, Z`, with a passing
`certQ`, give `2N D + 2μ Z ≠ 0` for all `N > 0`, `μ`. -/
theorem hgrp_of_cert {k₀ : Type*} [Field k₀] [CharZero k₀] [DecidableEq k₀] (j : k₀ →+* k)
    (c3 c2 c1 c0 : C) (u : RatFunc k) (hu : u ≠ 0) (A₀ B₀ : k₀[X])
    (hA : algebraMap k[X] (RatFunc k) (A₀.map j) = u ^ 4 * (φ (c1 * c3) - φ c2 ^ 2 / 3))
    (hB : algebraMap k[X] (RatFunc k) (B₀.map j) =
      u ^ 6 * (φ (c0 * c3 ^ 2) - φ c2 * φ (c1 * c3) / 3 + 2 * φ c2 ^ 3 / 27))
    (hΔ : 4 * (A₀.map j) ^ 3 + 27 * (B₀.map j) ^ 2 ≠ 0)
    (D Z : (WG c3 c2 c1 c0).Point) (Ac : CPoly k₀) (hAc : CPoly.toPoly Ac = A₀) (kk : ℕ)
    (oD oZ : FFHeight.PtC k₀) (PD PZ : (FFHeight.shortW A₀ B₀).toAffine.Point)
    (hD : FFHeight.Rel A₀ B₀ oD PD) (hZ : FFHeight.Rel A₀ B₀ oZ PZ)
    (hmD : FFHeight.mapE j A₀ B₀ PD = toShort φ c3 c2 c1 c0 u hu (A₀.map j) (B₀.map j) hA hB D)
    (hmZ : FFHeight.mapE j A₀ B₀ PZ = toShort φ c3 c2 c1 c0 u hu (A₀.map j) (B₀.map j) hA hB Z)
    (hc : FFHeight.certQ Ac (max A₀.natDegree B₀.natDegree) kk oD oZ = true) :
    ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • D + (2 * μ) • Z ≠ 0 :=
  hgrp_of_indep (toShort φ c3 c2 c1 c0 u hu (A₀.map j) (B₀.map j) hA hB)
    (toShort_injective φ c3 c2 c1 c0 u hu _ _ hA hB) D Z (fun m n h ↦ by
      rw [← hmD, ← hmZ] at h
      exact FFHeight.indep_mapE_of_certQ j Ac A₀ B₀ hAc hΔ kk oD oZ PD PZ hD hZ hc m n h)

/-- **One certificate point**: two coordinate equalities give the represented point. -/
lemma cert_pt {k₀ : Type*} [Field k₀] [CharZero k₀] [DecidableEq k₀] (j : k₀ →+* k)
    (c3 c2 c1 c0 : C) (u : RatFunc k) (hu : u ≠ 0) (A₀ B₀ : k₀[X])
    (hA : algebraMap k[X] (RatFunc k) (A₀.map j) = u ^ 4 * (φ (c1 * c3) - φ c2 ^ 2 / 3))
    (hB : algebraMap k[X] (RatFunc k) (B₀.map j) =
      u ^ 6 * (φ (c0 * c3 ^ 2) - φ c2 * φ (c1 * c3) / 3 + 2 * φ c2 ^ 3 / 27))
    (x y : C) (h : (WG c3 c2 c1 c0).Nonsingular x y) (fx fy : FFHeight.Fr k₀)
    (ox : FFHeight.Fr.ok fx) (oy : FFHeight.Fr.ok fy)
    (hx : FFHeight.ratMap j (FFHeight.Fr.val fx) = u ^ 2 * (φ x + φ c2 / 3))
    (hy : FFHeight.ratMap j (FFHeight.Fr.val fy) = u ^ 3 * φ y) :
    ∃ Pk : (FFHeight.shortW A₀ B₀).toAffine.Point, FFHeight.Rel A₀ B₀ (some (fx, fy)) Pk ∧
      FFHeight.mapE j A₀ B₀ Pk = toShort φ c3 c2 c1 c0 u hu (A₀.map j) (B₀.map j) hA hB
        (WeierstrassCurve.Affine.Point.some x y h) := by
  obtain ⟨h', e⟩ := toShort_some φ c3 c2 c1 c0 u hu _ _ hA hB x y h
  have h'' : (FFHeight.shortW (A₀.map j) (B₀.map j)).toAffine.Nonsingular
      (FFHeight.ratMap j (FFHeight.Fr.val fx)) (FFHeight.ratMap j (FFHeight.Fr.val fy)) := by
    rw [hx, hy]; exact h'
  obtain ⟨Pk, hR, hm⟩ := FFHeight.pt_of_image j A₀ B₀ fx fy ox oy h''
  refine ⟨Pk, hR, ?_⟩
  rw [hm, e]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

/-- **Combinations of certificate points.** -/
lemma cert_sum {k₀ : Type*} [Field k₀] [CharZero k₀] [DecidableEq k₀] (j : k₀ →+* k)
    (c3 c2 c1 c0 : C) (u : RatFunc k) (hu : u ≠ 0) (A₀ B₀ : k₀[X])
    (hA : algebraMap k[X] (RatFunc k) (A₀.map j) = u ^ 4 * (φ (c1 * c3) - φ c2 ^ 2 / 3))
    (hB : algebraMap k[X] (RatFunc k) (B₀.map j) =
      u ^ 6 * (φ (c0 * c3 ^ 2) - φ c2 * φ (c1 * c3) / 3 + 2 * φ c2 ^ 3 / 27))
    (Ac : CPoly k₀) (hAc : CPoly.toPoly Ac = A₀) :
    ∀ (l : List (ℤ × FFHeight.PtC k₀ × (WG c3 c2 c1 c0).Point)),
      (∀ e ∈ l, ∃ Pk : (FFHeight.shortW A₀ B₀).toAffine.Point, FFHeight.Rel A₀ B₀ e.2.1 Pk ∧
        FFHeight.mapE j A₀ B₀ Pk = toShort φ c3 c2 c1 c0 u hu (A₀.map j) (B₀.map j) hA hB e.2.2) →
      ∃ Pk : (FFHeight.shortW A₀ B₀).toAffine.Point,
        FFHeight.Rel A₀ B₀ (FFHeight.sumC Ac (l.map fun e ↦ (e.1, e.2.1))) Pk ∧
        FFHeight.mapE j A₀ B₀ Pk = toShort φ c3 c2 c1 c0 u hu (A₀.map j) (B₀.map j) hA hB
          (l.map fun e ↦ e.1 • e.2.2).sum
  | [], _ => ⟨0, trivial, by simp⟩
  | e :: l, h => by
    obtain ⟨P1, hR1, hm1⟩ := h e List.mem_cons_self
    obtain ⟨P2, hR2, hm2⟩ := cert_sum j c3 c2 c1 c0 u hu A₀ B₀ hA hB Ac hAc l
      (fun e' he' ↦ h e' (List.mem_cons_of_mem _ he'))
    refine ⟨e.1 • P1 + P2, FFHeight.addC_spec Ac A₀ B₀ hAc _ _ _ _
      (FFHeight.zsmulC_spec Ac A₀ B₀ hAc e.1 _ P1 hR1) hR2, ?_⟩
    simp only [List.map_cons, List.sum_cons, map_add, map_zsmul, hm1, hm2]

end SuperData

end Differential
