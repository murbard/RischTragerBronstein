import RischTragerBronstein.Mixed.KRCyclo

/-!
# `Φₙ` stays irreducible over the code fields of a linear base

For the base curve `y + c₀(x) = 0` (the field `ℚ(x)`), `Φₙ` is irreducible over every code field
`Kₘ = ℚ(x)(t₁, …, tₘ)` (`cycK_irr_linear`): by Gauss's lemma and the specialization `t ↦ 0`, a
monic irreducible polynomial over `K` stays irreducible over `K(t)` (`irr_ratFunc`), and
irreducibility pulls back along field homomorphisms (`irr_pullback`).
-/

open Polynomial CPoly Sup

namespace Curves.MT

/-- **Gauss**: a monic irreducible polynomial over `K` stays irreducible over `K(t)`. -/
lemma irr_ratFunc {K : Type*} [Field K] (p : K[X]) (hm : p.Monic) (hp : Irreducible p) :
    Irreducible (p.map (algebraMap K (RatFunc K))) := by
  have h1 : Irreducible (p.map (Polynomial.C : K →+* K[X])) := by
    refine (hm.map _).irreducible_of_irreducible_map (Polynomial.constantCoeff) _ ?_
    rw [Polynomial.map_map]
    convert hp
    have : (Polynomial.constantCoeff).comp (Polynomial.C : K →+* K[X]) = RingHom.id K :=
      RingHom.ext fun a ↦ by simp
    rw [this, Polynomial.map_id]
  have h2 := ((hm.map (Polynomial.C : K →+* K[X])).irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc K)).mp h1
  rw [Polynomial.map_map] at h2
  convert h2 using 2

/-- Irreducibility pulls back along a field homomorphism. -/
lemma irr_pullback {F F' : Type*} [Field F] [Field F'] [CharZero F] [CharZero F'] (ψ : F →+* F')
    (p : ℚ[X]) (hm : p.Monic) (χ : ℚ →+* F') (h : Irreducible (p.map χ)) :
    Irreducible (p.map (algebraMap ℚ F)) := by
  refine (hm.map _).irreducible_of_irreducible_map ψ _ ?_
  rw [Polynomial.map_map]
  convert h using 2
  exact RingHom.ext_rat _ _

variable (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))]

/-- The evaluation `K₀ = ℚ(x)[y]/(y + c₀) → ℚ(x)`. -/
noncomputable def psiLin : KF [c0, [1]] 0 →+* RatFunc ℚ :=
  (AdjoinRoot.lift (RFC.toRFHom (K := ℚ)) (-(RFC.toRF (RFC.mk c0 [1] : RFC.RatFuncC ℚ))) (by
    change (toPoly [RFC.mk c0 [1], RFC.mk [1] [1]]).eval₂ _ _ = 0
    simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero, eval₂_add, eval₂_C, eval₂_mul, eval₂_X]
    change RFC.toRF (RFC.mk c0 [1]) + -RFC.toRF (RFC.mk c0 [1]) * RFC.toRF (RFC.mk [1] [1]) = 0
    rw [RFC.toRF_const, map_one]
    ring)).comp (NFK.toARHom _)

/-- **`Φₙ` is irreducible over every code field of a linear base.** -/
theorem cyc_irr_KF (n : ℕ) (hn : 0 < n) :
    ∀ m, Irreducible ((cyclotomic n ℚ).map (algebraMap ℚ (KF [c0, [1]] m)))
  | 0 => irr_pullback (psiLin c0) _ (cyclotomic.monic n ℚ) _
      (irr_ratFunc _ (cyclotomic.monic n ℚ) (cyclotomic.irreducible_rat hn))
  | m + 1 => by
    letI := (KB [c0, [1]] m).2.fld
    letI := (KB [c0, [1]] m).2.deq
    letI := (KB [c0, [1]] m).2.cz
    have ih := cyc_irr_KF n hn m
    have h := irr_ratFunc _ ((cyclotomic.monic n ℚ).map _) ih
    rw [Polynomial.map_map] at h
    exact irr_pullback (RFC.toRFHom (K := KF [c0, [1]] m)) _ (cyclotomic.monic n ℚ) _ h

lemma toPoly_cycK (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (m n : ℕ) (hn : 0 < n) :
    toPoly (cycK Fc m n) = (cyclotomic n ℚ).map (algebraMap ℚ (KF Fc m)) := by
  rw [cycK, toPoly_trim]
  have hmap : ∀ l : List ℚ, toPoly (List.map (fun q : ℚ ↦ (Rat.cast q : KF Fc m)) l) =
      (toPoly l).map (algebraMap ℚ _) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, toPoly_cons, toPoly_cons, ih, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X, eq_ratCast]
  rw [hmap, cycloQ_spec n hn]

/-- **The `Fact` needed by `krDecide`** for a linear base. -/
theorem cycK_irr_linear (m n : ℕ) (hn : 0 < n) : Irreducible (toPoly (cycK [c0, [1]] m n)) := by
  rw [toPoly_cycK _ m n hn]
  exact cyc_irr_KF c0 n hn m

end Curves.MT
