import RischTragerBronstein.Curves.Branch

/-!
# Restricting a curve to a subfield of the constants

A curve `S` over `Kc` whose equation has coefficients in a subfield `F ⊆ Kc` (`S.F = G.map ι`) is also
a curve over `F` in the same field `E` (`CurveData.restrict`): `x` stays transcendental and `G`
stays irreducible over `F⟮x⟯`. All evaluations agree (`restrict_evXY`).
-/

open Polynomial

namespace Curves

section Restrict

variable {F Kc E : Type*} [Field F] [Field Kc] [Field E] [Algebra Kc E] [Algebra F E]

lemma aeval_restrict (ι : F →+* Kc) (hc : ∀ c, algebraMap F E c = algebraMap Kc E (ι c)) (x : E) :
    (aeval x : F[X] →ₐ[F] E).toRingHom = (aeval x : Kc[X] →ₐ[Kc] E).toRingHom.comp (mapRingHom ι) := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · simp [hc]
  · simp

namespace CurveData

/-- **The curve over the subfield `F`.** -/
def restrict (S : CurveData Kc E) (ι : F →+* Kc) (hc : ∀ c, algebraMap F E c = algebraMap Kc E (ι c))
    (G : F[X][X]) (hG : S.F = G.map (mapRingHom ι)) (hmon : G.Monic) : CurveData F E where
  x := S.x
  y := S.y
  F := G
  htr := by
    intro ⟨p, hp0, hp⟩
    apply S.htr
    refine ⟨p.map ι, (Polynomial.map_ne_zero_iff ι.injective).mpr hp0, ?_⟩
    have := congrArg (fun f ↦ f p) (aeval_restrict ι hc S.x)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
      coe_mapRingHom] at this
    rw [← this]; exact hp
  monic := hmon
  irr := by
    intro H hH h0
    have e : (H.map (aeval S.x).toRingHom).eval S.y =
        ((H.map (mapRingHom ι)).map (aeval S.x).toRingHom).eval S.y := by
      rw [Polynomial.map_map, aeval_restrict ι hc]
    have hdeg : (H.map (mapRingHom ι)).natDegree < S.F.natDegree := by
      rw [hG, natDegree_map_eq_of_injective (Polynomial.map_injective _ ι.injective),
        natDegree_map_eq_of_injective (Polynomial.map_injective _ ι.injective)]
      exact hH
    have := S.irr _ hdeg (by rw [← e]; exact h0)
    exact (Polynomial.map_eq_zero_iff (Polynomial.map_injective _ ι.injective)).mp this
  root := by
    have e : (G.map (aeval S.x).toRingHom).eval S.y =
        ((G.map (mapRingHom ι)).map (aeval S.x).toRingHom).eval S.y := by
      rw [Polynomial.map_map, aeval_restrict ι hc]
    rw [e, ← hG]; exact S.root

variable (S : CurveData Kc E) (ι : F →+* Kc) (hc : ∀ c, algebraMap F E c = algebraMap Kc E (ι c))
  (G : F[X][X]) (hG : S.F = G.map (mapRingHom ι)) (hmon : G.Monic)

@[simp] lemma restrict_x : (S.restrict ι hc G hG hmon).x = S.x := rfl
@[simp] lemma restrict_y : (S.restrict ι hc G hG hmon).y = S.y := rfl
@[simp] lemma restrict_F : (S.restrict ι hc G hG hmon).F = G := rfl

lemma restrict_evXY (W : F[X][X]) :
    (S.restrict ι hc G hG hmon).evXY W = S.evXY (W.map (mapRingHom ι)) := by
  simp only [evXY, restrict_x, restrict_y]
  rw [Polynomial.map_map, aeval_restrict ι hc]

end CurveData

end Restrict

end Curves
