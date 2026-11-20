import RischTragerBronstein.Mixed.KBMain
import RischTragerBronstein.Mixed.KRIrr

/-!
# Changing the base curve: the irreducibility facts from Eisenstein

`fKc_irr_eis`: an Eisenstein base curve is irreducible over the code field `ℚ(x)`;
`qK_irr_linear`: over a linear base, the minimal polynomial `Q` of the new coordinate, given by a
bivariate polynomial over `ℚ` which is Eisenstein, is irreducible over the code field. Both by
Gauss's lemma over `ℚ(x)` and pulling back along an injective homomorphism.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT

lemma irr_ratFunc_of_eis (Fq : BPoly ℚ) (hmon : (toB Fq).Monic)
    (hlen : (toB Fq).natDegree = Fq.length - 1) (hd : 0 < (toB Fq).natDegree) (c : ℚ)
    (heis : eisC Fq c = true) :
    Irreducible ((toB Fq).map (algebraMap ℚ[X] (RatFunc ℚ))) := by
  have hQ := eis_irr ℚ Fq hmon hlen hd c heis
  have hid : (toB Fq).map (mapRingHom (algebraMap ℚ ℚ)) = toB Fq := by
    rw [Algebra.algebraMap_self, mapRingHom_id, Polynomial.map_id]
  rw [hid] at hQ
  exact (hmon.irreducible_iff_irreducible_map_fraction_map).mp hQ

lemma fKc_map (Fq : BPoly ℚ) : (toPoly (fKc Fq)).map (RFC.toRFHom (K := ℚ)) =
    (toB Fq).map (algebraMap ℚ[X] (RatFunc ℚ)) := by
  induction Fq with
  | nil => simp [fKc]
  | cons p W ih =>
    simp only [fKc, List.map_cons, toPoly_cons, toB_cons, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X] at ih ⊢
    rw [ih]
    congr 2
    change RFC.toRF (RFC.mk p [1]) = _
    rw [RFC.toRF_mk]
    simp

/-- **A base curve irreducible over `ℚ(x)` is irreducible over the code field.** -/
theorem fKc_irr_of_ratFunc (Fq : BPoly ℚ) (hmon : (toB Fq).Monic)
    (hR : Irreducible ((toB Fq).map (algebraMap ℚ[X] (RatFunc ℚ)))) :
    Irreducible (toPoly (fKc Fq)) := by
  have hmap := fKc_map Fq
  have hinj : Function.Injective (RFC.toRFHom (K := ℚ)) := RFC.toRF_injective
  have hm : (toPoly (fKc Fq)).Monic := Polynomial.monic_of_injective hinj (by rw [hmap]; exact hmon.map _)
  exact hm.irreducible_of_irreducible_map _ _ (by rw [hmap]; exact hR)

/-- **An Eisenstein base curve is irreducible over the code field.** -/
theorem fKc_irr_eis (Fq : BPoly ℚ) (hmon : (toB Fq).Monic)
    (hlen : (toB Fq).natDegree = Fq.length - 1) (hd : 0 < (toB Fq).natDegree) (c : ℚ)
    (heis : eisC Fq c = true) : Irreducible (toPoly (fKc Fq)) :=
  fKc_irr_of_ratFunc Fq hmon (irr_ratFunc_of_eis Fq hmon hlen hd c heis)

/-- The minimal polynomial `Q` given by a bivariate polynomial over `ℚ`. -/
def qOfB (Fq : BPoly ℚ) : GPoly (LC 0) := Fq.map fun p ↦ ([(p, [1])] : GPoly (GFrac ℚ))

/-- **Over a linear base, a `Q` irreducible over `ℚ(x)` is irreducible over the code field.** -/
theorem qK_irr_linear_of_ratFunc (c0 : CPoly ℚ) (Fq : BPoly ℚ) (hmon : (toB Fq).Monic)
    (hR : Irreducible ((toB Fq).map (algebraMap ℚ[X] (RatFunc ℚ)))) :
    haveI : Fact (Irreducible (toPoly (fKc [c0, [1]]))) := ⟨fKc_irr_linear c0⟩
    Irreducible (toPoly (qK [c0, [1]] (qOfB Fq))) := by
  haveI : Fact (Irreducible (toPoly (fKc [c0, [1]]))) := ⟨fKc_irr_linear c0⟩
  set ψ := psiLin c0 with hψ
  have hψmk : ∀ r : RFC.RatFuncC ℚ, ψ (NFK.mk _ [r]) = RFC.toRF r := fun r ↦ by
    simp only [hψ, psiLin, RingHom.comp_apply]
    change AdjoinRoot.lift _ _ _ (NFK.toAR _ (NFK.mk _ [r])) = _
    rw [NFK.toAR_mk, AdjoinRoot.lift_mk]
    simp [toPoly_cons]
    rfl
  set gq : CPoly ℚ → KF [c0, [1]] 0 := fun p ↦ NFK.mk _ [trX (p, [1])] with hgq
  have hlist : (qOfB Fq).map (trC [c0, [1]] 0) = Fq.map gq := by
    clear hR hmon
    induction Fq with
    | nil => rfl
    | cons p W ih => exact congrArg (List.cons (gq p)) ih
  have hmap : (toPoly (qK [c0, [1]] (qOfB Fq))).map ψ = (toB Fq).map (algebraMap ℚ[X] (RatFunc ℚ)) := by
    rw [qK, toPoly_trim, hlist]
    clear hR hmon hlist
    induction Fq with
    | nil => simp
    | cons p W ih =>
      rw [List.map_cons, toPoly_cons, toB_cons, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X, ih, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X]
      congr 2
      rw [hgq, hψmk, trX, RFC.toRF_mk]
      simp
  have hm : (toPoly (qK [c0, [1]] (qOfB Fq))).Monic :=
    Polynomial.monic_of_injective ψ.injective (by rw [hmap]; exact hmon.map _)
  exact hm.irreducible_of_irreducible_map _ _ (by rw [hmap]; exact hR)

/-- **Over a linear base, an Eisenstein `Q` is irreducible over the code field.** -/
theorem qK_irr_linear (c0 : CPoly ℚ) (Fq : BPoly ℚ) (hmon : (toB Fq).Monic)
    (hlen : (toB Fq).natDegree = Fq.length - 1) (hd : 0 < (toB Fq).natDegree) (c : ℚ)
    (heis : eisC Fq c = true) :
    haveI : Fact (Irreducible (toPoly (fKc [c0, [1]]))) := ⟨fKc_irr_linear c0⟩
    Irreducible (toPoly (qK [c0, [1]] (qOfB Fq))) :=
  qK_irr_linear_of_ratFunc c0 Fq hmon (irr_ratFunc_of_eis Fq hmon hlen hd c heis)

/-- **`N = ℚ`**: `M = X` is irreducible over every code field. -/
theorem liftQ_X_irr (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) :
    Irreducible (toPoly (liftQ Fc m [0, 1])) := by
  rw [toPoly_liftQ]
  refine Polynomial.irreducible_of_degree_eq_one ?_
  simp [toPoly_cons]

end Curves.MT
