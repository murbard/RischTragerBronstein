import RischTragerBronstein.Mixed.CurveLiouvilleFormMob
import RischTragerBronstein.Torsion.CertExistsFinal

/-!
# Elementary integrals on curves are explicit Liouville forms

**`curve_liouvilleForm`**: on a curve over `ℚ` with algebraically closed constants `Kc`
(`E = Kc(x, y)`), an integrand of valid shape with an elementary integral is `v′ + ∑ cᵢ uᵢ′/uᵢ`
with `cᵢ ∈ Kc`, `v, uᵢ ∈ E`. (Certificates exist, `certExists_of_curve`, and the positive answer
of a certificate is such a form, `CertQ.run_true`.) Consequently it has an elementary integral over
every differential extension of `E` (`curve_hasElementaryIntegralIn`).
-/

open Polynomial IntermediateField Differential

namespace Curves

open CPoly Sup NFC

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- **A positive certificate answer is a Liouville form.** -/
theorem CertQ.run_true (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (P0 : CurveProb ℚ)
    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc))) (c : CertQ)
    (h : c.run P0 = some true) :
    LiouvilleFormE ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) := by
  obtain ⟨⟨M, hM⟩, d⟩ := c
  haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound _ hM⟩
  set ι : NFC.NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NFC.NF M) (M := Kc)).toRingHom
  have hι : ι.comp (algebraMap ℚ (NFC.NF M)) = algebraMap ℚ Kc := Subsingleton.elim _ _
  obtain ⟨pts, inf, ws, twps, mob⟩ := d
  have hSF' : ∀ pts inf, S.F = (toB (P0.baseChange (algebraMap ℚ (NFC.NF M)) P0.k pts inf).Fc).map
      (mapRingHom ι) := fun pts inf ↦ by
    rw [hSF, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp, hι]
  cases mob with
  | none =>
    have key := decideLog_true hC S hx _ ι (hSF' pts inf) ws (decideLog_of_decideLogTP_true h)
    rwa [S.fE_baseChange, hι] at key
  | some q =>
    obtain ⟨e, k₀, DA, k'⟩ := q
    simp only [CertQ.run] at h
    split_ifs at h with hmob
    have key := decideLogTP_mob_true hC S hx hgen (redAtM M) (redAtM_valid M) _ _ ι
      (hSF' [] ⟨1, [], 0⟩) e k₀ DA hmob ws [] twps h
    rwa [S.fE_baseChange, hι] at key

theorem decideEnum_true (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (P0 : CurveProb ℚ)
    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc))) (N : ℕ)
    (h : decideEnum P0 N = some true) :
    LiouvilleFormE ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨c, -, hc⟩ := Option.bind_eq_some_iff.mp hk
  exact CertQ.run_true hC S hx hgen P0 hSF c hc

/-- **Elementary integrals on a curve are Liouville forms over the function field.** -/
theorem curve_liouvilleForm (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (P0 : CurveProb ℚ) (hS : P0.shapeOK = true)
    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc)))
    (hel : HasElementaryIntegral ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E)) :
    LiouvilleFormE ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) := by
  obtain ⟨N₀, hN₀⟩ := decideEnum_complete P0 (certExists_of_curve P0 hS S hSF)
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hN₀ N₀ le_rfl)
  have hbt := (decideEnum_spec hC S hx hgen P0 hSF N₀ b hb).mp hel
  subst hbt
  exact decideEnum_true hC S hx hgen P0 hSF N₀ hb

end Main

end Curves
