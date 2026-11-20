import RischTragerBronstein.Mixed.KBWeights
import RischTragerBronstein.Torsion.MobCurve
import RischTragerBronstein.Torsion.IrrSubset
import RischTragerBronstein.Torsion.AutoField

/-!
# Geometric irreducibility through a Möbius transformation

`irreducible_of_mob`: if the inverted curve `F′(x′, Y) = x′ᴹ F(a + 1/x′, Y/x′ᵏ)` (`invP (shiftP F a)`)
is irreducible over `K[x]`, so is `F`: a root `y′` of `F′` over `K(x′)` gives the curve `S′`, whose
inverse `mobCurve S′ 0` is the curve of `shiftP F a` (`invP_invP`), so a factor of `F` would give a
lower-degree polynomial vanishing at a point of an irreducible curve. Hence geometric irreducibility
transfers (`geomIrr_of_mob`), and a single place at a rational point `x = a` (a single place at
infinity of the inverted curve, `wtC`) certifies it (`geomIrr_of_wt_mob`): this generalizes both
the Eisenstein criterion and `geomIrr_of_wt`.
-/

open Polynomial

namespace Curves.MT

open CPoly CPoly.Kron Sup Curves

section Gen

variable {K : Type*} [Field K]

lemma invP_invP (Q : K[X][X]) (k M : ℕ) : invP (invP Q k M) k M = Q := by
  ext1 i
  rw [coeff_invP, coeff_invP, reflect_reflect]

lemma shiftP_zero' (Q : K[X][X]) : shiftP Q 0 = Q := by
  ext1 i
  rw [coeff_shiftP, map_zero, add_zero, comp_X]

lemma natDegree_shiftP_eq (Q : K[X][X]) (c : K) : (shiftP Q c).natDegree = Q.natDegree := by
  apply le_antisymm (natDegree_shiftP_le Q c)
  have h := natDegree_shiftP_le (shiftP Q c) (-c)
  rwa [show shiftP (shiftP Q c) (-c) = Q by
    have := shiftP_shiftP Q (-c); rwa [neg_neg] at this] at h

lemma shiftP_monic {Q : K[X][X]} (hQ : Q.Monic) (c : K) : (shiftP Q c).Monic := by
  rw [Monic, leadingCoeff, natDegree_shiftP_eq, coeff_shiftP, hQ.coeff_natDegree, one_comp]

/-- **Irreducibility from the inverted curve.** -/
theorem irreducible_of_mob (F : K[X][X]) (hF : F.Monic) (hn : 0 < F.natDegree) (a : K) (k M : ℕ)
    (hM : ∀ i ≤ (shiftP F a).natDegree, ((shiftP F a).coeff i).natDegree + k * i ≤ M)
    (hGm : (invP (shiftP F a) k M).Monic)
    (hGn : (invP (shiftP F a) k M).natDegree = F.natDegree)
    (hirr : Irreducible (invP (shiftP F a) k M)) : Irreducible F := by
  classical
  set F' := invP (shiftP F a) k M with hF'
  set E := AlgebraicClosure (RatFunc K)
  set x' : E := algebraMap (RatFunc K) E RatFunc.X with hx'
  have htr : Transcendental K x' :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc K) E).injective).mpr RatFunc.transcendental_X
  obtain ⟨y', hy'⟩ : ∃ y' : E, (F'.map (aeval x').toRingHom).eval y' = 0 := by
    have hdeg : (F'.map (aeval x').toRingHom).degree ≠ 0 := by
      rw [hGm.degree_map, degree_eq_natDegree hGm.ne_zero, hGn]
      exact_mod_cast hn.ne'
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
    exact ⟨z, hz⟩
  set S' : CurveData K E := ⟨x', y', F', htr, hGm, Curves.MT.curve_irr x' y' htr F' hGm hirr hy', hy'⟩
  -- the degree bounds of `F′`
  have hM' : ∀ i ≤ (shiftP S'.F 0).natDegree, ((shiftP S'.F 0).coeff i).natDegree + k * i ≤ M := by
    intro i hi
    change i ≤ (shiftP F' 0).natDegree at hi
    rw [shiftP_zero'] at hi ⊢
    change (F'.coeff i).natDegree + k * i ≤ M
    have hi' : i ≤ (shiftP F a).natDegree := by
      rw [natDegree_shiftP_eq]; rw [hGn] at hi; exact hi
    have hki : k * i ≤ M := by have := hM i hi'; omega
    rw [hF', coeff_invP]
    have := natDegree_reflect_le (N := M - k * i) (p := (shiftP F a).coeff i)
    have h2 : ((shiftP F a).coeff i).natDegree ≤ M - k * i := by have := hM i hi'; omega
    omega
  have hinv : invP (shiftP S'.F 0) k M = shiftP F a := by
    change invP (shiftP F' 0) k M = _
    rw [shiftP_zero', hF', invP_invP]
  have hGm' : (invP (shiftP S'.F 0) k M).Monic := by rw [hinv]; exact shiftP_monic hF a
  have hGn' : (invP (shiftP S'.F 0) k M).natDegree = S'.F.natDegree := by
    rw [hinv, natDegree_shiftP_eq]; exact hGn.symm
  set S'' := mobCurve S' 0 k M hM' hGm' hGn' with hS''
  have hS''F : S''.F = shiftP F a := hinv
  -- `F` vanishes at `(x″ + a, y″)` and nothing of lower degree does
  refine Curves.MT.irreducible_of_no_small_factor (aeval (S''.x + algebraMap K E a)).toRingHom F hF
    hn S''.y ?_ ?_
  · have h := S''.root
    rw [hS''F] at h
    have h2 := ev_shiftP F a S''.x S''.y
    unfold ev at h2
    rw [← h2]; exact h
  · intro G hG hGy
    have h2 := ev_shiftP G a S''.x S''.y
    unfold ev at h2
    rw [← h2] at hGy
    have hdeg : (shiftP G a).natDegree < S''.F.natDegree := by
      rw [hS''F, natDegree_shiftP_eq, natDegree_shiftP_eq]; exact hG
    have h0 := S''.irr _ hdeg hGy
    have := shiftP_shiftP G (-a)
    rw [neg_neg] at this
    rw [← this, h0]
    ext1 i
    rw [coeff_shiftP]; simp

end Gen

universe u

/-- **Geometric irreducibility transfers back through the inversion** `x′ = 1/(x − a)`. -/
theorem geomIrr_of_mob (Fq : BPoly ℚ) (hmon : (toB Fq).Monic) (hn : 0 < (toB Fq).natDegree) (a : ℚ)
    (k M : ℕ) (hinv : InvOK k M 0 (shiftB Fq a)) (hGm : (toB (invB (shiftB Fq a) k M)).Monic)
    (hGn : (toB (invB (shiftB Fq a) k M)).natDegree = (toB Fq).natDegree)
    (h : GeomIrr.{u} (invB (shiftB Fq a) k M)) : GeomIrr.{u} Fq := fun K _ _ ↦ by
  set ψ := mapRingHom (algebraMap ℚ K) with hψ
  have hinj : Function.Injective ψ := map_injective _ (algebraMap ℚ K).injective
  have e : (toB (invB (shiftB Fq a) k M)).map ψ =
      invP (shiftP ((toB Fq).map ψ) (algebraMap ℚ K a)) k M := by
    rw [toB_invB _ _ _ hinv, toB_shiftB, ← shiftP_map, ← invP_map]
  have hsh : shiftP ((toB Fq).map ψ) (algebraMap ℚ K a) = (shiftP (toB Fq) a).map ψ := by
    rw [shiftP_map]
  have hb := invBound_of_invOK _ _ _ hinv
  rw [toB_shiftB] at hb
  refine irreducible_of_mob ((toB Fq).map ψ) (hmon.map _)
    (by rw [natDegree_map_eq_of_injective hinj]; exact hn) (algebraMap ℚ K a) k M (fun i hi ↦ ?_)
    (by rw [← e]; exact hGm.map _)
    (by rw [← e, natDegree_map_eq_of_injective hinj, hGn, natDegree_map_eq_of_injective hinj])
    (by rw [← e]; exact h K)
  rw [hsh, natDegree_map_eq_of_injective hinj] at hi
  rw [hsh, coeff_map, coe_mapRingHom, natDegree_map_eq_of_injective (algebraMap ℚ K).injective]
  exact hb i hi

/-- **A single place above a rational point certifies geometric irreducibility**: the inverted curve
at `x = a` has a single place at infinity (`wtC`). -/
theorem geomIrr_of_wt_mob (Fq : BPoly ℚ) (hmon : (toB Fq).Monic) (hn : 0 < (toB Fq).natDegree)
    (a : ℚ) (k M : ℕ) (hinv : InvOK k M 0 (shiftB Fq a))
    (hGm : (toB (invB (shiftB Fq a) k M)).Monic)
    (hGn : (toB (invB (shiftB Fq a) k M)).natDegree = (toB Fq).natDegree)
    (hlen : (toB (invB (shiftB Fq a) k M)).natDegree = (invB (shiftB Fq a) k M).length - 1)
    (hwt : wtC (invB (shiftB Fq a) k M) = true) : GeomIrr.{u} Fq :=
  geomIrr_of_mob Fq hmon hn a k M hinv hGm hGn (geomIrr_of_wt _ hGm hlen hwt)

/-- **A complete certificate of geometric irreducibility**: the subset certificate
(`irrSubsetCheck`, a split point `x = a` with branches over a number field `ℚ[γ]/(M)`) proves
irreducibility over every field containing `ℚ[γ]/(M)` (`irrSubsetCheck_spec`), in particular over
the algebraic closure of any `K ⊇ ℚ`, hence over `K`. Such a certificate exists for every
geometrically irreducible curve (at any point where the fibre splits). -/
theorem geomIrr_of_subsets (Fq : BPoly ℚ) (MM : CPoly ℚ) [Fact (Irreducible (toPoly MM))]
    (hmon : (toB Fq).Monic) (n d : ℕ) (hn : (toB Fq).natDegree = n) (hn0 : 0 < n)
    (a : NFC.NF MM) (c : BranchCert (NFC.NF MM))
    (h : irrSubsetCheck (Fq.map (·.map (algebraMap ℚ (NFC.NF MM)))) n d a c = true) :
    GeomIrr.{u} Fq := fun K _ _ ↦ by
  set Kb := AlgebraicClosure K
  set ψ : NFC.NF MM →+* Kb := (IsAlgClosed.lift (R := ℚ) (S := NFC.NF MM) (M := Kb)).toRingHom
  have hφ : (toB (Fq.map (·.map (algebraMap ℚ (NFC.NF MM))))) =
      (toB Fq).map (mapRingHom (algebraMap ℚ (NFC.NF MM))) := toB_mapL _ _
  have hinjM : Function.Injective (mapRingHom (algebraMap ℚ (NFC.NF MM))) :=
    map_injective _ (algebraMap ℚ (NFC.NF MM)).injective
  have hmon' : (toB (Fq.map (·.map (algebraMap ℚ (NFC.NF MM))))).Monic := by
    rw [hφ]; exact hmon.map _
  have hn' : (toB (Fq.map (·.map (algebraMap ℚ (NFC.NF MM))))).natDegree = n := by
    rw [hφ, natDegree_map_eq_of_injective hinjM, hn]
  have h1 := irrSubsetCheck_spec _ n d a c h hmon' hn' hn0 ψ
  rw [hφ, Polynomial.map_map, mapRingHom_comp,
    (Subsingleton.elim _ _ : ψ.comp (algebraMap ℚ (NFC.NF MM)) =
      (algebraMap K Kb).comp (algebraMap ℚ K)),
    ← mapRingHom_comp, ← Polynomial.map_map] at h1
  exact Monic.irreducible_of_irreducible_map (mapRingHom (algebraMap K Kb)) _ (hmon.map _) h1

/-- Geometric irreducibility gives irreducibility over `ℚ(x)`. -/
lemma irr_ratFunc_of_geomIrr (Fq : BPoly ℚ) (hmon : (toB Fq).Monic) (h : GeomIrr.{0} Fq) :
    Irreducible ((toB Fq).map (algebraMap ℚ[X] (RatFunc ℚ))) := by
  have hQ := h ℚ
  have hid : (toB Fq).map (mapRingHom (algebraMap ℚ ℚ)) = toB Fq := by
    rw [Algebra.algebraMap_self, mapRingHom_id, Polynomial.map_id]
  rw [hid] at hQ
  exact (hmon.irreducible_iff_irreducible_map_fraction_map).mp hQ

/-- **Any geometrically irreducible base curve is irreducible over the code field** (the `Fact`
needed by `kzDecide_bc_correct`, from any `GeomIrr` certificate, e.g. `geomIrr_of_subsets`). -/
theorem fKc_irr_geom (Fq : BPoly ℚ) (hmon : (toB Fq).Monic) (h : GeomIrr.{0} Fq) :
    Irreducible (toPoly (fKc Fq)) :=
  fKc_irr_of_ratFunc Fq hmon (irr_ratFunc_of_geomIrr Fq hmon h)

/-- **Over a linear base, a geometrically irreducible `Q` is irreducible over the code field.** -/
theorem qK_irr_linear_geom (c0 : CPoly ℚ) (Fq : BPoly ℚ) (hmon : (toB Fq).Monic)
    (h : GeomIrr.{0} Fq) :
    haveI : Fact (Irreducible (toPoly (fKc [c0, [1]]))) := ⟨fKc_irr_linear c0⟩
    Irreducible (toPoly (qK [c0, [1]] (qOfB Fq))) :=
  qK_irr_linear_of_ratFunc c0 Fq hmon (irr_ratFunc_of_geomIrr Fq hmon h)

end Curves.MT
