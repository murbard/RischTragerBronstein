import RischTragerBronstein.Algebraic.NFRoots
import RischTragerBronstein.Algebraic.EllDecideADK

/-!
# Adjoining a root: Trager's primitive element step

For `K = ℚ[θ]/(f)` and `h ∈ K[x]`, let `N_t` be the norm of `h(x − tθ)` and `M` an irreducible
factor of `N_t`. In `K' = ℚ[γ]/(M)` the element `θ` is recovered as the root of the linear
`G(y) = gcd(f(y), H(γ − t y, y))` (`H` the lift of `h` to `ℚ[x, y]`), and `α = γ − tθ` is a root of
`h` with `θ ↦ θ'`. `adjoinStep` computes `(θ', α')`. Every output satisfies `f(θ') = 0` and
`h_{θ'}(α') = 0` (`adjoinStep_sound`). For an admissible `t` the step always succeeds
(`adjoinStep_complete`).
-/

open Polynomial CPoly

namespace NFC

variable (f : CPoly ℚ) [hf : Fact (Irreducible (toPoly f))]
variable (M : CPoly ℚ) [hM : Fact (Irreducible (toPoly M))]

/-- `y ↦ H(γ − t y, y)` over `K' = ℚ[γ]/(M)`. -/
noncomputable def hPoly (h : CPoly (NF f)) (γ : NF M) (t : ℚ) : CPoly (NF M) :=
  h.foldr (fun c acc ↦ add (EllQuad.liftK c.1) (mul [γ, -(t : NF M)] acc)) []

/-- The evaluation of an element of `K` at `θ' ∈ K'`. -/
noncomputable def evK (θ' : NF M) (c : NF f) : NF M := EllQuad.evalQK c.1 θ'

/-- **The step**: `(θ', α')` with `f(θ') = 0` and `h_{θ'}(α') = 0`. -/
noncomputable def adjoinStep (h : CPoly (NF f)) (t : ℚ) : Option (NF M × NF M) :=
  let G := trim (egcd (EllQuad.liftK (K := NF M) f) (hPoly f M h (gen M) t)).1
  if degT G = 1 then
    let θ' := -(G.getD 0 0) / G.getD 1 0
    some (θ', gen M - (t : NF M) * θ')
  else none

lemma eval_hPoly (h : CPoly (NF f)) (γ : NF M) (t : ℚ) (y : NF M) :
    (toPoly (hPoly f M h γ t)).eval y =
      (toPoly (h.map (evK f M y))).eval (γ - (t : NF M) * y) := by
  induction h with
  | nil => simp [hPoly, CPoly.toPoly]
  | cons c r ih =>
    rw [hPoly, List.foldr_cons, ← hPoly, toPoly_add, toPoly_mul, eval_add, eval_mul, ih,
      EllQuad.toPoly_liftK, eval_map_algebraMap, List.map_cons, toPoly_cons, eval_add, eval_C,
      eval_mul, eval_X, evK, EllQuad.evalQK_eq]
    simp only [CPoly.toPoly, eval_add, eval_mul, eval_C, eval_X, mul_zero, add_zero]
    ring

/-- **Soundness of the step.** -/
theorem adjoinStep_sound (h : CPoly (NF f)) (t : ℚ) {θ' α' : NF M}
    (hs : adjoinStep f M h t = some (θ', α')) :
    aeval θ' (toPoly f) = 0 ∧ (toPoly (h.map (evK f M θ'))).eval α' = 0 := by
  unfold adjoinStep at hs
  simp only at hs
  split_ifs at hs with hdeg
  simp only [Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  set G := trim (egcd (EllQuad.liftK (K := NF M) f) (hPoly f M h (gen M) t)).1
  rw [degT_eq] at hdeg
  have hGd : toPoly G ∣ toPoly (EllQuad.liftK (K := NF M) f) ∧ toPoly G ∣ toPoly (hPoly f M h (gen M) t) := by
    rw [toPoly_trim]; exact egcd_dvd _ _
  have hG0 : toPoly G ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hdeg; omega
  have hc1 : (toPoly G).coeff 1 ≠ 0 := by rw [← hdeg]; exact leadingCoeff_ne_zero.mpr hG0
  have hlin := eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)
  have hGr : (toPoly G).eval (-(G.getD 0 0) / G.getD 1 0) = 0 := by
    rw [hlin, ← coeff_toPoly, ← coeff_toPoly]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    field_simp
    ring
  constructor
  · obtain ⟨q, hq⟩ := hGd.1
    have := congrArg (eval (-(G.getD 0 0) / G.getD 1 0)) hq
    rw [eval_mul, hGr, zero_mul, EllQuad.toPoly_liftK, eval_map_algebraMap] at this
    exact this
  · obtain ⟨q, hq⟩ := hGd.2
    have := congrArg (eval (-(G.getD 0 0) / G.getD 1 0)) hq
    rw [eval_mul, hGr, zero_mul, eval_hPoly] at this
    exact this


lemma map_eval_hPoly (h : CPoly (NF f)) (t : ℚ) {γ0 : QB} (hγ : aeval γ0 (toPoly M) = 0) (y : QB) :
    ((toPoly (hPoly f M h (gen M) t)).map (rho M hγ)).eval y =
      (toPoly (h.map (evAt f y))).eval (γ0 - algebraMap ℚ QB t * y) := by
  induction h with
  | nil => simp [hPoly, CPoly.toPoly]
  | cons c r ih =>
    rw [hPoly, List.foldr_cons, ← hPoly, toPoly_add, toPoly_mul, Polynomial.map_add,
      Polynomial.map_mul, eval_add, eval_mul, ih, EllQuad.toPoly_liftK, Polynomial.map_map,
      show (rho M hγ).comp (algebraMap ℚ (NF M)) = algebraMap ℚ QB from RingHom.ext_rat _ _,
      eval_map_algebraMap, List.map_cons,
      show toPoly (evAt f y c :: List.map (evAt f y) r) =
        C (evAt f y c) + X * toPoly (List.map (evAt f y) r) from toPoly_cons _ _,
      eval_add, eval_C, eval_mul, eval_X]
    simp only [CPoly.toPoly, Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_X,
      eval_add, eval_mul, eval_C, eval_X, mul_zero, add_zero, rho_gen, map_neg, map_ratCast,
      Polynomial.map_zero, eval_zero, Polynomial.map_neg, eval_neg]
    simp only [evAt, eq_ratCast]
    ring

set_option maxHeartbeats 3200000 in
/-- **Completeness of the step**: for `t` with squarefree norm and any irreducible factor `M` of
the norm, the linear gcd exists. -/
theorem adjoinStep_complete (h : CPoly (NF f)) (t : ℚ)
    (hN : Squarefree (toPoly (normPoly f h t))) (hMdvd : toPoly M ∣ toPoly (normPoly f h t)) :
    adjoinStep f M h t ≠ none := by
  classical
  obtain ⟨γ0, hγ0⟩ := exists_root_fL M
  have hγ := root_of_mem M hγ0
  set ι := rho M hγ
  -- `γ0` is a root of the norm
  have hNγ : ((toPoly (normPoly f h t)).map (algebraMap ℚ QB)).eval γ0 = 0 := by
    obtain ⟨q, hq⟩ := hMdvd
    rw [hq, Polynomial.map_mul, eval_mul, eval_map_algebraMap, hγ, zero_mul]
  rw [normPoly_map f (fL_splits f), eval_mul, eval_C, eval_multiset_prod] at hNγ
  have hc0 : algebraMap ℚ QB (lcT f) ^ eDeg f h ≠ 0 := by
    refine pow_ne_zero _ ((map_ne_zero_iff _ (algebraMap ℚ QB).injective).mpr ?_)
    rw [lcT_eq]; exact leadingCoeff_ne_zero.mpr (f_ne_zero f)
  have h0 := Multiset.prod_eq_zero_iff.mp ((mul_eq_zero.mp hNγ).resolve_left hc0)
  obtain ⟨v, hv, hv0⟩ := Multiset.mem_map.mp h0
  obtain ⟨θ0, hθ0, rfl⟩ := Multiset.mem_map.mp hv
  simp only [eval_comp, eval_sub, eval_X, eval_C] at hv0
  -- the gcd over `K'` and its image
  set F' := EllQuad.liftK (K := NF M) f
  set H' := hPoly f M h (gen M) t
  set G := trim (egcd F' H').1
  have hF'L : (toPoly F').map ι = fL f := by
    rw [EllQuad.toPoly_liftK, Polynomial.map_map]
    congr 1; exact RingHom.ext_rat _ _
  have hGd : toPoly G ∣ toPoly F' ∧ toPoly G ∣ toPoly H' := by rw [toPoly_trim]; exact egcd_dvd _ _
  have hF'0 : toPoly F' ≠ 0 := by
    rw [EllQuad.toPoly_liftK, Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective]
    exact f_ne_zero f
  have hG0 : toPoly G ≠ 0 := fun h0 ↦ hF'0 (zero_dvd_iff.mp (h0 ▸ hGd.1))
  have hGL0 : (toPoly G).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hG0
  -- `θ0` is a root of the image of `G`
  have hXG : X - C θ0 ∣ (toPoly G).map ι := by
    rw [dvd_iff_isRoot, IsRoot]
    have hbez : toPoly (egcd F' H').2.1 * toPoly F' + toPoly (egcd F' H').2.2 * toPoly H' =
        toPoly G := by rw [toPoly_trim]; exact egcd_spec F' H'
    rw [← hbez, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, eval_add, eval_mul,
      eval_mul, hF'L, map_eval_hPoly f M h t hγ]
    have h1 : (fL f).eval θ0 = 0 := (mem_roots'.mp hθ0).2
    rw [h1, hv0]; ring
  -- every root of the image of `G` is `θ0`
  have hroots : ∀ z, ((toPoly G).map ι).IsRoot z → z = θ0 := by
    intro z hz
    have hzf : (fL f).eval z = 0 := by
      obtain ⟨q, hq⟩ := hGd.1
      have := congrArg (fun P ↦ (P.map ι).eval z) hq
      simp only [Polynomial.map_mul, eval_mul, hz.eq_zero, zero_mul, hF'L] at this
      exact this
    have hzH : (toPoly (h.map (evAt f z))).eval (γ0 - algebraMap ℚ QB t * z) = 0 := by
      obtain ⟨q, hq⟩ := hGd.2
      have := congrArg (fun P ↦ (P.map ι).eval z) hq
      simp only [Polynomial.map_mul, eval_mul, hz.eq_zero, zero_mul] at this
      rw [map_eval_hPoly f M h t hγ] at this
      exact this
    have hzmem : z ∈ (fL f).roots :=
      (mem_roots ((Polynomial.map_ne_zero_iff (algebraMap ℚ QB).injective).mpr (f_ne_zero f))).mpr hzf
    exact no_collision f h t hN hzmem hθ0 hzH hv0 (by ring)
  -- hence `G` is linear
  have hFsep : (toPoly F').Separable := by
    rw [EllQuad.toPoly_liftK]; exact hf.out.separable.map
  have hGLsep : ((toPoly G).map ι).Separable := (hFsep.of_dvd hGd.1).map
  have hspl : ((toPoly G).map ι).Splits := IsAlgClosed.splits _
  have hnd := (nodup_roots_iff_of_splits hGL0 hspl).mpr hGLsep
  have hsub : ((toPoly G).map ι).roots ≤ {θ0} := by
    rw [Multiset.le_iff_subset hnd]
    intro z hz
    rw [Multiset.mem_singleton]
    exact hroots z ((mem_roots hGL0).mp hz)
  have hcard : ((toPoly G).map ι).natDegree ≤ 1 := by
    rw [hspl.natDegree_eq_card_roots]
    simpa using Multiset.card_le_card hsub
  have hge : 1 ≤ ((toPoly G).map ι).natDegree := by
    have := natDegree_le_of_dvd hXG hGL0
    rwa [natDegree_X_sub_C] at this
  rw [natDegree_map_eq_of_injective ι.injective] at hcard hge
  have hdeg1 : (toPoly G).natDegree = 1 := le_antisymm hcard hge
  unfold adjoinStep
  simp only
  rw [if_pos (show degT G = 1 by rw [degT_eq]; exact hdeg1)]
  simp


/-- The embedding `K → K'`, `θ ↦ θ'` (for a root `θ'` of `f`). -/
noncomputable def emb {θ' : NF M} (hθ' : aeval θ' (toPoly f) = 0) : NF f →+* NF M :=
  (AdjoinRoot.lift (algebraMap ℚ (NF M)) θ' (by rwa [aeval_def] at hθ')).comp (toARHom f)

lemma emb_apply {θ' : NF M} (hθ' : aeval θ' (toPoly f) = 0) (c : NF f) :
    emb f M hθ' c = evK f M θ' c := by
  simp only [emb, RingHom.comp_apply, toARHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    toAR, AdjoinRoot.lift_mk, evK, EllQuad.evalQK_eq]
  rfl

lemma emb_liftK {θ' : NF M} (hθ' : aeval θ' (toPoly f) = 0) (D : CPoly ℚ) :
    (toPoly (EllQuad.liftK (K := NF f) D)).map (emb f M hθ') = toPoly (EllQuad.liftK (K := NF M) D) := by
  rw [EllQuad.toPoly_liftK, EllQuad.toPoly_liftK, Polynomial.map_map]
  congr 1; exact RingHom.ext_rat _ _

lemma map_emb_eq {θ' : NF M} (hθ' : aeval θ' (toPoly f) = 0) (h : CPoly (NF f)) :
    (toPoly h).map (emb f M hθ') = toPoly (h.map (evK f M θ')) := by
  induction h with
  | nil => simp [CPoly.toPoly]
  | cons c t ih =>
    rw [toPoly_cons, List.map_cons, toPoly_cons, Polynomial.map_add, Polynomial.map_mul, map_C,
      Polynomial.map_X, ih, emb_apply]

end NFC
