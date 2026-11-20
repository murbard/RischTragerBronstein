import RischTragerBronstein.Mixed.KBCodes

/-!
# Changing the base curve: irreducibility over every constant field

`eisC Fc' c`: the new curve `Fc'(x, w)`, monic in `w`, is Eisenstein at `x = c` (all lower
coefficients vanish at `c`, the constant one simply). Then `Fc'` is irreducible over `K[x]` for every
field `K` of characteristic `0` (`eis_irr`), hence minimal for any root over `K(x)` (`curve_irr`):
the curve stays irreducible whatever the constants.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly CPoly.Kron Sup

/-- The Eisenstein check at `x = c`. -/
def eisC (Fc' : BPoly ℚ) (c : ℚ) : Bool :=
  (List.range (Fc'.length - 1)).all (fun i ↦ decide (evalC (Fc'.getD i []) c = 0)) &&
    decide (evalC (CPoly.deriv (Fc'.getD 0 [])) c ≠ 0)

/-- **Eisenstein**: `Fc'` is irreducible over `K[x]`. -/
theorem eis_irr (K : Type*) [Field K] [CharZero K] (Fc' : BPoly ℚ) (hmon : (toB Fc').Monic)
    (hlen : (toB Fc').natDegree = Fc'.length - 1) (hd : 0 < (toB Fc').natDegree) (c : ℚ)
    (h : eisC Fc' c = true) :
    Irreducible ((toB Fc').map (mapRingHom (algebraMap ℚ K))) := by
  simp only [eisC, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hlow, hder⟩ := h
  set F := (toB Fc').map (mapRingHom (algebraMap ℚ K)) with hF
  set P : Ideal K[X] := Ideal.span {X - Polynomial.C (c : K)} with hP
  have hprime : P.IsPrime :=
    (Ideal.span_singleton_prime (X_sub_C_ne_zero _)).mpr (prime_X_sub_C _)
  have hFm : F.Monic := hmon.map _
  have hFd : F.natDegree = (toB Fc').natDegree :=
    natDegree_map_eq_of_injective (Polynomial.map_injective _ (algebraMap ℚ K).injective) _
  have hcoeff : ∀ i, F.coeff i = (CPoly.toPoly (Fc'.getD i [])).map (algebraMap ℚ K) := fun i ↦ by
    rw [hF, coeff_map, coeff_toB]; rfl
  have hmemP : ∀ p : K[X], p ∈ P ↔ p.IsRoot (c : K) := fun p ↦ by
    rw [hP, Ideal.mem_span_singleton, dvd_iff_isRoot]
  have hev : ∀ p : ℚ[X], (p.map (algebraMap ℚ K)).eval (c : K) = ((p.eval c : ℚ) : K) := fun p ↦ by
    rw [eval_map, ← eq_ratCast (algebraMap ℚ K) c, eval₂_at_apply, eq_ratCast]
  refine (IsEisensteinAt.irreducible ⟨?_, ?_, ?_⟩ hprime hFm.isPrimitive (by rw [hFd]; exact hd))
  · rw [hFm.leadingCoeff, hmemP]
    simp [IsRoot]
  · intro i hi
    rw [hmemP, IsRoot, hcoeff, hev, ← evalC_eq, hlow i (by rw [hFd, hlen] at hi; exact hi)]
    simp
  · intro hsq
    rw [sq, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton, ← sq] at hsq
    obtain ⟨r, hr⟩ := hsq
    apply hder
    have h1 := congrArg (fun q ↦ (derivative q).eval (c : K)) hr
    simp only [derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C, sub_zero,
      eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self] at h1
    rw [hcoeff, derivative_map, hev, ← CPoly.toPoly_deriv, ← evalC_eq] at h1
    simp at h1
    exact_mod_cast h1

/-- **Eisenstein at a squarefree `p(x)`**, with Bezout certificates `a p + b p′ = 1` and
`c p + e r = 1` (`r = a₀ / p`): every lower coefficient is divisible by `p`, the constant one is
`p r`. -/
def eisPC (Fc' : BPoly ℚ) (p a b c e : CPoly ℚ) : Bool :=
  decide (1 < (CPoly.trim p).length) &&
  (List.range (Fc'.length - 1)).all (fun i ↦ decide (CPoly.trim (divMod (Fc'.getD i []) p).2 = [])) &&
  decide (CPoly.trim (CPoly.add (CPoly.mul a p) (CPoly.mul b (CPoly.deriv p))) = [1]) &&
  decide (CPoly.trim (CPoly.add (CPoly.mul c p) (CPoly.mul e (divMod (Fc'.getD 0 []) p).1)) = [1])

/-- **Eisenstein at a squarefree polynomial**: `Fc'` is irreducible over `K[x]` for every field
`K` of characteristic `0` (Eisenstein at a prime factor of `p` over `K`). -/
theorem eisP_irr (K : Type*) [Field K] [CharZero K] (Fc' : BPoly ℚ) (hmon : (toB Fc').Monic)
    (hlen : (toB Fc').natDegree = Fc'.length - 1) (hd : 0 < (toB Fc').natDegree)
    (p a b c e : CPoly ℚ) (h : eisPC Fc' p a b c e = true) :
    Irreducible ((toB Fc').map (mapRingHom (algebraMap ℚ K))) := by
  classical
  simp only [eisPC, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp1, hlow⟩, hab⟩, hce⟩ := h
  set ι := algebraMap ℚ K
  set P : K[X] := (toPoly p).map ι with hPdef
  set Rr : ℚ[X] := toPoly (divMod (Fc'.getD 0 []) p).1 with hRr
  -- the Bezout identities over `K`
  have hab' : (toPoly a).map ι * P + (toPoly b).map ι * derivative P = 1 := by
    have := congrArg toPoly hab
    rw [toPoly_trim, toPoly_add, toPoly_mul, toPoly_mul, CPoly.toPoly_deriv] at this
    rw [hPdef, derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add,
      this]
    simp
  have hce' : (toPoly c).map ι * P + (toPoly e).map ι * Rr.map ι = 1 := by
    have := congrArg toPoly hce
    rw [toPoly_trim, toPoly_add, toPoly_mul, toPoly_mul] at this
    rw [hPdef, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, this]
    simp
  -- `p` divides the lower coefficients; `a₀ = p r`
  have hdiv : ∀ i < Fc'.length - 1, toPoly (Fc'.getD i []) =
      toPoly (divMod (Fc'.getD i []) p).1 * toPoly p := fun i hi ↦ by
    have hs := divMod_spec (Fc'.getD i []) p
    have hr := congrArg toPoly (hlow i hi)
    rw [toPoly_trim, toPoly_nil] at hr
    rw [hs, hr, add_zero]
  set F := (toB Fc').map (mapRingHom ι) with hF
  have hFm : F.Monic := hmon.map _
  have hFd : F.natDegree = (toB Fc').natDegree :=
    natDegree_map_eq_of_injective (Polynomial.map_injective _ ι.injective) _
  have hcoeff : ∀ i, F.coeff i = (toPoly (Fc'.getD i [])).map ι := fun i ↦ by
    rw [hF, coeff_map, coeff_toB]; rfl
  -- a prime factor of `p` over `K`
  have hP0 : P ≠ 0 := by
    rw [hPdef, Ne, Polynomial.map_eq_zero_iff ι.injective]
    intro h0
    have := (CPoly.trim_eq_nil_iff p).mpr h0
    rw [this] at hp1; simp at hp1
  have hPu : ¬ IsUnit P := fun hu ↦ by
    have hdeg := natDegree_eq_zero_of_isUnit hu
    rw [hPdef, natDegree_map_eq_of_injective ι.injective] at hdeg
    have hne : CPoly.trim p ≠ [] := fun h0 ↦ by rw [h0] at hp1; simp at hp1
    have := CPoly.length_trim hne
    omega
  obtain ⟨q, hq, hqP⟩ := WfDvdMonoid.exists_irreducible_factor hPu hP0
  have hqp : Prime q := hq.prime
  set Pq : Ideal K[X] := Ideal.span {q} with hPq
  have hprime : Pq.IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hqp
  have hmem : ∀ f : K[X], f ∈ Pq ↔ q ∣ f := fun f ↦ Ideal.mem_span_singleton
  refine (IsEisensteinAt.irreducible ⟨?_, ?_, ?_⟩ hprime hFm.isPrimitive (by rw [hFd]; exact hd))
  · rw [hFm.leadingCoeff, hmem]
    exact fun h1 ↦ hq.not_isUnit (isUnit_of_dvd_one h1)
  · intro i hi
    rw [hmem, hcoeff, hdiv i (by rw [hFd, hlen] at hi; exact hi), Polynomial.map_mul]
    exact dvd_mul_of_dvd_right hqP _
  · intro hsq
    rw [sq, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton, ← sq] at hsq
    have h0 : F.coeff 0 = P * Rr.map ι := by
      rw [hcoeff, hdiv 0 (by rw [← hlen]; exact hd), Polynomial.map_mul, mul_comm]
    rw [h0] at hsq
    -- `q ∤ r`
    have hqR : ¬ q ∣ Rr.map ι := fun hq1 ↦ hq.not_isUnit (isUnit_of_dvd_one (by
      rw [← hce']; exact dvd_add (dvd_mul_of_dvd_right hqP _) (dvd_mul_of_dvd_right hq1 _)))
    -- so `q² ∣ p`
    have hq2 : q ^ 2 ∣ P := by
      have hcop : IsCoprime (q ^ 2) (Rr.map ι) :=
        IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd hq).mpr hqR)
      exact hcop.dvd_of_dvd_mul_right hsq
    -- then `q ∣ p′`, contradicting `a p + b p′ = 1`
    obtain ⟨t, ht⟩ := hq2
    have hqd : q ∣ derivative P :=
      ⟨Polynomial.C 2 * derivative q * t + q * derivative t, by
        rw [ht, derivative_mul, derivative_sq]; ring⟩
    apply hq.not_isUnit
    apply isUnit_of_dvd_one
    rw [← hab']
    exact dvd_add (dvd_mul_of_dvd_right hqP _) (dvd_mul_of_dvd_right hqd _)

universe u in
/-- **Geometric irreducibility**: irreducible over `K[x]` for every field `K ⊇ ℚ`. -/
def GeomIrr (Fc' : BPoly ℚ) : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K], Irreducible ((toB Fc').map (mapRingHom (algebraMap ℚ K)))

lemma geomIrr_of_eis (Fc' : BPoly ℚ) (hmon : (toB Fc').Monic)
    (hlen : (toB Fc').natDegree = Fc'.length - 1) (hd : 0 < (toB Fc').natDegree) (c : ℚ)
    (h : eisC Fc' c = true) : GeomIrr.{u} Fc' := fun K _ _ ↦ eis_irr K Fc' hmon hlen hd c h

lemma geomIrr_of_eisP (Fc' : BPoly ℚ) (hmon : (toB Fc').Monic)
    (hlen : (toB Fc').natDegree = Fc'.length - 1) (hd : 0 < (toB Fc').natDegree)
    (p a b c e : CPoly ℚ) (h : eisPC Fc' p a b c e = true) : GeomIrr.{u} Fc' :=
  fun K _ _ ↦ eisP_irr K Fc' hmon hlen hd p a b c e h

/-- **Minimality of a root of an irreducible monic curve equation** over `C(x)`. -/
theorem curve_irr {C L : Type*} [Field C] [Field L] [Algebra C L] (x y : L)
    (htr : Transcendental C x) (F : C[X][X]) (hF : F.Monic) (hirr : Irreducible F)
    (hy : (F.map (aeval x).toRingHom).eval y = 0) :
    ∀ G : C[X][X], G.natDegree < F.natDegree → (G.map (aeval x).toRingHom).eval y = 0 → G = 0 := by
  letI := algebraAdjoinSimple (F := C) x
  haveI := isFractionRing_adjoin_simple (F := C) x htr
  letI : Algebra C⟮x⟯ L := (IntermediateField.val C⟮x⟯).toRingHom.toAlgebra
  have hmapK : ∀ P : C[X][X], ((P.map (algebraMap C[X] C⟮x⟯)).map (algebraMap C⟮x⟯ L)) =
      P.map (aeval x).toRingHom := fun P ↦ by
    rw [Polynomial.map_map]
    congr 1
    refine RingHom.ext fun q ↦ ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    change ((algebraMap C[X] C⟮x⟯ q : C⟮x⟯) : L) = _
    rw [algebraMap_adjoinSimple]
  have hirr' : Irreducible (F.map (algebraMap C[X] C⟮x⟯)) :=
    (hF.irreducible_iff_irreducible_map_fraction_map).mp hirr
  have hF'm : (F.map (algebraMap C[X] C⟮x⟯)).Monic := hF.map _
  have hroot : aeval y (F.map (algebraMap C[X] C⟮x⟯)) = 0 := by
    rw [aeval_def, ← eval_map, hmapK]; exact hy
  have hmin : minpoly C⟮x⟯ y = F.map (algebraMap C[X] C⟮x⟯) :=
    (minpoly.eq_of_irreducible_of_monic hirr' hroot hF'm).symm
  intro G hG hGy
  by_contra hG0
  have hG'0 : G.map (algebraMap C[X] C⟮x⟯) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff (IsFractionRing.injective C[X] C⟮x⟯)]; exact hG0
  have hG'y : aeval y (G.map (algebraMap C[X] C⟮x⟯)) = 0 := by
    rw [aeval_def, ← eval_map, hmapK]; exact hGy
  have := natDegree_le_natDegree (minpoly.degree_le_of_ne_zero C⟮x⟯ y hG'0 hG'y)
  rw [hmin, natDegree_map_eq_of_injective (IsFractionRing.injective C[X] C⟮x⟯),
    natDegree_map_eq_of_injective (IsFractionRing.injective C[X] C⟮x⟯)] at this
  omega

end Curves.MT
