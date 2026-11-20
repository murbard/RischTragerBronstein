import RischTragerBronstein.Algebraic.NFNorm
import RischTragerBronstein.Computable.KronComplete
import RischTragerBronstein.Computable.HexpDegenerateDecide

/-!
# Roots in a number field (Trager's norm method)

For `K = ℚ[θ]/(f)` and a squarefree `g ∈ K[x]`: find `s` with `N_s = Norm(g(x − sθ))` squarefree,
factor `N_s` over `ℚ` (Kronecker), and for each factor `M` take `G = gcd_K(g, M(x + sθ))`; a linear
`G` gives a root. `rootsIn`: every returned element is a root (`rootsIn_sound`), and every root is
returned (`rootsIn_complete`).
-/

open Polynomial CPoly

namespace NFC

variable (f : CPoly ℚ) [hf : Fact (Irreducible (toPoly f))]

/-- The generator `θ`. -/
def gen : NF f := mk f [0, 1]

/-- `M(x + t)` over `K`. -/
def shiftQ (M : CPoly ℚ) (t : NF f) : CPoly (NF f) :=
  M.foldr (fun c acc ↦ add [((c : ℚ) : NF f)] (mul [t, 1] acc)) []

/-- The roots read off the factors of the norm. -/
def rootsFromN (g : CPoly (NF f)) (s : ℚ) (N : CPoly ℚ) : List (NF f) :=
  (Kron.factorQ (Kron.degC N + 1) N).filterMap fun M ↦
    let G := trim (egcd g (shiftQ f M ((s : NF f) * gen f))).1
    if degT G = 1 then some (-(G.getD 0 0) / G.getD 1 0) else none

/-- The search bound for `s`. -/
def sBound (g : CPoly (NF f)) : ℕ := (degT f * (g.length - 1)) ^ 2 + 2

/-- **The roots of `g` in `K`** (`none` if no admissible `s` is found). -/
def rootsIn (g : CPoly (NF f)) : Option (List (NF f)) :=
  (List.range (sBound f g)).findSome? fun i : ℕ ↦
    if squarefreeCheck (normPoly f g ((i : ℚ) + 1)) then
      some (rootsFromN f g ((i : ℚ) + 1) (normPoly f g ((i : ℚ) + 1)))
    else none


/-! ### Embeddings into `ℚ̄` -/

/-- The algebraic closure of `ℚ`. -/
abbrev QB := AlgebraicClosure ℚ

lemma evAt_mk {θ : QB} (hθ : aeval θ (toPoly f) = 0) (l : CPoly ℚ) :
    evAt f θ (mk f l) = aeval θ (toPoly l) := by
  obtain ⟨q, hq⟩ := norm_dvd f l
  have : aeval θ (toPoly (norm f l)) = aeval θ (toPoly l) := by
    rw [← sub_eq_zero, ← map_sub, hq, map_mul, hθ, zero_mul]
  exact this

/-- The embedding `K → ℚ̄`, `θ ↦` a root of `f`. -/
noncomputable def rho {θ : QB} (hθ : aeval θ (toPoly f) = 0) : NF f →+* QB :=
  (AdjoinRoot.lift (algebraMap ℚ QB) θ (by rwa [aeval_def] at hθ)).comp (toARHom f)

lemma rho_apply {θ : QB} (hθ : aeval θ (toPoly f) = 0) (c : NF f) :
    rho f hθ c = evAt f θ c := by
  simp only [rho, RingHom.comp_apply, toARHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    toAR, AdjoinRoot.lift_mk]
  rfl

lemma rho_gen {θ : QB} (hθ : aeval θ (toPoly f) = 0) : rho f hθ (gen f) = θ := by
  rw [rho_apply, gen, evAt_mk f hθ]; simp [CPoly.toPoly]

lemma rho_injective {θ : QB} (hθ : aeval θ (toPoly f) = 0) : Function.Injective (rho f hθ) :=
  (rho f hθ).injective

lemma map_rho (g : CPoly (NF f)) {θ : QB} (hθ : aeval θ (toPoly f) = 0) :
    (toPoly g).map (rho f hθ) = toPoly (g.map (evAt f θ)) := by
  induction g with
  | nil => simp [CPoly.toPoly]
  | cons c t ih =>
    rw [toPoly_cons, List.map_cons, toPoly_cons, Polynomial.map_add, Polynomial.map_mul, map_C,
      Polynomial.map_X, ih, rho_apply]

/-- `f` over `ℚ̄`. -/
noncomputable abbrev fL : QB[X] := (toPoly f).map (algebraMap ℚ QB)

lemma fL_splits : (fL f).Splits := IsAlgClosed.splits _

lemma root_of_mem {θ : QB} (h : θ ∈ (fL f).roots) : aeval θ (toPoly f) = 0 := by
  have := (mem_roots'.mp h).2
  rwa [IsRoot, eval_map_algebraMap] at this

/-- The factor of the norm at `θ`: `g_θ(x − sθ)`. -/
noncomputable def normFac (g : CPoly (NF f)) (s : ℚ) (θ : QB) : QB[X] :=
  (toPoly (g.map (evAt f θ))).comp (X - C (algebraMap ℚ QB s * θ))

lemma squarefree_map_of {N : ℚ[X]} (h : Squarefree N) :
    Squarefree (N.map (algebraMap ℚ QB)) :=
  ((PerfectField.separable_iff_squarefree).mpr h).map.squarefree

/-- **No collisions**: if the norm is squarefree, two roots `z₁ + sθ₁ = z₂ + sθ₂` of conjugate
factors come from the same `θ`. -/
lemma no_collision (g : CPoly (NF f)) (s : ℚ) (hsq : Squarefree (toPoly (normPoly f g s)))
    {θ₁ θ₂ : QB} (h₁ : θ₁ ∈ (fL f).roots) (h₂ : θ₂ ∈ (fL f).roots) {z₁ z₂ : QB}
    (hz₁ : (toPoly (g.map (evAt f θ₁))).eval z₁ = 0) (hz₂ : (toPoly (g.map (evAt f θ₂))).eval z₂ = 0)
    (heq : z₁ + algebraMap ℚ QB s * θ₁ = z₂ + algebraMap ℚ QB s * θ₂) : θ₁ = θ₂ := by
  classical
  by_contra hne
  set w := z₁ + algebraMap ℚ QB s * θ₁
  have hd₁ : X - C w ∣ normFac f g s θ₁ := by
    rw [dvd_iff_isRoot, IsRoot, normFac, eval_comp]; simp [w, hz₁]
  have hd₂ : X - C w ∣ normFac f g s θ₂ := by
    rw [dvd_iff_isRoot, IsRoot, normFac, eval_comp, heq]; simp [hz₂]
  have hN := normPoly_map f (fL_splits f) g s
  have hsqL := squarefree_map_of hsq
  rw [hN] at hsqL
  have hprod : ((fL f).roots.map (normFac f g s)).prod =
      normFac f g s θ₁ * (normFac f g s θ₂ *
        ((((fL f).roots.erase θ₁).erase θ₂).map (normFac f g s)).prod) := by
    rw [← Multiset.prod_map_erase h₁, ← Multiset.prod_map_erase
      (Multiset.mem_erase_of_ne (Ne.symm hne) |>.mpr h₂)]
  have hdvd : (X - C w) * (X - C w) ∣ C (algebraMap ℚ QB (lcT f) ^ eDeg f g) *
      ((fL f).roots.map fun θ ↦ (toPoly (g.map (evAt f θ))).comp
        (X - C (algebraMap ℚ QB s * θ))).prod := by
    change _ ∣ C _ * ((fL f).roots.map (normFac f g s)).prod
    rw [hprod]
    exact Dvd.dvd.mul_left (mul_dvd_mul hd₁ (Dvd.dvd.mul_right hd₂ _)) _
  exact (irreducible_X_sub_C w).not_isUnit (hsqL _ hdvd)


lemma toPoly_shiftQ (M : CPoly ℚ) (t : NF f) :
    toPoly (shiftQ f M t) = ((toPoly M).map (algebraMap ℚ (NF f))).comp (X + C t) := by
  induction M with
  | nil => simp [shiftQ, CPoly.toPoly]
  | cons c M ih =>
    rw [shiftQ, List.foldr_cons, ← shiftQ, toPoly_add, toPoly_mul, ih,
      show toPoly (c :: M) = C c + X * toPoly M from toPoly_cons c M,
      Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_X, add_comp, mul_comp, C_comp,
      X_comp]
    simp only [CPoly.toPoly, eq_ratCast, map_one, mul_zero, add_zero]
    ring

lemma eval_shiftQ (M : CPoly ℚ) (t α : NF f) :
    (toPoly (shiftQ f M t)).eval α = aeval (α + t) (toPoly M) := by
  rw [toPoly_shiftQ, eval_comp, eval_map_algebraMap]; simp

lemma map_shiftQ {θ : QB} (hθ : aeval θ (toPoly f) = 0) (M : CPoly ℚ) (t : NF f) (z : QB) :
    ((toPoly (shiftQ f M t)).map (rho f hθ)).eval z = aeval (z + rho f hθ t) (toPoly M) := by
  rw [toPoly_shiftQ, Polynomial.map_comp, Polynomial.map_map, eval_comp,
    show (rho f hθ).comp (algebraMap ℚ (NF f)) = algebraMap ℚ QB from RingHom.ext_rat _ _,
    eval_map_algebraMap]
  simp


lemma exists_root_fL : ∃ θ, θ ∈ (fL f).roots := by
  have hdeg : 0 < (fL f).natDegree := by
    rw [natDegree_map_eq_of_injective (algebraMap ℚ QB).injective]
    exact Nat.pos_of_ne_zero fun h ↦ hf.out.not_isUnit (isUnit_iff_degree_eq_zero.mpr (by
      rw [degree_eq_natDegree (f_ne_zero f), h]; rfl))
  rw [(fL_splits f).natDegree_eq_card_roots] at hdeg
  exact Multiset.card_pos_iff_exists_mem.mp hdeg

/-- Conjugating a root: `σ` sends `θ ↦ σθ` and `rho θ c ↦ rho (σθ) c`. -/
lemma sigma_evAt (σ : QB ≃ₐ[ℚ] QB) (θ : QB) (c : NF f) : σ (evAt f θ c) = evAt f (σ θ) c := by
  simp only [evAt]
  rw [← Polynomial.aeval_algHom_apply]

lemma sigma_root (σ : QB ≃ₐ[ℚ] QB) {θ : QB} (h : θ ∈ (fL f).roots) : σ θ ∈ (fL f).roots := by
  have hθ := root_of_mem f h
  rw [mem_roots ((Polynomial.map_ne_zero_iff (algebraMap ℚ QB).injective).mpr (f_ne_zero f)), IsRoot,
    eval_map_algebraMap]
  have := Polynomial.aeval_algHom_apply (σ : QB →ₐ[ℚ] QB) θ (toPoly f)
  rw [hθ, map_zero] at this
  exact this

lemma eval_map_evAt (σ : QB ≃ₐ[ℚ] QB) (g : CPoly (NF f)) (θ z : QB) :
    (toPoly (g.map (evAt f (σ θ)))).eval (σ z) = σ ((toPoly (g.map (evAt f θ))).eval z) := by
  induction g with
  | nil => simp [CPoly.toPoly]
  | cons c t ih =>
    simp only [List.map_cons, toPoly_cons, eval_add, eval_C, eval_mul, eval_X, ih, map_add, map_mul,
      sigma_evAt]

set_option maxHeartbeats 3200000 in
/-- **Every root is found** (for an `s` with squarefree norm). -/
theorem mem_rootsFromN (g : CPoly (NF f)) (hgsq : Squarefree (toPoly g)) (s : ℚ)
    (hsq : Squarefree (toPoly (normPoly f g s))) {α : NF f} (hα : (toPoly g).eval α = 0) :
    α ∈ rootsFromN f g s (normPoly f g s) := by
  classical
  have hg0 : toPoly g ≠ 0 := hgsq.ne_zero
  obtain ⟨θ₁, hθ₁⟩ := exists_root_fL f
  have hθ := root_of_mem f hθ₁
  set ι := rho f hθ
  set t : NF f := (s : NF f) * gen f
  set γ : NF f := α + t
  have hιt : ι t = algebraMap ℚ QB s * θ₁ := by
    simp only [t, map_mul, map_ratCast, ι, rho_gen]; simp
  have hιg : ∀ z, (toPoly (g.map (evAt f θ₁))).eval z = ((toPoly g).map ι).eval z := by
    intro z; rw [map_rho]
  -- `N(ιγ) = 0`
  set N := normPoly f g s
  have hN0 : aeval (ι γ) (toPoly N) = 0 := by
    rw [← eval_map_algebraMap, normPoly_map f (fL_splits f), eval_mul, eval_multiset_prod]
    apply mul_eq_zero_of_right
    apply Multiset.prod_eq_zero
    refine Multiset.mem_map.mpr ⟨_, Multiset.mem_map_of_mem _ hθ₁, ?_⟩
    simp only [eval_comp, eval_sub, eval_X, eval_C]
    rw [show ι γ - algebraMap ℚ QB s * θ₁ = ι α by simp [γ, hιt], hιg, eval_map, eval₂_at_apply,
      hα, map_zero]
  -- the minimal polynomial of `ιγ` is one of the factors of `N`
  have hint : IsIntegral ℚ (ι γ) := Algebra.IsIntegral.isIntegral _
  have hM0dvd : minpoly ℚ (ι γ) ∣ toPoly N := minpoly.dvd ℚ _ hN0
  have hN0' : toPoly N ≠ 0 := hsq.ne_zero
  have hNpos : 0 < (toPoly N).natDegree := by
    have := natDegree_le_of_dvd hM0dvd hN0'
    have := minpoly.natDegree_pos hint
    omega
  obtain ⟨hirr, k, hk, hNk⟩ := Kron.factorQ_spec (Kron.degC N + 1) N hNpos
    (by rw [Kron.degC_eq N hN0']; omega)
  have hprime : Prime (minpoly ℚ (ι γ)) := (minpoly.irreducible hint).prime
  have hdvdprod : minpoly ℚ (ι γ) ∣ ((Kron.factorQ (Kron.degC N + 1) N).map toPoly).prod := by
    rw [hNk] at hM0dvd
    exact (hprime.dvd_or_dvd hM0dvd).resolve_left fun h ↦ hprime.not_unit
      (isUnit_of_dvd_unit h (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hk)))
  obtain ⟨Mp, hMp_mem, hMp⟩ := hprime.dvd_prod_iff.mp hdvdprod
  obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hMp_mem
  have hMirr : Irreducible (toPoly M) := Kron.irredQ_sound M (hirr M hM)
  have hassoc : Associated (minpoly ℚ (ι γ)) (toPoly M) :=
    (minpoly.irreducible hint).associated_of_dvd hMirr hMp
  have hMι : aeval (ι γ) (toPoly M) = 0 := by
    obtain ⟨q, hq⟩ := hassoc.dvd
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  have hMγ : aeval γ (toPoly M) = 0 := by
    apply ι.injective
    rw [map_zero, ← hMι]
    exact (Polynomial.aeval_algHom_apply ι.toRatAlgHom γ _).symm
  -- the gcd
  set S := shiftQ f M t
  have hSα : (toPoly S).eval α = 0 := by rw [eval_shiftQ]; exact hMγ
  set G := trim (egcd g S).1
  have hGd : toPoly G ∣ toPoly g ∧ toPoly G ∣ toPoly S := by rw [toPoly_trim]; exact egcd_dvd g S
  have hXG : X - C α ∣ toPoly G := by
    rw [toPoly_trim]; exact dvd_egcd g S (dvd_iff_isRoot.mpr hα) (dvd_iff_isRoot.mpr hSα)
  have hG0 : toPoly G ≠ 0 := fun h0 ↦ hg0 (zero_dvd_iff.mp (h0 ▸ hGd.1))
  -- every root of `ι(G)` is `ια`
  have hGL : ∀ z, ((toPoly G).map ι).IsRoot z → z = ι α := by
    intro z hz
    have hgz : ((toPoly g).map ι).eval z = 0 := by
      obtain ⟨q, hq⟩ := hGd.1
      rw [hq, Polynomial.map_mul, eval_mul, hz.eq_zero, zero_mul]
    have hSz : ((toPoly S).map ι).eval z = 0 := by
      obtain ⟨q, hq⟩ := hGd.2
      rw [hq, Polynomial.map_mul, eval_mul, hz.eq_zero, zero_mul]
    rw [map_shiftQ, hιt] at hSz
    have hM0z : aeval (z + algebraMap ℚ QB s * θ₁) (minpoly ℚ (ι γ)) = 0 := by
      obtain ⟨q, hq⟩ := hassoc.symm.dvd
      rw [hq, map_mul, hSz, zero_mul]
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' hint.isAlgebraic hM0z
    have hσγ : σ (ι γ) = σ (ι α) + algebraMap ℚ QB s * σ θ₁ := by
      simp only [γ, map_add, hιt, map_mul, AlgEquiv.commutes]
    have hroot' : (toPoly (g.map (evAt f (σ θ₁)))).eval (σ (ι α)) = 0 := by
      rw [eval_map_evAt, hιg, eval_map, eval₂_at_apply, hα, map_zero, map_zero]
    have hz' : (toPoly (g.map (evAt f θ₁))).eval z = 0 := by rw [hιg]; exact hgz
    have heqθ := no_collision f g s hsq (sigma_root f σ hθ₁) hθ₁ hroot' hz' (by rw [← hσγ, hσ])
    have hfix : σ (ι α) = ι α := by
      simp only [ι]; rw [rho_apply, sigma_evAt, heqθ]
    have hz2 : z = σ (ι γ) - algebraMap ℚ QB s * θ₁ := by rw [hσ]; ring
    rw [hz2, hσγ, heqθ, hfix]; ring
  -- hence `G` is linear
  have hGsq : Squarefree (toPoly G) := hgsq.squarefree_of_dvd hGd.1
  have hGLsep : ((toPoly G).map ι).Separable :=
    ((PerfectField.separable_iff_squarefree).mpr hGsq).map
  have hGL0 : (toPoly G).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hG0
  have hspl : ((toPoly G).map ι).Splits := IsAlgClosed.splits _
  have hnd := (nodup_roots_iff_of_splits hGL0 hspl).mpr hGLsep
  have hsub : ((toPoly G).map ι).roots ≤ {ι α} := by
    rw [Multiset.le_iff_subset hnd]
    intro z hz
    rw [Multiset.mem_singleton]
    exact hGL z ((mem_roots hGL0).mp hz)
  have hcard : ((toPoly G).map ι).natDegree ≤ 1 := by
    rw [hspl.natDegree_eq_card_roots]
    simpa using Multiset.card_le_card hsub
  rw [natDegree_map_eq_of_injective ι.injective] at hcard
  have hge : 1 ≤ (toPoly G).natDegree := by
    have := natDegree_le_of_dvd hXG hG0
    rwa [natDegree_X_sub_C] at this
  have hdeg1 : (toPoly G).natDegree = 1 := le_antisymm hcard hge
  -- read off the root
  have hc1 : (toPoly G).coeff 1 ≠ 0 := by
    rw [← hdeg1]; exact leadingCoeff_ne_zero.mpr hG0
  have hlin := eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg1)
  have hev : (toPoly G).eval α = 0 := (dvd_iff_isRoot.mp hXG)
  rw [hlin] at hev
  simp only [eval_add, eval_mul, eval_C, eval_X] at hev
  have hval : -(G.getD 0 0) / G.getD 1 0 = α := by
    rw [← coeff_toPoly, ← coeff_toPoly]
    field_simp
    linear_combination -hev
  unfold rootsFromN
  refine List.mem_filterMap.mpr ⟨M, hM, ?_⟩
  simp only
  rw [if_pos (by rw [degT_eq]; exact hdeg1)]
  exact congrArg some hval


omit hf in
lemma separable_comp_X_sub_C {F : Type*} [Field F] {p : F[X]} (hp : p.Separable) (a : F) :
    (p.comp (X - C a)).Separable := by
  obtain ⟨u, v, h⟩ := hp
  refine ⟨u.comp (X - C a), v.comp (X - C a), ?_⟩
  rw [derivative_comp, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  have := congrArg (fun P : F[X] ↦ P.comp (X - C a)) h
  simpa only [add_comp, mul_comp, one_comp] using this

lemma fL_nodup : (fL f).roots.Nodup :=
  nodup_roots (hf.out.separable.map)

lemma gθ_separable (g : CPoly (NF f)) (hgsq : Squarefree (toPoly g)) {θ : QB}
    (hθ : θ ∈ (fL f).roots) : (toPoly (g.map (evAt f θ))).Separable := by
  rw [← map_rho f g (root_of_mem f hθ)]
  exact ((PerfectField.separable_iff_squarefree).mpr hgsq).map

lemma card_roots_gθ (g : CPoly (NF f)) (θ : QB) :
    (toPoly (g.map (evAt f θ))).roots.card ≤ g.length - 1 := by
  refine (card_roots' _).trans ?_
  have := natDegree_toPoly_le_length (g.map (evAt f θ))
  rwa [List.length_map] at this

set_option maxHeartbeats 3200000 in
/-- **An admissible `s` exists in the search range.** -/
theorem exists_good_s (g : CPoly (NF f)) (hgsq : Squarefree (toPoly g)) :
    ∃ i < sBound f g, Squarefree (toPoly (normPoly f g ((i : ℚ) + 1))) := by
  classical
  set R := (fL f).roots
  set m := g.length - 1
  set n := (toPoly f).natDegree
  have hRcard : R.card = n := by
    rw [← (fL_splits f).natDegree_eq_card_roots,
      natDegree_map_eq_of_injective (algebraMap ℚ QB).injective]
  set B : QB → Multiset QB := fun θ ↦ (toPoly (g.map (evAt f θ))).roots
  set bad : Finset QB := (R.toFinset ×ˢ R.toFinset).biUnion fun p ↦
    if p.1 = p.2 then ∅ else
      ((B p.1).toFinset ×ˢ (B p.2).toFinset).image fun q ↦ (q.2 - q.1) / (p.1 - p.2)
  have hbad : bad.card ≤ (n * m) ^ 2 := by
    refine (Finset.card_biUnion_le).trans ?_
    have hterm : ∀ p ∈ R.toFinset ×ˢ R.toFinset, (if p.1 = p.2 then (∅ : Finset QB) else
        ((B p.1).toFinset ×ˢ (B p.2).toFinset).image fun q ↦ (q.2 - q.1) / (p.1 - p.2)).card ≤
        m * m := by
      intro p _
      split_ifs
      · simp
      · refine Finset.card_image_le.trans ?_
        rw [Finset.card_product]
        exact Nat.mul_le_mul ((Multiset.toFinset_card_le _).trans (card_roots_gθ f g _))
          ((Multiset.toFinset_card_le _).trans (card_roots_gθ f g _))
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_product, smul_eq_mul]
    have hR : R.toFinset.card ≤ n := (Multiset.toFinset_card_le _).trans hRcard.le
    calc R.toFinset.card * R.toFinset.card * (m * m) ≤ n * n * (m * m) :=
          Nat.mul_le_mul (Nat.mul_le_mul hR hR) le_rfl
      _ = (n * m) ^ 2 := by ring
  set T : Finset QB := (Finset.range (sBound f g)).image fun i : ℕ ↦ algebraMap ℚ QB ((i : ℚ) + 1)
  have hT : T.card = sBound f g := by
    rw [Finset.card_image_of_injective _ (fun a b h ↦ by
      have := (algebraMap ℚ QB).injective h
      exact_mod_cast (show (a : ℚ) = b by linarith)), Finset.card_range]
  have hlt : bad.card < T.card := by
    rw [hT, show sBound f g = (n * m) ^ 2 + 2 by simp [sBound, degT_eq, n, m]]; omega
  obtain ⟨x, hxT, hxbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxT
  refine ⟨i, Finset.mem_range.mp hi, ?_⟩
  set s : ℚ := (i : ℚ) + 1
  suffices hsep : ((toPoly (normPoly f g s)).map (algebraMap ℚ QB)).Separable from
    ((separable_map (algebraMap ℚ QB)).mp hsep).squarefree
  rw [normPoly_map f (fL_splits f)]
  have hprod : (R.map fun θ ↦ (toPoly (g.map (evAt f θ))).comp (X - C (algebraMap ℚ QB s * θ))).prod =
      ∏ θ ∈ R.toFinset, normFac f g s θ := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, (fL_nodup f).dedup]; rfl
  rw [hprod]
  have hc0 : algebraMap ℚ QB (lcT f) ^ eDeg f g ≠ 0 := by
    refine pow_ne_zero _ ((map_ne_zero_iff _ (algebraMap ℚ QB).injective).mpr ?_)
    rw [lcT_eq]; exact leadingCoeff_ne_zero.mpr (f_ne_zero f)
  refine ((separable_C _).mpr (isUnit_iff_ne_zero.mpr hc0)).mul ?_ (isCoprime_one_left.of_isCoprime_of_dvd_left
    (isUnit_iff_dvd_one.mp (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))))
  refine separable_prod' ?_ fun θ hθ ↦ separable_comp_X_sub_C (gθ_separable f g hgsq
    (Multiset.mem_toFinset.mp hθ)) _
  intro θ hθ θ' hθ' hne
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := QB) QB]
  intro a
  by_contra hboth
  push_neg at hboth
  obtain ⟨h1, h2⟩ := hboth
  simp only [normFac, coe_aeval_eq_eval, eval_comp, eval_sub,
    eval_X, eval_C] at h1 h2
  have hg1 : toPoly (g.map (evAt f θ)) ≠ 0 := (gθ_separable f g hgsq (Multiset.mem_toFinset.mp hθ)).ne_zero
  have hg2 : toPoly (g.map (evAt f θ')) ≠ 0 := (gθ_separable f g hgsq (Multiset.mem_toFinset.mp hθ')).ne_zero
  apply hxbad
  refine Finset.mem_biUnion.mpr ⟨(θ, θ'), Finset.mem_product.mpr ⟨hθ, hθ'⟩, ?_⟩
  simp only [if_neg hne]
  refine Finset.mem_image.mpr ⟨(a - algebraMap ℚ QB s * θ, a - algebraMap ℚ QB s * θ'),
    Finset.mem_product.mpr ⟨Multiset.mem_toFinset.mpr ((mem_roots hg1).mpr h1),
      Multiset.mem_toFinset.mpr ((mem_roots hg2).mpr h2)⟩, ?_⟩
  have : θ - θ' ≠ 0 := sub_ne_zero.mpr hne
  field_simp
  ring


/-- Every element returned by `rootsFromN` is a root of `g`. -/
lemma rootsFromN_sound (g : CPoly (NF f)) (s : ℚ) (N : CPoly ℚ) {r : NF f}
    (hr : r ∈ rootsFromN f g s N) : (toPoly g).eval r = 0 := by
  unfold rootsFromN at hr
  obtain ⟨M, -, hM⟩ := List.mem_filterMap.mp hr
  simp only at hM
  split_ifs at hM with hdeg
  simp only [Option.some.injEq] at hM
  set G := trim (egcd g (shiftQ f M ((s : NF f) * gen f))).1
  rw [degT_eq] at hdeg
  have hGd : toPoly G ∣ toPoly g := by rw [toPoly_trim]; exact (egcd_dvd _ _).1
  have hG0 : toPoly G ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hdeg; omega
  have hc1 : (toPoly G).coeff 1 ≠ 0 := by rw [← hdeg]; exact leadingCoeff_ne_zero.mpr hG0
  have hlin := eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)
  have hGr : (toPoly G).eval r = 0 := by
    rw [hlin, ← hM, ← coeff_toPoly, ← coeff_toPoly]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    field_simp
    ring
  obtain ⟨q, hq⟩ := hGd
  rw [hq, eval_mul, hGr, zero_mul]

/-- **Soundness of `rootsIn`.** -/
theorem rootsIn_sound (g : CPoly (NF f)) {rs : List (NF f)} (h : rootsIn f g = some rs) :
    ∀ r ∈ rs, (toPoly g).eval r = 0 := by
  unfold rootsIn at h
  obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at hi
  simp only [Option.some.injEq] at hi
  subst hi
  exact fun r hr ↦ rootsFromN_sound f g _ _ hr

/-- **Completeness of `rootsIn`**: for squarefree `g`, the search succeeds and returns every root
of `g` in `K`. -/
theorem rootsIn_complete (g : CPoly (NF f)) (hgsq : Squarefree (toPoly g)) :
    ∃ rs, rootsIn f g = some rs ∧ ∀ α : NF f, (toPoly g).eval α = 0 → α ∈ rs := by
  obtain ⟨i, hi, hsq⟩ := exists_good_s f g hgsq
  have hsome : (rootsIn f g).isSome := by
    unfold rootsIn
    rw [List.findSome?_isSome_iff]
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    rw [if_pos (squarefreeCheck_complete' hsq)]; rfl
  obtain ⟨rs, hrs⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨rs, hrs, fun α hα ↦ ?_⟩
  have h := hrs
  unfold rootsIn at h
  obtain ⟨j, -, hj⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at hj with hc
  simp only [Option.some.injEq] at hj
  subst hj
  exact mem_rootsFromN f g hgsq _ (squarefreeCheck_sound hc) hα

end NFC
