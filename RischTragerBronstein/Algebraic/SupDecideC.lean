import RischTragerBronstein.Algebraic.SupCands
import RischTragerBronstein.Algebraic.SupSupComplete
import RischTragerBronstein.Elementary.FiniteBase

/-!
# The complete superelliptic procedure

`superDecideMobMC` is `superDecideMobM` with the combined torsion oracle `torsOracleFB`, fed with
candidate points `(t_c, y_c t_cᵐ)` (`t_c = 1/(c − e)`, `y_cⁿ = f(c)`) of the transformed curve.
`superDecideMobQC` builds the field with `buildFieldAll` (candidates `candQ`); `superDecideCoverC`
reaches every `n ≥ 2` through the cover `sᵏ = x − c`.

* soundness: `superDecideMobMC_spec`, `superDecideMobQC_spec`, `superDecideCoverC_spec`.
* completeness (`SupDecideCComplete.lean`): they answer for all large bounds, with no hypothesis.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac NFC

namespace Sup

/-- The `n`-th root found by `rootsIn` (or `0`). -/
noncomputable def nthK (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (n : ℕ) (c : NF M) : NF M :=
  ((rootsIn M (xnMinus n c)).bind List.head?).getD 0

/-- The candidate points of the transformed curve. -/
noncomputable def candsMob (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (f : CPoly ℚ) (n : ℕ)
    (e : NF M) (cs : List ℚ) : List (NF M × NF M) :=
  cs.map fun c : ℚ ↦ (((c : NF M) - e)⁻¹,
    nthK M n (evalC (liftK (K := NF M) f) (c : NF M)) * ((c : NF M) - e)⁻¹ ^ ((f.length - 1) / n))

/-- **The procedure over a given field, with the complete oracle.** -/
noncomputable def superDecideMobMC (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (f : CPoly ℚ)
    (n : ℕ) (A : List (CPoly ℚ)) (D : CPoly ℚ) (B : ℕ) (cs : List ℚ) : Option Bool :=
  match rootsIn M (liftK (K := NF M) (xnMinus n 1)), rootsIn M (liftK (K := NF M) f) with
  | some rz, some (e :: _) =>
    match rz.find? (isPrimRoot M n) with
    | some ζ =>
      if isPrimRoot M n ζ then
        superFrontMob (liftK (K := NF M) f) n ζ
          (fun P ↦ torsOracleFB (nfRedAt (M := M) (M.map Rat.num)) (primesBelow B) B P n ζ
            (candsMob M f n e cs))
          (fun S ↦ (rootsIn M S).getD [])
          (fun c ↦ nthK M n c)
          e (A.map (liftK (K := NF M))) (liftK (K := NF M) D)
      else none
    | none => none
  | _, _ => none

/-- The number of candidates. -/
def candCount (f : CPoly ℚ) (n : ℕ) (D : CPoly ℚ) : ℕ :=
  n * f.length + f.length + n * (D.length + 1) + 1

/-- The fuel for the field loops. -/
def candFuel (f : CPoly ℚ) (n : ℕ) (D : CPoly ℚ) : ℕ :=
  n + f.length + (nbPartK f D).length + candCount f n D + 1

/-- **The complete procedure for `n ∣ deg f`.** -/
noncomputable def superDecideMobQC (f : CPoly ℚ) (n : ℕ) (A : List (CPoly ℚ)) (D : CPoly ℚ)
    (B : ℕ) : Option Bool :=
  match buildFieldAll f (nbPartK f D) n (candFuel f n D) (candQ f (candCount f n D)) with
  | none => none
  | some ⟨M, hM⟩ =>
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    superDecideMobMC M f n A D B (candQ f (candCount f n D))

/-- **The complete procedure for any `n ≥ 2`**, through the cover `sᵏ = x − c`. -/
noncomputable def superDecideCoverC (f : CPoly ℚ) (n : ℕ) (A : List (CPoly ℚ)) (D : CPoly ℚ)
    (B : ℕ) : Option Bool :=
  superDecideMobQC (compShiftPow f (coverC f) (coverK f n)) n
    (A.map (coverNum (coverC f) (coverK f n))) (compShiftPow D (coverC f) (coverK f n)) B

section Spec

open Differential IntermediateField

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `superDecideMobMC`.** -/
theorem superDecideMobMC_spec [IsAlgClosed Kc] (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]
    (hM : Kron.irredQ M = true) (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (f : CPoly ℚ) {n : ℕ} (hn : 0 < n) (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ)
    (B : ℕ) (cs : List ℚ) (ans : Bool) (h : superDecideMobMC M f n A D B cs = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  unfold superDecideMobMC at h
  split at h
  swap
  · cases h
  rename_i rz e _ _ _
  split at h
  swap
  · cases h
  rename_i ζ _
  split_ifs at h with hζ
  let ι : NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NF M) (M := Kc)).toRingHom
  have hmZ : toPoly M = (toPoly (M.map Rat.num)).map (Int.castRingHom ℚ) :=
    (Kron.polyZ_map M (int_of_irredQ hM)).symm
  have hyK : y ^ n = aeval x ((toPoly (liftK (K := NF M) f)).map ι) := by
    rw [map_liftK_comp]; exact hy
  have hspec := superFrontMob_spec hC x y hx ι (liftK (K := NF M) f) hn hyK hgen
    (isPrimRoot_spec hn hζ) _
    (fun P hsq hcop ↦ torsOracleFB_spec (nfRedAt (M := M) (M.map Rat.num))
      (fun p _ R hR ↦ nfRedAt_valid _ hmZ p R hR) (primesBelow B) B ζ _ hsq hcop)
    _ _ e _ _ ans h
  rw [hspec]
  have hA : ∀ j, (toPoly ((A.map (liftK (K := NF M))).getD j [])).map ι =
      (toPoly (A.getD j [])).map (algebraMap ℚ Kc) := fun j ↦ by
    rw [show ([] : CPoly (NF M)) = liftK (K := NF M) [] from rfl, List.getD_map, map_liftK_comp]
  simp only [hA, map_liftK_comp]

/-- **Correctness of `superDecideMobQC`.** -/
theorem superDecideMobQC_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (f : CPoly ℚ) {n : ℕ} (hn : 0 < n) (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ) (B : ℕ) (ans : Bool)
    (h : superDecideMobQC f n A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  unfold superDecideMobQC at h
  split at h
  · cases h
  rename_i M hM _
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  exact superDecideMobMC_spec M hM hC x y hx f hn hy hgen A D B _ ans h

set_option maxHeartbeats 3200000 in
/-- **Correctness through a cover** `sᵏ = x − c` (any `c ∈ ℚ`, `k ≥ 1`). -/
theorem superDecideMobQC_cover_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0) (x y : E)
    (hx : x′ = 1) (f : CPoly ℚ) {n : ℕ} (hn : 0 < n)
    (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ) (c : ℚ) {k : ℕ}
    (hk : 0 < k) (B : ℕ) (ans : Bool)
    (h : superDecideMobQC (compShiftPow f c k) n (A.map (coverNum c k)) (compShiftPow D c k) B
      = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  classical
  set cE : E := algebraMap Kc E (algebraMap ℚ Kc c) with hcE
  have hxc : x - cE ≠ 0 := x_sub_const_ne hC x hx _
  -- the cover
  set Q : E[X] := X ^ k - C (x - cE) with hQ
  have hQdeg : 0 < Q.degree := by
    rw [hQ, degree_X_pow_sub_C hk]; exact_mod_cast hk
  obtain ⟨g0, hg0irr, hg0dvd⟩ := exists_irreducible_of_degree_pos hQdeg
  have hlc : g0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0irr.ne_zero
  set q := g0 * C (g0.leadingCoeff)⁻¹ with hq
  have hqmon : q.Monic := monic_mul_leadingCoeff_inv hg0irr.ne_zero
  have hqirr : Irreducible q :=
    (irreducible_mul_isUnit (isUnit_C.mpr (inv_ne_zero hlc).isUnit)).mpr hg0irr
  have hqdvd : q ∣ Q := dvd_trans ⟨C g0.leadingCoeff, by
    rw [hq, mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]⟩ hg0dvd
  haveI : Fact (Irreducible q) := ⟨hqirr⟩
  haveI : Fact q.Monic := ⟨hqmon⟩
  haveI : FiniteDimensional E (AdjoinRoot q) := (AdjoinRoot.powerBasis hqirr.ne_zero).finite
  haveI : CharZero (AdjoinRoot q) :=
    charZero_of_injective_algebraMap (algebraMap E (AdjoinRoot q)).injective
  set s : AdjoinRoot q := AdjoinRoot.root q with hsdef
  have hs : s ^ k = algebraMap E (AdjoinRoot q) (x - cE) := by
    have h0 : aeval s Q = 0 := by
      obtain ⟨r, hr⟩ := hqdvd
      rw [hr, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
    rw [hQ] at h0
    simp only [map_sub, map_pow, aeval_X, aeval_C] at h0
    rw [map_sub]
    exact sub_eq_zero.mp h0
  set x' : AdjoinRoot q := algebraMap E (AdjoinRoot q) x with hx'
  set y' : AdjoinRoot q := algebraMap E (AdjoinRoot q) y with hy'
  have hs0 : s ≠ 0 := by
    intro h0
    have : s ^ k = 0 := by rw [h0, zero_pow hk.ne']
    rw [hs] at this
    exact hxc ((algebraMap E (AdjoinRoot q)).injective (by rw [this, map_zero]))
  -- constants and derivations
  have hDAKc : DifferentialAlgebra Kc (AdjoinRoot q) :=
    ⟨fun r ↦ by
      rw [IsScalarTower.algebraMap_apply Kc E (AdjoinRoot q), deriv_algebraMap, deriv_algebraMap,
        hC, map_zero, map_zero, map_zero]⟩
  have hsd : ((k : AdjoinRoot q) * s ^ (k - 1)) * s′ = 1 := by
    have h1 := congrArg (fun z : AdjoinRoot q ↦ z′) hs
    simp only [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, deriv_algebraMap, map_sub, hx,
      hcE] at h1
    rw [hC, map_zero, map_zero, sub_zero, map_one] at h1
    rw [← h1]; ring
  set φ : AdjoinRoot q := (k : AdjoinRoot q) * s ^ (k - 1) with hφ
  have hφ0 : φ ≠ 0 := mul_ne_zero (by exact_mod_cast hk.ne') (pow_ne_zero _ hs0)
  let d0 : Derivation ℤ (AdjoinRoot q) (AdjoinRoot q) := Differential.deriv
  have hT : (rescale ⟨d0⟩ φ).deriv s = 1 := by
    show φ * d0 s = 1
    exact hsd
  have hDA' : @DifferentialAlgebra Kc (AdjoinRoot q) _ _ _ _ (rescale ⟨d0⟩ φ) :=
    @DifferentialAlgebra.mk Kc (AdjoinRoot q) _ _ _ _ (rescale ⟨d0⟩ φ) (fun r ↦ by
      show φ * d0 (algebraMap Kc (AdjoinRoot q) r) = algebraMap Kc (AdjoinRoot q) r′
      rw [hC, map_zero]
      have : d0 (algebraMap Kc (AdjoinRoot q) r) = 0 := by
        show (algebraMap Kc (AdjoinRoot q) r)′ = 0
        rw [hDAKc.deriv_algebraMap, hC, map_zero]
      rw [this, mul_zero])
  -- the substitution `x = c + sᵏ`
  have hxs : aeval s ((C c + X ^ k : ℚ[X]).map (algebraMap ℚ Kc)) = x' := by
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, map_C, map_add, map_pow,
      aeval_X, aeval_C]
    rw [hs, IsScalarTower.algebraMap_apply Kc E (AdjoinRoot q), ← hcE, ← map_add, hx']
    ring_nf
  have hsub : ∀ P : CPoly ℚ, aeval s ((toPoly (compShiftPow P c k)).map (algebraMap ℚ Kc)) =
      algebraMap E (AdjoinRoot q) (aeval x ((toPoly P).map (algebraMap ℚ Kc))) := fun P ↦ by
    rw [toPoly_compShiftPow, Polynomial.map_comp, aeval_comp, hxs, hx',
      aeval_algebraMap_apply]
  have hyC : y' ^ n = aeval s ((toPoly (compShiftPow f c k)).map (algebraMap ℚ Kc)) := by
    rw [hsub, ← hy, hy', map_pow]
  -- generation
  have hgen' : ∀ z : AdjoinRoot q, z ∈ Kc⟮s⟯⟮y'⟯ := by
    set M : IntermediateField Kc (AdjoinRoot q) := Kc⟮s, y'⟯ with hM
    have hsM : s ∈ M := subset_adjoin _ _ (by simp)
    have hyM : y' ∈ M := subset_adjoin _ _ (by simp)
    have hEM : ∀ e : E, algebraMap E (AdjoinRoot q) e ∈ M := by
      intro e
      have he := hgen e
      rw [← IntermediateField.mem_restrictScalars Kc, adjoin_simple_adjoin_simple] at he
      have hmap : (Kc⟮x, y⟯).map (IsScalarTower.toAlgHom Kc E (AdjoinRoot q)) ≤ M := by
        rw [IntermediateField.adjoin_map]
        rw [adjoin_le_iff]
        rintro v ⟨w, hw, rfl⟩
        rcases hw with hw | hw
        · rw [hw]
          change x' ∈ M
          rw [← hxs]
          simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, map_C, map_add,
            map_pow, aeval_X, aeval_C]
          exact add_mem (IntermediateField.algebraMap_mem _ _) (pow_mem hsM _)
        · rw [Set.mem_singleton_iff] at hw
          rw [hw]
          exact hyM
      exact hmap ⟨e, he, rfl⟩
    intro z
    rw [← IntermediateField.mem_restrictScalars Kc, adjoin_simple_adjoin_simple]
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [← AdjoinRoot.aeval_eq, aeval_eq_sum_range]
    refine sum_mem fun i _ ↦ ?_
    rw [Algebra.smul_def]
    exact mul_mem (hEM _) (pow_mem hsM _)
  -- run the procedure over the cover
  have hspec := @superDecideMobQC_spec Kc (AdjoinRoot q) _ _ _ _ (rescale ⟨d0⟩ φ) hDA' _ _ _ hC s y' hT
    (compShiftPow f c k) n hn hyC hgen' (A.map (coverNum c k)) (compShiftPow D c k) B ans h
  rw [hspec]
  set H := ∑ j ∈ Finset.range n, aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
      aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j with hH
  have hterm : ∀ j ∈ Finset.range n,
      aeval s ((toPoly ((A.map (coverNum c k)).getD j [])).map (algebraMap ℚ Kc)) /
          aeval s ((toPoly (compShiftPow D c k)).map (algebraMap ℚ Kc)) * y' ^ j =
        φ * algebraMap E (AdjoinRoot q) (aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
          aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
    intro j _
    rw [hsub D, map_mul, map_div₀, map_pow, ← hy']
    by_cases hj : j < A.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
        List.getD_eq_getElem _ _ hj, coverNum, toPoly_mul, toPoly_mul, toPoly_monomial,
        Polynomial.map_mul, Polynomial.map_mul, map_mul, map_mul]
      rw [hsub]
      simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero, map_C, aeval_C, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_X, map_one, one_mul, map_pow, aeval_X, map_natCast,
        eq_ratCast, Rat.cast_natCast]
      rw [hφ, Polynomial.map_natCast, map_natCast]
      ring
    · rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ (by omega)]
      simp [toPoly_nil]
  have hsum : (∑ j ∈ Finset.range n,
      aeval s ((toPoly ((A.map (coverNum c k)).getD j [])).map (algebraMap ℚ Kc)) /
          aeval s ((toPoly (compShiftPow D c k)).map (algebraMap ℚ Kc)) * y' ^ j) =
      φ * algebraMap E (AdjoinRoot q) H := by
    rw [hH, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [hsum]
  exact (hasElementaryIntegral_rescale_iff ⟨d0⟩ φ _ hφ0).trans (hasElementaryIntegral_finite_iff H)


/-- **Correctness of `superDecideCoverC`.** -/
theorem superDecideCoverC_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0) (x y : E)
    (hx : x′ = 1) (f : CPoly ℚ) {n : ℕ} (hn : 0 < n)
    (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ) (B : ℕ) (ans : Bool)
    (h : superDecideCoverC f n A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  have hk : 0 < coverK f n :=
    Nat.div_pos (Nat.gcd_le_left _ hn) (Nat.gcd_pos_of_pos_left _ hn)
  exact superDecideMobQC_cover_spec hC x y hx f hn hy hgen A D (coverC f) hk B ans h

end Spec

section Complete

theorem superDecideMobMC_eventually (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]
    (hM : Kron.irredQ M = true) (f : CPoly ℚ) {n : ℕ} (hn2 : 2 ≤ n) (hsq : Squarefree (toPoly f))
    (hfd : (toPoly f).natDegree = f.length - 1)
    (hd1 : 1 ≤ (toPoly f).natDegree) (hnd : n ∣ (toPoly f).natDegree) (A : List (CPoly ℚ))
    (D : CPoly ℚ) (hD : toPoly D ≠ 0) (hMF : MobField f (nbPartK f D) n M hM) (cs : List ℚ)
    (hcs : cs.Nodup) (hcf : ∀ c ∈ cs, (toPoly f).eval c ≠ 0)
    (hcr : ∀ c ∈ cs, ∃ y : NF M, y ^ n = aeval (c : NF M) (toPoly f))
    (hcard : n * (toPoly f).natDegree + (toPoly f).natDegree +
      n * ((toPoly D).natDegree + 1) < cs.length) :
    ∃ B0, ∀ B, B0 ≤ B → superDecideMobMC M f n A D B cs ≠ none := by
  classical
  have hn : 0 < n := by omega
  obtain ⟨hU, hF, hSr, hSn, hLc⟩ := hMF
  set S := nbPartK f D with hSdef
  have hX : Squarefree (toPoly (liftK (K := NF M) (xnMinus n (1 : ℚ)))) := by
    rw [toPoly_liftK]
    exact ((PerfectField.separable_iff_squarefree).mpr (sqf_xnMinus hn one_ne_zero)).map.squarefree
  obtain ⟨rz, hrz, hallz⟩ := rootsIn_complete M _ hX
  have hsqK : Squarefree (toPoly (liftK (K := NF M) f)) := by
    rw [toPoly_liftK]; exact ((PerfectField.separable_iff_squarefree).mpr hsq).map.squarefree
  obtain ⟨rf, hrf, hallf⟩ := rootsIn_complete M _ hsqK
  -- `f` has a root, so the list is non-empty
  obtain ⟨lf, hlf, hlflen, hlfr⟩ := hF
  obtain ⟨r0, hr0⟩ := List.exists_mem_of_length_pos (by omega : 0 < lf.length)
  have hr0f : r0 ∈ rf := hallf r0 (by rw [toPoly_liftK, eval_map_algebraMap]; exact hlfr r0 hr0)
  obtain ⟨e, rest, hrfe⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hr0f)
  have he : (toPoly (liftK (K := NF M) f)).eval e = 0 :=
    rootsIn_sound M _ hrf e (by rw [hrfe]; exact List.mem_cons_self)
  -- a primitive root of unity
  obtain ⟨ζ0, hζ0⟩ : ∃ ζ : NF M, IsPrimitiveRoot ζ n := by
    obtain ⟨l, hl, hlen, hr⟩ := hU
    refine exists_primRoot_of_roots hn hl hlen fun a ha ↦ ?_
    have := hr a ha
    rw [toPoly_xnMinus hn] at this
    simpa [sub_eq_zero] using this
  have hζ0mem : ζ0 ∈ rz := hallz ζ0 (by
    rw [toPoly_liftK, eval_map_algebraMap, toPoly_xnMinus hn]; simp [hζ0.pow_eq_one])
  have hprim : isPrimRoot M n ζ0 = true := by
    simp only [isPrimRoot, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, beq_iff_eq]
    exact ⟨hζ0.pow_eq_one, fun l hl ↦ by
      rcases Nat.eq_zero_or_pos l with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr (by simpa using hζ0.pow_ne_one_of_pos_of_lt hpos.ne' hl)⟩
  obtain ⟨ζ, hfind⟩ : ∃ ζ, rz.find? (isPrimRoot M n) = some ζ :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨ζ0, hζ0mem, hprim⟩)
  have hζp : isPrimRoot M n ζ = true := List.find?_some hfind
  have hζ : IsPrimitiveRoot ζ n := isPrimRoot_spec hn hζp
  -- the non-branch part over `K` splits over the roots of `S`
  have hSsqK : Squarefree (toPoly (liftK (K := NF M) S)) := by
    rw [toPoly_liftK]
    exact ((PerfectField.separable_iff_squarefree).mpr (squarefree_nbPartK f D hD)).map.squarefree
  obtain ⟨rs, hrs, hallS⟩ := rootsIn_complete M _ hSsqK
  set as := rs.dedup with has
  have hasnd : as.Nodup := List.nodup_dedup _
  have hrootS : ∀ α ∈ as, aeval α (toPoly S) = 0 := fun α hα ↦ by
    have := rootsIn_sound M _ hrs α (List.mem_dedup.mp hα)
    rwa [toPoly_liftK, eval_map_algebraMap] at this
  have hcount : (toPoly S).natDegree ≤ as.length := by
    obtain ⟨l, hl, hlen', hr⟩ := hSr
    have hsub : l ⊆ as := fun a ha ↦ List.mem_dedup.mpr (hallS a (by
      rw [toPoly_liftK, eval_map_algebraMap]; exact hr a ha))
    exact hlen'.trans (hl.subperm hsub).length_le
  obtain ⟨lc, hlc, hSK⟩ := nbPart_split f D hD as hasnd hrootS hcount
  have hSKroot : ∀ a, (toPoly (nbPartK (liftK (K := NF M) f) (liftK (K := NF M) D))).eval a = 0 →
      a ∈ as := by
    intro a ha
    rw [hSK, eval_mul, eval_C, eval_prod] at ha
    rcases mul_eq_zero.mp ha with h | h
    · exact absurd h hlc
    · obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hi
      rw [hi]; exact List.get_mem _ _
  have hDK : toPoly (liftK (K := NF M) D) ≠ 0 := by
    rw [toPoly_liftK]; exact (Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective).mpr hD
  have hmZ : toPoly M = (toPoly (M.map Rat.num)).map (Int.castRingHom ℚ) :=
    (Kron.polyZ_map M (int_of_irredQ hM)).symm
  have hnthF : ∀ c b : NF M, c ≠ 0 → b ^ n = c → nthK M n c ^ n = c := by
    intro c b hc hb
    have hxsq := sqf_xnMinus (K := NF M) hn hc
    obtain ⟨l, hl, hcl⟩ := rootsIn_complete M _ hxsq
    have hbl : b ∈ l := hcl b (by rw [toPoly_xnMinus hn]; simp [hb])
    obtain ⟨r, rest', hlr⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hbl)
    have hroot := rootsIn_sound M _ hl r (by rw [hlr]; exact List.mem_cons_self)
    rw [toPoly_xnMinus hn] at hroot
    simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hroot
    unfold nthK
    rw [hl, hlr]
    simpa using hroot
  have hfdK : (toPoly (liftK (K := NF M) f)).natDegree = (toPoly f).natDegree := by
    rw [toPoly_liftK, natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective]
  obtain ⟨P, A'', D'', m', a, b, lc', hPsq, hp1, hcopP, hpdP, hlcP, hD''0, hinj, hb0, hbf, hlc'0,
      hS', hPeq, hmD, heq⟩ :=
    superFrontMob_data (liftK f) hn2 hζ hsqK hfdK hnd hd1 e he
    (fun S ↦ (rootsIn M S).getD [])
    (fun Q hQ a ↦ by
      obtain ⟨l, hl, hc⟩ := rootsIn_complete M Q hQ
      rw [hl, Option.getD_some]
      exact ⟨hc a, rootsIn_sound M Q hl a⟩)
    (fun c ↦ nthK M n c) hnthF (A.map (liftK (K := NF M))) (liftK (K := NF M) D) hDK
    ⟨as, hasnd, by
      rw [hSK]
      refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
      refine (Finset.sum_le_sum fun i _ ↦ natDegree_X_sub_C_le _).trans ?_
      simp, fun a ha ↦ by
      rw [hSK, eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_univ ⟨as.idxOf a,
        List.idxOf_lt_length_of_mem ha⟩) (by simp), mul_zero]⟩
    (fun a ha ↦ by
      have ham := hSKroot a ha
      obtain ⟨b, hb⟩ := hSn a (hrootS a ham)
      exact ⟨b, by rw [hb, toPoly_liftK, eval_map_algebraMap]⟩)
    (by
      obtain ⟨c, hc⟩ := hLc
      exact ⟨c, by rw [hc, toPoly_liftK, leadingCoeff_map_of_injective
        (algebraMap ℚ (NF M)).injective]⟩)
  have hM1 : 0 < (toPoly (M.map Rat.num)).natDegree := by
    have hirr : Irreducible (toPoly M) := Fact.out
    have h0 : 0 < (toPoly M).natDegree :=
      natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
    rw [hmZ, natDegree_map_eq_of_injective (RingHom.injective_int _)] at h0
    exact h0
  -- values of `f` at rational points
  have hfc : ∀ c : ℚ, (toPoly (liftK (K := NF M) f)).eval (c : NF M) =
      (((toPoly f).eval c : ℚ) : NF M) := fun c ↦ by
    rw [toPoly_liftK, eval_map, ← eq_ratCast (algebraMap ℚ (NF M)) c, eval₂_at_apply,
      eq_ratCast]
  have hce : ∀ c ∈ cs, (c : NF M) - e ≠ 0 := by
    intro c hc h0
    have hce' : (c : NF M) = e := sub_eq_zero.mp h0
    apply hcf c hc
    have h2 : (toPoly (liftK (K := NF M) f)).eval (c : NF M) = 0 := by rw [hce']; exact he
    rw [hfc] at h2
    exact_mod_cast h2
  have hPlen : P.length = (toPoly f).natDegree := by
    rw [hPeq, List.length_reverse, length_R (liftK (K := NF M) f) e hfdK hd1 he]
  -- the candidate points lie on the transformed curve
  have hcv : ∀ c' ∈ candsMob M f n e cs, c'.2 ≠ 0 ∧ c'.2 ^ n = evalC P c'.1 := by
    intro c' hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    have hfK : evalC (liftK (K := NF M) f) (c : NF M) = (((toPoly f).eval c : ℚ) : NF M) := by
      rw [evalC_eq, hfc]
    have hfK0 : evalC (liftK (K := NF M) f) (c : NF M) ≠ 0 := by
      rw [hfK]; exact_mod_cast hcf c hc
    obtain ⟨y, hy⟩ := hcr c hc
    have hy' : y ^ n = evalC (liftK (K := NF M) f) (c : NF M) := by
      rw [hy, evalC_eq, toPoly_liftK, eval_map_algebraMap]
    have hyc := hnthF _ y hfK0 hy'
    have hyc0 : nthK M n (evalC (liftK (K := NF M) f) (c : NF M)) ≠ 0 := fun h0 ↦
      hfK0 (by rw [← hyc, h0, zero_pow hn.ne'])
    have ht0 : ((c : NF M) - e)⁻¹ ≠ 0 := inv_ne_zero (hce c hc)
    refine ⟨mul_ne_zero hyc0 (pow_ne_zero _ ht0), ?_⟩
    have hPt : evalC P ((c : NF M) - e)⁻¹ = ((c : NF M) - e)⁻¹ ^ (toPoly f).natDegree *
        evalC (liftK (K := NF M) f) (c : NF M) := by
      rw [evalC_eq, hPeq]
      have := P_eval (RingHom.id (NF M)) (liftK (K := NF M) f) e hfdK hd1 he ht0
      simp only [Polynomial.map_id, RingHom.id_apply] at this
      rw [this, evalC_eq, inv_inv, sub_add_cancel]
    have hm : (f.length - 1) / n * n = (toPoly f).natDegree := by
      rw [← hfd]; exact Nat.div_mul_cancel (hfd ▸ hnd)
    simp only
    rw [hPt, mul_pow, hyc, ← pow_mul, hm]
    ring
  have hcandcard : ((candsMob M f n e cs).map Prod.fst).toFinset.card = cs.length := by
    rw [List.toFinset_card_of_nodup]
    · simp [candsMob]
    · rw [candsMob, List.map_map]
      refine List.Nodup.map_on (fun c hc c' hc' h ↦ ?_) hcs
      simp only [Function.comp_apply, inv_inj] at h
      exact_mod_cast sub_left_injective h
  -- each query of the logarithmic part is eventually answered
  have hj : ∀ j, ∃ B0, ∀ B, B0 ≤ B → (torsOracleFB (nfRedAt (M := M) (M.map Rat.num))
      (primesBelow B) B P n ζ (candsMob M f n e cs)
      (gammaL (ptA n a) (ptB n ζ b) (mqJ n ζ a b (frontG P n A'' D'' a) j) 1)).isSome := by
    intro j
    refine torsOracleFB_eventually hmZ hM1 hn2 hpdP hlcP hPsq hcopP hζ _ hcv (ptA n a)
      (ptB n ζ b) _ (fun q ↦ ⟨pt_ne_zero hn hζ b hb0 q, by
        rw [evalC_eq]; exact pt_valid _ hζ a b hbf q⟩) (pt_injective hζ a b hinj hb0) ?_
    rw [hcandcard, hPlen]
    have hmD' : m' ≤ (toPoly D).natDegree + 1 := by
      rw [toPoly_liftK, natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective] at hmD
      exact hmD
    have h1 : ((n - 1) * ((toPoly f).natDegree - 1 - 1) + 1) / 2 ≤ n * (toPoly f).natDegree := by
      have : (n - 1) * ((toPoly f).natDegree - 1 - 1) ≤ n * (toPoly f).natDegree :=
        Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
      omega
    have h2 : m' * n ≤ n * ((toPoly D).natDegree + 1) := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ hmD'
    omega
  choose B0f hB0f using hj
  refine ⟨Finset.univ.sup B0f, fun B hB ↦ ?_⟩
  unfold superDecideMobMC
  rw [hrz, hrf, hrfe]
  simp only [hfind, hζp, if_true]
  rw [heq]
  exact superFront_ne_none_of P hn hPsq hp1 hζ _
    (torsOracleFB_spec (nfRedAt (M := M) (M.map Rat.num))
      (fun p _ R hR ↦ nfRedAt_valid _ hmZ p R hR) (primesBelow B) B ζ _ hPsq hcopP)
    A'' D'' hD''0 a b hinj hb0 hbf lc' hlc'0 hS'
    (fun j ↦ hB0f j B (le_trans (Finset.le_sup (Finset.mem_univ j)) hB))

end Complete

end Sup
