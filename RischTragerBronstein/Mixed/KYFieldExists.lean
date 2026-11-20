import RischTragerBronstein.Mixed.KYDecides

/-!
# The number field of `kyDecide` exists

For a primitive `n`-th root of unity and `n`-th roots of finitely many rationals `κ_q`, there is a
number field `ℚ[X]/(M)` (`M` monic irreducible) with codes `zN`, `gs` passing the checks of
`kyFieldOK` (`ky_field_exists`): take the splitting field of `(Xⁿ − 1) ∏ (Xⁿ − κ_q)`, a primitive
element and its minimal polynomial `M`, and write `ζ`, `γ_q` as polynomials in it. The checks are
read at the root (`fieldChecks_of_aeval`, through `normQ_eq_of_aeval`).
-/

open Polynomial CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

set_option linter.unusedSectionVars false

namespace Curves.MT

/-- The code of a rational polynomial. -/
noncomputable def ofPolyQ (p : ℚ[X]) : CPoly ℚ := (List.range (p.natDegree + 1)).map p.coeff

lemma getD_ofPolyQ (p : ℚ[X]) (i : ℕ) : (ofPolyQ p).getD i 0 = p.coeff i := by
  unfold ofPolyQ
  by_cases hi : i < p.natDegree + 1
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  · rw [List.getD_eq_default _ _ (by simp; omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma toPoly_ofPolyQ (p : ℚ[X]) : toPoly (ofPolyQ p) = p := by
  ext i; rw [coeff_toPoly, getD_ofPolyQ]

lemma length_ofPolyQ (p : ℚ[X]) : (ofPolyQ p).length = p.natDegree + 1 := by simp [ofPolyQ]

lemma trim_ofPolyQ (p : ℚ[X]) (hp : p ≠ 0) : CPoly.trim (ofPolyQ p) = ofPolyQ p := by
  have hlc : p.coeff p.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have e : ofPolyQ p = (List.range p.natDegree).map p.coeff ++ [p.coeff p.natDegree] := by
    rw [ofPolyQ, List.range_succ, List.map_append, List.map_singleton]
  rw [e, CPoly.trim, List.reverse_append]
  simp [List.dropWhile, hp]

section Checks

variable (M : CPoly ℚ) {F : Type*} [Field F] [CharZero F] (ρ : F) (hρ : aeval ρ (toPoly M) = 0)
  (hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0)

include hρ hmin in
lemma powQ_eq_of_aeval (hM0 : toPoly M ≠ 0) (a : CPoly ℚ) (k : ℕ) (c : ℚ)
    (h : aeval ρ (toPoly a) ^ k = (c : F)) : powQ M a k = NFK.norm M [c] := by
  obtain ⟨l, hl⟩ := powQ_norm M a k
  rw [hl]
  apply normQ_eq_of_aeval M ρ hmin hM0
  rw [← hl, aeval_powQ M ρ hρ, h, aeval_normQ M ρ hρ]
  simp [CPoly.toPoly]

include hρ hmin in
lemma powQ_ne_of_aeval (hM0 : toPoly M ≠ 0) (a : CPoly ℚ) (k : ℕ) (c : ℚ)
    (h : aeval ρ (toPoly a) ^ k ≠ (c : F)) : powQ M a k ≠ NFK.norm M [c] := by
  intro h'
  apply h
  have := congrArg (fun l ↦ aeval ρ (toPoly l)) h'
  simp only [aeval_powQ M ρ hρ, aeval_normQ M ρ hρ] at this
  rw [this]; simp [CPoly.toPoly]

end Checks

/-- An element of `ℚ⟮α⟯ = ⊤` is a polynomial in `α`. -/
lemma exists_poly_of_top {K : Type*} [Field K] [CharZero K] [FiniteDimensional ℚ K] (α : K)
    (hα : IntermediateField.adjoin ℚ {α} = ⊤) (z : K) : ∃ r : ℚ[X], aeval α r = z := by
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  have hz : z ∈ (IntermediateField.adjoin ℚ {α}).toSubalgebra := by rw [hα]; trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨r, hr⟩ := hz
  exact ⟨r, hr⟩

/-- **The field data of `kyDecide` exist**: for `n ≥ 1` and rationals `κs`, a monic irreducible `M`
and codes `zN` (a primitive `n`-th root of unity) and `gs` (`n`-th roots of the `κs`). -/
theorem ky_field_exists (n : ℕ) (hn : 0 < n) (κs : List ℚ) :
    ∃ M : CPoly ℚ, (toPoly M).Monic ∧ Irreducible (toPoly M) ∧ CPoly.trim M = M ∧
      1 < M.length ∧ ∃ zN : CPoly ℚ, ∃ gs : List (CPoly ℚ),
        powQ M zN n = NFK.norm M [1] ∧ (∀ k, 0 < k → k < n → powQ M zN k ≠ NFK.norm M [1]) ∧
        gs.length = κs.length ∧
        ∀ q < κs.length, powQ M (gs.getD q []) n = NFK.norm M [κs.getD q 0] := by
  classical
  let A := AlgebraicClosure ℚ
  -- a primitive root of unity and the roots
  haveI : NeZero (n : A) := ⟨by exact_mod_cast hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic n A)
    (by rw [degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hn).ne')
  have hζp : IsPrimitiveRoot ζ n := (isRoot_cyclotomic_iff).mp hζ
  have hγ : ∀ q : ℚ, ∃ γ : A, γ ^ n = (q : A) := fun q ↦ IsAlgClosed.exists_pow_nat_eq _ hn
  choose γ hγ using hγ
  -- the field generated
  set S : Set A := insert ζ (Set.range fun i : Fin κs.length ↦ γ (κs.get i)) with hS
  have hSint : ∀ s ∈ S, IsIntegral ℚ s := fun s _ ↦ Algebra.IsIntegral.isIntegral s
  let K := IntermediateField.adjoin ℚ S
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin hSint
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  set p := minpoly ℚ α with hp
  have hpmon : p.Monic := minpoly.monic hint
  have hpirr : Irreducible p := minpoly.irreducible hint
  have hp0 : p ≠ 0 := hpmon.ne_zero
  have hpdeg : 0 < p.natDegree := minpoly.natDegree_pos hint
  set M := ofPolyQ p with hM
  have hMp : toPoly M = p := toPoly_ofPolyQ p
  have hρ : aeval α (toPoly M) = 0 := by rw [hMp]; exact minpoly.aeval ℚ α
  have hmin := hmin_of_irr M α hρ (K := ℚ) (by
    rw [hMp, show algebraMap ℚ ℚ = RingHom.id ℚ from rfl, Polynomial.map_id]; exact hpirr)
  have hM0 : toPoly M ≠ 0 := by rw [hMp]; exact hp0
  -- the elements as polynomials in `α`
  have hζK : ζ ∈ K := IntermediateField.subset_adjoin ℚ S (Set.mem_insert _ _)
  have hγK : ∀ i : Fin κs.length, γ (κs.get i) ∈ K := fun i ↦
    IntermediateField.subset_adjoin ℚ S (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  obtain ⟨rz, hrz⟩ := exists_poly_of_top α hα ⟨ζ, hζK⟩
  have hrγ : ∀ i : Fin κs.length, ∃ r : ℚ[X], aeval α r = ⟨γ (κs.get i), hγK i⟩ :=
    fun i ↦ exists_poly_of_top α hα _
  choose rγ hrγ using hrγ
  have hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : K) n :=
    (IsPrimitiveRoot.map_iff_of_injective (f := K.val) K.val.injective).mp hζp
  refine ⟨M, by rw [hMp]; exact hpmon, by rw [hMp]; exact hpirr, trim_ofPolyQ p hp0,
    by rw [length_ofPolyQ]; omega, ofPolyQ rz,
    List.ofFn fun i : Fin κs.length ↦ ofPolyQ (rγ i), ?_, ?_, by simp, ?_⟩
  · apply powQ_eq_of_aeval M α hρ hmin hM0
    rw [toPoly_ofPolyQ, hrz, hζK'.pow_eq_one]; simp
  · intro k hk0 hkn
    apply powQ_ne_of_aeval M α hρ hmin hM0
    rw [toPoly_ofPolyQ, hrz]
    have := hζK'.pow_ne_one_of_pos_of_lt (by omega : k ≠ 0) hkn
    simpa using this
  · intro q hq
    apply powQ_eq_of_aeval M α hρ hmin hM0
    rw [List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_ofFn, toPoly_ofPolyQ, hrγ]
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    change γ (κs.get ⟨q, hq⟩) ^ n = ((((κs.getD q 0 : ℚ) : K)) : A)
    rw [hγ, List.getD_eq_getElem _ _ hq]
    exact (map_ratCast K.val _).symm

section Auto

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}

/-- **The converse of `kyFieldOK_spec`.** -/
lemma kyFieldOK_of [Fact (Irreducible (toPoly (fKc Fc)))] {m n j : ℕ} {g : LC m}
    {A B : GPoly (LC m)} {kt l : ℕ} {cs : List (LC m)} {M zN : CPoly ℚ} {gs : List (CPoly ℚ)}
    (htrim : CPoly.trim M = M) (hlen : 1 < M.length) (h1 : powQ M zN n = NFK.norm M [1])
    (h2 : ∀ k, 0 < k → k < n → powQ M zN k ≠ NFK.norm M [1]) (hgl : gs.length = cs.length)
    (hgn : ∀ q < cs.length,
      powQ M (gs.getD q []) n = NFK.norm M [kyK Fc ks m n j g A B kt l cs q]) :
    kyFieldOK Fc ks m n j g A B kt l cs M zN gs = true := by
  simp only [kyFieldOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  refine ⟨⟨⟨⟨⟨htrim, hlen⟩, h1⟩, fun k hk ↦ ?_⟩, hgl⟩, fun q hq ↦ hgn q hq⟩
  by_cases hk0 : k = 0
  · exact Or.inl hk0
  · exact Or.inr (h2 k (by omega) hk)

end Auto

universe u

open Differential in
/-- **Radicals over an exponential level with ordinary poles are decided, over a linear base,
with no field supplied**: there is a number field `ℚ[X]/(M)` with codes `zN`, `gs` such that, at
suitable residues and every large bound, `kyDecideL` answers correctly, outside the
Mordell–Weil case (`ky_decided` with the field of `ky_field_exists`). -/
theorem ky_decided_linear {c0 : CPoly ℚ} [Fact (Irreducible (toPoly (fKc [c0, [1]])))]
    {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
    {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
    [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
    (T : MTower [c0, [1]] ks Cc L)
    (hmon : (toB [c0, [1]]).Monic) (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC [c0, [1]] ks lv (m + 1) = true) {g : LC m}
    (hk : ks m = .exp g) (n j : ℕ)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO [c0, [1]] ks m) A = true)
    (hdegpos : 0 < degG (MO [c0, [1]] ks m) A) (hcop : Nat.Coprime n (degG (MO [c0, [1]] ks m) A))
    (θ : L) (hθ : θ ^ n = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (hn1 : 1 < n) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n) (hr0 : cs.length ≠ 0)
    (hok : kxOK [c0, [1]] ks m A B kt l cs = true) :
    ∃ (M : CPoly ℚ) (_ : Fact (Irreducible (toPoly (liftQ [c0, [1]] m M))))
      (_ : Fact (Irreducible (toPoly (liftQ [c0, [1]] (m + 1) M)))) (zN : CPoly ℚ)
      (gs : List (CPoly ℚ)),
      ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (∃ b, kyDecideL [c0, [1]] ks lv m n j g M zN gs A B kt l cs (primesBelow Bd) Bd rs =
          some b ∧
        (HasElementaryIntegral (T.ev (m + 1) ((B, kxDen [c0, [1]] ks m A kt l cs) : LC (m + 1)) *
          θ ^ j) ↔ b = true)) ∨
      ((((List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)).map
          (kyTorsC [c0, [1]] ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n)
            (primesBelow Bd) Bd rs)).any (· == some none) = true ∧
        ((krZ [c0, [1]] ks lv m n A = none ∧ ∃ ℓ, ℓ.Prime ∧ ℓ ∣ n ∧
            (krZ [c0, [1]] ks lv m ℓ A).isSome) ∨
          ∃ z, krZ [c0, [1]] ks lv m n A = some z ∧ ∃ k < n,
            kyZeroQ [c0, [1]] ks m n M A zN z (kyKap [c0, [1]] ks m n A z)
              (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs k = some none)) := by
  obtain ⟨M, hMmon, hMirr, htrim, hlen, zN, gs, h1, h2, hgl, hgn⟩ := ky_field_exists n (by omega)
    ((List.range cs.length).map fun q ↦ kyK [c0, [1]] ks m n j g A B kt l cs q)
  haveI i1 : Fact (Irreducible (toPoly (liftQ [c0, [1]] m M))) :=
    ⟨liftQ_irr_linear c0 M hMmon hMirr m⟩
  haveI i2 : Fact (Irreducible (toPoly (liftQ [c0, [1]] (m + 1) M))) :=
    ⟨liftQ_irr_linear c0 M hMmon hMirr (m + 1)⟩
  have hF : kyFieldOK [c0, [1]] ks m n j g A B kt l cs M zN gs = true := by
    refine kyFieldOK_of htrim hlen h1 h2 (by rw [hgl]; simp) fun q hq ↦ ?_
    have := hgn q (by simpa using hq)
    have hκ : ((List.range cs.length).map fun q ↦ kyK [c0, [1]] ks m n j g A B kt l cs q).getD q 0 =
        kyK [c0, [1]] ks m n j g A B kt l cs q := by
      rw [List.getD_eq_getElem _ _ (by simpa using hq)]; simp
    rwa [hκ] at this
  exact ⟨M, i1, i2, zN, gs, T.ky_decided hmon hdeg m hn hc hk n j M zN gs A hsqc hdegpos hcop θ hθ
    hgen B kt l cs hn1 hj0 hjn hjc hr0 hok (fun _ ↦ hF)⟩

end Curves.MT
