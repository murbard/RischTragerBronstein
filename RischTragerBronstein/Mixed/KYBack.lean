import RischTragerBronstein.Mixed.KYForward

/-!
# Radicals with poles over an exponential: the columns are elementary

The coordinates `col_f` of a column `zʲ Dⱼ/g ∈ K_{m+1} ⊗ N` are recovered from its images under
all embeddings of `N` (a Vandermonde system in the roots of `M`); each image, times `θʲ`, is
`(sʲ/n) ∑_k ζ^{(n−j)k} W(ζᵏỹ)′/W(ζᵏỹ)` (`twist_dlog`, `twist_sum`), elementary.
-/

open Polynomial Differential IntermediateField CPoly

set_option linter.unusedSectionVars false

namespace Differential

universe v

/-- An element algebraic over `ℚ` is a constant. -/
lemma deriv_eq_zero_of_isAlgebraic {F : Type*} [Field F] [CharZero F] [Differential F] (x : F)
    (hx : IsAlgebraic ℚ x) : x′ = 0 := by
  have hint : IsIntegral ℚ x := hx.isIntegral
  set μ := minpoly ℚ x
  have hsep : μ.Separable := (minpoly.irreducible hint).separable
  refine deriv_eq_zero_of_aeval_eq_zero (A := F) (μ.map (algebraMap ℚ F)) (fun i ↦ ?_) x ?_ ?_
  · rw [coeff_map, eq_ratCast]; exact Tower.NestP.deriv_ratCastK (K := F) _
  · rw [aeval_map_algebraMap]; exact minpoly.aeval ℚ x
  · rw [derivative_map, aeval_map_algebraMap]; exact hsep.aeval_derivative_ne_zero (minpoly.aeval ℚ x)

/-- **Adjoining `ⁿ√κ`, `ζₙ` and the roots of `M`**: a finite, hence elementary, extension. -/
theorem split_ext (E : Type v) [Field E] [Differential E] [CharZero E] (n : ℕ) (hn : 0 < n)
    (κ : ℚ) (hκ : κ ≠ 0) (P : ℚ[X]) (hP : P ≠ 0) :
    ∃ (E₂ : Type v) (_ : Field E₂) (_ : Differential E₂) (_ : Algebra E E₂)
      (_ : DifferentialAlgebra E E₂) (_ : CharZero E₂), IsElementaryExtension E E₂ ∧
        Algebra.IsAlgebraic E E₂ ∧
        (∃ s ζ : E₂, s ^ n = κ ∧ s′ = 0 ∧ IsPrimitiveRoot ζ n ∧ ζ′ = 0) ∧
        (P.map (algebraMap ℚ E₂)).Splits := by
  classical
  set q : E[X] := (X ^ n - Polynomial.C ((κ : ℚ) : E)) * cyclotomic n E * P.map (algebraMap ℚ E)
  letI : Differential (SplittingField q) := differentialFiniteDimensional E (SplittingField q)
  haveI : DifferentialAlgebra E (SplittingField q) := differentialAlgebraFiniteDimensional
  haveI : CharZero (SplittingField q) :=
    charZero_of_injective_algebraMap (algebraMap E (SplittingField q)).injective
  set F := SplittingField q
  have hf0 : X ^ n - Polynomial.C ((κ : ℚ) : E) ≠ 0 := X_pow_sub_C_ne_zero hn _
  have hc0 : cyclotomic n E ≠ 0 := cyclotomic_ne_zero n E
  have hP0 : P.map (algebraMap ℚ E) ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ E).injective).mpr hP
  have hq0 : q.map (algebraMap E F) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap E _).injective]
    exact mul_ne_zero (mul_ne_zero hf0 hc0) hP0
  have hs1 := (SplittingField.splits q).of_dvd hq0
    (Polynomial.map_dvd (algebraMap E F) (dvd_mul_of_dvd_left (dvd_mul_right (X ^ n -
      Polynomial.C ((κ : ℚ) : E)) _) _))
  have hs2 := (SplittingField.splits q).of_dvd hq0
    (Polynomial.map_dvd (algebraMap E F) (dvd_mul_of_dvd_left (dvd_mul_left (cyclotomic n E) _) _))
  have hs3 := (SplittingField.splits q).of_dvd hq0
    (Polynomial.map_dvd (algebraMap E F) (dvd_mul_left (P.map (algebraMap ℚ E)) _))
  obtain ⟨s, hs⟩ := hs1.exists_eval_eq_zero (by
    rw [degree_map, degree_X_pow_sub_C hn]; exact_mod_cast hn.ne')
  obtain ⟨ζ, hζ⟩ := hs2.exists_eval_eq_zero (by
    rw [degree_map, degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hn).ne')
  have hsn : s ^ n = (κ : F) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      eval_sub, eval_pow, eval_X, eval_C, map_ratCast] at hs
    linear_combination hs
  haveI : NeZero (n : F) := ⟨by exact_mod_cast hn.ne'⟩
  have hζp : IsPrimitiveRoot ζ n := by
    rw [map_cyclotomic] at hζ
    exact (isRoot_cyclotomic_iff).mp hζ
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    isElementaryExtension_of_finiteDimensional, Algebra.IsAlgebraic.of_finite _ _,
    ⟨s, ζ, hsn, ?_, hζp, LaurentSeries.deriv_root_of_unity hn hζp.pow_eq_one⟩, ?_⟩
  · have hs0 : s ≠ 0 := fun h ↦ by
      rw [h, zero_pow hn.ne'] at hsn; exact hκ (by exact_mod_cast hsn.symm)
    have hd := congrArg (fun w ↦ w′) hsn
    simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
    rw [Tower.NestP.deriv_ratCastK (K := F) κ] at hd
    have hn' : ((n : ℕ) : F) * s ^ (n - 1) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hn.ne') (pow_ne_zero _ hs0)
    have : ((n : ℕ) : F) * s ^ (n - 1) * s′ = 0 := by rw [← hd]; ring
    exact (mul_eq_zero.mp this).resolve_left hn'
  · rw [show algebraMap ℚ F = (algebraMap E F).comp (algebraMap ℚ E) from RingHom.ext_rat _ _,
      ← Polynomial.map_map]
    exact hs3

/-- **Solving a Vandermonde system with constant nodes**: the unknowns are constant combinations
of the right-hand sides. -/
lemma vandermonde_const {F : Type*} [Field F] [Differential F] (d : ℕ) (ρs : Fin d → F)
    (hρ : ∀ i, (ρs i)′ = 0) (hinj : Function.Injective ρs) (Xv S : Fin d → F)
    (hS : ∀ i, ∑ f : Fin d, Xv f * ρs i ^ (f : ℕ) = S i) :
    ∀ f, ∃ c : Fin d → F, (∀ i, (c i)′ = 0) ∧ Xv f = ∑ i, c i * S i := by
  classical
  set ρ0 : Fin d → constants F := fun i ↦ ⟨ρs i, hρ i⟩ with hρ0
  have hinj0 : Function.Injective ρ0 := fun i i' h ↦ hinj (congrArg Subtype.val h)
  set V0 := Matrix.vandermonde ρ0 with hV0
  have hdet : IsUnit V0.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj0)
  set ι := (constants F).subtype with hι
  set W : Matrix (Fin d) (Fin d) F := V0⁻¹.map ι with hW
  set V : Matrix (Fin d) (Fin d) F := V0.map ι with hV
  have hWV : W * V = 1 := by
    rw [hW, hV, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero ι)
      (map_one ι)]
  have hVX : V.mulVec Xv = S := by
    funext i
    rw [← hS i, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun f _ ↦ ?_
    simp only [hV, hV0, Matrix.map_apply, Matrix.vandermonde_apply, hρ0, map_pow]
    exact mul_comm _ _
  intro f
  refine ⟨fun i ↦ W f i, fun i ↦ ?_, ?_⟩
  · simp only [hW, Matrix.map_apply]
    exact (V0⁻¹ f i).2
  · have : Xv = W.mulVec S := by
      rw [← hVX, Matrix.mulVec_mulVec, hWV, Matrix.one_mulVec]
    rw [this, Matrix.mulVec, dotProduct]

end Differential

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 1600000 in
/-- **One embedding of `N`**: the image of the column under `X ↦ ρ`, times `θʲ`, is
`(sʲ/n) ∑_k ζ^{(n−j)k} W(ζᵏỹ)′/W(ζᵏỹ)` with `ỹ = zθ/s`, hence elementary. -/
theorem ky_root_hei (m n j : ℕ) (hn : 0 < n) (hj : j < n) (hTr : T.Tr (m + 1)) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (htrim : CPoly.trim M = M) (hlen : 1 < M.length)
    (Ah : GPoly (LC m)) (z : LC m) (θ : L) (κ : ℚ) (hκ : κ ≠ 0) (hθ0 : θ ≠ 0)
    (hz0 : T.ev m z ≠ 0)
    (hAh : T.ev (m + 1) (pcP Fc ks m Ah) = T.ev m z ^ n * ((κ⁻¹ : ℚ) : L) * θ ^ n)
    (hzj : T.ev (m + 1) (pcP Fc ks m [powC (MO Fc ks m) z j]) = T.ev m z ^ j)
    (W : BPoly (NFM Fc m M)) (cols : List (LC (m + 1)))
    (h : kyColM Fc ks m n M Ah z j W = some cols)
    {E₂ : Type u} [Field E₂] [CharZero E₂] [Differential E₂] [Algebra L E₂]
    [DifferentialAlgebra L E₂] (s ζ : E₂) (hsn : s ^ n = κ) (hs' : s′ = 0)
    (hζ : IsPrimitiveRoot ζ n) (hζ' : ζ′ = 0)
    (ρE : E₂) (hρE : aeval ρE (toPoly M) = 0) (hρd : ρE′ = 0) :
    HasElementaryIntegralIn ((∑ f ∈ Finset.range (M.length - 1),
      algebraMap L E₂ (T.ev (m + 1) (cols.getD f (MO Fc ks (m + 1)).zero)) * ρE ^ f) *
        algebraMap L E₂ θ ^ j) := by
  obtain ⟨Wd, s1, s2, Q, D, gg, hg, hWd, hbez, hdiv, hD, hcolv, -⟩ :=
    T.kyColM_spec m n hn hTr M htrim hlen Ah z j W cols h ρE hρE hρd
  set ψ := algebraMap L E₂ with hψ
  set WE := toPoly (W.map fun c ↦ ∑ f ∈ Finset.range (M.length - 1),
    ψ (T.ev (m + 1) (pcP Fc ks m ((c.map fun a ↦ a.1.getD f 0).map (unTr Fc m)))) * ρE ^ f)
    with hWE
  set AhE := ψ (T.ev (m + 1) (pcP Fc ks m Ah)) with hAhE
  have hκE : (κ : E₂) ≠ 0 := by exact_mod_cast hκ
  have hs0 : s ≠ 0 := fun h0 ↦ hκE (by rw [← hsn, h0, zero_pow hn.ne'])
  set Y0 : E₂ := ψ (T.ev m z * θ) / s with hY0
  have hY0n : Y0 ^ n = AhE := by
    rw [hAhE, hAh, hY0, div_pow, hsn, ← map_pow, mul_pow]
    simp only [map_mul, map_pow, map_ratCast]
    rw [Rat.cast_inv]
    ring
  have hAh0 : AhE ≠ 0 := by
    rw [hAhE, hAh]
    refine (map_ne_zero ψ).mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hz0) ?_)
      (pow_ne_zero _ hθ0))
    exact_mod_cast inv_ne_zero hκ
  have hkey : ∀ k : ℕ, WE.eval (ζ ^ k * Y0) ≠ 0 ∧
      logDeriv (WE.eval (ζ ^ k * Y0)) = D.eval (ζ ^ k * Y0) / gg := fun k ↦ by
    have hYk : (ζ ^ k * Y0) ^ n = AhE := by
      rw [mul_pow, ← pow_mul, mul_comm k n, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hY0n]
    refine twist_dlog n WE Wd s1 s2 Q D AhE (((1 / n : ℚ) : E₂) * (AhE′ * AhE⁻¹)) gg _ hYk
      (deriv_of_pow_eq n hn _ _ hYk hAh0) (fun i ↦ ?_) hbez hg hdiv
    rw [hWd i]
  have hsum := twist_sum n ζ hζ D hD j hj Y0
  have hgoal : (∑ f ∈ Finset.range (M.length - 1),
      ψ (T.ev (m + 1) (cols.getD f (MO Fc ks (m + 1)).zero)) * ρE ^ f) * ψ θ ^ j =
      ∑ k ∈ Finset.range n, (s ^ j / n * ζ ^ ((n - j) * k)) *
        logDeriv (WE.eval (ζ ^ k * Y0)) := by
    simp_rw [fun k ↦ (hkey k).2]
    rw [hcolv, hzj]
    have hnE : (n : E₂) ≠ 0 := by exact_mod_cast hn.ne'
    have e3 : ∑ k ∈ Finset.range n, s ^ j / n * ζ ^ ((n - j) * k) *
        (D.eval (ζ ^ k * Y0) / gg) = s ^ j / n / gg *
          ∑ k ∈ Finset.range n, ζ ^ ((n - j) * k) * D.eval (ζ ^ k * Y0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      field_simp
    rw [e3, hsum, hY0]
    simp only [map_mul, map_pow]
    field_simp
    rw [div_pow, mul_pow]
    field_simp
  rw [hgoal]
  refine hei_sum_range n _ fun k _ ↦ hei_logDeriv _ _ ?_ (hkey k).1
  have hn' : ((n : ℕ) : E₂)′ = 0 := Derivation.map_natCast _ _
  rw [Derivation.leibniz, Derivation.leibniz_pow, hζ', div_eq_mul_inv, Derivation.leibniz,
    Derivation.leibniz_inv, hn', Derivation.leibniz_pow, hs']
  simp

set_option maxHeartbeats 1600000 in
/-- **The coordinates of a column are elementary**: `∫ q col_f θʲ` for every coordinate `f`. -/
theorem ky_col_hei (m n j : ℕ) (hn : 0 < n) (hj : j < n) (hTr : T.Tr (m + 1)) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (htrim : CPoly.trim M = M) (hlen : 1 < M.length)
    (Ah : GPoly (LC m)) (z : LC m) (θ : L) (κ : ℚ) (hκ : κ ≠ 0) (hθ0 : θ ≠ 0)
    (hz0 : T.ev m z ≠ 0)
    (hAh : T.ev (m + 1) (pcP Fc ks m Ah) = T.ev m z ^ n * ((κ⁻¹ : ℚ) : L) * θ ^ n)
    (hzj : T.ev (m + 1) (pcP Fc ks m [powC (MO Fc ks m) z j]) = T.ev m z ^ j)
    (W : BPoly (NFM Fc m M)) (cols : List (LC (m + 1)))
    (h : kyColM Fc ks m n M Ah z j W = some cols) (f : ℕ) (hf : f < M.length - 1) (q : ℚ) :
    HasElementaryIntegralIn ((q : L) * (T.ev (m + 1) (cols.getD f (MO Fc ks (m + 1)).zero) *
      θ ^ j)) := by
  classical
  set d := M.length - 1 with hd
  have hMne : M ≠ [] := fun h0 ↦ by rw [h0] at hlen; simp at hlen
  have hMdeg : (toPoly M).natDegree = d := by
    have := CPoly.length_trim (p := M) (by rw [htrim]; exact hMne)
    rw [htrim] at this; omega
  have hM0 : toPoly M ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hMdeg; omega
  have hsep : (toPoly M).Separable := by
    have hirr := (Fact.out : Irreducible (toPoly (liftQ Fc m M)))
    rw [toPoly_liftQ] at hirr
    exact (Polynomial.separable_map _).mp hirr.separable
  obtain ⟨E₂, _, _, _, _, _, -, halg, ⟨s, ζ, hsn, hs', hζ, hζ'⟩, hspl⟩ :=
    split_ext L n hn κ hκ (toPoly M) hM0
  refine HasElementaryIntegralIn.of_isAlgebraic halg ?_
  set ψ := algebraMap L E₂ with hψ
  set R := ((toPoly M).map (algebraMap ℚ E₂)).roots with hR
  have hRnd : R.Nodup := nodup_roots hsep.map
  have hRcard : R.card = d := by
    rw [hR, ← hspl.natDegree_eq_card_roots, natDegree_map, hMdeg]
  set S := R.toFinset with hS
  have hScard : S.card = d := by rw [hS, Multiset.toFinset_card_of_nodup hRnd, hRcard]
  set ρs : Fin d → E₂ := fun i ↦ (S.equivFin.symm (Fin.cast hScard.symm i)).1 with hρs
  have hρinj : Function.Injective ρs := fun i i' hii ↦ by
    have := Subtype.ext hii
    simpa using this
  have hρroot : ∀ i, aeval (ρs i) (toPoly M) = 0 := fun i ↦ by
    have hmem : ρs i ∈ R := Multiset.mem_toFinset.mp (S.equivFin.symm (Fin.cast hScard.symm i)).2
    rw [hR, mem_roots_map_of_injective (algebraMap ℚ E₂).injective hM0] at hmem
    rwa [aeval_def]
  have hρd : ∀ i, (ρs i)′ = 0 := fun i ↦
    deriv_eq_zero_of_isAlgebraic _ ⟨toPoly M, hM0, hρroot i⟩
  set Xv : Fin d → E₂ := fun f ↦ ψ (T.ev (m + 1) (cols.getD f (MO Fc ks (m + 1)).zero) * θ ^ j)
    with hXv
  set Sv : Fin d → E₂ := fun i ↦ (∑ f ∈ Finset.range (M.length - 1),
      ψ (T.ev (m + 1) (cols.getD f (MO Fc ks (m + 1)).zero)) * ρs i ^ f) * ψ θ ^ j with hSv
  have hSeq : ∀ i, ∑ f : Fin d, Xv f * ρs i ^ (f : ℕ) = Sv i := fun i ↦ by
    rw [Fin.sum_univ_eq_sum_range (fun f ↦ ψ (T.ev (m + 1) (cols.getD f (MO Fc ks (m + 1)).zero) *
      θ ^ j) * ρs i ^ f)]
    simp only [hSv]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ ↦ ?_
    rw [map_mul, map_pow]
    ring
  have hSh : ∀ i, HasElementaryIntegralIn (Sv i) := fun i ↦
    T.ky_root_hei m n j hn hj hTr M htrim hlen Ah z θ κ hκ hθ0 hz0 hAh hzj W cols h s ζ hsn hs' hζ
      hζ' (ρs i) (hρroot i) (hρd i)
  obtain ⟨c, hc, hXf⟩ := vandermonde_const d ρs hρd hρinj Xv Sv hSeq ⟨f, hf⟩
  have hgoal : ψ ((q : L) * (T.ev (m + 1) (cols.getD f (MO Fc ks (m + 1)).zero) * θ ^ j)) =
      ∑ i, ((q : E₂) * c i) * Sv i := by
    rw [map_mul, map_ratCast]
    change (q : E₂) * Xv ⟨f, hf⟩ = _
    rw [hXf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hgoal]
  refine Finset.sum_induction _ HasElementaryIntegralIn (fun a b ha hb ↦ ha.add hb)
    ((hasElementaryIntegralIn_deriv (0 : E₂)).congr (by simp)) fun i _ ↦ ?_
  refine (hSh i).const_mul _ ?_
  rw [Derivation.leibniz, hc i, Tower.NestP.deriv_ratCastK (K := E₂) q]
  simp

end MTower

end Curves.MT
