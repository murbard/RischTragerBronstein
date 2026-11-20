import RischTragerBronstein.Algebraic.SupDecideAll
import RischTragerBronstein.Elementary.FiniteBase

/-!
# Superelliptic curves with `1 < gcd(n, deg f) < n`: passing to a cover

For `yⁿ = f(x)`, `d = deg f`, `k = n / gcd(n, d)` and `c ∈ ℚ`, adjoin `s` with `sᵏ = x − c`
(a root of an irreducible factor of `Sᵏ − (x − c)` over `E`: a finite extension `E'`). Over
`Kc(s)` the curve is `yⁿ = g(s)`, `g = f(c + Xᵏ)`, of degree `d k`, divisible by `n`; with the
derivation rescaled by `k sᵏ⁻¹` (so that `s′ = 1`) the integrand becomes
`∑ k sᵏ⁻¹ Aⱼ(c + sᵏ)/D(c + sᵏ) yʲ`, all over `ℚ`. `superDecideCover` runs `superDecideMobQ` on
this data.

Correctness (`superDecideCover_spec`) combines `superDecideMobQ_spec` over `E'`, the change of
derivation (`hasElementaryIntegral_rescale_iff`) and the invariance of elementary integrability
under finite extensions of the base (`hasElementaryIntegral_finite_iff`).

`superDecideSup` dispatches: `gcd(n, d) = 1` → `superDecideQ`, `n ∣ d` → `superDecideMobQ`,
otherwise → `superDecideCover`; every answer is correct (`superDecideSup_spec`), for every `f`.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac NFC

namespace Sup

/-- `p(c + Xᵏ)`, untrimmed. -/
def compShiftPow0 (p : CPoly ℚ) (c : ℚ) (k : ℕ) : CPoly ℚ :=
  p.foldr (fun a acc ↦ add [a] (mul (add [c] (monomial k 1)) acc)) []

/-- `p(c + Xᵏ)` (trimmed, so that its last entry is the leading coefficient). -/
def compShiftPow (p : CPoly ℚ) (c : ℚ) (k : ℕ) : CPoly ℚ := trim (compShiftPow0 p c k)

lemma toPoly_compShiftPow0 (c : ℚ) (k : ℕ) : ∀ p : CPoly ℚ,
    toPoly (compShiftPow0 p c k) = (toPoly p).comp (C c + X ^ k)
  | [] => by simp [compShiftPow0]
  | a :: p => by
    have ih := toPoly_compShiftPow0 c k p
    simp only [compShiftPow0, List.foldr_cons] at ih ⊢
    rw [toPoly_add, toPoly_mul, toPoly_add, ih, toPoly_monomial, toPoly_cons]
    simp [toPoly_cons]

lemma toPoly_compShiftPow (c : ℚ) (k : ℕ) (p : CPoly ℚ) :
    toPoly (compShiftPow p c k) = (toPoly p).comp (C c + X ^ k) := by
  rw [compShiftPow, toPoly_trim, toPoly_compShiftPow0]

/-- The cover degree `k = n / gcd(n, deg f)`. -/
def coverK (f : CPoly ℚ) (n : ℕ) : ℕ := n / Nat.gcd n (f.length - 1)

/-- A rational point `c` with `f(c) ≠ 0` (so that `f(c + Xᵏ)` stays squarefree). -/
def coverC (f : CPoly ℚ) : ℚ :=
  (((List.range (f.length + 1)).map fun i : ℕ ↦ (i : ℚ)).find? fun c ↦ decide (evalC f c ≠ 0)).getD 0

/-- The transformed numerator `k Xᵏ⁻¹ a(c + Xᵏ)`. -/
def coverNum (c : ℚ) (k : ℕ) (a : CPoly ℚ) : CPoly ℚ :=
  mul [(k : ℚ)] (mul (monomial (k - 1) 1) (compShiftPow a c k))

/-- **The procedure through the cover `sᵏ = x − c`.** -/
noncomputable def superDecideCover (f : CPoly ℚ) (n : ℕ) (A : List (CPoly ℚ)) (D : CPoly ℚ)
    (B fuel : ℕ) : Option Bool :=
  superDecideMobQ (compShiftPow f (coverC f) (coverK f n)) n
    (A.map (coverNum (coverC f) (coverK f n))) (compShiftPow D (coverC f) (coverK f n)) B fuel

/-- **The superelliptic dispatcher**: `gcd(n, deg f) = 1`, `n ∣ deg f`, or through a cover. -/
noncomputable def superDecideSup (f : CPoly ℚ) (n : ℕ) (A : List (CPoly ℚ)) (D : CPoly ℚ)
    (B fuel : ℕ) : Option Bool :=
  if Nat.Coprime n (f.length - 1) then superDecideQ f n A D B fuel
  else if (f.length - 1) % n = 0 then superDecideMobQ f n A D B fuel
  else superDecideCover f n A D B fuel

section Spec

open Differential IntermediateField

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 3200000 in
/-- **Correctness through a cover** `sᵏ = x − c` (any `c ∈ ℚ`, `k ≥ 1`). -/
theorem superDecideMobQ_cover_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0) (x y : E)
    (hx : x′ = 1) (f : CPoly ℚ) {n : ℕ} (hn : 0 < n)
    (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ) (c : ℚ) {k : ℕ}
    (hk : 0 < k) (B fuel : ℕ) (ans : Bool)
    (h : superDecideMobQ (compShiftPow f c k) n (A.map (coverNum c k)) (compShiftPow D c k) B
      fuel = some ans) :
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
  have hspec := @superDecideMobQ_spec Kc (AdjoinRoot q) _ _ _ _ (rescale ⟨d0⟩ φ) hDA' _ _ _ hC s y' hT
    (compShiftPow f c k) n hn hyC hgen' (A.map (coverNum c k)) (compShiftPow D c k) B fuel ans h
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

/-- **Correctness of `superDecideCover`.** -/
theorem superDecideCover_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0) (x y : E)
    (hx : x′ = 1) (f : CPoly ℚ) {n : ℕ} (hn : 0 < n)
    (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ) (B fuel : ℕ) (ans : Bool)
    (h : superDecideCover f n A D B fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  have hk : 0 < coverK f n :=
    Nat.div_pos (Nat.gcd_le_left _ hn) (Nat.gcd_pos_of_pos_left _ hn)
  exact superDecideMobQ_cover_spec hC x y hx f hn hy hgen A D (coverC f) hk B fuel ans h

/-- **Correctness of `superDecideSup`**: for `f ∈ ℚ[x]` squarefree of positive degree and any
`n ≥ 1`, every answer is correct. -/
theorem superDecideSup_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (f : CPoly ℚ) {n : ℕ} (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hdeg : (toPoly f).natDegree = f.length - 1) (hpd : 0 < f.length - 1)
    (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ) (hD : toPoly D ≠ 0)
    (B fuel : ℕ) (ans : Bool) (h : superDecideSup f n A D B fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  unfold superDecideSup at h
  split_ifs at h with hcop hdiv
  · exact superDecideQ_spec hC x y hx f hn hsq hdeg hpd hcop hy hgen A D hD B fuel ans h
  · exact superDecideMobQ_spec hC x y hx f hn hy hgen A D B fuel ans h
  · exact superDecideCover_spec hC x y hx f hn hy hgen A D B fuel ans h

end Spec

end Sup
