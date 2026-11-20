import RischTragerBronstein.Mixed.EllBaseChange

/-!
# Conjugation and a one-point height certificate

* `certQ1` / `nontors_of_certQ1`: a level-`k` lower bound `ĥ(P) ≥ h(2ᵏP)/4ᵏ − C/(3·4ᵏ) > 0` shows
  `P` has infinite order (`ĥ(nP) = n² ĥ(P)`).
* `conj_nontors`: over `k(X)` with an automorphism `τ` of `k` fixing the image of `k₀`, if `τ`
  negates `Z` and `D` comes from `k₀(X)` and has infinite order, then `2N D + 2μ Z ≠ 0` for `N > 0`
  (apply `τ`: `2N D − 2μ Z = 0`, so `4N D = 0`). This settles the Mordell–Weil exception when `D`
  and `P₊` lie in different square classes, with a certificate for `D` alone.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

section OnePoint

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- **The one-point check**: `C/(3·4ᵏ) < h(2ᵏP)/4ᵏ` (`C = 11 D`). -/
def certQ1 (Ac : CPoly K) (D k : ℕ) (oP : PtC K) : Bool :=
  decide ((11 * D : ℚ) / 3 / 4 ^ k < (htC (dblC Ac k oP) : ℚ) / 4 ^ k)

lemma canonH_zsmul (A B : K[X]) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (P : (shortW A B).toAffine.Point) (n : ℤ) :
    canonH A B (n • P) = (n : ℝ) ^ 2 * canonH A B P := by
  rw [← ntPairing_self A B hΔ, ← ntPairing_self A B hΔ]
  simp only [map_zsmul, AddMonoidHom.zsmul_apply, zsmul_eq_mul]
  ring

/-- **A passing one-point check proves infinite order.** -/
theorem nontors_of_certQ1 (Ac : CPoly K) (A B : K[X]) (hA : CPoly.toPoly Ac = A)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (k : ℕ) (oP : PtC K) (P : (shortW A B).toAffine.Point)
    (hP : Rel A B oP P) (hc : certQ1 Ac (max A.natDegree B.natDegree) k oP = true)
    (n : ℤ) (hn : n • P = 0) : n = 0 := by
  have e1 := htC_spec A B _ _ (dblC_spec Ac A B hA k oP P hP)
  simp only [certQ1, decide_eq_true_eq] at hc
  have hc' := (Rat.cast_lt (K := ℝ)).mpr hc
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow] at hc'
  have happ := MWPair.canon_approx (hR_double A B hΔ) k P
  have hpos : 0 < canonH A B P := by
    simp only [canonH]
    have : (hR A B (MWPair.dbl^[k] P)) = (htC (dblC Ac k oP) : ℝ) := by simp only [hR, e1]
    rw [this] at happ
    rw [abs_le] at happ
    linarith [happ.1]
  have h0 : canonH A B (n • P) = 0 := by
    rw [hn, ← ntPairing_self A B hΔ, map_zero]
  rw [canonH_zsmul A B hΔ] at h0
  have : (n : ℝ) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hpos.ne'
  exact_mod_cast pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this

end OnePoint

section Conj

variable {k₀ k : Type*} [Field k₀] [Field k] [CharZero k₀] [CharZero k]

/-- Composition of coefficient maps. -/
lemma ratMap_comp' {k'' : Type*} [Field k''] [CharZero k''] (f : k₀ →+* k) (g : k →+* k'')
    (r : RatFunc k₀) : ratMap g (ratMap f r) = ratMap (g.comp f) r := by
  have key : (ratMap g).comp (ratMap f) = ratMap (g.comp f) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors k₀[X]) (RingHom.ext fun p ↦ ?_)
    simp only [RingHom.comp_apply, ratMap_alg, Polynomial.map_map]
  exact congrArg (fun φ : RatFunc k₀ →+* RatFunc k'' ↦ φ r) key

lemma mapE_injective (f : k₀ →+* k) (A B : k₀[X]) : Function.Injective (mapE f A B) := by
  letI : Algebra (RatFunc k₀) (RatFunc k) := (ratMap f).toAlgebra
  unfold mapE
  exact (castHom_injective _).comp ((Point.map_injective _).comp (castHom_injective _))

variable (τ : k →+* k) (A B : k[X]) (hA : A.map τ = A) (hB : B.map τ = B)

/-- **The conjugation** `E(k(X)) → E(k(X))` for a curve fixed by `τ`. -/
noncomputable def τE : (shortW A B).toAffine.Point →+ (shortW A B).toAffine.Point :=
  (castHom (by rw [hA, hB])).comp (mapE τ A B)

lemma τE_some (x y : RatFunc k) (h : (shortW A B).toAffine.Nonsingular x y) :
    ∃ h', τE τ A B hA hB (Point.some x y h) = Point.some (ratMap τ x) (ratMap τ y) h' := by
  obtain ⟨h1, e⟩ := mapE_some τ A B x y h
  refine ⟨by rw [hA, hB] at h1; exact h1, ?_⟩
  simp only [τE, AddMonoidHom.comp_apply, e, castHom_some]

/-- **Conjugation argument.** -/
theorem conj_nontors (e : k₀ →+* k) (hτe : τ.comp e = e) (A₀ B₀ : k₀[X])
    (hA' : (A₀.map e).map τ = A₀.map e) (hB' : (B₀.map e).map τ = B₀.map e)
    (PD : (shortW A₀ B₀).toAffine.Point) (PZ : (shortW (A₀.map e) (B₀.map e)).toAffine.Point)
    (hZ : τE τ (A₀.map e) (B₀.map e) hA' hB' PZ = -PZ)
    (hnt : ∀ n : ℤ, n • PD = 0 → n = 0) :
    ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • mapE e A₀ B₀ PD + (2 * μ) • PZ ≠ 0 := by
  have hfix : ∀ P, τE τ (A₀.map e) (B₀.map e) hA' hB' (mapE e A₀ B₀ P) = mapE e A₀ B₀ P := by
    intro P
    rcases P with _ | ⟨x, y, h⟩
    · show τE τ _ _ hA' hB' (mapE e A₀ B₀ 0) = mapE e A₀ B₀ 0
      rw [map_zero, map_zero]
    · obtain ⟨h1, e1⟩ := mapE_some e A₀ B₀ x y h
      rw [e1]
      obtain ⟨h2, e2⟩ := τE_some τ _ _ hA' hB' _ _ h1
      rw [e2]
      simp only [Point.some.injEq, ratMap_comp', hτe, and_self]
  intro N hN μ hrel
  have h2 := congrArg (τE τ (A₀.map e) (B₀.map e) hA' hB') hrel
  rw [map_add, map_zsmul, map_zsmul, hfix, hZ, map_zero] at h2
  have h4 : (4 * (N : ℤ)) • mapE e A₀ B₀ PD = 0 := by
    have : (4 * (N : ℤ)) • mapE e A₀ B₀ PD = ((2 * (N : ℤ)) • mapE e A₀ B₀ PD + (2 * μ) • PZ) +
        ((2 * (N : ℤ)) • mapE e A₀ B₀ PD + (2 * μ) • -PZ) := by
      rw [zsmul_neg, show (4 : ℤ) * N = 2 * N + 2 * N by ring, add_zsmul]; abel
    rw [this, hrel, h2, add_zero]
  rw [← map_zsmul] at h4
  have := hnt _ ((mapE_injective e A₀ B₀) (by rw [h4, map_zero]))
  omega

end Conj

end FFHeight
