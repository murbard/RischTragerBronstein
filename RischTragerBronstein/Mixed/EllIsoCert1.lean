import RischTragerBronstein.Mixed.KXRepS2
import RischTragerBronstein.Mixed.KXConj

/-!
# One-point height certificates exist on twists of constant curves

`canonH_pos_iso`: on a non-trivial twist of a constant curve (`IsoNT`), a point of infinite order
has positive canonical height (exact integral heights + positivity, `EllIso*`). Hence
**`certQ1_exists_iso`**: the one-point executable check `certQ1` (used by the conjugation branch)
passes at some level for every represented point of infinite order.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine Filter Topology

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

/-- **Positivity of the canonical height on non-trivial twists.** -/
theorem canonH_pos_iso (A B : K[X]) (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hiso : IsoNT A B)
    (P : (shortW A B).toAffine.Point) (hP : ∀ n : ℤ, n • P = 0 → n = 0) : 0 < canonH A B P := by
  -- non-negativity and the torsion criterion, case by case
  have key : 0 ≤ canonH A B P ∧ (canonH A B P = 0 → ∃ n : ℕ, 0 < n ∧ n • P = 0) := by
    rcases hiso with ⟨hA0, hB0, hcube⟩ | ⟨hB0, hA0, hsq⟩ | ⟨a, b, D, hD, hΔ, hA, hB, hsq⟩
    · subst hA0
      exact ⟨by rw [canonH_eq_gT0 hB0 hΔ']; positivity, tors_of_canonH0 hB0 hΔ' hcube P⟩
    · subst hB0
      exact ⟨by rw [canonH_eq_gT1 hA0 hΔ']; positivity, tors_of_canonH1 hA0 hΔ' hsq P⟩
    · refine ⟨by rw [canonH_eq_gTw hD hΔ hA hB hΔ']; positivity, fun h0 ↦ ⟨2, two_pos, ?_⟩⟩
      rw [two_nsmul]; exact two_tors_of_canonH hD hΔ hA hB hΔ' hsq P h0
  rcases key.1.lt_or_eq with h | h
  · exact h
  · obtain ⟨n, hn, hnP⟩ := key.2 h.symm
    have := hP n (by rw [natCast_zsmul]; exact hnP)
    omega

/-- **The one-point certificate exists** on non-trivial twists, for points of infinite order. -/
theorem certQ1_exists_iso (Ac : CPoly K) (A B : K[X]) (hAc : CPoly.toPoly Ac = A)
    (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hiso : IsoNT A B) (oP : PtC K)
    (P : (shortW A B).toAffine.Point) (hRel : Rel A B oP P) (hP : ∀ n : ℤ, n • P = 0 → n = 0) :
    ∃ k, certQ1 Ac (max A.natDegree B.natDegree) k oP = true := by
  have hpos := canonH_pos_iso A B hΔ' hiso P hP
  set C : ℝ := 11 * (max A.natDegree B.natDegree : ℕ)
  have tP := MWTate.tendsto_canon (hR_double A B hΔ') P
  have te : Tendsto (fun k : ℕ ↦ C / 3 / 4 ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  obtain ⟨k, hk⟩ := (te.eventually_lt tP hpos).exists
  refine ⟨k, ?_⟩
  have e1 := htC_spec A B _ _ (dblC_spec Ac A B hAc k oP P hRel)
  simp only [certQ1, decide_eq_true_eq]
  apply (Rat.cast_lt (K := ℝ)).mp
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow]
  have : (htC (dblC Ac k oP) : ℝ) = hR A B (MWPair.dbl^[k] P) := by simp only [hR, e1]
  rw [this]
  exact hk

end FFHeight

