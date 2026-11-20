import RischTragerBronstein.Mixed.FFMorph

/-!
# Base change of the naive height

For a field extension `f : K →+* L`, the naive height on `K(X)` is unchanged under the induced
map `K(X) → L(X)` (`ht_map`): heights, hence the height-pairing certificates of `EllNT`, may be
computed over a small field (e.g. `ℚ` or a number field) and used over its algebraic closure.
-/

open Polynomial

namespace FFHeight

variable {K L : Type*} [Field K] [Field L]

/-- Non-zero polynomials stay non-zero under a field homomorphism. -/
lemma map_nzd (f : K →+* L) :
    nonZeroDivisors K[X] ≤ (nonZeroDivisors L[X]).comap (Polynomial.mapRingHom f) := fun p hp ↦ by
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
  simpa [Polynomial.map_eq_zero_iff f.injective] using hp0

/-- **The naive height is invariant under extension of the constants.** -/
theorem ht_map (f : K →+* L) (x : RatFunc K) :
    ht (RatFunc.map (Polynomial.mapRingHom f) (map_nzd f) x) = ht x := by
  set u := RatFunc.num x
  set v := RatFunc.denom x
  have hv : v ≠ 0 := RatFunc.denom_ne_zero x
  have hc : IsCoprime u v := RatFunc.isCoprime_num_denom x
  have hx : x = algebraMap K[X] (RatFunc K) u / algebraMap K[X] (RatFunc K) v :=
    (RatFunc.num_div_denom x).symm
  have hv' : v.map f ≠ 0 := by simpa [Polynomial.map_eq_zero_iff f.injective] using hv
  have hc' : IsCoprime (u.map f) (v.map f) := by
    simpa using hc.map (Polynomial.mapRingHom f)
  conv_lhs => rw [hx, RatFunc.map_apply_div]
  rw [coe_mapRingHom, ht_div_coprime _ _ hv' hc', natDegree_map, natDegree_map, hx,
    ht_div_coprime u v hv hc]

end FFHeight
