import RischTragerBronstein.Mixed.EllIso

/-!
# Completeness of height certificates on quadratic twists of constant curves

On `y² = x³ + a D² x + b D³` (`D³` not a constant times a square) the canonical height is the
natural number `ht (x / D)` (`canonH_eq_gTw`) and vanishes only on `2`-torsion
(`two_tors_of_canonH`). Hence for independent `P, Q` the binary form
`canonH (m P + n Q) = a m² + b m n + c n²` (`a, b, c ∈ ℤ`) is `≥ 1` off the origin, so
`4ac − b² ≥ 1` (`disc_pos`: evaluate at `(b, −2a)`), the Gram determinant is positive, and the
**level-`k` height certificate of `ell_indep` holds for all large `k`** (`hgap_exists`): the
certificate search is complete on these isotrivial curves.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine Filter Topology

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

variable {A B D : K[X]} {a b : K}

/-- The canonical height is a quadratic form (from the Néron–Tate pairing). -/
theorem canonH_quad (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (P Q : (shortW A B).toAffine.Point) (m n : ℤ) :
    canonH A B (m • P + n • Q) = m ^ 2 * canonH A B P +
      m * n * (canonH A B (P + Q) - canonH A B P - canonH A B Q) + n ^ 2 * canonH A B Q := by
  have hs : ∀ X, ntPairing A B hΔ' X X = canonH A B X := ntPairing_self A B hΔ'
  have hpq : ntPairing A B hΔ' P Q = (canonH A B (P + Q) - canonH A B P - canonH A B Q) / 2 := rfl
  have hqp : ntPairing A B hΔ' Q P = ntPairing A B hΔ' P Q :=
    show MWPair.polar (canonH A B) Q P = MWPair.polar (canonH A B) P Q from MWPair.polar_comm _ _ _
  have e : ntPairing A B hΔ' (m • P + n • Q) (m • P + n • Q) =
      m ^ 2 * ntPairing A B hΔ' P P + m * n * (ntPairing A B hΔ' P Q + ntPairing A B hΔ' Q P) +
        n ^ 2 * ntPairing A B hΔ' Q Q := by
    simp only [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply, zsmul_eq_mul]
    ring
  rw [← hs, e, hs, hs, hqp, hpq]
  ring


/-- Off the origin, the canonical height of `m P + n Q` is at least `1` for independent `P, Q`. -/
theorem canonH_ge_one (hD : D ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hA : A = C a * D ^ 2)
    (hB : B = C b * D ^ 3) (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hsq : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι D ^ 3 ≠ w ^ 2)
    (P Q : (shortW A B).toAffine.Point)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) (m n : ℤ) (hmn : ¬ (m = 0 ∧ n = 0)) :
    1 ≤ canonH A B (m • P + n • Q) := by
  rw [canonH_eq_gTw hD hΔ hA hB hΔ']
  by_contra hlt
  have h0 : gTw A B D (m • P + n • Q) = 0 := by
    have : (gTw A B D (m • P + n • Q) : ℝ) < 1 := not_le.mp hlt
    exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
  have h2 := two_tors_of_canonH hD hΔ hA hB hΔ' hsq (m • P + n • Q)
    (by rw [canonH_eq_gTw hD hΔ hA hB hΔ', h0, Nat.cast_zero])
  have : (2 * m) • P = (-(2 * n)) • Q := by
    have e : (2 * m) • P - (-(2 * n)) • Q = (m • P + n • Q) + (m • P + n • Q) := by
      rw [neg_smul, sub_neg_eq_add, mul_smul, mul_smul, two_zsmul, two_zsmul]; abel
    rw [← sub_eq_zero, e]; exact h2
  obtain ⟨h1, h2'⟩ := hind _ _ this
  exact hmn ⟨by omega, by omega⟩

/-- **The discriminant of the height form is negative.** -/
theorem disc_pos (hD : D ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hA : A = C a * D ^ 2)
    (hB : B = C b * D ^ 3) (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hsq : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι D ^ 3 ≠ w ^ 2)
    (P Q : (shortW A B).toAffine.Point)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    0 < 4 * canonH A B P * canonH A B Q -
      (canonH A B (P + Q) - canonH A B P - canonH A B Q) ^ 2 := by
  have hint : ∀ X, ∃ z : ℕ, canonH A B X = z := fun X ↦ ⟨_, canonH_eq_gTw hD hΔ hA hB hΔ' X⟩
  obtain ⟨za, hza⟩ := hint P
  obtain ⟨zc, hzc⟩ := hint Q
  obtain ⟨zs, hzs⟩ := hint (P + Q)
  set bb : ℤ := (zs : ℤ) - za - zc
  have hb : canonH A B (P + Q) - canonH A B P - canonH A B Q = bb := by rw [hza, hzc, hzs]; push_cast [bb]; ring
  have ha : 1 ≤ canonH A B P := by
    have := canonH_ge_one hD hΔ hA hB hΔ' hsq P Q hind 1 0 (by simp)
    simpa using this
  have hza1 : 1 ≤ (za : ℤ) := by rw [hza] at ha; exact_mod_cast ha
  have key := canonH_ge_one hD hΔ hA hB hΔ' hsq P Q hind bb (-(2 * za)) (by omega)
  rw [canonH_quad hΔ', hb, hza, hzc] at key
  rw [hb, hza, hzc]
  push_cast at key ⊢
  have e : (bb : ℝ) ^ 2 * za + bb * (-(2 * za)) * bb + (-(2 * (za : ℝ))) ^ 2 * zc =
      za * (4 * za * zc - bb ^ 2) := by ring
  have hza' : (1 : ℝ) ≤ za := by exact_mod_cast hza1
  nlinarith

/-- **The height certificate of `ell_indep` exists** for independent points (some level `k`). -/
theorem hgap_exists (hD : D ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hA : A = C a * D ^ 2)
    (hB : B = C b * D ^ 3) (hΔ' : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hsq : ∀ (c : K) (w : RatFunc K), c ≠ 0 → κ c * ι D ^ 3 ≠ w ^ 2)
    (P Q : (shortW A B).toAffine.Point)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    ∃ k : ℕ, let C : ℝ := 11 * (max A.natDegree B.natDegree : ℕ)
      let h := hR A B
      let d := MWPair.dbl (G := (shortW A B).toAffine.Point)
      C / 3 / 4 ^ k * (|h (d^[k] P) / 4 ^ k| + |h (d^[k] Q) / 4 ^ k| + C / 3 / 4 ^ k) +
        3 * (C / 3 / 4 ^ k) / 2 * (|h (d^[k] (P + Q)) / 4 ^ k - h (d^[k] P) / 4 ^ k -
          h (d^[k] Q) / 4 ^ k| + 3 * (C / 3 / 4 ^ k) / 2) <
      |h (d^[k] P) / 4 ^ k * (h (d^[k] Q) / 4 ^ k) - ((h (d^[k] (P + Q)) / 4 ^ k -
          h (d^[k] P) / 4 ^ k - h (d^[k] Q) / 4 ^ k) / 2) ^ 2| := by
  set C : ℝ := 11 * (max A.natDegree B.natDegree : ℕ)
  have hC := hR_double A B hΔ'
  have tP := MWTate.tendsto_canon hC P
  have tQ := MWTate.tendsto_canon hC Q
  have tS := MWTate.tendsto_canon hC (P + Q)
  have te : Tendsto (fun k : ℕ ↦ C / 3 / 4 ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  set f := canonH A B
  have hlim1 := (te.mul ((tP.abs.add tQ.abs).add te)).add
    (((te.const_mul 3).div_const 2).mul (((tS.sub tP).sub tQ).abs.add ((te.const_mul 3).div_const 2)))
  have hlim2 := ((tP.mul tQ).sub ((((tS.sub tP).sub tQ).div_const 2).pow 2)).abs
  have hpos : (0 : ℝ) * (|f P| + |f Q| + 0) + 3 * 0 / 2 * (|f (P + Q) - f P - f Q| + 3 * 0 / 2) <
      |f P * f Q - ((f (P + Q) - f P - f Q) / 2) ^ 2| := by
    have := disc_pos hD hΔ hA hB hΔ' hsq P Q hind
    have hk : 0 < f P * f Q - ((f (P + Q) - f P - f Q) / 2) ^ 2 := by nlinarith
    rw [abs_of_pos hk]
    linarith
  obtain ⟨k, hk⟩ := (hlim1.eventually_lt hlim2 hpos).exists
  exact ⟨k, hk⟩

end FFHeight

