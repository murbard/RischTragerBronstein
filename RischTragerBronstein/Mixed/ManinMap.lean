import RischTragerBronstein.Mixed.ManinGM
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Derivation.Basic

/-!
# The Manin map of `y² = x³ + A x + B` over a differential field

For a field `K` of characteristic `0` with a derivation `D` and `E : y² = x³ + A x + B`
(`4A³ + 27B² ≠ 0`), the **Manin map** `mu : E(K) → K` is
`mu R = D b₁(R) − κ b₁(R) + β b₂(R)`,
where `b = (b₁, b₂)` is the Gauss–Manin vector of `ManinGM` (`b := 0` on `2`-torsion points),
`β, δ = −α` are the Gauss–Manin coefficients and `κ = (Dβ + βδ)/β`. Analytically
`mu R = L(∫_O^R dx/y)` for the Picard–Fuchs operator `L`.

* `mu_add`: `mu` is additive (all cases of the group law), so `muHom : E(K) →+ K`;
* `mu_torsion`: torsion points lie in the kernel;
* `indep_of_wronskian`: if the Wronskian `mu P · D(mu Q) − mu Q · D(mu P)` is non-zero, then no
  relation `m P = n Q + T` (`T` torsion, `(m, n) ≠ 0`) holds. This is a **sound independence
  certificate** for the Mordell–Weil exception on non-constant curves.

Completeness of the certificate (`mu R = 0 ⇒ R` torsion when `j ∉` constants) is Manin's theorem
of the kernel, not proved here.
-/

set_option linter.unusedSectionVars false

namespace Manin

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- `y² = x³ + A x + B`. -/
def sW (A B : K) : WeierstrassCurve K := ⟨0, 0, 0, A, B⟩

variable (D : Derivation ℤ K K) (A B : K)

/-- `4A³ + 27B²`. -/
def ZZ : K := 4 * A ^ 3 + 27 * B ^ 2

/-- The Gauss–Manin coefficient `β`. -/
def bt : K := beZ (ZZ A B) A B (D A) (D B)

/-- `κ = (Dβ − βα) / β`. -/
def ka : K := (D (bt D A B) - bt D A B * alZ (ZZ A B) A B (D A) (D B)) / bt D A B

/-- The Gauss–Manin vector of an affine point (`0` on `2`-torsion points). -/
def bvU (u v : K) : K × K :=
  if v = 0 then (0, 0) else
    (b1Z (ZZ A B) A B (D A) (D B) u v (D u), b2Z (ZZ A B) A B (D A) (D B) u v (D u))

/-- The linear differential form killing coboundaries. -/
def muP (p : K × K) : K := D p.1 - ka D A B * p.1 + bt D A B * p.2

/-- **The Manin map.** -/
def mu : (sW A B).toAffine.Point → K
  | .zero => 0
  | .some u v _ => muP D A B (bvU D A B u v)

theorem ka_mul : ka D A B * bt D A B = D (bt D A B) - bt D A B * alZ (ZZ A B) A B (D A) (D B) := by
  by_cases hb : bt D A B = 0
  · simp [ka, hb]
  · unfold ka; field_simp

/-- Coboundaries `(−β c, D c − δ c)` are killed. -/
theorem cob (p1 p2 p3 : K × K) (c : K)
    (h1 : p3.1 = p1.1 + p2.1 - bt D A B * c)
    (h2 : p3.2 = p1.2 + p2.2 + D c + alZ (ZZ A B) A B (D A) (D B) * c) :
    muP D A B p3 = muP D A B p1 + muP D A B p2 := by
  unfold muP
  rw [h1, h2, D.map_sub, D.map_add, D.leibniz, smul_eq_mul, smul_eq_mul]
  linear_combination c * ka_mul D A B

theorem muP_zero : muP D A B (0, 0) = 0 := by simp [muP]

theorem muP_neg (p : K × K) : muP D A B (-p) = -muP D A B p := by
  simp only [muP, Prod.fst_neg, Prod.snd_neg, D.map_neg]; ring

theorem bvU_zero (u : K) : bvU D A B u 0 = (0, 0) := by simp [bvU]

theorem bvU_neg (u v : K) : bvU D A B u (-v) = -bvU D A B u v := by
  by_cases hv : v = 0
  · simp [bvU, hv]
  · have hv' : -v ≠ 0 := neg_ne_zero.mpr hv
    simp only [bvU, if_neg hv, if_neg hv', b1Z, b2Z, div_neg, Prod.neg_mk]

/-! ### Curve facts -/

variable {A B}

theorem eqn {u v : K} (h : (sW A B).toAffine.Nonsingular u v) : v ^ 2 = u ^ 3 + A * u + B := by
  have h1 := h.1
  rw [equation_iff] at h1
  simpa [sW] using h1

theorem negY_sW (u v : K) : (sW A B).toAffine.negY u v = -v := by simp [negY, sW]

omit [CharZero K] [DecidableEq K] in
theorem dv_rel {u v : K} (h : v ^ 2 = u ^ 3 + A * u + B) :
    2 * v * D v = 3 * u ^ 2 * D u + D A * u + A * D u + D B := by
  have h' := congrArg D h
  simp only [pow_succ, pow_zero, one_mul, D.leibniz, D.map_add, smul_eq_mul] at h'
  linear_combination h'

theorem hs_of {u : K} (h : (sW A B).toAffine.Nonsingular u 0) : 3 * u ^ 2 + A ≠ 0 := by
  rw [nonsingular_iff'] at h
  rcases h.2 with h | h
  · intro hc; apply h; simp only [sW]; linear_combination -hc
  · simp [sW] at h

theorem t2_iff {u v : K} (h : (sW A B).toAffine.Nonsingular u v) :
    Point.some u v h + Point.some u v h = 0 ↔ v = 0 := by
  by_cases hv : v = (sW A B).toAffine.negY u v
  · rw [add_self_of_Y_eq hv]
    rw [negY_sW] at hv
    simp only [true_iff]
    linear_combination hv / 2
  · rw [add_self_of_Y_ne hv]
    rw [negY_sW] at hv
    simp only [reduceCtorEq, false_iff]
    intro h0; apply hv; rw [h0, _root_.neg_zero]

theorem mu_two_tors {u : K} (h : (sW A B).toAffine.Nonsingular u 0) :
    mu D A B (Point.some u 0 h) = 0 := by
  simp [mu, bvU_zero, muP_zero]

theorem mu_neg (P : (sW A B).toAffine.Point) : mu D A B (-P) = -mu D A B P := by
  rcases P with _ | ⟨u, v, h⟩
  · show mu D A B 0 = -mu D A B 0
    simp [mu]
  · rw [neg_some]
    simp only [mu, negY_sW, bvU_neg, muP_neg]

/-! ### The three algebraic cases -/

variable (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
include hΔ

omit [DecidableEq K] in
theorem dl_rel {l u1 u2 v1 v2 : K} (hl : l * (u2 - u1) = v2 - v1) :
    D l * (u2 - u1) = D v2 - D v1 - l * (D u2 - D u1) := by
  have h' := congrArg D hl
  simp only [D.leibniz, D.map_sub, smul_eq_mul] at h'
  linear_combination h'

/-- Chord case, no `2`-torsion involved. -/
theorem case_G {u1 v1 u2 v2 l : K} (h1 : v1 ^ 2 = u1 ^ 3 + A * u1 + B)
    (h2 : v2 ^ 2 = u2 ^ 3 + A * u2 + B) (hu : u2 - u1 ≠ 0) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0)
    (hl : l * (u2 - u1) = v2 - v1) (hv3 : -(v1 + l * ((l ^ 2 - u1 - u2) - u1)) ≠ 0) :
    muP D A B (bvU D A B (l ^ 2 - u1 - u2) (-(v1 + l * ((l ^ 2 - u1 - u2) - u1)))) =
      muP D A B (bvU D A B u1 v1) + muP D A B (bvU D A B u2 v2) := by
  have hZ0 : ZZ A B ≠ 0 := hΔ
  have hd3 : D (l ^ 2 - u1 - u2) = 2 * l * D l - D u1 - D u2 := by
    simp only [D.map_sub, pow_two, D.leibniz, smul_eq_mul]; ring
  have hdL := dl_rel D hΔ hl
  apply cob D A B _ _ _ (-(l + l))
  · simp only [bvU, if_neg hv1, if_neg hv2, if_neg hv3]
    rw [gm1 (ZZ A B) A B (D A) (D B) u1 v1 (D u1) (D v1) u2 v2 (D u2) (D v2) l (D l) _ _ _ h1 h2
      (dv_rel D h1) (dv_rel D h2) hl hdL rfl rfl hd3 rfl hu hv1 hv2 hv3 hZ0]
    unfold bt; ring
  · simp only [bvU, if_neg hv1, if_neg hv2, if_neg hv3]
    rw [gm2 (ZZ A B) A B (D A) (D B) u1 v1 (D u1) (D v1) u2 v2 (D u2) (D v2) l (D l) _ _ _ h1 h2
      (dv_rel D h1) (dv_rel D h2) hl hdL rfl rfl hd3 rfl hu hv1 hv2 hv3 hZ0]
    simp only [D.map_neg, D.map_add]; ring

/-- Chord through a `2`-torsion point `(u1, 0)`. -/
theorem case_T {u1 u2 v2 l : K} (h1 : u1 ^ 3 + A * u1 + B = 0)
    (h2 : v2 ^ 2 = u2 ^ 3 + A * u2 + B) (hs : 3 * u1 ^ 2 + A ≠ 0) (hu : u2 - u1 ≠ 0)
    (hv2 : v2 ≠ 0) (hl : l * (u2 - u1) = v2) (hv3 : -(l * ((l ^ 2 - u1 - u2) - u1)) ≠ 0) :
    muP D A B (bvU D A B (l ^ 2 - u1 - u2) (-(l * ((l ^ 2 - u1 - u2) - u1)))) =
      muP D A B (bvU D A B u1 0) + muP D A B (bvU D A B u2 v2) := by
  have hZ0 : ZZ A B ≠ 0 := hΔ
  have hd3 : D (l ^ 2 - u1 - u2) = 2 * l * D l - D u1 - D u2 := by
    simp only [D.map_sub, pow_two, D.leibniz, smul_eq_mul]; ring
  have hdL : D l * (u2 - u1) = D v2 - l * (D u2 - D u1) := by
    have := dl_rel D hΔ (l := l) (u1 := u1) (u2 := u2) (v1 := 0) (v2 := v2) (by rw [sub_zero]; exact hl)
    rwa [D.map_zero, sub_zero] at this
  have he1 : 3 * u1 ^ 2 * D u1 + D A * u1 + A * D u1 + D B = 0 := by
    have := dv_rel D (u := u1) (v := 0) (by rw [h1]; ring)
    linear_combination -this
  rw [bvU_zero]
  apply cob D A B _ _ _ (-(l + l))
  · simp only [bvU, if_neg hv2, if_neg hv3]
    rw [tm1 (ZZ A B) A B (D A) (D B) u1 0 (D u1) 0 u2 v2 (D u2) (D v2) l (D l) _ _ _ h1 h2
      he1 (dv_rel D h2) hl hdL rfl rfl hd3 rfl hu hs hv2 hv3 hZ0]
    unfold bt; ring
  · simp only [bvU, if_neg hv2, if_neg hv3]
    rw [tm2 (ZZ A B) A B (D A) (D B) u1 0 (D u1) 0 u2 v2 (D u2) (D v2) l (D l) _ _ _ h1 h2
      he1 (dv_rel D h2) hl hdL rfl rfl hd3 rfl hu hs hv2 hv3 hZ0]
    simp only [D.map_neg, D.map_add]; ring

/-- Tangent case. -/
theorem case_D {u1 v1 l : K} (h1 : v1 ^ 2 = u1 ^ 3 + A * u1 + B) (hv1 : v1 ≠ 0)
    (hl : l * (2 * v1) = 3 * u1 ^ 2 + A) (hv3 : -(v1 + l * ((l ^ 2 - 2 * u1) - u1)) ≠ 0) :
    muP D A B (bvU D A B (l ^ 2 - 2 * u1) (-(v1 + l * ((l ^ 2 - 2 * u1) - u1)))) =
      muP D A B (bvU D A B u1 v1) + muP D A B (bvU D A B u1 v1) := by
  have hZ0 : ZZ A B ≠ 0 := hΔ
  have hd3 : D (l ^ 2 - 2 * u1) = 2 * l * D l - 2 * D u1 := by
    rw [show l ^ 2 - 2 * u1 = l * l - (u1 + u1) by ring]
    simp only [D.map_sub, D.map_add, D.leibniz, smul_eq_mul]; ring
  have hdL : D l * (2 * v1) = 6 * u1 * D u1 + D A - l * (2 * D v1) := by
    have h' := congrArg D (show l * (v1 + v1) = u1 * u1 * 3 + A by linear_combination hl)
    simp only [D.leibniz, D.map_add, smul_eq_mul] at h'
    have h3 : D (3 : K) = 0 := by
      rw [show (3 : K) = ((3 : ℤ) : K) by norm_num]; exact D.map_intCast 3
    rw [h3] at h'
    linear_combination h'
  apply cob D A B _ _ _ (-(l + l))
  · simp only [bvU, if_neg hv1, if_neg hv3]
    rw [dm1 (ZZ A B) A B (D A) (D B) u1 v1 (D u1) (D v1) 0 0 0 0 l (D l) _ _ _ h1
      (dv_rel D h1) hl hdL rfl rfl hd3 rfl hv1 hv3 hZ0]
    unfold bt; ring
  · simp only [bvU, if_neg hv1, if_neg hv3]
    rw [dm2 (ZZ A B) A B (D A) (D B) u1 v1 (D u1) (D v1) 0 0 0 0 l (D l) _ _ _ h1
      (dv_rel D h1) hl hdL rfl rfl hd3 rfl hv1 hv3 hZ0]
    simp only [D.map_neg, D.map_add]; ring

/-! ### Additivity on points -/

omit hΔ in
theorem addX_sW (x1 x2 l : K) : (sW A B).toAffine.addX x1 x2 l = l ^ 2 - x1 - x2 := by
  simp [addX, sW]

omit hΔ in
theorem addY_sW (x1 x2 y1 l : K) :
    (sW A B).toAffine.addY x1 x2 y1 l = -(y1 + l * ((l ^ 2 - x1 - x2) - x1)) := by
  simp [addY, negAddY, negY, addX, sW]; ring

/-- Adding a `2`-torsion point does not change `mu`. -/
theorem mu_add_T {u1 u2 v2 : K} (hT : (sW A B).toAffine.Nonsingular u1 0)
    (hR : (sW A B).toAffine.Nonsingular u2 v2) (hx : u1 ≠ u2) (hv2 : v2 ≠ 0) :
    mu D A B (Point.some u1 0 hT + Point.some u2 v2 hR) = mu D A B (Point.some u2 v2 hR) := by
  have key : (Point.some u1 0 hT + Point.some u2 v2 hR) +
      (Point.some u1 0 hT + Point.some u2 v2 hR) ≠ 0 := by
    intro h; apply hv2; rw [← t2_iff hR]
    have hT2 := (t2_iff hT).mpr rfl
    calc Point.some u2 v2 hR + Point.some u2 v2 hR =
        (Point.some u1 0 hT + Point.some u2 v2 hR) + (Point.some u1 0 hT + Point.some u2 v2 hR) -
          (Point.some u1 0 hT + Point.some u1 0 hT) := by abel
      _ = 0 := by rw [h, hT2, sub_zero]
  rw [add_of_X_ne hx] at key ⊢
  rw [Ne, t2_iff, addY_sW, zero_add] at key
  have hl := slope_of_X_ne (W := (sW A B).toAffine) (y₁ := (0 : K)) (y₂ := v2) hx
  have hu : u2 - u1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hl' : (sW A B).toAffine.slope u1 u2 0 v2 * (u2 - u1) = v2 := by
    rw [hl, div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.mpr hx)]; ring
  simp only [mu]
  rw [addX_sW, addY_sW, zero_add]
  have h1 : u1 ^ 3 + A * u1 + B = 0 := by have := eqn hT; linear_combination -this
  have := case_T D hΔ h1 (eqn hR) (hs_of hT) hu hv2 hl' key
  rw [this, bvU_zero, muP_zero, zero_add]

/-- **The Manin map is additive.** -/
theorem mu_add (P Q : (sW A B).toAffine.Point) : mu D A B (P + Q) = mu D A B P + mu D A B Q := by
  rcases P with _ | ⟨u1, v1, h1⟩
  · show mu D A B (0 + Q) = mu D A B 0 + mu D A B Q
    rw [zero_add]; simp [mu]
  rcases Q with _ | ⟨u2, v2, h2⟩
  · show mu D A B (_ + 0) = _ + mu D A B 0
    rw [add_zero]; simp [mu]
  have e1 := eqn h1
  have e2 := eqn h2
  by_cases hx : u1 = u2
  · subst hx
    by_cases hy : v1 = (sW A B).toAffine.negY u1 v2
    · rw [add_of_Y_eq rfl hy]
      have : Point.some u1 v1 h1 = -Point.some u1 v2 h2 := by
        simp only [neg_some, Point.some.injEq, true_and]; exact hy
      rw [this, mu_neg, show mu D A B 0 = 0 from rfl]
      ring
    · rw [negY_sW] at hy
      have hvv : v1 = v2 := by
        have : (v1 - v2) * (v1 + v2) = 0 := by linear_combination e1 - e2
        rcases mul_eq_zero.mp this with h | h
        · linear_combination h
        · exact absurd (by linear_combination h) hy
      subst hvv
      have hv1 : v1 ≠ 0 := fun h0 ↦ hy (by rw [h0, _root_.neg_zero])
      -- doubling
      have hy' : v1 ≠ (sW A B).toAffine.negY u1 v1 := by rwa [negY_sW]
      have hl := slope_of_Y_ne (W := (sW A B).toAffine) (rfl : u1 = u1) hy'
      set l := (sW A B).toAffine.slope u1 u1 v1 v1
      have hl' : l * (2 * v1) = 3 * u1 ^ 2 + A := by
        have : v1 - -v1 ≠ 0 := by
          intro h; apply hv1; linear_combination h / 2
        rw [hl, negY_sW, div_mul_eq_mul_div, div_eq_iff this]
        simp only [sW]; ring
      by_cases hv3 : -(v1 + l * ((l ^ 2 - u1 - u1) - u1)) = 0
      · -- `2P` is `2`-torsion: `mu P = 0`
        have hns := nonsingular_add h1 h1 fun hxy => hy' hxy.right
        have hnsS : (sW A B).toAffine.Nonsingular (l ^ 2 - u1 - u1) 0 := by
          have := hns; rw [addX_sW, addY_sW, hv3] at this; exact this
        have hSeq : Point.some u1 v1 h1 + Point.some u1 v1 h1 = Point.some _ _ hnsS := by
          rw [add_some (fun hxy => hy' hxy.right)]; congr 1
          · exact addX_sW _ _ _
          · rw [addY_sW]; exact hv3
        have hne : l ^ 2 - u1 - u1 ≠ u1 := by
          intro h; apply hv1
          have := eqn hnsS
          rw [h] at this
          have : v1 ^ 2 = 0 := by linear_combination e1 - this
          exact pow_eq_zero_iff (two_ne_zero) |>.mp this
        have hT := mu_add_T D hΔ hnsS ((nonsingular_neg ..).mpr h1) hne
          (by rw [negY_sW]; exact neg_ne_zero.mpr hv1)
        have hP : Point.some _ _ hnsS + Point.some u1 ((sW A B).toAffine.negY u1 v1)
            ((nonsingular_neg ..).mpr h1) = Point.some u1 v1 h1 := by
          rw [← hSeq, ← neg_some h1]; abel
        rw [hP, ← neg_some h1, mu_neg] at hT
        rw [hSeq, mu_two_tors]
        linear_combination -hT
      · rw [add_some (fun hxy => hy' hxy.right)]
        simp only [mu, addX_sW, addY_sW]
        have := case_D D hΔ e1 hv1 hl' (by rwa [show l ^ 2 - 2 * u1 = l ^ 2 - u1 - u1 by ring])
        rw [show l ^ 2 - u1 - u1 = l ^ 2 - 2 * u1 by ring]
        exact this
  · -- chord
    have hl := slope_of_X_ne (W := (sW A B).toAffine) (y₁ := v1) (y₂ := v2) hx
    set l := (sW A B).toAffine.slope u1 u2 v1 v2
    have hu : u2 - u1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hl' : l * (u2 - u1) = v2 - v1 := by
      rw [hl, div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.mpr hx)]; ring
    by_cases hv1 : v1 = 0
    · subst hv1
      by_cases hv2 : v2 = 0
      · subst hv2
        rw [add_of_X_ne hx]
        simp only [mu, addX_sW, addY_sW]
        rw [show (sW A B).toAffine.slope u1 u2 0 0 = 0 by rw [slope_of_X_ne hx]; simp]
        simp [bvU_zero, muP_zero]
      · rw [mu_add_T D hΔ h1 h2 hx hv2, mu_two_tors, zero_add]
    by_cases hv2 : v2 = 0
    · subst hv2
      rw [add_comm, mu_add_T D hΔ h2 h1 (Ne.symm hx) hv1, mu_two_tors, add_zero]
    by_cases hv3 : -(v1 + l * ((l ^ 2 - u1 - u2) - u1)) = 0
    · -- the sum is `2`-torsion: `Q = S + (-P)`
      have hns := nonsingular_add h1 h2 fun hxy => hx hxy.left
      have hnsS : (sW A B).toAffine.Nonsingular (l ^ 2 - u1 - u2) 0 := by
        have := hns; rw [addX_sW, addY_sW, hv3] at this; exact this
      have hSeq : Point.some u1 v1 h1 + Point.some u2 v2 h2 = Point.some _ _ hnsS := by
        rw [add_of_X_ne hx]; congr 1
        · exact addX_sW _ _ _
        · rw [addY_sW]; exact hv3
      have hne : l ^ 2 - u1 - u2 ≠ u1 := by
        intro h; apply hv1
        have := eqn hnsS
        rw [h] at this
        have : v1 ^ 2 = 0 := by linear_combination e1 - this
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      have hT := mu_add_T D hΔ hnsS ((nonsingular_neg ..).mpr h1) hne
        (by rw [negY_sW]; exact neg_ne_zero.mpr hv1)
      have hQ : Point.some _ _ hnsS + Point.some u1 ((sW A B).toAffine.negY u1 v1)
          ((nonsingular_neg ..).mpr h1) = Point.some u2 v2 h2 := by
        rw [← hSeq, ← neg_some h1]; abel
      rw [hQ, ← neg_some h1, mu_neg] at hT
      rw [hSeq, mu_two_tors, hT]; ring
    · rw [add_of_X_ne hx]
      simp only [mu, addX_sW, addY_sW]
      exact case_G D hΔ e1 e2 hu hv1 hv2 hl' hv3

/-- The Manin map as a group homomorphism. -/
def muHom : (sW A B).toAffine.Point →+ K where
  toFun := mu D A B
  map_zero' := rfl
  map_add' := mu_add D hΔ

/-- Torsion points lie in the kernel. -/
theorem mu_torsion {T : (sW A B).toAffine.Point} {k : ℕ} (hk : k ≠ 0) (hT : k • T = 0) :
    mu D A B T = 0 := by
  have := congrArg (muHom D hΔ) hT
  rw [map_nsmul, _root_.map_zero, nsmul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hk)

omit hΔ in
theorem D_intCast (n : ℤ) : D (n : K) = 0 := D.map_intCast n

/-- **Independence certificate.** A non-zero Wronskian of `mu P, mu Q` excludes every relation
`m P = n Q + T` with `T` torsion and `(m, n) ≠ (0, 0)`. -/
theorem indep_of_wronskian (P Q : (sW A B).toAffine.Point)
    (hW : mu D A B P * D (mu D A B Q) - mu D A B Q * D (mu D A B P) ≠ 0)
    (m n : ℤ) (T : (sW A B).toAffine.Point) (k : ℕ) (hk : k ≠ 0) (hT : k • T = 0)
    (hrel : m • P = n • Q + T) : m = 0 ∧ n = 0 := by
  have h := congrArg (muHom D hΔ) hrel
  simp only [map_zsmul, map_add, zsmul_eq_mul] at h
  have hT0 : muHom D hΔ T = 0 := mu_torsion D hΔ hk hT
  rw [hT0, add_zero] at h
  change (m : K) * mu D A B P = n * mu D A B Q at h
  have hD := congrArg D h
  simp only [D.leibniz, smul_eq_mul, D_intCast, mul_zero, add_zero] at hD
  -- `m W = 0` and `n W = 0`
  have hm : (m : K) * (mu D A B P * D (mu D A B Q) - mu D A B Q * D (mu D A B P)) = 0 := by
    linear_combination D (mu D A B Q) * h - mu D A B Q * hD
  have hn : (n : K) * (mu D A B P * D (mu D A B Q) - mu D A B Q * D (mu D A B P)) = 0 := by
    linear_combination D (mu D A B P) * h - mu D A B P * hD
  exact ⟨by exact_mod_cast (mul_eq_zero.mp hm).resolve_right hW,
    by exact_mod_cast (mul_eq_zero.mp hn).resolve_right hW⟩

/-- **Independence certificate (constant ratio).** If `mu P ≠ 0` and `mu Q = c · mu P` with `c`
not a rational number, no relation `m P = n Q + T` (`T` torsion, `(m, n) ≠ 0`) holds. Together
with `indep_of_wronskian` this covers every pair whose Manin images are `ℚ`-independent. -/
theorem indep_of_ratio (P Q : (sW A B).toAffine.Point) (hP0 : mu D A B P ≠ 0) (c : K)
    (hc : mu D A B Q = c * mu D A B P) (hcq : ∀ q : ℚ, c ≠ q)
    (m n : ℤ) (T : (sW A B).toAffine.Point) (k : ℕ) (hk : k ≠ 0) (hT : k • T = 0)
    (hrel : m • P = n • Q + T) : m = 0 ∧ n = 0 := by
  have h := congrArg (muHom D hΔ) hrel
  simp only [map_zsmul, map_add, zsmul_eq_mul] at h
  have hT0 : muHom D hΔ T = 0 := mu_torsion D hΔ hk hT
  rw [hT0, add_zero] at h
  change (m : K) * mu D A B P = n * mu D A B Q at h
  rw [hc] at h
  have h' : ((m : K) - n * c) * mu D A B P = 0 := by linear_combination h
  have h'' := (mul_eq_zero.mp h').resolve_right hP0
  by_cases hn : n = 0
  · subst hn
    simp only [Int.cast_zero, zero_mul, sub_zero, Int.cast_eq_zero] at h''
    exact ⟨h'', rfl⟩
  · exfalso
    apply hcq ((m : ℚ) / n)
    have hn' : (n : K) ≠ 0 := by exact_mod_cast hn
    push_cast
    field_simp
    linear_combination -h''

end Manin
