import RischTragerBronstein.Mixed.KFRatGuess
import RischTragerBronstein.Mixed.KFConstPts
import RischTragerBronstein.Mixed.QHeightExists
import RischTragerBronstein.Mixed.QIndepExists

/-!
# The height part of the level-`m + 1` constant-curve checks passes (linear base)

On `y² = x³ + a x + b` (`a, b ∈ ℤ`) over `Kₘ(X)`, every point has rational coordinates
(`rat_point_KF`), which `ptRat` reads off (`ptRat_some`); a point of infinite order (resp. two
independent points) then passes `certH` (resp. `certG`) at some level (`ck_tail_existsS`,
`tk_tail_existsS`).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

lemma isConstK_of_natDegree (p : CPoly K) (h : (CPoly.toPoly p).natDegree = 0) :
    isConstK p = true := by
  rcases p with _ | ⟨c, t⟩
  · rfl
  · simp only [isConstK, List.tail_cons, List.all_eq_true, beq_iff_eq]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have h1 := CPoly.coeff_toPoly (c :: t) (i + 1)
    rw [coeff_eq_zero_of_natDegree_lt (by omega)] at h1
    rw [h1]
    simp [List.getD_eq_getElem?_getD, hi]

/-- **A constant value has a constant reduced representation, with the right ratio.** -/
lemma isConstK_norm (f : Fr K) (hf : Fr.ok f) (c : K)
    (hv : Fr.val f = algebraMap K (RatFunc K) c) :
    isConstK (Fr.norm f).1 = true ∧ isConstK (Fr.norm f).2 = true ∧
      (Fr.norm f).1.headD 0 / (Fr.norm f).2.headD 0 = c := by
  set u := CPoly.toPoly (Fr.norm f).1
  set v := CPoly.toPoly (Fr.norm f).2
  have hv0 : v ≠ 0 := Fr.ok_norm hf
  have hcop : IsCoprime u v := reduce_coprime f.1 f.2 hf
  have hval : Fr.val (Fr.norm f) = algebraMap K (RatFunc K) c := by rw [Fr.val_norm hf, hv]
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have huv : u = C c * v := by
    apply hinj
    have hιv : algebraMap K[X] (RatFunc K) v ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv0
    simp only [Fr.val] at hval
    rw [map_mul, RatFunc.algebraMap_C]
    rw [div_eq_iff hιv] at hval
    exact hval
  have hu : IsUnit v := by
    rw [huv] at hcop
    exact isCoprime_self.mp (hcop.of_mul_left_right)
  have hvd : v.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  have hvC := eq_C_of_natDegree_eq_zero hvd
  have hv00 : v.coeff 0 ≠ 0 := fun h ↦ hv0 (by rw [hvC, h, map_zero])
  refine ⟨isConstK_of_natDegree _ ?_, isConstK_of_natDegree _ hvd, ?_⟩
  · show u.natDegree = 0
    rw [huv, hvC, ← C_mul]; exact natDegree_C _
  · rw [Curves.MT.headD_eq_coeff, Curves.MT.headD_eq_coeff]
    show u.coeff 0 / v.coeff 0 = c
    rw [huv, coeff_C_mul]; field_simp

/-- A rational function with a constant square is constant. -/
lemma const_of_sq_constK (Y : RatFunc K) (c : K) (h : Y ^ 2 = algebraMap K (RatFunc K) c) :
    ∃ y : K, Y = algebraMap K (RatFunc K) y := by
  obtain ⟨d, hd⟩ := Curves.MT.sq_const_ratFunc Y c h
  have h2 : (Y - algebraMap K (RatFunc K) d) * (Y + algebraMap K (RatFunc K) d) = 0 := by
    have e : (Y - algebraMap K (RatFunc K) d) * (Y + algebraMap K (RatFunc K) d) =
        Y ^ 2 - algebraMap K (RatFunc K) (d * d) := by rw [map_mul]; ring
    rw [e, h, ← hd, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact ⟨d, sub_eq_zero.mp h3⟩
  · exact ⟨-d, by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h3⟩

end FFHeight

namespace Curves.MT

open CPoly Sup FFHeight

/-- Rational squares in `Kₘ` are squares in `ℚ` (linear base). -/
lemma isSquare_of_KF (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))] (r : ℚ) (m : ℕ)
    (h : IsSquare ((r : ℚ) : KF [c0, [1]] m)) : IsSquare r := by
  by_contra hn; exact not_isSquare_KF c0 r hn m h

variable (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))]

/-- **Points of constant curves over `Kₘ(X)` are rational** (linear base). -/
theorem rat_point_KF (m : ℕ) (a b : ℚ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (X Y : RatFunc (KF [c0, [1]] m)) (h : Y ^ 2 = X ^ 3 + (a : RatFunc (KF [c0, [1]] m)) * X +
      (b : RatFunc (KF [c0, [1]] m))) :
    ∃ x0 y0 : ℚ, X = algebraMap ℚ _ x0 ∧ Y = algebraMap ℚ _ y0 := by
  set K := KF [c0, [1]] m
  obtain ⟨c, d, hc, hd⟩ := ratFunc_point_const a b hΔ X Y h
  obtain ⟨q, rfl⟩ := KF_point_rat c0 a b hΔ m c d hd
  have hY2 : Y ^ 2 = algebraMap K (RatFunc K) ((q ^ 3 + a * q + b : ℚ) : K) := by
    rw [h, hc]; simp [RatFunc.algebraMap_C, map_ratCast]
  obtain ⟨y, hy⟩ := const_of_sq_constK Y _ hY2
  have hy2 : y ^ 2 = ((q ^ 3 + a * q + b : ℚ) : K) := by
    apply (algebraMap K (RatFunc K)).injective
    rw [map_pow, ← hy, hY2]
  obtain ⟨t, ht⟩ := isSquare_of_KF c0 _ m ⟨y, by rw [← sq, hy2]⟩
  have hyt : (y - (t : K)) * (y + (t : K)) = 0 := by
    have : ((q ^ 3 + a * q + b : ℚ) : K) = (t : K) * (t : K) := by rw [ht]; push_cast; ring
    linear_combination hy2.trans this
  have hX : X = algebraMap ℚ (RatFunc K) q := by
    rw [hc, map_ratCast]; exact (eq_ratCast _ q).symm
  obtain ⟨y0, hY0⟩ : ∃ y0 : ℚ, Y = algebraMap ℚ (RatFunc K) y0 := by
    rcases mul_eq_zero.mp hyt with h1 | h1
    · exact ⟨t, by rw [hy, sub_eq_zero.mp h1, map_ratCast]; exact (eq_ratCast _ t).symm⟩
    · refine ⟨-t, ?_⟩
      rw [hy, eq_neg_of_add_eq_zero_left h1, map_neg, map_ratCast, map_neg]
      exact congrArg Neg.neg (eq_ratCast _ t).symm
  exact ⟨q, y0, hX, hY0⟩

open scoped Classical in
/-- `ptRat` reads the rational coordinates of a point on the constant model. -/
lemma ptRat_of_rel (m : ℕ) (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (fx fy : Fr (KF [c0, [1]] m))
    (PD : (shortW (Polynomial.C ((a : ℚ) : KF [c0, [1]] m))
      (Polynomial.C ((b : ℚ) : KF [c0, [1]] m))).toAffine.Point)
    (hR : Rel _ _ (some (fx, fy)) PD) :
    ∃ x0 y0 : ℚ, ptRat [c0, [1]] m (some (fx, fy)) = some (x0, y0) ∧
      Fr.val fx = algebraMap ℚ (RatFunc (KF [c0, [1]] m)) x0 ∧
      Fr.val fy = algebraMap ℚ (RatFunc (KF [c0, [1]] m)) y0 := by
  rcases PD with _ | ⟨X, Y, hXY⟩
  · exact absurd hR (by simp [FFHeight.Rel])
  obtain ⟨ox, oy, hX, hY⟩ := hR
  have heq := hXY.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [FFHeight.shortW, zero_mul, add_zero, RatFunc.algebraMap_C, map_ratCast] at heq
  have hΔq : 4 * ((a : ℤ) : ℚ) ^ 3 + 27 * ((b : ℤ) : ℚ) ^ 2 ≠ 0 := by exact_mod_cast hΔ
  obtain ⟨x0, y0, eX, eY⟩ := rat_point_KF c0 m a b hΔq X Y (by
    push_cast at heq ⊢; linear_combination heq)
  have hx : Fr.val fx = algebraMap (KF [c0, [1]] m) (RatFunc (KF [c0, [1]] m)) (x0 : KF [c0, [1]] m) := by
    rw [hX, eX, eq_ratCast (algebraMap ℚ _), map_ratCast]
  have hy : Fr.val fy = algebraMap (KF [c0, [1]] m) (RatFunc (KF [c0, [1]] m)) (y0 : KF [c0, [1]] m) := by
    rw [hY, eY, eq_ratCast (algebraMap ℚ _), map_ratCast]
  obtain ⟨cx1, cx2, rx⟩ := isConstK_norm fx ox _ hx
  obtain ⟨cy1, cy2, ry⟩ := isConstK_norm fy oy _ hy
  refine ⟨x0, y0, ?_, by rw [hX, eX], by rw [hY, eY]⟩
  simp only [ptRat, normPtK, ratFr, cx1, cx2, cy1, cy2, Bool.and_self, ite_true, rx, ry,
    ratOfK_ratCast]

open scoped Classical in
/-- **The height part of `kxChkCKS` passes on a point of infinite order.** -/
theorem ck_tail_existsS (m : ℕ) (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (p : PtC (KF [c0, [1]] m))
    (A B : (KF [c0, [1]] m)[X]) (hA : A = Polynomial.C ((a : ℚ) : KF [c0, [1]] m))
    (hB : B = Polynomial.C ((b : ℚ) : KF [c0, [1]] m)) (PD : (shortW A B).toAffine.Point)
    (hR : Rel _ _ p PD) (hnt : ∀ n : ℤ, n • PD = 0 → n = 0) :
    ∃ kk, (match ptRat [c0, [1]] m p with
      | some (x0, _) => QHeight.certH a b kk x0
      | none => false) = true := by
  subst hA hB
  rcases p with _ | ⟨fx, fy⟩
  · exfalso
    rcases PD with _ | ⟨X, Y, hXY⟩
    · exact one_ne_zero (hnt 1 (by rw [one_zsmul]; rfl))
    · exact absurd hR (by simp [FFHeight.Rel])
  obtain ⟨x0, y0, hp, hx, hy⟩ := ptRat_of_rel c0 m a b hΔ fx fy PD hR
  have hAa : Polynomial.C ((a : ℚ) : KF [c0, [1]] m) = Polynomial.C ((a : KF [c0, [1]] m)) := by
    push_cast; rfl
  have hBb : Polynomial.C ((b : ℚ) : KF [c0, [1]] m) = Polynomial.C ((b : KF [c0, [1]] m)) := by
    push_cast; rfl
  obtain ⟨h0, e0⟩ := const_pointK a b fx fy x0 y0 hx hy _ _ hAa hBb PD hR
  have hntQ : ∀ n : ℕ, 0 < n → n • Point.some _ _ h0 ≠ 0 := by
    intro n hn h0'
    have : ((n : ℤ) • PD) = 0 := by
      apply castHom_injective (by rw [hAa, hBb] : (shortW (Polynomial.C ((a : ℚ) : KF [c0, [1]] m))
        (Polynomial.C ((b : ℚ) : KF [c0, [1]] m))).toAffine =
        (shortW (Polynomial.C ((a : KF [c0, [1]] m))) (Polynomial.C ((b : KF [c0, [1]] m)))).toAffine)
      rw [map_zsmul, e0, ← map_zsmul, natCast_zsmul, h0', map_zero, map_zero]
    have := hnt n this
    omega
  obtain ⟨kk, hk⟩ := QHeight.certH_exists a b _ _ h0 hntQ
  exact ⟨kk, by rw [hp]; exact hk⟩

open scoped Classical in
/-- **The height part of `kxChkTKS` passes on independent points.** -/
theorem tk_tail_existsS (m : ℕ) (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (p p' : PtC (KF [c0, [1]] m))
    (A B : (KF [c0, [1]] m)[X]) (hA : A = Polynomial.C ((a : ℚ) : KF [c0, [1]] m))
    (hB : B = Polynomial.C ((b : ℚ) : KF [c0, [1]] m)) (PD PZ : (shortW A B).toAffine.Point)
    (hRD : Rel _ _ p PD) (hRZ : Rel _ _ p' PZ)
    (hind : ∀ m' n : ℤ, m' • PD = n • PZ → m' = 0 ∧ n = 0) :
    ∃ kk, (match ptRat [c0, [1]] m p, ptRat [c0, [1]] m p' with
      | some (x1, y1), some (x2, y2) => QHeight.certG a b kk x1 y1 x2 y2
      | _, _ => false) = true := by
  subst hA hB
  have hD0 : PD ≠ 0 := fun h ↦ by
    have := hind 1 0 (by rw [one_zsmul, zero_zsmul, h]); exact one_ne_zero this.1
  have hZ0 : PZ ≠ 0 := fun h ↦ by
    have := hind 0 1 (by rw [one_zsmul, zero_zsmul, h]); exact one_ne_zero this.2
  rcases p with _ | ⟨fx, fy⟩
  · exfalso; rcases PD with _ | ⟨X, Y, hXY⟩
    · exact hD0 rfl
    · exact absurd hRD (by simp [FFHeight.Rel])
  rcases p' with _ | ⟨gx, gy⟩
  · exfalso; rcases PZ with _ | ⟨X, Y, hXY⟩
    · exact hZ0 rfl
    · exact absurd hRZ (by simp [FFHeight.Rel])
  obtain ⟨x1, y1, hp1, hx1, hy1⟩ := ptRat_of_rel c0 m a b hΔ fx fy PD hRD
  obtain ⟨x2, y2, hp2, hx2, hy2⟩ := ptRat_of_rel c0 m a b hΔ gx gy PZ hRZ
  have hAa : Polynomial.C ((a : ℚ) : KF [c0, [1]] m) = Polynomial.C ((a : KF [c0, [1]] m)) := by
    push_cast; rfl
  have hBb : Polynomial.C ((b : ℚ) : KF [c0, [1]] m) = Polynomial.C ((b : KF [c0, [1]] m)) := by
    push_cast; rfl
  obtain ⟨h1, e1⟩ := const_pointK a b fx fy x1 y1 hx1 hy1 _ _ hAa hBb PD hRD
  obtain ⟨h2, e2⟩ := const_pointK a b gx gy x2 y2 hx2 hy2 _ _ hAa hBb PZ hRZ
  have hindQ : ∀ m' n : ℤ, m' • Point.some _ _ h1 = n • Point.some _ _ h2 → m' = 0 ∧ n = 0 := by
    intro m' n hmn
    apply hind m' n
    apply castHom_injective (by rw [hAa, hBb] : (shortW (Polynomial.C ((a : ℚ) : KF [c0, [1]] m))
        (Polynomial.C ((b : ℚ) : KF [c0, [1]] m))).toAffine =
        (shortW (Polynomial.C ((a : KF [c0, [1]] m))) (Polynomial.C ((b : KF [c0, [1]] m)))).toAffine)
    rw [map_zsmul, map_zsmul, e1, e2, ← map_zsmul, ← map_zsmul, hmn]
  obtain ⟨kk, hk⟩ := QHeight.certG_exists a b hΔ _ _ _ _ h1 h2 hindQ
  exact ⟨kk, by rw [hp1, hp2]; exact hk⟩

end Curves.MT
