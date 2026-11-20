import RischTragerBronstein.Mixed.KXMWDecideK
import RischTragerBronstein.Mixed.EllConstPts
import RischTragerBronstein.Mixed.QHeightExists
import RischTragerBronstein.Mixed.QIndepExists
import RischTragerBronstein.Mixed.KFSquare

/-!
# Completeness of the constant-curve checks: structural facts

* `isConstB_of_natDegree`, `isConstB_norm`: a fraction with a constant value has constant reduced
  numerator and denominator, so the `isConstB` tests of the (normalized) checks pass.
-/

open Polynomial

namespace FFHeight

lemma isConstB_of_natDegree (p : CPoly ℚ) (h : (CPoly.toPoly p).natDegree = 0) : isConstB p = true := by
  rcases p with _ | ⟨c, t⟩
  · rfl
  · simp only [isConstB, List.tail_cons, List.all_eq_true, beq_iff_eq]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have h1 := CPoly.coeff_toPoly (c :: t) (i + 1)
    rw [coeff_eq_zero_of_natDegree_lt (by omega)] at h1
    rw [h1]
    simp [List.getD_eq_getElem?_getD, hi]

/-- **A constant value has a constant reduced representation.** -/
lemma isConstB_norm (f : Fr ℚ) (hf : Fr.ok f) (c : ℚ)
    (hv : Fr.val f = algebraMap ℚ (RatFunc ℚ) c) :
    isConstB (Fr.norm f).1 = true ∧ isConstB (Fr.norm f).2 = true := by
  set u := CPoly.toPoly (Fr.norm f).1
  set v := CPoly.toPoly (Fr.norm f).2
  have hv0 : v ≠ 0 := Fr.ok_norm hf
  have hcop : IsCoprime u v := reduce_coprime f.1 f.2 hf
  have hval : Fr.val (Fr.norm f) = algebraMap ℚ (RatFunc ℚ) c := by rw [Fr.val_norm hf, hv]
  have hinj := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have huv : u = C c * v := by
    apply hinj
    have hιv : algebraMap ℚ[X] (RatFunc ℚ) v ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv0
    simp only [Fr.val] at hval
    rw [map_mul, RatFunc.algebraMap_C]
    rw [div_eq_iff hιv] at hval
    convert hval using 2
    rw [eq_ratCast RatFunc.C, eq_ratCast (algebraMap ℚ (RatFunc ℚ))]
  have hu : IsUnit v := by
    rw [huv] at hcop
    exact isCoprime_self.mp (hcop.of_mul_left_right)
  have hvd : v.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  refine ⟨isConstB_of_natDegree _ ?_, isConstB_of_natDegree _ hvd⟩
  show u.natDegree = 0
  rw [huv, eq_C_of_natDegree_eq_zero hvd, ← C_mul]; exact natDegree_C _

lemma dropWhile_zeros_append (t : List ℚ) (ht : ∀ x ∈ t, x = 0) (l : List ℚ) :
    (t ++ l).dropWhile (fun x ↦ decide (x = 0)) = l.dropWhile (fun x ↦ decide (x = 0)) := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    rw [List.cons_append, List.dropWhile_cons, if_pos (by simp [ht a List.mem_cons_self])]
    exact ih fun x hx ↦ ht x (List.mem_cons_of_mem _ hx)

lemma trim_of_isConstB (p : CPoly ℚ) (h : isConstB p = true) :
    CPoly.trim p = if p.headD 0 = 0 then [] else [p.headD 0] := by
  rcases p with _ | ⟨c, t⟩
  · simp [CPoly.trim]
  · have ht : ∀ x ∈ t, x = 0 := by
      simpa [isConstB, List.all_eq_true] using h
    simp only [CPoly.trim, List.reverse_cons, List.headD_cons]
    rw [dropWhile_zeros_append _ (fun x hx ↦ ht x (List.mem_reverse.mp hx))]
    by_cases hc : c = 0 <;> simp [hc]

/-- **`polyOf` reads the value of a constant fraction.** -/
lemma polyOf_head (f : Fr ℚ) (hf : Fr.ok f) (c : ℚ) (hv : Fr.val f = algebraMap ℚ (RatFunc ℚ) c) :
    (Curves.MT.polyOf f).headD 0 = c := by
  obtain ⟨h1, h2⟩ := isConstB_norm f hf c hv
  have hok := Fr.ok_norm hf
  have hval : Fr.val (Fr.norm f) = algebraMap ℚ (RatFunc ℚ) c := by rw [Fr.val_norm hf, hv]
  set p := (Fr.norm f).1
  set q := (Fr.norm f).2
  have hp := toPoly_of_isConstB h1
  have hq := toPoly_of_isConstB h2
  have hq0 : q.headD 0 ≠ 0 := by
    intro h0; apply hok; show CPoly.toPoly q = 0; rw [hq, h0, C_0]
  have hpc : p.headD 0 = c * q.headD 0 := by
    simp only [Fr.val] at hval
    rw [hp, hq, RatFunc.algebraMap_C, RatFunc.algebraMap_C] at hval
    have hqq : (RatFunc.C (q.headD 0) : RatFunc ℚ) ≠ 0 := by
      rw [← RatFunc.algebraMap_C]; exact (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] _)).mpr
        (C_ne_zero.mpr hq0)
    rw [div_eq_iff hqq] at hval
    have := congrArg (fun r : RatFunc ℚ ↦ r) hval
    rw [eq_ratCast (algebraMap ℚ (RatFunc ℚ)), ← eq_ratCast RatFunc.C, ← map_mul] at hval
    exact RatFunc.C_injective hval
  unfold Curves.MT.polyOf
  rw [trim_of_isConstB _ h1, trim_of_isConstB _ h2, if_neg hq0]
  split_ifs with hp0
  · simp only [List.map_nil, List.headD_nil]
    rw [hp0] at hpc
    exact ((mul_eq_zero.mp hpc.symm).resolve_right hq0).symm
  · simp only [List.map_cons, List.map_nil, List.headD_cons]
    rw [hpc]; field_simp

/-- A rational function with a constant square is constant. -/
lemma const_of_sq_const (Y : RatFunc ℚ) (c : ℚ) (h : Y ^ 2 = RatFunc.C c) :
    ∃ y : ℚ, Y = RatFunc.C y := by
  obtain ⟨d, hd⟩ := Curves.MT.sq_const_ratFunc Y c (by
    rw [h, eq_ratCast RatFunc.C]; exact (eq_ratCast _ c).symm)
  have h2 : (Y - RatFunc.C d) * (Y + RatFunc.C d) = 0 := by
    have e : (Y - RatFunc.C d) * (Y + RatFunc.C d) = Y ^ 2 - RatFunc.C (d * d) := by
      rw [map_mul]; ring
    rw [e, h, ← hd, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact ⟨d, sub_eq_zero.mp h3⟩
  · exact ⟨-d, by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h3⟩


end FFHeight

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

/-- **Normalized codes are well formed.** -/
lemma codeOKb_normC (Fc : Sup.BPoly ℚ) [Fact (Irreducible (CPoly.toPoly (fKc Fc)))] (q : LC 0) :
    codeOKb (normC Fc 0 q) = true := by
  simp only [codeOKb, normC, unTr, List.all_map, List.all_eq_true, Function.comp_apply,
    Bool.not_eq_true']
  intro c _
  rw [Bool.eq_false_iff, Ne, CPoly.isZero_iff]
  exact (RFC.canon_spec c).1

section Vals

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (c0f : CPoly ℚ) (A : GPoly (LC 0))

/-- The constant fractions. -/
def IsConstFr (f : Fr ℚ) (c : ℚ) : Prop := Fr.ok f ∧ Fr.val f = algebraMap ℚ (RatFunc ℚ) c

lemma constFr_mul {f g : Fr ℚ} {a b : ℚ} (hf : IsConstFr f a) (hg : IsConstFr g b) :
    IsConstFr (Fr.mul f g) (a * b) :=
  ⟨Fr.ok_mul hf.1 hg.1, by rw [Fr.val_mul hf.1 hg.1, hf.2, hg.2, map_mul]⟩

lemma constFr_sub {f g : Fr ℚ} {a b : ℚ} (hf : IsConstFr f a) (hg : IsConstFr g b) :
    IsConstFr (Fr.sub f g) (a - b) :=
  ⟨Fr.ok_sub hf.1 hg.1, by rw [Fr.val_sub hf.1 hg.1, hf.2, hg.2, map_sub]⟩

lemma constFr_add {f g : Fr ℚ} {a b : ℚ} (hf : IsConstFr f a) (hg : IsConstFr g b) :
    IsConstFr (Fr.add f g) (a + b) :=
  ⟨Fr.ok_add hf.1 hg.1, by rw [Fr.val_add hf.1 hg.1, hf.2, hg.2, map_add]⟩

lemma constFr_smulC {f : Fr ℚ} {a : ℚ} (c : ℚ) (hf : IsConstFr f a) :
    IsConstFr (Fr.smulC c f) (c * a) :=
  ⟨Fr.ok_smulC c hf.1, by
    rw [Fr.val_smulC, hf.2, map_mul]
    congr 1
    exact (eq_ratCast _ c).trans (eq_ratCast _ c).symm⟩

lemma constFr_ofPoly (c : ℚ) : IsConstFr (Fr.ofPoly [c]) c :=
  ⟨Fr.ok_ofPoly _, by rw [Fr.val_ofPoly]; simp [CPoly.toPoly, RatFunc.algebraMap_C]⟩

/-- The reduced denominator of a constant fraction is a non-zero constant. -/
lemma constFr_den (f : Fr ℚ) (c : ℚ) (hf : IsConstFr f c) :
    ∃ d : ℚ, d ≠ 0 ∧ IsConstFr (Fr.ofPoly (Fr.norm f).2) d := by
  obtain ⟨-, h2⟩ := isConstB_norm f hf.1 c hf.2
  have hok := Fr.ok_norm hf.1
  have hq := toPoly_of_isConstB h2
  refine ⟨(Fr.norm f).2.headD 0, fun h0 ↦ hok (by show CPoly.toPoly _ = 0; rw [hq, h0, C_0]),
    Fr.ok_ofPoly _, ?_⟩
  rw [Fr.val_ofPoly, hq, RatFunc.algebraMap_C, eq_ratCast RatFunc.C,
    eq_ratCast (algebraMap ℚ (RatFunc ℚ))]

lemma constFr_foldr (l : List (Fr ℚ)) (hl : ∀ f ∈ l, ∃ d : ℚ, d ≠ 0 ∧ IsConstFr f d) :
    ∃ U : ℚ, U ≠ 0 ∧ IsConstFr (l.foldr Fr.mul (Fr.ofPoly [1])) U := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, constFr_ofPoly 1⟩
  | cons f l ih =>
    obtain ⟨d, hd, hf⟩ := hl f List.mem_cons_self
    obtain ⟨U, hU, hlU⟩ := ih fun g hg ↦ hl g (List.mem_cons_of_mem _ hg)
    exact ⟨d * U, mul_ne_zero hd hU, constFr_mul hf hlU⟩

/-- **The scaling of a constant curve is a non-zero constant.** -/
lemma mwU_const (r : ℕ → ℚ) (hcF : ∀ i < 4, IsConstFr (cF Fc ks c0f A i) (r i)) :
    ∃ U : ℚ, U ≠ 0 ∧ IsConstFr (mwU Fc ks c0f A) U := by
  apply constFr_foldr
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
  exact constFr_den _ _ (hcF i (List.mem_range.mp hi))

lemma AFr_const (r : ℕ → ℚ) (hcF : ∀ i < 4, IsConstFr (cF Fc ks c0f A i) (r i)) (uF : Fr ℚ) (u : ℚ)
    (hu : IsConstFr uF u) :
    IsConstFr (AFr Fc ks c0f A uF) (u * u * (u * u) * (r 1 * r 3 - 1 / 3 * (r 2 * r 2))) := by
  unfold AFr
  exact constFr_mul (constFr_mul (constFr_mul hu hu) (constFr_mul hu hu))
    (constFr_sub (constFr_mul (hcF 1 (by norm_num)) (hcF 3 (by norm_num)))
      (constFr_smulC _ (constFr_mul (hcF 2 (by norm_num)) (hcF 2 (by norm_num)))))

lemma BFr_const (r : ℕ → ℚ) (hcF : ∀ i < 4, IsConstFr (cF Fc ks c0f A i) (r i)) (uF : Fr ℚ) (u : ℚ)
    (hu : IsConstFr uF u) :
    IsConstFr (BFr Fc ks c0f A uF) (u * u * (u * u * (u * u)) *
      (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2)))) := by
  unfold BFr
  have h0 := hcF 0 (by norm_num); have h1 := hcF 1 (by norm_num)
  have h2 := hcF 2 (by norm_num); have h3 := hcF 3 (by norm_num)
  exact constFr_mul (constFr_mul (constFr_mul hu hu) (constFr_mul (constFr_mul hu hu) (constFr_mul hu hu)))
    (constFr_add (constFr_sub (constFr_mul h0 (constFr_mul h3 h3))
      (constFr_smulC _ (constFr_mul h2 (constFr_mul h1 h3))))
      (constFr_smulC _ (constFr_mul h2 (constFr_mul h2 h2))))

/-- `den α ∣ m` makes `mⁿ α` an integer (`n ≥ 1`). -/
lemma pow_mul_int (α : ℚ) (m : ℕ) (hm : α.den ∣ m) (n : ℕ) (hn : 1 ≤ n) :
    (((m : ℚ) ^ n * α).num : ℚ) = (m : ℚ) ^ n * α := by
  obtain ⟨k, hk⟩ := hm
  have e : (m : ℚ) ^ n * α = ((α.num * α.den ^ (n - 1) * k ^ n : ℤ) : ℚ) := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have h1 : α * α.den = α.num := Rat.mul_den_eq_num α
    rw [hk]; push_cast
    rw [← h1]; ring
  rw [e, Rat.num_intCast]

lemma Ac_head (r : ℕ → ℚ) (hcF : ∀ i < 4, IsConstFr (cF Fc ks c0f A i) (r i)) (s : ℚ) (uF : Fr ℚ)
    (u : ℚ) (hu : IsConstFr uF u) :
    (polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A uF))).headD 0 =
      s ^ 2 * (u * u * (u * u) * (r 1 * r 3 - 1 / 3 * (r 2 * r 2))) :=
  polyOf_head _ (constFr_smulC _ (AFr_const Fc ks c0f A r hcF _ u hu)).1 _
    (constFr_smulC _ (AFr_const Fc ks c0f A r hcF _ u hu)).2

lemma Bc_head (r : ℕ → ℚ) (hcF : ∀ i < 4, IsConstFr (cF Fc ks c0f A i) (r i)) (s : ℚ) (uF : Fr ℚ)
    (u : ℚ) (hu : IsConstFr uF u) :
    (polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A uF))).headD 0 =
      s ^ 3 * (u * u * (u * u * (u * u)) *
        (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2)))) :=
  polyOf_head _ (constFr_smulC _ (BFr_const Fc ks c0f A r hcF _ u hu)).1 _
    (constFr_smulC _ (BFr_const Fc ks c0f A r hcF _ u hu)).2

open scoped Classical in
/-- **The tail of the constant-curve check passes** on a point of infinite order. -/
theorem ck_tail_exists (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (A B : ℚ[X])
    (hA : A = Polynomial.C (a : ℚ)) (hB : B = Polynomial.C (b : ℚ)) (p : PtC ℚ)
    (PD : (shortW A B).toAffine.Point) (hR : Rel A B p PD)
    (hnt : ∀ n : ℤ, n • PD = 0 → n = 0) :
    ∃ kk, (match normPt p with
      | some (fx, fy) => isConstB fx.1 && isConstB fx.2 && isConstB fy.1 && isConstB fy.2 &&
          QHeight.certH a b kk (fx.1.headD 0 / fx.2.headD 0)
      | none => false) = true := by
  have hR' := rel_normPt hR
  rcases p with _ | ⟨fx, fy⟩
  · exfalso
    rcases PD with _ | ⟨X, Y, hXY⟩
    · exact one_ne_zero (hnt 1 (by rw [one_zsmul]; rfl))
    · exact absurd hR (by simp [FFHeight.Rel])
  rcases PD with _ | ⟨X, Y, hXY⟩
  · exact absurd hR (by simp [FFHeight.Rel])
  obtain ⟨ox, oy, hX, hY⟩ := hR
  -- the coordinates are constant
  have heq := hXY.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [shortW, zero_mul, add_zero, hA, hB, RatFunc.algebraMap_C] at heq
  have hΔq : 4 * (a : ℚ) ^ 3 + 27 * (b : ℚ) ^ 2 ≠ 0 := by exact_mod_cast hΔ
  obtain ⟨x0, hx0⟩ := EllConst.weierstrass_const (a : ℚ) b hΔq X Y (by linear_combination heq)
  obtain ⟨y0, hy0⟩ := const_of_sq_const Y (x0 ^ 3 + a * x0 + b) (by
    rw [heq, hx0]; simp only [map_add, map_mul, map_pow, map_intCast])
  have cx : IsConstFr fx x0 := ⟨ox, by rw [hX, hx0, eq_ratCast RatFunc.C,
    eq_ratCast (algebraMap ℚ (RatFunc ℚ))]⟩
  have cy : IsConstFr fy y0 := ⟨oy, by rw [hY, hy0, eq_ratCast RatFunc.C,
    eq_ratCast (algebraMap ℚ (RatFunc ℚ))]⟩
  obtain ⟨hx1, hx2⟩ := isConstB_norm fx cx.1 x0 cx.2
  obtain ⟨hy1, hy2⟩ := isConstB_norm fy cy.1 y0 cy.2
  -- the `ℚ`-point and its infinite order
  obtain ⟨h0, e0⟩ := const_point a b (Fr.norm fx) (Fr.norm fy) hx1 hx2 hy1 hy2 A B hA hB _ hR'
  have hntQ : ∀ n : ℕ, 0 < n → n • WeierstrassCurve.Affine.Point.some _ _ h0 ≠ 0 := by
    intro n hn h0'
    have : ((n : ℤ) • WeierstrassCurve.Affine.Point.some X Y hXY : (shortW A B).toAffine.Point) = 0 := by
      apply castHom_injective (by rw [hA, hB] : (shortW A B).toAffine =
        (shortW (Polynomial.C (a : ℚ)) (Polynomial.C (b : ℚ))).toAffine)
      rw [map_zsmul, e0, ← map_zsmul, natCast_zsmul, h0', map_zero, map_zero]
    have := hnt n this
    omega
  obtain ⟨kk, hk⟩ := QHeight.certH_exists a b _ _ h0 hntQ
  refine ⟨kk, ?_⟩
  simp only [normPt, hx1, hx2, hy1, hy2, hk, Bool.and_self]

open scoped Classical in
/-- Constant coordinates of a non-zero point on a constant model, with its `ℚ`-point. -/
theorem const_pt_of_rel (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (A B : ℚ[X])
    (hA : A = Polynomial.C (a : ℚ)) (hB : B = Polynomial.C (b : ℚ)) (fx fy : Fr ℚ)
    (PD : (shortW A B).toAffine.Point) (hR : Rel A B (some (fx, fy)) PD) :
    isConstB (Fr.norm fx).1 = true ∧ isConstB (Fr.norm fx).2 = true ∧
      isConstB (Fr.norm fy).1 = true ∧ isConstB (Fr.norm fy).2 = true := by
  have hR0 := hR
  subst hA hB
  rcases PD with _ | ⟨X, Y, hXY⟩
  · exact absurd hR (by simp [FFHeight.Rel])
  obtain ⟨ox, oy, hX, hY⟩ := hR
  have heq := hXY.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [shortW, zero_mul, add_zero, RatFunc.algebraMap_C] at heq
  have hΔq : 4 * (a : ℚ) ^ 3 + 27 * (b : ℚ) ^ 2 ≠ 0 := by exact_mod_cast hΔ
  obtain ⟨x0, hx0⟩ := EllConst.weierstrass_const (a : ℚ) b hΔq X Y (by linear_combination heq)
  obtain ⟨y0, hy0⟩ := const_of_sq_const Y (x0 ^ 3 + a * x0 + b) (by
    rw [heq, hx0]; simp only [map_add, map_mul, map_pow, map_intCast])
  have cx : IsConstFr fx x0 := ⟨ox, by rw [hX, hx0, eq_ratCast RatFunc.C,
    eq_ratCast (algebraMap ℚ (RatFunc ℚ))]⟩
  have cy : IsConstFr fy y0 := ⟨oy, by rw [hY, hy0, eq_ratCast RatFunc.C,
    eq_ratCast (algebraMap ℚ (RatFunc ℚ))]⟩
  obtain ⟨hx1, hx2⟩ := isConstB_norm fx cx.1 x0 cx.2
  obtain ⟨hy1, hy2⟩ := isConstB_norm fy cy.1 y0 cy.2
  exact ⟨hx1, hx2, hy1, hy2⟩

open scoped Classical in
/-- **The tail of the twisted constant-curve check passes** on two independent points. -/
theorem tk_tail_exists (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (A B : ℚ[X])
    (hA : A = Polynomial.C (a : ℚ)) (hB : B = Polynomial.C (b : ℚ)) (p p' : PtC ℚ)
    (PD PZ : (shortW A B).toAffine.Point) (hRD : Rel A B p PD) (hRZ : Rel A B p' PZ)
    (hind : ∀ m n : ℤ, m • PD = n • PZ → m = 0 ∧ n = 0) :
    ∃ kk, (match normPt p, normPt p' with
      | some (fx, fy), some (gx, gy) => isConstB fx.1 && isConstB fx.2 && isConstB fy.1 &&
          isConstB fy.2 && isConstB gx.1 && isConstB gx.2 && isConstB gy.1 && isConstB gy.2 &&
          QHeight.certG a b kk (fx.1.headD 0 / fx.2.headD 0) (fy.1.headD 0 / fy.2.headD 0)
            (gx.1.headD 0 / gx.2.headD 0) (gy.1.headD 0 / gy.2.headD 0)
      | _, _ => false) = true := by
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
  obtain ⟨hx1, hx2, hy1, hy2⟩ := const_pt_of_rel a b hΔ A B hA hB fx fy PD hRD
  obtain ⟨gx1, gx2, gy1, gy2⟩ := const_pt_of_rel a b hΔ A B hA hB gx gy PZ hRZ
  have hRD' := rel_normPt hRD
  have hRZ' := rel_normPt hRZ
  obtain ⟨h1, e1⟩ := const_point a b (Fr.norm fx) (Fr.norm fy) hx1 hx2 hy1 hy2 A B hA hB _ hRD'
  obtain ⟨h2, e2⟩ := const_point a b (Fr.norm gx) (Fr.norm gy) gx1 gx2 gy1 gy2 A B hA hB _ hRZ'
  have hindQ : ∀ m n : ℤ, m • WeierstrassCurve.Affine.Point.some _ _ h1 =
      n • WeierstrassCurve.Affine.Point.some _ _ h2 → m = 0 ∧ n = 0 := by
    intro m n hmn
    apply hind m n
    apply castHom_injective (by rw [hA, hB] : (shortW A B).toAffine =
      (shortW (Polynomial.C (a : ℚ)) (Polynomial.C (b : ℚ))).toAffine)
    rw [map_zsmul, map_zsmul, e1, e2, ← map_zsmul, ← map_zsmul, hmn]
  obtain ⟨kk, hk⟩ := QHeight.certG_exists a b hΔ _ _ _ _ h1 h2 hindQ
  refine ⟨kk, ?_⟩
  simp only [normPt, hx1, hx2, hy1, hy2, gx1, gx2, gy1, gy2, hk, Bool.and_self]

end Vals

namespace MTower

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

/-- **A code with a rational value has a rational fraction.** -/
lemma frval_of_rat (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) (b : LC 0) (hb : codeOKb b = true)
    (r : ℚ) (hr : T.val 0 b = (r : T.F 0)) :
    Fr.val (codeFr (yL c0) b) = algebraMap ℚ (RatFunc ℚ) r := by
  apply (ratMap (algebraMap ℚ Cc)).injective
  rw [show yL c0 = (CPoly.neg c0, [1]) from rfl, ← T.phi0_val c0 hFc b (codeOK_of hb), hr,
    map_ratCast]
  rw [eq_ratCast (algebraMap ℚ (RatFunc ℚ)), map_ratCast]

set_option maxHeartbeats 4000000 in
/-- **The structural part of the conjugation check passes on constant-curve data.** -/
theorem kxChkC0_true [Fact (Irreducible (CPoly.toPoly (fKc Fc)))] (c0 : CPoly ℚ)
    (hFc : Fc = [c0, [1]]) (h0 : T.Tr 0) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ)
    (cs : List (LC 0)) (z : LC 0) (κ : ℚ) (kc : ℕ) (mm : ℚ)
    (hA4 : ∀ i < 4, codeOKb (aC Fc ks A i) = true) (hBok : ∀ b ∈ B, codeOKb b = true)
    (hcs : ∀ q < cs.length, codeOKb (kqC Fc ks 0 cs q) = true)
    (hD : ∀ q < cs.length, codeOKb (kxD Fc ks 0 g cs q) = true) (hz : codeOKb z = true)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.val 0 (aC Fc ks A i) = (r i : T.F 0))
    (hBq : ∀ q < cs.length,
      (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 (kqC Fc ks 0 cs q)) ≠ 0)
    (hκ : κ ≠ 0) (hs : sT Fc ks g A B kt l cs kc ≠ 0)
    (hzκ : T.val 0 z ^ 2 * T.val 0 (aC Fc ks A 0) = (κ : T.F 0))
    (hmG : mG Fc ks g A B kt l cs kc ≠ 0) (hm : mm ≠ 0)
    (hdisc : 4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0) :
    kxChkC0 Fc ks c0 g A B kt l cs z κ (Fr.mul (mwU Fc ks c0 A) (Fr.ofPoly [mm]))
      [(polyOf (Fr.smulC (sT Fc ks g A B kt l cs kc ^ 2)
        (AFr Fc ks c0 A (Fr.mul (mwU Fc ks c0 A) (Fr.ofPoly [mm]))))).headD 0]
      [(polyOf (Fr.smulC (sT Fc ks g A B kt l cs kc ^ 3)
        (BFr Fc ks c0 A (Fr.mul (mwU Fc ks c0 A) (Fr.ofPoly [mm]))))).headD 0] kc = true := by
  set s := sT Fc ks g A B kt l cs kc with hsdef
  set uF := Fr.mul (mwU Fc ks c0 A) (Fr.ofPoly [mm]) with huF
  have hyok : Fr.ok (yL c0) := by simp [Fr.ok, CPoly.toPoly]
  have hcF : ∀ i < 4, IsConstFr (cF Fc ks c0 A i) (r i) := fun i hi ↦
    ⟨codeFr_ok _ hyok _ (codeOK_of (hA4 i hi)), T.frval_of_rat c0 hFc _ (hA4 i hi) (r i) (hr i hi)⟩
  obtain ⟨U, hU0, hU⟩ := mwU_const Fc ks c0 A r hcF
  have hu : IsConstFr uF (U * mm) := constFr_mul hU (constFr_ofPoly mm)
  have hAc := constFr_smulC (s ^ 2) (AFr_const Fc ks c0 A r hcF uF _ hu)
  have hBc := constFr_smulC (s ^ 3) (BFr_const Fc ks c0 A r hcF uF _ hu)
  have hAh := polyOf_head _ hAc.1 _ hAc.2
  have hBh := polyOf_head _ hBc.1 _ hBc.2
  -- the conjuncts
  have h1 : (List.range 4).all (fun i ↦ codeOKb (aC Fc ks A i)) = true :=
    List.all_eq_true.mpr fun i hi ↦ hA4 i (List.mem_range.mp hi)
  have h2 : B.all codeOKb = true := List.all_eq_true.mpr hBok
  have h3 : (List.range cs.length).all (fun q ↦ codeOKb (kqC Fc ks 0 cs q) &&
      codeOKb (kxD Fc ks 0 g cs q) && codeOKb (kxR Fc ks 0 A kt l cs q) &&
      !Fr.isZ (MTower.hornerFr (yL c0) (codeFr (yL c0) (kqC Fc ks 0 cs q)) B)) = true := by
    refine List.all_eq_true.mpr fun q hq ↦ ?_
    have hq' := List.mem_range.mp hq
    have kq := codeOK_of (hcs q hq')
    have oq := codeFr_ok _ hyok _ kq
    have hBc' : ∀ b ∈ B, codeOK b := fun b hb ↦ codeOK_of (hBok b hb)
    have oH := hornerFr_ok _ _ hyok oq B hBc'
    have hHs := T.hornerFr_spec c0 hFc h0 _ oq (T.val 0 (kqC Fc ks 0 cs q))
      (T.phi0_val c0 hFc _ kq) B hBc'
    have hH : Fr.isZ (MTower.hornerFr (yL c0) (codeFr (yL c0) (kqC Fc ks 0 cs q)) B) = false := by
      rw [Bool.eq_false_iff, Ne, Fr.isZ_iff oH]
      intro h0'
      apply hBq q hq'
      have := hHs; rw [h0', map_zero] at this
      exact (map_eq_zero_iff _ (T.phi0 c0 hFc).injective).mp this.symm
    simp only [hcs q hq', hD q hq', hH, Bool.true_and, Bool.not_false, Bool.and_true]
    exact codeOKb_normC Fc _
  have h5 : (!CPoly.isZero uF.2) = true := by
    have := hu.1; rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]; exact this
  have h6 : (!Fr.isZ uF) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, Fr.isZ_iff hu.1, hu.2]
    exact (map_ne_zero_iff _ (algebraMap ℚ (RatFunc ℚ)).injective).mpr (mul_ne_zero hU0 hm)
  have h7 : Fr.eqb (Fr.ofPoly [(polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF))).headD 0])
      (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF)) = true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) hAc.1, (constFr_ofPoly _).2, hAc.2, hAh]
  have h8 : Fr.eqb (Fr.ofPoly [(polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF))).headD 0])
      (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF)) = true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) hBc.1, (constFr_ofPoly _).2, hBc.2, hBh]
  have h9 : (!CPoly.isZero (discC [(polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF))).headD 0]
      [(polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF))).headD 0])) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff, hAh, hBh]
    simp only [discC, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, CPoly.toPoly,
      mul_zero, add_zero, ← C_mul, ← C_add]
    rw [C_eq_zero]
    have hU' : U * mm ≠ 0 := mul_ne_zero hU0 hm
    intro h0'
    apply hdisc
    have h1' : s ^ 6 * (U * mm) ^ 12 * (4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
        27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2) = 0 := by
      linear_combination h0'
    exact (mul_eq_zero.mp h1').resolve_left (mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hU'))
  have h12 : Fr.eqb (Fr.mul (Fr.mul (codeFr (yL c0) z) (codeFr (yL c0) z)) (cF Fc ks c0 A 0))
      (Fr.ofPoly [κ]) = true := by
    have oz := codeFr_ok _ hyok _ (codeOK_of hz)
    rw [Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul oz oz) (hcF 0 (by norm_num)).1) (Fr.ok_ofPoly _)]
    apply (ratMap (algebraMap ℚ Cc)).injective
    rw [Fr.val_mul (Fr.ok_mul oz oz) (hcF 0 (by norm_num)).1, Fr.val_mul oz oz, map_mul, map_mul,
      show cF Fc ks c0 A 0 = codeFr (CPoly.neg c0, [1]) (aC Fc ks A 0) from rfl,
      show yL c0 = (CPoly.neg c0, [1]) from rfl, ← T.phi0_val c0 hFc z (codeOK_of hz),
      ← T.phi0_val c0 hFc _ (codeOK_of (hA4 0 (by norm_num))), ← map_mul, ← map_mul, ← sq, hzκ,
      map_ratCast, (constFr_ofPoly κ).2, eq_ratCast (algebraMap ℚ (RatFunc ℚ)), map_ratCast]
  unfold kxChkC0
  simp only [← hsdef]
  simp only [h1, h2, h3, h5, h6, h7, h8, h9, h12, hz, Bool.true_and, Bool.and_true,
    bne_iff_ne, ne_eq, hκ, hs, hmG, not_false_eq_true, decide_true]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨⟨hκ, hs⟩, hmG⟩

set_option maxHeartbeats 4000000 in
/-- **The structural part of the twisted check passes on constant-curve data.** -/
theorem kxChkT0_true [Fact (Irreducible (CPoly.toPoly (fKc Fc)))] (c0 : CPoly ℚ)
    (hFc : Fc = [c0, [1]]) (h0 : T.Tr 0) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ)
    (cs : List (LC 0)) (z : LC 0) (c : ℚ) (kc : ℕ) (mm : ℚ)
    (hA4 : ∀ i < 4, codeOKb (aC Fc ks A i) = true) (hBok : ∀ b ∈ B, codeOKb b = true)
    (hcs : ∀ q < cs.length, codeOKb (kqC Fc ks 0 cs q) = true)
    (hD : ∀ q < cs.length, codeOKb (kxD Fc ks 0 g cs q) = true) (hz : codeOKb z = true)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.val 0 (aC Fc ks A i) = (r i : T.F 0))
    (hBq : ∀ q < cs.length,
      (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 (kqC Fc ks 0 cs q)) ≠ 0)
    (hκ : c ≠ 0) (hs : sT Fc ks g A B kt l cs kc ≠ 0)
    (hzκ : T.val 0 z ^ 2 * T.val 0 (aC Fc ks A 0) =
      ((sT Fc ks g A B kt l cs kc * c * c : ℚ) : T.F 0))
    (hmG : mG Fc ks g A B kt l cs kc ≠ 0) (hm : mm ≠ 0)
    (hdisc : 4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0) :
    kxChkT0 Fc ks c0 g A B kt l cs z c (Fr.mul (mwU Fc ks c0 A) (Fr.ofPoly [mm]))
      [(polyOf (Fr.smulC (sT Fc ks g A B kt l cs kc ^ 2)
        (AFr Fc ks c0 A (Fr.mul (mwU Fc ks c0 A) (Fr.ofPoly [mm]))))).headD 0]
      [(polyOf (Fr.smulC (sT Fc ks g A B kt l cs kc ^ 3)
        (BFr Fc ks c0 A (Fr.mul (mwU Fc ks c0 A) (Fr.ofPoly [mm]))))).headD 0] kc = true := by
  set s := sT Fc ks g A B kt l cs kc with hsdef
  set uF := Fr.mul (mwU Fc ks c0 A) (Fr.ofPoly [mm]) with huF
  have hyok : Fr.ok (yL c0) := by simp [Fr.ok, CPoly.toPoly]
  have hcF : ∀ i < 4, IsConstFr (cF Fc ks c0 A i) (r i) := fun i hi ↦
    ⟨codeFr_ok _ hyok _ (codeOK_of (hA4 i hi)), T.frval_of_rat c0 hFc _ (hA4 i hi) (r i) (hr i hi)⟩
  obtain ⟨U, hU0, hU⟩ := mwU_const Fc ks c0 A r hcF
  have hu : IsConstFr uF (U * mm) := constFr_mul hU (constFr_ofPoly mm)
  have hAc := constFr_smulC (s ^ 2) (AFr_const Fc ks c0 A r hcF uF _ hu)
  have hBc := constFr_smulC (s ^ 3) (BFr_const Fc ks c0 A r hcF uF _ hu)
  have hAh := polyOf_head _ hAc.1 _ hAc.2
  have hBh := polyOf_head _ hBc.1 _ hBc.2
  -- the conjuncts
  have h1 : (List.range 4).all (fun i ↦ codeOKb (aC Fc ks A i)) = true :=
    List.all_eq_true.mpr fun i hi ↦ hA4 i (List.mem_range.mp hi)
  have h2 : B.all codeOKb = true := List.all_eq_true.mpr hBok
  have h3 : (List.range cs.length).all (fun q ↦ codeOKb (kqC Fc ks 0 cs q) &&
      codeOKb (kxD Fc ks 0 g cs q) && codeOKb (kxR Fc ks 0 A kt l cs q) &&
      !Fr.isZ (MTower.hornerFr (yL c0) (codeFr (yL c0) (kqC Fc ks 0 cs q)) B)) = true := by
    refine List.all_eq_true.mpr fun q hq ↦ ?_
    have hq' := List.mem_range.mp hq
    have kq := codeOK_of (hcs q hq')
    have oq := codeFr_ok _ hyok _ kq
    have hBc' : ∀ b ∈ B, codeOK b := fun b hb ↦ codeOK_of (hBok b hb)
    have oH := hornerFr_ok _ _ hyok oq B hBc'
    have hHs := T.hornerFr_spec c0 hFc h0 _ oq (T.val 0 (kqC Fc ks 0 cs q))
      (T.phi0_val c0 hFc _ kq) B hBc'
    have hH : Fr.isZ (MTower.hornerFr (yL c0) (codeFr (yL c0) (kqC Fc ks 0 cs q)) B) = false := by
      rw [Bool.eq_false_iff, Ne, Fr.isZ_iff oH]
      intro h0'
      apply hBq q hq'
      have := hHs; rw [h0', map_zero] at this
      exact (map_eq_zero_iff _ (T.phi0 c0 hFc).injective).mp this.symm
    simp only [hcs q hq', hD q hq', hH, Bool.true_and, Bool.not_false, Bool.and_true]
    exact codeOKb_normC Fc _
  have h5 : (!CPoly.isZero uF.2) = true := by
    have := hu.1; rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]; exact this
  have h6 : (!Fr.isZ uF) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, Fr.isZ_iff hu.1, hu.2]
    exact (map_ne_zero_iff _ (algebraMap ℚ (RatFunc ℚ)).injective).mpr (mul_ne_zero hU0 hm)
  have h7 : Fr.eqb (Fr.ofPoly [(polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF))).headD 0])
      (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF)) = true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) hAc.1, (constFr_ofPoly _).2, hAc.2, hAh]
  have h8 : Fr.eqb (Fr.ofPoly [(polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF))).headD 0])
      (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF)) = true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) hBc.1, (constFr_ofPoly _).2, hBc.2, hBh]
  have h9 : (!CPoly.isZero (discC [(polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF))).headD 0]
      [(polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF))).headD 0])) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff, hAh, hBh]
    simp only [discC, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, CPoly.toPoly,
      mul_zero, add_zero, ← C_mul, ← C_add]
    rw [C_eq_zero]
    have hU' : U * mm ≠ 0 := mul_ne_zero hU0 hm
    intro h0'
    apply hdisc
    have h1' : s ^ 6 * (U * mm) ^ 12 * (4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
        27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2) = 0 := by
      linear_combination h0'
    exact (mul_eq_zero.mp h1').resolve_left (mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hU'))
  have h12 : Fr.eqb (Fr.mul (Fr.mul (codeFr (yL c0) z) (codeFr (yL c0) z)) (cF Fc ks c0 A 0))
      (Fr.ofPoly [s * c * c]) = true := by
    have oz := codeFr_ok _ hyok _ (codeOK_of hz)
    rw [Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul oz oz) (hcF 0 (by norm_num)).1) (Fr.ok_ofPoly _)]
    apply (ratMap (algebraMap ℚ Cc)).injective
    rw [Fr.val_mul (Fr.ok_mul oz oz) (hcF 0 (by norm_num)).1, Fr.val_mul oz oz, map_mul, map_mul,
      show cF Fc ks c0 A 0 = codeFr (CPoly.neg c0, [1]) (aC Fc ks A 0) from rfl,
      show yL c0 = (CPoly.neg c0, [1]) from rfl, ← T.phi0_val c0 hFc z (codeOK_of hz),
      ← T.phi0_val c0 hFc _ (codeOK_of (hA4 0 (by norm_num))), ← map_mul, ← map_mul, ← sq, hzκ,
      map_ratCast, (constFr_ofPoly (s * c * c)).2, eq_ratCast (algebraMap ℚ (RatFunc ℚ)), map_ratCast]
  unfold kxChkT0
  simp only [← hsdef]
  simp only [h1, h2, h3, h5, h6, h7, h8, h9, h12, hz, Bool.true_and, Bool.and_true,
    bne_iff_ne, ne_eq, hκ, hs, hmG, not_false_eq_true, decide_true]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨⟨hκ, hs⟩, hmG⟩

end MTower

end Curves.MT
