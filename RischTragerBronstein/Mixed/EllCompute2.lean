import RischTragerBronstein.Mixed.EllCompute

/-!
# Executable fractions over `K(X)` (step 4b, part 1)

`Fr K = CPoly K × CPoly K` with value `a / b` in `K(X)`; arithmetic with value lemmas
(`val_add`, `val_mul`, `val_neg`, `val_sub`, `val_div`) under non-zero denominators (`ok`), an
executable equality test (`eqb_iff`), and gcd normalization (`norm`).
-/

open Polynomial

namespace FFHeight

variable {K : Type*} [Field K] [DecidableEq K]

local notation "ι" => algebraMap K[X] (RatFunc K)

/-- Executable fractions. -/
abbrev Fr (K : Type*) := CPoly K × CPoly K

namespace Fr

/-- The value of a fraction. -/
noncomputable def val (f : Fr K) : RatFunc K := ι (CPoly.toPoly f.1) / ι (CPoly.toPoly f.2)

/-- Non-zero denominator. -/
def ok (f : Fr K) : Prop := CPoly.toPoly f.2 ≠ 0

def ofPoly (p : CPoly K) : Fr K := (p, [1])
def add (f g : Fr K) : Fr K := (CPoly.add (CPoly.mul f.1 g.2) (CPoly.mul g.1 f.2), CPoly.mul f.2 g.2)
def mul (f g : Fr K) : Fr K := (CPoly.mul f.1 g.1, CPoly.mul f.2 g.2)
def neg (f : Fr K) : Fr K := (CPoly.neg f.1, f.2)
def sub (f g : Fr K) : Fr K := add f (neg g)
def inv (f : Fr K) : Fr K := (f.2, f.1)
def div (f g : Fr K) : Fr K := mul f (inv g)
/-- Executable equality of values (for non-zero denominators). -/
def eqb (f g : Fr K) : Bool := CPoly.isZero (CPoly.sub (CPoly.mul f.1 g.2) (CPoly.mul g.1 f.2))
/-- Executable test `val f = 0`. -/
def isZ (f : Fr K) : Bool := CPoly.isZero f.1
/-- Normalize by the gcd. -/
def norm (f : Fr K) : Fr K := reduce f.1 f.2
def smulC (c : K) (f : Fr K) : Fr K := (CPoly.smul c f.1, f.2)

lemma hinj : Function.Injective (algebraMap K[X] (RatFunc K)) := IsFractionRing.injective K[X] (RatFunc K)

lemma ι_ne {p : K[X]} (hp : p ≠ 0) : ι p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp

lemma ok_ofPoly (p : CPoly K) : ok (ofPoly p) := by simp [ok, ofPoly, CPoly.toPoly]
lemma val_ofPoly (p : CPoly K) : val (ofPoly p) = ι (CPoly.toPoly p) := by
  simp [val, ofPoly, CPoly.toPoly]

lemma ok_add {f g : Fr K} (hf : ok f) (hg : ok g) : ok (add f g) := by
  simp only [ok, add, CPoly.toPoly_mul] at *; exact mul_ne_zero hf hg
lemma ok_mul {f g : Fr K} (hf : ok f) (hg : ok g) : ok (mul f g) := by
  simp only [ok, mul, CPoly.toPoly_mul] at *; exact mul_ne_zero hf hg
lemma ok_neg {f : Fr K} (hf : ok f) : ok (neg f) := hf
lemma ok_sub {f g : Fr K} (hf : ok f) (hg : ok g) : ok (sub f g) := ok_add hf (ok_neg hg)
lemma ok_smulC {f : Fr K} (c : K) (hf : ok f) : ok (smulC c f) := hf
lemma ok_norm {f : Fr K} (hf : ok f) : ok (norm f) := reduce_ne_zero f.1 f.2 hf

lemma val_add {f g : Fr K} (hf : ok f) (hg : ok g) : val (add f g) = val f + val g := by
  simp only [val, add, CPoly.toPoly_add, CPoly.toPoly_mul, map_add, map_mul]
  field_simp [ι_ne hf, ι_ne hg]
lemma val_mul {f g : Fr K} (hf : ok f) (hg : ok g) : val (mul f g) = val f * val g := by
  simp only [val, mul, CPoly.toPoly_mul, map_mul]
  field_simp [ι_ne hf, ι_ne hg]
lemma val_neg (f : Fr K) : val (neg f) = -val f := by
  simp only [val, neg, CPoly.toPoly_neg, map_neg, neg_div]
lemma val_sub {f g : Fr K} (hf : ok f) (hg : ok g) : val (sub f g) = val f - val g := by
  rw [sub, val_add hf (ok_neg hg), val_neg, sub_eq_add_neg]
lemma val_smulC (c : K) (f : Fr K) : val (smulC c f) = algebraMap K (RatFunc K) c * val f := by
  simp only [val, smulC, CPoly.toPoly_smul, map_mul, mul_div_assoc]
  rfl
lemma val_norm {f : Fr K} (hf : ok f) : val (norm f) = val f := reduce_div f.1 f.2 hf

lemma val_eq_zero_iff {f : Fr K} (hf : ok f) : val f = 0 ↔ CPoly.toPoly f.1 = 0 := by
  rw [val, div_eq_zero_iff, map_eq_zero_iff _ hinj, map_eq_zero_iff _ hinj]
  exact ⟨fun h ↦ h.resolve_right hf, Or.inl⟩

lemma isZ_iff {f : Fr K} (hf : ok f) : isZ f = true ↔ val f = 0 := by
  rw [isZ, CPoly.isZero_iff, val_eq_zero_iff hf]

lemma ok_inv {f : Fr K} (h0 : val f ≠ 0) : ok (inv f) := by
  intro h; apply h0; simp only [inv] at h; rw [val, h]; simp

lemma val_inv {f : Fr K} (hf : ok f) (h0 : val f ≠ 0) : val (inv f) = (val f)⁻¹ := by
  simp [val, inv, inv_div]

lemma ok_div {f g : Fr K} (hf : ok f) (hg0 : val g ≠ 0) : ok (div f g) := ok_mul hf (ok_inv hg0)

lemma val_div {f g : Fr K} (hf : ok f) (hg : ok g) (hg0 : val g ≠ 0) :
    val (div f g) = val f / val g := by
  rw [div, val_mul hf (ok_inv hg0), val_inv hg hg0, div_eq_mul_inv]

lemma eqb_iff {f g : Fr K} (hf : ok f) (hg : ok g) : eqb f g = true ↔ val f = val g := by
  rw [eqb, CPoly.isZero_iff, CPoly.toPoly_sub, CPoly.toPoly_mul, CPoly.toPoly_mul, sub_eq_zero, val,
    val, div_eq_div_iff (ι_ne hf) (ι_ne hg), ← map_mul, ← map_mul]
  exact ⟨fun h ↦ by rw [h], fun h ↦ hinj (by rw [map_mul, map_mul] at h ⊢; exact h)⟩

end Fr

section Points

open WeierstrassCurve WeierstrassCurve.Affine Fr

open scoped Classical

variable [CharZero K]

/-- Executable points: `none` is the origin. -/
abbrev PtC (K : Type*) := Option (Fr K × Fr K)

/-- `o` represents the point `P` of `y² = x³ + A x + B`. -/
def Rel (A B : K[X]) : PtC K → (shortW A B).toAffine.Point → Prop
  | none, .zero => True
  | some (fx, fy), .some x y _ => ok fx ∧ ok fy ∧ val fx = x ∧ val fy = y
  | _, _ => False

/-- **Executable addition** on `y² = x³ + A x + B` (`A` given as a `CPoly`). -/
def addC (Ac : CPoly K) : PtC K → PtC K → PtC K
  | none, q => q
  | some p, none => some p
  | some (x1, y1), some (x2, y2) =>
    if eqb x1 x2 && eqb y1 (neg y2) then none else
    let ℓ := if eqb x1 x2 then div (add (smulC 3 (mul x1 x1)) (ofPoly Ac)) (smulC 2 y1)
      else div (sub y1 y2) (sub x1 x2)
    let x3 := sub (sub (mul ℓ ℓ) x1) x2
    let y3 := neg (add (mul ℓ (sub x3 x1)) y1)
    some (norm x3, norm y3)

lemma negY_shortW (A B : K[X]) (x y : RatFunc K) : (shortW A B).toAffine.negY x y = -y := by
  simp [negY, shortW]

/-- **Correctness of the executable addition.** -/
theorem addC_spec (Ac : CPoly K) (A B : K[X]) (hA : CPoly.toPoly Ac = A)
    (o1 o2 : PtC K) (P Q : (shortW A B).toAffine.Point) (h1 : Rel A B o1 P) (h2 : Rel A B o2 Q) :
    Rel A B (addC Ac o1 o2) (P + Q) := by
  rcases o1 with _ | ⟨fx1, fy1⟩ <;> rcases P with _ | ⟨x1, y1, hP⟩ <;> simp only [Rel] at h1
  · have e : (Point.zero : (shortW A B).toAffine.Point) + Q = Q := zero_add Q
    rw [e]; exact h2
  rcases o2 with _ | ⟨fx2, fy2⟩ <;> rcases Q with _ | ⟨x2, y2, hQ⟩ <;> simp only [Rel] at h2
  · have e : Point.some x1 y1 hP + (Point.zero : (shortW A B).toAffine.Point) = Point.some x1 y1 hP :=
      add_zero _
    rw [e]; exact h1
  obtain ⟨ox1, oy1, vx1, vy1⟩ := h1
  obtain ⟨ox2, oy2, vx2, vy2⟩ := h2
  have hcx : eqb fx1 fx2 = true ↔ x1 = x2 := by rw [eqb_iff ox1 ox2, vx1, vx2]
  have hcy : eqb fy1 (neg fy2) = true ↔ y1 = (shortW A B).toAffine.negY x2 y2 := by
    rw [eqb_iff oy1 (ok_neg oy2), val_neg, vy1, vy2, negY_shortW]
  simp only [addC]
  by_cases hxy : x1 = x2 ∧ y1 = (shortW A B).toAffine.negY x2 y2
  · have hb : (eqb fx1 fx2 && eqb fy1 (neg fy2)) = true := by
      rw [Bool.and_eq_true, hcx, hcy]; exact hxy
    rw [if_pos hb, Point.add_of_Y_eq hxy.1 hxy.2]; trivial
  · have hb : ¬ (eqb fx1 fx2 && eqb fy1 (neg fy2)) = true := by
      rw [Bool.and_eq_true, hcx, hcy]; exact hxy
    rw [if_neg hb, Point.add_some hxy]
    -- the slope
    have hslope : ∃ fl : Fr K, ok fl ∧ val fl = (shortW A B).toAffine.slope x1 x2 y1 y2 ∧
        fl = (if eqb fx1 fx2 then div (add (smulC 3 (mul fx1 fx1)) (ofPoly Ac)) (smulC 2 fy1)
          else div (sub fy1 fy2) (sub fx1 fx2)) := by
      by_cases hx : x1 = x2
      · have hy : y1 ≠ (shortW A B).toAffine.negY x2 y2 := fun h ↦ hxy ⟨hx, h⟩
        have hy12 : y1 = y2 := Y_eq_of_Y_ne hP.1 hQ.1 hx hy
        have h2y : val (smulC 2 fy1) ≠ 0 := by
          rw [val_smulC, vy1]
          intro h0
          apply hy
          rw [negY_shortW, ← hy12]
          have : (2 : RatFunc K) * y1 = 0 := by simpa using h0
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h two_ne_zero
          · rw [h, neg_zero]
        refine ⟨_, ok_div (ok_add (ok_smulC 3 (ok_mul ox1 ox1)) (ok_ofPoly Ac)) h2y, ?_,
          by rw [if_pos (hcx.mpr hx)]⟩
        rw [val_div (ok_add (ok_smulC 3 (ok_mul ox1 ox1)) (ok_ofPoly Ac)) (ok_smulC 2 oy1) h2y,
          val_add (ok_smulC 3 (ok_mul ox1 ox1)) (ok_ofPoly Ac), val_smulC, val_mul ox1 ox1,
          val_ofPoly, val_smulC, vx1, vy1, hA, slope_of_Y_ne hx hy, negY_shortW]
        simp only [shortW, map_ofNat]
        congr 1 <;> ring
      · have hd : val (sub fx1 fx2) ≠ 0 := by
          rw [val_sub ox1 ox2, vx1, vx2]; exact sub_ne_zero.mpr hx
        refine ⟨_, ok_div (ok_sub oy1 oy2) hd, ?_, by rw [if_neg (fun h ↦ hx (hcx.mp h))]⟩
        rw [val_div (ok_sub oy1 oy2) (ok_sub ox1 ox2) hd, val_sub oy1 oy2, val_sub ox1 ox2, vx1, vx2,
          vy1, vy2, slope_of_X_ne hx]
    obtain ⟨fl, ol, vl, hfl⟩ := hslope
    rw [← hfl]
    set ℓ := (shortW A B).toAffine.slope x1 x2 y1 y2
    have ox3 : ok (sub (sub (mul fl fl) fx1) fx2) := ok_sub (ok_sub (ok_mul ol ol) ox1) ox2
    have vx3 : val (sub (sub (mul fl fl) fx1) fx2) = (shortW A B).toAffine.addX x1 x2 ℓ := by
      rw [val_sub (ok_sub (ok_mul ol ol) ox1) ox2, val_sub (ok_mul ol ol) ox1, val_mul ol ol, vl, vx1,
        vx2]
      simp [addX, shortW]; ring
    refine ⟨ok_norm ox3, ok_norm (ok_neg (ok_add (ok_mul ol (ok_sub ox3 ox1)) oy1)), ?_, ?_⟩
    · rw [val_norm ox3, vx3]
    · rw [val_norm (ok_neg (ok_add (ok_mul ol (ok_sub ox3 ox1)) oy1)), val_neg,
        val_add (ok_mul ol (ok_sub ox3 ox1)) oy1, val_mul ol (ok_sub ox3 ox1), val_sub ox3 ox1, vx3,
        vl, vx1, vy1]
      simp [ℓ, addY, negAddY, negY, shortW]

end Points

section Cert

open WeierstrassCurve WeierstrassCurve.Affine Fr

open scoped Classical

variable [CharZero K]

/-- The executable height of a point. -/
def htC : PtC K → ℕ
  | none => 0
  | some (fx, _) => htPair fx.1 fx.2

lemma htC_spec (A B : K[X]) (o : PtC K) (P : (shortW A B).toAffine.Point) (h : Rel A B o P) :
    htC o = hN A B P := by
  rcases o with _ | ⟨fx, fy⟩ <;> rcases P with _ | ⟨x, y, hP⟩ <;> simp only [Rel] at h
  · rfl
  · obtain ⟨ox, -, vx, -⟩ := h
    simp only [htC, hN]
    rw [htPair_spec _ _ ox]
    rw [← vx]; rfl

/-- Iterated executable doubling. -/
def dblC (Ac : CPoly K) (k : ℕ) (o : PtC K) : PtC K := (fun o ↦ addC Ac o o)^[k] o

lemma dblC_spec (Ac : CPoly K) (A B : K[X]) (hA : CPoly.toPoly Ac = A) (k : ℕ) (o : PtC K)
    (P : (shortW A B).toAffine.Point) (h : Rel A B o P) :
    Rel A B (dblC Ac k o) (MWPair.dbl^[k] P) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [dblC, Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact addC_spec Ac A B hA _ _ _ _ ih ih

/-- **The executable certificate check** (rational arithmetic): `D = max (deg A) (deg B)`. -/
def certQ (Ac : CPoly K) (D : ℕ) (k : ℕ) (oP oQ : PtC K) : Bool :=
  let Cc : ℚ := 11 * D
  let hP : ℚ := htC (dblC Ac k oP)
  let hQ : ℚ := htC (dblC Ac k oQ)
  let hPQ : ℚ := htC (dblC Ac k (addC Ac oP oQ))
  let e : ℚ := Cc / 3 / 4 ^ k
  decide (e * (|hP / 4 ^ k| + |hQ / 4 ^ k| + e) +
      3 * e / 2 * (|hPQ / 4 ^ k - hP / 4 ^ k - hQ / 4 ^ k| + 3 * e / 2) <
    |hP / 4 ^ k * (hQ / 4 ^ k) - ((hPQ / 4 ^ k - hP / 4 ^ k - hQ / 4 ^ k) / 2) ^ 2|)

/-- **A passing executable check proves independence.** -/
theorem indep_of_certQ (Ac Bc : CPoly K) (A B : K[X]) (hA : CPoly.toPoly Ac = A)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (k : ℕ) (oP oQ : PtC K)
    (P Q : (shortW A B).toAffine.Point) (hP : Rel A B oP P) (hQ : Rel A B oQ Q)
    (hc : certQ Ac (max A.natDegree B.natDegree) k oP oQ = true)
    (m n : ℤ) (hrel : m • P = n • Q) : m = 0 ∧ n = 0 := by
  refine ell_indep A B hΔ P Q k ?_ m n hrel
  have e1 := htC_spec A B _ _ (dblC_spec Ac A B hA k oP P hP)
  have e2 := htC_spec A B _ _ (dblC_spec Ac A B hA k oQ Q hQ)
  have e3 := htC_spec A B _ _ (dblC_spec Ac A B hA k _ _ (addC_spec Ac A B hA oP oQ P Q hP hQ))
  simp only [certQ, decide_eq_true_eq] at hc
  simp only [hR]
  rw [← e1, ← e2, ← e3]
  have hc' := (Rat.cast_lt (K := ℝ)).mpr hc
  push_cast [Rat.cast_abs] at hc' ⊢
  exact hc'

end Cert

section Mult

open WeierstrassCurve WeierstrassCurve.Affine Fr

open scoped Classical

variable [CharZero K]

/-- Executable negation `(x, y) ↦ (x, −y)`. -/
def negC : PtC K → PtC K
  | none => none
  | some (fx, fy) => some (fx, neg fy)

lemma negC_spec (A B : K[X]) (o : PtC K) (P : (shortW A B).toAffine.Point) (h : Rel A B o P) :
    Rel A B (negC o) (-P) := by
  rcases o with _ | ⟨fx, fy⟩ <;> rcases P with _ | ⟨x, y, hP⟩ <;> simp only [Rel] at h
  · trivial
  · obtain ⟨ox, oy, vx, vy⟩ := h
    refine ⟨ox, ok_neg oy, vx, ?_⟩
    rw [val_neg, vy, negY_shortW]

/-- Executable natural multiples. -/
def nsmulC (Ac : CPoly K) : ℕ → PtC K → PtC K
  | 0, _ => none
  | n + 1, o => addC Ac o (nsmulC Ac n o)

lemma nsmulC_spec (Ac : CPoly K) (A B : K[X]) (hA : CPoly.toPoly Ac = A) (o : PtC K)
    (P : (shortW A B).toAffine.Point) (h : Rel A B o P) :
    ∀ n : ℕ, Rel A B (nsmulC Ac n o) (n • P)
  | 0 => by simp only [nsmulC, zero_smul]; trivial
  | n + 1 => by
    rw [nsmulC, succ_nsmul']
    exact addC_spec Ac A B hA _ _ _ _ h (nsmulC_spec Ac A B hA o P h n)

/-- Executable integer multiples. -/
def zsmulC (Ac : CPoly K) (n : ℤ) (o : PtC K) : PtC K :=
  if 0 ≤ n then nsmulC Ac n.toNat o else negC (nsmulC Ac n.natAbs o)

lemma zsmulC_spec (Ac : CPoly K) (A B : K[X]) (hA : CPoly.toPoly Ac = A) (n : ℤ) (o : PtC K)
    (P : (shortW A B).toAffine.Point) (h : Rel A B o P) : Rel A B (zsmulC Ac n o) (n • P) := by
  unfold zsmulC
  split_ifs with hn
  · have : n • P = n.toNat • P := by
      rw [← natCast_zsmul, Int.toNat_of_nonneg hn]
    rw [this]; exact nsmulC_spec Ac A B hA o P h _
  · have : n • P = -(n.natAbs • P) := by
      rw [← natCast_zsmul, ← neg_zsmul]; congr 1; omega
    rw [this]; exact negC_spec A B _ _ (nsmulC_spec Ac A B hA o P h _)

/-- Executable sums `∑ nᵢ Pᵢ`. -/
def sumC (Ac : CPoly K) : List (ℤ × PtC K) → PtC K
  | [] => none
  | e :: l => addC Ac (zsmulC Ac e.1 e.2) (sumC Ac l)

end Mult

end FFHeight
