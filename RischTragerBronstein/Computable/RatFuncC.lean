import RischTragerBronstein.Computable.EuclidDegree

/-!
# Computable rational function fields `K(t)`

For a computable field `K` (`[Field K] [DecidableEq K]`, characteristic zero), `RatFuncC K` is the
quotient of the pairs `(p, q)` of coefficient lists with `q ≠ 0` by `p/q = p'/q'`. The operations
are computable (and reduce fractions by the `gcd`), equality is decided by cross-multiplication,
and the field structure is transported from Mathlib's `RatFunc K` along the injective map `toRF`
(`Function.Injective.field`), with computable data.

`evalHom φ z`: the evaluation `t ↦ z` into a field `E` through `φ : K →+* E`, for `z` transcendental
over the image of `φ`; it is an injective ring homomorphism.
-/

open Polynomial CPoly

set_option linter.unusedSectionVars false

namespace RFC

variable (K : Type*) [Field K] [DecidableEq K] [CharZero K]

/-- Pairs `(p, q)` with `q ≠ 0`. -/
abbrev Pr : Type _ := {pq : CPoly K × CPoly K // isZero pq.2 = false}

variable {K}

lemma den_ne_zero (x : Pr K) : toPoly x.1.2 ≠ 0 := fun h ↦ by
  have := x.2
  rw [(isZero_iff _).mpr h] at this
  exact Bool.noConfusion this

/-- The value of a pair. -/
noncomputable def val (x : Pr K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (toPoly x.1.1) / algebraMap K[X] (RatFunc K) (toPoly x.1.2)

lemma algebraMap_ne_zero {p : K[X]} (hp : p ≠ 0) : algebraMap K[X] (RatFunc K) p ≠ 0 :=
  fun h ↦ hp ((map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h)

lemma val_eq_iff (x y : Pr K) : val x = val y ↔
    toPoly x.1.1 * toPoly y.1.2 = toPoly y.1.1 * toPoly x.1.2 := by
  have hx := algebraMap_ne_zero (den_ne_zero x)
  have hy := algebraMap_ne_zero (den_ne_zero y)
  rw [val, val, div_eq_div_iff hx hy, ← map_mul, ← map_mul]
  exact (IsFractionRing.injective K[X] (RatFunc K)).eq_iff

instance setoid : Setoid (Pr K) where
  r x y := val x = val y
  iseqv := ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h h' ↦ h.trans h'⟩

lemma rel_iff_isZero (x y : Pr K) : val x = val y ↔
    isZero (sub (mul x.1.1 y.1.2) (mul y.1.1 x.1.2)) = true := by
  rw [val_eq_iff, isZero_iff, toPoly_sub, toPoly_mul, toPoly_mul, sub_eq_zero]

instance decRel : DecidableRel (fun x y : Pr K ↦ val x = val y) := fun x y ↦
  decidable_of_iff _ (rel_iff_isZero x y).symm

variable (K) in
/-- **The rational function field `K(t)`**, computably. -/
def RatFuncC : Type _ := Quotient (setoid (K := K))

instance : DecidableEq (RatFuncC K) := fun a b ↦
  Quotient.recOnSubsingleton₂ a b fun x y ↦
    decidable_of_iff (val x = val y) ⟨fun h ↦ Quotient.sound h, fun h ↦ Quotient.exact h⟩

instance [Countable K] : Countable (RatFuncC K) := by
  unfold RatFuncC; infer_instance

/-! ### Normalization -/

/-- Exact division by `g` (when `g ∣ p`). -/
lemma divMod_exact {p g : CPoly K} (hg : toPoly g ≠ 0) (hd : toPoly g ∣ toPoly p) :
    toPoly (divMod p g).1 * toPoly g = toPoly p := by
  have hs := divMod_spec p g
  have hr : toPoly (divMod p g).2 = 0 := by
    have h1 : toPoly g ∣ toPoly (divMod p g).2 := by
      have : toPoly (divMod p g).2 = toPoly p - toPoly (divMod p g).1 * toPoly g := by
        rw [hs]; ring
      rw [this]
      exact dvd_sub hd (dvd_mul_left _ _)
    exact eq_zero_of_dvd_of_degree_lt h1 (divMod_degree_lt p g hg)
  rw [hr, add_zero] at hs
  exact hs.symm

/-- Reduce by the `gcd` and make the denominator monic. -/
def normPair (p q : CPoly K) : CPoly K × CPoly K :=
  let g := trim (egcd p q).1
  if isZero g then (p, q) else
    let p' := (divMod p g).1
    let q' := (divMod q g).1
    let c := lead (trim q')
    if c = 0 then (p, q) else (smul c⁻¹ p', smul c⁻¹ q')

lemma normPair_spec (p q : CPoly K) (hq : toPoly q ≠ 0) :
    toPoly (normPair p q).2 ≠ 0 ∧
      toPoly (normPair p q).1 * toPoly q = toPoly p * toPoly (normPair p q).2 := by
  unfold normPair
  simp only
  split_ifs with hg hc
  · exact ⟨hq, rfl⟩
  · exact ⟨hq, rfl⟩
  · have hg0 : toPoly (trim (egcd p q).1) ≠ 0 := fun h ↦ hg ((isZero_iff _).mpr h)
    rw [toPoly_trim] at hg0
    obtain ⟨hdp, hdq⟩ := egcd_dvd p q
    have hdp' : toPoly (trim (egcd p q).1) ∣ toPoly p := by rw [toPoly_trim]; exact hdp
    have hdq' : toPoly (trim (egcd p q).1) ∣ toPoly q := by rw [toPoly_trim]; exact hdq
    have hg0' : toPoly (trim (egcd p q).1) ≠ 0 := by rwa [toPoly_trim]
    have ep := divMod_exact (p := p) hg0' hdp'
    have eq := divMod_exact (p := q) hg0' hdq'
    simp only [toPoly_smul]
    have hc0 : (lead (trim (divMod q (trim (egcd p q).1)).1))⁻¹ ≠ 0 := inv_ne_zero hc
    refine ⟨fun h ↦ ?_, ?_⟩
    · rcases mul_eq_zero.mp h with h1 | h1
      · exact hc0 (C_eq_zero.mp h1)
      · exact hq (by rw [← eq, h1, zero_mul])
    · rw [← ep, ← eq]; ring

/-- A pair from lists (normalized); `q = 0` gives `0`. -/
def mkPr (p q : CPoly K) : Pr K :=
  if h : isZero q = false then
    ⟨normPair p q, by
      have hq : toPoly q ≠ 0 := fun h0 ↦ by rw [(isZero_iff _).mpr h0] at h; exact Bool.noConfusion h
      have := (normPair_spec p q hq).1
      cases h' : isZero (normPair p q).2
      · rfl
      · exact absurd ((isZero_iff _).mp h') this⟩
  else ⟨([], [1]), by simp [isZero]⟩

lemma val_mkPr (p q : CPoly K) (hq : toPoly q ≠ 0) :
    val (mkPr p q) = algebraMap K[X] (RatFunc K) (toPoly p) / algebraMap K[X] (RatFunc K) (toPoly q) := by
  have h : isZero q = false := by
    cases h' : isZero q
    · rfl
    · exact absurd ((isZero_iff _).mp h') hq
  rw [mkPr, dif_pos h, val]
  obtain ⟨h2, h3⟩ := normPair_spec p q hq
  rw [div_eq_div_iff (algebraMap_ne_zero h2) (algebraMap_ne_zero hq), ← map_mul, ← map_mul, h3]

lemma val_mkPr_zero (p q : CPoly K) (hq : toPoly q = 0) : val (mkPr p q) = 0 := by
  have h : ¬ isZero q = false := by rw [(isZero_iff _).mpr hq]; exact Bool.noConfusion
  rw [mkPr, dif_neg h, val]
  simp

/-- The general formula (with `a / 0 = 0`). -/
lemma val_mkPr' (p q : CPoly K) :
    val (mkPr p q) = algebraMap K[X] (RatFunc K) (toPoly p) / algebraMap K[X] (RatFunc K) (toPoly q) := by
  by_cases hq : toPoly q = 0
  · rw [val_mkPr_zero p q hq, hq, map_zero, div_zero]
  · exact val_mkPr p q hq

/-- The element `p / q`. -/
def mk (p q : CPoly K) : RatFuncC K := Quotient.mk _ (mkPr p q)

/-! ### The comparison map -/

/-- The value in `RatFunc K`. -/
noncomputable def toRF : RatFuncC K → RatFunc K := Quotient.lift val fun _ _ h ↦ h

lemma toRF_mk (p q : CPoly K) :
    toRF (mk p q) = algebraMap K[X] (RatFunc K) (toPoly p) / algebraMap K[X] (RatFunc K) (toPoly q) :=
  val_mkPr' p q

lemma toRF_injective : Function.Injective (toRF (K := K)) := by
  intro a b h
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  exact Quotient.sound h

lemma exists_mk (a : RatFuncC K) : ∃ x : Pr K, a = Quotient.mk _ x ∧ toRF a = val x := by
  induction a using Quotient.inductionOn with
  | h x => exact ⟨x, rfl, rfl⟩

/-! ### Operations -/

/-- Lift a binary operation on representatives. -/
def lift₂ (f : Pr K → Pr K → RatFuncC K) (hf : ∀ a b a' b', val a = val a' → val b = val b' →
    f a b = f a' b') : RatFuncC K → RatFuncC K → RatFuncC K :=
  Quotient.lift₂ f fun _ _ _ _ h h' ↦ hf _ _ _ _ h h'

/-- Lift a unary operation on representatives. -/
def lift₁ (f : Pr K → RatFuncC K) (hf : ∀ a a', val a = val a' → f a = f a') :
    RatFuncC K → RatFuncC K :=
  Quotient.lift f fun _ _ h ↦ hf _ _ h

lemma val_eq_div (x : Pr K) : val x =
    algebraMap K[X] (RatFunc K) (toPoly x.1.1) / algebraMap K[X] (RatFunc K) (toPoly x.1.2) := rfl

/-- Addition of representatives. -/
def addP (a b : Pr K) : RatFuncC K := mk (add (mul a.1.1 b.1.2) (mul b.1.1 a.1.2)) (mul a.1.2 b.1.2)

lemma toRF_addP (a b : Pr K) : toRF (addP a b) = val a + val b := by
  rw [addP, toRF_mk, val_eq_div a, val_eq_div b,
    div_add_div _ _ (algebraMap_ne_zero (den_ne_zero a)) (algebraMap_ne_zero (den_ne_zero b))]
  simp only [toPoly_add, toPoly_mul, map_add, map_mul]
  ring

/-- Multiplication of representatives. -/
def mulP (a b : Pr K) : RatFuncC K := mk (mul a.1.1 b.1.1) (mul a.1.2 b.1.2)

lemma toRF_mulP (a b : Pr K) : toRF (mulP a b) = val a * val b := by
  rw [mulP, toRF_mk, val_eq_div a, val_eq_div b, div_mul_div_comm]
  simp only [toPoly_mul, map_mul]

/-- Negation of representatives. -/
def negP (a : Pr K) : RatFuncC K := mk (smul (-1) a.1.1) a.1.2

lemma toRF_negP (a : Pr K) : toRF (negP a) = -val a := by
  rw [negP, toRF_mk, val_eq_div a, toPoly_smul, map_mul]
  simp [neg_div]

/-- Inversion of representatives. -/
def invP (a : Pr K) : RatFuncC K := if isZero a.1.1 then mk [] [1] else mk a.1.2 a.1.1

lemma toRF_invP (a : Pr K) : toRF (invP a) = (val a)⁻¹ := by
  rw [invP]
  split_ifs with h
  · rw [toRF_mk, val_eq_div a, (isZero_iff _).mp h]
    simp
  · rw [toRF_mk, val_eq_div a, inv_div]

/-- Scalar multiplication of representatives. -/
def smulP (c : K) (a : Pr K) : RatFuncC K := mk (smul c a.1.1) a.1.2

lemma toRF_smulP (c : K) (a : Pr K) : toRF (smulP c a) = algebraMap K (RatFunc K) c * val a := by
  rw [smulP, toRF_mk, val_eq_div a, toPoly_smul, map_mul, mul_div_assoc]
  rfl

instance : Zero (RatFuncC K) := ⟨mk [] [1]⟩
instance : One (RatFuncC K) := ⟨mk [1] [1]⟩
instance : Add (RatFuncC K) :=
  ⟨lift₂ addP fun a b a' b' h h' ↦ toRF_injective (by rw [toRF_addP, toRF_addP, h, h'])⟩
instance : Mul (RatFuncC K) :=
  ⟨lift₂ mulP fun a b a' b' h h' ↦ toRF_injective (by rw [toRF_mulP, toRF_mulP, h, h'])⟩
instance : Neg (RatFuncC K) :=
  ⟨lift₁ negP fun a a' h ↦ toRF_injective (by rw [toRF_negP, toRF_negP, h])⟩
instance : Sub (RatFuncC K) := ⟨fun a b ↦ a + -b⟩
instance : Inv (RatFuncC K) :=
  ⟨lift₁ invP fun a a' h ↦ toRF_injective (by rw [toRF_invP, toRF_invP, h])⟩
instance : Div (RatFuncC K) := ⟨fun a b ↦ a * b⁻¹⟩

/-- Scalar multiplication by `K`. -/
def smulK (c : K) : RatFuncC K → RatFuncC K :=
  lift₁ (smulP c) fun a a' h ↦ toRF_injective (by rw [toRF_smulP, toRF_smulP, h])

instance : SMul ℕ (RatFuncC K) := ⟨fun n x ↦ smulK (n : K) x⟩
instance : SMul ℤ (RatFuncC K) := ⟨fun n x ↦ smulK (n : K) x⟩
instance : SMul ℚ≥0 (RatFuncC K) := ⟨fun q x ↦ smulK (q : K) x⟩
instance : SMul ℚ (RatFuncC K) := ⟨fun q x ↦ smulK (q : K) x⟩
instance : Pow (RatFuncC K) ℕ := ⟨fun x n ↦ npowRec n x⟩
instance : Pow (RatFuncC K) ℤ := ⟨fun x n ↦ zpowRec npowRec n x⟩
instance : NatCast (RatFuncC K) := ⟨fun n ↦ mk [(n : K)] [1]⟩
instance : IntCast (RatFuncC K) := ⟨fun n ↦ mk [(n : K)] [1]⟩
instance : NNRatCast (RatFuncC K) := ⟨fun q ↦ mk [((q : ℚ≥0) : K)] [1]⟩
instance : RatCast (RatFuncC K) := ⟨fun q ↦ mk [(q : K)] [1]⟩

lemma toRF_const (c : K) : toRF (mk [c] [1] : RatFuncC K) = algebraMap K (RatFunc K) c := by
  rw [toRF_mk]
  simp [CPoly.toPoly, RatFunc.algebraMap_C]

lemma toRF_zero : toRF (0 : RatFuncC K) = 0 := by
  show toRF (mk [] [1]) = 0; rw [toRF_mk]; simp [CPoly.toPoly]

lemma toRF_one : toRF (1 : RatFuncC K) = 1 := by
  show toRF (mk [1] [1]) = 1; rw [toRF_const, map_one]

lemma toRF_add (x y : RatFuncC K) : toRF (x + y) = toRF x + toRF y := by
  obtain ⟨a, rfl, ha⟩ := exists_mk x
  obtain ⟨b, rfl, hb⟩ := exists_mk y
  rw [ha, hb]
  exact toRF_addP a b

lemma toRF_mul (x y : RatFuncC K) : toRF (x * y) = toRF x * toRF y := by
  obtain ⟨a, rfl, ha⟩ := exists_mk x
  obtain ⟨b, rfl, hb⟩ := exists_mk y
  rw [ha, hb]
  exact toRF_mulP a b

lemma toRF_neg (x : RatFuncC K) : toRF (-x) = -toRF x := by
  obtain ⟨a, rfl, ha⟩ := exists_mk x
  rw [ha]
  exact toRF_negP a

lemma toRF_sub (x y : RatFuncC K) : toRF (x - y) = toRF x - toRF y := by
  show toRF (x + -y) = _
  rw [toRF_add, toRF_neg, sub_eq_add_neg]

lemma toRF_inv (x : RatFuncC K) : toRF x⁻¹ = (toRF x)⁻¹ := by
  obtain ⟨a, rfl, ha⟩ := exists_mk x
  rw [ha]
  exact toRF_invP a

lemma toRF_div (x y : RatFuncC K) : toRF (x / y) = toRF x / toRF y := by
  show toRF (x * y⁻¹) = _
  rw [toRF_mul, toRF_inv, div_eq_mul_inv]

lemma toRF_smulK (c : K) (x : RatFuncC K) : toRF (smulK c x) = algebraMap K (RatFunc K) c * toRF x := by
  obtain ⟨a, rfl, ha⟩ := exists_mk x
  rw [ha]
  exact toRF_smulP c a

lemma toRF_nsmul (n : ℕ) (x : RatFuncC K) : toRF (n • x) = n • toRF x := by
  show toRF (smulK _ x) = _; rw [toRF_smulK, nsmul_eq_mul, map_natCast]

lemma toRF_zsmul (n : ℤ) (x : RatFuncC K) : toRF (n • x) = n • toRF x := by
  show toRF (smulK _ x) = _; rw [toRF_smulK, zsmul_eq_mul, map_intCast]

lemma toRF_nnqsmul (q : ℚ≥0) (x : RatFuncC K) : toRF (q • x) =
    @HSMul.hSMul ℚ≥0 _ _ (@instHSMul _ _ NNRat.smulDivisionSemiring) q (toRF x) := by
  show toRF (smulK _ x) = _; rw [toRF_smulK, map_nnratCast]; exact (NNRat.smul_def q _).symm

lemma toRF_qsmul (q : ℚ) (x : RatFuncC K) : toRF (q • x) =
    @HSMul.hSMul ℚ _ _ (@instHSMul _ _ Rat.smulDivisionRing) q (toRF x) := by
  show toRF (smulK _ x) = _; rw [toRF_smulK, map_ratCast]; exact (Rat.smul_def q _).symm

lemma toRF_npow (x : RatFuncC K) (n : ℕ) : toRF (x ^ n) = toRF x ^ n := by
  show toRF (npowRec n x) = _
  induction n with
  | zero => simp [npowRec, toRF_one]
  | succ n ih => rw [npowRec, toRF_mul, ih, pow_succ]

lemma toRF_zpow (x : RatFuncC K) (n : ℤ) : toRF (x ^ n) = toRF x ^ n := by
  show toRF (zpowRec npowRec n x) = _
  rcases n with n | n
  · simp only [zpowRec, Int.ofNat_eq_natCast, zpow_natCast]
    exact toRF_npow x n
  · simp only [zpowRec, zpow_negSucc]
    rw [toRF_inv]
    exact congrArg _ (toRF_npow x (n + 1))

lemma toRF_natCast (n : ℕ) : toRF (n : RatFuncC K) = n := by
  show toRF (mk _ _) = _; rw [toRF_const, map_natCast]

lemma toRF_intCast (n : ℤ) : toRF (n : RatFuncC K) = n := by
  show toRF (mk _ _) = _; rw [toRF_const, map_intCast]

lemma toRF_nnratCast (q : ℚ≥0) : toRF (q : RatFuncC K) = q := by
  show toRF (mk _ _) = _; rw [toRF_const, map_nnratCast]

lemma toRF_ratCast (q : ℚ) : toRF (q : RatFuncC K) = q := by
  show toRF (mk _ _) = _; rw [toRF_const, map_ratCast]

/-- The field structure through the (noncomputable) embedding into `RatFunc K`. -/
noncomputable def instFieldNC : Field (RatFuncC K) :=
  toRF_injective.field toRF toRF_zero toRF_one toRF_add toRF_mul toRF_neg toRF_sub toRF_inv
    toRF_div toRF_nsmul toRF_zsmul toRF_nnqsmul toRF_qsmul toRF_npow toRF_zpow toRF_natCast
    toRF_intCast toRF_nnratCast toRF_ratCast

/-- **`K(t)` is a field** (computable data, proofs from `instFieldNC`). -/
instance instField : Field (RatFuncC K) where
  zero := 0
  add := (· + ·)
  add_assoc := (instFieldNC (K := K)).add_assoc
  zero_add := (instFieldNC (K := K)).zero_add
  add_zero := (instFieldNC (K := K)).add_zero
  nsmul := fun n x ↦ n • x
  nsmul_zero := (instFieldNC (K := K)).nsmul_zero
  nsmul_succ := (instFieldNC (K := K)).nsmul_succ
  add_comm := (instFieldNC (K := K)).add_comm
  one := 1
  mul := (· * ·)
  mul_assoc := (instFieldNC (K := K)).mul_assoc
  one_mul := (instFieldNC (K := K)).one_mul
  mul_one := (instFieldNC (K := K)).mul_one
  npow := fun n x ↦ x ^ n
  npow_zero := (instFieldNC (K := K)).npow_zero
  npow_succ := (instFieldNC (K := K)).npow_succ
  zero_mul := (instFieldNC (K := K)).zero_mul
  mul_zero := (instFieldNC (K := K)).mul_zero
  left_distrib := (instFieldNC (K := K)).left_distrib
  right_distrib := (instFieldNC (K := K)).right_distrib
  natCast := fun n ↦ (n : RatFuncC K)
  natCast_zero := (instFieldNC (K := K)).natCast_zero
  natCast_succ := (instFieldNC (K := K)).natCast_succ
  neg := Neg.neg
  sub := Sub.sub
  zsmul := fun n x ↦ n • x
  sub_eq_add_neg := (instFieldNC (K := K)).sub_eq_add_neg
  zsmul_zero' := (instFieldNC (K := K)).zsmul_zero'
  zsmul_succ' := (instFieldNC (K := K)).zsmul_succ'
  zsmul_neg' := (instFieldNC (K := K)).zsmul_neg'
  neg_add_cancel := (instFieldNC (K := K)).neg_add_cancel
  intCast := fun n ↦ (n : RatFuncC K)
  intCast_ofNat := (instFieldNC (K := K)).intCast_ofNat
  intCast_negSucc := (instFieldNC (K := K)).intCast_negSucc
  mul_comm := (instFieldNC (K := K)).mul_comm
  inv := Inv.inv
  div := (· / ·)
  zpow := fun n x ↦ x ^ n
  div_eq_mul_inv := (instFieldNC (K := K)).div_eq_mul_inv
  zpow_zero' := (instFieldNC (K := K)).zpow_zero'
  zpow_succ' := (instFieldNC (K := K)).zpow_succ'
  zpow_neg' := (instFieldNC (K := K)).zpow_neg'
  exists_pair_ne := (instFieldNC (K := K)).exists_pair_ne
  nnratCast := fun q ↦ (q : RatFuncC K)
  ratCast := fun q ↦ (q : RatFuncC K)
  mul_inv_cancel := (instFieldNC (K := K)).mul_inv_cancel
  inv_zero := (instFieldNC (K := K)).inv_zero
  nnratCast_def := (instFieldNC (K := K)).nnratCast_def
  nnqsmul := fun q x ↦ q • x
  nnqsmul_def := (instFieldNC (K := K)).nnqsmul_def
  ratCast_def := (instFieldNC (K := K)).ratCast_def
  qsmul := fun q x ↦ q • x
  qsmul_def := (instFieldNC (K := K)).qsmul_def

/-- `toRF` as a ring homomorphism. -/
noncomputable def toRFHom : RatFuncC K →+* RatFunc K where
  toFun := toRF
  map_one' := toRF_one
  map_mul' := toRF_mul
  map_zero' := toRF_zero
  map_add' := toRF_add

instance : CharZero (RatFuncC K) := ⟨fun m n h ↦ by
  have := congrArg toRF h
  rw [toRF_natCast, toRF_natCast] at this
  exact_mod_cast this⟩

/-- The constants. -/
def cst (c : K) : RatFuncC K := mk [c] [1]

/-- The variable `t`. -/
def tvar : RatFuncC K := mk [0, 1] [1]

/-- The embedding of `K`. -/
def cstHom : K →+* RatFuncC K where
  toFun := cst
  map_one' := toRF_injective (by rw [cst, toRF_const, map_one]; exact toRF_one.symm)
  map_mul' a b := toRF_injective (by
    show toRF (cst (a * b)) = toRF (cst a * cst b)
    rw [toRF_mul, cst, cst, cst, toRF_const, toRF_const, toRF_const, map_mul])
  map_zero' := toRF_injective (by rw [cst, toRF_const, map_zero]; exact toRF_zero.symm)
  map_add' a b := toRF_injective (by
    show toRF (cst (a + b)) = toRF (cst a + cst b)
    rw [toRF_add, cst, cst, cst, toRF_const, toRF_const, toRF_const, map_add])

instance : Algebra K (RatFuncC K) := cstHom.toAlgebra

lemma toRF_algebraMap (c : K) : toRF (algebraMap K (RatFuncC K) c) = algebraMap K (RatFunc K) c :=
  toRF_const c

lemma toRF_tvar : toRF (tvar : RatFuncC K) = RatFunc.X := by
  rw [tvar, toRF_mk]
  simp [CPoly.toPoly, RatFunc.algebraMap_X]


/-! ### Canonical representatives -/

/-- Two trimmed lists with the same polynomial are equal. -/
lemma trim_ext {p q : CPoly K} (hp : trim p = p) (hq : trim q = q) (h : toPoly p = toPoly q) :
    p = q := by
  by_cases h0 : toPoly p = 0
  · have h1 : trim p = [] := (trim_eq_nil_iff p).mpr h0
    have h2 : trim q = [] := (trim_eq_nil_iff q).mpr (h ▸ h0)
    rw [← hp, ← hq, h1, h2]
  · have hpne : trim p ≠ [] := fun h1 ↦ h0 ((trim_eq_nil_iff p).mp h1)
    have hqne : trim q ≠ [] := fun h1 ↦ h0 (h ▸ (trim_eq_nil_iff q).mp h1)
    have hlp := length_trim hpne
    have hlq := length_trim hqne
    rw [hp] at hlp; rw [hq] at hlq
    apply List.ext_getElem
    · rw [hlp, hlq, h]
    · intro i h1 h2
      have e := congrArg (fun P ↦ P.coeff i) h
      simp only [coeff_toPoly, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
        List.getElem?_eq_getElem h2, Option.getD_some] at e
      exact e

lemma lead_trim_eq (p : CPoly K) : lead (trim p) = (toPoly p).leadingCoeff := by
  by_cases h0 : toPoly p = 0
  · rw [(trim_eq_nil_iff p).mpr h0, h0, leadingCoeff_zero]; rfl
  · have hne : trim p ≠ [] := fun h1 ↦ h0 ((trim_eq_nil_iff p).mp h1)
    have hl := length_trim hne
    rw [lead, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, leadingCoeff,
      ← toPoly_trim p, coeff_toPoly, List.getD_eq_getElem?_getD]
    congr 2
    rw [toPoly_trim]
    omega

/-- The normalized pair is coprime with a monic denominator. -/
lemma normPair_canon (p q : CPoly K) (hq : toPoly q ≠ 0) :
    IsCoprime (toPoly (normPair p q).1) (toPoly (normPair p q).2) ∧ (toPoly (normPair p q).2).Monic := by
  unfold normPair
  simp only
  have hg0 : toPoly (trim (egcd p q).1) ≠ 0 := by
    rw [toPoly_trim]; intro h
    obtain ⟨-, hdq⟩ := egcd_dvd p q
    rw [h] at hdq; exact hq (zero_dvd_iff.mp hdq)
  have hgZ : isZero (trim (egcd p q).1) = false := by
    cases h : isZero (trim (egcd p q).1)
    · rfl
    · exact absurd ((isZero_iff _).mp h) hg0
  rw [if_neg (by rw [hgZ]; exact Bool.false_ne_true)]
  obtain ⟨hdp, hdq⟩ := egcd_dvd p q
  have hdp' : toPoly (trim (egcd p q).1) ∣ toPoly p := by rw [toPoly_trim]; exact hdp
  have hdq' : toPoly (trim (egcd p q).1) ∣ toPoly q := by rw [toPoly_trim]; exact hdq
  have ep := divMod_exact (p := p) hg0 hdp'
  have eq := divMod_exact (p := q) hg0 hdq'
  set g := toPoly (trim (egcd p q).1)
  set P' := toPoly (divMod p (trim (egcd p q).1)).1
  set Q' := toPoly (divMod q (trim (egcd p q).1)).1
  have hQ' : Q' ≠ 0 := fun h ↦ hq (by rw [← eq, h, zero_mul])
  have hc : lead (trim (divMod q (trim (egcd p q).1)).1) ≠ 0 := by
    rw [lead_trim_eq]; exact leadingCoeff_ne_zero.mpr hQ'
  rw [if_neg hc]
  simp only [toPoly_smul]
  rw [lead_trim_eq]
  have hcop : IsCoprime P' Q' := by
    refine isCoprime_of_dvd _ _ (fun h ↦ hQ' h.2) fun z hz hz0 hzp hzq ↦ ?_
    have h1 : z * g ∣ toPoly p := by rw [← ep, mul_comm P' g, mul_comm z g]; exact mul_dvd_mul_left g hzp
    have h2 : z * g ∣ toPoly q := by rw [← eq, mul_comm Q' g, mul_comm z g]; exact mul_dvd_mul_left g hzq
    have h3 : z * g ∣ toPoly (egcd p q).1 := dvd_egcd p q h1 h2
    rw [← toPoly_trim] at h3
    obtain ⟨w, hw⟩ := h3
    have : g * (z * w) = g * 1 := by
      rw [mul_one]
      calc g * (z * w) = z * g * w := by ring
        _ = g := hw.symm
    exact hz (IsUnit.of_mul_eq_one w (mul_left_cancel₀ hg0 this))
  have hc0 : (Q'.leadingCoeff)⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hQ')
  refine ⟨?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hcop
    refine ⟨a * C (Q'.leadingCoeff)⁻¹⁻¹, b * C (Q'.leadingCoeff)⁻¹⁻¹, ?_⟩
    have hcc : C (Q'.leadingCoeff)⁻¹⁻¹ * C (Q'.leadingCoeff)⁻¹ = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hc0, C_1]
    linear_combination hab + (a * P' + b * Q') * hcc
  · exact monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hQ'))

/-- Coprime fractions with monic denominators are unique. -/
lemma canon_unique {P Q P' Q' : K[X]} (h : IsCoprime P Q) (hm : Q.Monic) (h' : IsCoprime P' Q')
    (hm' : Q'.Monic) (he : P * Q' = P' * Q) : P = P' ∧ Q = Q' := by
  have h1 : Q ∣ Q' := h.symm.dvd_of_dvd_mul_left ⟨P', by rw [he, mul_comm]⟩
  have h2 : Q' ∣ Q := h'.symm.dvd_of_dvd_mul_left ⟨P, by rw [← he, mul_comm]⟩
  have hQ : Q = Q' := eq_of_monic_of_associated hm hm' (associated_of_dvd_dvd h1 h2)
  subst hQ
  exact ⟨mul_right_cancel₀ hm.ne_zero he, rfl⟩

/-- The canonical representative of a pair. -/
def canonP (x : Pr K) : CPoly K × CPoly K := (trim (normPair x.1.1 x.1.2).1, trim (normPair x.1.1 x.1.2).2)

lemma canonP_congr (x y : Pr K) (h : val x = val y) : canonP x = canonP y := by
  obtain ⟨hx0, hx⟩ := normPair_spec x.1.1 x.1.2 (den_ne_zero x)
  obtain ⟨hy0, hy⟩ := normPair_spec y.1.1 y.1.2 (den_ne_zero y)
  obtain ⟨cx, mx⟩ := normPair_canon x.1.1 x.1.2 (den_ne_zero x)
  obtain ⟨cy, my⟩ := normPair_canon y.1.1 y.1.2 (den_ne_zero y)
  rw [val_eq_iff] at h
  have he : toPoly (normPair x.1.1 x.1.2).1 * toPoly (normPair y.1.1 y.1.2).2 =
      toPoly (normPair y.1.1 y.1.2).1 * toPoly (normPair x.1.1 x.1.2).2 := by
    have hX := den_ne_zero x
    have hY := den_ne_zero y
    apply mul_right_cancel₀ (mul_ne_zero hX hY)
    linear_combination (toPoly (normPair y.1.1 y.1.2).2) * toPoly y.1.2 * hx -
      (toPoly (normPair x.1.1 x.1.2).2) * toPoly x.1.2 * hy +
      (toPoly (normPair x.1.1 x.1.2).2) * (toPoly (normPair y.1.1 y.1.2).2) * h
  obtain ⟨e1, e2⟩ := canon_unique cx mx cy my he
  unfold canonP
  rw [Prod.mk.injEq]
  exact ⟨trim_ext (trim_trim _) (trim_trim _) (by rw [toPoly_trim, toPoly_trim, e1]),
    trim_ext (trim_trim _) (trim_trim _) (by rw [toPoly_trim, toPoly_trim, e2])⟩

/-- **The canonical representative** `(p, q)`: `q` monic, `gcd(p, q) = 1`, both trimmed. -/
def canon : RatFuncC K → CPoly K × CPoly K := Quotient.lift canonP canonP_congr

lemma canon_spec (x : RatFuncC K) :
    toPoly (canon x).2 ≠ 0 ∧ (toPoly (canon x).2).Monic ∧
      IsCoprime (toPoly (canon x).1) (toPoly (canon x).2) ∧
      toRF x = algebraMap K[X] (RatFunc K) (toPoly (canon x).1) /
        algebraMap K[X] (RatFunc K) (toPoly (canon x).2) := by
  obtain ⟨a, rfl, ha⟩ := exists_mk x
  have e : canon (Quotient.mk _ a : RatFuncC K) = canonP a := rfl
  rw [e, ha]
  unfold canonP
  simp only [toPoly_trim]
  obtain ⟨h0, h⟩ := normPair_spec a.1.1 a.1.2 (den_ne_zero a)
  obtain ⟨hc, hm⟩ := normPair_canon a.1.1 a.1.2 (den_ne_zero a)
  refine ⟨h0, hm, hc, ?_⟩
  rw [val_eq_div, div_eq_div_iff (algebraMap_ne_zero (den_ne_zero a)) (algebraMap_ne_zero h0),
    ← map_mul, ← map_mul, h]

/-! ### Evaluation -/

section Eval

variable {E : Type*} [Field E] (φ : K →+* E) (z : E)

/-- `z` is transcendental over the image of `φ`. -/
abbrev Transc : Prop := ∀ P : K[X], P ≠ 0 → P.eval₂ φ z ≠ 0

variable {φ z}

/-- The evaluation `t ↦ z` on `RatFunc K`. -/
noncomputable def evalRF (hz : Transc φ z) : RatFunc K →+* E :=
  RatFunc.liftRingHom (Polynomial.eval₂RingHom φ z) (fun P hP ↦ by
    have hP0 : P ≠ 0 := nonZeroDivisors.ne_zero hP
    exact mem_nonZeroDivisors_of_ne_zero (hz P hP0))

lemma evalRF_algebraMap (hz : Transc φ z) (P : K[X]) :
    evalRF hz (algebraMap K[X] (RatFunc K) P) = P.eval₂ φ z := by
  have := RatFunc.liftRingHom_apply_div (eval₂RingHom φ z) (fun P hP ↦ by
    have hP0 : P ≠ 0 := nonZeroDivisors.ne_zero hP
    exact mem_nonZeroDivisors_of_ne_zero (hz P hP0)) P 1
  rw [map_one, div_one, map_one, div_one] at this
  exact this

/-- **The evaluation `t ↦ z`**, an injective ring homomorphism `K(t) → E`. -/
noncomputable def evalHom (hz : Transc φ z) : RatFuncC K →+* E := (evalRF hz).comp toRFHom

lemma evalHom_mk (hz : Transc φ z) (p q : CPoly K) :
    evalHom hz (mk p q) = (toPoly p).eval₂ φ z / (toPoly q).eval₂ φ z := by
  rw [evalHom, RingHom.comp_apply]
  change evalRF hz (toRF (mk p q)) = _
  rw [toRF_mk, map_div₀, evalRF_algebraMap, evalRF_algebraMap]

lemma evalHom_apply (hz : Transc φ z) (x : RatFuncC K) : evalHom hz x = evalRF hz (toRF x) := rfl

lemma evalHom_quot (hz : Transc φ z) (a : Pr K) :
    evalHom hz (Quotient.mk _ a : RatFuncC K) = (toPoly a.1.1).eval₂ φ z / (toPoly a.1.2).eval₂ φ z := by
  show evalRF hz (val a) = _
  rw [val, map_div₀, evalRF_algebraMap, evalRF_algebraMap]

lemma evalHom_injective (hz : Transc φ z) : Function.Injective (evalHom hz) :=
  (evalHom hz).injective

lemma evalHom_cst (hz : Transc φ z) (c : K) : evalHom hz (algebraMap K (RatFuncC K) c) = φ c := by
  change evalHom hz (mk [c] [1]) = _
  rw [evalHom_mk]
  simp [CPoly.toPoly]

lemma evalHom_tvar (hz : Transc φ z) : evalHom hz (tvar : RatFuncC K) = z := by
  rw [tvar, evalHom_mk]
  simp [CPoly.toPoly]

end Eval

end RFC

-- Smoke test: (t² − 1)/(t − 1) = t + 1 in `ℚ(t)`.
#eval decide (RFC.mk ([-1, 0, 1] : CPoly ℚ) [-1, 1] = RFC.mk [1, 1] [1])
