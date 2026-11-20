import RischTragerBronstein.Computable.RatFuncC
import RischTragerBronstein.Computable.Hermite

/-!
# Computable simple algebraic extensions `K[x]/(f)`

The generalization of `NFC.NF` (number fields) to any computable field `K` of characteristic zero:
for `f ∈ K[x]` irreducible, `NFK.NF f` is the set of coefficient lists in normal form, with
computable operations and the field structure transported from `AdjoinRoot (toPoly f)`.
Used for the function field `ℚ(x)[y]/(F)` of the base curve over `RatFuncC ℚ`.
-/

open Polynomial CPoly

set_option linter.unusedSectionVars false

namespace NFK

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

/-- The inverse of `u` modulo `f`. -/
def modInvK (u f : CPoly K) : CPoly K :=
  let e := egcd u f
  (divMod (smul (lead (trim e.1))⁻¹ e.2.1) f).2

lemma modInvK_spec (u f : CPoly K) (hf : toPoly f ≠ 0) (hcop : IsCoprime (toPoly u) (toPoly f)) :
    toPoly f ∣ toPoly u * toPoly (modInvK u f) - 1 := by
  obtain ⟨hg1, hg2⟩ := egcd_dvd u f
  have hbez := egcd_spec u f
  set e := egcd u f with he
  have hunit : IsUnit (toPoly e.1) := by
    obtain ⟨s, t, hst⟩ := hcop
    exact isUnit_of_dvd_one (hst ▸ dvd_add (Dvd.dvd.mul_left hg1 s) (Dvd.dvd.mul_left hg2 t))
  have hne : trim e.1 ≠ [] := fun h ↦ hunit.ne_zero ((trim_eq_nil_iff _).mp h)
  have hlen : (trim e.1).length = 1 := by
    rw [length_trim hne, natDegree_eq_zero_of_isUnit hunit]
  obtain ⟨γ, hγ⟩ := List.length_eq_one_iff.mp hlen
  obtain ⟨hγ0, hg⟩ := trim_singleton hγ
  have hlead : lead (trim e.1) = γ := by rw [hγ]; rfl
  unfold modInvK
  dsimp only
  rw [← he, hlead]
  have hsp := divMod_spec (smul γ⁻¹ e.2.1) f
  rw [toPoly_smul] at hsp
  have hinv : C γ⁻¹ * C γ = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hγ0, C_1]
  refine ⟨-(C γ⁻¹ * toPoly e.2.2) - toPoly u * toPoly (divMod (smul γ⁻¹ e.2.1) f).1, ?_⟩
  have : toPoly (divMod (smul γ⁻¹ e.2.1) f).2 =
      C γ⁻¹ * toPoly e.2.1 - toPoly (divMod (smul γ⁻¹ e.2.1) f).1 * toPoly f := by
    rw [hsp]; ring
  rw [this]
  rw [hg] at hbez
  linear_combination (C γ⁻¹) * hbez + hinv

open RFC (trim_ext)


/-- The normal form: the trimmed remainder modulo `f`. -/
def norm (f l : CPoly K) : CPoly K := trim (divMod l f).2

variable (f : CPoly K) [hf : Fact (Irreducible (toPoly f))]

lemma f_ne_zero : toPoly f ≠ 0 := hf.out.ne_zero

lemma norm_degree (l : CPoly K) : (toPoly (norm f l)).degree < (toPoly f).degree := by
  rw [norm, toPoly_trim]; exact divMod_degree_lt _ _ (f_ne_zero f)

lemma norm_dvd (l : CPoly K) : toPoly f ∣ toPoly (norm f l) - toPoly l := by
  have h := divMod_spec l f
  rw [norm, toPoly_trim, h]
  exact ⟨-toPoly (divMod l f).1, by ring⟩

/-- A polynomial of degree `< deg f` is its own normal form (as a polynomial). -/
lemma toPoly_norm_of_lt (l : CPoly K) (hl : (toPoly l).degree < (toPoly f).degree) :
    toPoly (norm f l) = toPoly l := by
  have h := norm_dvd f l
  have hlt : (toPoly (norm f l) - toPoly l).degree < (toPoly f).degree :=
    (degree_sub_le _ _).trans_lt (max_lt (norm_degree f l) hl)
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt h hlt)

lemma norm_idem (l : CPoly K) : norm f (norm f l) = norm f l := by
  refine trim_ext (trim_trim _) (by rw [norm, trim_trim]) ?_
  exact toPoly_norm_of_lt f _ (norm_degree f l)

/-- **The field `K[x]/(f)`**, computably. -/
def NF (f : CPoly K) : Type _ := {l : CPoly K // norm f l = l}

instance : DecidableEq (NF f) := inferInstanceAs (DecidableEq {l : CPoly K // norm f l = l})

/-- The element with representative `l`. -/
def mk (l : CPoly K) : NF f := ⟨norm f l, norm_idem f l⟩

/-- The comparison map to `AdjoinRoot`. -/
noncomputable def toAR (x : NF f) : AdjoinRoot (toPoly f) := AdjoinRoot.mk (toPoly f) (toPoly x.1)

lemma toAR_mk (l : CPoly K) : toAR f (mk f l) = AdjoinRoot.mk (toPoly f) (toPoly l) :=
  AdjoinRoot.mk_eq_mk.mpr (norm_dvd f l)

lemma degree_val (x : NF f) : (toPoly x.1).degree < (toPoly f).degree := by
  rw [← x.2]; exact norm_degree f _

lemma toAR_injective : Function.Injective (toAR f) := by
  intro x y h
  have hd := AdjoinRoot.mk_eq_mk.mp h
  have hlt : (toPoly x.1 - toPoly y.1).degree < (toPoly f).degree :=
    (degree_sub_le _ _).trans_lt (max_lt (degree_val f x) (degree_val f y))
  have heq := sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt hd hlt)
  apply Subtype.ext
  refine trim_ext ?_ ?_ heq
  · rw [← x.2, norm, trim_trim]
  · rw [← y.2, norm, trim_trim]


/-! ### Operations -/

instance : Zero (NF f) := ⟨mk f []⟩
instance : One (NF f) := ⟨mk f [1]⟩
instance : Add (NF f) := ⟨fun x y ↦ mk f (add x.1 y.1)⟩
instance : Mul (NF f) := ⟨fun x y ↦ mk f (mul x.1 y.1)⟩
instance : Neg (NF f) := ⟨fun x ↦ mk f (smul (-1 : K) x.1)⟩
instance : Sub (NF f) := ⟨fun x y ↦ mk f (sub x.1 y.1)⟩
instance : Inv (NF f) := ⟨fun x ↦ if x.1 = [] then mk f [] else mk f (modInvK x.1 f)⟩
instance : Div (NF f) := ⟨fun x y ↦ x * y⁻¹⟩
instance : SMul ℕ (NF f) := ⟨fun n x ↦ mk f (smul (n : K) x.1)⟩
instance : SMul ℤ (NF f) := ⟨fun n x ↦ mk f (smul (n : K) x.1)⟩
instance : SMul ℚ≥0 (NF f) := ⟨fun q x ↦ mk f (smul ((q : ℚ≥0) : K) x.1)⟩
instance : SMul ℚ (NF f) := ⟨fun q x ↦ mk f (smul (q : K) x.1)⟩
instance : Pow (NF f) ℕ := ⟨fun x n ↦ npowRec n x⟩
instance : Pow (NF f) ℤ := ⟨fun x n ↦ zpowRec npowRec n x⟩
instance : NatCast (NF f) := ⟨fun n ↦ mk f [(n : K)]⟩
instance : IntCast (NF f) := ⟨fun n ↦ mk f [(n : K)]⟩
instance : NNRatCast (NF f) := ⟨fun q ↦ mk f [((q : ℚ≥0) : K)]⟩
instance : RatCast (NF f) := ⟨fun q ↦ mk f [(q : K)]⟩

lemma toAR_const (c : K) : toAR f (mk f [c]) = algebraMap K (AdjoinRoot (toPoly f)) c := by
  rw [toAR_mk]; simp [CPoly.toPoly, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

lemma toAR_zero : toAR f 0 = 0 := by
  show toAR f (mk f []) = 0; rw [toAR_mk]; simp [CPoly.toPoly]

lemma toAR_one : toAR f 1 = 1 := by
  show toAR f (mk f [1]) = 1; rw [toAR_const, map_one]

lemma toAR_add (x y : NF f) : toAR f (x + y) = toAR f x + toAR f y := by
  show toAR f (mk f _) = _; rw [toAR_mk, toPoly_add, map_add]; rfl

lemma toAR_mul (x y : NF f) : toAR f (x * y) = toAR f x * toAR f y := by
  show toAR f (mk f _) = _; rw [toAR_mk, toPoly_mul, map_mul]; rfl

lemma toAR_smulC (c : K) (x : NF f) :
    toAR f (mk f (smul c x.1)) = algebraMap K (AdjoinRoot (toPoly f)) c * toAR f x := by
  rw [toAR_mk, toPoly_smul, map_mul, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]; rfl

lemma toAR_neg (x : NF f) : toAR f (-x) = -toAR f x := by
  show toAR f (mk f _) = _; rw [toAR_smulC, map_neg, map_one]; simp

lemma toAR_sub (x y : NF f) : toAR f (x - y) = toAR f x - toAR f y := by
  show toAR f (mk f _) = _; rw [toAR_mk, toPoly_sub, map_sub]; rfl

lemma toAR_inv (x : NF f) : toAR f x⁻¹ = (toAR f x)⁻¹ := by
  show toAR f (if x.1 = [] then mk f [] else mk f (modInvK x.1 f)) = _
  split_ifs with h0
  · have : toAR f x = 0 := by simp [toAR, h0, CPoly.toPoly]
    rw [this, inv_zero, toAR_mk]; simp [CPoly.toPoly]
  · have hx0 : toPoly x.1 ≠ 0 := by
      intro h1
      have ht : trim x.1 = x.1 := by
        have h := trim_trim (divMod x.1 f).2
        change trim (norm f x.1) = norm f x.1 at h
        rwa [x.2] at h
      exact h0 (ht ▸ (trim_eq_nil_iff x.1).mpr h1)
    have hnd : ¬toPoly f ∣ toPoly x.1 := fun hd ↦ hx0 (eq_zero_of_dvd_of_degree_lt hd (degree_val f x))
    have hcop : IsCoprime (toPoly x.1) (toPoly f) :=
      ((hf.out.coprime_iff_not_dvd).mpr hnd).symm
    have hspec := modInvK_spec x.1 f (f_ne_zero f) hcop
    have hmul : toAR f x * toAR f (mk f (modInvK x.1 f)) = 1 := by
      rw [toAR_mk, toAR, ← map_mul, ← map_one (AdjoinRoot.mk (toPoly f))]
      exact AdjoinRoot.mk_eq_mk.mpr hspec
    exact eq_inv_of_mul_eq_one_right hmul

lemma toAR_div (x y : NF f) : toAR f (x / y) = toAR f x / toAR f y := by
  show toAR f (x * y⁻¹) = _; rw [toAR_mul, toAR_inv, div_eq_mul_inv]

lemma toAR_nsmul (n : ℕ) (x : NF f) : toAR f (n • x) = n • toAR f x := by
  show toAR f (mk f _) = _; rw [toAR_smulC, nsmul_eq_mul, map_natCast]

lemma toAR_zsmul (n : ℤ) (x : NF f) : toAR f (n • x) = n • toAR f x := by
  show toAR f (mk f _) = _; rw [toAR_smulC, zsmul_eq_mul, map_intCast]

lemma toAR_nnqsmul (q : ℚ≥0) (x : NF f) : toAR f (q • x) =
    @HSMul.hSMul ℚ≥0 _ _ (@instHSMul _ _ NNRat.smulDivisionSemiring) q (toAR f x) := by
  show toAR f (mk f _) = _; rw [toAR_smulC, map_nnratCast]; exact (NNRat.smul_def q _).symm

lemma toAR_qsmul (q : ℚ) (x : NF f) : toAR f (q • x) =
    @HSMul.hSMul ℚ _ _ (@instHSMul _ _ Rat.smulDivisionRing) q (toAR f x) := by
  show toAR f (mk f _) = _; rw [toAR_smulC, map_ratCast]; exact (Rat.smul_def q _).symm

lemma toAR_npow (x : NF f) (n : ℕ) : toAR f (x ^ n) = toAR f x ^ n := by
  show toAR f (npowRec n x) = _
  induction n with
  | zero => simp [npowRec, toAR_one]
  | succ n ih => rw [npowRec, toAR_mul, ih, pow_succ]

lemma toAR_zpow (x : NF f) (n : ℤ) : toAR f (x ^ n) = toAR f x ^ n := by
  show toAR f (zpowRec npowRec n x) = _
  rcases n with n | n
  · simp only [zpowRec, Int.ofNat_eq_natCast, zpow_natCast]
    exact toAR_npow f x n
  · simp only [zpowRec, zpow_negSucc]
    rw [toAR_inv]
    exact congrArg _ (toAR_npow f x (n + 1))

lemma toAR_natCast (n : ℕ) : toAR f n = n := by
  show toAR f (mk f _) = _; rw [toAR_const, map_natCast]

lemma toAR_intCast (n : ℤ) : toAR f n = n := by
  show toAR f (mk f _) = _; rw [toAR_const, map_intCast]

lemma toAR_nnratCast (q : ℚ≥0) : toAR f q = q := by
  show toAR f (mk f _) = _; rw [toAR_const, map_nnratCast]

lemma toAR_ratCast (q : ℚ) : toAR f q = q := by
  show toAR f (mk f _) = _; rw [toAR_const, map_ratCast]

/-- The field structure built through the (noncomputable) embedding into `AdjoinRoot`; its
proofs are reused by the computable instance `instField`. -/
noncomputable def instFieldNC : Field (NF f) :=
  (toAR_injective f).field (toAR f) (toAR_zero f) (toAR_one f) (toAR_add f) (toAR_mul f)
    (toAR_neg f) (toAR_sub f) (toAR_inv f) (toAR_div f) (toAR_nsmul f) (toAR_zsmul f)
    (toAR_nnqsmul f) (toAR_qsmul f) (toAR_npow f) (toAR_zpow f) (toAR_natCast f) (toAR_intCast f)
    (toAR_nnratCast f) (toAR_ratCast f)

/-- **`K[x]/(f)` is a field** (computable data, proofs from `instFieldNC`). -/
instance instField : Field (NF f) where
  zero := 0
  add := (· + ·)
  add_assoc := (instFieldNC f).add_assoc
  zero_add := (instFieldNC f).zero_add
  add_zero := (instFieldNC f).add_zero
  nsmul := fun n x ↦ n • x
  nsmul_zero := (instFieldNC f).nsmul_zero
  nsmul_succ := (instFieldNC f).nsmul_succ
  add_comm := (instFieldNC f).add_comm
  one := 1
  mul := (· * ·)
  mul_assoc := (instFieldNC f).mul_assoc
  one_mul := (instFieldNC f).one_mul
  mul_one := (instFieldNC f).mul_one
  npow := fun n x ↦ x ^ n
  npow_zero := (instFieldNC f).npow_zero
  npow_succ := (instFieldNC f).npow_succ
  zero_mul := (instFieldNC f).zero_mul
  mul_zero := (instFieldNC f).mul_zero
  left_distrib := (instFieldNC f).left_distrib
  right_distrib := (instFieldNC f).right_distrib
  natCast := fun n ↦ (n : NF f)
  natCast_zero := (instFieldNC f).natCast_zero
  natCast_succ := (instFieldNC f).natCast_succ
  neg := Neg.neg
  sub := Sub.sub
  zsmul := fun n x ↦ n • x
  sub_eq_add_neg := (instFieldNC f).sub_eq_add_neg
  zsmul_zero' := (instFieldNC f).zsmul_zero'
  zsmul_succ' := (instFieldNC f).zsmul_succ'
  zsmul_neg' := (instFieldNC f).zsmul_neg'
  neg_add_cancel := (instFieldNC f).neg_add_cancel
  intCast := fun n ↦ (n : NF f)
  intCast_ofNat := (instFieldNC f).intCast_ofNat
  intCast_negSucc := (instFieldNC f).intCast_negSucc
  mul_comm := (instFieldNC f).mul_comm
  inv := Inv.inv
  div := (· / ·)
  zpow := fun n x ↦ x ^ n
  div_eq_mul_inv := (instFieldNC f).div_eq_mul_inv
  zpow_zero' := (instFieldNC f).zpow_zero'
  zpow_succ' := (instFieldNC f).zpow_succ'
  zpow_neg' := (instFieldNC f).zpow_neg'
  exists_pair_ne := (instFieldNC f).exists_pair_ne
  nnratCast := fun q ↦ (q : NF f)
  ratCast := fun q ↦ (q : NF f)
  mul_inv_cancel := (instFieldNC f).mul_inv_cancel
  inv_zero := (instFieldNC f).inv_zero
  nnratCast_def := (instFieldNC f).nnratCast_def
  nnqsmul := fun q x ↦ q • x
  nnqsmul_def := (instFieldNC f).nnqsmul_def
  ratCast_def := (instFieldNC f).ratCast_def
  qsmul := fun q x ↦ q • x
  qsmul_def := (instFieldNC f).qsmul_def

/-- `toAR` as a ring homomorphism. -/
noncomputable def toARHom : NF f →+* AdjoinRoot (toPoly f) where
  toFun := toAR f
  map_one' := toAR_one f
  map_mul' := toAR_mul f
  map_zero' := toAR_zero f
  map_add' := toAR_add f

instance : CharZero (NF f) := ⟨fun m n h ↦ by
  have := congrArg (toAR f) h
  rw [toAR_natCast, toAR_natCast] at this
  have h2 : ((m : K)) = n := (algebraMap K (AdjoinRoot (toPoly f))).injective (by
    rw [map_natCast, map_natCast]; exact this)
  exact_mod_cast h2⟩



end NFK
