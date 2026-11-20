import RischTragerBronstein.Algebraic.EllOrbitComplete
import RischTragerBronstein.Algebraic.EllDecideK

/-!
# Computable number fields `ℚ[x]/(f)`

For `f ∈ ℚ[x]` irreducible, `NF f` is the set of coefficient lists in normal form (trimmed
remainders modulo `f`). The operations are computable (`divMod`, `egcd`), and the field structure is
transported from Mathlib's `AdjoinRoot (toPoly f)` along the injective map `toAR`
(`Function.Injective.field`). The power basis `1, x, …, x^{n-1}` with its coordinates gives a
`QCoords` instance, so `ellDecideK` runs (and is proved correct) over any number field.
-/

open Polynomial CPoly

namespace NFC

/-- The normal form: the trimmed remainder modulo `f`. -/
def norm (f l : CPoly ℚ) : CPoly ℚ := trim (divMod l f).2

/-- Two trimmed lists with the same polynomial are equal. -/
lemma trim_ext {p q : CPoly ℚ} (hp : trim p = p) (hq : trim q = q) (h : toPoly p = toPoly q) :
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

variable (f : CPoly ℚ) [hf : Fact (Irreducible (toPoly f))]

lemma f_ne_zero : toPoly f ≠ 0 := hf.out.ne_zero

lemma norm_degree (l : CPoly ℚ) : (toPoly (norm f l)).degree < (toPoly f).degree := by
  rw [norm, toPoly_trim]; exact divMod_degree_lt _ _ (f_ne_zero f)

lemma norm_dvd (l : CPoly ℚ) : toPoly f ∣ toPoly (norm f l) - toPoly l := by
  have h := divMod_spec l f
  rw [norm, toPoly_trim, h]
  exact ⟨-toPoly (divMod l f).1, by ring⟩

/-- A polynomial of degree `< deg f` is its own normal form (as a polynomial). -/
lemma toPoly_norm_of_lt (l : CPoly ℚ) (hl : (toPoly l).degree < (toPoly f).degree) :
    toPoly (norm f l) = toPoly l := by
  have h := norm_dvd f l
  have hlt : (toPoly (norm f l) - toPoly l).degree < (toPoly f).degree :=
    (degree_sub_le _ _).trans_lt (max_lt (norm_degree f l) hl)
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt h hlt)

lemma norm_idem (l : CPoly ℚ) : norm f (norm f l) = norm f l := by
  refine trim_ext (trim_trim _) (by rw [norm, trim_trim]) ?_
  exact toPoly_norm_of_lt f _ (norm_degree f l)

/-- **The number field `ℚ[x]/(f)`**, computably. -/
def NF (f : CPoly ℚ) : Type := {l : CPoly ℚ // norm f l = l}

instance : DecidableEq (NF f) := inferInstanceAs (DecidableEq {l : CPoly ℚ // norm f l = l})

/-- The element with representative `l`. -/
def mk (l : CPoly ℚ) : NF f := ⟨norm f l, norm_idem f l⟩

/-- The comparison map to `AdjoinRoot`. -/
noncomputable def toAR (x : NF f) : AdjoinRoot (toPoly f) := AdjoinRoot.mk (toPoly f) (toPoly x.1)

lemma toAR_mk (l : CPoly ℚ) : toAR f (mk f l) = AdjoinRoot.mk (toPoly f) (toPoly l) :=
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
instance : Neg (NF f) := ⟨fun x ↦ mk f (smul (-1) x.1)⟩
instance : Sub (NF f) := ⟨fun x y ↦ mk f (sub x.1 y.1)⟩
instance : Inv (NF f) := ⟨fun x ↦ if x.1 = [] then mk f [] else mk f (EllAlgo.modInv x.1 f)⟩
instance : Div (NF f) := ⟨fun x y ↦ x * y⁻¹⟩
instance : SMul ℕ (NF f) := ⟨fun n x ↦ mk f (smul (n : ℚ) x.1)⟩
instance : SMul ℤ (NF f) := ⟨fun n x ↦ mk f (smul (n : ℚ) x.1)⟩
instance : SMul ℚ≥0 (NF f) := ⟨fun q x ↦ mk f (smul (q : ℚ) x.1)⟩
instance : SMul ℚ (NF f) := ⟨fun q x ↦ mk f (smul q x.1)⟩
instance : Pow (NF f) ℕ := ⟨fun x n ↦ npowRec n x⟩
instance : Pow (NF f) ℤ := ⟨fun x n ↦ zpowRec npowRec n x⟩
instance : NatCast (NF f) := ⟨fun n ↦ mk f [(n : ℚ)]⟩
instance : IntCast (NF f) := ⟨fun n ↦ mk f [(n : ℚ)]⟩
instance : NNRatCast (NF f) := ⟨fun q ↦ mk f [((q : ℚ≥0) : ℚ)]⟩
instance : RatCast (NF f) := ⟨fun q ↦ mk f [q]⟩

lemma toAR_const (q : ℚ) : toAR f (mk f [q]) = (q : AdjoinRoot (toPoly f)) := by
  rw [toAR_mk]; simp [CPoly.toPoly, AdjoinRoot.mk_C]

lemma toAR_zero : toAR f 0 = 0 := by
  show toAR f (mk f []) = 0; rw [toAR_mk]; simp [CPoly.toPoly]

lemma toAR_one : toAR f 1 = 1 := by
  show toAR f (mk f [1]) = 1; rw [toAR_const]; simp

lemma toAR_add (x y : NF f) : toAR f (x + y) = toAR f x + toAR f y := by
  show toAR f (mk f _) = _; rw [toAR_mk, toPoly_add, map_add]; rfl

lemma toAR_mul (x y : NF f) : toAR f (x * y) = toAR f x * toAR f y := by
  show toAR f (mk f _) = _; rw [toAR_mk, toPoly_mul, map_mul]; rfl

lemma toAR_smulC (q : ℚ) (x : NF f) :
    toAR f (mk f (smul q x.1)) = (q : AdjoinRoot (toPoly f)) * toAR f x := by
  rw [toAR_mk, toPoly_smul, map_mul, AdjoinRoot.mk_C, eq_ratCast]; rfl

lemma toAR_neg (x : NF f) : toAR f (-x) = -toAR f x := by
  show toAR f (mk f _) = _; rw [toAR_smulC]; simp

lemma toAR_sub (x y : NF f) : toAR f (x - y) = toAR f x - toAR f y := by
  show toAR f (mk f _) = _; rw [toAR_mk, toPoly_sub, map_sub]; rfl

lemma toAR_inv (x : NF f) : toAR f x⁻¹ = (toAR f x)⁻¹ := by
  show toAR f (if x.1 = [] then mk f [] else mk f (EllAlgo.modInv x.1 f)) = _
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
    have hspec := EllAlgo.modInv_spec x.1 f (f_ne_zero f) hcop
    have hmul : toAR f x * toAR f (mk f (EllAlgo.modInv x.1 f)) = 1 := by
      rw [toAR_mk, toAR, ← map_mul, ← map_one (AdjoinRoot.mk (toPoly f))]
      exact AdjoinRoot.mk_eq_mk.mpr hspec
    exact eq_inv_of_mul_eq_one_right hmul

lemma toAR_div (x y : NF f) : toAR f (x / y) = toAR f x / toAR f y := by
  show toAR f (x * y⁻¹) = _; rw [toAR_mul, toAR_inv, div_eq_mul_inv]

lemma toAR_nsmul (n : ℕ) (x : NF f) : toAR f (n • x) = n • toAR f x := by
  show toAR f (mk f _) = _; rw [toAR_smulC, nsmul_eq_mul]; simp

lemma toAR_zsmul (n : ℤ) (x : NF f) : toAR f (n • x) = n • toAR f x := by
  show toAR f (mk f _) = _; rw [toAR_smulC, zsmul_eq_mul]; simp

lemma toAR_nnqsmul (q : ℚ≥0) (x : NF f) : toAR f (q • x) = q • toAR f x := by
  show toAR f (mk f _) = _; rw [toAR_smulC, NNRat.smul_def]; simp

lemma toAR_qsmul (q : ℚ) (x : NF f) : toAR f (q • x) = q • toAR f x := by
  show toAR f (mk f _) = _; rw [toAR_smulC, Rat.smul_def]

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
  show toAR f (mk f _) = _; rw [toAR_const]; simp

lemma toAR_intCast (n : ℤ) : toAR f n = n := by
  show toAR f (mk f _) = _; rw [toAR_const]; simp

lemma toAR_nnratCast (q : ℚ≥0) : toAR f q = q := by
  show toAR f (mk f _) = _; rw [toAR_const]; simp

lemma toAR_ratCast (q : ℚ) : toAR f q = q := by
  show toAR f (mk f _) = _; rw [toAR_const]

/-- The field structure built through the (noncomputable) embedding into `AdjoinRoot`; its
proofs are reused by the computable instance `instField`. -/
noncomputable def instFieldNC : Field (NF f) :=
  (toAR_injective f).field (toAR f) (toAR_zero f) (toAR_one f) (toAR_add f) (toAR_mul f)
    (toAR_neg f) (toAR_sub f) (toAR_inv f) (toAR_div f) (toAR_nsmul f) (toAR_zsmul f)
    (toAR_nnqsmul f) (toAR_qsmul f) (toAR_npow f) (toAR_zpow f) (toAR_natCast f) (toAR_intCast f)
    (toAR_nnratCast f) (toAR_ratCast f)

/-- **`ℚ[x]/(f)` is a field** (computable data, proofs from `instFieldNC`). -/
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
  exact_mod_cast this⟩


/-! ### The power basis -/

lemma getD_eq_coeff (x : NF f) (i : ℕ) : x.1.getD i 0 = (toPoly x.1).coeff i :=
  (coeff_toPoly _ _).symm

lemma val_add (x y : NF f) : toPoly (x + y).1 = toPoly x.1 + toPoly y.1 := by
  show toPoly (norm f (add x.1 y.1)) = _
  rw [toPoly_norm_of_lt, toPoly_add]
  rw [toPoly_add]
  exact (degree_add_le _ _).trans_lt (max_lt (degree_val f x) (degree_val f y))

lemma val_qsmul (q : ℚ) (x : NF f) : toPoly (q • x).1 = C q * toPoly x.1 := by
  show toPoly (norm f (smul q x.1)) = _
  rw [toPoly_norm_of_lt, toPoly_smul]
  rw [toPoly_smul]
  calc (C q * toPoly x.1).degree ≤ (toPoly x.1).degree := by
        rw [← smul_eq_C_mul]; exact degree_smul_le _ _
    _ < _ := degree_val f x

/-- The `i`-th coordinate. -/
def coordNF (i : ℕ) : NF f →ₗ[ℚ] ℚ where
  toFun x := x.1.getD i 0
  map_add' x y := by
    simp only [getD_eq_coeff, val_add, coeff_add]
  map_smul' q x := by
    simp only [getD_eq_coeff, RingHom.id_apply, smul_eq_mul]
    rw [val_qsmul f q x, coeff_C_mul]

lemma natDegree_val_lt (z : NF f) : (toPoly z.1).natDegree < (toPoly f).natDegree := by
  by_cases h0 : toPoly z.1 = 0
  · rw [h0, natDegree_zero]
    exact Nat.pos_of_ne_zero fun h ↦ hf.out.not_isUnit (isUnit_iff_degree_eq_zero.mpr (by
      rw [degree_eq_natDegree (f_ne_zero f), h]; rfl))
  · exact natDegree_lt_natDegree h0 (degree_val f z)

lemma degC_eq_f : Kron.degC f = (toPoly f).natDegree := Kron.degC_eq f (f_ne_zero f)

instance nfCoords : EllQuad.QCoords (NF f) where
  dim := Kron.degC f
  coord i := coordNF f i
  bvec i := mk f (monomial i 1)
  repr z := by
    apply toAR_injective f
    have hlt : (toPoly z.1).natDegree < Kron.degC f := by
      rw [degC_eq_f]; exact natDegree_val_lt f z
    have hsum : toPoly z.1 = ∑ i : Fin (Kron.degC f),
        C ((toPoly z.1).coeff i) * X ^ (i : ℕ) := by
      rw [Fin.sum_univ_eq_sum_range (fun i ↦ C ((toPoly z.1).coeff i) * X ^ i)]
      conv_lhs => rw [as_sum_range' _ _ hlt]
      simp [C_mul_X_pow_eq_monomial]
    calc toAR f z = AdjoinRoot.mk (toPoly f) (toPoly z.1) := rfl
      _ = AdjoinRoot.mk (toPoly f) (∑ i : Fin (Kron.degC f),
          C ((toPoly z.1).coeff i) * X ^ (i : ℕ)) := by rw [← hsum]
      _ = ∑ i : Fin (Kron.degC f), toAR f (((coordNF f i z : ℚ) : NF f) *
          mk f (monomial i 1)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [toAR_mul, toAR_ratCast, toAR_mk, toPoly_monomial, map_mul, AdjoinRoot.mk_C, eq_ratCast]
        simp [coordNF]
        left; rw [coeff_toPoly, List.getD_eq_getElem?_getD]
      _ = toAR f (∑ i : Fin (Kron.degC f), ((coordNF f i z : ℚ) : NF f) *
          mk f (monomial i 1)) := (map_sum (toARHom f) _ _).symm


/-- **Embedding `ℚ[x]/(f)` into `ℚ_p`** from a simple root of `f` modulo `p` (Hensel). -/
lemma exists_embedNF {p : ℕ} [Fact p.Prime] (fZ : ℤ[X]) (hfZ : toPoly f = fZ.map (Int.castRingHom ℚ))
    (s : ZMod p) (hs : (fZ.map (Int.castRingHom (ZMod p))).eval s = 0)
    (hs' : ((derivative fZ).map (Int.castRingHom (ZMod p))).eval s ≠ 0) :
    Nonempty (NF f →ₐ[ℚ] ℚ_[p]) := by
  obtain ⟨z, hz⟩ := EllDV.hensel_root fZ s hs hs'
  have hcoe : (PadicInt.Coe.ringHom (aeval z fZ) : ℚ_[p]) = aeval (PadicInt.Coe.ringHom z) fZ := by
    rw [aeval_def, aeval_def, hom_eval₂]
    congr 1
  have hzq : (toPoly f).eval₂ (algebraMap ℚ ℚ_[p]) (PadicInt.Coe.ringHom z) = 0 := by
    rw [← aeval_def, hfZ, show fZ.map (Int.castRingHom ℚ) = fZ.map (algebraMap ℤ ℚ) from rfl,
      aeval_map_algebraMap, ← hcoe, hz, map_zero]
  exact ⟨((AdjoinRoot.lift (algebraMap ℚ ℚ_[p]) _ hzq).comp (toARHom f)).toRatAlgHom⟩

end NFC
