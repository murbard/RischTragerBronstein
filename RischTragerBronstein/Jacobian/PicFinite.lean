import RischTragerBronstein.Jacobian.AbelCore
import Mathlib.NumberTheory.ClassNumber.FunctionField
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.SeparableDegree

/-!
# Divisor classes over a finite field have finite order

For a finite field `k` of odd characteristic and `f ∈ k[x]` squarefree of degree `2g + 1`, the
function field `L = k(x)[y]/(y² − f)` has a finite class group (Mathlib:
`FunctionField.RingOfIntegers`). We show that its ring of integers is `k[x] ⊕ k[x] y`, and deduce
`exists_principalMul`: for every divisor `Γ` supported on non-branch `k`-points with distinct
abscissae, some positive multiple `h Γ` is principal (`PrincipalMul`).
-/

open Polynomial
open scoped nonZeroDivisors

namespace Jac.PicFin

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

/-- `Y² − f` over `k(x)`. -/
noncomputable def cpoly (f : k[X]) : (RatFunc k)[X] := X ^ 2 - C (algebraMap k[X] (RatFunc k) f)

lemma natDegree_cpoly (f : k[X]) : (cpoly f).natDegree = 2 := by
  unfold cpoly; compute_degree!

lemma not_square {f : k[X]} (hodd : Odd f.natDegree) (r : RatFunc k) :
    r ^ 2 ≠ algebraMap k[X] (RatFunc k) f := by
  intro h
  have hf0 : f ≠ 0 := by rintro rfl; simp at hodd
  obtain ⟨n, d, hd0, rfl⟩ : ∃ n d : k[X], d ≠ 0 ∧
      r = algebraMap k[X] (RatFunc k) n / algebraMap k[X] (RatFunc k) d :=
    ⟨r.num, r.denom, r.denom_ne_zero, (RatFunc.num_div_denom r).symm⟩
  have hd : algebraMap k[X] (RatFunc k) d ≠ 0 := fun h0 ↦
    hd0 (IsFractionRing.injective k[X] (RatFunc k) (by rw [h0, map_zero]))
  have e : algebraMap k[X] (RatFunc k) (n ^ 2) = algebraMap k[X] (RatFunc k) (f * d ^ 2) := by
    rw [map_pow, map_mul, map_pow, ← h]; field_simp
  have e' := IsFractionRing.injective k[X] (RatFunc k) e
  have hn0 : n ≠ 0 := by
    intro h0; rw [h0] at e'; simp [hf0, hd0] at e'
  have := congrArg natDegree e'
  rw [natDegree_pow, natDegree_mul hf0 (pow_ne_zero _ hd0), natDegree_pow] at this
  obtain ⟨m, hm⟩ := hodd
  omega

variable (f : k[X]) [hodd : Fact (Odd f.natDegree)]

instance irreducible_cpoly : Fact (Irreducible (cpoly f)) := by
  refine ⟨irreducible_of_degree_le_three_of_not_isRoot (by rw [natDegree_cpoly]; decide) ?_⟩
  intro r hr
  apply not_square hodd.out r
  simpa [cpoly, sub_eq_zero] using hr

/-- The function field of `y² = f`. -/
abbrev L := AdjoinRoot (cpoly f)

/-- The class `y`. -/
noncomputable abbrev yL : L f := AdjoinRoot.root (cpoly f)

instance : FunctionField k (L f) :=
  (AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible (cpoly f)))).finite

variable [Fact ((2 : k) ≠ 0)]

instance : Algebra.IsSeparable (RatFunc k) (L f) := by
  have hsep : IsSeparable (RatFunc k) (yL f) := by
    unfold IsSeparable
    rw [AdjoinRoot.minpoly_root (Irreducible.ne_zero (Fact.out : Irreducible (cpoly f)))]
    have hmon : (cpoly f).leadingCoeff = 1 := (monic_X_pow_sub_C _ two_ne_zero).leadingCoeff
    rw [hmon, inv_one, C_1, mul_one]
    have hf0 : algebraMap k[X] (RatFunc k) f ≠ 0 := by
      intro h0
      have : f = 0 := IsFractionRing.injective k[X] (RatFunc k) (by rw [h0, map_zero])
      have := hodd.out; simp_all
    have h2 : ((2 : ℕ) : RatFunc k) ≠ 0 := by
      have : (algebraMap k (RatFunc k)) 2 ≠ 0 :=
        (_root_.map_ne_zero _).mpr (Fact.out : (2 : k) ≠ 0)
      rw [map_ofNat] at this; exact_mod_cast this
    exact separable_X_pow_sub_C _ h2 hf0
  have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (RatFunc k) (L f)).2 hsep
  rw [IntermediateField.adjoin_root_eq_top] at this
  exact Algebra.IsSeparable.of_algHom (E' := ↥(⊤ : IntermediateField (RatFunc k) (L f)))
    (f := IntermediateField.topEquiv.symm.toAlgHom)



/-! ### Elements `a + b y` -/

omit [Fact ((2 : k) ≠ 0)] in
lemma algebraMap_eq : algebraMap k[X] (L f) =
    (algebraMap (RatFunc k) (L f)).comp (algebraMap k[X] (RatFunc k)) :=
  IsScalarTower.algebraMap_eq _ _ _

omit [Fact ((2 : k) ≠ 0)] in
lemma yL_sq : yL f ^ 2 = algebraMap k[X] (L f) f := by
  have h : aeval (yL f) (cpoly f) = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simp only [cpoly, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  rw [h, algebraMap_eq]; rfl

/-- `a + b y`. -/
noncomputable def elt (ψ : k[X] × k[X]) : L f :=
  algebraMap k[X] (L f) ψ.1 + algebraMap k[X] (L f) ψ.2 * yL f

omit [Fact ((2 : k) ≠ 0)] in
lemma elt_mul (ψ φ : k[X] × k[X]) : elt f ψ * elt f φ = elt f (hmul f ψ φ) := by
  simp only [elt, hmul, map_add, map_mul]
  linear_combination (algebraMap k[X] (L f) ψ.2 * algebraMap k[X] (L f) φ.2) * yL_sq f

omit [Fact ((2 : k) ≠ 0)] in
lemma elt_add (ψ φ : k[X] × k[X]) : elt f ψ + elt f φ = elt f (ψ + φ) := by
  simp only [elt, Prod.fst_add, Prod.snd_add, map_add]; ring

omit [Fact ((2 : k) ≠ 0)] in
lemma elt_zero : elt f (0, 0) = 0 := by simp [elt]

omit [Fact ((2 : k) ≠ 0)] in
lemma isIntegral_yL : IsIntegral k[X] (yL f) :=
  ⟨X ^ 2 - C f, monic_X_pow_sub_C _ two_ne_zero, by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, yL_sq, sub_self]⟩

omit [Fact ((2 : k) ≠ 0)] in
lemma isIntegral_elt (ψ : k[X] × k[X]) : IsIntegral k[X] (elt f ψ) :=
  (isIntegral_algebraMap).add ((isIntegral_algebraMap).mul (isIntegral_yL f))

omit [Fact ((2 : k) ≠ 0)] in
/-- `1, y` are linearly independent over `k(x)`. -/
lemma eq_zero_of_add_mul_yL {a b : RatFunc k}
    (h : algebraMap (RatFunc k) (L f) a + algebraMap (RatFunc k) (L f) b * yL f = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    simp only [map_zero, zero_mul, add_zero] at h
    exact ⟨(map_eq_zero _).mp h, rfl⟩
  · exfalso
    have hy : yL f = algebraMap (RatFunc k) (L f) (-a / b) := by
      rw [map_div₀, map_neg]
      have hb' : algebraMap (RatFunc k) (L f) b ≠ 0 := (_root_.map_ne_zero _).mpr hb
      field_simp
      linear_combination h
    apply not_square hodd.out (-a / b)
    apply (algebraMap (RatFunc k) (L f)).injective
    rw [map_pow, ← hy, yL_sq, algebraMap_eq]; rfl

omit [Fact ((2 : k) ≠ 0)] in
lemma elt_injective {ψ φ : k[X] × k[X]} (h : elt f ψ = elt f φ) : ψ = φ := by
  have h' : algebraMap (RatFunc k) (L f) (algebraMap k[X] (RatFunc k) (ψ.1 - φ.1)) +
      algebraMap (RatFunc k) (L f) (algebraMap k[X] (RatFunc k) (ψ.2 - φ.2)) * yL f = 0 := by
    have := sub_eq_zero.mpr h
    simp only [elt, algebraMap_eq, RingHom.comp_apply] at this
    simp only [map_sub]; linear_combination this
  obtain ⟨h1, h2⟩ := eq_zero_of_add_mul_yL f h'
  have i := IsFractionRing.injective k[X] (RatFunc k)
  exact Prod.ext (sub_eq_zero.mp (i (by rw [h1, map_zero])))
    (sub_eq_zero.mp (i (by rw [h2, map_zero])))

/-! ### The involution `y ↦ −y` -/

omit [Fact ((2 : k) ≠ 0)] in
lemma eval₂_neg_yL : (cpoly f).eval₂ (IsScalarTower.toAlgHom k[X] (RatFunc k) (L f)).toRingHom
    (-yL f) = 0 := by
  simp only [cpoly, eval₂_sub, eval₂_X_pow, eval₂_C, neg_sq]
  rw [yL_sq, algebraMap_eq]; exact sub_self _

/-- The hyperelliptic involution, over `k[x]`. -/
noncomputable def sigma : L f →ₐ[k[X]] L f :=
  AdjoinRoot.liftAlgHom (cpoly f) (IsScalarTower.toAlgHom k[X] (RatFunc k) (L f)) (-yL f)
    (eval₂_neg_yL f)

omit [Fact ((2 : k) ≠ 0)] in
lemma sigma_yL : sigma f (yL f) = -yL f := AdjoinRoot.liftAlgHom_root _ _ _ _

omit [Fact ((2 : k) ≠ 0)] in
lemma sigma_ofK (a : RatFunc k) :
    sigma f (algebraMap (RatFunc k) (L f) a) = algebraMap (RatFunc k) (L f) a :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ a

omit [Fact ((2 : k) ≠ 0)] in
lemma sigma_elt (ψ : k[X] × k[X]) : sigma f (elt f ψ) = elt f (hconj ψ) := by
  simp only [elt, hconj, map_add, map_mul, AlgHom.commutes, sigma_yL, map_neg]; ring

omit [Fact ((2 : k) ≠ 0)] in
/-- Every element is `a + b y` with `a, b ∈ k(x)`. -/
lemma exists_decomp (z : L f) : ∃ a b : RatFunc k,
    z = algebraMap (RatFunc k) (L f) a + algebraMap (RatFunc k) (L f) b * yL f := by
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    have hmon : (cpoly f).Monic := monic_X_pow_sub_C _ two_ne_zero
    have hlt : (p %ₘ cpoly f).natDegree ≤ 1 := by
      have := natDegree_modByMonic_lt p hmon (by
        intro h; have := congrArg natDegree h; rw [natDegree_cpoly, natDegree_one] at this
        exact absurd this (by decide))
      rw [natDegree_cpoly] at this; omega
    have hp : AdjoinRoot.mk (cpoly f) p = aeval (yL f) (p %ₘ cpoly f) := by
      conv_lhs => rw [← modByMonic_add_div p (cpoly f)]
      rw [← AdjoinRoot.aeval_eq, map_add, map_mul, AdjoinRoot.aeval_eq (cpoly f),
        AdjoinRoot.mk_self, zero_mul, add_zero]
    refine ⟨(p %ₘ cpoly f).coeff 0, (p %ₘ cpoly f).coeff 1, ?_⟩
    rw [hp]
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hlt]
    simp only [map_add, map_mul, aeval_C, aeval_X]; ring

omit [Fact ((2 : k) ≠ 0)] in
lemma sigma_decomp (a b : RatFunc k) :
    sigma f (algebraMap (RatFunc k) (L f) a + algebraMap (RatFunc k) (L f) b * yL f) =
      algebraMap (RatFunc k) (L f) a - algebraMap (RatFunc k) (L f) b * yL f := by
  rw [map_add, map_mul, sigma_ofK, sigma_ofK, sigma_yL]; ring

omit [Fact ((2 : k) ≠ 0)] in
lemma sigma_sigma (z : L f) : sigma f (sigma f z) = z := by
  obtain ⟨a, b, rfl⟩ := exists_decomp f z
  rw [sigma_decomp, sub_eq_add_neg, ← neg_mul, ← map_neg, sigma_decomp, map_neg, neg_mul,
    sub_neg_eq_add]


/-! ### The ring of integers is `k[x] ⊕ k[x] y` -/

omit [Fact ((2 : k) ≠ 0)] in
lemma isIntegral_of_algebraMap {t : RatFunc k}
    (h : IsIntegral k[X] (algebraMap (RatFunc k) (L f) t)) : ∃ A : k[X],
      algebraMap k[X] (RatFunc k) A = t :=
  IsIntegrallyClosed.isIntegral_iff.mp
    ((isIntegral_algHom_iff (IsScalarTower.toAlgHom k[X] (RatFunc k) (L f))
      (algebraMap (RatFunc k) (L f)).injective).mp h)

/-- **Integral elements are `a + b y` with `a, b ∈ k[x]`** (`f` squarefree, `2 ≠ 0`). -/
lemma exists_elt_of_isIntegral (hsq : Squarefree f) {z : L f} (hz : IsIntegral k[X] z) :
    ∃ ψ, z = elt f ψ := by
  obtain ⟨a, b, rfl⟩ := exists_decomp f z
  set ι := algebraMap (RatFunc k) (L f)
  set j := algebraMap k[X] (RatFunc k)
  have hz' := hz.map (sigma f)
  rw [sigma_decomp] at hz'
  have hy2 : yL f ^ 2 = ι (j f) := by rw [yL_sq, algebraMap_eq]; rfl
  obtain ⟨A, hA⟩ := isIntegral_of_algebraMap f (t := 2 * a) (by
    have := hz.add hz'; convert this using 1; simp only [ι, map_mul, map_ofNat]; ring)
  obtain ⟨Nn, hN⟩ := isIntegral_of_algebraMap f (t := a ^ 2 - b ^ 2 * j f) (by
    have := hz.mul hz'; convert this using 1
    simp only [ι, map_sub, map_mul, map_pow]; rw [← hy2]; ring)
  have h2 : (2 : k) ≠ 0 := Fact.out
  set A' := C (2 : k)⁻¹ * A
  have hA' : j A' = a := by
    have e2 : j (C (2 : k)) = 2 := by
      rw [show C (2 : k) = 2 from map_ofNat C 2]; exact map_ofNat j 2
    have hc : j (C (2 : k)⁻¹) * 2 = 1 := by
      rw [← e2, ← map_mul, ← C_mul, inv_mul_cancel₀ h2, C_1, map_one]
    show j (C (2 : k)⁻¹ * A) = a
    rw [map_mul]
    change j (C (2 : k)⁻¹) * algebraMap k[X] (RatFunc k) A = a
    rw [hA]
    linear_combination a * hc
  -- `b² f ∈ k[x]`
  have hb2 : b ^ 2 * j f = j (A' ^ 2 - Nn) := by rw [map_sub, map_pow, hA', hN]; ring
  obtain ⟨n, d, hd0, hcop, rfl⟩ : ∃ n d : k[X], d ≠ 0 ∧ IsCoprime n d ∧ b = j n / j d :=
    ⟨b.num, b.denom, b.denom_ne_zero, b.isCoprime_num_denom, (RatFunc.num_div_denom b).symm⟩
  have hjd : j d ≠ 0 := fun h0 ↦ hd0 (IsFractionRing.injective k[X] (RatFunc k)
    (by rw [h0, map_zero]))
  have e : n ^ 2 * f = (A' ^ 2 - Nn) * d ^ 2 := by
    apply IsFractionRing.injective k[X] (RatFunc k)
    simp only [map_mul, map_pow]
    rw [← hb2, div_pow]; field_simp; rfl
  have hdd : d ^ 2 ∣ f := by
    have : d ^ 2 ∣ n ^ 2 * f := ⟨A' ^ 2 - Nn, by rw [e]; ring⟩
    exact (hcop.symm.pow).dvd_of_dvd_mul_left this
  have hdu : IsUnit d := hsq d (by rw [← sq]; exact hdd)
  refine ⟨(A', n * ↑hdu.unit⁻¹), ?_⟩
  simp only [elt, algebraMap_eq, RingHom.comp_apply]
  congr 2
  · exact hA'.symm
  · have hu : j (↑hdu.unit⁻¹ : k[X]) * j d = 1 := by
      rw [← map_mul, IsUnit.val_inv_mul, map_one]
    change ι (j n / j d) = ι (j (n * ↑hdu.unit⁻¹))
    congr 1
    rw [map_mul, div_eq_iff hjd]
    linear_combination (-(j n)) * hu

/-! ### The ideals of functions vanishing on `n Γ` -/

omit [Fintype k] [DecidableEq k] in
lemma VanishAt.add' {f a b a' b' : k[X]} {x₀ Y₀ : k} {m : ℕ} (hY : IsUnit (2 * Y₀))
    (h : VanishAt f a b x₀ Y₀ m) (h' : VanishAt f a' b' x₀ Y₀ m) :
    VanishAt f (a + a') (b + b') x₀ Y₀ m := by
  obtain ⟨V, hV, hj⟩ := h
  exact ⟨V, hV, by rw [jet_add]; exact dvd_add hj (h'.jet_dvd hY hV le_rfl)⟩

/-- The ring of integers. -/
noncomputable abbrev O := FunctionField.ringOfIntegers k (L f)

variable {f}

omit [Fact ((2 : k) ≠ 0)] in
lemma elt_mem_O (ψ : k[X] × k[X]) : elt f ψ ∈ O f := isIntegral_elt f ψ

/-- The element `a + b y` of the ring of integers. -/
noncomputable def eltO (ψ : k[X] × k[X]) : O f := ⟨elt f ψ, elt_mem_O ψ⟩

/-- `{a + b y : a + b y vanishes on n Γ}`. -/
noncomputable def J (hsq : Squarefree f) {Γ : EDiv k} (hon : OnCurve f Γ) (n : ℕ) :
    Ideal (O f) where
  carrier := {z | ∃ ψ, (z : L f) = elt f ψ ∧ Vanishes f ψ (escale n Γ)}
  add_mem' := by
    rintro _ _ ⟨ψ, hψ, hv⟩ ⟨φ, hφ, hw⟩
    refine ⟨ψ + φ, by rw [Subalgebra.coe_add, hψ, hφ, elt_add], fun q hq ↦ ?_⟩
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact VanishAt.add' (hon q' hq').1 (hv (q'.1, q'.2.1, n * q'.2.2) hq)
      (hw (q'.1, q'.2.1, n * q'.2.2) hq)
  zero_mem' := by
    refine ⟨(0, 0), by simp [elt_zero], fun q hq ↦ ?_⟩
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    obtain ⟨V, hV⟩ := exists_branch (hon q' hq').1 (hon q' hq').2 (n * q'.2.2)
    exact ⟨V, hV, by simp [jet]⟩
  smul_mem' := by
    rintro c _ ⟨ψ, hψ, hv⟩
    obtain ⟨φ, hφ⟩ := exists_elt_of_isIntegral f hsq c.2
    refine ⟨hmul f φ ψ, by rw [smul_eq_mul, Subalgebra.coe_mul, hφ, hψ, elt_mul], fun q hq ↦ ?_⟩
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    have := VanishAt.hmul (hon q' hq').1 (hon q' hq').2
      (VanishAt.zero (a := φ.1) (b := φ.2) (hon q' hq').1 (hon q' hq').2)
      (hv (q'.1, q'.2.1, n * q'.2.2) hq)
    rwa [zero_add] at this

variable (hsq : Squarefree f) {Γ : EDiv k} (hon : OnCurve f Γ)

lemma mem_J {n : ℕ} {z : O f} : z ∈ J hsq hon n ↔
    ∃ ψ, (z : L f) = elt f ψ ∧ Vanishes f ψ (escale n Γ) := Iff.rfl

lemma J_mul_le (n m : ℕ) : J hsq hon n * J hsq hon m ≤ J hsq hon (n + m) := by
  rw [Submodule.mul_le]
  rintro _ ⟨ψ, hψ, hv⟩ _ ⟨φ, hφ, hw⟩
  refine ⟨hmul f ψ φ, by rw [Subalgebra.coe_mul, hψ, hφ, elt_mul], fun q hq ↦ ?_⟩
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  have := VanishAt.hmul (hon q' hq').1 (hon q' hq').2
    (hv (q'.1, q'.2.1, n * q'.2.2) (List.mem_map_of_mem (f := fun q ↦ (q.1, q.2.1, n * q.2.2)) hq'))
    (hw (q'.1, q'.2.1, m * q'.2.2) (List.mem_map_of_mem (f := fun q ↦ (q.1, q.2.1, m * q.2.2)) hq'))
  rwa [← add_mul] at this

lemma J_pow_le (n : ℕ) : J hsq hon 1 ^ (n + 1) ≤ J hsq hon (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono_left ih).trans (J_mul_le hsq hon _ _)

lemma wpoly_mem_J : eltO (wpoly Γ, 0) ∈ J hsq hon 1 := by
  refine ⟨(wpoly Γ, 0), rfl, fun q hq ↦ ?_⟩
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  obtain ⟨V, hV⟩ := exists_branch (hon q' hq').1 (hon q' hq').2 (1 * q'.2.2)
  refine ⟨V, hV, ?_⟩
  simp only [jet, zero_comp, zero_mul, add_zero, one_mul]
  apply comp_dvd_of_dvd
  exact List.dvd_prod (List.mem_map_of_mem (f := fun q : k × k × ℕ ↦ (X - C q.1) ^ q.2.2) hq')

omit [Fintype k] [DecidableEq k] hodd [Fact ((2 : k) ≠ 0)] in
include hon in
/-- **A global jet** (Chinese remainders): `V − y` vanishes on `Γ`. -/
lemma exists_V (hnd : (Γ.map Prod.fst).Nodup) : ∃ V : k[X], Vanishes f (V, -1) Γ := by
  classical
  have hbr : ∀ i : Fin Γ.length, ∃ W, IsBranch f Γ[i].1 Γ[i].2.1 Γ[i].2.2 W := fun i ↦
    exists_branch (hon _ (List.getElem_mem i.2)).1 (hon _ (List.getElem_mem i.2)).2 _
  choose W hW using hbr
  have hcop : Pairwise fun i j : Fin Γ.length ↦
      IsCoprime (Ideal.span {(X - C Γ[i].1) ^ Γ[i].2.2})
        (Ideal.span {(X - C Γ[j].1) ^ Γ[j].2.2}) := by
    intro i j hij
    simp only [Ideal.isCoprime_span_singleton_iff]
    apply IsCoprime.pow
    apply isCoprime_X_sub_C_of_isUnit_sub
    apply IsUnit.mk0
    rw [sub_ne_zero]
    intro he
    have := (List.Nodup.getElem_inj_iff hnd (i := i) (j := j) (hi := by simp) (hj := by simp)).mp
      (by simpa using he)
    exact hij (Fin.ext this)
  obtain ⟨V, hV⟩ := Ideal.exists_forall_sub_mem_ideal hcop
    (fun i ↦ (W i).comp (X - C Γ[i].1))
  refine ⟨V, fun q hq ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  refine ⟨W ⟨i, hi⟩, hW ⟨i, hi⟩, ?_⟩
  have h1 := comp_dvd_of_dvd (Ideal.mem_span_singleton.mp (hV ⟨i, hi⟩))
  convert h1 using 1
  simp only [jet, sub_comp, comp_assoc]
  simp [sub_eq_add_neg]

/-! ### The involution on the ring of integers -/

omit [Fact ((2 : k) ≠ 0)] in
lemma sigma_mem {z : L f} (hz : z ∈ O f) : sigma f z ∈ O f :=
  IsIntegral.map (sigma f) hz

/-- `y ↦ −y` on the ring of integers. -/
noncomputable def sigmaO : O f ≃+* O f where
  toFun z := ⟨sigma f z, sigma_mem z.2⟩
  invFun z := ⟨sigma f z, sigma_mem z.2⟩
  left_inv z := Subtype.ext (sigma_sigma f z)
  right_inv z := Subtype.ext (sigma_sigma f z)
  map_mul' _ _ := Subtype.ext (map_mul (sigma f) _ _)
  map_add' _ _ := Subtype.ext (map_add (sigma f) _ _)

omit [Fact ((2 : k) ≠ 0)] in
@[simp] lemma coe_sigmaO (z : O f) : ((sigmaO z : O f) : L f) = sigma f z := rfl

omit [Fact ((2 : k) ≠ 0)] in
@[simp] lemma coe_eltO (ψ : k[X] × k[X]) : ((eltO ψ : O f) : L f) = elt f ψ := rfl


omit [Fact ((2 : k) ≠ 0)] in
lemma sigma_eltO (ψ : k[X] × k[X]) : sigmaO (eltO ψ) = eltO (f := f) (hconj ψ) :=
  Subtype.ext (sigma_elt f ψ)

omit [Fact ((2 : k) ≠ 0)] in
lemma eltO_mul (ψ φ : k[X] × k[X]) : eltO (f := f) ψ * eltO φ = eltO (hmul f ψ φ) :=
  Subtype.ext (elt_mul f ψ φ)

include hon in
omit [Fintype k] [DecidableEq k] hodd [Fact ((2 : k) ≠ 0)] in
lemma isCoprime_wpoly {V : k[X]} (hV : Vanishes f (V, -1) Γ) : IsCoprime (wpoly Γ) V := by
  induction Γ with
  | nil => simp only [wpoly, List.map_nil, List.prod_nil]; exact isCoprime_one_left
  | cons q Γ ih =>
    have hon' : OnCurve f Γ := fun r hr ↦ hon r (List.mem_cons_of_mem _ hr)
    rw [wpoly, List.map_cons, List.prod_cons]
    refine IsCoprime.mul_left ?_ (ih hon' fun r hr ↦ hV r (List.mem_cons_of_mem _ hr))
    rcases Nat.eq_zero_or_pos q.2.2 with h0 | hpos
    · rw [h0, pow_zero]; exact isCoprime_one_left
    apply IsCoprime.pow_left
    rw [(irreducible_X_sub_C q.1).coprime_iff_not_dvd, dvd_iff_isRoot]
    obtain ⟨W, hW, hj⟩ := hV q List.mem_cons_self
    have h0 : (jet V (-1) q.1 W).coeff 0 = 0 := by
      obtain ⟨c, hc⟩ := hj
      rw [hc, coeff_X_pow_mul']; exact ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)
    simp only [jet, neg_comp, one_comp] at h0
    rw [coeff_add, coeff_zero_eq_eval_zero, eval_comp, neg_mul, one_mul, coeff_neg, hW.1] at h0
    simp only [eval_add, eval_X, eval_C, zero_add] at h0
    intro hr
    rw [IsRoot.def] at hr
    rw [hr, zero_add, neg_eq_zero] at h0
    have := (hon q List.mem_cons_self).1
    rw [h0, mul_zero] at this
    exact not_isUnit_zero this

variable (hnd : (Γ.map Prod.fst).Nodup)
include hnd

lemma J_mul_sigma_le :
    J hsq hon 1 * (J hsq hon 1).map (sigmaO (f := f)) ≤ Ideal.span {eltO (wpoly Γ, 0)} := by
  rw [Submodule.mul_le]
  intro a ha b hb
  obtain ⟨b', hb', rfl⟩ := (Ideal.mem_map_of_equiv sigmaO b).mp hb
  obtain ⟨ψ, hψ, hv⟩ := ha
  obtain ⟨φ, hφ, hw⟩ := hb'
  have ea : a = eltO ψ := Subtype.ext hψ
  have eb : b' = eltO φ := Subtype.ext hφ
  rw [ea, eb, sigma_eltO, eltO_mul]
  have h1 : Vanishes f (hmul f ψ (hconj φ)) Γ := fun q hq ↦ by
    have := VanishAt.hmul (hon q hq).1 (hon q hq).2
      (hv (q.1, q.2.1, 1 * q.2.2) (List.mem_map_of_mem (f := fun q ↦ (q.1, q.2.1, 1 * q.2.2)) hq))
      (VanishAt.zero (a := (hconj φ).1) (b := (hconj φ).2) (hon q hq).1 (hon q hq).2)
    rwa [one_mul, add_zero] at this
  have h2 : Vanishes f (hmul f ψ (hconj φ)) (econj Γ) := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    have hu : IsUnit (2 * -q'.2.1) := by rw [mul_neg]; exact (hon q' hq').1.neg
    have he : (-q'.2.1) ^ 2 = f.eval q'.1 := by rw [neg_sq]; exact (hon q' hq').2
    have hA : VanishAt f ψ.1 ψ.2 q'.1 (-q'.2.1) 0 := VanishAt.zero hu he
    have hB0 : VanishAt f φ.1 φ.2 q'.1 q'.2.1 (1 * q'.2.2) :=
      hw (q'.1, q'.2.1, 1 * q'.2.2) (List.mem_map_of_mem (f := fun q ↦ (q.1, q.2.1, 1 * q.2.2)) hq')
    have hB : VanishAt f (hconj φ).1 (hconj φ).2 q'.1 (-q'.2.1) (1 * q'.2.2) := hB0.hconj
    have := VanishAt.hmul (ψ := ψ) (φ := hconj φ) hu he hA hB
    rw [zero_add, one_mul] at this
    exact this
  obtain ⟨⟨u, hu⟩, ⟨v, hv'⟩⟩ := wpoly_dvd_of_vanish_both hnd hon h1 h2
  rw [Ideal.mem_span_singleton']
  refine ⟨eltO (u, v), ?_⟩
  rw [eltO_mul]
  have : hmul f (u, v) (wpoly Γ, 0) = hmul f ψ (hconj φ) := by
    refine Prod.ext ?_ ?_
    · change u * wpoly Γ + v * 0 * f = _; rw [hu]; ring
    · change u * 0 + wpoly Γ * v = _; rw [hv']; ring
  rw [this]

lemma wpoly_mem_mul_sigma :
    eltO (wpoly Γ, 0) ∈ J hsq hon 1 * (J hsq hon 1).map (sigmaO (f := f)) := by
  obtain ⟨V, hV⟩ := exists_V hon hnd
  have e1 := wpoly_mem_J hsq hon
  have e2 : eltO (V, -1) ∈ J hsq hon 1 := ⟨(V, -1), rfl, fun q hq ↦ by
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    simpa using hV q' hq'⟩
  have s1 := Ideal.mem_map_of_mem (sigmaO (f := f)) e1
  have s2 := Ideal.mem_map_of_mem (sigmaO (f := f)) e2
  obtain ⟨α, β, hαβ⟩ := isCoprime_wpoly hon hV
  have h2 : (2 : k) ≠ 0 := Fact.out
  have key : eltO (f := f) (wpoly Γ, 0) =
      eltO (α, 0) * (eltO (wpoly Γ, 0) * sigmaO (eltO (wpoly Γ, 0))) +
      eltO (C (2 : k)⁻¹ * β, 0) * (eltO (wpoly Γ, 0) * sigmaO (eltO (V, -1)) +
        eltO (V, -1) * sigmaO (eltO (wpoly Γ, 0))) := by
    apply Subtype.ext
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, coe_sigmaO, coe_eltO, sigma_elt]
    simp only [elt, hconj, map_zero, zero_mul, add_zero, neg_zero, map_neg, map_one, neg_neg,
      one_mul, map_mul]
    have hc : algebraMap k[X] (L f) (C (2 : k)⁻¹) * 2 = 1 := by
      rw [show (2 : L f) = algebraMap k[X] (L f) (C 2) by simp [map_ofNat], ← map_mul, ← C_mul,
        inv_mul_cancel₀ h2, C_1, map_one]
    have hab := congrArg (algebraMap k[X] (L f)) hαβ
    simp only [map_add, map_mul, map_one] at hab
    linear_combination (-algebraMap k[X] (L f) (wpoly Γ)) * hab -
      (algebraMap k[X] (L f) β * algebraMap k[X] (L f) (wpoly Γ) * algebraMap k[X] (L f) V) * hc
  rw [key]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul e1 s1))
    (Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.mul_mem_mul e1 s2) (Ideal.mul_mem_mul e2 s1)))

lemma J_mul_sigma :
    J hsq hon 1 * (J hsq hon 1).map (sigmaO (f := f)) = Ideal.span {eltO (wpoly Γ, 0)} :=
  le_antisymm (J_mul_sigma_le hsq hon hnd)
    ((Ideal.span_singleton_le_iff_mem _).mpr (wpoly_mem_mul_sigma hsq hon hnd))


omit [Fact ((2 : k) ≠ 0)] hsq hon hnd in
lemma eltO_pow (w : k[X]) (n : ℕ) : eltO (f := f) (w, 0) ^ n = eltO (w ^ n, 0) := by
  induction n with
  | zero => apply Subtype.ext; simp [elt]
  | succ n ih =>
    rw [pow_succ, ih, eltO_mul]; congr 1; ext <;> simp [hmul, pow_succ]

include hsq hon in
/-- **Finite order**: some positive multiple of `Γ` is principal. -/
theorem exists_principalMul_aux {g : ℕ} (hdeg : f.natDegree = 2 * g + 1) :
    ∃ h, 1 ≤ h ∧ PrincipalMul f g Γ h := by
  classical
  set I := J hsq hon 1 with hIdef
  have hw0 : wpoly Γ ≠ 0 := (wpoly_monic Γ).ne_zero
  have hwO : (eltO (f := f) (wpoly Γ, 0)) ≠ 0 := by
    intro h0
    have h1 : elt f (wpoly Γ, 0) = elt f (0, 0) := by
      rw [elt_zero]; exact congrArg Subtype.val h0
    exact hw0 (congrArg Prod.fst (elt_injective f h1))
  have hI0 : I ≠ ⊥ := fun h0 ↦ hwO ((Submodule.eq_bot_iff _).mp h0 _ (wpoly_mem_J hsq hon))
  have hI : I ∈ (Ideal (O f))⁰ := mem_nonZeroDivisors_of_ne_zero hI0
  set c := ClassGroup.mk0 (⟨I, hI⟩ : (Ideal (O f))⁰)
  set h := orderOf c
  have hpos : 0 < h := orderOf_pos c
  have hprin : (I ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hI h)]
    have : (⟨I ^ h, pow_mem hI h⟩ : (Ideal (O f))⁰) = ⟨I, hI⟩ ^ h := Subtype.ext (by simp)
    rw [this, map_pow, pow_orderOf_eq_one]
  obtain ⟨z₀, hz₀⟩ := hprin
  have hz₀' : Ideal.span {z₀} = I ^ h := hz₀.symm
  have hle : I ^ h ≤ J hsq hon h := by
    have := J_pow_le hsq hon (h - 1); rwa [Nat.sub_add_cancel hpos] at this
  obtain ⟨ψ, hψ, hv⟩ := hle (hz₀' ▸ Ideal.mem_span_singleton_self z₀)
  have ez : z₀ = eltO ψ := Subtype.ext hψ
  have key : Ideal.span {z₀ * sigmaO z₀} = Ideal.span {eltO (f := f) (wpoly Γ, 0) ^ h} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Set.image_singleton, ← Ideal.map_span,
      hz₀', Ideal.map_pow, ← mul_pow, J_mul_sigma hsq hon hnd, Ideal.span_singleton_pow]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp key
  have hN : z₀ * sigmaO z₀ = eltO (hnorm f ψ, 0) := by
    rw [ez, sigma_eltO, eltO_mul]; congr 1; ext <;> simp [hmul, hconj, hnorm] <;> ring
  obtain ⟨φ, hφ⟩ := exists_elt_of_isIntegral f hsq (u : O f).2
  obtain ⟨φ', hφ'⟩ := exists_elt_of_isIntegral f hsq ((u⁻¹ : (O f)ˣ) : O f).2
  have eu : (u : O f) = eltO φ := Subtype.ext hφ
  have eu' : ((u⁻¹ : (O f)ˣ) : O f) = eltO φ' := Subtype.ext hφ'
  rw [hN, eltO_pow] at hu
  have hu2 : eltO (f := f) (wpoly Γ ^ h, 0) * eltO φ' = eltO (hnorm f ψ, 0) := by
    rw [← hu, ← eu', mul_assoc, Units.mul_inv, mul_one]
  rw [eu, eltO_mul] at hu
  rw [eltO_mul] at hu2
  have hu1 := congrArg Prod.fst (elt_injective f (congrArg Subtype.val hu))
  have hu3 := congrArg Prod.fst (elt_injective f (congrArg Subtype.val hu2))
  simp only [hmul, zero_mul, add_zero] at hu1 hu3
  have hd1 : hnorm f ψ ∣ wpoly Γ ^ h := ⟨φ.1, hu1.symm⟩
  have hd2 : wpoly Γ ^ h ∣ hnorm f ψ := ⟨φ'.1, hu3.symm⟩
  have hN0 : hnorm f ψ ≠ 0 := fun h0 ↦ pow_ne_zero h hw0 (by rw [h0] at hd1; exact zero_dvd_iff.mp hd1)
  have hdegN : (hnorm f ψ).natDegree = h * edeg Γ := by
    apply le_antisymm
    · calc _ ≤ (wpoly Γ ^ h).natDegree := natDegree_le_of_dvd hd1 (pow_ne_zero _ hw0)
        _ = _ := by rw [natDegree_pow, natDegree_wpoly]
    · calc h * edeg Γ = (wpoly Γ ^ h).natDegree := by rw [natDegree_pow, natDegree_wpoly]
        _ ≤ _ := natDegree_le_of_dvd hd2 hN0
  have hψ0 : ψ ≠ (0, 0) := by rintro rfl; exact hN0 (by simp [hnorm])
  refine ⟨h, hpos, ψ, hψ0, ?_, hv⟩
  have := poleLE_hnorm hdeg ψ
  rwa [hdegN] at this

end Jac.PicFin

namespace Jac

/-- **Divisors over a finite field have finite order** (`Pic⁰(k)` is finite): for `f`
squarefree of degree `2g + 1` over a finite field of odd characteristic and `Γ` supported on
non-branch points with distinct abscissae, `h Γ` is principal for some `h ≥ 1`. -/
theorem exists_principalMul {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    (h2 : (2 : k) ≠ 0) {f : k[X]} {g : ℕ} (hdeg : f.natDegree = 2 * g + 1) (hsq : Squarefree f)
    {Γ : EDiv k} (hon : OnCurve f Γ) (hnd : (Γ.map Prod.fst).Nodup) :
    ∃ h, 1 ≤ h ∧ PrincipalMul f g Γ h := by
  have : Fact (Odd f.natDegree) := ⟨⟨g, hdeg⟩⟩
  have : Fact ((2 : k) ≠ 0) := ⟨h2⟩
  exact PicFin.exists_principalMul_aux hsq hon hnd hdeg

end Jac
