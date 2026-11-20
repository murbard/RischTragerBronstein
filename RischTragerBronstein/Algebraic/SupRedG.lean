import RischTragerBronstein.Algebraic.SupRedOracle

/-!
# Global certificates and their reductions

`globalCert ζ xs ys lam`: base points `(xᵢ, yᵢ)`, the root of unity `ζ` and a non-speciality
certificate `λ`, all over `K`, reduced modulo `p`. `reduce_lift` etc.: identities among
integral elements of `K` reduce modulo `p` (through `φ : K → ℚ_p`).
-/

open Polynomial CPoly CPoly.Kron

namespace Sup

section Red

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K]
variable (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)

/-- The lift of an integral element. -/
noncomputable def zL (x : K) : ℤ_[p] :=
  if hx : R.ok x = true then Classical.choose (hR x hx) else 0

include hR in
lemma zL_spec {x : K} (hx : R.ok x = true) :
    φ x = algebraMap ℤ_[p] ℚ_[p] (zL R φ hR x) ∧ PadicInt.toZMod (zL R φ hR x) = R.red x := by
  simp only [zL, dif_pos hx]
  exact Classical.choose_spec (hR x hx)

lemma algZ_injective : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) :=
  IsFractionRing.injective ℤ_[p] ℚ_[p]

include hR in
/-- A unit with integral inverse reduces to a unit. -/
lemma red_mul_inv {x : K} (hx0 : x ≠ 0) (hx : R.ok x = true) (hxi : R.ok x⁻¹ = true) :
    R.red x * R.red x⁻¹ = 1 := by
  have h1 := zL_spec R φ hR hx
  have h2 := zL_spec R φ hR hxi
  have : zL R φ hR x * zL R φ hR x⁻¹ = 1 := by
    apply algZ_injective
    rw [map_mul, ← h1.1, ← h2.1, ← map_mul, mul_inv_cancel₀ hx0, map_one, map_one]
  rw [← h1.2, ← h2.2, ← map_mul, this, map_one]

include hR in
lemma red_ne_zero {x : K} (hx0 : x ≠ 0) (hx : R.ok x = true) (hxi : R.ok x⁻¹ = true) :
    R.red x ≠ 0 := fun h ↦ by
  have := red_mul_inv R φ hR hx0 hx hxi
  rw [h, zero_mul] at this; exact zero_ne_one this

include hR in
/-- Distinct elements with an integral inverse difference reduce to distinct residues. -/
lemma red_ne_of_sub {x y : K} (hxy : x ≠ y) (hx : R.ok x = true) (hy : R.ok y = true)
    (hw : R.ok (x - y)⁻¹ = true) : R.red x ≠ R.red y := fun h ↦ by
  have h1 := zL_spec R φ hR hx
  have h2 := zL_spec R φ hR hy
  have h3 := zL_spec R φ hR hw
  have e : (zL R φ hR x - zL R φ hR y) * zL R φ hR (x - y)⁻¹ = 1 := by
    apply algZ_injective
    rw [map_mul, map_sub, ← h1.1, ← h2.1, ← h3.1, ← map_sub, ← map_mul,
      mul_inv_cancel₀ (sub_ne_zero.mpr hxy), map_one, map_one]
  have := congrArg PadicInt.toZMod e
  rw [map_mul, map_sub, h1.2, h2.2, h, sub_self, zero_mul, map_one] at this
  exact zero_ne_one this

end Red

section Sub

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] (φ : K →+* ℚ_[p])

/-- The elements of `K` that are integral at `p` (through `φ`). -/
def intSub : Subring K where
  carrier := {x | ∃ z : ℤ_[p], φ x = algebraMap ℤ_[p] ℚ_[p] z}
  mul_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a * b, by rw [map_mul, ha, hb, map_mul]⟩
  one_mem' := ⟨1, by rw [map_one, map_one]⟩
  add_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  zero_mem' := ⟨0, by rw [map_zero, map_zero]⟩
  neg_mem' := fun ⟨a, ha⟩ ↦ ⟨-a, by rw [map_neg, ha, map_neg]⟩

/-- The lift to `ℤ_p`. -/
noncomputable def liftZ' (x : intSub φ) : ℤ_[p] := Classical.choose x.2

lemma liftZ'_spec (x : intSub φ) : φ x = algebraMap ℤ_[p] ℚ_[p] (liftZ' φ x) :=
  Classical.choose_spec x.2

lemma liftZ'_eq (x : intSub φ) (z : ℤ_[p]) (h : φ x = algebraMap ℤ_[p] ℚ_[p] z) :
    liftZ' φ x = z := algZ_injective (by rw [← liftZ'_spec, h])

/-- **Reduction modulo `p`** on the integral elements, as a ring homomorphism. -/
noncomputable def psiRed : intSub φ →+* ZMod p where
  toFun x := PadicInt.toZMod (liftZ' φ x)
  map_one' := by
    rw [liftZ'_eq φ 1 1 (by simp), map_one]
  map_mul' x y := by
    rw [liftZ'_eq φ (x * y) (liftZ' φ x * liftZ' φ y) (by
      rw [Subring.coe_mul, map_mul, liftZ'_spec, liftZ'_spec, map_mul]), map_mul]
  map_zero' := by
    rw [liftZ'_eq φ 0 0 (by simp), map_zero]
  map_add' x y := by
    rw [liftZ'_eq φ (x + y) (liftZ' φ x + liftZ' φ y) (by
      rw [Subring.coe_add, map_add, liftZ'_spec, liftZ'_spec, map_add]), map_add]

variable (R : RedFns p K) (hR : RedValid p R φ)

/-- An integral atom. -/
def atom {x : K} (hx : R.ok x = true) : intSub φ :=
  ⟨x, (hR x hx).elim fun z hz ↦ ⟨z, hz.1⟩⟩

@[simp] lemma coe_atom {x : K} (hx : R.ok x = true) : ((atom φ R hR hx : intSub φ) : K) = x := rfl

lemma psiRed_atom {x : K} (hx : R.ok x = true) : psiRed φ (atom φ R hR hx) = R.red x := by
  obtain ⟨z, hz1, hz2⟩ := hR x hx
  show PadicInt.toZMod (liftZ' φ _) = _
  rw [liftZ'_eq φ _ z hz1, hz2]

end Sub

section Global

variable {K : Type*} [Field K] [DecidableEq K]

/-- The certificate coefficient over `K`. -/
def lamK (lam : List (List K)) (n i i' k : ℕ) : K :=
  (lam.getD i []).getD (i' * (n - 1) + (k - 1)) 0

/-- **The global certificate provider**: the reductions of global data. -/
def globalCert (ζ : K) (xs ys : List K) (lam : List (List K)) : CertProv K :=
  fun _ _ R _ _ ↦ some (xs.length, xs.map R.red, ys.map R.red, R.red ζ, lam.map (·.map R.red))

lemma toPoly_mapHom {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B) (l : CPoly A) :
    toPoly (l.map g) = (toPoly l).map g := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

variable {p : ℕ} [hp : Fact p.Prime] (φ : K →+* ℚ_[p]) (R : RedFns p K) (hR : RedValid p R φ)

/-- Lifting a list of integral elements. -/
def atomsL (l : List K) (hl : ∀ c ∈ l, R.ok c = true) : List (intSub φ) :=
  l.pmap (fun x hx ↦ atom φ R hR hx) hl

omit [DecidableEq K] in
lemma atomsL_coe (l : List K) (hl : ∀ c ∈ l, R.ok c = true) :
    (atomsL φ R hR l hl).map (intSub φ).subtype = l := by
  simp [atomsL, List.map_pmap]

lemma atomsL_red (l : List K) (hl : ∀ c ∈ l, R.ok c = true) :
    (atomsL φ R hR l hl).map (psiRed φ) = l.map R.red := by
  simp only [atomsL, List.map_pmap, psiRed_atom, List.pmap_eq_map]

lemma coe_eval_intSub (P : (intSub φ)[X]) (a : intSub φ) :
    ((P.eval a : intSub φ) : K) = (P.map (intSub φ).subtype).eval (a : K) := by
  rw [eval_map]; exact (eval₂_at_apply (p := P) (intSub φ).subtype a).symm

lemma toPoly_atomsL (l : List K) (hl : ∀ c ∈ l, R.ok c = true) :
    (toPoly (atomsL φ R hR l hl)).map (intSub φ).subtype = toPoly l := by
  rw [← toPoly_mapHom, atomsL_coe]

lemma toPoly_atomsL_red (l : List K) (hl : ∀ c ∈ l, R.ok c = true) :
    (toPoly (atomsL φ R hR l hl)).map (psiRed φ) = toPoly (l.map R.red) := by
  rw [← toPoly_mapHom, atomsL_red]

include hR in
/-- `yⁿ = f(x)` reduces modulo `p`. -/
lemma red_pow_eval {l : List K} (hl : ∀ c ∈ l, R.ok c = true) {x y : K} (hx : R.ok x = true)
    (hy : R.ok y = true) (n : ℕ) (h : y ^ n = evalC l x) :
    R.red y ^ n = evalC (l.map R.red) (R.red x) := by
  have e : (atom φ R hR hy) ^ n = (toPoly (atomsL φ R hR l hl)).eval (atom φ R hR hx) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, coe_eval_intSub, toPoly_atomsL, coe_atom, coe_atom, h, evalC_eq]
  have := congrArg (psiRed φ) e
  rw [map_pow, psiRed_atom, ← eval₂_at_apply, ← eval_map, toPoly_atomsL_red, psiRed_atom,
    ← evalC_eq] at this
  exact this

include hR in
/-- A Bézout identity reduces modulo `p`. -/
lemma red_bezout {u v f : List K} (hu : ∀ c ∈ u, R.ok c = true) (hv : ∀ c ∈ v, R.ok c = true)
    (hf : ∀ c ∈ f, R.ok c = true)
    (h : toPoly u * toPoly f + toPoly v * derivative (toPoly f) = 1) :
    toPoly (u.map R.red) * toPoly (f.map R.red) +
      toPoly (v.map R.red) * derivative (toPoly (f.map R.red)) = 1 := by
  set U := toPoly (atomsL φ R hR u hu)
  set V := toPoly (atomsL φ R hR v hv)
  set Fp := toPoly (atomsL φ R hR f hf)
  have e : U * Fp + V * derivative Fp = 1 := by
    apply Polynomial.map_injective (intSub φ).subtype Subtype.coe_injective
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, ← derivative_map, U, V,
      Fp, toPoly_atomsL]
    exact h
  have := congrArg (Polynomial.map (psiRed φ)) e
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, ← derivative_map, U, V,
    Fp, toPoly_atomsL_red] at this
  exact this

include hR in
lemma red_ne_one_of {z w : K} {l : ℕ} (hz : R.ok z = true) (hw : R.ok w = true)
    (h : (z ^ l - 1) * w = 1) : R.red z ^ l ≠ 1 := by
  have e : ((atom φ R hR hz) ^ l - 1) * atom φ R hR hw = 1 := by
    apply Subtype.ext; simpa using h
  have := congrArg (psiRed φ) e
  rw [map_mul, map_sub, map_pow, map_one, psiRed_atom, psiRed_atom] at this
  intro h1
  rw [h1, sub_self, zero_mul] at this
  exact zero_ne_one this

omit [DecidableEq K] hp in
lemma squarefreeCheck_of_coprime {q : ℕ} [Fact q.Prime] {s : CPoly (ZMod q)}
    (hcop : IsCoprime (toPoly s) (derivative (toPoly s))) : squarefreeCheck s = true := by
  rw [← toPoly_deriv] at hcop
  obtain ⟨hga, hgb⟩ := egcd_dvd s (deriv s)
  have hunit : IsUnit (toPoly (egcd s (deriv s)).1) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact isUnit_of_dvd_one (huv ▸ dvd_add (Dvd.dvd.mul_left hga u) (Dvd.dvd.mul_left hgb v))
  have hne : trim (egcd s (deriv s)).1 ≠ [] := fun h ↦
    hunit.ne_zero ((trim_eq_nil_iff _).mp h)
  rw [squarefreeCheck, beq_iff_eq, length_trim hne, natDegree_eq_zero_of_isUnit hunit]

set_option maxHeartbeats 1600000 in
include hR in
/-- **The reduced global certificate passes the check** when every relevant element (and the
inverses witnessing non-vanishing) is integral at `p`. -/
theorem globalCert_check {fK : CPoly K} {n : ℕ} (hn2 : 2 ≤ n) (hnp : ((n : ℕ) : ZMod p) ≠ 0)
    (hd : 0 < fK.length - 1) (hokf : ∀ c ∈ fK, R.ok c = true)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hlci : R.ok (fK.getD (fK.length - 1) 0)⁻¹ = true)
    {u v : List K} (hu : ∀ c ∈ u, R.ok c = true) (hv : ∀ c ∈ v, R.ok c = true)
    (hbez : toPoly u * toPoly fK + toPoly v * derivative (toPoly fK) = 1)
    {ζ : K} (hζok : R.ok ζ = true) (hζn : ζ ^ n = 1)
    (hζl : ∀ l, 0 < l → l < n → ∃ w, R.ok w = true ∧ (ζ ^ l - 1) * w = 1)
    {xs ys : List K} (hgen : (n - 1) * (fK.length - 1 - 1) ≤ 2 * xs.length)
    (hlen : ys.length = xs.length)
    (hE : ∀ i < xs.length, R.ok (xs.getD i 0) = true ∧ R.ok (ys.getD i 0) = true ∧
      ys.getD i 0 ≠ 0 ∧ R.ok (ys.getD i 0)⁻¹ = true ∧ ys.getD i 0 ^ n = evalC fK (xs.getD i 0))
    (hxd : ∀ i < xs.length, ∀ j < xs.length, i ≠ j →
      xs.getD i 0 ≠ xs.getD j 0 ∧ R.ok (xs.getD i 0 - xs.getD j 0)⁻¹ = true)
    {r : ℕ} {α β : Fin r → K}
    (hΓ : ∀ q, R.ok (α q) = true ∧ R.ok (β q) = true ∧ β q ≠ 0 ∧ R.ok (β q)⁻¹ = true ∧
      β q ^ n = evalC fK (α q) ∧ ∀ x ∈ xs, α q ≠ x ∧ R.ok (α q - x)⁻¹ = true)
    (hΓd : ∀ q q', α q ≠ α q' → R.ok (α q - α q')⁻¹ = true)
    (hΓβ : ∀ q q', q ≠ q' → α q = α q' → β q ≠ β q' ∧ R.ok (β q - β q')⁻¹ = true)
    {lam : List (List K)} (h0 : R.ok 0 = true) (hlam : ∀ l ∈ lam, ∀ c ∈ l, R.ok c = true)
    (hcert : ∀ i < xs.length, ∀ ai ∈ basisN n (fK.length - 1) (n * xs.length),
      xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2 =
        ∑ i' ∈ Finset.range xs.length, ∑ k ∈ Finset.Ico 1 n, lamK lam n i i' k *
          (xs.getD i' 0 ^ ai.1 * (ζ ^ k * ys.getD i' 0) ^ ai.2)) :
    supCheckR p R fK n xs.length α β (xs.map R.red) (ys.map R.red) (R.red ζ)
      (lam.map (·.map R.red)) := by
  have hn : 0 < n := by omega
  -- reductions of list entries
  have hred0 : R.red 0 = 0 := by
    have := psiRed_atom φ R hR h0
    rw [show atom φ R hR h0 = 0 from Subtype.ext rfl, map_zero] at this
    exact this.symm
  have hgetR : ∀ (l : List K) (i : ℕ), (l.map R.red).getD i 0 = R.red (l.getD i 0) := by
    intro l i
    rw [← hred0, List.getD_map]
  have hlamZ : ∀ i i' k, lamZ p (lam.map (·.map R.red)) n i i' k = R.red (lamK lam n i i' k) := by
    intro i i' k
    simp only [lamZ, lamK]
    rw [show ([] : List (ZMod p)) = ([] : List K).map R.red from rfl, List.getD_map, hgetR]
  have hlamok : ∀ i i' k, R.ok (lamK lam n i i' k) = true := by
    intro i i' k
    simp only [lamK]
    by_cases hi : i < lam.length
    · by_cases ht : i' * (n - 1) + (k - 1) < (lam.getD i []).length
      · rw [List.getD_eq_getElem _ _ ht]
        exact hlam _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
          _ (List.getElem_mem ht)
      · rw [List.getD_eq_default _ _ (by omega)]; exact h0
    · rw [List.getD_eq_default lam [] (by omega)]; simpa using h0
  refine ⟨hn2, hnp, hd, hokf, red_ne_zero R φ hR hlc (hokf _ ?_) hlci, by simpa using hgen, ?_,
    ?_, ?_, by simp, by simp [hlen], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hlm : fK.length - 1 < fK.length := by omega
    rw [List.getD_eq_getElem _ _ hlm]; exact List.getElem_mem hlm
  · -- squarefree
    have hb := red_bezout φ R hR hu hv hokf hbez
    exact squarefreeCheck_of_coprime ⟨_, _, hb⟩
  · -- `ζ₀ⁿ = 1`
    have e : (atom φ R hR hζok) ^ n = 1 := Subtype.ext (by simpa using hζn)
    have := congrArg (psiRed φ) e
    rwa [map_pow, map_one, psiRed_atom] at this
  · intro l hl hl0
    obtain ⟨w, hw, hwe⟩ := hζl l hl0 (List.mem_range.mp hl)
    exact red_ne_one_of φ R hR hζok hw hwe
  · intro i hi
    have hi' := List.mem_range.mp hi
    obtain ⟨hx, hy, hy0, hyi, hye⟩ := hE i hi'
    rw [hgetR, hgetR]
    exact ⟨red_pow_eval φ R hR hokf hx hy n hye, red_ne_zero R φ hR hy0 hy hyi⟩
  · rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij
    obtain ⟨hne, hok⟩ := hxd i hi j hj (by omega)
    have hxi := (hE i hi).1
    have hxj := (hE j hj).1
    rw [List.getD_eq_getElem _ _ hi] at hne hok hxi
    rw [List.getD_eq_getElem _ _ hj] at hne hok hxj
    exact red_ne_of_sub R φ hR hne hxi hxj hok
  · intro q
    obtain ⟨ha, hb, hb0, hbi, hbe, hax⟩ := hΓ q
    refine ⟨ha, hb, red_ne_zero R φ hR hb0 hb hbi, hbe, fun x hx ↦ ?_⟩
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hne, hok⟩ := hax x0 hx0
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx0
    have hxi := (hE i hi).1
    rw [List.getD_eq_getElem _ _ hi] at hxi
    exact red_ne_of_sub R φ hR hne ha hxi hok
  · intro q q'
    by_cases h : α q = α q'
    · exact Or.inl h
    · exact Or.inr (red_ne_of_sub R φ hR h (hΓ q).1 (hΓ q').1 (hΓd q q' h))
  · intro q q' hqq hα
    obtain ⟨hne, hok⟩ := hΓβ q q' hqq hα
    exact red_ne_of_sub R φ hR hne (hΓ q).2.1 (hΓ q').2.1 hok
  · have hxok : ∀ i, R.ok (xs.getD i 0) = true := fun i ↦ by
      by_cases hi : i < xs.length
      · exact (hE i hi).1
      · rw [List.getD_eq_default _ _ (by omega)]; exact h0
    have hyok : ∀ i, R.ok (ys.getD i 0) = true := fun i ↦ by
      by_cases hi : i < xs.length
      · exact (hE i hi).2.1
      · rw [List.getD_eq_default _ _ (by omega)]; exact h0
    unfold nsCheckZ
    refine List.all_eq_true.mpr fun i hi ↦ List.all_eq_true.mpr fun ai hai ↦ ?_
    rw [decide_eq_true_eq]
    have hi' := List.mem_range.mp hi
    have e : atom φ R hR (hxok i) ^ ai.1 * atom φ R hR (hyok i) ^ ai.2 =
        ∑ i' ∈ Finset.range xs.length, ∑ k ∈ Finset.Ico 1 n, atom φ R hR (hlamok i i' k) *
          (atom φ R hR (hxok i') ^ ai.1 * (atom φ R hR hζok ^ k * atom φ R hR (hyok i')) ^ ai.2) := by
      apply Subtype.ext
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow, coe_atom, AddSubmonoidClass.coe_finset_sum]
      exact hcert i hi' ai hai
    have := congrArg (psiRed φ) e
    simp only [map_mul, map_pow, map_sum, psiRed_atom] at this
    simp only [hgetR, hlamZ]
    exact this

end Global

end Sup
