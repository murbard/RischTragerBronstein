import RischTragerBronstein.Mixed.KPMain

/-!
# `B(x) yʲ` over a differential base: exactness once the logarithms are in the base

`S : SuperData C L` with `x′ = η ∈ C`. The derivation respects the decomposition
`C(x, y) = ⊕ C(x) yⁱ`: `(a yⁱ)′ = (a′ + i r a) yⁱ` with `r = (p^δ + η p′)(x) / (n p(x))`
(`deriv_mul_pow_y`). Hence (`exact_of_log_in_base`) if `b yʲ = v′ + ℓ` with `b ∈ C(x)`, `ℓ ∈ C` and
`0 < j < n`, the `yʲ`-coordinate `a` of `v` already satisfies `b yʲ = (a yʲ)′`
(`coords_unique'`: `1, y, …, yⁿ⁻¹` are independent over `C(x)`).

`liouville_exact`: combined with `logs_in_base`, a Liouville form for an integrand `b yʲ` without
poles at the finite places gives `b yʲ = (a yʲ)′`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

namespace Differential

namespace SuperData

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable (S : SuperData C L)

omit [CharZero C] [CharZero L] [Differential C] [Differential L] [DifferentialAlgebra C L] in
/-- **Coordinates over `C(x)` are unique.** -/
theorem coords_unique' (c : Fin S.n → L) (hc : ∀ i, c i ∈ C⟮S.x⟯)
    (h : ∑ i, c i * S.y ^ (i : ℕ) = 0) : ∀ i, c i = 0 := by
  classical
  set Q : C⟮S.x⟯[X] := ∑ i : Fin S.n, monomial (i : ℕ) (⟨c i, hc i⟩ : C⟮S.x⟯) with hQdef
  have hQ : aeval S.y Q = 0 := by
    rw [← h, hQdef, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [aeval_monomial, IntermediateField.algebraMap_apply]
  have hcoeff : ∀ i : Fin S.n, Q.coeff i = ⟨c i, hc i⟩ := fun i ↦ by
    rw [hQdef, finsetSum_coeff, Finset.sum_eq_single i (fun b _ hb ↦ by
      rw [coeff_monomial, if_neg (fun h ↦ hb (Fin.ext h))]) (fun h ↦ absurd (Finset.mem_univ i) h),
      coeff_monomial, if_pos rfl]
  have hQ0 : Q = 0 := by
    by_contra hQ0
    have h1 := minpoly.degree_le_of_ne_zero C⟮S.x⟯ S.y hQ0 hQ
    rw [S.minpoly_eq, degree_X_pow_sub_C S.hn] at h1
    have h2 : Q.degree < S.n := by
      refine (degree_sum_le _ _).trans_lt ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i _ ↦ ?_
      exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast i.2)
    exact absurd (h1.trans_lt h2) (lt_irrefl _)
  intro i
  have := hcoeff i
  rw [hQ0, Polynomial.coeff_zero] at this
  exact (congrArg Subtype.val this).symm

variable (η : C) (hx : S.x′ = algebraMap C L η)
include hx

omit [CharZero C] in
/-- `r = (p^δ + η p′)(x) / (n p(x))`. -/
lemma r_mem : aeval S.x (mapCoeffs S.p + Polynomial.C η * derivative S.p) /
    ((S.n : L) * aeval S.x S.p) ∈ C⟮S.x⟯ := by
  letI := algebraAdjoinSimple (F := C) S.x
  have h1 : ∀ P : C[X], aeval S.x P ∈ C⟮S.x⟯ := fun P ↦ by
    rw [← algebraMap_adjoinSimple (F := C) S.x P]; exact SetLike.coe_mem _
  exact div_mem (h1 _) (mul_mem (_root_.natCast_mem _ _) (h1 _))

/-- `(a yⁱ)′ = (a′ + i r a) yⁱ`. -/
lemma deriv_mul_pow_y (a : L) (i : ℕ) :
    (a * S.y ^ i)′ = (a′ + (i : L) * (aeval S.x (mapCoeffs S.p + Polynomial.C η * derivative S.p) /
      ((S.n : L) * aeval S.x S.p)) * a) * S.y ^ i := by
  have hp0 : aeval S.x S.p ≠ 0 := fun h ↦ S.htr ⟨S.p, S.hsq.ne_zero, h⟩
  have hy0 : S.y ≠ 0 := fun h ↦ hp0 (by rw [← S.hy, h, zero_pow S.hn.ne'])
  rw [Derivation.leibniz, Derivation.leibniz_pow, S.deriv_y' η hx, smul_eq_mul, smul_eq_mul,
    nsmul_eq_mul]
  rcases i with _ | i
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    field_simp
    ring

/-- **Exactness once the logarithmic part lies in the base.** -/
theorem exact_of_log_in_base (j : ℕ) (hj0 : 0 < j) (hjn : j < S.n) (b : L) (hb : b ∈ C⟮S.x⟯)
    (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (ℓ : C) (heq : b * S.y ^ j = v′ + algebraMap C L ℓ) :
    ∃ a ∈ C⟮S.x⟯, b * S.y ^ j = (a * S.y ^ j)′ := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  obtain ⟨a, ha⟩ := S.power_repr ⟨v, hv⟩
  have hvL : v = ∑ i : Fin S.n, (a i : L) * S.y ^ (i : ℕ) := by
    have := congrArg Subtype.val ha
    simpa using this
  set r := aeval S.x (mapCoeffs S.p + Polynomial.C η * derivative S.p) /
    ((S.n : L) * aeval S.x S.p) with hr
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedX' η hx
  have hrm : r ∈ C⟮S.x⟯ := S.r_mem η hx
  have hvd : v′ = ∑ i : Fin S.n, ((a i : L)′ + ((i : ℕ) : L) * r * (a i : L)) * S.y ^ (i : ℕ) := by
    rw [hvL, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ S.deriv_mul_pow_y η hx _ _
  -- the coordinates of `b yʲ − v′ − ℓ`
  set jj : Fin S.n := ⟨j, hjn⟩
  set i0 : Fin S.n := ⟨0, S.hn⟩
  set c : Fin S.n → L := fun i ↦ (if i = jj then b else 0) -
    ((a i : L)′ + ((i : ℕ) : L) * r * (a i : L)) - (if i = i0 then algebraMap C L ℓ else 0)
    with hcdef
  have hcm : ∀ i, c i ∈ C⟮S.x⟯ := fun i ↦ by
    refine sub_mem (sub_mem ?_ (add_mem (hcl _ (a i).2) (mul_mem (mul_mem (_root_.natCast_mem _ _) hrm)
      (a i).2))) ?_
    · split_ifs
      · exact hb
      · exact zero_mem _
    · split_ifs
      · exact IntermediateField.algebraMap_mem _ ℓ
      · exact zero_mem _
  have hsum : ∑ i, c i * S.y ^ (i : ℕ) = 0 := by
    simp only [hcdef, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [← hvd, show (i0 : ℕ) = 0 from rfl, pow_zero, mul_one, show (jj : ℕ) = j from rfl, heq]
    ring
  have hcj := S.coords_unique' c hcm hsum jj
  have hj' : jj ≠ i0 := fun h ↦ by
    have := congrArg Fin.val h
    simp [jj, i0] at this
    omega
  have hcj' : b - ((a jj : L)′ + ((jj : ℕ) : L) * r * (a jj : L)) = 0 := by
    simpa [hcdef, hj'] using hcj
  refine ⟨a jj, (a jj).2, ?_⟩
  rw [S.deriv_mul_pow_y η hx]
  rw [sub_eq_zero] at hcj'
  rw [hcj']

end SuperData

end Differential
