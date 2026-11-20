import RischTragerBronstein.Mixed.KWMain
import RischTragerBronstein.Mixed.KPExact

/-!
# `B(x) yʲ` with `x′ = ω(x)`: exactness modulo `C(x)`

The generalization of `KPExact` to `x′ = ω(x)`: `(a yⁱ)′ = (a′ + i r a) yⁱ` with
`r = (p^δ + ω p′)(x) / (n p(x))` (`deriv_mul_pow_yW`), and (`exact_of_even`) if `b yʲ = v′ + g` with
`b, g ∈ C(x)` and `0 < j < n`, then `b yʲ = (a yʲ)′` for the `yʲ`-coordinate `a` of `v`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

namespace Differential

namespace SuperData

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable (S : SuperData C L)

variable (ω : C[X]) (hx : S.x′ = aeval S.x ω)
include hx

omit [CharZero C] in
/-- `r = (p^δ + η p′)(x) / (n p(x))`. -/
lemma r_memW : aeval S.x (mapCoeffs S.p + ω * derivative S.p) /
    ((S.n : L) * aeval S.x S.p) ∈ C⟮S.x⟯ := by
  letI := algebraAdjoinSimple (F := C) S.x
  have h1 : ∀ P : C[X], aeval S.x P ∈ C⟮S.x⟯ := fun P ↦ by
    rw [← algebraMap_adjoinSimple (F := C) S.x P]; exact SetLike.coe_mem _
  exact div_mem (h1 _) (mul_mem (_root_.natCast_mem _ _) (h1 _))

/-- `(a yⁱ)′ = (a′ + i r a) yⁱ`. -/
lemma deriv_mul_pow_yW (a : L) (i : ℕ) :
    (a * S.y ^ i)′ = (a′ + (i : L) * (aeval S.x (mapCoeffs S.p + ω * derivative S.p) /
      ((S.n : L) * aeval S.x S.p)) * a) * S.y ^ i := by
  have hp0 : aeval S.x S.p ≠ 0 := fun h ↦ S.htr ⟨S.p, S.hsq.ne_zero, h⟩
  have hy0 : S.y ≠ 0 := fun h ↦ hp0 (by rw [← S.hy, h, zero_pow S.hn.ne'])
  rw [Derivation.leibniz, Derivation.leibniz_pow, S.deriv_yW ω hx, smul_eq_mul, smul_eq_mul,
    nsmul_eq_mul]
  rcases i with _ | i
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    field_simp
    ring

/-- **Exactness once the logarithmic part lies in the base.** -/
theorem exact_of_even (j : ℕ) (hj0 : 0 < j) (hjn : j < S.n) (b : L) (hb : b ∈ C⟮S.x⟯)
    (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (g : L) (hg : g ∈ C⟮S.x⟯) (heq : b * S.y ^ j = v′ + g) :
    ∃ a ∈ C⟮S.x⟯, b * S.y ^ j = (a * S.y ^ j)′ := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  obtain ⟨a, ha⟩ := S.power_repr ⟨v, hv⟩
  have hvL : v = ∑ i : Fin S.n, (a i : L) * S.y ^ (i : ℕ) := by
    have := congrArg Subtype.val ha
    simpa using this
  set r := aeval S.x (mapCoeffs S.p + ω * derivative S.p) /
    ((S.n : L) * aeval S.x S.p) with hr
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedXW ω hx
  have hrm : r ∈ C⟮S.x⟯ := S.r_memW ω hx
  have hvd : v′ = ∑ i : Fin S.n, ((a i : L)′ + ((i : ℕ) : L) * r * (a i : L)) * S.y ^ (i : ℕ) := by
    rw [hvL, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ S.deriv_mul_pow_yW ω hx _ _
  -- the coordinates of `b yʲ − v′ − ℓ`
  set jj : Fin S.n := ⟨j, hjn⟩
  set i0 : Fin S.n := ⟨0, S.hn⟩
  set c : Fin S.n → L := fun i ↦ (if i = jj then b else 0) -
    ((a i : L)′ + ((i : ℕ) : L) * r * (a i : L)) - (if i = i0 then g else 0)
    with hcdef
  have hcm : ∀ i, c i ∈ C⟮S.x⟯ := fun i ↦ by
    refine sub_mem (sub_mem ?_ (add_mem (hcl _ (a i).2) (mul_mem (mul_mem (_root_.natCast_mem _ _) hrm)
      (a i).2))) ?_
    · split_ifs
      · exact hb
      · exact zero_mem _
    · split_ifs
      · exact hg
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
  rw [S.deriv_mul_pow_yW ω hx]
  rw [sub_eq_zero] at hcj'
  rw [hcj']

end SuperData

end Differential
