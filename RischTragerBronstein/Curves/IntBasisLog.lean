import RischTragerBronstein.Curves.Infinity
import RischTragerBronstein.Curves.PoleBounds
import Mathlib.RingTheory.Radical.Basic

/-!
# Integrality and logarithmic stability along branches

For a curve `F(x, y) = 0` over `C` (`d/dx`, constants `C`):

* `regularFinite_of_integral`: a root of a monic polynomial over `C[x]` has no pole along any
  finite branch (its branch values are roots of monic polynomials over `K⟦T⟧`);
* `regularFinite_rad_deriv`: if `f` has no finite pole and `f′ = W(x, y)/Q(x)`, then
  `rad(Q) f′` has no finite pole — along a branch `x = a + Tᴺ` above a root `a` of `Q`,
  `(x − a) d/dx` is `(T/N) d/dT`, which preserves `K⟦T⟧`; elsewhere `W/Q` has no pole.

So integral elements have derivatives with squarefree denominators over the integral closure.
-/

open Polynomial HahnSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Basic

variable {K : Type*} [Field K]

lemma lowerBd_of_order_nonneg {z : LaurentSeries K} (hz : 0 ≤ z.order) : LowerBd z 0 :=
  fun k hk ↦ HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk hz)

lemma lowerBd_derivative_zero [CharZero K] {z : LaurentSeries K} (hz : LowerBd z 0) :
    LowerBd (LaurentSeries.derivative K z) 0 := fun k hk ↦ by
  rw [LaurentSeries.derivative_coeff]
  by_cases hk1 : k = -1
  · subst hk1; simp
  · rw [hz (k + 1) (by omega), mul_zero]

end Basic

section NoDeriv

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- Branch values of a root of `M ∈ C[x][Z]` are roots of `M` along the branch. -/
lemma embG_eval_poly (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (f : C⟮S.x⟯⟮S.y⟯) (M : C[X][X])
    (hev : (M.map (aeval S.x).toRingHom).eval (f : L) = 0) :
    (M.map g).eval (S.embG g hg Y hY f) = 0 := by
  set n := M.natDegree + 1
  have h1 : (M.map (aeval S.x).toRingHom).natDegree < n :=
    Nat.lt_succ_of_le (natDegree_map_le)
  have h2 : (M.map g).natDegree < n := Nat.lt_succ_of_le (natDegree_map_le)
  have e : (∑ i ∈ Finset.range n,
      (⟨aeval S.x (M.coeff i), S.aeval_mem _⟩ : C⟮S.x⟯⟮S.y⟯) * f ^ i) = 0 := by
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, ← hev, eval_eq_sum_range' h1]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coeff_map]; rfl
  have := congrArg (S.embG g hg Y hY) e
  rw [map_sum, map_zero] at this
  rw [eval_eq_sum_range' h2, ← this]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, S.embG_polyX, coeff_map]

/-- **Integral elements have no pole along finite branches.** -/
theorem regularFinite_of_integral (f : C⟮S.x⟯⟮S.y⟯) (M : C[X][X]) (hM : M.Monic)
    (hev : (M.map (aeval S.x).toRingHom).eval (f : L) = 0) : S.RegularFinite K f := by
  intro a N hN l hl r hr
  have hroot := S.embG_eval_poly (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a)
    r (S.root_of_mem hl hr) f M hev
  refine order_nonneg_of_lowerBd _ (root_lowerBd _ (hM.map _) 0 le_rfl (fun i _ ↦ ?_) _ hroot)
  rw [coeff_map, zero_mul]; exact lowerBd_branchSub_nonneg N a _

lemma derivation_branchX_ne (N : ℕ) (hN : 0 < N) (a : K) :
    LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K)) ≠ 0 := by
  rw [SuperData.derivation_branchX N hN a]
  exact HahnSeries.single_ne_zero (by exact_mod_cast hN.ne')

lemma radical_ne_zero' (Q : C[X]) : UniqueFactorizationMonoid.radical Q ≠ 0 := by
  classical
  unfold UniqueFactorizationMonoid.radical
  refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor p
    (UniqueFactorizationMonoid.mem_primeFactors.mp hp)).ne_zero

/-- A root `a` of `Q` is a root of `rad Q`. -/
lemma eval_radical_eq_zero (Q : C[X]) (hQ : Q ≠ 0) (a : K)
    (ha : (Q.map (algebraMap C K)).eval a = 0) :
    ((UniqueFactorizationMonoid.radical Q).map (algebraMap C K)).eval a = 0 := by
  obtain ⟨k, u, hu⟩ := UniqueFactorizationMonoid.exists_dvd_radical_self_pow hQ
  by_contra h
  have := congrArg (fun P : C[X] ↦ (P.map (algebraMap C K)).eval a) hu
  simp only [Polynomial.map_mul, Polynomial.map_pow, eval_mul, eval_pow, ha, zero_mul] at this
  exact pow_ne_zero k h this

end CurveData

end NoDeriv

section Main

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Logarithmic stability**: if `f` has no finite pole and `f′ = W/Q`, then `rad(Q) f′` has no
finite pole. -/
theorem regularFinite_rad_deriv (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (f : C⟮S.x⟯⟮S.y⟯)
    (hf : S.RegularFinite K f) (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0)
    (hWQ : ((f : L))′ * aeval S.x Q = S.evXY W) :
    S.RegularFinite K ((⟨aeval S.x (UniqueFactorizationMonoid.radical Q), S.aeval_mem _⟩ :
      C⟮S.x⟯⟮S.y⟯) * ⟨(f : L)′, S.derivClosedXY hC hx f f.2⟩) := by
  intro a N hN l hl r hr
  have hN0 := Nat.pos_of_ne_zero hN
  have hY := S.root_of_mem hl hr
  set R := UniqueFactorizationMonoid.radical Q with hR
  have hR0 : R ≠ 0 := radical_ne_zero' Q
  rw [map_mul, S.embG_polyX]
  refine order_nonneg_of_lowerBd _ ?_
  by_cases hQa : (Q.map (algebraMap C K)).eval a = 0
  · -- a branch above a root of `Q`: `(x − a) d/dx = (T/N) d/dT`
    have hRa := eval_radical_eq_zero Q hQ a hQa
    have hRord : LowerBd (branchSub (C := C) N a R) (N : ℤ) := by
      have ho := order_branchSub (K := K) N hN0 a R hR0
      have hm : 1 ≤ (R.map (algebraMap C K)).rootMultiplicity a :=
        (rootMultiplicity_pos ((Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hR0)).mpr
          hRa
      intro k hk
      refine HahnSeries.coeff_eq_zero_of_lt_order ?_
      rw [ho]
      have : (N : ℤ) ≤ ((N * (R.map (algebraMap C K)).rootMultiplicity a : ℕ) : ℤ) := by
        exact_mod_cast Nat.le_mul_of_pos_right N hm
      omega
    have hd := S.embG_derivG (HahnSeries.C a + single (N : ℤ) (1 : K)) (derivation_branchX_ne N hN0 a)
      (branchSub N a) (branchSub_injective N hN0 a) (fun P ↦ by rw [SuperData.branchSub_eq_subst])
      hC hx r hY (f : L) f.2
    simp only [Subtype.coe_eta] at hd
    rw [hd]
    have hfr : LowerBd (S.embG (branchSub N a) (branchSub_injective N hN0 a) r hY f) 0 :=
      lowerBd_of_order_nonneg (hf a N hN l hl r hr)
    have hδ : SuperData.deltaX (HahnSeries.C a + single (N : ℤ) (1 : K))
        (S.embG (branchSub N a) (branchSub_injective N hN0 a) r hY f) =
        (single ((N : ℤ) - 1) (N : K))⁻¹ * LaurentSeries.derivative K
          (S.embG (branchSub N a) (branchSub_injective N hN0 a) r hY f) := by
      show (LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K)))⁻¹ *
        LaurentSeries.derivation _ = _
      rw [SuperData.derivation_branchX N hN0 a, LaurentSeries.derivation_apply]
    rw [hδ]
    have hinv : LowerBd (single ((N : ℤ) - 1) (N : K))⁻¹ (-((N : ℤ) - 1)) := by
      have := lowerBd_inv (single ((N : ℤ) - 1) (N : K))
        (HahnSeries.single_ne_zero (by exact_mod_cast hN0.ne'))
      rwa [HahnSeries.order_single (by exact_mod_cast hN0.ne')] at this
    have := hRord.mul (hinv.mul (lowerBd_derivative_zero hfr))
    refine this.mono ?_
    omega
  · -- elsewhere `W/Q` has no pole
    have h1 := S.lowerBd_fin N hN0 a r hY ⟨(f : L)′, S.derivClosedXY hC hx f f.2⟩ W Q hQ hWQ
    rw [rootMultiplicity_eq_zero hQa, mul_zero, Nat.cast_zero, neg_zero] at h1
    have := (lowerBd_branchSub_nonneg N a R).mul h1
    rwa [zero_add] at this

end CurveData

end Main

end Curves
