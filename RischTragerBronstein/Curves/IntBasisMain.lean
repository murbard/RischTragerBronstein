import RischTragerBronstein.Curves.IntBasisAnn
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Integral bases normal at infinity with logarithmic derivation matrices

**`exists_logBasis`**: for a curve over a field `C` of characteristic `0` (derivation `d/dx`,
constants `C`) there are a basis `w₀, …, w_{n−1}` of `C(x, y)` over `C(x)`, shifts `rᵢ ≥ 0`, a
squarefree `S₀ ∈ C[x]` and polynomials `Pᵢⱼ` with

* `S₀ wᵢ′ = ∑ⱼ Pᵢⱼ wⱼ` (the derivation matrix `Pᵢⱼ/S₀` has a squarefree denominator), and
* the matrix of `w̃ᵢ = x^{−rᵢ} wᵢ`, `M̃ᵢⱼ = x^{rⱼ−rᵢ} Pᵢⱼ/S₀ − δᵢⱼ rᵢ/x`, vanishes at infinity:
  `deg (x^{rⱼ+1} Pᵢⱼ − δᵢⱼ rᵢ x^{rᵢ} S₀) ≤ rᵢ + deg S₀`.

The basis is an integral basis (`exists_IBasis`) made reduced at infinity (`exists_reduced`); the
denominator comes from logarithmic stability at finite places (`regularFinite_rad_deriv`), the
bound at infinity from logarithmic stability there (`infOrd_x_deriv`) and normality
(`reduced_normal`).

**`exists_logBasisA`** adds the residue matrices: at `x = 0` and at infinity they are annihilated
by `∏_{k<n!} (X ∓ k/n!)` (Puiseux exponents have denominators at most `n`; `IntBasisAnn`).
-/

open Polynomial HahnSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Main

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- **Integral bases normal at infinity with logarithmic derivation matrices**, with their residue
matrices: at `x = 0` (if `S₀ = x S₁`) `∏_{k<n!} (P(0) − S₁(0) k/n!) = 0`, and at infinity
`∏_{k<n!} (Λ∞ + k/n!) = 0` (`resid0_ann`, `resInf_ann`). -/
theorem exists_logBasisA (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) :
    ∃ (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ) (S0 : C[X])
      (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X]),
      (∀ c : Fin S.F.natDegree → C⟮S.x⟯,
        ∑ j, algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (c j) * w j = 0 → ∀ j, c j = 0) ∧
      S0 ≠ 0 ∧ Squarefree S0 ∧
      (∀ i, (⟨(w i : L)′, S.derivClosedXY hC hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE S0 =
        ∑ j, S.polyE (P i j) * w j) ∧
      (∀ i j, (X ^ (r j + 1) * P i j -
        (if i = j then Polynomial.C (r i : C) * X ^ r i * S0 else 0)).natDegree ≤
          r i + S0.natDegree) ∧
      (∀ S1 : C[X], S0 = X * S1 →
        ((List.range S.F.natDegree.factorial).map fun k : ℕ ↦
          S1.eval 0 * (k : C) / S.F.natDegree.factorial).foldr
        (fun μ M ↦ M * (Matrix.of (fun i j ↦ (P i j).eval 0) - μ • 1)) 1 = 0) ∧
      ((List.range S.F.natDegree.factorial).map fun k : ℕ ↦
          -((k : C) / S.F.natDegree.factorial)).foldr
        (fun μ M ↦ M * (lamInf r P S0 - μ • 1)) 1 = 0 := by
  classical
  let K := AlgebraicClosure C
  obtain ⟨w0, hw0⟩ := S.exists_IBasis K
  obtain ⟨w, r, hw, hr, hred⟩ := S.exists_reduced K w0 hw0
  -- the derivatives: `wᵢ′ = Wᵢ/Qᵢ`
  have hderiv : ∀ i, ∃ (W : C[X][X]) (Q : C[X]), Q ≠ 0 ∧
      ((w i : L))′ * aeval S.x Q = S.evXY W := fun i ↦
    S.exists_repr ⟨(w i : L)′, S.derivClosedXY hC hx _ (w i).2⟩
  choose W Q hQ hWQ using hderiv
  set S0 := UniqueFactorizationMonoid.radical (∏ i, Q i) with hS0
  have hQprod : ∏ i, Q i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hQ i
  have hS00 : S0 ≠ 0 := radical_ne_zero' _
  -- `S₀ wᵢ′` is integral, hence a polynomial combination
  have hcoord : ∀ i, ∃ c : Fin S.F.natDegree → C[X],
      (⟨(w i : L)′, S.derivClosedXY hC hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE S0 =
        ∑ j, S.polyE (c j) * w j := by
    intro i
    have hreg := S.regularFinite_rad_deriv (K := K) hC hx (w i) (hw.1 i) (W i) (Q i) (hQ i) (hWQ i)
    obtain ⟨T, hT⟩ : UniqueFactorizationMonoid.radical (Q i) ∣ S0 :=
      UniqueFactorizationMonoid.radical_dvd_radical (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
        hQprod
    have hreg2 := S.regularFinite_polyE_mul (K := K) T hreg
    obtain ⟨c, hc⟩ := hw.2.1 _ hreg2
    refine ⟨c, ?_⟩
    rw [← hc, hT, S.polyE_mul]
    ring
  choose P hP using hcoord
  have hdegP : ∀ i j, (X ^ (r j + 1) * P i j -
      (if i = j then Polynomial.C (r i : C) * X ^ r i * S0 else 0)).natDegree ≤
        r i + S0.natDegree := fun i j ↦ by
    -- normality at infinity applied to `x w̃ᵢ′`
    set wt : C⟮S.x⟯⟮S.y⟯ := (S.polyE (X ^ r i))⁻¹ * w i with hwt
    have hwt0 : S.InfOrd K wt 0 := by
      have := InfOrd.mul S (S.infOrd_inv_poly (K := K) (X ^ r i) (pow_ne_zero _ X_ne_zero)) (hr i)
      rw [natDegree_X_pow] at this
      exact InfOrd.mono S this (by omega)
    have hu := S.infOrd_x_deriv (K := K) hC hx wt 0 hwt0
    have hq : (X ^ r i * S0 : C[X]) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
    have hnorm := S.reduced_normal (K := K) w r hr hred _ hu (pqF r P S0 i) (X ^ r i * S0) hq
      (S.dX_wt hC hx w r S0 hS00 P hP i) j
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hS00, natDegree_X_pow] at hnorm
    exact hnorm
  refine ⟨w, r, S0, P, fun c hc ↦ ?_, hS00, UniqueFactorizationMonoid.squarefree_radical, hP,
    hdegP, fun S1 hS1 ↦ S.resid0_ann (K := K) hC hx w hw S0 S1 hS1 P hP,
    S.resInf_ann (K := K) hC hx w r hr hred S0 hS00 P hP hdegP⟩
  · -- independence over `C(x)`: clear denominators
    letI := algebraAdjoinSimple (F := C) S.x
    haveI := isFractionRing_adjoin_simple S.x S.htr
    have hpoly : ∀ p : C[X], S.polyE p =
        algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (algebraMap C[X] C⟮S.x⟯ p) := fun p ↦ Subtype.ext (by
      show aeval S.x p = ((algebraMap C[X] C⟮S.x⟯ p : C⟮S.x⟯) : L)
      rw [algebraMap_adjoinSimple])
    obtain ⟨⟨d, hd⟩, hdc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors C[X])
      (Finset.univ.image c)
    choose p hp using fun j ↦ hdc (c j) (Finset.mem_image_of_mem c (Finset.mem_univ j))
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have h0 := hw.2.2 p (by
      have : ∑ j, S.polyE (p j) * w j =
          algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (algebraMap C[X] C⟮S.x⟯ d) *
            ∑ j, algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (c j) * w j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hpoly, hp j, Algebra.smul_def, map_mul]
        ring
      rw [this, hc, mul_zero])
    intro j
    have := hp j
    rw [h0 j, map_zero, Algebra.smul_def] at this
    have hdne : algebraMap C[X] C⟮S.x⟯ d ≠ 0 := fun h ↦ hd0 (IsFractionRing.injective C[X] C⟮S.x⟯
      (by rw [h, map_zero]))
    exact (mul_eq_zero.mp this.symm).resolve_left hdne

/-- **Integral bases normal at infinity with logarithmic derivation matrices.** -/
theorem exists_logBasis (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) :
    ∃ (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ) (S0 : C[X])
      (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X]),
      (∀ c : Fin S.F.natDegree → C⟮S.x⟯,
        ∑ j, algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (c j) * w j = 0 → ∀ j, c j = 0) ∧
      S0 ≠ 0 ∧ Squarefree S0 ∧
      (∀ i, (⟨(w i : L)′, S.derivClosedXY hC hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE S0 =
        ∑ j, S.polyE (P i j) * w j) ∧
      ∀ i j, (X ^ (r j + 1) * P i j -
        (if i = j then Polynomial.C (r i : C) * X ^ r i * S0 else 0)).natDegree ≤
          r i + S0.natDegree := by
  obtain ⟨w, r, S0, P, h1, h2, h3, h4, h5, -, -⟩ := S.exists_logBasisA hC hx
  exact ⟨w, r, S0, P, h1, h2, h3, h4, h5⟩

end CurveData

end Main

end Curves
