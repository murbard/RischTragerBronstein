import RischTragerBronstein.Mixed.KFSquare
import RischTragerBronstein.Computable.EuclidDegree
import RischTragerBronstein.Mixed.KFSquareQuad

/-!
# Rational non-squares stay non-squares over base curves of odd degree

If `√δ` lay in an extension `E/K` of odd degree, `K(√δ)` would be a subextension of degree `2`
(`not_isSquare_odd`). The function field `K₀ = ℚ(x)[y]/(F)` of a base curve of odd degree in `y`
has odd degree over `ℚ(x)`, where a rational non-square stays a non-square; so (with
`sq_KF_descend`) a rational non-square is a non-square in every `Kₘ` (`not_isSquare_KF_odd`), and
`sqOK` (linear, odd degree, or quadratic with squarefree discriminant, `quadOK`) suffices for the conjugation searches (`not_isSquare_KF_sqOK`).
-/

open Polynomial CPoly IntermediateField

namespace Curves.MT

/-- **No square root in an extension of odd degree.** -/
theorem not_isSquare_odd {K E : Type*} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    (hodd : Odd (Module.finrank K E)) (δ : K) (hδ : ¬ IsSquare δ) :
    ¬ IsSquare (algebraMap K E δ) := by
  rintro ⟨r, hr⟩
  have hint : IsIntegral K r := Algebra.IsIntegral.isIntegral r
  set p : K[X] := X ^ 2 - Polynomial.C δ with hp
  have hpm : p.Monic := by rw [hp]; exact monic_X_pow_sub_C _ two_ne_zero
  have hpr : aeval r p = 0 := by
    simp only [hp, map_sub, map_pow, aeval_X, aeval_C]; rw [hr]; ring
  have hpdeg : p.natDegree = 2 := by rw [hp]; exact natDegree_X_pow_sub_C
  have hirr : Irreducible p := by
    rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hpdeg])
      (by rw [hpdeg]; norm_num)]
    refine Multiset.eq_zero_of_forall_notMem fun a ha ↦ hδ ⟨a, ?_⟩
    rw [mem_roots hpm.ne_zero, IsRoot, hp] at ha
    simp only [eval_sub, eval_pow, eval_X, eval_C] at ha
    rw [← sq]; exact (sub_eq_zero.mp ha).symm
  have hmin : minpoly K r = p := (minpoly.eq_of_irreducible_of_monic hirr hpr hpm).symm
  have h2 : Module.finrank K K⟮r⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hmin, hpdeg]
  have hdvd : Module.finrank K K⟮r⟯ ∣ Module.finrank K E :=
    ⟨Module.finrank K⟮r⟯ E, (Module.finrank_mul_finrank K K⟮r⟯ E).symm⟩
  rw [h2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

/-- **Rational non-squares stay non-squares in every `Kₘ`** (base curve of odd degree in `y`). -/
theorem not_isSquare_KF_odd (Fc : Sup.BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))]
    (hodd : (CPoly.trim (fKc Fc)).length % 2 = 0) (q : ℚ) (hq : ¬ IsSquare q) (m : ℕ) :
    ¬ IsSquare ((q : ℚ) : KF Fc m) := by
  intro h
  obtain ⟨r, hr⟩ := sq_KF_descend Fc q m h
  set f := toPoly (fKc Fc)
  have hf0 : f ≠ 0 := hF.out.ne_zero
  have htr : CPoly.trim (fKc Fc) ≠ [] := fun h0 ↦ hf0 ((CPoly.trim_eq_nil_iff _).mp h0)
  have hlen := CPoly.length_trim htr
  have hodd' : Odd f.natDegree := by
    rw [hlen] at hodd
    show Odd (toPoly (fKc Fc)).natDegree
    rw [Nat.odd_iff]; omega
  set pb := AdjoinRoot.powerBasis hf0
  have : FiniteDimensional (RFC.RatFuncC ℚ) (AdjoinRoot f) := pb.finite
  have hrank : Module.finrank (RFC.RatFuncC ℚ) (AdjoinRoot f) = f.natDegree := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim]
  have hqK : ¬ IsSquare ((q : ℚ) : RFC.RatFuncC ℚ) := fun ⟨s, hs⟩ ↦
    hq (sq_const_RFC (K := ℚ) s q (by rw [sq]; exact hs.symm))
  apply not_isSquare_odd (E := AdjoinRoot f) (by rw [hrank]; exact hodd') _ hqK
  refine ⟨NFK.toARHom (fKc Fc) r, ?_⟩
  rw [← map_mul, ← hr, map_ratCast, map_ratCast]

end Curves.MT
