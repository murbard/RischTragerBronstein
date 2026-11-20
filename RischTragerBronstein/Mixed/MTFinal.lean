import RischTragerBronstein.Mixed.MTMain
import RischTragerBronstein.Elementary.AlgBase

/-!
# Mixed towers over a curve: the decision over any constant field

**`elM_decides_any`**: `elM_decides` without the hypothesis that the constants are algebraically
closed. A realization `T` (constants `Cc`, any field of characteristic zero containing all the
constants of `L`) is pushed into the algebraic closure `Ē` of `L`, over the constants of `Ē` —
which are algebraically closed (`isAlgClosed_constants`) — and restricted to its top level
`K = Cc̄(x, y, t₀, …)`. `K` is algebraic over `L`, so by the invariance of elementary
integrability under algebraic extensions of the base (`hasElementaryIntegral_isAlgebraic_iff`,
`HasElementaryIntegralIn.of_isAlgebraic`) the answer of `elM` for `K` is the answer for `L`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Differential

/-- **The constants of an algebraically closed differential field of characteristic zero are
algebraically closed**: a root of a polynomial with constant coefficients is constant. -/
theorem isAlgClosed_constants (A : Type*) [Field A] [Differential A] [CharZero A] [IsAlgClosed A] :
    IsAlgClosed (constants A) := by
  letI : Differential (constants A) := ⟨0⟩
  haveI : DifferentialAlgebra (constants A) A := ⟨fun c ↦ c.2⟩
  haveI : CharZero (constants A) := ⟨fun a b h ↦ by
    have := congrArg (fun z : constants A ↦ (z : A)) h
    simpa using this⟩
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr ↦ ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (algebraMap (constants A) A))
    (by rw [degree_map]; exact (degree_pos_of_irreducible hirr).ne')
  have hz' : aeval z p = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
  have hint : IsIntegral (constants A) z := ⟨p, hmon, hz'⟩
  have hd : z′ = 0 := by
    rw [deriv_eq_algDerivFun z hint, algDerivFun]
    have h0 : mapCoeffs (minpoly (constants A) z) = 0 := by
      ext i
      rw [coeff_mapCoeffs, coeff_zero]
      rfl
    rw [h0, map_zero, neg_zero, zero_div]
  refine ⟨⟨z, hd⟩, Subtype.val_injective ?_⟩
  change ((constants A).subtype (eval₂ (RingHom.id _) ⟨z, hd⟩ p)) = 0
  rw [Polynomial.hom_eval₂]
  exact hz'

end Differential

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}

/-- **Mixed towers of logarithms and exponentials over a curve are decided, over any constant
field**: for a realization of height `k` generating `L`, whose certificate holds, `elM` answers
for every large search bound, the answer is `true` exactly when the integrand has an elementary
integral over `L`, and then it has one over every elementary extension of `L`. -/
theorem elM_decides_any (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hsh : curveShape Fc = true) {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L]
    [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
    (T : MTower Fc ks Cc L) (k : ℕ) (hn : T.n = k) (hc : certC Fc ks lv k = true)
    (hgen : ∀ z : L, z ∈ T.F k) (q : LC k) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b, elM Fc ks lv k q N = some b ∧
      (HasElementaryIntegral (T.ev k q) ↔ b = true) ∧
      (b = true → HasElementaryIntegralIn (T.ev k q)) := by
  classical
  set Ē := AlgebraicClosure L
  obtain ⟨T', hT'n, -, hT'ev, hT'mem⟩ := T.exists_lift Ē
  haveI : IsAlgClosed (constants Ē) := isAlgClosed_constants Ē
  obtain ⟨Tk, hTkn, hTkev, hTkgen, -⟩ := T'.exists_sub k (by omega)
  have H := elM_decides (ks := ks) (lv := lv) hmon hdeg hsh k (constants Ē) (T'.F k) Tk hTkn hc
    hTkgen q
  -- `L` inside `K = F k` of the lifted tower
  set K := T'.F k
  let j : L →+* K :=
    { toFun := fun z ↦ ⟨algebraMap L Ē z, hT'mem k z (hgen z)⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ ↦ Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _) }
  letI : Algebra L K := j.toAlgebra
  haveI hDA : DifferentialAlgebra L K :=
    ⟨fun z ↦ Subtype.val_injective (by
      rw [MTower.coe_deriv]
      exact deriv_algebraMap (A := L) (B := Ē) z)⟩
  have halg : Algebra.IsAlgebraic L K := ⟨fun z ↦ by
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := L) (z : Ē)
    refine ⟨p, hp0, Subtype.val_injective ?_⟩
    let φ : K →ₐ[L] Ē :=
      { toRingHom := K.val.toRingHom
        commutes' := fun _ ↦ rfl }
    have := Polynomial.aeval_algHom_apply φ z p
    change aeval (z : Ē) p = φ (aeval z p) at this
    change φ (aeval z p) = φ 0
    rw [← this, hp, map_zero]⟩
  have hval : algebraMap L K (T.ev k q) = Tk.ev k q := Subtype.val_injective (by
    rw [hTkev k le_rfl q, hT'ev]
    rfl)
  obtain ⟨N₀, hN₀⟩ := H
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, hIn⟩ := hN₀ N hN
  refine ⟨b, hb, ?_, fun hb1 ↦ ?_⟩
  · rw [← hasElementaryIntegral_isAlgebraic_iff halg, hval]
    exact hiff
  · exact HasElementaryIntegralIn.of_isAlgebraic halg (by rw [hval]; exact hIn hb1)

end Curves.MT
