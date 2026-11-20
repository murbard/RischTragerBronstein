import RischTragerBronstein.Mixed.KBFacts
import RischTragerBronstein.Mixed.NKLog
import RischTragerBronstein.Torsion.StdCurve

/-!
# Geometric irreducibility from a single place at infinity

`wtC Fc'`: the monic curve `wⁿ + ∑ aᵢ(x) wⁱ` over `ℚ` has `deg a₀ = d > 0`, `gcd(n, d) = 1` and
`n deg aᵢ < d (n − i)` (one totally ramified place at infinity). Then it is irreducible over
`K[x]` for every field `K ⊇ ℚ` (`geomIrr_of_wt`, from `irr_of_weights`), so it can serve as a new
base curve (`GeomIrr`, `kzDecide_bc_correct`) without an Eisenstein certificate.
-/

open Polynomial

namespace Curves.MT

open CPoly CPoly.Kron Sup

/-- **The weight check** over `ℚ`. -/
def wtC (Fc' : BPoly ℚ) : Bool :=
  let n := Fc'.length - 1
  let d := degC (Fc'.getD 0 [])
  decide (0 < n) && !isZero (Fc'.getD 0 []) && Nat.gcd n d == 1 &&
    (List.range n).all fun i ↦ i == 0 || isZero (Fc'.getD i []) ||
      decide (n * degC (Fc'.getD i []) < d * (n - i))

/-- A monic polynomial over a domain whose positive-degree factors of smaller degree cannot vanish
at a root `y` is irreducible. -/
lemma irreducible_of_no_small_factor {R E : Type*} [CommRing R] [IsDomain R] [Field E]
    (f : R →+* E) (F : R[X]) (hF : F.Monic) (hd : 0 < F.natDegree) (y : E)
    (hy : (F.map f).eval y = 0)
    (hsmall : ∀ G : R[X], G.natDegree < F.natDegree → (G.map f).eval y = 0 → G = 0) :
    Irreducible F := by
  refine ⟨fun hu ↦ ?_, fun a b hab ↦ ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu; omega
  · have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← leadingCoeff_mul, ← hab]; exact hF
    have ha0 : a ≠ 0 := fun h ↦ by rw [h, zero_mul] at hab; exact hF.ne_zero hab
    have hb0 : b ≠ 0 := fun h ↦ by rw [h, mul_zero] at hab; exact hF.ne_zero hab
    have hdeg : F.natDegree = a.natDegree + b.natDegree := by rw [hab, natDegree_mul ha0 hb0]
    by_cases hadeg : a.natDegree = 0
    · left
      rw [eq_C_of_natDegree_eq_zero hadeg]
      exact isUnit_C.mpr (isUnit_iff_exists_inv.mpr ⟨_, by rw [leadingCoeff, hadeg] at hlc; exact hlc⟩)
    by_cases hbdeg : b.natDegree = 0
    · right
      rw [eq_C_of_natDegree_eq_zero hbdeg]
      exact isUnit_C.mpr (isUnit_iff_exists_inv.mpr ⟨_, by
        rw [mul_comm, leadingCoeff, hbdeg] at hlc; exact hlc⟩)
    exfalso
    rw [hab, Polynomial.map_mul, eval_mul, mul_eq_zero] at hy
    rcases hy with hy | hy
    · exact ha0 (hsmall a (by omega) hy)
    · exact hb0 (hsmall b (by omega) hy)

universe u

/-- **A single place at infinity gives geometric irreducibility.** -/
theorem geomIrr_of_wt (Fc' : BPoly ℚ) (hmon : (toB Fc').Monic)
    (hlen : (toB Fc').natDegree = Fc'.length - 1) (h : wtC Fc' = true) : GeomIrr.{u} Fc' := by
  intro K _ _
  simp only [wtC, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨hn0, ha0⟩, hcop⟩, hw⟩ := h
  set n := Fc'.length - 1 with hn
  set d := degC (Fc'.getD 0 []) with hd
  set φ := algebraMap ℚ K with hφ
  set F := (toB Fc').map (mapRingHom φ) with hFdef
  have hinj : Function.Injective (mapRingHom φ) := map_injective _ φ.injective
  have hFm : F.Monic := hmon.map _
  have hFn : F.natDegree = n := by rw [hFdef, natDegree_map_eq_of_injective hinj, hlen]
  have hcoeff : ∀ i, F.coeff i = (toPoly (Fc'.getD i [])).map φ := fun i ↦ by
    rw [hFdef, coeff_map, coeff_toB]; rfl
  have hnz : ∀ i, isZero (Fc'.getD i []) = false → toPoly (Fc'.getD i []) ≠ 0 := fun i hi h0 ↦ by
    rw [← isZero_iff] at h0; rw [h0] at hi; exact absurd hi (by simp)
  have hdegi : ∀ i, isZero (Fc'.getD i []) = false →
      (F.coeff i).natDegree = degC (Fc'.getD i []) := fun i hi ↦ by
    rw [hcoeff, natDegree_map_eq_of_injective φ.injective, degC_eq _ (hnz i hi)]
  have hF0 : F.coeff 0 ≠ 0 := by
    rw [hcoeff, Ne, Polynomial.map_eq_zero_iff φ.injective]; exact hnz 0 ha0
  have hd0 : (F.coeff 0).natDegree = d := hdegi 0 ha0
  have hw' : ∀ i, 0 < i → i < n → F.coeff i = 0 ∨ n * (F.coeff i).natDegree < d * (n - i) := by
    intro i hi hin
    rcases hw i hin with (h0 | h0) | h0
    · omega
    · left
      rw [hcoeff, (isZero_iff _).mp h0, Polynomial.map_zero]
    · by_cases hz : isZero (Fc'.getD i []) = true
      · left; rw [hcoeff, (isZero_iff _).mp hz, Polynomial.map_zero]
      · right
        rw [hdegi i (by simpa using hz)]; exact h0
  have hFd : 0 < F.natDegree := by rw [hFn]; exact hn0
  obtain ⟨y, hy⟩ := exists_root_std F hFm hFd
  have htr : Transcendental K (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K)) RatFunc.X) :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc K) _).injective).mpr
      RatFunc.transcendental_X
  have hroot : (F.map (aeval (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K))
      RatFunc.X)).toRingHom).eval y = 0 := by rw [map_aeval_std]; exact hy
  refine irreducible_of_no_small_factor (toAC K) F hFm hFd y hy fun G hG hGy ↦ ?_
  refine irr_of_weights _ y htr F hFm n d hFn hn0 hF0 hd0 hw' (Nat.coprime_iff_gcd_eq_one.mpr hcop)
    hroot G (by rw [← hFn]; exact hG) ?_
  rw [map_aeval_std]; exact hGy

lemma irr_ratFunc_of_wt (Fq : BPoly ℚ) (hmon : (toB Fq).Monic)
    (hlen : (toB Fq).natDegree = Fq.length - 1) (h : wtC Fq = true) :
    Irreducible ((toB Fq).map (algebraMap ℚ[X] (RatFunc ℚ))) := by
  have hQ := geomIrr_of_wt.{0} Fq hmon hlen h ℚ
  have hid : (toB Fq).map (mapRingHom (algebraMap ℚ ℚ)) = toB Fq := by
    rw [Algebra.algebraMap_self, mapRingHom_id, Polynomial.map_id]
  rw [hid] at hQ
  exact (hmon.irreducible_iff_irreducible_map_fraction_map).mp hQ

/-- **A base curve with one place at infinity is irreducible over the code field.** -/
theorem fKc_irr_wt (Fq : BPoly ℚ) (hmon : (toB Fq).Monic)
    (hlen : (toB Fq).natDegree = Fq.length - 1) (h : wtC Fq = true) :
    Irreducible (toPoly (fKc Fq)) :=
  fKc_irr_of_ratFunc Fq hmon (irr_ratFunc_of_wt Fq hmon hlen h)

/-- **Over a linear base, a `Q` with one place at infinity is irreducible over the code field.** -/
theorem qK_irr_linear_wt (c0 : CPoly ℚ) (Fq : BPoly ℚ) (hmon : (toB Fq).Monic)
    (hlen : (toB Fq).natDegree = Fq.length - 1) (h : wtC Fq = true) :
    haveI : Fact (Irreducible (toPoly (fKc [c0, [1]]))) := ⟨fKc_irr_linear c0⟩
    Irreducible (toPoly (qK [c0, [1]] (qOfB Fq))) :=
  qK_irr_linear_of_ratFunc c0 Fq hmon (irr_ratFunc_of_wt Fq hmon hlen h)

end Curves.MT
