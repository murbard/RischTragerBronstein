import RischTragerBronstein.Torsion.IntBasis
import RischTragerBronstein.Torsion.GJets
import Mathlib.RingTheory.Henselian
import RischTragerBronstein.Algebraic.EllDecideQ

/-!
# Unramified branches by Hensel's lemma (any characteristic)

Above a point `a` whose fibre `F(a, Y)` has `n` distinct roots `b_k`:

* `psSub N a`: `P ↦ P(a + Tᴺ)` into `K⟦T⟧` (so `branchSub N a = ofPowerSeries ∘ psSub N a`);
* `exists_root_lift`: each simple root `b` lifts to a root `Y ∈ K⟦T⟧` of `F(a + T, Y)`;
* `split_unramified`: `F(a + T, Y) = ∏ₖ (Y − Yₖ)`;
* `lowerBd_wE_iff_vanish`: along the branch through `(a, b)`, `W(x, y)` has order `≥ m` iff `W`
  vanishes to order `m` at `(a, b)` in the sense of jets (`VanishAtG`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section PS

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- `P ↦ P(a + Tᴺ)` into `K⟦T⟧`. -/
noncomputable def psSub (N : ℕ) (a : K) : C[X] →+* PowerSeries K :=
  (Polynomial.coeToPowerSeries.ringHom (R := K)).comp
    ((Polynomial.compRingHom (Polynomial.C a + X ^ N)).comp (Polynomial.mapRingHom (algebraMap C K)))

lemma branchSub_eq_psSub (N : ℕ) (a : K) (P : C[X]) :
    branchSub N a P = ofPowerSeries ℤ K (psSub N a P) := rfl

/-- The bivariate polynomial `F(a + T, Y)` over `K⟦T⟧`. -/
noncomputable def fibrePS (F : C[X][X]) (a : K) : (PowerSeries K)[X] := F.map (psSub 1 a)

lemma coeff_zero_psSub (a : K) (P : C[X]) :
    PowerSeries.constantCoeff (psSub (C := C) 1 a P) = (P.map (algebraMap C K)).eval a := by
  rw [psSub, RingHom.comp_apply, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, coeff_zero_eq_eval_zero,
    coe_compRingHom, coe_mapRingHom, eval_comp]
  simp

/-- The constant coefficient of `F(a + T, Y)` evaluated at a constant: `F(a, b)`. -/
lemma fibrePS_eval_const (F : C[X][X]) (a b : K) :
    PowerSeries.constantCoeff ((fibrePS F a).eval (PowerSeries.C b)) =
      ((F.map (mapRingHom (algebraMap C K))).map (evalRingHom a)).eval b := by
  simp only [fibrePS, eval_map, Polynomial.eval₂_eq_sum_range, map_sum, map_mul, map_pow,
    PowerSeries.constantCoeff_C, Polynomial.map_map]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_zero_psSub]
  rfl

end PS

section Lift

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- The fibre polynomial `F(a, Y) ∈ K[Y]`. -/
noncomputable def fibreAt (F : C[X][X]) (a : K) : K[X] :=
  (F.map (mapRingHom (algebraMap C K))).map (evalRingHom a)

lemma derivative_fibrePS (F : C[X][X]) (a : K) :
    derivative (fibrePS F a) = fibrePS (derivative F) a := by
  rw [fibrePS, fibrePS, Polynomial.derivative_map]

/-- **Hensel lifting of a simple root of the fibre.** -/
theorem exists_root_lift (F : C[X][X]) (hF : F.Monic) (a b : K) (hb : (fibreAt F a).eval b = 0)
    (hb' : (fibreAt (derivative F) a).eval b ≠ 0) :
    ∃ Y : PowerSeries K, (fibrePS F a).eval Y = 0 ∧ PowerSeries.constantCoeff Y = b := by
  set f := fibrePS F a with hf
  have hmon : f.Monic := hF.map _
  have h1 : f.eval (PowerSeries.C b) ∈ Ideal.span {(PowerSeries.X : PowerSeries K)} := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, hf, fibrePS_eval_const]
    exact hb
  have h2 : IsUnit (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K)})
      (f.derivative.eval (PowerSeries.C b))) := by
    refine IsUnit.map _ ?_
    rw [PowerSeries.isUnit_iff_constantCoeff, hf, derivative_fibrePS, fibrePS_eval_const]
    exact Ne.isUnit hb'
  obtain ⟨Y, hY, hYa⟩ := HenselianRing.is_henselian f hmon (PowerSeries.C b) h1 h2
  refine ⟨Y, hY, ?_⟩
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, sub_eq_zero] at hYa
  simpa using hYa

/-- **Unramified splitting**: above a point with `n` distinct simple roots, `F(a + T, Y)` splits
into `n` power-series roots. -/
theorem split_unramified (F : C[X][X]) (hF : F.Monic) (a : K) (b : Fin F.natDegree → K)
    (hbi : Function.Injective b) (hb : ∀ k, (fibreAt F a).eval (b k) = 0)
    (hb' : ∀ k, (fibreAt (derivative F) a).eval (b k) ≠ 0) :
    ∃ Y : Fin F.natDegree → PowerSeries K, (∀ k, (fibrePS F a).eval (Y k) = 0 ∧
      PowerSeries.constantCoeff (Y k) = b k) ∧
      F.map (branchSub 1 a) = ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K (Y k))) := by
  classical
  choose Y hY using fun k ↦ exists_root_lift F hF a (b k) (hb k) (hb' k)
  refine ⟨Y, hY, ?_⟩
  set G := F.map (branchSub (K := K) 1 a) with hG
  have hGmap : G = (fibrePS F a).map (ofPowerSeries ℤ K) := by
    rw [hG, fibrePS, Polynomial.map_map]; rfl
  have hGm : G.Monic := hF.map _
  have hGd : G.natDegree = F.natDegree := hF.natDegree_map _
  set l := List.ofFn fun k ↦ ofPowerSeries ℤ K (Y k) with hl
  have hinj : Function.Injective fun k ↦ ofPowerSeries ℤ K (Y k) := by
    intro i j h
    have h1 := HahnSeries.ofPowerSeries_injective h
    have h2 := congrArg PowerSeries.constantCoeff h1
    rw [(hY i).2, (hY j).2] at h2
    exact hbi h2
  have hnd : l.Nodup := List.nodup_ofFn.mpr hinj
  have hroot : ∀ z ∈ l, G.eval z = 0 := by
    intro z hz
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hz
    rw [hGmap, eval_map, Polynomial.eval₂_hom, (hY k).1, map_zero]
  have h := EllQuad.split_of_hasRoots hGm.ne_zero hnd (by rw [hGd, List.length_ofFn]) hroot
  rw [hGm.leadingCoeff, map_one, one_mul] at h
  rw [h, hl, List.map_ofFn, List.prod_ofFn]
  rfl

end Lift

section Jets

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

lemma lowerBd_ofPS_iff (s : PowerSeries K) (m : ℕ) :
    LowerBd (ofPowerSeries ℤ K s) m ↔ (PowerSeries.X : PowerSeries K) ^ m ∣ s := by
  rw [PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h d hd
    have := h d (by exact_mod_cast hd)
    rwa [LaurentSeries.coeff_ofPS, if_pos (by positivity), Int.toNat_natCast] at this
  · intro h i hi
    rw [LaurentSeries.coeff_ofPS]
    split_ifs with h0
    · exact h _ (by omega)
    · rfl

/-- The jet of `W` along a polynomial `V`, as a power series. -/
lemma coe_jetN (W : C[X][X]) (a : K) (V : K[X]) :
    ((GTors.jetN' (W.map (mapRingHom (algebraMap C K))) a V : K[X]) : PowerSeries K) =
      (W.map (psSub 1 a)).eval (V : PowerSeries K) := by
  rw [GTors.jetN', Sup.jetN, eval_map, ← Polynomial.coeToPowerSeries.ringHom_apply,
    hom_eval₂, eval₂_map, eval_map]
  congr 1
  refine RingHom.ext fun P ↦ ?_
  simp only [RingHom.comp_apply, psSub, coe_compRingHom, coe_mapRingHom, pow_one,
    add_comm (X : K[X])]

lemma X_pow_dvd_coe_iff (P : K[X]) (m : ℕ) :
    (PowerSeries.X : PowerSeries K) ^ m ∣ (P : PowerSeries K) ↔ (X : K[X]) ^ m ∣ P := by
  rw [PowerSeries.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  simp only [Polynomial.coeff_coe]

lemma X_pow_dvd_sub_trunc (Y : PowerSeries K) (m : ℕ) :
    (PowerSeries.X : PowerSeries K) ^ m ∣ Y - (PowerSeries.trunc m Y : PowerSeries K) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro d hd
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hd, sub_self]

/-- **Orders along an unramified branch are jet vanishing orders.** -/
theorem lowerBd_iff_vanishAtG (F : C[X][X]) (a b : K) (Y : PowerSeries K)
    (hY : (fibrePS F a).eval Y = 0) (hYb : PowerSeries.constantCoeff Y = b)
    (hb' : (fibreAt (derivative F) a).eval b ≠ 0) (W : C[X][X]) (m : ℕ) :
    LowerBd (ofPowerSeries ℤ K ((W.map (psSub 1 a)).eval Y)) m ↔
      GTors.VanishAtG (F.map (mapRingHom (algebraMap C K))) (W.map (mapRingHom (algebraMap C K)))
        a b m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨fun _ ↦ ⟨Polynomial.C b, ⟨by simp, by simp⟩, by simp⟩, fun _ ↦ ?_⟩
    have := lowerBd_ofPS ((W.map (psSub 1 a)).eval Y)
    exact_mod_cast this
  set V := PowerSeries.trunc m Y with hV
  have hV0 : V.coeff 0 = b := by
    rw [hV, PowerSeries.coeff_trunc, if_pos hm, PowerSeries.coeff_zero_eq_constantCoeff_apply, hYb]
  have hcong : ∀ P : C[X][X], (PowerSeries.X : PowerSeries K) ^ m ∣
      (P.map (psSub 1 a)).eval Y - (P.map (psSub 1 a)).eval (V : PowerSeries K) :=
    fun P ↦ (X_pow_dvd_sub_trunc Y m).trans (sub_dvd_eval_sub _ _ _)
  have hbr : GTors.IsBranchG (F.map (mapRingHom (algebraMap C K))) a b m V := by
    refine ⟨hV0, ?_⟩
    rw [← X_pow_dvd_coe_iff, show (Sup.jetN (F.map (mapRingHom (algebraMap C K))) a V : PowerSeries K)
      = _ from coe_jetN F a V]
    have := hcong F
    rw [show (F.map (psSub 1 a)).eval Y = 0 from hY, zero_sub, dvd_neg] at this
    exact this
  have hu : IsUnit (Sup.evalW (derivative (F.map (mapRingHom (algebraMap C K)))) a b) := by
    refine Ne.isUnit ?_
    rw [Sup.evalW, Polynomial.derivative_map]
    exact hb'
  rw [GTors.vanishAtG_iff hu hbr, ← X_pow_dvd_coe_iff, lowerBd_ofPS_iff,
    show (Sup.jetN (W.map (mapRingHom (algebraMap C K))) a V : PowerSeries K) = _ from coe_jetN W a V]
  constructor
  · intro h
    have := dvd_sub h (hcong W)
    rwa [sub_sub_cancel] at this
  · intro h
    have := dvd_add h (hcong W)
    rwa [add_sub_cancel] at this

end Jets

end Curves
