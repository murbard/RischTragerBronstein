import RischTragerBronstein.Torsion.PlaceLocal3
import RischTragerBronstein.Torsion.RamRes

/-!
# Residues at the places of a split fibre

For the integrand `f` of a valid problem over the curve `S` (with `S.F` the image of `P.Fc`) and a
split fibre `Φ` above `x = a` (level `N`):

* `resAlong`: the residue of `f dx` along a root `Y` of `F(a + Tᴺ, Y)`;
* `resAlong_conj`: it is constant on the orbits of `T ↦ ζ T` (`embG_rot`, `res_rot_branch`);
* **`resFin_locPlaces`**: the computed residue `resFin` along the approximations of the local place
  data is the residue along the corresponding root (`resFin_sem`, `lp_approx`), given the
  side conditions on the order of `D`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

section Res

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- The residue of `f dx` along a root at `x = a + Tᴺ`. -/
noncomputable def resAlong (N : ℕ) (hN : 0 < N) (a : C) (Y : PowerSeries C)
    (hY : (S.F.map (branchSub (C := C) (K := C) N a)).eval (ofPowerSeries ℤ C Y) = 0)
    (f : C⟮S.x⟯⟮S.y⟯) : C :=
  LaurentSeries.res (S.embG (branchSub N a) (branchSub_injective N hN a) (ofPowerSeries ℤ C Y) hY f *
    LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : C)))

lemma resAlong_congr (N : ℕ) (hN : 0 < N) (a : C) (Y Y' : PowerSeries C) (hYY : Y = Y')
    (hY : (S.F.map (branchSub (C := C) (K := C) N a)).eval (ofPowerSeries ℤ C Y) = 0)
    (hY' : (S.F.map (branchSub (C := C) (K := C) N a)).eval (ofPowerSeries ℤ C Y') = 0)
    (f : C⟮S.x⟯⟮S.y⟯) : S.resAlong N hN a Y hY f = S.resAlong N hN a Y' hY' f := by
  subst hYY; rfl

lemma resAlong_a (N : ℕ) (hN : 0 < N) (a a' : C) (h : a = a') (Y : PowerSeries C)
    (hY : (S.F.map (branchSub (C := C) (K := C) N a)).eval (ofPowerSeries ℤ C Y) = 0)
    (hY' : (S.F.map (branchSub (C := C) (K := C) N a')).eval (ofPowerSeries ℤ C Y) = 0)
    (f : C⟮S.x⟯⟮S.y⟯) : S.resAlong N hN a Y hY f = S.resAlong N hN a' Y hY' f := by
  subst h; rfl

lemma embG_congr_root (g : C[X] →+* LaurentSeries C) (hg : Function.Injective g)
    (r r' : LaurentSeries C) (h : r = r') (hr : (S.F.map g).eval r = 0)
    (hr' : (S.F.map g).eval r' = 0) (f : C⟮S.x⟯⟮S.y⟯) : S.embG g hg r hr f = S.embG g hg r' hr' f := by
  subst h; rfl

/-- **Residues are constant on conjugate roots.** -/
lemma resAlong_rot (N : ℕ) (hN : 0 < N) (a : C) (ζ : C) (hζ : ζ ≠ 0) (hζN : ζ ^ N = 1)
    (Y Y' : PowerSeries C) (hYY : ofPowerSeries ℤ C Y' = rot ζ hζ (ofPowerSeries ℤ C Y))
    (hY : (S.F.map (branchSub (C := C) (K := C) N a)).eval (ofPowerSeries ℤ C Y) = 0)
    (hY' : (S.F.map (branchSub (C := C) (K := C) N a)).eval (ofPowerSeries ℤ C Y') = 0)
    (f : C⟮S.x⟯⟮S.y⟯) : S.resAlong N hN a Y' hY' f = S.resAlong N hN a Y hY f := by
  unfold resAlong
  have h1 : S.embG (branchSub N a) (branchSub_injective N hN a) (ofPowerSeries ℤ C Y') hY' f =
      S.embG (branchSub N a) (branchSub_injective N hN a) (rot ζ hζ (ofPowerSeries ℤ C Y))
        (rot_root ζ hζ N hζN a S.F _ hY) f :=
    S.embG_congr_root _ _ _ _ hYY _ _ f
  rw [h1, S.embG_rot ζ hζ N hN hζN a _ hY f, res_rot_branch ζ hζ N hN hζN a]

end CurveData

end Res

section Fibre

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) {n : ℕ}
  (Φ : SplitFibre (C := C) (K := C) ((toB P.Fc).map (mapRingHom ψ)) n) {ζ : C}
  (hζ : IsPrimitiveRoot ζ Φ.N)

include hSF in
lemma SplitFibre.root_S (k : Fin n) :
    (S.F.map (branchSub (C := C) (K := C) Φ.N Φ.a)).eval (ofPowerSeries ℤ C (Φ.y k)) = 0 := by
  rw [hSF, Φ.split, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)

include hSF in
/-- **The residue is constant on the orbit of a root.** -/
lemma SplitFibre.resAlong_rep (f : C⟮S.x⟯⟮S.y⟯) (k : Fin n) :
    S.resAlong Φ.N Φ.hN Φ.a (Φ.y k) (Φ.root_S S P hSF k) f =
      S.resAlong Φ.N Φ.hN Φ.a (Φ.y (Φ.rep hζ k)) (Φ.root_S S P hSF _) f := by
  obtain ⟨i, hi⟩ := Φ.rep_mem hζ k
  have h := Φ.conjPerm_iterate hζ i (Φ.rep hζ k)
  rw [hi] at h
  have hz : ζ ^ i ≠ 0 := pow_ne_zero _ (Φ.ζ_ne_zero hζ)
  have hzN : (ζ ^ i) ^ Φ.N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine S.resAlong_rot Φ.N Φ.hN Φ.a (ζ ^ i) hz hzN _ _ ?_ _ _ f
  rw [h]

include hSF in
/-- **The computed residues of the local place data.** -/
theorem SplitFibre.resFin_locPlaces (hV : P.ValidFacts) {α : F} (hα : ψ α = Φ.a) (tx : ℕ)
    (pre : C → F) {ζF : F} (Γf : Fin n → ℕ) (hζF : ψ ζF = ζ)
    (hpre : ∀ π : Fin n, ∀ i < Φ.bnd hζ hα tx, ψ (pre (PowerSeries.coeff i (Φ.placeSer hζ π))) =
      PowerSeries.coeff i (Φ.placeSer hζ π))
    (hμ : P.mufFin α Φ.N < (Φ.tpF + tx) + Φ.N) (hQ : P.mufFin α Φ.N < (P.QfFin α Φ.N).length)
    (k : Fin n) :
    ψ (P.resFin α ⟨Φ.N, [], Φ.tpF + tx⟩
      (conjC ((Φ.locPlaces hζ hα tx pre ζF Γf).ζ k) ((Φ.locPlaces hζ hα tx pre ζF Γf).s k)
        ((Φ.locPlaces hζ hα tx pre ζF Γf).y ((Φ.locPlaces hζ hα tx pre ζF Γf).idx k)))) =
      S.resAlong Φ.N Φ.hN Φ.a (Φ.y k) (Φ.root_S S P hSF k) (S.fE P ψ) := by
  have hY : (S.F.map (branchSub (C := C) (K := C) Φ.N (algebraMap C C (ψ α)))).eval
      (ofPowerSeries ℤ C (Φ.y k)) = 0 := by
    rw [Algebra.algebraMap_self, RingHom.id_apply, hα]; exact Φ.root_S S P hSF k
  have h := S.resFin_sem (K := C) P ψ hSF α ⟨Φ.N, [], Φ.tpF + tx⟩ Φ.hN (Φ.y k) hY _
    (by rw [Algebra.algebraMap_self, RingHom.id_comp]
        exact Φ.lp_approx hζ hα tx Γf hζF hpre k) hμ hQ (S.fE P ψ) (S.fE_spec P ψ hV)
  rw [S.resAlong_a Φ.N Φ.hN Φ.a (algebraMap C C (ψ α)) (by rw [Algebra.algebraMap_self,
    RingHom.id_apply, hα]) (Φ.y k) (Φ.root_S S P hSF k) hY (S.fE P ψ)]
  exact h.symm

include hSF in
/-- **The fibre sum of residues over the places.** -/
lemma SplitFibre.sum_resAlong (f : C⟮S.x⟯⟮S.y⟯) :
    ((Φ.N : C))⁻¹ * ∑ k, S.resAlong Φ.N Φ.hN Φ.a (Φ.y k) (Φ.root_S S P hSF k) f =
      ∑ π ∈ Finset.univ.filter (fun π ↦ Φ.rep hζ π = π),
        S.resAlong Φ.N Φ.hN Φ.a (Φ.y π) (Φ.root_S S P hSF π) f / (Φ.sIdx hζ π : C) := by
  classical
  rw [Finset.sum_congr rfl fun k _ ↦ Φ.resAlong_rep S P hSF hζ f k]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Φ.rep hζ)
    (t := Finset.univ.filter fun π ↦ Φ.rep hζ π = π)
    (fun k _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, Φ.rep_rep hζ k⟩), Finset.mul_sum]
  refine Finset.sum_congr rfl fun π hπ ↦ ?_
  have hπ' := (Finset.mem_filter.mp hπ).2
  rw [Finset.sum_congr rfl fun k hk ↦ by
    rw [S.resAlong_congr Φ.N Φ.hN Φ.a _ _ (congrArg Φ.y (Finset.mem_filter.mp hk).2) _
      (Φ.root_S S P hSF π)]]
  rw [Finset.sum_const, nsmul_eq_mul, Φ.card_orbit hζ π hπ']
  have hN : (Φ.N : C) = (Φ.sIdx hζ π : C) * (Φ.period hζ π : C) := by
    rw [← Nat.cast_mul, Φ.sIdx_mul hζ]
  have hs : (Φ.sIdx hζ π : C) ≠ 0 := by exact_mod_cast (Φ.sIdx_pos hζ π).ne'
  have hp : (Φ.period hζ π : C) ≠ 0 := by exact_mod_cast (Φ.period_pos hζ π).ne'
  rw [hN]
  field_simp

end Fibre

end Curves
