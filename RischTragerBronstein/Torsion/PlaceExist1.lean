import RischTragerBronstein.Torsion.Conj
import RischTragerBronstein.Torsion.RamRoots

/-!
# Places above a point exist (1): the conjugation of roots

For the roots `rₖ = yₖ(T)` (`yₖ ∈ K⟦T⟧`) of `G(a + Tᴺ, Y)` and a primitive `N`-th root of unity
`ζ`, the substitution `T ↦ ζ T` permutes the roots (`conjPerm`). The minimal period `e` of a root
under this permutation divides `N`, the root only involves powers of `T^{N/e}`
(`coeff_eq_zero_of_period`), and it is `y(T^{N/e})` for the **place series**
`placeSer` of a root of `G(a + tᵉ, Y)` (`placeSer_root`); its conjugates are
`y((ζⁱT)^{N/e})`.
-/

open Polynomial HahnSeries

namespace Curves

open Differential LaurentSeries

section RotPow

variable {K : Type*} [Field K]

lemma rot_rot (ζ ζ' : K) (hζ : ζ ≠ 0) (hζ' : ζ' ≠ 0) (z : LaurentSeries K) :
    rot ζ hζ (rot ζ' hζ' z) = rot (ζ * ζ') (mul_ne_zero hζ hζ') z := by
  ext m
  simp only [rot_coeff, mul_zpow]
  ring

lemma rot_one (z : LaurentSeries K) : rot 1 one_ne_zero z = z := by
  ext m; simp

lemma rot_iterate (ζ : K) (hζ : ζ ≠ 0) (i : ℕ) (z : LaurentSeries K) :
    (rot ζ hζ)^[i] z = rot (ζ ^ i) (pow_ne_zero _ hζ) z := by
  induction i with
  | zero => simp [rot_one]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, rot_rot]
    congr 1
    ring_nf

end RotPow

section Perm

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- The data of a split fibre: `G(a + Tᴺ, Y) = ∏ (Y − yₖ(T))` with distinct power series roots. -/
structure SplitFibre (G : C[X][X]) (n : ℕ) where
  a : K
  N : ℕ
  hN : 0 < N
  y : Fin n → PowerSeries K
  inj : Function.Injective y
  split : G.map (branchSub N a) = ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K (y k)))

variable {G : C[X][X]} {n : ℕ}

namespace SplitFibre

variable (Φ : SplitFibre (K := K) G n) {ζ : K} (hζ : IsPrimitiveRoot ζ Φ.N)
include hζ

lemma ζ_ne_zero : ζ ≠ 0 := hζ.ne_zero Φ.hN.ne'

lemma exists_conj (k : Fin n) : ∃ l, rot ζ (Φ.ζ_ne_zero hζ) (ofPowerSeries ℤ K (Φ.y k)) =
    ofPowerSeries ℤ K (Φ.y l) := by
  have h := rot_root ζ (Φ.ζ_ne_zero hζ) Φ.N hζ.pow_eq_one Φ.a G (ofPowerSeries ℤ K (Φ.y k)) (by
    rw [Φ.split, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp))
  rw [Φ.split, eval_prod] at h
  obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp h
  exact ⟨l, by simpa [sub_eq_zero] using hl⟩

/-- The permutation of the roots induced by `T ↦ ζ T`. -/
noncomputable def conjPerm (k : Fin n) : Fin n := Classical.choose (Φ.exists_conj hζ k)

lemma conjPerm_spec (k : Fin n) : ofPowerSeries ℤ K (Φ.y (Φ.conjPerm hζ k)) =
    rot ζ (Φ.ζ_ne_zero hζ) (ofPowerSeries ℤ K (Φ.y k)) :=
  (Classical.choose_spec (Φ.exists_conj hζ k)).symm

lemma conjPerm_iterate (i : ℕ) (k : Fin n) : ofPowerSeries ℤ K (Φ.y ((Φ.conjPerm hζ)^[i] k)) =
    rot (ζ ^ i) (pow_ne_zero _ (Φ.ζ_ne_zero hζ)) (ofPowerSeries ℤ K (Φ.y k)) := by
  induction i with
  | zero => simp [rot_one]
  | succ i ih =>
    rw [Function.iterate_succ_apply', conjPerm_spec, ih, rot_rot]
    congr 1
    ring

lemma ofPS_injective_y : Function.Injective fun k ↦ ofPowerSeries ℤ K (Φ.y k) :=
  fun _ _ h ↦ Φ.inj (HahnSeries.ofPowerSeries_injective h)

lemma conjPerm_iterate_N (k : Fin n) : (Φ.conjPerm hζ)^[Φ.N] k = k := by
  apply Φ.ofPS_injective_y hζ
  show ofPowerSeries ℤ K (Φ.y _) = ofPowerSeries ℤ K (Φ.y k)
  rw [conjPerm_iterate]
  have : rot (ζ ^ Φ.N) (pow_ne_zero _ (Φ.ζ_ne_zero hζ)) = rot 1 one_ne_zero := by
    congr 1; exact hζ.pow_eq_one
  rw [this, rot_one]

lemma mem_periodicPts (k : Fin n) : k ∈ Function.periodicPts (Φ.conjPerm hζ) :=
  ⟨Φ.N, Φ.hN, Φ.conjPerm_iterate_N hζ k⟩

/-- The ramification index of the place of the root `k`. -/
noncomputable def period (k : Fin n) : ℕ := Function.minimalPeriod (Φ.conjPerm hζ) k

lemma period_pos (k : Fin n) : 0 < Φ.period hζ k :=
  Function.minimalPeriod_pos_of_mem_periodicPts (Φ.mem_periodicPts hζ k)

lemma period_dvd (k : Fin n) : Φ.period hζ k ∣ Φ.N :=
  Function.IsPeriodicPt.minimalPeriod_dvd (Φ.conjPerm_iterate_N hζ k)

lemma period_fix (k : Fin n) :
    rot (ζ ^ Φ.period hζ k) (pow_ne_zero _ (Φ.ζ_ne_zero hζ)) (ofPowerSeries ℤ K (Φ.y k)) =
      ofPowerSeries ℤ K (Φ.y k) := by
  rw [← conjPerm_iterate]
  congr 2
  exact Function.iterate_minimalPeriod

/-- The index `s = N/e`. -/
noncomputable def sIdx (k : Fin n) : ℕ := Φ.N / Φ.period hζ k

lemma sIdx_mul (k : Fin n) : Φ.sIdx hζ k * Φ.period hζ k = Φ.N :=
  Nat.div_mul_cancel (Φ.period_dvd hζ k)

lemma sIdx_pos (k : Fin n) : 0 < Φ.sIdx hζ k :=
  Nat.pos_of_ne_zero fun h ↦ by
    have := Φ.sIdx_mul hζ k
    rw [h, zero_mul] at this
    exact Φ.hN.ne' this.symm

/-- **The root only involves the powers of `T^{N/e}`.** -/
lemma coeff_eq_zero_of_period (k : Fin n) (m : ℕ) (hm : ¬ Φ.sIdx hζ k ∣ m) :
    PowerSeries.coeff m (Φ.y k) = 0 := by
  have h := congrArg (fun z ↦ z.coeff (m : ℤ)) (Φ.period_fix hζ k)
  simp only [rot_coeff, coeff_ofPS] at h
  rw [if_pos (by positivity), Int.toNat_natCast] at h
  by_contra h0
  have h1 : (ζ ^ Φ.period hζ k) ^ (m : ℤ) = 1 := by
    have := mul_right_cancel₀ h0 (h.trans (one_mul _).symm)
    exact this
  rw [zpow_natCast, ← pow_mul] at h1
  have h2 := (hζ.pow_eq_one_iff_dvd _).mp h1
  apply hm
  have h3 : Φ.sIdx hζ k * Φ.period hζ k ∣ Φ.period hζ k * m := by rw [Φ.sIdx_mul]; exact h2
  rw [mul_comm (Φ.period hζ k)] at h3
  exact Nat.dvd_of_mul_dvd_mul_right (Φ.period_pos hζ k) h3

/-- The place series `y(t)` with `yₖ(T) = y(T^{N/e})`. -/
noncomputable def placeSer (k : Fin n) : PowerSeries K :=
  PowerSeries.mk fun j ↦ PowerSeries.coeff (Φ.sIdx hζ k * j) (Φ.y k)

lemma y_eq_conjPS (k : Fin n) : Φ.y k = conjPS 1 (Φ.sIdx hζ k) (Φ.placeSer hζ k) := by
  ext m
  rw [coeff_conjPS]
  split_ifs with hm
  · rw [one_pow, one_mul, placeSer, PowerSeries.coeff_mk, Nat.mul_div_cancel' hm]
  · exact Φ.coeff_eq_zero_of_period hζ k m hm

lemma ofPS_y_eq_lsub (k : Fin n) : ofPowerSeries ℤ K (Φ.y k) =
    lsub (Φ.sIdx hζ k) (Φ.sIdx_pos hζ k) (ofPowerSeries ℤ K (Φ.placeSer hζ k)) := by
  rw [Φ.y_eq_conjPS hζ k, ofPS_conjPS 1 one_ne_zero _ (Φ.sIdx_pos hζ k), rot_one]

/-- **The place series is a root at level `e`.** -/
lemma placeSer_root (k : Fin n) :
    (G.map (branchSub (Φ.period hζ k) Φ.a)).eval (ofPowerSeries ℤ K (Φ.placeSer hζ k)) = 0 := by
  have hs := Φ.sIdx_pos hζ k
  apply lsub_injective (Φ.sIdx hζ k) hs
  rw [map_zero, ← eval₂_at_apply, ← eval_map, Polynomial.map_map, lsub_comp_branchSub,
    ← Φ.ofPS_y_eq_lsub hζ k, mul_comm, Φ.sIdx_mul hζ k, Φ.split, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)

end SplitFibre

end Perm

end Curves
