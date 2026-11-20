import RischTragerBronstein.Mixed.NKResInf
import RischTragerBronstein.Torsion.HenselBranch
import RischTragerBronstein.Mixed.NKMultiData

/-!
# Split places at infinity by Hensel's lemma

For `P = Yⁿ + ∑ aᵢ(x) Yⁱ` with `deg aᵢ ≤ (n − i) s`, the inverted polynomial
`Q(T, Θ) = T^{ns} P(1/T, Θ/Tˢ)` (`invPS`) has coefficients `reflect ((n − i) s) aᵢ`. A power-series
root `Θ` of `Q(T, ·)` gives the root `Θ T⁻ˢ` of `P` along `x = T⁻¹` (`inv_root`); if `Q(0, ·)` has
`n` distinct simple roots, `P` splits along `x = T⁻¹` (`split_inf_inv`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Inv

variable {C K : Type*} [Field C] [CharZero C] [Field K] [CharZero K] [Algebra C K] [Differential C]
  [Differential K]

/-- `Q(T, Θ) = T^{ns} P(1/T, Θ/Tˢ)`. -/
noncomputable def invPS (n s : ℕ) (P : C[X][X]) : C[X][X] :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (reflect ((n - i) * s) (P.coeff i)) * X ^ i

lemma coeff_invPS (n s : ℕ) (P : C[X][X]) (i : ℕ) :
    (invPS n s P).coeff i = if i ≤ n then reflect ((n - i) * s) (P.coeff i) else 0 := by
  unfold invPS
  rw [finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- `x ↦ T⁻¹` is `T ↦ T` after reflecting, times `T^{−d}`. -/
lemma infSub_one_reflect (d : ℕ) (a : C[X]) (ha : a.natDegree ≤ d) :
    infSub (K := K) 1 a = branchSub 1 (0 : K) (reflect d a) * single (-(d : ℤ)) 1 := by
  set i : C →+* LaurentSeries K := (HahnSeries.C).comp (algebraMap C K) with hi
  set x : LaurentSeries K := single (-1 : ℤ) 1 with hx
  let _ : Invertible x := ⟨single (1 : ℤ) 1, by
    rw [hx, HahnSeries.single_mul_single]; simp, by rw [hx, HahnSeries.single_mul_single]; simp⟩
  have h := eval₂_reflect_mul_pow i x d a ha
  have e1 : infSub (K := K) 1 a = eval₂ i x a := by
    rw [infSub, coe_eval₂RingHom]; rfl
  have e2 : branchSub 1 (0 : K) (reflect d a) = eval₂ i (⅟x) (reflect d a) := by
    rw [SuperData.branchSub_eq_subst, substHom_apply, aeval_def, eval₂_map]
    congr 1
    · ext c; simp [hi, HahnSeries.algebraMap_apply']
    · show HahnSeries.C (0 : K) + single ((1 : ℕ) : ℤ) 1 = single (1 : ℤ) 1
      simp
  have e3 : x ^ d = single (-(d : ℤ)) 1 := by
    rw [hx, HahnSeries.single_pow]; simp
  rw [e1, e2, ← e3, h]

/-- **A root of the inverted polynomial gives a root along `x = T⁻¹`.** -/
theorem inv_root (P : C[X][X]) (n s : ℕ) (hn : P.natDegree = n)
    (hdeg : ∀ i ≤ n, (P.coeff i).natDegree ≤ (n - i) * s) (Y : LaurentSeries K)
    (hY : ((invPS n s P).map (branchSub 1 (0 : K))).eval Y = 0) :
    (P.map (infSub (K := K) 1)).eval (Y * single (-(s : ℤ)) 1) = 0 := by
  have hsum : (P.map (infSub (K := K) 1)).eval (Y * single (-(s : ℤ)) 1) =
      single (-((n * s : ℕ) : ℤ)) 1 * ((invPS n s P).map (branchSub 1 (0 : K))).eval Y := by
    rw [eval_map, eval_map, eval₂_eq_sum_range' (n := n + 1) _ (by omega),
      eval₂_eq_sum_range' (n := n + 1) _ (by
        refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_) (Nat.lt_succ_self n)
        refine (natDegree_C_mul_le _ _).trans ?_
        rw [natDegree_X_pow]; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [coeff_invPS, if_pos hi', infSub_one_reflect ((n - i) * s) _ (hdeg i hi'), mul_pow,
      HahnSeries.single_pow]
    have e : ((n - i) * s : ℕ) + (s * i : ℕ) = n * s := by
      rw [show s * i = i * s by ring, ← add_mul, Nat.sub_add_cancel hi']
    have hsing : single (-(((n - i) * s : ℕ) : ℤ)) (1 : K) * single (i • -(s : ℤ)) (1 ^ i) =
        single (-((n * s : ℕ) : ℤ)) 1 := by
      rw [HahnSeries.single_mul_single, one_pow, mul_one]
      congr 1
      rw [← e]; push_cast; ring
    rw [← hsing]
    ring
  rw [hsum, hY, mul_zero]

lemma invPS_monic (P : C[X][X]) (n s : ℕ) (hm : P.Monic) (hn : P.natDegree = n) :
    (invPS n s P).Monic ∧ (invPS n s P).natDegree = n := by
  have hle : (invPS n s P).natDegree ≤ n := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_invPS, if_neg (by exact_mod_cast not_le.mpr hi)]
  have hc : (invPS n s P).coeff n = 1 := by
    rw [coeff_invPS, if_pos le_rfl, Nat.sub_self, zero_mul, ← hn]
    rw [hm.coeff_natDegree, ← map_one Polynomial.C, reflect_C, pow_zero, mul_one, map_one]
  have hdeg : (invPS n s P).natDegree = n :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero))
  refine ⟨?_, hdeg⟩
  rw [Monic, Polynomial.leadingCoeff, hdeg, hc]

/-- **Split places at infinity**: if the fibre at `T = 0` of the inverted polynomial has `n`
distinct simple roots, `P` splits along `x = T⁻¹` into the roots `Θₖ T⁻ˢ`. -/
theorem split_inf_inv (P : C[X][X]) (n s : ℕ) (hm : P.Monic) (hn : P.natDegree = n)
    (hdeg : ∀ i ≤ n, (P.coeff i).natDegree ≤ (n - i) * s) (γ : Fin n → K)
    (hγi : Function.Injective γ) (hγ : ∀ k, (fibreAt (invPS n s P) 0).eval (γ k) = 0)
    (hγ' : ∀ k, (fibreAt (derivative (invPS n s P)) 0).eval (γ k) ≠ 0) :
    ∃ Θ : Fin n → PowerSeries K, (∀ k, (fibrePS (invPS n s P) 0).eval (Θ k) = 0 ∧
      PowerSeries.constantCoeff (Θ k) = γ k) ∧
      P.map (infSub (K := K) 1) =
        ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K (Θ k) * single (-(s : ℤ)) 1)) := by
  classical
  obtain ⟨hQm, hQn⟩ := invPS_monic P n s hm hn
  obtain ⟨Θ, hΘ, -⟩ := split_unramified (invPS n s P) hQm 0 (fun k ↦ γ (Fin.cast hQn k))
    (fun i j h ↦ by simpa using hγi h) (fun k ↦ hγ _) (fun k ↦ hγ' _)
  set Θ' : Fin n → PowerSeries K := fun k ↦ Θ (Fin.cast hQn.symm k) with hΘ'
  have hΘ'p : ∀ k, (fibrePS (invPS n s P) 0).eval (Θ' k) = 0 ∧
      PowerSeries.constantCoeff (Θ' k) = γ k := fun k ↦ by
    refine ⟨(hΘ _).1, ?_⟩
    rw [hΘ', (hΘ _).2]; simp
  refine ⟨Θ', hΘ'p, ?_⟩
  set G := P.map (infSub (K := K) 1) with hG
  have hGm : G.Monic := hm.map _
  have hGd : G.natDegree = n := by rw [hG, hm.natDegree_map, hn]
  set l := List.ofFn fun k ↦ ofPowerSeries ℤ K (Θ' k) * single (-(s : ℤ)) 1 with hl
  have hinj : Function.Injective fun k ↦ ofPowerSeries ℤ K (Θ' k) * single (-(s : ℤ)) (1 : K) := by
    intro i j h
    have hs : single (-(s : ℤ)) (1 : K) ≠ 0 := by simp
    have h1 := HahnSeries.ofPowerSeries_injective (mul_right_cancel₀ hs h)
    have h2 := congrArg PowerSeries.constantCoeff h1
    rw [(hΘ'p i).2, (hΘ'p j).2] at h2
    exact hγi h2
  have hnd : l.Nodup := List.nodup_ofFn.mpr hinj
  have hroot : ∀ z ∈ l, G.eval z = 0 := by
    intro z hz
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hz
    refine inv_root P n s hn hdeg _ ?_
    have := (hΘ'p k).1
    rw [fibrePS] at this
    have e : (invPS n s P).map (branchSub 1 (0 : K)) =
        ((invPS n s P).map (psSub 1 (0 : K))).map (ofPowerSeries ℤ K) := by
      rw [Polynomial.map_map]; rfl
    rw [e, eval_map, Polynomial.eval₂_hom, this, map_zero]
  have h := EllQuad.split_of_hasRoots hGm.ne_zero hnd (by rw [hGd, List.length_ofFn]) hroot
  rw [hGm.leadingCoeff, map_one, one_mul] at h
  rw [h, hl, List.map_ofFn, List.prod_ofFn]
  rfl

end Inv

section Trunc

variable {K : Type*} [Field K]

/-- **Hensel uniqueness for truncations**: a power-series root `Θ` and an approximate root `Θ̃`
(`Q(Θ̃) ≡ 0 mod Tᴹ`) with the same constant term and `Q′(Θ̃)` a unit agree modulo `Tᴹ`. -/
theorem hensel_trunc (Q : (PowerSeries K)[X]) (Θ Θt : PowerSeries K) (hQ : Q.eval Θ = 0)
    (hc : PowerSeries.constantCoeff Θ = PowerSeries.constantCoeff Θt)
    (hu : PowerSeries.constantCoeff ((derivative Q).eval Θt) ≠ 0) (M : ℕ)
    (hM : (PowerSeries.X : PowerSeries K) ^ M ∣ Q.eval Θt) :
    (PowerSeries.X : PowerSeries K) ^ M ∣ Θ - Θt := by
  set δ := Θ - Θt with hδ
  have hunit : IsUnit ((derivative Q).eval Θt) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; exact Ne.isUnit hu
  obtain ⟨h, hh⟩ := Q.binomExpansion Θt δ
  rw [hδ, add_sub_cancel, hQ] at hh
  rw [← hδ] at hh
  have step : ∀ k, 1 ≤ k → k < M → (PowerSeries.X : PowerSeries K) ^ k ∣ δ →
      (PowerSeries.X : PowerSeries K) ^ (k + 1) ∣ δ := by
    intro k hk hkM hdk
    have h1 : (PowerSeries.X : PowerSeries K) ^ (k + 1) ∣ Q.eval Θt :=
      (pow_dvd_pow _ (by omega)).trans hM
    have h2 : (PowerSeries.X : PowerSeries K) ^ (k + 1) ∣ h * δ ^ 2 := by
      refine Dvd.dvd.mul_left ?_ _
      have : (PowerSeries.X : PowerSeries K) ^ (k + k) ∣ δ ^ 2 := by
        rw [pow_add, sq]; exact mul_dvd_mul hdk hdk
      exact (pow_dvd_pow _ (by omega)).trans this
    have h3 : (PowerSeries.X : PowerSeries K) ^ (k + 1) ∣ (derivative Q).eval Θt * δ := by
      have e : (derivative Q).eval Θt * δ = -(Q.eval Θt) - h * δ ^ 2 := by
        linear_combination -hh
      rw [e]
      exact dvd_sub (dvd_neg.mpr h1) h2
    exact (hunit.dvd_mul_left).mp h3
  have base : (PowerSeries.X : PowerSeries K) ^ 1 ∣ δ := by
    rw [pow_one, PowerSeries.X_dvd_iff, hδ, map_sub, hc, sub_self]
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · rw [h0, pow_zero]; exact one_dvd _
  · have : ∀ k, 1 ≤ k → k ≤ M → (PowerSeries.X : PowerSeries K) ^ k ∣ δ := by
      intro k hk1 hkM
      induction k with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0; exact base
        · exact step k hk0 (by omega) (ih hk0 (by omega))
    exact this M hpos le_rfl

end Trunc

section Coeff

variable {C K : Type*} [Field C] [CharZero C] [Field K] [CharZero K] [Algebra C K]

/-- **The coefficient at `T` along a split root**, from a truncation `Θ̃ ≡ Θ mod Tᴹ` of the
inverted root: a finite sum of coefficients of the powers of `Θ̃`. -/
theorem coeff_eval_inf_split (Q : C[X][X]) (s M : ℕ) (Θ Θt : PowerSeries K)
    (hX : (PowerSeries.X : PowerSeries K) ^ M ∣ Θ - Θt)
    (hM : ∀ j ≤ Q.natDegree, 1 + (Q.coeff j).natDegree + s * j < M) :
    ((Q.map (infSub (K := K) 1)).eval (ofPowerSeries ℤ K Θ * single (-(s : ℤ)) 1)).coeff 1 =
      ∑ j ∈ Finset.range (Q.natDegree + 1), ∑ i ∈ Finset.range ((Q.coeff j).natDegree + 1),
        algebraMap C K ((Q.coeff j).coeff i) * PowerSeries.coeff (1 + i + s * j) (Θt ^ j) := by
  rw [eval_map, eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [infSub_eq_sum, Finset.sum_mul, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ (Q.coeff j).natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : (ofPowerSeries ℤ K Θ * single (-(s : ℤ)) 1) ^ j =
      ofPowerSeries ℤ K (Θ ^ j) * single (-((s * j : ℕ) : ℤ)) 1 := by
    rw [mul_pow, map_pow, HahnSeries.single_pow, one_pow]
    congr 2
    push_cast; ring
  rw [hpow, ← mul_assoc, mul_comm (single _ _), mul_assoc, HahnSeries.single_mul_single, mul_one]
  rw [show (-(((1 : ℕ) : ℤ) * (i : ℤ)) + -(((s * j : ℕ)) : ℤ)) = -((i + s * j : ℕ) : ℤ) by
    push_cast; ring]
  have key := HahnSeries.coeff_mul_single_add (r := algebraMap C K ((Q.coeff j).coeff i))
    (x := ofPowerSeries ℤ K (Θ ^ j)) (a := ((1 + i + s * j : ℕ) : ℤ)) (b := -((i + s * j : ℕ) : ℤ))
  rw [show ((1 + i + s * j : ℕ) : ℤ) + -((i + s * j : ℕ) : ℤ) = 1 by push_cast; ring] at key
  rw [key, ofPowerSeries_apply_coeff, mul_comm]
  congr 1
  -- the powers agree below `M`
  have hdj : (PowerSeries.X : PowerSeries K) ^ M ∣ Θ ^ j - Θt ^ j :=
    hX.trans (sub_dvd_pow_sub_pow _ _ _)
  have hlt : 1 + i + s * j < M := lt_of_le_of_lt (by omega) (hM j hj')
  have h0 := (PowerSeries.X_pow_dvd_iff.mp hdj) (1 + i + s * j) hlt
  rw [map_sub, sub_eq_zero] at h0
  exact h0

end Coeff

section FibreConst

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- The constant coefficient of `F(a + T, Y)` at a power series `Y`: `F(a, Y(0))`. -/
lemma fibrePS_eval_const' (F : C[X][X]) (a : K) (Y : PowerSeries K) :
    PowerSeries.constantCoeff ((fibrePS F a).eval Y) =
      (fibreAt F a).eval (PowerSeries.constantCoeff Y) := by
  simp only [fibrePS, fibreAt, eval_map, Polynomial.eval₂_eq_sum_range, map_sum, map_mul, map_pow,
    Polynomial.map_map, natDegree_map]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_zero_psSub]
  rfl

end FibreConst

section Cert

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L)

/-- **Zero residues at split places at infinity, certified by truncations.** If the fibre at
`T = 0` of the inverted curve has the distinct simple roots `γₖ`, the polynomials `Θ̃ₖ` are
approximate roots modulo `Tᴹ`, and the residue values `cₖ` computed from them are derivatives,
then along the split branch system above infinity (`N = 1`) every residue of `evT Q` vanishes. -/
theorem zero_res_split (n s M : ℕ) (hn : S.F.natDegree = n)
    (hdeg : ∀ i ≤ n, (S.F.coeff i).natDegree ≤ (n - i) * s) (γ : Fin n → C)
    (hγi : Function.Injective γ)
    (hγ : ∀ k, (fibreAt (K := K) (invPS n s S.F) 0).eval (algebraMap C K (γ k)) = 0)
    (hγ' : ∀ k, (fibreAt (K := K) (derivative (invPS n s S.F)) 0).eval (algebraMap C K (γ k)) ≠ 0)
    (Θt : Fin n → C[X]) (hΘ0 : ∀ k, (Θt k).coeff 0 = γ k)
    (hΘM : ∀ k, (PowerSeries.X : PowerSeries K) ^ M ∣
      (fibrePS (K := K) (invPS n s S.F) 0).eval (((Θt k).map (algebraMap C K) : K[X]) : PowerSeries K))
    (Q : C[X][X]) (hM : ∀ j ≤ Q.natDegree, 1 + (Q.coeff j).natDegree + s * j < M)
    (z : Fin n → C)
    (hz : ∀ k, (z k)′ = ∑ j ∈ Finset.range (Q.natDegree + 1),
      ∑ i ∈ Finset.range ((Q.coeff j).natDegree + 1),
        (Q.coeff j).coeff i * ((Θt k) ^ j).coeff (1 + i + s * j))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′) :
    ∃ li : List (LaurentSeries K), ∃ hli : S.F.map (infSub (K := K) 1) =
      (li.map fun r ↦ X - Polynomial.C r).prod,
      ∀ r (hr : r ∈ li), ∃ β : K, (S.embG (infSub 1) (infSub_injective 1 one_pos) r
        (S.root_of_mem hli hr) (S.evT Q)).coeff 1 = β′ := by
  classical
  have hγK : Function.Injective fun k ↦ algebraMap C K (γ k) := fun i j h ↦
    hγi ((algebraMap C K).injective h)
  obtain ⟨Θ, hΘ, hsplit⟩ := split_inf_inv S.F n s S.monic hn hdeg (fun k ↦ algebraMap C K (γ k))
    hγK hγ hγ'
  set r : Fin n → LaurentSeries K := fun k ↦ ofPowerSeries ℤ K (Θ k) * single (-(s : ℤ)) 1 with hr
  refine ⟨List.ofFn r, by rw [hsplit, List.map_ofFn, List.prod_ofFn]; rfl, ?_⟩
  intro r0 hr0
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr0
  refine ⟨algebraMap C K (z k), ?_⟩
  rw [S.embG_evT]
  set Θk : PowerSeries K := (((Θt k).map (algebraMap C K) : K[X]) : PowerSeries K) with hΘk
  -- the truncation agrees with the root modulo `Tᴹ`
  have hagree : (PowerSeries.X : PowerSeries K) ^ M ∣ Θ k - Θk := by
    refine hensel_trunc _ (Θ k) Θk (hΘ k).1 ?_ ?_ M (hΘM k)
    · rw [(hΘ k).2, hΘk, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        Polynomial.coeff_map, hΘ0]
    · rw [derivative_fibrePS, fibrePS_eval_const', hΘk, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        Polynomial.coeff_coe, Polynomial.coeff_map, hΘ0]
      exact hγ' k
  rw [coeff_eval_inf_split Q s M (Θ k) Θk hagree hM, hK, hz k, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, hΘk, ← Polynomial.coe_pow, Polynomial.coeff_coe, ← Polynomial.map_pow,
    Polynomial.coeff_map]

end CurveData

end Cert

end Curves



