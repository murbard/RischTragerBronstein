import RischTragerBronstein.Mixed.NKResRamConj
import RischTragerBronstein.Mixed.NKMultiRUnits
import RischTragerBronstein.Algebraic.LaurentDeriv

/-!
# Zero residues at infinity for several slopes: one Newton segment at a time

For a segment of slope `s/e` (`s ∈ ℤ`) and height `K₀` (`e·deg aᵢ + i s ≤ K₀`), the segment
polynomial `Q(τ, Z) = τ^{K₀} P(τ^{−e}, Z τ^{−s})` (`segPoly`) has polynomial coefficients. Along a
branch system `x = T^{−N}`, `N = d e`, a root `ρ = T^{−ds} Θ(T)` of `P` gives the power-series root
`Θ` of `Q(T^d, Z)` (`segPoly_root`), and the coefficient at `T^N` of `f(ρ)` is
`∑ⱼ ∑ₗ fⱼₗ [T^{N + N l + d s j}] Θʲ` (`coeff_eval_seg`) — computable from a truncation of `Θ`.
-/

open Polynomial HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Seg

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- The coefficient `τ^{K₀ − i s} a(τ^{−e})` of the segment polynomial. -/
noncomputable def segCoef (e : ℕ) (s K0 : ℤ) (i : ℕ) (a : C[X]) : C[X] :=
  ∑ l ∈ Finset.range (a.natDegree + 1),
    Polynomial.C (a.coeff l) * X ^ (K0 - i * s - e * l).toNat

/-- **The segment polynomial** `τ^{K₀} P(τ^{−e}, Z τ^{−s})`. -/
noncomputable def segPoly (e : ℕ) (s K0 : ℤ) (P : C[X][X]) : C[X][X] :=
  ∑ i ∈ Finset.range (P.natDegree + 1), Polynomial.C (segCoef e s K0 i (P.coeff i)) * X ^ i

/-- `q(τ) ↦ q(T^d)` in `K⟦T⟧`. -/
noncomputable def phiD (d : ℕ) : C[X] →+* PowerSeries K :=
  (Polynomial.coeToPowerSeries.ringHom (R := K)).comp
    ((expand K d : K[X] →ₐ[K] K[X]).toRingHom.comp (mapRingHom (algebraMap C K)))

lemma ofPS_phiD_monomial (d : ℕ) (c : C) (k : ℕ) :
    ofPowerSeries ℤ K (phiD d (Polynomial.C c * X ^ k)) = single ((d * k : ℕ) : ℤ) (algebraMap C K c) := by
  have h1 : phiD (K := K) d (Polynomial.C c * X ^ k) =
      PowerSeries.C (algebraMap C K c) * PowerSeries.X ^ (d * k) := by
    simp only [phiD, RingHom.comp_apply, map_mul, map_pow, coe_mapRingHom, Polynomial.map_C,
      Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, expand_C, expand_X,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow,
      Polynomial.coe_mul, ← pow_mul]
  rw [h1, map_mul, HahnSeries.ofPowerSeries_C, ofPowerSeries_X_pow, HahnSeries.C_mul_eq_smul]
  ext n
  simp only [HahnSeries.coeff_smul, HahnSeries.coeff_single, smul_eq_mul]
  split_ifs <;> simp

lemma ofPS_phiD_segCoef (N d e : ℕ) (hN : N = d * e) (s K0 : ℤ) (i : ℕ) (a : C[X])
    (hb : a ≠ 0 → (e : ℤ) * a.natDegree + i * s ≤ K0) :
    ofPowerSeries ℤ K (phiD d (segCoef e s K0 i a)) =
      single ((d : ℤ) * (K0 - i * s)) 1 * infSub (K := K) N a := by
  by_cases ha : a = 0
  · subst ha; simp [segCoef]
  have hb' := hb ha
  rw [segCoef, map_sum, map_sum, infSub_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' : l ≤ a.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [ofPS_phiD_monomial, HahnSeries.single_mul_single, one_mul]
  have hnn : 0 ≤ K0 - i * s - e * l := by
    have : (e : ℤ) * l ≤ e * a.natDegree := by exact_mod_cast Nat.mul_le_mul_left e hl'
    linarith
  congr 1
  rw [Nat.cast_mul, Int.toNat_of_nonneg hnn, hN]
  push_cast; ring

lemma coeff_segPoly (e : ℕ) (s K0 : ℤ) (P : C[X][X]) (i : ℕ) :
    (segPoly e s K0 P).coeff i = if i ≤ P.natDegree then segCoef e s K0 i (P.coeff i) else 0 := by
  classical
  rw [segPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_iff]

lemma natDegree_segPoly_le (e : ℕ) (s K0 : ℤ) (P : C[X][X]) :
    (segPoly e s K0 P).natDegree ≤ P.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_segPoly, if_neg (by exact_mod_cast not_le.mpr hi)]

/-- **A root along `x = T^{−N}` gives a power-series root of the segment polynomial.** -/
theorem segPoly_root (N d e : ℕ) (hN : N = d * e) (s K0 : ℤ) (P : C[X][X])
    (hb : ∀ i ≤ P.natDegree, P.coeff i ≠ 0 → (e : ℤ) * (P.coeff i).natDegree + i * s ≤ K0)
    (Θ : PowerSeries K)
    (hr : (P.map (infSub (K := K) N)).eval (single (-((d : ℤ) * s)) 1 * ofPowerSeries ℤ K Θ) = 0) :
    ((segPoly e s K0 P).map (phiD (K := K) d)).eval Θ = 0 := by
  classical
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [map_zero]
  have hlt : ((segPoly e s K0 P).map (phiD (K := K) d)).natDegree < P.natDegree + 1 :=
    lt_of_le_of_lt (natDegree_map_le.trans (natDegree_segPoly_le e s K0 P)) (Nat.lt_succ_self _)
  have hlt' : (P.map (infSub (K := K) N)).natDegree < P.natDegree + 1 :=
    lt_of_le_of_lt natDegree_map_le (Nat.lt_succ_self _)
  rw [eval_eq_sum_range' hlt'] at hr
  rw [eval_eq_sum_range' hlt, map_sum]
  have key : ∀ i ∈ Finset.range (P.natDegree + 1),
      ofPowerSeries ℤ K (((segPoly e s K0 P).map (phiD (K := K) d)).coeff i * Θ ^ i) =
        single ((d : ℤ) * K0) 1 * ((P.map (infSub (K := K) N)).coeff i *
          (single (-((d : ℤ) * s)) 1 * ofPowerSeries ℤ K Θ) ^ i) := by
    intro i hi
    have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Polynomial.coeff_map, coeff_segPoly, if_pos hi', map_mul, map_pow,
      ofPS_phiD_segCoef N d e hN s K0 i _ (hb i hi'), Polynomial.coeff_map, mul_pow,
      HahnSeries.single_pow, one_pow]
    have hs : single ((d : ℤ) * (K0 - i * s)) (1 : K) =
        single ((d : ℤ) * K0) 1 * single (i • -((d : ℤ) * s)) 1 := by
      rw [HahnSeries.single_mul_single, one_mul]
      congr 1
      rw [nsmul_eq_mul]; ring
    rw [hs]
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, hr, mul_zero]

/-- **The coefficient at `T^N` along `ρ = T^{−ds} Θ`**, from a truncation `Θ̃ ≡ Θ mod T^{M}`. -/
theorem coeff_eval_seg (Q : C[X][X]) (N d : ℕ) (s : ℤ) (Θ Θt : PowerSeries K) (Mt : ℕ)
    (hX : (PowerSeries.X : PowerSeries K) ^ Mt ∣ Θ - Θt)
    (hM : ∀ j ≤ Q.natDegree, ∀ l ≤ (Q.coeff j).natDegree,
      (N : ℤ) + N * l + d * s * j < Mt) :
    ((Q.map (infSub (K := K) N)).eval (single (-((d : ℤ) * s)) 1 * ofPowerSeries ℤ K Θ)).coeff
        (N : ℤ) =
      ∑ j ∈ Finset.range (Q.natDegree + 1), ∑ l ∈ Finset.range ((Q.coeff j).natDegree + 1),
        algebraMap C K ((Q.coeff j).coeff l) *
          (ofPowerSeries ℤ K (Θt ^ j)).coeff ((N : ℤ) + N * l + d * s * j) := by
  rw [eval_map, eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [infSub_eq_sum, Finset.sum_mul, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' : l ≤ (Q.coeff j).natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hpow : (single (-((d : ℤ) * s)) (1 : K) * ofPowerSeries ℤ K Θ) ^ j =
      single (-((d : ℤ) * s * j)) 1 * ofPowerSeries ℤ K (Θ ^ j) := by
    rw [mul_pow, map_pow, HahnSeries.single_pow, one_pow]
    congr 2
    rw [nsmul_eq_mul]; ring
  have hsg : single (-((N : ℤ) * l)) (algebraMap C K ((Q.coeff j).coeff l)) =
      HahnSeries.C (algebraMap C K ((Q.coeff j).coeff l)) * single (-((N : ℤ) * l)) 1 := by
    rw [HahnSeries.C_mul_eq_smul]
    ext n
    simp only [HahnSeries.coeff_smul, HahnSeries.coeff_single, smul_eq_mul]
    split_ifs <;> simp
  rw [hpow, hsg, mul_assoc, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, ← mul_assoc,
    HahnSeries.single_mul_single, one_mul, LaurentSeries.coeff_single_mul, smul_eq_mul]
  congr 1
  rw [show (N : ℤ) - (-((N : ℤ) * l) + -((d : ℤ) * s * j)) = (N : ℤ) + N * l + d * s * j by ring]
  rw [LaurentSeries.coeff_ofPS, LaurentSeries.coeff_ofPS]
  split_ifs with h0
  · have hdj : (PowerSeries.X : PowerSeries K) ^ Mt ∣ Θ ^ j - Θt ^ j :=
      hX.trans (sub_dvd_pow_sub_pow _ _ _)
    have hlt : ((N : ℤ) + N * l + d * s * j).toNat < Mt := by
      have := hM j hj' l hl'; omega
    have h0' := (PowerSeries.X_pow_dvd_iff.mp hdj) _ hlt
    rw [map_sub, sub_eq_zero] at h0'
    exact h0'
  · rfl

/-- The truncation through `q(τ) ↦ q(T^d)`: coefficients at multiples of `d`. -/
lemma coeff_ofPS_phiD_pow (d : ℕ) (hd : 0 < d) (Θ : C[X]) (j : ℕ) (k : ℤ) :
    (ofPowerSeries ℤ K (phiD (K := K) d Θ ^ j)).coeff ((d : ℤ) * k) =
      if 0 ≤ k then algebraMap C K ((Θ ^ j).coeff k.toNat) else 0 := by
  rw [← map_pow, LaurentSeries.coeff_ofPS]
  by_cases hk : 0 ≤ k
  · rw [if_pos (by positivity), if_pos hk]
    simp only [phiD, RingHom.comp_apply, coe_mapRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]
    have e1 : ((d : ℤ) * k).toNat = d * k.toNat := by
      lift k to ℕ using hk
      rw [Int.toNat_natCast, ← Nat.cast_mul, Int.toNat_natCast]
    rw [e1]
    rw [coeff_expand_mul' hd, Polynomial.coeff_map]
  · rw [if_neg (by nlinarith), if_neg hk]

lemma phiD_eval (d : ℕ) (Q : C[X][X]) (q : C[X]) :
    (Q.map (phiD (K := K) d)).eval (phiD d q) = phiD d (Q.eval q) := by
  rw [eval_map, eval₂_hom]

lemma coeff_phiD (d : ℕ) (hd : 0 < d) (q : C[X]) (n : ℕ) :
    PowerSeries.coeff n (phiD (K := K) d q) =
      if d ∣ n then algebraMap C K (q.coeff (n / d)) else 0 := by
  simp only [phiD, RingHom.comp_apply, coe_mapRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]
  rw [coeff_expand hd]
  split_ifs <;> simp [Polynomial.coeff_map]

/-- **Truncation of a segment root**: a power-series root `Θ` of `Q(T^d, ·)` and an approximate
root `Θ̃` of `Q(τ, ·)` modulo `τᴹ` with the same constant term and `∂Q(0, Θ̃(0)) ≠ 0` agree
modulo `T^{dM}`. -/
theorem seg_trunc (d : ℕ) (hd : 0 < d) (Qs : C[X][X]) (Θ : PowerSeries K)
    (hΘ : (Qs.map (phiD (K := K) d)).eval Θ = 0) (Θt : C[X])
    (hc : PowerSeries.constantCoeff Θ = algebraMap C K (Θt.coeff 0))
    (hu : ((derivative Qs).eval Θt).coeff 0 ≠ 0) (M : ℕ)
    (hM : ∀ k < M, (Qs.eval Θt).coeff k = 0) :
    (PowerSeries.X : PowerSeries K) ^ (d * M) ∣ Θ - phiD d Θt := by
  have hc0 : ∀ q : C[X], PowerSeries.constantCoeff (phiD (K := K) d q) =
      algebraMap C K (q.coeff 0) := fun q ↦ by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_phiD d hd, if_pos (dvd_zero d),
      Nat.zero_div]
  refine hensel_trunc _ Θ (phiD d Θt) hΘ (by rw [hc, hc0]) ?_ (d * M) ?_
  · rw [Polynomial.derivative_map, phiD_eval, hc0]
    exact fun h ↦ hu ((algebraMap C K).injective (by rw [h, map_zero]))
  · rw [phiD_eval, PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [coeff_phiD d hd]
    split_ifs with hdn
    · obtain ⟨k, rfl⟩ := hdn
      rw [Nat.mul_div_cancel_left _ hd, hM k (by
        by_contra h; push_neg at h; exact absurd (Nat.mul_le_mul_left d h) (by omega)), map_zero]
    · rfl

end Seg

section Curve

variable {C L Kb : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Differential C] [Differential L] [DifferentialAlgebra C L]
  [Field Kb] [CharZero Kb] [Algebra C Kb] [Differential Kb] [IsAlgClosed Kb]

namespace CurveData

variable (S : CurveData C L)

/-- **Zero residues at infinity for several Newton segments**: for every place `(k, γ)` an
`eₖ`-th root `β` of `γ` in `C`, an approximate root `Θ̃` of the segment polynomial with
`Θ̃(0) = β`, `∂Q(0, β) ≠ 0`, and residue values `∑ⱼ ∑ₗ fⱼₗ [τ^{e + e l + s j}] Θ̃ʲ` that are
derivatives: then along a branch system above infinity every residue of `f` vanishes. -/
theorem zero_res_multi {q : ℕ} (e : Fin (q + 1) → ℕ) (he : ∀ k, 0 < e k) (s : Fin (q + 1) → ℤ)
    (hcop : ∀ k, Int.gcd (s k) (e k) = 1)
    (hdec : ∀ k : Fin q, s k.succ * e k.castSucc < s k.castSucc * e k.succ)
    (K0 : Fin (q + 1) → ℤ) (c : Fin (q + 1) → C) (hc : ∀ k, c k ≠ 0) (lo : Fin (q + 1) → ℕ)
    (Γ : Fin (q + 1) → List C) (hΓ : ∀ k, (Γ k).Nodup ∧ (0 : C) ∉ Γ k)
    (hbound : ∀ k, ∀ i ≤ S.F.natDegree, S.F.coeff i ≠ 0 →
      (e k : ℤ) * (S.F.coeff i).natDegree + i * s k ≤ K0 k)
    (hres : ∀ k, ∑ i ∈ Finset.range (S.F.natDegree + 1),
      Polynomial.C (coeffZe (S.F.coeff i) (e k) (K0 k - i * s k)) * X ^ i =
        Polynomial.C (c k) * X ^ (lo k) * ((Γ k).map fun γ ↦ X ^ (e k) - Polynomial.C γ).prod)
    (htop : lo 0 + e 0 * (Γ 0).length = S.F.natDegree)
    (hchain : ∀ k : Fin q, lo k.castSucc = lo k.succ + e k.succ * (Γ k.succ).length)
    (hlast : lo (Fin.last q) = 0)
    (β : ∀ k, Fin (Γ k).length → C) (hβ : ∀ k i, β k i ^ e k = (Γ k)[(i : ℕ)])
    (Θt : ∀ k, Fin (Γ k).length → C[X]) (hΘ0 : ∀ k i, (Θt k i).coeff 0 = β k i)
    (hu : ∀ k i, ((derivative (segPoly (e k) (s k) (K0 k) S.F)).eval (Θt k i)).coeff 0 ≠ 0)
    (M : ℕ) (hM : ∀ k i, ∀ n < M, ((segPoly (e k) (s k) (K0 k) S.F).eval (Θt k i)).coeff n = 0)
    (Q : C[X][X])
    (hMb : ∀ k, ∀ j ≤ Q.natDegree, ∀ l ≤ (Q.coeff j).natDegree,
      (e k : ℤ) + e k * l + s k * j < M)
    (z : ∀ k, Fin (Γ k).length → C)
    (hz : ∀ k i, (z k i)′ = ∑ j ∈ Finset.range (Q.natDegree + 1),
      ∑ l ∈ Finset.range ((Q.coeff j).natDegree + 1), (Q.coeff j).coeff l *
        (if 0 ≤ (e k : ℤ) + e k * l + s k * j then
          ((Θt k i) ^ j).coeff ((e k : ℤ) + e k * l + s k * j).toNat else 0))
    (hK : ∀ c : C, (algebraMap C Kb c)′ = algebraMap C Kb c′) :
    ∃ (N : ℕ) (hN : 0 < N) (li : List (LaurentSeries Kb)) (hli : S.F.map (infSub (K := Kb) N) =
      (li.map fun r ↦ X - Polynomial.C r).prod),
      ∀ r (hr : r ∈ li), ∃ b : Kb, (S.embG (infSub N) (infSub_injective N hN) r
        (S.root_of_mem hli hr) (S.evT Q)).coeff (N : ℤ) = b′ := by
  classical
  have hF0 : S.F.coeff 0 ≠ 0 := coeff0_ne_of_resR S.F (e (Fin.last q)) (he _) (s (Fin.last q))
    (K0 (Fin.last q)) (c (Fin.last q)) (hc _) (Γ (Fin.last q)) (hΓ _).2
    (by rw [← hlast]; exact hres _)
  obtain ⟨Nb, hNb, lb, -, hlb⟩ := S.hasBranchesInf (K := Kb)
  have hNb' := Nat.pos_of_ne_zero hNb
  set E : ℕ := ∏ k, e k with hE
  have hE0 : 0 < E := Finset.prod_pos fun k _ ↦ he k
  set N : ℕ := Nb * E with hNdef
  have hN : 0 < N := Nat.mul_pos hNb' hE0
  set lr := lb.map (lsub E hE0) with hlr
  have hl : S.F.map (infSub N) = (lr.map fun r ↦ X - Polynomial.C r).prod :=
    branchSys_lsub S.F Nb E hE0 lb hlb
  have hed : ∀ k, e k ∣ N := fun k ↦
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) _
  have hsA := strictAnti_weights N hN e he hed s hdec
  obtain ⟨hord, huniq, -⟩ := multi_hdataR (K := Kb) N hN S.F S.monic hF0 lr hl e he hed s
    hsA K0 c hc lo Γ hΓ hbound hres htop hchain hlast
  have hl0 : ∀ r ∈ lr, r ≠ 0 := by
    intro r hr h0
    subst h0
    have h1 : (S.F.map (infSub (K := Kb) N)).eval 0 = 0 := S.root_of_mem hl hr
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at h1
    exact hF0 ((infSub_injective N hN) (by rw [h1, map_zero]))
  have : NeZero ((N : ℕ) : Kb) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Kb N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  refine ⟨N, hN, lr, hl, fun r hr ↦ ?_⟩
  obtain ⟨k, hk, γ, hγ, hγe⟩ := hord r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hγ
  set ι := algebraMap C Kb with hι
  set cr := r.coeff r.order with hcr
  have hcr0 : cr ≠ 0 := fun h ↦ hl0 r hr (HahnSeries.coeff_order_eq_zero.mp h)
  set bK := ι (β k ⟨i, hi⟩) with hbK
  set uu := bK / cr with huu
  have hue : uu ^ e k = 1 := by
    rw [huu, div_pow, hγe, hbK, ← map_pow, hβ k ⟨i, hi⟩, div_self]
    rw [← hγe]; exact pow_ne_zero _ hcr0
  obtain ⟨d, hd⟩ := hed k
  have hNe : N / e k = d := by rw [hd, Nat.mul_div_cancel_left _ (he k)]
  have hω : IsPrimitiveRoot (ζ ^ d) (e k) := hζ.pow hN (by rw [hd, mul_comm])
  have hωs : IsPrimitiveRoot ((ζ ^ d) ^ (-s k)) (e k) :=
    hω.zpow_of_gcd_eq_one (-s k) (by rw [Int.neg_gcd]; exact hcop k)
  haveI : NeZero (e k) := ⟨(he k).ne'⟩
  obtain ⟨j, -, hj⟩ := hωs.eq_pow_of_pow_eq_one hue
  have hζj0 : ζ ^ j ≠ 0 := pow_ne_zero _ hζ0
  have hζjN : (ζ ^ j) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  set r' := rot (ζ ^ j) hζj0 r with hr'
  have hr'mem : r' ∈ lr := S.rot_mem N hζj0 hζjN lr hl hr
  have hr'o : r'.order = -((d : ℤ) * s k) := by rw [hr', rot_order, hk, hNe]
  have hr'c : r'.coeff r'.order = bK := by
    rw [hr', rot_lc]
    have hpow' : (ζ ^ j) ^ r.order = ((ζ ^ d) ^ (-s k)) ^ j := by
      rw [hk, hNe, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
        ← zpow_mul]
      congr 1
      ring
    rw [hpow', hj, huu, div_mul_cancel₀ _ hcr0]
  -- the residue along `r` is the one along `r'`
  have hrr := S.root_of_mem hl hr
  have hrr' := S.root_of_mem hl hr'mem
  have hrot := S.embG_rot_coeff N hN hζj0 hζjN r hrr hrr' (S.evT Q) (N : ℤ)
  rw [show (ζ ^ j) ^ (N : ℤ) = 1 by rw [zpow_natCast, hζjN], one_mul] at hrot
  rw [← hrot]
  -- the power series of `r'`
  set Θ := r'.powerSeriesPart with hΘ
  have hr'eq : r' = single (-((d : ℤ) * s k)) 1 * ofPowerSeries ℤ Kb Θ := by
    rw [← hr'o]; exact (single_order_mul_powerSeriesPart r').symm
  have hΘc : PowerSeries.constantCoeff Θ = ι ((Θt k ⟨i, hi⟩).coeff 0) := by
    rw [hΘ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeriesPart_coeff, Nat.cast_zero,
      add_zero, hr'c, hΘ0]
  have hNde : N = d * e k := by rw [hd, mul_comm]
  have hroot : ((segPoly (e k) (s k) (K0 k) S.F).map (phiD (K := Kb) d)).eval Θ = 0 :=
    segPoly_root N d (e k) hNde (s k) (K0 k) S.F (hbound k) Θ (by rw [← hr'eq]; exact hrr')
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hd; omega)
  have hagree := seg_trunc d hd0 _ Θ hroot (Θt k ⟨i, hi⟩) hΘc (hu k ⟨i, hi⟩) M (hM k ⟨i, hi⟩)
  refine ⟨ι (z k ⟨i, hi⟩), ?_⟩
  rw [S.embG_evT]
  rw [show (rot (ζ ^ j) hζj0) r = r' from rfl, hr'eq]
  rw [coeff_eval_seg Q N d (s k) Θ (phiD d (Θt k ⟨i, hi⟩)) (d * M) hagree (fun j' hj' l hl' ↦ by
    have := hMb k j' hj' l hl'
    have h2 : (N : ℤ) + N * l + d * s k * j' = d * ((e k : ℤ) + e k * l + s k * j') := by
      rw [hNde]; push_cast; ring
    rw [h2]; push_cast
    exact mul_lt_mul_of_pos_left this (by exact_mod_cast hd0))]
  rw [hK, hz k ⟨i, hi⟩, map_sum]
  refine Finset.sum_congr rfl fun j' _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have h2 : (N : ℤ) + N * l + d * s k * j' = d * ((e k : ℤ) + e k * l + s k * j') := by
    rw [hNde]; push_cast; ring
  rw [h2, coeff_ofPS_phiD_pow d hd0, map_mul]
  split_ifs
  · rfl
  · rw [map_zero, mul_zero]

end CurveData

end Curve

end Curves
