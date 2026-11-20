import RischTragerBronstein.Algebraic.SuperPrincipal
import RischTragerBronstein.Algebraic.SuperExact

/-!
# Jets and orders on a superelliptic curve

For `W ∈ C[X][X]` (degree `< n` in the second variable), `elemW W = ∑ Wᵢ(x) yⁱ ∈ C⟮x⟯⟮y⟯`. At an
ordinary point `(α, β)`, the expansion of `elemW W` is the jet of `W` along the Hensel branch of
`ⁿ√p` (`embXY_elemW`), so:

* `orderTop_ge_of_vanish`: vanishing to order `m` (`VanishAtN`, with any polynomial branch jet)
  gives order `≥ m`;
* `vanish_of_orderTop_ge`: conversely, order `≥ m` gives vanishing to order `m`.
-/

open Polynomial IntermediateField HahnSeries

namespace Sup

section PS

variable {K : Type*} [Field K]

/-- The jet along a power series branch `Y`: `∑_{i < N} Wᵢ(α + s) Yⁱ`. -/
noncomputable def jetPS (W : K[X][X]) (α : K) (Y : PowerSeries K) (N : ℕ) : PowerSeries K :=
  ∑ i ∈ Finset.range N, (((W.coeff i).comp (X + Polynomial.C α) : K[X]) : PowerSeries K) * Y ^ i

lemma coe_jetN (W : K[X][X]) (α : K) (V : K[X]) (N : ℕ) (hN : W.natDegree < N) :
    ((jetN W α V : K[X]) : PowerSeries K) = jetPS W α (V : PowerSeries K) N := by
  rw [jetN, eval_eq_sum_range' (n := N) (lt_of_le_of_lt (natDegree_map_le) hN)]
  rw [show ((∑ i ∈ Finset.range N, (W.map (compRingHom (X + Polynomial.C α))).coeff i * V ^ i :
      K[X]) : PowerSeries K) = Polynomial.coeToPowerSeries.ringHom
        (∑ i ∈ Finset.range N, (W.map (compRingHom (X + Polynomial.C α))).coeff i * V ^ i) from rfl,
    map_sum]
  simp [jetPS, Polynomial.coeff_map, Polynomial.coe_mul, Polynomial.coe_pow]

lemma jetPS_congr (W : K[X][X]) (α : K) {Y Z : PowerSeries K} (N m : ℕ)
    (h : (PowerSeries.X : PowerSeries K) ^ m ∣ Y - Z) :
    (PowerSeries.X : PowerSeries K) ^ m ∣ jetPS W α Y N - jetPS W α Z N := by
  simp only [jetPS, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ ↦ ?_
  rw [← mul_sub]
  exact Dvd.dvd.mul_left (h.trans (sub_dvd_pow_sub_pow Y Z i)) _

lemma X_pow_dvd_coe_iff (P : K[X]) (m : ℕ) :
    (PowerSeries.X : PowerSeries K) ^ m ∣ (P : PowerSeries K) ↔ X ^ m ∣ P := by
  rw [PowerSeries.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  simp only [Polynomial.coeff_coe]

lemma X_pow_dvd_trunc_sub (Y : PowerSeries K) (m : ℕ) :
    (PowerSeries.X : PowerSeries K) ^ m ∣ ((PowerSeries.trunc m Y : K[X]) : PowerSeries K) - Y := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hk, sub_self]

/-- **A polynomial branch jet agrees with the power series branch** modulo `Xᵐ`. -/
theorem branch_ps_unique {f : K[X]} {n : ℕ} (hn : 0 < n) {α β : K} {m : ℕ} {V : K[X]}
    (hu : IsUnit ((n : K) * β ^ (n - 1))) (hV : IsBranchN f n α β m V) (Y : PowerSeries K)
    (hY : Y ^ n = ((f.comp (X + Polynomial.C α) : K[X]) : PowerSeries K))
    (hY0 : PowerSeries.constantCoeff Y = β) :
    (PowerSeries.X : PowerSeries K) ^ m ∣ (V : PowerSeries K) - Y := by
  have hd : (PowerSeries.X : PowerSeries K) ^ m ∣
      ((V : PowerSeries K) - Y) * ∑ k ∈ Finset.range n, (V : PowerSeries K) ^ k * Y ^ (n - 1 - k) := by
    rw [mul_comm, Commute.geom_sum₂_mul (Commute.all _ _), hY, ← Polynomial.coe_pow,
      ← Polynomial.coe_sub, X_pow_dvd_coe_iff]
    exact hV.2
  have hunit : IsUnit (∑ k ∈ Finset.range n, (V : PowerSeries K) ^ k * Y ^ (n - 1 - k)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_sum]
    have : ∀ k ∈ Finset.range n, PowerSeries.constantCoeff ((V : PowerSeries K) ^ k *
        Y ^ (n - 1 - k)) = β ^ (n - 1) := fun k hk ↦ by
      rw [map_mul, map_pow, map_pow, hY0, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        Polynomial.coeff_coe, hV.1, ← pow_add,
        show k + (n - 1 - k) = n - 1 by have := Finset.mem_range.mp hk; omega]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact hu
  obtain ⟨u, hu'⟩ := hunit
  rw [← hu'] at hd
  exact (Units.dvd_mul_right).mp hd

end PS

lemma le_orderTop_ofPS_iff {K : Type*} [Field K] (H : PowerSeries K) (m : ℕ) :
    ((m : ℤ) : WithTop ℤ) ≤ (ofPowerSeries ℤ K H).orderTop ↔
      (PowerSeries.X : PowerSeries K) ^ m ∣ H := by
  rw [HahnSeries.le_orderTop_iff_forall, PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h k hk
    have := h k (by exact_mod_cast hk)
    rw [LaurentSeries.coeff_ofPS, if_pos (by omega), Int.toNat_natCast] at this
    exact this
  · intro h j hj
    rw [LaurentSeries.coeff_ofPS]
    split_ifs with hj0
    · exact h _ (by have : j < m := by exact_mod_cast hj
                    omega)
    · rfl

end Sup

namespace Differential

namespace SuperData

open Sup

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K]

variable (S : SuperData C L)

/-- `∑_{i < n} Wᵢ(x) yⁱ`. -/
noncomputable def elemW (W : C[X][X]) : C⟮S.x⟯⟮S.y⟯ :=
  ∑ i ∈ Finset.range S.n, S.polyX (W.coeff i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ i

lemma embXY_polyX (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (P : C[X]) : S.embXY α β hβ hβp (S.polyX P) =
      ofPowerSeries ℤ K (((P.map (algebraMap C K)).comp (X + Polynomial.C α) : K[X]) :
        PowerSeries K) := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [polyX, S.embXY_algebraMap, S.embX_algebraMap, shiftHom_apply]

/-- **The expansion of `∑ Wᵢ(x) yⁱ` is the jet along the Hensel branch.** -/
theorem embXY_elemW (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (W : C[X][X]) : S.embXY α β hβ hβp (S.elemW W) = ofPowerSeries ℤ K
      (jetPS (W.map (mapRingHom (algebraMap C K))) α (branchY S.n S.hn (S.hnK K) S.p α β hβ hβp) S.n) := by
  rw [elemW, map_sum, jetPS, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, S.embXY_polyX, S.embXY_gen, map_mul, map_pow, Polynomial.coeff_map,
    coe_mapRingHom]

lemma natDegree_lt_of_coeff (W : C[X][X]) (hW : ∀ i, S.n ≤ i → W.coeff i = 0) :
    (W.map (mapRingHom (algebraMap C K))).natDegree < S.n := by
  refine lt_of_le_of_lt natDegree_map_le ?_
  by_cases hW0 : W = 0
  · rw [hW0, natDegree_zero]; exact S.hn
  rw [natDegree_lt_iff_degree_lt hW0, degree_lt_iff_coeff_zero]
  exact fun i hi ↦ hW i hi

lemma unit_branch (β : K) (hβ : β ≠ 0) : IsUnit ((S.n : K) * β ^ (S.n - 1)) :=
  IsUnit.mk0 _ (mul_ne_zero (S.hnK K) (pow_ne_zero _ hβ))

/-- **Vanishing ⇒ order.** -/
theorem orderTop_ge_of_vanish (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) (W : C[X][X])
    (hW : ∀ i, S.n ≤ i → W.coeff i = 0) (m : ℕ)
    (h : VanishAtN (S.p.map (algebraMap C K)) S.n (W.map (mapRingHom (algebraMap C K))) α β m) :
    ((m : ℤ) : WithTop ℤ) ≤ (S.embXY α β hβ hβp (S.elemW W)).orderTop := by
  obtain ⟨V, hV, hdv⟩ := h
  rw [S.embXY_elemW, le_orderTop_ofPS_iff]
  have hY := branchY_pow S.n S.hn (S.hnK K) S.p α β hβ hβp
  have hcong := branch_ps_unique S.hn (S.unit_branch β hβ) hV _ hY
    (branchY_const S.n S.hn (S.hnK K) S.p α β hβ hβp)
  have h1 := jetPS_congr (W.map (mapRingHom (algebraMap C K))) α S.n m hcong
  rw [← coe_jetN _ _ _ _ (S.natDegree_lt_of_coeff W hW)] at h1
  have h2 := (X_pow_dvd_coe_iff _ m).mpr hdv
  have := dvd_sub h2 h1
  rwa [sub_sub_cancel] at this

/-- **Order ⇒ vanishing.** -/
theorem vanish_of_orderTop_ge (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) (W : C[X][X])
    (hW : ∀ i, S.n ≤ i → W.coeff i = 0) (m : ℕ)
    (h : ((m : ℤ) : WithTop ℤ) ≤ (S.embXY α β hβ hβp (S.elemW W)).orderTop) :
    VanishAtN (S.p.map (algebraMap C K)) S.n (W.map (mapRingHom (algebraMap C K))) α β m := by
  rw [S.embXY_elemW, le_orderTop_ofPS_iff] at h
  set Y := branchY S.n S.hn (S.hnK K) S.p α β hβ hβp
  have hY := branchY_pow S.n S.hn (S.hnK K) S.p α β hβ hβp
  have hY0 := branchY_const S.n S.hn (S.hnK K) S.p α β hβ hβp
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨Polynomial.C β, ⟨by simp, by simp⟩, by simp⟩
  set V : K[X] := PowerSeries.trunc m Y
  have hVY := X_pow_dvd_trunc_sub Y m
  refine ⟨V, ⟨?_, ?_⟩, ?_⟩
  · rw [PowerSeries.coeff_trunc, if_pos hm, PowerSeries.coeff_zero_eq_constantCoeff_apply, hY0]
  · rw [← X_pow_dvd_coe_iff, Polynomial.coe_sub, Polynomial.coe_pow]
    have h3 : (PowerSeries.X : PowerSeries K) ^ m ∣ (V : PowerSeries K) ^ S.n - Y ^ S.n :=
      hVY.trans (sub_dvd_pow_sub_pow _ _ _)
    rwa [hY, pShift] at h3
  · rw [← X_pow_dvd_coe_iff, coe_jetN _ _ _ _ (S.natDegree_lt_of_coeff W hW)]
    have h4 := jetPS_congr (W.map (mapRingHom (algebraMap C K))) α S.n m hVY
    have := dvd_add h4 h
    rwa [sub_add_cancel] at this

section Cert

variable [IsAlgClosed K]

lemma ordInf_gen (hcop : Nat.Coprime S.n S.p.natDegree) :
    S.ordInf K (AdjoinSimple.gen C⟮S.x⟯ S.y) = -(S.p.natDegree : ℤ) := by
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  rw [S.ordInf_eq hcop _ lam hlam hlp]
  unfold embI
  rw [S.embG_gen, S.order_infY]

/-- A lower bound on every term bounds the order of a sum (for a valuation given by a ring map). -/
lemma le_order_hom_sum {M' : Type*} [Field M'] (φ : M' →+* LaurentSeries K) {ι : Type*}
    (s : Finset ι) (t : ι → M') (c : ℤ) (ht : ∀ i ∈ s, t i ≠ 0 → c ≤ (φ (t i)).order)
    (hsum : ∑ i ∈ s, t i ≠ 0) : c ≤ (φ (∑ i ∈ s, t i)).order := by
  have h0 : φ (∑ i ∈ s, t i) ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr hsum
  have : (c : WithTop ℤ) ≤ (φ (∑ i ∈ s, t i)).orderTop := by
    rw [map_sum]
    refine LaurentSeries.le_orderTop_sum _ _ _ fun i hi ↦ ?_
    by_cases hti : t i = 0
    · rw [hti, map_zero, HahnSeries.orderTop_zero]; exact le_top
    · rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ φ.injective).mpr hti)]
      exact_mod_cast ht i hi hti
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero h0] at this
  exact_mod_cast this

/-- `∑ Wᵢ(x) yⁱ` is integral. -/
lemma elemW_integral (W : C[X][X]) : S.IsIntegralS K (S.elemW W) := by
  intro α β hv
  obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hv
  by_cases h0 : S.elemW W = 0
  · rw [hφ, h0, map_zero, HahnSeries.order_zero]
  rw [hφ]
  refine le_order_hom_sum φ _ _ 0 (fun i _ hti ↦ ?_) h0
  have hP : W.coeff i ≠ 0 := fun h ↦ hti (by rw [h, polyX, map_zero, map_zero, zero_mul])
  have hg0 : AdjoinSimple.gen C⟮S.x⟯ S.y ≠ 0 := fun h ↦ S.y_ne_zero (congrArg Subtype.val h)
  rw [← hφ, S.ordAt_mul hv (S.polyX_ne_zero hP) (pow_ne_zero _ hg0), S.ordAt_pow hv,
    S.ordAt_polyX _ hP α β hv, S.ordAt_gen α β hv]
  have : (0 : ℤ) ≤ ((W.coeff i).map (algebraMap C K)).rootMultiplicity α := by positivity
  split_ifs <;> positivity

/-- The pole order at infinity of `∑ Wᵢ(x) yⁱ` is at most `M` when `n deg Wᵢ + d i ≤ M`. -/
lemma elemW_ordInf (hcop : Nat.Coprime S.n S.p.natDegree) (W : C[X][X]) (M : ℕ)
    (hsupp : ∀ i a, (W.coeff i).coeff a ≠ 0 → i < S.n ∧ S.n * a + S.p.natDegree * i ≤ M)
    (h0 : S.elemW W ≠ 0) : -(M : ℤ) ≤ S.ordInf K (S.elemW W) := by
  obtain ⟨φ, hφ⟩ := S.ordInf_hom (K := K) hcop
  rw [hφ]
  refine le_order_hom_sum φ _ _ _ (fun i _ hti ↦ ?_) h0
  have hP : W.coeff i ≠ 0 := fun h ↦ hti (by rw [h, polyX, map_zero, map_zero, zero_mul])
  have hg0 : AdjoinSimple.gen C⟮S.x⟯ S.y ≠ 0 := fun h ↦ S.y_ne_zero (congrArg Subtype.val h)
  rw [← hφ, S.ordInf_mul hcop (S.polyX_ne_zero hP) (pow_ne_zero _ hg0)]
  obtain ⟨ψ, hψ⟩ := S.ordInf_hom (K := K) hcop
  rw [hψ (_ ^ i), map_pow, HahnSeries.order_pow, ← hψ, S.ordInf_gen hcop, S.ordInf_polyX hcop _ hP]
  have hb := hsupp i _ (leadingCoeff_ne_zero.mpr hP)
  have h2 : (S.n : ℤ) * (W.coeff i).natDegree + S.p.natDegree * i ≤ M := by exact_mod_cast hb.2
  rw [nsmul_eq_mul]
  push_cast
  linarith

/-- `∑ Wᵢ(x) yⁱ ≠ 0` for `W ≠ 0` of degree `< n` in `y`. -/
lemma elemW_ne_zero (W : C[X][X]) (hW0 : W ≠ 0) (hW : ∀ i, S.n ≤ i → W.coeff i = 0) :
    S.elemW W ≠ 0 := by
  intro h
  apply hW0
  have hL : ∑ i : Fin S.n, aeval S.x (W.coeff i) * S.y ^ (i : ℕ) = 0 := by
    have := congrArg Subtype.val h
    simp only [elemW, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      SubmonoidClass.coe_pow, AdjoinSimple.coe_gen, S.polyX_coe] at this
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ aeval S.x (W.coeff i) * S.y ^ i)]
    exact this
  have hc := S.coords_unique (fun i ↦ W.coeff i) hL
  ext i : 1
  by_cases hi : i < S.n
  · rw [Polynomial.coeff_zero]; exact hc ⟨i, hi⟩
  · rw [Polynomial.coeff_zero]; exact hW i (not_lt.mp hi)

lemma coeff_ge_n_of_supp (W : C[X][X]) (M : ℕ)
    (hsupp : ∀ i a, (W.coeff i).coeff a ≠ 0 → i < S.n ∧ S.n * a + S.p.natDegree * i ≤ M) :
    ∀ i, S.n ≤ i → W.coeff i = 0 := fun i hi ↦ by
  ext a
  by_contra h
  exact absurd (hsupp i a h).1 (not_lt.mpr hi)

open Classical in
/-- **A certificate gives an exact principal divisor**: a non-zero `∑ Wᵢ(x) yⁱ` built from the
monomials `xᵃ yⁱ`, `n a + d i ≤ M`, vanishing to order `m_Q` at the points `Q ∈ T` (ordinary,
`∑ m_Q = M`) has divisor exactly `∑ m_Q Q − M ∞`. -/
theorem cert_principal (hcop : Nat.Coprime S.n S.p.natDegree) (W : C[X][X]) (hW0 : W ≠ 0)
    (M : ℕ) (hsupp : ∀ i a, (W.coeff i).coeff a ≠ 0 → i < S.n ∧ S.n * a + S.p.natDegree * i ≤ M)
    (T : Finset (K × K)) (mult : K × K → ℕ)
    (hT : ∀ Q ∈ T, Q.2 ≠ 0 ∧ Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1)
    (hM : ∑ Q ∈ T, mult Q = M)
    (hv : ∀ Q ∈ T, VanishAtN (S.p.map (algebraMap C K)) S.n (W.map (mapRingHom (algebraMap C K)))
      Q.1 Q.2 (mult Q)) :
    S.IsPrincipalS K (fun Q ↦ if Q ∈ T then mult Q else 0) 1 := by
  have hW := S.coeff_ge_n_of_supp W M hsupp
  set w := S.elemW W
  have hw0 : w ≠ 0 := S.elemW_ne_zero W hW0 hW
  have hint := S.elemW_integral (K := K) W
  have hinf := S.elemW_ordInf (K := K) hcop W M hsupp hw0
  have hge : ∀ Q ∈ T, (mult Q : ℤ) ≤ S.ordAt K w Q.1 Q.2 := fun Q hQ ↦ by
    obtain ⟨hβ, hvQ⟩ := hT Q hQ
    have h1 := S.orderTop_ge_of_vanish Q.1 Q.2 hβ hvQ W hW (mult Q) (hv Q hQ)
    rw [S.ordAt_nb _ _ _ hβ hvQ]
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr
      hw0)] at h1
    exact_mod_cast h1
  have hvalid : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 := fun Q hQ ↦ (hT Q hQ).2
  have hsumT := S.degree_le' K hcop w hw0 hint T hvalid
  have hsumge : (M : ℤ) ≤ ∑ Q ∈ T, S.ordAt K w Q.1 Q.2 := by
    rw [← hM]; push_cast; exact Finset.sum_le_sum hge
  -- equality on `T`
  have heqT : ∀ Q ∈ T, S.ordAt K w Q.1 Q.2 = mult Q := by
    have hM' : (∑ Q ∈ T, (mult Q : ℤ)) = M := by exact_mod_cast hM
    have hsum0 : ∑ Q ∈ T, (S.ordAt K w Q.1 Q.2 - mult Q) = 0 := by
      rw [Finset.sum_sub_distrib, hM']; linarith
    intro Q hQ
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun Q hQ ↦ sub_nonneg.mpr (hge Q hQ))).mp hsum0 Q hQ
    linarith
  refine ⟨w, hw0, hint, fun Q hQv ↦ ?_⟩
  dsimp only
  by_cases hQ : Q ∈ T
  · rw [if_pos hQ, heqT Q hQ]; push_cast; ring
  · rw [if_neg hQ, Nat.cast_zero, mul_zero]
    have h1 := S.degree_le' K hcop w hw0 hint (insert Q T) (fun Q' hQ' ↦ by
      rcases Finset.mem_insert.mp hQ' with rfl | h
      · exact hQv
      · exact hvalid Q' h)
    rw [Finset.sum_insert hQ] at h1
    have h2 := hint Q.1 Q.2 hQv
    linarith

open Classical in
/-- **An exact principal divisor gives a certificate.** -/
theorem principal_cert (hcop : Nat.Coprime S.n S.p.natDegree) (T : Finset (K × K))
    (mult : K × K → ℕ)
    (hT : ∀ Q ∈ T, Q.2 ≠ 0 ∧ Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1)
    (h : S.IsPrincipalS K (fun Q ↦ if Q ∈ T then mult Q else 0) 1) :
    ∃ W : C[X][X], W ≠ 0 ∧
      (∀ i a, (W.coeff i).coeff a ≠ 0 → i < S.n ∧
        S.n * a + S.p.natDegree * i ≤ ∑ Q ∈ T, mult Q) ∧
      ∀ Q ∈ T, VanishAtN (S.p.map (algebraMap C K)) S.n (W.map (mapRingHom (algebraMap C K)))
        Q.1 Q.2 (mult Q) := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  obtain ⟨w, hw0, hint, hord⟩ := h
  obtain ⟨a, ha, hpoly⟩ := S.integral_of_regular' K w hint
  choose P hP using hpoly
  set W : C[X][X] := ∑ i : Fin S.n, Polynomial.monomial (i : ℕ) (P i)
  have hWc : ∀ i : ℕ, W.coeff i = if h : i < S.n then P ⟨i, h⟩ else 0 := fun i ↦ by
    simp only [W, finsetSum_coeff, coeff_monomial]
    split_ifs with hi
    · rw [Finset.sum_eq_single ⟨i, hi⟩ (fun b _ hb ↦ by
        rw [if_neg (fun h ↦ hb (Fin.ext h))]) (fun h ↦ absurd (Finset.mem_univ _) h), if_pos rfl]
    · exact Finset.sum_eq_zero fun b _ ↦ by rw [if_neg (fun h ↦ hi (by rw [← h]; exact b.2))]
  have hWn : ∀ i, S.n ≤ i → W.coeff i = 0 := fun i hi ↦ by rw [hWc, dif_neg (by omega)]
  have haP : ∀ i, a i = algebraMap C[X] C⟮S.x⟯ (P i) := fun i ↦
    Subtype.ext (by rw [hP i, algebraMap_adjoinSimple])
  have hwW : S.elemW W = w := by
    rw [ha, elemW, ← Fin.sum_univ_eq_sum_range (fun i ↦ S.polyX (W.coeff i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hWc, dif_pos i.2, haP]
    rfl
  have hW0 : W ≠ 0 := fun h0 ↦ hw0 (by rw [← hwW, h0]; simp [elemW, polyX])
  have hvalid : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 := fun Q hQ ↦ (hT Q hQ).2
  -- the pole order at infinity
  have hdeg := S.degree_eq' K hcop w hw0 hint T hvalid (fun α β hv hn ↦ by
    rw [hord (α, β) hv]; simp [hn])
  have hdeg' : ∑ Q ∈ T, (mult Q : ℤ) = -S.ordInf K w := by
    rw [← hdeg]
    refine Finset.sum_congr rfl fun Q hQ ↦ ?_
    rw [hord Q (hvalid Q hQ)]
    simp [hQ]
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  have hinf : ((-(∑ Q ∈ T, mult Q : ℕ) : ℤ) : WithTop ℤ) ≤
      (S.embI lam hlam hlp (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
        AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ))).orderTop := by
    rw [← ha, ← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr
      hw0), ← S.ordInf_eq hcop w lam hlam hlp]
    exact WithTop.coe_le_coe.mpr (by push_cast; linarith)
  have hb := S.inf_bound hcop lam hlam hlp a _ hinf
  refine ⟨W, hW0, fun i b hib ↦ ?_, fun Q hQ ↦ ?_⟩
  · have hi : i < S.n := by
      by_contra hni
      exact hib (by rw [hWn i (not_lt.mp hni), Polynomial.coeff_zero])
    rw [hWc, dif_pos hi] at hib
    have hPi : P ⟨i, hi⟩ ≠ 0 := fun h0 ↦ hib (by rw [h0, Polynomial.coeff_zero])
    have hai : a ⟨i, hi⟩ ≠ 0 := by
      rw [haP]; exact fun h0 ↦ hPi ((map_eq_zero_iff _ (IsFractionRing.injective C[X] C⟮S.x⟯)).mp h0)
    have h1 := hb ⟨i, hi⟩ hai
    rw [haP, S.embXG_inf_poly _ hPi] at h1
    have hbd : b ≤ (P ⟨i, hi⟩).natDegree := le_natDegree_of_ne_zero hib
    refine ⟨hi, ?_⟩
    have : (S.n : ℤ) * b ≤ S.n * (P ⟨i, hi⟩).natDegree := by
      exact_mod_cast Nat.mul_le_mul_left _ hbd
    have h2 : (S.n : ℤ) * b + S.p.natDegree * i ≤ ∑ Q ∈ T, mult Q := by
      push_cast at h1 ⊢; linarith
    exact_mod_cast h2
  · obtain ⟨hβ, hvQ⟩ := hT Q hQ
    refine S.vanish_of_orderTop_ge Q.1 Q.2 hβ hvQ W hWn (mult Q) ?_
    rw [hwW, ← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr
      hw0), ← S.ordAt_nb _ _ _ hβ hvQ, hord Q hvQ]
    simp [hQ]

end Cert

end SuperData

end Differential
