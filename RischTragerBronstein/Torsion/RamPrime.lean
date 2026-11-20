import RischTragerBronstein.Torsion.UnramPrime
import RischTragerBronstein.Torsion.Conj

/-!
# Torsion at a prime for divisors at places with representatives (general curves)

`principal_at_prime_places`: `principal_at_primeG` for divisors supported at places `π` above
points `α_j`, each given by a representative root `ρ_π ∈ O⟦T⟧` of `F(α + Tᵉ, Y)` (ramification
`e_π`), the full branch systems above `α_j` consisting of the conjugates `ζ`-rotations of the
reparametrized representatives, over `K̄₀` and over `k̄`.

* `order_conj`: orders along `rot ζ (lsub s ρ)` are `s` times those along `ρ`;
* `lowerBd_of_map_lowerBd`: `ℤ_p`-integral expansions keep their lower bounds modulo `p`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Conj

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma lsub_root_fin (s : ℕ) (hs : 0 < s) (e : ℕ) (a : K) (ρ : LaurentSeries K)
    (hρ : (S.F.map (branchSub e a)).eval ρ = 0) :
    (S.F.map (branchSub (s * e) a)).eval (lsub s hs ρ) = 0 := by
  have hc : (lsub s hs).comp (branchSub (C := C) e a) = branchSub (s * e) a := by
    rw [lsub_comp_branchSub, mul_comm]
  rw [← hc, ← Polynomial.map_map, eval_map, eval₂_at_apply, hρ, map_zero]

/-- **Orders along conjugate reparametrized roots.** -/
lemma order_conj (ζ : K) (hζ : ζ ≠ 0) (s e : ℕ) (hs : 0 < s) (he : 0 < e) (a : K)
    (hζN : ζ ^ (s * e) = 1) (ρ : LaurentSeries K) (hρ : (S.F.map (branchSub e a)).eval ρ = 0)
    (hr : (S.F.map (branchSub (s * e) a)).eval (rot ζ hζ (lsub s hs ρ)) = 0) (f : C⟮S.x⟯⟮S.y⟯) :
    (S.embG (branchSub (s * e) a) (branchSub_injective _ (Nat.mul_pos hs he) a)
      (rot ζ hζ (lsub s hs ρ)) hr f).order =
      s * (S.embG (branchSub e a) (branchSub_injective e he a) ρ hρ f).order := by
  have hρ' := S.lsub_root_fin s hs e a ρ hρ
  rw [S.embG_congr' rfl _ (branchSub_injective _ (Nat.mul_pos hs he) a) rfl hr
      (rot_root ζ hζ (s * e) hζN a S.F _ hρ'),
    S.embG_rot ζ hζ (s * e) (Nat.mul_pos hs he) hζN a _ hρ', order_rot,
    S.embG_lsub_fin s hs e he a ρ hρ hρ', order_lsub']

end CurveData

end Conj

section Integral

variable {R : Type*} [CommRing R]

/-- `P ↦ P(a + Tᵉ)` into `R⟦T⟧`. -/
noncomputable def psSubR (e : ℕ) (a : R) : R[X] →+* PowerSeries R :=
  (Polynomial.coeToPowerSeries.ringHom (R := R)).comp (compRingHom (Polynomial.C a + X ^ e))

variable {K : Type*} [Field K]

lemma map_psSubR (φ : R →+* K) (e : ℕ) (a : R) (P : R[X]) :
    PowerSeries.map φ (psSubR e a P) = psSub (C := K) (K := K) e (φ a) (P.map φ) := by
  ext t
  simp only [psSubR, psSub, RingHom.comp_apply, coe_compRingHom, Algebra.algebraMap_self,
    Polynomial.mapRingHom_id, RingHom.id_apply, PowerSeries.coeff_map,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]
  rw [← coeff_map, Polynomial.map_comp]
  simp

lemma ofPS_map_psSubR (φ : R →+* K) (e : ℕ) (a : R) (P : R[X]) :
    ofPowerSeries ℤ K (PowerSeries.map φ (psSubR e a P)) = branchSub (C := K) (K := K) e (φ a) (P.map φ) :=
  by rw [map_psSubR, ← branchSub_eq_psSub]

/-- Evaluation commutes with the coefficient maps. -/
lemma eval_psSubR_map (φ : R →+* K) (e : ℕ) (a : R) (Q : R[X][X]) (ρ : PowerSeries R) :
    ofPowerSeries ℤ K (PowerSeries.map φ ((Q.map (psSubR e a)).eval ρ)) =
      ((Q.map (mapRingHom φ)).map (branchSub (C := K) (K := K) e (φ a))).eval
        (ofPowerSeries ℤ K (PowerSeries.map φ ρ)) := by
  rw [← RingHom.comp_apply (ofPowerSeries ℤ K) (PowerSeries.map φ), ← eval₂_at_apply,
    eval_map, eval₂_map, eval₂_map]
  congr 1
  refine RingHom.ext fun P ↦ ?_
  simp only [RingHom.comp_apply, coe_mapRingHom]
  exact ofPS_map_psSubR φ e a P

/-- **The expansion of `∑ cᵢ Bᵢ / D` along a representative over `R`.** -/
lemma expansion_eq (φ : R →+* K) {n : ℕ} (B : Fin n → R[X][X]) (D : R[X]) (c : Fin n → R[X])
    (e : ℕ) (a : R) (ρ : PowerSeries R) :
    ∑ i, branchSub (C := K) (K := K) e (φ a) ((c i).map φ) *
      basisSer (fun i ↦ (B i).map (mapRingHom φ)) (D.map φ) e (φ a)
        (ofPowerSeries ℤ K (PowerSeries.map φ ρ)) i =
      ofPowerSeries ℤ K (PowerSeries.map φ (((PsiC B c).map (psSubR e a)).eval ρ)) *
        (ofPowerSeries ℤ K (PowerSeries.map φ (psSubR e a D)))⁻¹ := by
  rw [eval_psSubR_map, ofPS_map_psSubR, PsiC_map, PsiC, Polynomial.map_sum, eval_finsetSum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [basisSer, Polynomial.map_mul, eval_mul, Polynomial.map_C, eval_C]
  ring

variable (φ : R →+* K) {n : ℕ} (B : Fin n → R[X][X]) (D : R[X]) (c : Fin n → R[X]) (e : ℕ) (a : R)
  (ρ : PowerSeries R)

lemma constantCoeff_psSubR (P : R[X]) (e : ℕ) (he : 0 < e) :
    PowerSeries.constantCoeff (psSubR e a P) = P.eval a := by
  rw [psSubR, RingHom.comp_apply, coe_compRingHom, Polynomial.coeToPowerSeries.ringHom_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, coeff_zero_eq_eval_zero,
    eval_comp]
  simp [zero_pow he.ne']

/-- **From a lower bound over `K` (injective `φ`) to divisibility over `R`.** -/
lemma dvd_of_lowerBd (hφ : Function.Injective φ) (he : 0 < e) (hD : φ (D.eval a) ≠ 0) (u : ℕ)
    (h : LowerBd (∑ i, branchSub (C := K) (K := K) e (φ a) ((c i).map φ) *
      basisSer (fun i ↦ (B i).map (mapRingHom φ)) (D.map φ) e (φ a)
        (ofPowerSeries ℤ K (PowerSeries.map φ ρ)) i) u) :
    (PowerSeries.X : PowerSeries R) ^ u ∣ ((PsiC B c).map (psSubR e a)).eval ρ := by
  rw [expansion_eq] at h
  set Dα := PowerSeries.map φ (psSubR e a D) with hDα
  have hDc : PowerSeries.constantCoeff Dα ≠ 0 := by
    rw [hDα, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_psSubR _ _ _ he]
    exact hD
  have hinv : (ofPowerSeries ℤ K Dα)⁻¹ = ofPowerSeries ℤ K Dα⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← map_mul, PowerSeries.mul_inv_cancel _ hDc, map_one]
  rw [hinv, ← map_mul, lowerBd_ofPS_iff] at h
  have h2 : (PowerSeries.X : PowerSeries K) ^ u ∣ PowerSeries.map φ (((PsiC B c).map (psSubR e a)).eval ρ) := by
    have := Dvd.dvd.mul_right h Dα
    rwa [mul_assoc, PowerSeries.inv_mul_cancel _ hDc, mul_one] at this
  rw [PowerSeries.X_pow_dvd_iff] at h2 ⊢
  intro t ht
  have := h2 t ht
  rw [PowerSeries.coeff_map] at this
  exact (map_eq_zero_iff φ hφ).mp this

/-- **From divisibility over `R` to a lower bound over `K`.** -/
lemma lowerBd_of_dvd (he : 0 < e) (hD : φ (D.eval a) ≠ 0) (u : ℕ)
    (h : (PowerSeries.X : PowerSeries R) ^ u ∣ ((PsiC B c).map (psSubR e a)).eval ρ) :
    LowerBd (∑ i, branchSub (C := K) (K := K) e (φ a) ((c i).map φ) *
      basisSer (fun i ↦ (B i).map (mapRingHom φ)) (D.map φ) e (φ a)
        (ofPowerSeries ℤ K (PowerSeries.map φ ρ)) i) u := by
  rw [expansion_eq]
  set Dα := PowerSeries.map φ (psSubR e a D) with hDα
  have hDc : PowerSeries.constantCoeff Dα ≠ 0 := by
    rw [hDα, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_psSubR _ _ _ he]
    exact hD
  have hinv : (ofPowerSeries ℤ K Dα)⁻¹ = ofPowerSeries ℤ K Dα⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← map_mul, PowerSeries.mul_inv_cancel _ hDc, map_one]
  rw [hinv, ← map_mul, lowerBd_ofPS_iff]
  refine Dvd.dvd.mul_right ?_ _
  rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  intro t ht
  rw [PowerSeries.coeff_map, h t ht, map_zero]

/-- Shifting a lower bound by the order `μ` of a denominator `Tᵘ V` (`V` a unit). -/
lemma lowerBd_shift_iff (t V : PowerSeries K) (hV : PowerSeries.constantCoeff V ≠ 0) (μ u : ℕ) :
    LowerBd (ofPowerSeries ℤ K t * (ofPowerSeries ℤ K (PowerSeries.X ^ μ * V))⁻¹) u ↔
      (PowerSeries.X : PowerSeries K) ^ (u + μ) ∣ t := by
  have hVinv : (ofPowerSeries ℤ K V)⁻¹ = ofPowerSeries ℤ K V⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← map_mul, PowerSeries.mul_inv_cancel _ hV, map_one]
  have hsinv : (single (μ : ℤ) (1 : K))⁻¹ = single (-(μ : ℤ)) 1 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [single_mul_single, add_neg_cancel, mul_one]; rfl
  have e1 : ofPowerSeries ℤ K t * (ofPowerSeries ℤ K (PowerSeries.X ^ μ * V))⁻¹ =
      single (-(μ : ℤ)) 1 * ofPowerSeries ℤ K (t * V⁻¹) := by
    rw [map_mul, map_mul, ofPowerSeries_X_pow, mul_inv, hsinv, hVinv]; ring
  have hu : IsUnit V⁻¹ := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    rw [PowerSeries.constantCoeff_inv]; exact (Ne.isUnit (inv_ne_zero hV)))
  rw [e1]
  constructor
  · intro h
    have h1 : (PowerSeries.X : PowerSeries K) ^ (u + μ) ∣ t * V⁻¹ := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro s hs
      have := h (s + -(μ : ℤ)) (by omega)
      rwa [coeff_single_mul_add, one_mul, ofPowerSeries_apply_coeff] at this
    obtain ⟨w, hw⟩ := h1
    refine ⟨w * V, ?_⟩
    have : t = t * V⁻¹ * V := by rw [mul_assoc, PowerSeries.inv_mul_cancel _ hV, mul_one]
    rw [this, hw]; ring
  · intro h k hk
    have h1 : (PowerSeries.X : PowerSeries K) ^ (u + μ) ∣ t * V⁻¹ := dvd_mul_of_dvd_left h _
    have ek : k = (k + μ) + -(μ : ℤ) := by ring
    rw [ek, coeff_single_mul_add, one_mul, LaurentSeries.coeff_ofPS]
    split_ifs with h0
    · exact (PowerSeries.X_pow_dvd_iff.mp h1) _ (by omega)
    · rfl

/-- **From a lower bound over `K` (injective `φ`) to divisibility over `R`**, with a denominator of
order `μ` at the representative. -/
lemma dvd_of_lowerBdM (hφ : Function.Injective φ) (μ : ℕ) (U : PowerSeries R)
    (hD : psSubR e a D = PowerSeries.X ^ μ * U) (hU : φ (PowerSeries.constantCoeff U) ≠ 0) (u : ℕ)
    (h : LowerBd (∑ i, branchSub (C := K) (K := K) e (φ a) ((c i).map φ) *
      basisSer (fun i ↦ (B i).map (mapRingHom φ)) (D.map φ) e (φ a)
        (ofPowerSeries ℤ K (PowerSeries.map φ ρ)) i) u) :
    (PowerSeries.X : PowerSeries R) ^ (u + μ) ∣ ((PsiC B c).map (psSubR e a)).eval ρ := by
  rw [expansion_eq, hD, map_mul, map_pow, PowerSeries.map_X,
    lowerBd_shift_iff _ _ (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hU)] at h
  rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  intro t ht
  have := h t ht
  rw [PowerSeries.coeff_map] at this
  exact (map_eq_zero_iff φ hφ).mp this

/-- **From divisibility over `R` to a lower bound over `K`**, with a denominator of order `μ`. -/
lemma lowerBd_of_dvdM (μ : ℕ) (U : PowerSeries R)
    (hD : psSubR e a D = PowerSeries.X ^ μ * U) (hU : φ (PowerSeries.constantCoeff U) ≠ 0) (u : ℕ)
    (h : (PowerSeries.X : PowerSeries R) ^ (u + μ) ∣ ((PsiC B c).map (psSubR e a)).eval ρ) :
    LowerBd (∑ i, branchSub (C := K) (K := K) e (φ a) ((c i).map φ) *
      basisSer (fun i ↦ (B i).map (mapRingHom φ)) (D.map φ) e (φ a)
        (ofPowerSeries ℤ K (PowerSeries.map φ ρ)) i) u := by
  rw [expansion_eq, hD, map_mul, map_pow, PowerSeries.map_X,
    lowerBd_shift_iff _ _ (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hU)]
  rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  intro t ht
  rw [PowerSeries.coeff_map, h t ht, map_zero]

/-- The denominator at `a + Tᵉ` from its order at `a`. -/
lemma psSubR_of_comp (he : 0 < e) (μ : ℕ) (Q : R[X]) (hQ : D.comp (X + Polynomial.C a) = X ^ μ * Q) :
    psSubR e a D = PowerSeries.X ^ (e * μ) * (Q.comp (X ^ e) : PowerSeries R) ∧
      PowerSeries.constantCoeff (Q.comp (X ^ e) : PowerSeries R) = Q.eval 0 := by
  have h1 : D.comp (Polynomial.C a + X ^ e) = (D.comp (X + Polynomial.C a)).comp (X ^ e) := by
    rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, add_comm]
  constructor
  · rw [psSubR, RingHom.comp_apply, coe_compRingHom]
    dsimp only
    rw [h1, hQ, Polynomial.mul_comp, Polynomial.X_pow_comp,
      ← pow_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X]
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
    simp [zero_pow he.ne']

end Integral

section Order

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Orders along conjugates from the representative expansion.** -/
lemma le_order_conj (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (cK : Fin S.F.natDegree → C[X])
    (hne : S.elt B D cK ≠ 0) (e : ℕ) (he : 0 < e) (a : C) (ρ : LaurentSeries C)
    (hρ : (S.F.map (branchSub (K := C) e a)).eval ρ = 0) (u : ℕ)
    (hLB : LowerBd (∑ i, branchSub (C := C) (K := C) e a (cK i) * basisSer B D e a ρ i) u)
    (s : ℕ) (hs : 0 < s) (ζ : K) (hζ : ζ ≠ 0) (hζN : ζ ^ (s * e) = 1)
    (hr : (S.F.map (branchSub (s * e) (algebraMap C K a))).eval
      (rot ζ hζ (lsub s hs (lmap (algebraMap C K) ρ))) = 0) :
    ((s * u : ℕ) : ℤ) ≤ (S.embG (branchSub (s * e) (algebraMap C K a))
      (branchSub_injective _ (Nat.mul_pos hs he) _) (rot ζ hζ (lsub s hs (lmap (algebraMap C K) ρ)))
      hr (S.elt B D cK)).order := by
  rw [S.order_conj ζ hζ s e hs he _ hζN _ (S.lmap_root e a ρ hρ) hr,
    S.embG_elt_lmap B D cK e he a ρ hρ]
  have hne' : lmap (algebraMap C K) (∑ i, branchSub (C := C) (K := C) e a (cK i) *
      basisSer B D e a ρ i) ≠ 0 := by
    rw [← S.embG_elt_lmap B D cK e he a ρ hρ]
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hne
  have h1 := le_order_of_lowerBd _ hne' u ((lowerBd_lmap_iff _ _ _).mpr hLB)
  push_cast
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

end CurveData

end Order

section PlacePrime

variable {O K₀ : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)] [Field K₀] [Algebra O K₀] [IsFractionRing O K₀]
variable {LK KK Lk kk : Type*} [Field LK] [Algebra K₀ LK] [Field KK] [Algebra K₀ KK] [IsAlgClosed KK]
  [Field Lk] [Algebra (IsLocalRing.ResidueField O) Lk] [Field kk]
  [Algebra (IsLocalRing.ResidueField O) kk] [IsAlgClosed kk]

local notation "𝕜" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "ι" => algebraMap O K₀

lemma sum_cast_eq {M : Type*} [AddCommMonoid M] {a b : ℕ} (h : a = b) (f : Fin b → M) :
    ∑ k : Fin a, f (Fin.cast h k) = ∑ k, f k :=
  Fintype.sum_equiv (finCongr h) _ _ fun _ ↦ rfl

set_option maxHeartbeats 4000000 in
/-- **Torsion at a prime, divisors at places with representatives.** -/
theorem principal_at_prime_places {ϖ : O} (hϖ : Irreducible ϖ) (F : O[X][X]) (hF : F.Monic)
    (SK : CurveData K₀ LK) (hSK : SK.F = F.map (mapRingHom ι)) (hBrK : SK.HasBranches KK)
    (hBIK : SK.HasBranchesInf KK)
    (Sk : CurveData 𝕜 Lk) (hSk : Sk.F = F.map (mapRingHom ρ)) (hBrk : Sk.HasBranches kk)
    (hBIk : Sk.HasBranchesInf kk)
    (hnk : Sk.F.natDegree = SK.F.natDegree) (hn : 0 < SK.F.natDegree)
    -- the integral basis
    (B : Fin SK.F.natDegree → O[X][X]) (D : O[X]) (hDm : D.Monic) (δ : Fin SK.F.natDegree → ℕ)
    (hB0 : B ⟨0, hn⟩ = Polynomial.C D) (hδ0 : δ ⟨0, hn⟩ = 0)
    (hδ : ∀ j : Fin SK.F.natDegree, (j : ℕ) ≠ 0 → 1 ≤ δ j)
    (hBK : SK.IsIntBasis KK (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) δ)
    (hBk : Sk.IsIntBasis kk (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) (D.map ρ)
      (fun j ↦ δ (Fin.cast hnk j)))
    -- the base fibres
    {g : ℕ} (hg : ∑ j, δ j + 1 = g + SK.F.natDegree)
    (x : Fin g → O) (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (y : Fin g → Fin SK.F.natDegree → O)
    (hsplit : ∀ i, F.map (evalRingHom (x i)) = ∏ k, (X - Polynomial.C (y i k)))
    (hFu : ∀ i k, IsUnit (Sup.evalW (derivative F) (x i) (y i k)))
    (hdet : ∀ i, IsUnit (Matrix.det (Matrix.of fun kk j ↦ Sup.evalW (B j) (x i) (y i kk))))
    (hDx : ∀ i, IsUnit (D.eval (x i)))
    (hNS : ∀ q : Fin SK.F.natDegree → 𝕜[X], (∀ j, q j ≠ 0 → (q j).natDegree + δ j ≤ g) →
      (∀ i (k : Fin SK.F.natDegree), (k : ℕ) ≠ 0 →
        Sup.evalW (PsiC (fun j ↦ (B j).map (mapRingHom ρ)) q) (ρ (x i)) (ρ (y i k)) = 0) →
      ∀ i, Sup.evalW (PsiC (fun j ↦ (B j).map (mapRingHom ρ)) q) (ρ (x i)) (ρ (y i ⟨0, hn⟩)) = 0)
    -- the points
    {J : Type*} [Fintype J] (α : J → O) (hα : ∀ j j', j ≠ j' → IsUnit (α j - α j'))
    (hαx : ∀ j i, IsUnit (α j - x i))
    (hDα : ∀ j, ∃ μ : ℕ, ∃ Q : O[X], D.comp (X + Polynomial.C (α j)) = X ^ μ * Q ∧ IsUnit (Q.eval 0))
    (N : J → ℕ) (hN : ∀ j, 0 < N j)
    -- the places and their representatives
    {P : Type*} [Fintype P] (pj : P → J) (e : P → ℕ) (he : ∀ π, 0 < e π) (ρO : P → PowerSeries O)
    (hρO : ∀ π, (F.map (psSubR (e π) (α (pj π)))).eval (ρO π) = 0)
    -- the branch systems over `K̄₀`
    (lK : J → List (LaurentSeries KK))
    (hlK : ∀ j, SK.F.map (branchSub (N j) (algebraMap K₀ KK (ι (α j)))) =
      ((lK j).map fun r ↦ X - Polynomial.C r).prod)
    (πK : J → LaurentSeries KK → P) (hπK : ∀ j r, r ∈ lK j → pj (πK j r) = j)
    (sK : J → LaurentSeries KK → ℕ) (hsK : ∀ j r, 0 < sK j r)
    (hNK : ∀ j r, r ∈ lK j → N j = sK j r * e (πK j r))
    (ζK : J → LaurentSeries KK → KK) (hζK0 : ∀ j r, ζK j r ≠ 0)
    (hζKN : ∀ j r, r ∈ lK j → ζK j r ^ N j = 1)
    (hconjK : ∀ j r, r ∈ lK j → r = rot (ζK j r) (hζK0 j r) (lsub (sK j r) (hsK j r)
      (lmap (algebraMap K₀ KK) (ofPowerSeries ℤ K₀ (PowerSeries.map ι (ρO (πK j r)))))))
    (hsurjK : ∀ π, ∃ j, ∃ r ∈ lK j, πK j r = π)
    -- the branch systems over `k̄`
    (lk : J → List (LaurentSeries kk))
    (hlk : ∀ j, Sk.F.map (branchSub (N j) (algebraMap 𝕜 kk (ρ (α j)))) =
      ((lk j).map fun r ↦ X - Polynomial.C r).prod)
    (πk : J → LaurentSeries kk → P) (hπk : ∀ j r, r ∈ lk j → pj (πk j r) = j)
    (sk : J → LaurentSeries kk → ℕ) (hsk : ∀ j r, 0 < sk j r)
    (hNk : ∀ j r, r ∈ lk j → N j = sk j r * e (πk j r))
    (ζk : J → LaurentSeries kk → kk) (hζk0 : ∀ j r, ζk j r ≠ 0)
    (hζkN : ∀ j r, r ∈ lk j → ζk j r ^ N j = 1)
    (hconjk : ∀ j r, r ∈ lk j → r = rot (ζk j r) (hζk0 j r) (lsub (sk j r) (hsk j r)
      (lmap (algebraMap 𝕜 kk) (ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO (πk j r)))))))
    -- the multiplicities
    (ΓP : P → ℕ) (cΓ : ℕ) (c' dΓ : J → ℕ) (hΓle : ∀ π, ΓP π ≤ c' (pj π) * e π)
    (hdK : ∀ j, ((lK j).map fun r ↦ sK j r * ΓP (πK j r)).sum = N j * dΓ j)
    (hdk : ∀ j, ((lk j).map fun r ↦ sk j r * ΓP (πk j r)).sum = N j * dΓ j)
    (hsumΓ : ∑ j, dΓ j = cΓ * SK.F.natDegree) (hle : ∀ j, dΓ j ≤ SK.F.natDegree * c' j)
    (hmP : ∑ π, (c' (pj π) * e π - ΓP π) = ∑ j, (SK.F.natDegree * c' j - dΓ j))
    -- the multiples
    (m s ℓ : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hℓ1 : 1 ≤ ℓ) (hℓ : IsUnit (ℓ : O))
    (γk : 𝕜⟮Sk.x⟯⟮Sk.y⟯) (hγk0 : γk ≠ 0)
    (hγk : Sk.DivGE (fun j ↦ ρ (α j)) N hN lk hlk
      (fun j r ↦ m * (sk j r * ΓP (πk j r))) (m * cΓ) γk)
    (Ξ : K₀⟮SK.x⟯⟮SK.y⟯) (hΞ0 : Ξ ≠ 0)
    (hΞ : SK.DivGE (fun j ↦ ι (α j)) N hN lK hlK
      (fun j r ↦ (s * ℓ) * (sK j r * ΓP (πK j r))) ((s * ℓ) * cΓ) Ξ) :
    ∃ γ : K₀⟮SK.x⟯⟮SK.y⟯, γ ≠ 0 ∧ SK.DivGE (fun j ↦ ι (α j)) N hN lK hlK
      (fun j r ↦ (m * s) * (sK j r * ΓP (πK j r))) ((m * s) * cΓ) γ := by
  classical
  have hιi : Function.Injective ι := IsFractionRing.injective O K₀
  have hunitk : ∀ z : O, IsUnit z → ρ z ≠ 0 := fun z hz ↦ (hz.map ρ).ne_zero
  -- the representatives over `K₀` and `𝕜`
  have hρK : ∀ π, (SK.F.map (branchSub (C := K₀) (K := K₀) (e π) (ι (α (pj π))))).eval
      (ofPowerSeries ℤ K₀ (PowerSeries.map ι (ρO π))) = 0 := fun π ↦ by
    rw [hSK, ← eval_psSubR_map, hρO, map_zero, map_zero]
  have hρk : ∀ π, (Sk.F.map (branchSub (C := 𝕜) (K := 𝕜) (e π) (ρ (α (pj π))))).eval
      (ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO π))) = 0 := fun π ↦ by
    rw [hSk, ← eval_psSubR_map, hρO, map_zero, map_zero]
  -- the representative expansions
  set σK : P → Fin SK.F.natDegree → LaurentSeries K₀ := fun π i ↦
    basisSer (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) (e π) (ι (α (pj π)))
      (ofPowerSeries ℤ K₀ (PowerSeries.map ι (ρO π))) i with hσKdef
  have hσ : ∀ π i, LowerBd (σK π i) 0 := by
    intro π i
    obtain ⟨j, r, hr, hπ⟩ := hsurjK π
    subst hπ
    have hj := hπK j r hr
    have hNjr := hNK j r hr
    have hζN : ζK j r ^ (sK j r * e (πK j r)) = 1 := by rw [← hNjr]; exact hζKN j r hr
    have hr' := rot_root (ζK j r) (hζK0 j r) (sK j r * e (πK j r)) hζN _ SK.F _
      (SK.lsub_root_fin (sK j r) (hsK j r) (e (πK j r)) _ _
        (SK.lmap_root (e (πK j r)) _ _ (hρK (πK j r))))
    have hreg := hBK.reg i (algebraMap K₀ KK (ι (α j))) (N j) (hN j).ne' (lK j) (hlK j) r hr
    have hg : branchSub (C := K₀) (N j) (algebraMap K₀ KK (ι (α j))) =
        branchSub (sK j r * e (πK j r)) (algebraMap K₀ KK (ι (α (pj (πK j r))))) := by
      rw [hNjr, hj]
    rw [SK.embG_congr' hg _ (branchSub_injective _ (Nat.mul_pos (hsK j r) (he _)) _)
        (hconjK j r hr) _ hr',
      SK.order_conj (ζK j r) (hζK0 j r) (sK j r) (e (πK j r)) (hsK j r) (he _) _ hζN _
        (SK.lmap_root (e (πK j r)) _ _ (hρK (πK j r))) hr',
      SK.embG_lmap_fnWQ (e (πK j r)) (he _) _ _ (hρK (πK j r))] at hreg
    have h0 : 0 ≤ (lmap (algebraMap K₀ KK) (σK (πK j r) i)).order := by
      have hs := hsK j r
      by_contra hneg
      push Not at hneg
      have : (sK j r : ℤ) * (lmap (algebraMap K₀ KK) (σK (πK j r) i)).order < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast hs) hneg
      exact absurd hreg (not_le.mpr this)
    exact (lowerBd_lmap_iff _ _ _).mp (lowerBd_of_le_order _ 0 h0)
  have hψne : ∀ cK : Fin SK.F.natDegree → K₀[X], cK ≠ 0 →
      SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) cK ≠ 0 :=
    fun cK hcK h ↦ hcK (CurveData.elt_eq_zero hBK.hD hBK.deg hBK.det cK h)
  -- orders over `K̄₀`
  have hordK : ∀ (cK : Fin SK.F.natDegree → K₀[X]), cK ≠ 0 → ∀ (j : J) (r : LaurentSeries KK)
      (hr : r ∈ lK j) (u : ℕ), LowerBd (∑ i, branchSub (K := K₀) (e (πK j r))
        (ι (α (pj (πK j r)))) (cK i) * σK (πK j r) i) u →
      ((sK j r * u : ℕ) : ℤ) ≤ (SK.embG (branchSub (N j) (algebraMap K₀ KK (ι (α j))))
        (branchSub_injective _ (hN j) _) r (SK.root_of_mem (hlK j) hr)
        (SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) cK)).order := by
    intro cK hcK j r hr u hLB
    have hj := hπK j r hr
    have hNjr := hNK j r hr
    have hζN : ζK j r ^ (sK j r * e (πK j r)) = 1 := by rw [← hNjr]; exact hζKN j r hr
    have hr' := rot_root (ζK j r) (hζK0 j r) (sK j r * e (πK j r)) hζN _ SK.F _
      (SK.lsub_root_fin (sK j r) (hsK j r) (e (πK j r)) _ _
        (SK.lmap_root (e (πK j r)) _ _ (hρK (πK j r))))
    have hbound := SK.le_order_conj (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) cK (hψne cK hcK)
      (e (πK j r)) (he _) (ι (α (pj (πK j r)))) _ (hρK (πK j r)) u hLB (sK j r) (hsK j r)
      (ζK j r) (hζK0 j r) hζN hr'
    have hg : branchSub (C := K₀) (N j) (algebraMap K₀ KK (ι (α j))) =
        branchSub (sK j r * e (πK j r)) (algebraMap K₀ KK (ι (α (pj (πK j r))))) := by
      rw [hNjr, hj]
    rw [SK.embG_congr' hg _ _ (hconjK j r hr) _ hr']
    exact hbound
  -- orders over `k̄`, through the `O`-integral expansions
  have hordk : ∀ (c : Fin SK.F.natDegree → O[X]), (¬ ∀ j, Polynomial.C ϖ ∣ c j) →
      ∀ (j : J) (r : LaurentSeries kk) (hr : r ∈ lk j) (u : ℕ),
      LowerBd (∑ i, branchSub (K := K₀) (e (πk j r)) (ι (α (pj (πk j r))))
        ((c i).map ι) * σK (πk j r) i) u →
      ((sk j r * u : ℕ) : ℤ) ≤ (Sk.embG (branchSub (N j) (algebraMap 𝕜 kk (ρ (α j))))
        (branchSub_injective _ (hN j) _) r (Sk.root_of_mem (hlk j) hr)
        (Sk.elt (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) (D.map ρ)
          (fun j ↦ (c (Fin.cast hnk j)).map ρ))).order := by
    intro c hc j r hr u hLB
    set π := πk j r with hπ
    have hj := hπk j r hr
    have hNjr := hNk j r hr
    obtain ⟨j0, hj0⟩ : ∃ j0, ¬ Polynomial.C ϖ ∣ c j0 := by
      by_contra h; push Not at h; exact hc h
    have hck : (fun i ↦ (c (Fin.cast hnk i)).map ρ) ≠ 0 := by
      intro h
      apply hj0
      rw [Jac.C_dvd_iff_map hϖ]
      have := congrFun h (Fin.cast hnk.symm j0)
      simpa using this
    have hne : Sk.elt (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) (D.map ρ)
        (fun j ↦ (c (Fin.cast hnk j)).map ρ) ≠ 0 :=
      fun h ↦ hck (CurveData.elt_eq_zero hBk.hD hBk.deg hBk.det _ h)
    obtain ⟨μ, Q, hQ, hQu⟩ := hDα (pj π)
    obtain ⟨hDU, hU0⟩ := psSubR_of_comp D (e π) (α (pj π)) (he π) μ Q hQ
    have hX := dvd_of_lowerBdM ι B D c (e π) (α (pj π)) (ρO π) hιi (e π * μ) _ hDU
      (by rw [hU0]; exact (map_ne_zero_iff _ hιi).mpr hQu.ne_zero) u hLB
    have hLBk := lowerBd_of_dvdM ρ B D c (e π) (α (pj π)) (ρO π) (e π * μ) _ hDU
      (by rw [hU0]; exact hunitk _ hQu) u hX
    have hLBk' : LowerBd (∑ i : Fin Sk.F.natDegree, branchSub (C := 𝕜) (K := 𝕜) (e π) (ρ (α (pj π)))
        ((c (Fin.cast hnk i)).map ρ) * basisSer (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ))
          (D.map ρ) (e π) (ρ (α (pj π))) (ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO π))) i) u := by
      have := sum_cast_eq hnk (fun i : Fin SK.F.natDegree ↦ branchSub (C := 𝕜) (K := 𝕜) (e π)
        (ρ (α (pj π))) ((c i).map ρ) * basisSer (fun j ↦ (B j).map (mapRingHom ρ)) (D.map ρ) (e π)
          (ρ (α (pj π))) (ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO π))) i)
      simp only [basisSer] at this ⊢
      rw [this]
      simpa only [basisSer] using hLBk
    have hζN : ζk j r ^ (sk j r * e π) = 1 := by rw [← hNjr]; exact hζkN j r hr
    have hr' := rot_root (ζk j r) (hζk0 j r) (sk j r * e π) hζN _ Sk.F _
      (Sk.lsub_root_fin (sk j r) (hsk j r) (e π) _ _ (Sk.lmap_root (e π) _ _ (hρk π)))
    have hbound := Sk.le_order_conj (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) (D.map ρ)
      (fun j ↦ (c (Fin.cast hnk j)).map ρ) hne (e π) (he _) (ρ (α (pj π))) _ (hρk π) u hLBk'
      (sk j r) (hsk j r) (ζk j r) (hζk0 j r) hζN hr'
    have hg : branchSub (C := 𝕜) (N j) (algebraMap 𝕜 kk (ρ (α j))) =
        branchSub (sk j r * e π) (algebraMap 𝕜 kk (ρ (α (pj π)))) := by
      rw [hNjr, hj]
    rw [Sk.embG_congr' hg _ _ (hconjk j r hr) _ hr']
    exact hbound
  -- the multiplicity relations
  have hΓK : ∀ j r, r ∈ lK j → ((c' j * N j : ℕ) : ℤ) - ((sK j r * ΓP (πK j r) : ℕ) : ℤ) =
      (sK j r : ℤ) * ((c' (pj (πK j r)) * e (πK j r) - ΓP (πK j r) : ℕ) : ℤ) := by
    intro j r hr
    rw [hNK j r hr, hπK j r hr] at *
    have := hΓle (πK j r)
    rw [hπK j r hr] at this
    push_cast [Nat.cast_sub this]
    ring
  have hΓk : ∀ j r, r ∈ lk j → ((c' j * N j : ℕ) : ℤ) - ((sk j r * ΓP (πk j r) : ℕ) : ℤ) =
      (sk j r : ℤ) * ((c' (pj (πk j r)) * e (πk j r) - ΓP (πk j r) : ℕ) : ℤ) := by
    intro j r hr
    rw [hNk j r hr, hπk j r hr] at *
    have := hΓle (πk j r)
    rw [hπk j r hr] at this
    push_cast [Nat.cast_sub this]
    ring
  exact principal_at_primeG hϖ F hF SK hSK hBrK hBIK Sk hSk hBrk hBIk hnk hn B D hDm δ hB0 hδ0 hδ
    hBK hBk hg x hx y hsplit hFu hdet hDx hNS α hα hαx N hN lK hlK
    (fun j r ↦ sK j r * ΓP (πK j r)) N hN lk hlk (fun j r ↦ sk j r * ΓP (πk j r)) cΓ c' dΓ hdK hdk
    hsumΓ hle pj e he (fun π ↦ c' (pj π) * e π - ΓP π) hmP σK hσ πK sK hΓK hordK πk sk hΓk hordk
    m s ℓ hm hs hℓ1 hℓ γk hγk0 hγk Ξ hΞ0 hΞ

end PlacePrime

end Curves
