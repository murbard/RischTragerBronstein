import RischTragerBronstein.Torsion.CertBasis2

/-!
# Integral bases above infinity: certificates (any characteristic)

* `order_transfer_inf`: branch systems above infinity are related by `T ↦ Tᴺ`;
* `basisCheckInf`: along the certified system above infinity (`certInf_spec`), the expansions
  of `T^{N δⱼ} wⱼ` are power series (from `InvOK k (δⱼ + deg D) 0 Bⱼ`) whose first `N`
  coefficients form a matrix with a left inverse;
* `basisCheckInf_spec`: pole orders `≤ δⱼ` along every system above infinity, and the reduced
  (local independence) condition at infinity.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors CPoly Sup

section Defs

variable {F : Type*} [Field F] [DecidableEq F]

/-- The expansion coefficients of `T^{N δ} B/D` above infinity. -/
def serInf (B : BPoly F) (Dc : CPoly F) (k δ N prec : ℕ) (wt : CPoly F) : CPoly F :=
  divTrunc (bivEval (invB B k (δ + (Dc.length - 1))) (shiftC 0 N) wt)
    (compC (reflectC (Dc.length - 1) Dc) (shiftC 0 N)) prec

/-- The matrix above infinity. -/
def matInf (Bc : List (BPoly F)) (Dc : CPoly F) (k : ℕ) (δ : List ℕ) (c : BranchCert F)
    (r j : ℕ) : F :=
  (serInf (Bc.getD j []) Dc k (δ.getD j 0) c.N c.prec (c.ys.getD (r / c.N) [])).getD (r % c.N) 0

/-- `InvOK` as a Boolean. -/
def invOKb (k D : ℕ) (W : BPoly F) : Bool :=
  (List.range W.length).all fun j ↦ decide ((W.getD j []).length + k * j ≤ D + 1)

/-- **The basis check above infinity.** -/
def basisCheckInf (n k : ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (δ : List ℕ) (c : BranchCert F)
    (Lm : List (List F)) : Bool :=
  decide (0 < Dc.length) && decide (Dc.getD (Dc.length - 1) 0 ≠ 0) && decide (c.N ≤ c.prec) &&
    ((List.range n).all fun j ↦ invOKb k (δ.getD j 0 + (Dc.length - 1)) (Bc.getD j [])) &&
    leftInvCheck Lm (matInf Bc Dc k δ c) (n * c.N) n

/-- The syntactic pole order: the least `δ` with `invOKb k (δ + deg D) B`. -/
def synDelta (k : ℕ) (Dc : CPoly F) (B : BPoly F) : ℕ :=
  (List.range B.length).foldr (fun i m ↦ max m ((B.getD i []).length + k * i - 1 - (Dc.length - 1))) 0

/-- The matrix above infinity, shifted to the true pole orders `δ ≤ synDelta`. -/
def matInfS (Bc : List (BPoly F)) (Dc : CPoly F) (k : ℕ) (δ : List ℕ) (c : BranchCert F)
    (r j : ℕ) : F :=
  (serInf (Bc.getD j []) Dc k (synDelta k Dc (Bc.getD j [])) c.N c.prec (c.ys.getD (r / c.N) [])).getD
    (c.N * (synDelta k Dc (Bc.getD j []) - δ.getD j 0) + r % c.N) 0

/-- **The semantic basis check above infinity**: the expansions of `Bⱼ/(D xᵟʲ)` (computed through
the syntactic order `synDelta`) have no negative powers, and their leading terms are independent. -/
def basisCheckInfS (n k : ℕ) (Bc : List (BPoly F)) (Dc : CPoly F) (δ : List ℕ) (c : BranchCert F)
    (Lm : List (List F)) : Bool :=
  decide (0 < Dc.length) && decide (Dc.getD (Dc.length - 1) 0 ≠ 0) &&
    ((List.range n).all fun j ↦
      invOKb k (synDelta k Dc (Bc.getD j []) + (Dc.length - 1)) (Bc.getD j []) &&
      decide (δ.getD j 0 ≤ synDelta k Dc (Bc.getD j [])) &&
      decide (c.N * (synDelta k Dc (Bc.getD j []) - δ.getD j 0) + c.N ≤ c.prec) &&
      (List.range n).all fun m ↦ (List.range (c.N * (synDelta k Dc (Bc.getD j []) - δ.getD j 0))).all
        fun t ↦ decide ((serInf (Bc.getD j []) Dc k (synDelta k Dc (Bc.getD j [])) c.N c.prec
          (c.ys.getD m [])).getD t 0 = 0)) &&
    leftInvCheck Lm (matInfS Bc Dc k δ c) (n * c.N) n

lemma invOKb_spec {k D : ℕ} {W : BPoly F} (h : invOKb k D W = true) : InvOK k D 0 W := by
  simp only [invOKb, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  intro j hj
  simpa using h j hj

end Defs

section Transfer

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Transfer between branch systems above infinity** (char-free). -/
lemma order_transfer_inf (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (l l' : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (hl' : S.F.map (infSub N') = (l'.map fun r ↦ X - Polynomial.C r).prod)
    (r' : LaurentSeries K) (hr' : r' ∈ l') :
    ∃ r, ∃ hr : r ∈ l, ∀ u : C⟮S.x⟯⟮S.y⟯,
      (N : ℤ) * (S.embG (infSub N') (infSub_injective N' hN') r' (S.root_of_mem hl' hr') u).order =
      N' * (S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr) u).order := by
  have hc1 : (lsub N hN).comp (infSub (C := C) (K := K) N') = infSub (N * N') := by
    rw [lsub_comp_infSub, mul_comm]
  have hc2 : (lsub N' hN').comp (infSub (C := C) (K := K) N) = infSub (N * N') := by
    rw [lsub_comp_infSub]
  have hroot : (S.F.map (infSub (C := C) (K := K) (N * N'))).eval (lsub N hN r') = 0 := by
    rw [← hc1, ← Polynomial.map_map, eval_map, eval₂_at_apply, S.root_of_mem hl' hr', map_zero]
  have hsplit : S.F.map (infSub (C := C) (K := K) (N * N')) =
      ((l.map (lsub N' hN')).map fun r ↦ X - Polynomial.C r).prod := by
    rw [← hc2, ← Polynomial.map_map, hl, Polynomial.map_list_prod, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun r _ ↦ ?_
    simp
  rw [hsplit, eval_list_prod, List.prod_eq_zero_iff, List.map_map] at hroot
  obtain ⟨s, hs, hs0⟩ := List.mem_map.mp hroot
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at hs0
  refine ⟨r, hr, fun u ↦ ?_⟩
  have hinj1 : Function.Injective ((lsub N hN).comp (infSub (C := C) (K := K) N')) := by
    rw [hc1]; exact infSub_injective _ (Nat.mul_pos hN hN')
  have hinj2 : Function.Injective ((lsub N' hN').comp (infSub (C := C) (K := K) N)) := by
    rw [hc2]; exact infSub_injective _ (Nat.mul_pos hN hN')
  have hroot1 : (S.F.map ((lsub N hN).comp (infSub (C := C) (K := K) N'))).eval
      (lsub N hN r') = 0 := by
    rw [← Polynomial.map_map, eval_map, eval₂_at_apply, S.root_of_mem hl' hr', map_zero]
  have hroot2 : (S.F.map ((lsub N' hN').comp (infSub (C := C) (K := K) N))).eval
      (lsub N' hN' r) = 0 := by
    rw [← Polynomial.map_map, eval_map, eval₂_at_apply, S.root_of_mem hl hr, map_zero]
  have e1 := congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ u)
    (S.embG_comp (lsub N hN) (infSub N') (infSub_injective N' hN') hinj1 r'
      (S.root_of_mem hl' hr') hroot1)
  have e2 := congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ u)
    (S.embG_comp (lsub N' hN') (infSub N) (infSub_injective N hN) hinj2 r
      (S.root_of_mem hl hr) hroot2)
  have e3 : S.embG ((lsub N hN).comp (infSub (C := C) (K := K) N')) hinj1 (lsub N hN r') hroot1 u =
      S.embG ((lsub N' hN').comp (infSub (C := C) (K := K) N)) hinj2 (lsub N' hN' r) hroot2 u :=
    congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ u)
      (S.embG_congr' (by rw [hc1, hc2]) _ _ hs0 _ _)
  simp only [RingHom.comp_apply] at e1 e2
  have := congrArg HahnSeries.order (e1.trans (e3.trans e2.symm))
  rwa [order_lsub', order_lsub'] at this


variable {F : Type*} [Field F] [DecidableEq F]

/-- **The basis above infinity from its certificate.** -/
theorem basisCheckInf_spec (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = S.F.natDegree) (k : ℕ)
    (hok : InvOK k (k * S.F.natDegree) 0 Fc) (hmon' : (toB (invB Fc k (k * S.F.natDegree))).Monic)
    (hn' : (toB (invB Fc k (k * S.F.natDegree))).natDegree = S.F.natDegree)
    (Bc : List (BPoly F)) (Dc : CPoly F) (δ : List ℕ) (c : BranchCert F)
    (hcert : certCheck (invB Fc k (k * S.F.natDegree)) S.F.natDegree 0 c = true)
    (Lm : List (List F)) (hchk : basisCheckInf S.F.natDegree k Bc Dc δ c Lm = true) :
    (∀ (j : Fin S.F.natDegree) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K)
      (hr : r ∈ l), LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
        (S.root_of_mem hl hr)
        (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀)))
        (-((N * δ.getD j 0 : ℕ) : ℤ))) ∧
    (∃ N, ∃ hN : 0 < N, ∃ r : Fin S.F.natDegree → LaurentSeries K,
      ∃ hs : S.F.map (infSub N) = ∏ k, (X - Polynomial.C (r k)),
        S.LocIndepInf (fun j ↦ S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀))
          ((toPoly Dc).map ψ₀)) (fun j ↦ δ.getD j 0) N hN r hs) := by
  classical
  simp only [basisCheckInf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hchk
  obtain ⟨⟨⟨⟨hQ, hQl⟩, hprec⟩, hokB⟩, hinv⟩ := hchk
  have hN : 0 < c.N := by
    simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at hcert
    exact hcert.1.1.1
  have hD : toPoly Dc ≠ 0 := by
    intro h
    apply hQl
    rw [← coeff_toPoly, h, Polynomial.coeff_zero]
  have hD' : (toPoly Dc).map ψ₀ ≠ 0 := (Polynomial.map_ne_zero_iff ψ₀.injective).mpr hD
  obtain ⟨w, hw, hsplit⟩ := certInf_spec (K := K) Fc S.F.natDegree hmon hdeg k hok hmon' hn' c
    hcert ψ₀
  rw [← hSF] at hsplit
  set Y : Fin S.F.natDegree → LaurentSeries K :=
    fun m ↦ single (-((k * c.N : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K (w m) with hYdef
  have hroot : ∀ m, (S.F.map (infSub c.N)).eval (Y m) = 0 := fun m ↦ by
    rw [hsplit, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ m) (by simp [hYdef])
  -- the expansions along the certified system
  have hrep : ∀ (j m : Fin S.F.natDegree), ∃ V : PowerSeries K,
      S.embG (infSub c.N) (infSub_injective c.N hN) (Y m) (hroot m)
        (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀)) =
        single (-((c.N * δ.getD j 0 : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K V ∧
      ∀ t < c.prec, PowerSeries.coeff t V = algebraMap C K (ψ₀
        ((serInf (Bc.getD j []) Dc k (δ.getD j 0) c.N c.prec (c.ys.getD m [])).getD t 0)) := by
    intro j m
    obtain ⟨V, hV, hVt⟩ := S.phi_repr_inf Fc ψ₀ hSF k c.N hN (w m) (hroot m) (c.ys.getD m [])
      c.prec (hw m) _ (Bc.getD j []) Dc (S.fnWQ_mul _ _ hD') (δ.getD j 0 + (Dc.length - 1))
      (invOKb_spec (hokB j j.2)) hQ hQl
    refine ⟨V, ?_, fun t ht ↦ ?_⟩
    · rw [hV]
      congr 2
      push_cast
      ring
    · have := (PowerSeries.X_pow_dvd_iff.mp hVt) t ht
      rw [map_sub, coeff_thetaT, sub_eq_zero] at this
      rw [this]; rfl
  have hlist : S.F.map (infSub c.N) = ((List.ofFn Y).map fun r ↦ X - Polynomial.C r).prod := by
    rw [hsplit, List.map_ofFn, List.prod_ofFn]; rfl
  have hlb0 : ∀ (j m : Fin S.F.natDegree), -((c.N * δ.getD j 0 : ℕ) : ℤ) ≤
      (S.embG (infSub c.N) (infSub_injective c.N hN) (Y m) (hroot m)
        (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))).order := by
    intro j m
    obtain ⟨V, hV, -⟩ := hrep j m
    rw [hV]
    by_cases hV0 : V = 0
    · rw [hV0, map_zero, mul_zero, HahnSeries.order_zero]
      exact neg_nonpos.mpr (by positivity)
    rw [HahnSeries.order_mul (by simp) ((map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr
      hV0), HahnSeries.order_single one_ne_zero]
    have : 0 ≤ (ofPowerSeries ℤ K V).order := order_nonneg_of_lowerBd' _
      (fun i hi ↦ LaurentSeries.coeff_ofPS_neg _ hi)
    linarith
  refine ⟨fun j N' hN' l hl r hr ↦ ?_, c.N, hN, Y, hsplit, fun cc hcc ↦ ?_⟩
  · obtain ⟨r0, hr0, htr⟩ := S.order_transfer_inf c.N N' hN (Nat.pos_of_ne_zero hN') _ l hlist hl r hr
    obtain ⟨m, rfl⟩ := List.mem_ofFn.mp hr0
    have h1 := htr (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))
    have h2 := hlb0 j m
    refine lowerBd_of_le_order _ _ ?_
    have hNc : (0 : ℤ) < c.N := by exact_mod_cast hN
    have : (c.N : ℤ) * (-((N' * δ.getD j 0 : ℕ) : ℤ)) ≤ c.N * (S.embG (infSub N')
        (infSub_injective N' (Nat.pos_of_ne_zero hN')) r (S.root_of_mem hl hr)
        (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))).order := by
      rw [h1]
      push_cast at h2 ⊢
      have hN'0 : (0 : ℤ) ≤ N' := by positivity
      nlinarith
    exact le_of_mul_le_mul_left this hNc
  · refine eq_zero_of_leftInvCheck ((algebraMap C K).comp ψ₀) hinv cc fun r hr ↦ ?_
    have hk : r / c.N < S.F.natDegree := (Nat.div_lt_iff_lt_mul hN).mpr hr
    have ht : r % c.N < c.N := Nat.mod_lt _ hN
    have h := hcc ⟨r / c.N, hk⟩ ((r % c.N : ℕ) : ℤ) (by exact_mod_cast ht)
    rw [HahnSeries.coeff_sum] at h
    simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    obtain ⟨V, hV, hVt⟩ := hrep j ⟨r / c.N, hk⟩
    rw [hV, ← mul_assoc, HahnSeries.single_mul_single, one_mul]
    rw [show ((c.N * δ.getD j 0 : ℕ) : ℤ) + -((c.N * δ.getD j 0 : ℕ) : ℤ) = 0 by ring]
    rw [show (single (0 : ℤ) (1 : K)) = 1 from rfl, one_mul, coeff_ofPS, if_pos (by positivity),
      Int.toNat_natCast, hVt _ (by omega), mul_comm]
    rfl

theorem basisCheckInfS_spec (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = S.F.natDegree) (k : ℕ)
    (hok : InvOK k (k * S.F.natDegree) 0 Fc) (hmon' : (toB (invB Fc k (k * S.F.natDegree))).Monic)
    (hn' : (toB (invB Fc k (k * S.F.natDegree))).natDegree = S.F.natDegree)
    (Bc : List (BPoly F)) (Dc : CPoly F) (δ : List ℕ) (c : BranchCert F)
    (hcert : certCheck (invB Fc k (k * S.F.natDegree)) S.F.natDegree 0 c = true)
    (Lm : List (List F)) (hchk : basisCheckInfS S.F.natDegree k Bc Dc δ c Lm = true) :
    (∀ (j : Fin S.F.natDegree) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K)
      (hr : r ∈ l), LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
        (S.root_of_mem hl hr)
        (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀)))
        (-((N * δ.getD j 0 : ℕ) : ℤ))) ∧
    (∃ N, ∃ hN : 0 < N, ∃ r : Fin S.F.natDegree → LaurentSeries K,
      ∃ hs : S.F.map (infSub N) = ∏ k, (X - Polynomial.C (r k)),
        S.LocIndepInf (fun j ↦ S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀))
          ((toPoly Dc).map ψ₀)) (fun j ↦ δ.getD j 0) N hN r hs) := by
  classical
  simp only [basisCheckInfS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hchk
  obtain ⟨⟨⟨hQ, hQl⟩, hjs⟩, hinv⟩ := hchk
  set sy : ℕ → ℕ := fun j ↦ synDelta k Dc (Bc.getD j []) with hsy
  have hN : 0 < c.N := by
    simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at hcert
    exact hcert.1.1.1
  have hD : toPoly Dc ≠ 0 := by
    intro h
    apply hQl
    rw [← coeff_toPoly, h, Polynomial.coeff_zero]
  have hD' : (toPoly Dc).map ψ₀ ≠ 0 := (Polynomial.map_ne_zero_iff ψ₀.injective).mpr hD
  obtain ⟨w, hw, hsplit⟩ := certInf_spec (K := K) Fc S.F.natDegree hmon hdeg k hok hmon' hn' c
    hcert ψ₀
  rw [← hSF] at hsplit
  set Y : Fin S.F.natDegree → LaurentSeries K :=
    fun m ↦ single (-((k * c.N : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K (w m) with hYdef
  have hroot : ∀ m, (S.F.map (infSub c.N)).eval (Y m) = 0 := fun m ↦ by
    rw [hsplit, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ m) (by simp [hYdef])
  -- the expansions along the certified system
  have hrep : ∀ (j m : Fin S.F.natDegree), ∃ V : PowerSeries K,
      S.embG (infSub c.N) (infSub_injective c.N hN) (Y m) (hroot m)
        (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀)) =
        single (-((c.N * δ.getD j 0 : ℕ) : ℤ)) (1 : K) * ofPowerSeries ℤ K V ∧
      ∀ t < c.N, PowerSeries.coeff t V = algebraMap C K (ψ₀ (matInfS Bc Dc k δ c
        (m * c.N + t) j)) := by
    intro j m
    obtain ⟨⟨⟨hokj, hle⟩, hpr⟩, hlow⟩ := hjs j j.2
    obtain ⟨V, hV, hVt⟩ := S.phi_repr_inf Fc ψ₀ hSF k c.N hN (w m) (hroot m) (c.ys.getD m [])
      c.prec (hw m) _ (Bc.getD j []) Dc (S.fnWQ_mul _ _ hD') (sy j + (Dc.length - 1))
      (invOKb_spec hokj) hQ hQl
    have hVc : ∀ t < c.prec, PowerSeries.coeff t V = algebraMap C K (ψ₀
        ((serInf (Bc.getD j []) Dc k (sy j) c.N c.prec (c.ys.getD m [])).getD t 0)) := by
      intro t ht
      have := (PowerSeries.X_pow_dvd_iff.mp hVt) t ht
      rw [map_sub, coeff_thetaT, sub_eq_zero] at this
      rw [this]; rfl
    set sh := c.N * (sy j - δ.getD j 0) with hsh
    have hdvd : (PowerSeries.X : PowerSeries K) ^ sh ∣ V := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro t ht
      rw [hVc t (by omega), hlow m m.2 t ht, map_zero, map_zero]
    obtain ⟨V', hV'⟩ := hdvd
    refine ⟨V', ?_, fun t ht ↦ ?_⟩
    · rw [hV, hV', map_mul, HahnSeries.ofPowerSeries_X_pow, ← mul_assoc,
        HahnSeries.single_mul_single, one_mul]
      congr 2
      rw [hsh]
      have : δ.getD j 0 ≤ sy j := hle
      push_cast [Nat.cast_sub this]
      ring
    · have h1 : PowerSeries.coeff (sh + t) V = PowerSeries.coeff t V' := by
        rw [hV', PowerSeries.coeff_X_pow_mul']
        rw [if_pos (by omega), Nat.add_sub_cancel_left]
      rw [← h1, hVc _ (by omega), matInfS]
      congr 3
      · rw [show (m * c.N + t) / c.N = m by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt ht, zero_add]]
      · rw [Nat.add_comm (↑m * c.N) t, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  have hlist : S.F.map (infSub c.N) = ((List.ofFn Y).map fun r ↦ X - Polynomial.C r).prod := by
    rw [hsplit, List.map_ofFn, List.prod_ofFn]; rfl
  have hlb0 : ∀ (j m : Fin S.F.natDegree), -((c.N * δ.getD j 0 : ℕ) : ℤ) ≤
      (S.embG (infSub c.N) (infSub_injective c.N hN) (Y m) (hroot m)
        (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))).order := by
    intro j m
    obtain ⟨V, hV, -⟩ := hrep j m
    rw [hV]
    by_cases hV0 : V = 0
    · rw [hV0, map_zero, mul_zero, HahnSeries.order_zero]
      exact neg_nonpos.mpr (by positivity)
    rw [HahnSeries.order_mul (by simp) ((map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr
      hV0), HahnSeries.order_single one_ne_zero]
    have : 0 ≤ (ofPowerSeries ℤ K V).order := order_nonneg_of_lowerBd' _
      (fun i hi ↦ LaurentSeries.coeff_ofPS_neg _ hi)
    linarith
  refine ⟨fun j N' hN' l hl r hr ↦ ?_, c.N, hN, Y, hsplit, fun cc hcc ↦ ?_⟩
  · obtain ⟨r0, hr0, htr⟩ := S.order_transfer_inf c.N N' hN (Nat.pos_of_ne_zero hN') _ l hlist hl r hr
    obtain ⟨m, rfl⟩ := List.mem_ofFn.mp hr0
    have h1 := htr (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))
    have h2 := hlb0 j m
    refine lowerBd_of_le_order _ _ ?_
    have hNc : (0 : ℤ) < c.N := by exact_mod_cast hN
    have : (c.N : ℤ) * (-((N' * δ.getD j 0 : ℕ) : ℤ)) ≤ c.N * (S.embG (infSub N')
        (infSub_injective N' (Nat.pos_of_ne_zero hN')) r (S.root_of_mem hl hr)
        (S.fnWQ ((toB (Bc.getD j [])).map (mapRingHom ψ₀)) ((toPoly Dc).map ψ₀))).order := by
      rw [h1]
      push_cast at h2 ⊢
      have hN'0 : (0 : ℤ) ≤ N' := by positivity
      nlinarith
    exact le_of_mul_le_mul_left this hNc
  · refine eq_zero_of_leftInvCheck ((algebraMap C K).comp ψ₀) hinv cc fun r hr ↦ ?_
    have hk : r / c.N < S.F.natDegree := (Nat.div_lt_iff_lt_mul hN).mpr hr
    have ht : r % c.N < c.N := Nat.mod_lt _ hN
    have h := hcc ⟨r / c.N, hk⟩ ((r % c.N : ℕ) : ℤ) (by exact_mod_cast ht)
    rw [HahnSeries.coeff_sum] at h
    simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    obtain ⟨V, hV, hVt⟩ := hrep j ⟨r / c.N, hk⟩
    rw [hV, ← mul_assoc, HahnSeries.single_mul_single, one_mul]
    rw [show ((c.N * δ.getD j 0 : ℕ) : ℤ) + -((c.N * δ.getD j 0 : ℕ) : ℤ) = 0 by ring]
    rw [show (single (0 : ℤ) (1 : K)) = 1 from rfl, one_mul, coeff_ofPS, if_pos (by positivity),
      Int.toNat_natCast, hVt _ ht, mul_comm]
    rw [show r / c.N * c.N + r % c.N = r from Nat.div_add_mod' r c.N]
    rfl

end CurveData

end Transfer

end Curves
