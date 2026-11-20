import RischTragerBronstein.Mixed.NKExactTLVGExistsM
import RischTragerBronstein.Mixed.NKMultiRShape
import RischTragerBronstein.Mixed.NKMultiGaugeR

/-!
# `exactTLVG` answers for curves with several slopes at infinity, ramified or not

**`exactTLVG_exists_multiR`**: as `exactTLVG_exists_multi`, for `θⁿ + ∑ aᵢ(t) θⁱ = 0` over a
logarithmic level whose places at infinity are rational with any rational slopes `sₖ/eₖ`
(`multiShapeRC`: several Newton segments with residual polynomials `c Z^{lo} ∏ (Z^{eₖ} − γ)`). The
gauge is `multi_gauge_ram`'s `A` (twisted window values of the rescaled basis along representatives
of the places, rational by Galois descent); the gauged limit is diagonal, `(t/e) γ′/γ`, and the
limit system is non-degenerate: a solution `c` of the homogeneous system gives `z = U c` with
`z′ = −T z`, and `y` would make `w/z` (`w = U y`) an antiderivative of `η`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 8000000 in
/-- **`exactTLVG` answers for a suitable basis of a curve with several slopes at infinity, ramified
or not.** -/
theorem exactTLVG_exists_multiR (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m}
    (hk : ks m = .prim η) (htr : Transcendental (T.F m) (T.ts m))
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h1.of_succ).sem η)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    ∃ (Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (C Ci : List (List (LC m)))
      (dg : List (FRep (LC m))),
      (exactTLVG Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti f gs).isSome := by
  classical
  set h0 := h1.of_succ with hh0
  set C := T.codeVals m h0 with hC
  letI := diffRat
  letI := diffAlgRat (L := L)
  letI dC : Differential C := differentialOfDerivClosed (T.derivClosed_codeVals m h0)
  letI dCL : DifferentialAlgebra C L := differentialAlgebra_of_derivClosed (T.derivClosed_codeVals m h0)
  set K := AlgebraicClosure C with hKdef
  have hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′ := fun c ↦ deriv_algebraMap c
  set SQ := T.nkCurveQE m h1 Pp qE csE sE tE s2E t2E hck θ hθ with hSQ
  set ηQ : C := T.cv m h0 η with hηQ
  have hx : SQ.x′ = aeval SQ.x (Polynomial.C ηQ) := by
    rw [aeval_C]
    change (T.ts m)′ = _
    rw [T.deriv_ts_L m h0 hm hk]
    rfl
  obtain ⟨q, hq, hn0, hePos, hgcd, hdecS, hcne, hΓ, hbd, hres, htop, hchain, hlast⟩ :=
    T.multiShapeR_spec m h0 Pp segs hms
  set n := Pp.length with hn
  have hSQn : SQ.F.natDegree = n := polyF_natDegree _ _
  set ι := T.codeIncl m h0 with hι
  have hιi := T.codeIncl_injective m h0
  have hFF : (T.nkF m h0 Pp).natDegree = n := polyF_natDegree _ _
  have hcoefι : ∀ i, (SQ.F.coeff i).map ι = (T.nkF m h0 Pp).coeff i := fun i ↦ by
    rw [← T.map_nkFQ m h0 Pp, Polynomial.coeff_map]; rfl
  have hcoeffZe : ∀ (P : C[X]) (e : ℕ) (j : ℤ), ι (coeffZe P e j) = coeffZe (P.map ι) e j :=
    fun P e j ↦ by
      unfold coeffZe coeffZ
      split_ifs <;> simp [Polynomial.coeff_map]
  -- the segment data over the code values
  set eQ : Fin (q + 1) → ℕ := fun k ↦ (segs.getD k (segRD Fc ks m)).1 with heQ
  set sQ : Fin (q + 1) → ℤ := fun k ↦ (segs.getD k (segRD Fc ks m)).2.1 with hsQ
  set K0Q : Fin (q + 1) → ℤ := fun k ↦ (segs.getD k (segRD Fc ks m)).2.2.1 with hK0Q
  set cQ : Fin (q + 1) → C := fun k ↦ T.cv m h0 (segs.getD k (segRD Fc ks m)).2.2.2.1 with hcQ
  set ΓQ : Fin (q + 1) → List C := fun k ↦ (segs.getD k (segRD Fc ks m)).2.2.2.2.map (T.cv m h0)
    with hΓQ
  set loQ : Fin (q + 1) → ℕ := fun k ↦ loRC segs k with hloQ
  have hΓι : ∀ k, (ΓQ k).map ι = (segs.getD k (segRD Fc ks m)).2.2.2.2.map (T.MP m h0).sem := by
    intro k
    rw [hΓQ, List.map_map]
    rfl
  have hcQ0 : ∀ k, cQ k ≠ 0 := fun k h0' ↦ hcne k (by
    rw [← T.codeIncl_cv m h0, show T.cv m h0 _ = cQ k from rfl, h0', map_zero])
  have hΓQ0 : ∀ k, (ΓQ k).Nodup ∧ (0 : C) ∉ ΓQ k := by
    intro k
    refine ⟨List.Nodup.of_map ι (by rw [hΓι]; exact (hΓ k).1), fun h0' ↦ (hΓ k).2 ?_⟩
    rw [← hΓι]
    exact List.mem_map.mpr ⟨0, h0', map_zero ι⟩
  have hbdQ : ∀ k, ∀ i ≤ SQ.F.natDegree, SQ.F.coeff i ≠ 0 →
      (eQ k : ℤ) * (SQ.F.coeff i).natDegree + i * sQ k ≤ K0Q k := by
    intro k i hi hai
    have := hbd k i (by rw [hFF]; rw [hSQn] at hi; exact hi) (by
      rw [← hcoefι]; exact (Polynomial.map_ne_zero_iff hιi).mpr hai)
    rwa [← hcoefι, natDegree_map_eq_of_injective hιi] at this
  have hresQ : ∀ k, ∑ i ∈ Finset.range (SQ.F.natDegree + 1),
      Polynomial.C (coeffZe (SQ.F.coeff i) (eQ k) (K0Q k - i * sQ k)) * X ^ i =
        Polynomial.C (cQ k) * X ^ (loQ k) *
          ((ΓQ k).map fun γ ↦ X ^ (eQ k) - Polynomial.C γ).prod := by
    intro k
    apply Polynomial.map_injective ι hιi
    have h1 := hres k
    rw [hFF, ← hSQn] at h1
    have hL : (∑ i ∈ Finset.range (SQ.F.natDegree + 1),
        Polynomial.C (coeffZe (SQ.F.coeff i) (eQ k) (K0Q k - i * sQ k)) * X ^ i).map ι =
        ∑ i ∈ Finset.range (SQ.F.natDegree + 1), Polynomial.C (coeffZe ((T.nkF m h0 Pp).coeff i)
          (segs.getD k (segRD Fc ks m)).1
          ((segs.getD k (segRD Fc ks m)).2.2.1 - i * (segs.getD k (segRD Fc ks m)).2.1)) * X ^ i := by
      rw [Polynomial.map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hcoeffZe,
        hcoefι]
    have hR : (Polynomial.C (cQ k) * X ^ (loQ k) *
        ((ΓQ k).map fun γ ↦ X ^ (eQ k) - Polynomial.C γ).prod).map ι =
        Polynomial.C ((T.MP m h0).sem (segs.getD k (segRD Fc ks m)).2.2.2.1) * X ^ (loRC segs k) *
          (((segs.getD k (segRD Fc ks m)).2.2.2.2.map (T.MP m h0).sem).map
            fun γ ↦ X ^ (segs.getD k (segRD Fc ks m)).1 - Polynomial.C γ).prod := by
      rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_list_prod, ← hΓι, List.map_map, List.map_map]
      congr 2
      rw [hΓQ]
      simp only [List.map_map]
      refine List.map_congr_left fun g _ ↦ ?_
      simp [heQ]
    rw [hL, hR]
    exact h1
  have htopQ : loQ 0 + eQ 0 * (ΓQ 0).length = SQ.F.natDegree := by
    rw [hSQn, ← hFF, ← htop, hΓQ, List.length_map, List.length_map]
    rfl
  have hchainQ : ∀ k : Fin q, loQ k.castSucc = loQ k.succ + eQ k.succ * (ΓQ k.succ).length := by
    intro k
    show loRC segs k.castSucc = loRC segs k.succ + _ * _
    rw [hchain k, hΓQ, List.length_map, List.length_map]
  have hF0 : SQ.F.coeff 0 ≠ 0 := by
    intro h0'
    have h1 := congrArg (Polynomial.eval 0) (hresQ (Fin.last q))
    rw [show loQ (Fin.last q) = 0 from hlast, pow_zero, mul_one, eval_mul, eval_C, eval_list_prod,
      eval_finset_sum, Finset.sum_eq_single 0 (fun b _ hb ↦ by
        rw [eval_mul, eval_pow, eval_X, zero_pow hb, mul_zero])
      (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h), eval_mul, eval_C, pow_zero, eval_one,
      mul_one, h0'] at h1
    have hz : coeffZe (0 : C[X]) (eQ (Fin.last q)) (K0Q (Fin.last q) - (0 : ℕ) * sQ (Fin.last q)) = 0 := by
      unfold coeffZe coeffZ
      split_ifs <;> simp
    rw [hz] at h1
    symm at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hcQ0 _ h2
    · obtain ⟨v, hv, hv0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h2)
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hv
      simp only [eval_sub, eval_pow, eval_X, eval_C] at hv0
      rw [zero_pow (hePos (Fin.last q)).ne', zero_sub, neg_eq_zero] at hv0
      exact (hΓQ0 _).2 (hv0 ▸ hγ)
  obtain ⟨w, r, S0, Pm, hwB, hrw, hredw, hindw, hS00, hsq, hder, hdeg⟩ :=
    SQ.exists_nkBasisG (K := K) ηQ hx hK
  -- a branch system above infinity with `eₖ ∣ N`
  obtain ⟨Nb, hNb, lb, -, hlb⟩ := SQ.hasBranchesInf (K := K)
  have hNb' := Nat.pos_of_ne_zero hNb
  set E : ℕ := ∏ k, eQ k with hE
  have hE0 : 0 < E := Finset.prod_pos fun k _ ↦ hePos k
  set N : ℕ := Nb * E with hNdef
  have hN : 0 < N := Nat.mul_pos hNb' hE0
  set lr := lb.map (lsub E hE0) with hlr
  have hl : SQ.F.map (infSub N) = (lr.map fun r ↦ X - Polynomial.C r).prod :=
    branchSys_lsub SQ.F Nb E hE0 lb hlb
  have hedQ : ∀ k, eQ k ∣ N := fun k ↦
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) _
  set σ : Fin (q + 1) → ℤ := fun k ↦ ((N / eQ k : ℕ) : ℤ) * sQ k with hσ
  have hNe : ∀ k, ((N / eQ k : ℕ) : ℤ) * eQ k = N := fun k ↦ by
    exact_mod_cast Nat.div_mul_cancel (hedQ k)
  have hsA : StrictAnti σ := by
    rw [Fin.strictAnti_iff_succ_lt]
    intro k
    have h1 : sQ k.succ * eQ k.castSucc < sQ k.castSucc * eQ k.succ := hdecS k
    have hp : (0 : ℤ) < eQ k.castSucc * eQ k.succ := by
      have := hePos k.castSucc; have := hePos k.succ; positivity
    refine lt_of_mul_lt_mul_right ?_ hp.le
    have e1 : σ k.succ * (eQ k.castSucc * eQ k.succ) = N * (sQ k.succ * eQ k.castSucc) := by
      rw [hσ]; dsimp only; rw [← hNe k.succ]; ring
    have e2 : σ k.castSucc * (eQ k.castSucc * eQ k.succ) = N * (sQ k.castSucc * eQ k.succ) := by
      rw [hσ]; dsimp only; rw [← hNe k.castSucc]; ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left h1 (by exact_mod_cast hN)
  obtain ⟨hord, huniq, -⟩ := multi_hdataR (K := K) N hN SQ.F SQ.monic hF0 lr hl eQ hePos hedQ sQ
    hsA K0Q cQ hcQ0 loQ ΓQ hΓQ0 hbdQ hresQ htopQ hchainQ hlast
  have hl0 : ∀ r ∈ lr, r ≠ 0 := by
    intro r hr h0
    subst h0
    have h1 : (SQ.F.map (infSub (K := K) N)).eval 0 = 0 := by
      rw [hl, eval_list_prod]
      exact List.prod_eq_zero (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨0, hr, rfl⟩, by simp⟩)
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at h1
    exact hF0 ((infSub_injective N hN) (by rw [h1, map_zero]))
  -- the ramification and the slope numerator of an order
  have hσinj := hsA.injective
  set eF : ℤ → ℕ := fun o ↦ if h : ∃ k, o = -σ k then eQ (Classical.choose h) else 1 with heF
  set spF : ℤ → ℤ := fun o ↦ if h : ∃ k, o = -σ k then sQ (Classical.choose h) else 0 with hspF
  have hFk : ∀ k, eF (-σ k) = eQ k ∧ spF (-σ k) = sQ k := by
    intro k
    have hex : ∃ k', -σ k = -σ k' := ⟨k, rfl⟩
    have hc : Classical.choose hex = k := hσinj (neg_inj.mp (Classical.choose_spec hex)).symm
    simp only [heF, hspF, dif_pos hex, hc, and_self]
  have hdataR : ∀ r ∈ lr, 0 < eF r.order ∧ eF r.order ∣ N ∧
      Int.gcd (spF r.order) (eF r.order) = 1 ∧ r.order = -((N / eF r.order : ℕ) * spF r.order) := by
    intro r hr
    obtain ⟨k, hk, -⟩ := hord r hr
    have hk' : r.order = -σ k := hk
    rw [hk', (hFk k).1, (hFk k).2]
    exact ⟨hePos k, hedQ k, hgcd k, rfl⟩
  have hceR : ∀ r ∈ lr, (r.coeff r.order) ^ eF r.order ∈ Set.range (algebraMap C K) := by
    intro r hr
    obtain ⟨k, hk, γ, -, hγ⟩ := hord r hr
    have hk' : r.order = -σ k := hk
    have he' : eF r.order = eQ k := by rw [hk']; exact (hFk k).1
    rw [he', hγ]
    exact ⟨γ, rfl⟩
  obtain ⟨Ag, Td, hAg0, hAg', hTd, -⟩ := SQ.multi_gauge_ram (K := K) ηQ hx hK N hN lr hl hl0 eF spF
    hdataR hceR huniq w r hrw hredw S0 hS00 Pm hder hdeg
  obtain ⟨A, B, Ai, Bi, hB, hBi, hwA, hTTi, hTiT⟩ := SQ.exists_coordMats w hindw
  set σ : Equiv.Perm (Fin SQ.F.natDegree) := Equiv.refl _ with hσdef
  set RF : Fin SQ.F.natDegree → (T.F m)[X] := fun i ↦ (X ^ (r (σ i) + 1) * S0).map ι with hRF
  set PF : Fin SQ.F.natDegree → Fin SQ.F.natDegree → (T.F m)[X] := fun i j ↦
    (Curves.CurveData.pqV ηQ r Pm S0 (σ i) (σ j)).map ι with hPF
  have hRF0 : ∀ i, RF i ≠ 0 := fun i ↦
    (Polynomial.map_ne_zero_iff hιi).mpr (mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00)
  have hPRF : ∀ i j, (PF i j).natDegree ≤ (RF i).natDegree := fun i j ↦ by
    rw [hPF, hRF]; dsimp only
    rw [natDegree_map_eq_of_injective hιi, natDegree_map_eq_of_injective hιi]
    exact hdeg (σ i) (σ j)
  -- the curve polynomial `P`
  set P := nkPC Fc ks m Pp with hPdef
  set M1 := T.MPr (m + 1) h1 with hM1
  have hNP : P.length - 1 = SQ.F.natDegree := by rw [length_nkPC, hSQn]
  have hPlen : P.length = SQ.F.natDegree + 1 := by have := length_nkPC (Fc := Fc) (ks := ks) m Pp; omega
  have hP : T.evθ m h1 θ P = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hPn : P.getD SQ.F.natDegree (MOr Fc ks (m + 1)).zero = (MOr Fc ks (m + 1)).one := by
    have hl : (Pp.map (polyCode Fc ks m)).length = SQ.F.natDegree := by rw [List.length_map]; exact hSQn.symm
    rw [hPdef, nkPC, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl,
      Nat.sub_self]
    rfl
  have hPc : (MOr Fc ks (m + 1)).isZero ((MOr Fc ks (m + 1)).add
      (P.getD (P.length - 1) (MOr Fc ks (m + 1)).zero)
      ((MOr Fc ks (m + 1)).neg (MOr Fc ks (m + 1)).one)) = true := by
    rw [hNP, hPn]
    refine (M1.isZero_iff _).mpr ?_
    rw [M1.sem_add, M1.sem_neg, add_neg_cancel]
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0 := by
    rw [hNP, hSQn]; exact T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ
  have hPdeg : (GPoly.toPoly M1 P).natDegree = SQ.F.natDegree := by
    rw [hM1, hPdef, T.toPoly_nkPC m h1 Pp, polyF_natDegree]; exact hSQn.symm
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [hM1, hPdef, T.toPoly_nkPC m h1 Pp]; exact polyF_monic _ _
  have hcop := T.sep_P_const m h1 P hPm SQ.F.natDegree hPdeg θ hP (by rw [← hNP]; exact hind)
  obtain ⟨dθ, hd⟩ := Option.isSome_iff_exists.mp (dThetaC_isSome M1 P hcop)
  -- the candidate
  have hnpos : 0 < SQ.F.natDegree := by rw [hSQn]; exact hn0
  set fi : ℕ → Fin SQ.F.natDegree := fun i ↦ if h : i < SQ.F.natDegree then ⟨i, h⟩ else ⟨0, hnpos⟩ with hfidef
  have hfi : ∀ i (h : i < SQ.F.natDegree), fi i = ⟨i, h⟩ := fun i h ↦ by simp [hfidef, h]
  set Tc : List (List (LC (m + 1))) := (List.range SQ.F.natDegree).map fun i ↦ (List.range SQ.F.natDegree).map fun k ↦
    T.cvFrac (A (σ (fi i)) (fi k)) (B (σ (fi i)) (fi k)) with hTc
  set Ti : List (List (LC (m + 1))) := (List.range SQ.F.natDegree).map fun k ↦ (List.range SQ.F.natDegree).map fun j ↦
    T.cvFrac (Ai (fi k) (σ (fi j))) (Bi (fi k) (σ (fi j))) with hTi
  set r' : ℕ → ℤ := fun i ↦ (r (σ (fi i)) : ℤ) with hr'
  have sT : ∀ i (hi : i < SQ.F.natDegree) k (hk : k < SQ.F.natDegree),
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
        aeval SQ.x (A (σ ⟨i, hi⟩) ⟨k, hk⟩) / aeval SQ.x (B (σ ⟨i, hi⟩) ⟨k, hk⟩) := fun i hi k hk ↦ by
    rw [hTc, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ hk, T.coe_sem_cvFrac,
      hfi i hi, hfi k hk]
    rfl
  have sTi : ∀ k (hk : k < SQ.F.natDegree) j (hj : j < SQ.F.natDegree),
      ((M1.sem ((Ti.getD k []).getD j (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
        aeval SQ.x (Ai ⟨k, hk⟩ (σ ⟨j, hj⟩)) / aeval SQ.x (Bi ⟨k, hk⟩ (σ ⟨j, hj⟩)) := fun k hk j hj ↦ by
    rw [hTi, NestTower.getD_range_map _ _ hk, NestTower.getD_range_map _ _ hj, T.coe_sem_cvFrac,
      hfi k hk, hfi j hj]
    rfl
  have hfin : ∀ (g : ℕ → L), ∑ k ∈ Finset.range SQ.F.natDegree, g k = ∑ k : Fin SQ.F.natDegree, g k := fun g ↦
    (Fin.sum_univ_eq_sum_range g SQ.F.natDegree).symm
  have hok : prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true ∧
      prodIdC Fc ks m (P.length - 1) (fun i j ↦ (Ti.getD i []).getD j (MOr Fc ks (m + 1)).zero)
      (fun i j ↦ (Tc.getD i []).getD j (MOr Fc ks (m + 1)).zero) = true := by
    rw [hNP]
    refine ⟨T.prodIdC_of_sem m h1 SQ.F.natDegree _ _ fun i hi j hj ↦ ?_, T.prodIdC_of_sem m h1 SQ.F.natDegree _ _ fun i hi j hj ↦ ?_⟩
    · apply Subtype.ext
      push_cast
      rw [hfin (fun k ↦ ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) *
        ((M1.sem ((Ti.getD k []).getD j (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L))]
      rw [Finset.sum_congr rfl fun k _ ↦ by rw [sT i hi k k.2, sTi k k.2 j hj]]
      have := hTTi (σ ⟨i, hi⟩) (σ ⟨j, hj⟩)
      rw [this]
      by_cases hij : i = j
      · subst hij; simp
      · have : σ ⟨i, hi⟩ ≠ σ ⟨j, hj⟩ := fun h ↦ hij (by have := σ.injective h; simpa using this)
        simp [this, hij]
    · apply Subtype.ext
      push_cast
      rw [hfin (fun k ↦ ((M1.sem ((Ti.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) *
        ((M1.sem ((Tc.getD k []).getD j (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L))]
      rw [Finset.sum_congr rfl fun k _ ↦ by rw [sTi i hi k k.2, sT k k.2 j hj]]
      have := hTiT ⟨i, hi⟩ ⟨j, hj⟩
      rw [← Equiv.sum_comp σ] at this
      rw [this]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Fin.ext_iff]
  -- the derivation matrix
  set Mval : ℕ → ℕ → T.F (m + 1) := fun i j ↦
    T.phi m ((Pm (σ (fi i)) (σ (fi j))).map ι) / T.phi m (S0.map ι) with hMvaldef
  have hS0x : aeval SQ.x S0 ≠ 0 := fun h ↦ hS00 ((transcendental_iff.mp SQ.htr) _ h)
  have hMvalL : ∀ i j, (Mval i j : L) =
      aeval SQ.x (Pm (σ (fi i)) (σ (fi j))) / aeval SQ.x S0 := fun i j ↦ by
    rw [hMvaldef]
    push_cast
    rw [coe_phi, coe_phi, T.aeval_map_codeIncl, T.aeval_map_codeIncl]
    rfl
  have hwL : ∀ i (hi : i < SQ.F.natDegree), ∑ k ∈ Finset.range SQ.F.natDegree,
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k =
      (w (σ ⟨i, hi⟩) : L) := fun i hi ↦ by
    rw [hfin, hwA (σ ⟨i, hi⟩)]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [sT i hi k k.2]; rfl
  have hderL : ∀ a, (w a : L)′ * aeval SQ.x S0 = ∑ j, aeval SQ.x (Pm a j) * (w j : L) := by
    intro a
    have := congrArg Subtype.val (hder a)
    simpa [CurveData.polyE] using this
  have hMval : ∀ i < P.length - 1, (∑ k ∈ Finset.range (P.length - 1),
      ((M1.sem ((Tc.getD i []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k)′ =
      ∑ j ∈ Finset.range (P.length - 1), (Mval i j : L) *
        ∑ k ∈ Finset.range (P.length - 1), ((M1.sem ((Tc.getD j []).getD k
          (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k := by
    rw [hNP]
    intro i hi
    rw [hwL i hi, hfin]
    have hR : ∑ j : Fin SQ.F.natDegree, (Mval i j : L) * ∑ k ∈ Finset.range SQ.F.natDegree,
        ((M1.sem ((Tc.getD j []).getD k (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ k =
        ∑ j : Fin SQ.F.natDegree, aeval SQ.x (Pm (σ ⟨i, hi⟩) (σ j)) / aeval SQ.x S0 *
          (w (σ j) : L) :=
      Finset.sum_congr rfl fun j _ ↦ by
        rw [hwL j j.2, hMvalL, hfi i hi, hfi j j.2]
    rw [hR, ← mul_div_cancel_right₀ ((w (σ ⟨i, hi⟩) : L)′) hS0x, hderL, ← Equiv.sum_comp σ,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hsqF : Squarefree (S0.map ι) :=
    ((PerfectField.separable_iff_squarefree.mpr hsq).map (f := ι)).squarefree
  have hsq' : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A S : (T.F m)[X], Squarefree S ∧
      Mval i j = T.phi m A / T.phi m S := fun i _ j _ ↦
    ⟨(Pm (σ (fi i)) (σ (fi j))).map ι, S0.map ι, hsqF, rfl⟩
  -- the limit matrix
  set Λ : ℕ → ℕ → T.F m := fun i j ↦
    (PF (fi i) (fi j)).coeff (RF (fi i)).natDegree / (RF (fi i)).leadingCoeff with hΛdef
  have hτ : T.tau m ≠ 0 := T.tau_ne_zero m htr
  have hφS0 : T.phi m (S0.map ι) ≠ 0 := fun h0' ↦
    hsqF.ne_zero (T.phi_injective htr (by rw [h0', map_zero]))
  have hσfi : ∀ i (hi : i < SQ.F.natDegree) j (hj : j < SQ.F.natDegree),
      σ (fi i) = σ (fi j) ↔ i = j := fun i hi j hj ↦ by
    rw [hfi i hi, hfi j hj, σ.injective.eq_iff, Fin.mk.injEq]
  have hprop : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A' B' : (T.F m)[X], B' ≠ 0 ∧
      A'.natDegree ≤ B'.natDegree ∧ A'.coeff B'.natDegree / B'.leadingCoeff = Λ i j ∧
      Mval i j * T.tau m ^ (r' j - r' i) - (if i = j then (r' i : T.F (m + 1)) *
        T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem η)) / T.tau m else 0) =
        T.phi m A' / T.phi m B' := by
    rw [hNP]
    intro i hi j hj
    refine ⟨PF (fi i) (fi j), RF (fi i), hRF0 _, hPRF _ _, rfl, ?_⟩
    have hX : T.phi m X = T.tau m := rfl
    simp only [hMvaldef, hPF, hRF, hr', Curves.CurveData.pqV, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, map_mul, map_sub, map_pow, hX]
    rw [zpow_sub₀ hτ, zpow_natCast, zpow_natCast]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, Polynomial.map_mul, Polynomial.map_C, map_mul, map_natCast, map_pow,
        Polynomial.map_pow, Polynomial.map_X, hX]
      have hc : T.phi m (Polynomial.C (ι ηQ)) = T.phi m (Polynomial.C ((T.MP m h0).sem η)) := rfl
      rw [Polynomial.map_natCast, map_natCast, hc]
      push_cast
      field_simp
      ring
    · have hij' : ¬σ (fi i) = σ (fi j) := fun h ↦ hij ((hσfi i hi j hj).mp h)
      simp only [hij, hij', if_false, sub_zero, Polynomial.map_zero, map_zero]
      field_simp
      ring
  -- the limit in terms of the code values
  set ΛQ : Fin SQ.F.natDegree → Fin SQ.F.natDegree → C := fun i j ↦
    (Curves.CurveData.pqV ηQ r Pm S0 i j).coeff (X ^ (r i + 1) * S0).natDegree /
      (X ^ (r i + 1) * S0).leadingCoeff with hΛQ
  have hΛι : ∀ i j : Fin SQ.F.natDegree, Λ i j = ι (ΛQ i j) := by
    intro i j
    rw [hΛdef]; dsimp only
    rw [hfi i i.2, hfi j j.2, hPF, hRF]; dsimp only
    rw [coeff_map, natDegree_map_eq_of_injective hιi, leadingCoeff_map_of_injective hιi, map_div₀]
    rfl
  -- the gauge `U = Agᵀ`
  set U : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) C := Ag.transpose with hU
  have hUdet : U.det ≠ 0 := by rw [hU, Matrix.det_transpose]; exact hAg0
  set Ui : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) C := U⁻¹ with hUi
  have hUUi : U * Ui = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hUdet)
  have hUiU : Ui * U = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hUdet)
  -- `U F = U′ + D U` with `F a b = Λ b a`, `D = diag(Td)`
  have hUF : ∀ a b : Fin SQ.F.natDegree, ∑ k, U a k * ΛQ b k = (U a b)′ + Td a * U a b := by
    intro a b
    rw [hU, Matrix.transpose_apply, hAg' b a]
    have : ∑ k, Ag.transpose a k * ΛQ b k = ∑ j, ΛQ b j * Ag j a :=
      Finset.sum_congr rfl fun k _ ↦ by rw [Matrix.transpose_apply]; ring
    rw [this]
    ring
  set Cl : List (List (LC m)) := (List.range SQ.F.natDegree).map fun a ↦
    (List.range SQ.F.natDegree).map fun b ↦ T.cvCode (U (fi a) (fi b)) with hCl
  set Cil : List (List (LC m)) := (List.range SQ.F.natDegree).map fun a ↦
    (List.range SQ.F.natDegree).map fun b ↦ T.cvCode (Ui (fi a) (fi b)) with hCil
  have hcg : ∀ a b : Fin SQ.F.natDegree, (T.MP m h0).sem (cgV Fc ks m Cl a b) = ι (U a b) :=
    fun a b ↦ by
      rw [cgV, hCl, NestTower.getD_range_map _ _ a.2, NestTower.getD_range_map _ _ b.2,
        T.sem_cvCode, hfi a a.2, hfi b b.2]
  have hcig : ∀ a b : Fin SQ.F.natDegree, (T.MP m h0).sem (cgV Fc ks m Cil a b) = ι (Ui a b) :=
    fun a b ↦ by
      rw [cgV, hCil, NestTower.getD_range_map _ _ a.2, NestTower.getD_range_map _ _ b.2,
        T.sem_cvCode, hfi a a.2, hfi b b.2]
  have hinv : invOKG Fc ks m (P.length - 1) Cl Cil = true := by
    rw [hNP]
    refine T.invOKG_of h0 Cl Cil (fun i j ↦ ?_) (fun i j ↦ ?_)
    · simp only [hcg, hcig, ← map_mul, ← map_sum]
      have := congrFun (congrFun hUUi i) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      rw [this]; split_ifs <;> simp
    · simp only [hcg, hcig, ← map_mul, ← map_sum]
      have := congrFun (congrFun hUiU i) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      rw [this]; split_ifs <;> simp
  have hιd : ∀ z : C, (ι z)′ = ι (z′) := fun z ↦ rfl
  -- the gauged limit is `diag(Td)`
  have hgC : ∀ a b : Fin SQ.F.natDegree, ∑ k, ∑ l, U a k * ΛQ l k * Ui l b -
      ∑ k, (U a k)′ * Ui k b = if a = b then Td a else 0 := by
    intro a b
    have e1 : ∑ k, ∑ l, U a k * ΛQ l k * Ui l b = ∑ l, ((U a l)′ + Td a * U a l) * Ui l b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [← hUF a l, Finset.sum_mul]
    rw [e1]
    simp only [add_mul, Finset.sum_add_distrib, add_sub_cancel_left]
    have := congrFun (congrFun hUUi a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [show ∑ l, Td a * U a l * Ui l b = Td a * ∑ l, U a l * Ui l b by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ ↦ by ring, this]
    split_ifs <;> simp
  have hgaugeT : ∀ a b : Fin SQ.F.natDegree, gaugeM
      (fun i j : Fin SQ.F.natDegree ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cl i j))
      (fun i j : Fin SQ.F.natDegree ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cil i j))
      (fun a b : Fin SQ.F.natDegree ↦ Λ b a) a b = if a = b then ι (Td a) else 0 := by
    intro a b
    simp only [gaugeM, hcg, hcig, hΛι, hιd, ← map_mul, ← map_sum, ← map_sub, hgC]
    split_ifs <;> simp
  have htri : ∀ a b : Fin (P.length - 1), b < a → gaugeM
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cl i j))
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cil i j))
      (fun a b : Fin (P.length - 1) ↦ Λ b a) a b = 0 := by
    rw [hNP]
    intro a b hba
    rw [hgaugeT a b, if_neg (ne_of_lt hba).symm]
  -- the diagonal data
  choose qa γa hγa0 _ hTda using hTd
  set dgL : List (FRep (LC m)) := (List.range SQ.F.natDegree).map fun a ↦
    ⟨(MO Fc ks m).zero, [(mcst Fc ks m (qa (fi a)), T.cvCode (γa (fi a)))]⟩ with hdgL
  have hdgAt : ∀ a (ha : a < SQ.F.natDegree), dgAt Fc ks m dgL a =
      ⟨(MO Fc ks m).zero, [(mcst Fc ks m (qa (fi a)), T.cvCode (γa (fi a)))]⟩ := fun a ha ↦ by
    rw [dgAt, hdgL, NestTower.getD_range_map _ _ ha]
  have hdgAt' : ∀ a, SQ.F.natDegree ≤ a → dgAt Fc ks m dgL a = ⟨(MO Fc ks m).zero, []⟩ :=
    fun a ha ↦ by rw [dgAt, List.getD_eq_default _ _ (by simpa [hdgL] using ha)]
  have hdiag : ∀ a : Fin (P.length - 1), gaugeM
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cl i j))
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cil i j))
      (fun a b : Fin (P.length - 1) ↦ Λ b a) a a =
        (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (dgAt Fc ks m dgL a)) := by
    rw [hNP]
    intro a
    rw [hgaugeT a a, if_pos rfl, hdgAt a a.2, sem_fCode, hfi a a.2]
    simp only [Fin.eta, logSumV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      (T.MP m h1.of_succ).sem_zero, Derivation.map_zero, zero_add, T.sem_mcst m h0,
      Differential.logDeriv, T.sem_cvCode]
    rw [hTda, map_mul, map_div₀, map_ratCast, ← hιd]
  have hokd : ∀ i, ∀ cw ∈ (dgAt Fc ks m dgL i).logs, ((T.MP m h1.of_succ).sem cw.1)′ = 0 := by
    intro i cw hcw
    by_cases hi : i < SQ.F.natDegree
    · rw [hdgAt i hi] at hcw
      simp only [List.mem_singleton] at hcw
      rw [hcw, T.sem_mcst m h0]
      exact T.deriv_ratCast _
    · rw [hdgAt' i (by omega)] at hcw
      simp at hcw
  -- non-degeneracy: `z = U c` has `z′ = −D z`, and `w/z` (`w = U y`) would integrate `η`
  have hnd : ∀ c : Fin (P.length - 1) → T.F m, c ≠ 0 →
      (∀ a : Fin (P.length - 1), (c a)′ + ∑ b : Fin (P.length - 1), Λ b a * c b = 0) →
      ¬ ∃ y : Fin (P.length - 1) → T.F m, ∀ a : Fin (P.length - 1),
        (y a)′ + ∑ b : Fin (P.length - 1), Λ b a * y b = (T.MP m h1.of_succ).sem η * c a := by
    rw [hNP]
    intro c hc hhom ⟨y, hy⟩
    set Uf : Fin SQ.F.natDegree → Fin SQ.F.natDegree → T.F m := fun a b ↦ ι (U a b) with hUf
    set Df : Fin SQ.F.natDegree → T.F m := fun a ↦ ι (Td a) with hDf
    have hUF' : ∀ a b : Fin SQ.F.natDegree,
        (Uf a b)′ = ∑ k : Fin SQ.F.natDegree, Uf a k * Λ (b : ℕ) (k : ℕ) - Df a * Uf a b := by
      intro a b
      have := hUF a b
      rw [hUf]; dsimp only
      rw [hιd, show (U a b)′ = ∑ k, U a k * ΛQ b k - Td a * U a b by rw [this]; ring]
      simp only [map_sub, map_sum, map_mul, hΛι, hDf]
    have hz : ∀ a, (∑ k : Fin SQ.F.natDegree, Uf a k * c k)′ +
        Df a * ∑ k : Fin SQ.F.natDegree, Uf a k * c k = 0 := by
      intro a
      rw [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      simp only [Derivation.leibniz, smul_eq_mul]
      have e1 : ∀ k, Uf a k * (c k)′ + c k * (Uf a k)′ + Df a * (Uf a k * c k) =
          -Uf a k * ∑ b : Fin SQ.F.natDegree, Λ (b : ℕ) (k : ℕ) * c b +
            c k * ∑ b : Fin SQ.F.natDegree, Uf a b * Λ (k : ℕ) (b : ℕ) := fun k ↦ by
        rw [hUF', show (c k)′ = -∑ b : Fin SQ.F.natDegree, Λ (b : ℕ) (k : ℕ) * c b from
          eq_neg_of_add_eq_zero_left (hhom k)]
        ring
      simp only [e1, Finset.sum_add_distrib, Finset.mul_sum]
      have hsw : ∑ x : Fin SQ.F.natDegree, ∑ i : Fin SQ.F.natDegree, c x * (Uf a i * Λ (x : ℕ) (i : ℕ)) =
          ∑ x : Fin SQ.F.natDegree, ∑ i : Fin SQ.F.natDegree, c i * (Uf a x * Λ (i : ℕ) (x : ℕ)) :=
        Finset.sum_comm
      rw [hsw, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun j _ ↦ by ring
    have hzy : ∀ a, (∑ k : Fin SQ.F.natDegree, Uf a k * y k)′ +
        Df a * ∑ k : Fin SQ.F.natDegree, Uf a k * y k =
          (T.MP m h0).sem η * ∑ k : Fin SQ.F.natDegree, Uf a k * c k := by
      intro a
      rw [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Derivation.leibniz, smul_eq_mul]
      have e1 : ∀ k, Uf a k * (y k)′ + y k * (Uf a k)′ + Df a * (Uf a k * y k) =
          (T.MP m h0).sem η * (Uf a k * c k) +
            (-Uf a k * ∑ b : Fin SQ.F.natDegree, Λ (b : ℕ) (k : ℕ) * y b +
              y k * ∑ b : Fin SQ.F.natDegree, Uf a b * Λ (k : ℕ) (b : ℕ)) := fun k ↦ by
        rw [hUF', show (y k)′ = (T.MP m h0).sem η * c k -
          ∑ b : Fin SQ.F.natDegree, Λ (b : ℕ) (k : ℕ) * y b by rw [← hy k]; ring]
        ring
      simp only [e1, Finset.sum_add_distrib]
      rw [add_eq_left]
      simp only [Finset.mul_sum]
      have hsw : ∑ x : Fin SQ.F.natDegree, ∑ i : Fin SQ.F.natDegree, y x * (Uf a i * Λ (x : ℕ) (i : ℕ)) =
          ∑ x : Fin SQ.F.natDegree, ∑ i : Fin SQ.F.natDegree, y i * (Uf a x * Λ (i : ℕ) (x : ℕ)) :=
        Finset.sum_comm
      rw [hsw, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun j _ ↦ by ring
    -- `U c ≠ 0`
    have hUc : ∃ a, ∑ k : Fin SQ.F.natDegree, Uf a k * c k ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hc
      funext b
      have hUiUf : ∀ k b, ∑ a : Fin SQ.F.natDegree, ι (Ui b a) * Uf a k = if b = k then 1 else 0 :=
        fun k b ↦ by
          have := congrFun (congrFun hUiU b) k
          rw [Matrix.mul_apply, Matrix.one_apply] at this
          simp only [hUf, ← map_mul, ← map_sum, this]
          split_ifs <;> simp
      have : c b = ∑ a : Fin SQ.F.natDegree, ι (Ui b a) * ∑ k : Fin SQ.F.natDegree, Uf a k * c k := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [← mul_assoc, ← Finset.sum_mul, hUiUf]
        simp
      rw [this]
      simp [hall]
    obtain ⟨a, ha⟩ := hUc
    apply hη ((∑ k : Fin SQ.F.natDegree, Uf a k * y k) / ∑ k : Fin SQ.F.natDegree, Uf a k * c k)
    rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul,
      eq_sub_of_add_eq (hzy a), eq_neg_of_add_eq_zero_left (hz a)]
    field_simp
    ring
  exact ⟨Tc, Ti, r', Cl, Cil, dgL, T.exactTLVG_isSome h1 hm hk htr rde hrde dgL Cl Cil r'
    P θ hP hPc (by rw [hNP, hSQn]; exact hn0.ne') hind dθ hd Tc Ti hok f gs Mval hMval hsq' Λ hprop
    hinv htri hdiag hokd hnd⟩

end MTower

end Curves.MT
