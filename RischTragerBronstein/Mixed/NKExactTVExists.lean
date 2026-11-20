import RischTragerBronstein.Mixed.NKExactTVSome
import RischTragerBronstein.Mixed.NKExactTRExists
import RischTragerBronstein.Mixed.NKCodeField
import RischTragerBronstein.Mixed.NKCoordMats
import Mathlib.Data.Fin.Tuple.Sort

/-!
# `exactTV` answers for a suitable basis of a non-constant curve

**`exactTV_exists`**: for `θⁿ + ∑ aᵢ(t) θⁱ = 0` with coefficients `aᵢ ∈ Fₘ[t]` given by codes and a
single place at infinity (`nkShape`), over a primitive level, there are code matrices `Tc`, `Ti`,
shifts `r` and diagonal representations `dg` for which `exactTV` answers. The basis is an echelon
integral basis over the field of code values (`exists_nkBasis` on `nkCurveQ`), sorted by weight;
its limit matrix at infinity is triangular with diagonal `(j₀/n) c′/c` and gauge-trivial over the
algebraic closure (`nk_inf_struct` on the curve over `Fₘ`), hence non-degenerate
(`nondeg_of_gauge`).
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

/-- A code of a code value. -/
noncomputable def cvCode {m : ℕ} {h : T.Tr m} (z : T.codeVals m h) : LC m :=
  Classical.choose z.2

lemma sem_cvCode {m : ℕ} {h : T.Tr m} (z : T.codeVals m h) :
    (T.MP m h).sem (T.cvCode z) = T.codeIncl m h z :=
  Subtype.ext (Classical.choose_spec z.2).symm

/-- A polynomial over the code values as a code. -/
noncomputable def cvPoly {m : ℕ} {h : T.Tr m} (p : (T.codeVals m h)[X]) : GPoly (LC m) :=
  (List.range (p.natDegree + 1)).map fun k ↦ T.cvCode (p.coeff k)

lemma toPoly_cvPoly {m : ℕ} {h : T.Tr m} (p : (T.codeVals m h)[X]) :
    GPoly.toPoly (T.MP m h) (T.cvPoly p) = p.map (T.codeIncl m h) := by
  refine Polynomial.ext fun k ↦ ?_
  rw [coeff_toPoly_sem, coeff_map]
  by_cases hk : k < p.natDegree + 1
  · rw [cvPoly, NestTower.getD_range_map _ _ hk, T.sem_cvCode]
  · rw [List.getD_eq_default _ _ (by simpa [cvPoly] using hk), (T.MP m h).sem_zero,
      coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

/-- A fraction of polynomials over the code values as a code of level `m + 1`. -/
noncomputable def cvFrac {m : ℕ} {h : T.Tr m} (A B : (T.codeVals m h)[X]) : LC (m + 1) :=
  (T.cvPoly A, T.cvPoly B)

lemma coe_sem_cvFrac {m : ℕ} (h1 : T.Tr (m + 1)) (A B : (T.codeVals m h1.of_succ)[X]) :
    (((T.MPr (m + 1) h1).sem (T.cvFrac A B) : T.F (m + 1)) : L) =
      aeval (T.ts m) A / aeval (T.ts m) B := by
  rw [MPr_sem, T.sem_MP_succ]
  change ((T.phi m (GPoly.toPoly (T.MP m _) (T.cvPoly A)) /
    T.phi m (GPoly.toPoly (T.MP m _) (T.cvPoly B)) : T.F (m + 1)) : L) = _
  rw [T.toPoly_cvPoly, T.toPoly_cvPoly, IntermediateField.coe_div, coe_phi, coe_phi]
  have e : ∀ p : (T.codeVals m h1.of_succ)[X], aeval (T.ts m) (p.map (T.codeIncl m h1.of_succ)) =
      aeval (T.ts m) p := fun p ↦ by
    have e0 : (algebraMap (T.F m) L).comp (T.codeIncl m h1.of_succ) =
        algebraMap (T.codeVals m h1.of_succ) L := RingHom.ext fun z ↦ rfl
    rw [aeval_def, eval₂_map, e0, ← aeval_def]
  rw [e, e]



lemma aeval_map_codeIncl {m : ℕ} {h : T.Tr m} (p : (T.codeVals m h)[X]) (z : L) :
    aeval z (p.map (T.codeIncl m h)) = aeval z p := by
  have e0 : (algebraMap (T.F m) L).comp (T.codeIncl m h) = algebraMap (T.codeVals m h) L :=
    RingHom.ext fun z ↦ rfl
  rw [aeval_def, eval₂_map, e0, ← aeval_def]

lemma eval_map_map_codeIncl {m : ℕ} {h : T.Tr m} (W : (T.codeVals m h)[X][X]) (x y : L) :
    ((W.map (Polynomial.mapRingHom (T.codeIncl m h))).map (aeval x).toRingHom).eval y =
      (W.map (aeval x).toRingHom).eval y := by
  rw [Polynomial.map_map]
  congr 2
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, Polynomial.map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
    rfl
  · simp

/-- The weight is unchanged by an injective change of coefficients. -/
lemma wtW_map {A B : Type*} [Field A] [Field B] (φ : A →+* B) (n d : ℕ) (W : A[X][X]) :
    wtW n d (W.map (Polynomial.mapRingHom φ)) = wtW n d W := by
  classical
  unfold wtW
  refine Finset.sup_congr rfl fun j _ ↦ ?_
  simp only [Polynomial.coeff_map, coe_mapRingHom, Polynomial.map_eq_zero_iff φ.injective,
    natDegree_map_eq_of_injective φ.injective]

/-- A sorting permutation for distinct integer keys. -/
lemma exists_sort_strict {n : ℕ} (v : Fin n → ℤ) (hv : Function.Injective v) :
    ∃ σ : Equiv.Perm (Fin n), StrictMono (v ∘ σ) :=
  ⟨Tuple.sort v, (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)⟩

set_option maxHeartbeats 4000000 in
/-- **`exactTV` answers for a suitable basis of a non-constant curve.** -/
theorem exactTV_exists (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m}
    (hk : ks m = .prim η) (htr : Transcendental (T.F m) (T.ts m))
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h1.of_succ).sem η)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (f : List (LC (m + 1))) :
    ∃ (Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (dg : List (FRep (LC m))),
      (exactTV Fc ks m η rde dg r (nkPC Fc ks m Pp) Tc Ti f).isSome := by
  classical
  set h0 := h1.of_succ with hh0
  set C := T.codeVals m h0 with hC
  letI := diffRat
  letI := diffAlgRat (L := L)
  letI dC : Differential C := differentialOfDerivClosed (T.derivClosed_codeVals m h0)
  letI dCL : DifferentialAlgebra C L := differentialAlgebra_of_derivClosed (T.derivClosed_codeVals m h0)
  set K := AlgebraicClosure C with hKdef
  have hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′ := fun c ↦ deriv_algebraMap c
  set SQ := T.nkCurveQ m h1 Pp hsh θ hθ with hSQ
  set ηQ : C := T.cv m h0 η with hηQ
  have hx : SQ.x′ = aeval SQ.x (Polynomial.C ηQ) := by
    rw [aeval_C]
    change (T.ts m)′ = _
    rw [T.deriv_ts_L m h0 hm hk]
    rfl
  have hsp := T.nkShape_spec m h0 Pp hsh
  set n := Pp.length with hn
  set d := degG (MO Fc ks m) (Pp.getD 0 []) with hd
  have hSQn : SQ.F.natDegree = n := polyF_natDegree _ _
  have hSQa0 : SQ.F.coeff 0 ≠ 0 := fun h0' ↦ hsp.2.1 (by
    have := T.nkFQ_coeff m h0 Pp 0
    have h0'' : (T.nkFQ m h0 Pp).coeff 0 = 0 := h0'
    rw [h0'', Polynomial.map_zero] at this
    exact this.symm)
  have hSQd : (SQ.F.coeff 0).natDegree = d := by
    rw [show SQ.F = T.nkFQ m h0 Pp from rfl, T.nkFQ_natDegree_coeff]; exact hsp.2.2.1
  have hSQw : ∀ i, 0 < i → i < n → SQ.F.coeff i = 0 ∨
      n * (SQ.F.coeff i).natDegree < d * (n - i) := fun i hi hin ↦ by
    rcases hsp.2.2.2.1 i hi hin with h0' | h0'
    · left
      have := T.nkFQ_coeff m h0 Pp i
      have h0'' : (T.nkF m h0 Pp).coeff i = 0 := h0'
      rw [h0''] at this
      exact (Polynomial.map_eq_zero_iff (T.codeIncl_injective m h0)).mp this
    · right; rw [show SQ.F = T.nkFQ m h0 Pp from rfl, T.nkFQ_natDegree_coeff]; exact h0'
  obtain ⟨w, r, S0, Pm, W, Q, hindw, hS00, hsq, hder, hdeg, hrep, hwin, hdist, hnorm⟩ :=
    SQ.exists_nkBasis (K := K) ηQ hx hK n d hSQn hsp.1 hSQa0 hSQd hSQw hsp.2.2.2.2
  obtain ⟨A, B, Ai, Bi, hB, hBi, hwA, hTTi, hTiT⟩ := SQ.exists_coordMats w hindw
  -- sort by weight
  set v : Fin SQ.F.natDegree → ℤ := fun i ↦ (wtW n d (W i) : ℤ) - n * (Q i).natDegree with hv
  obtain ⟨σ, hσ⟩ := exists_sort_strict v (fun i j hij ↦ hdist i j hij)
  -- the curve over `Fₘ` and a branch above infinity
  set SF := T.nkCurve m h1 Pp hsh θ hθ with hSF
  set KF := AlgebraicClosure (T.F m) with hKFdef
  have hKF : ∀ c : T.F m, (algebraMap (T.F m) KF c)′ = algebraMap (T.F m) KF c′ :=
    fun c ↦ deriv_algebraMap c
  have hxF : SF.x′ = aeval SF.x (Polynomial.C ((T.MP m h0).sem η)) := by
    rw [aeval_C]
    change (T.ts m)′ = _
    rw [T.deriv_ts_L m h0 hm hk]
    rfl
  have hSFn : SF.F.natDegree = n := polyF_natDegree _ _
  obtain ⟨N, hN, l, hlen, hl, -⟩ := SF.hasBranchesInfB (K := KF)
  have hN0 := Nat.pos_of_ne_zero hN
  have hlne : l ≠ [] := by
    intro h; rw [h, List.length_nil, hSFn] at hlen; exact absurd hlen (by have := hsp.1; omega)
  obtain ⟨ρ, hρl⟩ := List.exists_mem_of_ne_nil l hlne
  have hρ := SF.root_of_mem hl hρl
  -- the sorted rescaled basis as elements over `Fₘ`
  set ι := T.codeIncl m h0 with hι
  have hmemF : ∀ i, (SQ.wTil w r i : L) ∈ (T.F m)⟮SF.x⟯⟮SF.y⟯ := by
    intro i
    obtain ⟨hQi, hWQi, -, -⟩ := hrep i
    have hQx : aeval SQ.x (Q i) ≠ 0 := fun h ↦ hQi ((transcendental_iff.mp SQ.htr) _ h)
    have e : (SQ.wTil w r i : L) = SF.evXY ((W i).map (Polynomial.mapRingHom ι)) /
        aeval SF.x ((Q i).map ι) := by
      rw [eq_div_iff (by rwa [T.aeval_map_codeIncl])]
      rw [T.aeval_map_codeIncl, CurveData.evXY, T.eval_map_map_codeIncl]
      exact hWQi
    rw [e]
    refine div_mem ?_ ?_
    · rw [← SF.coe_evT]; exact (SF.evT _).2
    · exact SF.aeval_mem _
  set wF : Fin SQ.F.natDegree → (T.F m)⟮SF.x⟯⟮SF.y⟯ := fun i ↦ ⟨_, hmemF (σ i)⟩ with hwF
  set WF : Fin SQ.F.natDegree → (T.F m)[X][X] := fun i ↦ (W (σ i)).map (Polynomial.mapRingHom ι)
    with hWF
  set QF : Fin SQ.F.natDegree → (T.F m)[X] := fun i ↦ (Q (σ i)).map ι with hQF
  set RF : Fin SQ.F.natDegree → (T.F m)[X] := fun i ↦ (X ^ (r (σ i) + 1) * S0).map ι with hRF
  set PF : Fin SQ.F.natDegree → Fin SQ.F.natDegree → (T.F m)[X] := fun i j ↦
    (Curves.CurveData.pqV ηQ r Pm S0 (σ i) (σ j)).map ι with hPF
  have hιi := T.codeIncl_injective m h0
  have hQF0 : ∀ i, QF i ≠ 0 := fun i ↦
    (Polynomial.map_ne_zero_iff hιi).mpr (hrep (σ i)).1
  have hWQF : ∀ i, (wF i : L) * aeval SF.x (QF i) = SF.evXY (WF i) := fun i ↦ by
    rw [hQF, hWF]
    dsimp only
    rw [T.aeval_map_codeIncl, CurveData.evXY, T.eval_map_map_codeIncl]
    exact (hrep (σ i)).2.1
  have hWF0 : ∀ i, WF i ≠ 0 := fun i ↦
    (Polynomial.map_ne_zero_iff (Polynomial.map_injective _ hιi)).mpr (hrep (σ i)).2.2.1
  have hWFn : ∀ i, (WF i).natDegree < n := fun i ↦ by
    rw [hWF]; dsimp only
    rw [natDegree_map_eq_of_injective (Polynomial.map_injective _ hιi)]
    exact (hrep (σ i)).2.2.2
  have hvF : ∀ i, (wtW n d (WF i) : ℤ) - n * (QF i).natDegree = v (σ i) := fun i ↦ by
    rw [hWF, hQF]; dsimp only
    rw [wtW_map, natDegree_map_eq_of_injective hιi]
  have hRF0 : ∀ i, RF i ≠ 0 := fun i ↦
    (Polynomial.map_ne_zero_iff hιi).mpr (mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00)
  have hPRF : ∀ i j, (PF i j).natDegree ≤ (RF i).natDegree := fun i j ↦ by
    rw [hPF, hRF]; dsimp only
    rw [natDegree_map_eq_of_injective hιi, natDegree_map_eq_of_injective hιi]
    exact hdeg (σ i) (σ j)
  have hDF : ∀ i, (wF i : L)′ * aeval SF.x (RF i) = ∑ j, aeval SF.x (PF i j) * (wF j : L) := by
    intro i
    have := SQ.deriv_wTil ηQ hx w r S0 Pm hder (σ i)
    rw [hRF]; dsimp only
    rw [T.aeval_map_codeIncl]
    change (SQ.wTil w r (σ i) : L)′ * aeval SQ.x _ = _
    rw [this, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hPF]; dsimp only
    rw [T.aeval_map_codeIncl]
    rfl
  obtain ⟨htriF, hdiagF, AF, hindAF, hAF⟩ := SF.nk_inf_struct (K := KF) ((T.MP m h0).sem η) hxF hKF
    n d hSFn hsp.1 hsp.2.1 hsp.2.2.1 hsp.2.2.2.1 hsp.2.2.2.2 N hN0 ρ hρ wF WF QF hQF0 hWQF hWF0 hWFn
    (fun i ↦ by rw [hvF]; exact hwin (σ i)) (fun i j hij ↦ by
      rw [hvF, hvF] at hij; exact σ.injective (hdist _ _ hij)) RF hRF0 PF hPRF hDF
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
    rw [hNP, hSQn]; exact T.nkCurve_ind m h1 Pp hsh θ hθ
  have hPdeg : (GPoly.toPoly M1 P).natDegree = SQ.F.natDegree := by
    rw [hM1, hPdef, T.toPoly_nkPC m h1 Pp, polyF_natDegree]; exact hSQn.symm
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [hM1, hPdef, T.toPoly_nkPC m h1 Pp]; exact polyF_monic _ _
  have hcop := T.sep_P_const m h1 P hPm SQ.F.natDegree hPdeg θ hP (by rw [← hNP]; exact hind)
  obtain ⟨dθ, hd⟩ := Option.isSome_iff_exists.mp (dThetaC_isSome M1 P hcop)
  -- the candidate
  have hnpos : 0 < SQ.F.natDegree := by rw [hSQn]; exact hsp.1
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
  -- triangularity
  have htri : ∀ i < P.length - 1, ∀ j < P.length - 1, i < j → Λ i j = 0 := by
    rw [hNP]
    intro i hi j hj hij
    by_contra hne
    have h1' := htriF (fi i) (fi j) hne
    rw [hvF, hvF] at h1'
    have : v (σ (fi i)) < v (σ (fi j)) := hσ (by rw [hfi i hi, hfi j hj]; exact hij)
    exact absurd h1' (not_le.mpr this)
  -- the diagonal
  choose j0F hj0n hj0c hj0w hj0Λ using hdiagF
  set lead := leadG (MO Fc ks m) (Pp.getD 0 []) with hlead
  set dgL : List (FRep (LC m)) := (List.range SQ.F.natDegree).map fun i ↦
    ⟨(MO Fc ks m).zero, [(mcst Fc ks m ((j0F (fi i) : ℚ) / n), lead)]⟩ with hdgL
  have hdgAt : ∀ i (hi : i < SQ.F.natDegree), dgAt Fc ks m dgL i =
      ⟨(MO Fc ks m).zero, [(mcst Fc ks m ((j0F (fi i) : ℚ) / n), lead)]⟩ := fun i hi ↦ by
    rw [dgAt, hdgL, NestTower.getD_range_map _ _ hi]
  have hdgAt' : ∀ i, SQ.F.natDegree ≤ i → dgAt Fc ks m dgL i = ⟨(MO Fc ks m).zero, []⟩ :=
    fun i hi ↦ by rw [dgAt, List.getD_eq_default _ _ (by simpa [hdgL] using hi)]
  have hβ1 : ∀ a, ((WF a).coeff (j0F a)).leadingCoeff / (QF a).leadingCoeff = 1 := by
    intro a
    have hc0 : (W (σ a)).coeff (j0F a) ≠ 0 := by
      intro h0'
      apply hj0c a
      rw [hWF]; dsimp only
      rw [Polynomial.coeff_map, h0', map_zero]
    have hwt : wtW n d (W (σ a)) = n * ((W (σ a)).coeff (j0F a)).natDegree + j0F a * d := by
      have := hj0w a
      rw [hWF] at this; dsimp only at this
      rw [wtW_map, Polynomial.coeff_map, coe_mapRingHom,
        natDegree_map_eq_of_injective hιi] at this
      exact this
    have hl := hnorm (σ a) (j0F a) (hj0n a) hc0 hwt
    rw [hWF, hQF]; dsimp only
    rw [Polynomial.coeff_map, coe_mapRingHom, leadingCoeff_map_of_injective hιi,
      leadingCoeff_map_of_injective hιi, hl]
    exact div_self ((map_ne_zero_iff _ hιi).mpr (leadingCoeff_ne_zero.mpr (hrep (σ a)).1))
  have hc0 : (SF.F.coeff 0) = GPoly.toPoly (T.MP m h0) (Pp.getD 0 []) := polyF_coeff _ _ _ hsp.1
  have hlc : (T.MP m h0).sem lead = (SF.F.coeff 0).leadingCoeff := by
    rw [hc0, hlead]
    exact sem_leadG (T.MP m h0) _ (by rw [← hc0]; exact hsp.2.1)
  have hdiag : ∀ i < P.length - 1, Λ i i =
      (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (dgAt Fc ks m dgL i)) := by
    rw [hNP]
    intro i hi
    rw [hdgAt i hi, sem_fCode]
    have hΛi := hj0Λ (fi i)
    rw [hβ1, Derivation.map_one_eq_zero, zero_div, zero_add] at hΛi
    rw [hΛdef]; dsimp only
    rw [hΛi]
    simp only [logSumV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      CField.sem_zero, Derivation.map_zero, zero_add, T.sem_mcst m h0, Differential.logDeriv, hlc]
    push_cast
    have hn0' : (n : T.F m) ≠ 0 := by exact_mod_cast hsp.1.ne'
    field_simp
  have hokd : ∀ i, ∀ cw ∈ (dgAt Fc ks m dgL i).logs, ((T.MP m h1.of_succ).sem cw.1)′ = 0 := by
    intro i cw hcw
    by_cases hi : i < SQ.F.natDegree
    · rw [hdgAt i hi] at hcw
      simp only [List.mem_singleton] at hcw
      rw [hcw, T.sem_mcst m h0]
      exact T.deriv_ratCast _
    · rw [hdgAt' i (by omega)] at hcw
      simp at hcw
  -- non-degeneracy
  have hηK : ∀ a : KF, a′ ≠ algebraMap (T.F m) KF ((T.MP m h0).sem η) := fun a ↦
    not_deriv_of_integral _ hη a (Algebra.IsIntegral.isIntegral a)
  have hnd : ∀ c : Fin (P.length - 1) → T.F m, c ≠ 0 →
      (∀ a : Fin (P.length - 1), (c a)′ + ∑ b : Fin (P.length - 1), Λ b a * c b = 0) →
      ¬ ∃ y : Fin (P.length - 1) → T.F m, ∀ a : Fin (P.length - 1),
        (y a)′ + ∑ b : Fin (P.length - 1), Λ b a * y b = (T.MP m h1.of_succ).sem η * c a := by
    rw [hNP]
    intro c hc hhom hy
    have e : ∀ a b : Fin SQ.F.natDegree, Λ b a =
        (PF b a).coeff (RF b).natDegree / (RF b).leadingCoeff := fun a b ↦ by
      rw [hΛdef]; dsimp only; rw [hfi b b.2, hfi a a.2]
    refine nondeg_of_gauge hKF (fun a b ↦ (PF a b).coeff (RF a).natDegree / (RF a).leadingCoeff) AF
      (fun k ↦ 0 ≤ k ∧ k < N) (fun c hc ↦ hindAF c fun k hk0 hkN ↦ hc k ⟨hk0, hkN⟩)
      (fun i k hk ↦ hAF i k hk.1 hk.2) ((T.MP m h0).sem η) hηK c hc
      (fun a ↦ by rw [← hhom a]; congr 1; exact Finset.sum_congr rfl fun b _ ↦ by rw [e]) ?_
    obtain ⟨y, hy⟩ := hy
    exact ⟨y, fun a ↦ by rw [← hy a]; congr 1; exact Finset.sum_congr rfl fun b _ ↦ by rw [e]⟩
  refine ⟨Tc, Ti, r', dgL, ?_⟩
  exact T.exactTV_isSome h1 hm hk htr rde hrde dgL r' P θ hP hPc (by omega) hind dθ hd Tc Ti hok f
    Mval hMval hsq' Λ hprop htri hdiag hokd hnd

end MTower

end Curves.MT
