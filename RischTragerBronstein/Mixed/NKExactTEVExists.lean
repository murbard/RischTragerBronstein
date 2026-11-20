import RischTragerBronstein.Mixed.NKExactTEVSome
import RischTragerBronstein.Mixed.NKExactTVExists
import RischTragerBronstein.Mixed.NKExp0Gauge
import RischTragerBronstein.Mixed.NKExpDecide

/-!
# `exactTEV` answers for a suitable basis of a non-constant curve over an exponential

**`exactTEV_exists`**: for `θⁿ + ∑ aᵢ(t) θⁱ = 0` with coefficients `aᵢ ∈ Fₘ[t]` given by codes, a
single place at infinity (`nkShape`) and a single place above `t = 0` (`nkShape0`), over an
exponential level `t = eᵃ`, there are code matrices `Tc`, `Ti`, shifts `r`, diagonal data `dg`,
a gauge `C`, `Ci` and diagonal data `dg0` at `t = 0` for which `exactTEV` answers. The basis is an
echelon integral basis over the field of code values (`exists_nkBasisE` on `nkCurveQ`), sorted by
weight at infinity; its limit matrix there is triangular (`nk_inf_struct_exp` on the curve over
`Fₘ`). At `t = 0` the gauge is the transition to `yʲ/t^{⌊jd₀/n⌋}`, sorted by the orders above `0`
(`exists_gauge0`).
-/

open Polynomial Differential IntermediateField
open scoped Matrix

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- Trailing degrees are kept by injective coefficient maps. -/
lemma natTrailingDegree_map_inj {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B)
    (hφ : Function.Injective φ) (p : A[X]) :
    (p.map φ).natTrailingDegree = p.natTrailingDegree := by
  simp only [natTrailingDegree, trailingDegree, support_map_of_injective p hφ]

/-- **Leibniz rule for matrices.** -/
lemma matrix_map_deriv_mul {ι R : Type*} [Fintype ι] [CommRing R] [Differential R]
    (A B : Matrix ι ι R) :
    (A * B).map (fun z ↦ z′) = A.map (fun z ↦ z′) * B + A * B.map (fun z ↦ z′) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, Derivation.leibniz,
    smul_eq_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **The gauge identity**: for `U U⁻¹ = 1`, `C = (U⁻¹)ᵀ`, `Ci = Uᵀ`:
`C M(0)ᵀ Ci − C′ Ci = ((U′ + U M(0)) U⁻¹)ᵀ`. -/
lemma gauge_transpose {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [Differential R]
    (U Ui M : Matrix ι ι R) (hU : U * Ui = 1) :
    Uiᵀ * Mᵀ * Uᵀ - Uiᵀ.map (fun z ↦ z′) * Uᵀ = ((U.map (fun z ↦ z′) + U * M) * Ui)ᵀ := by
  have h1 := matrix_map_deriv_mul U Ui
  rw [hU] at h1
  have h0 : (1 : Matrix ι ι R).map (fun z ↦ z′) = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.one_apply, Matrix.zero_apply]
    split_ifs <;> simp
  rw [h0] at h1
  have h2 : U * Ui.map (fun z ↦ z′) = -(U.map (fun z ↦ z′) * Ui) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1.symm
  have e : Uiᵀ.map (fun z ↦ z′) = (Ui.map (fun z ↦ z′))ᵀ := by ext i j; rfl
  rw [e, ← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul, h2,
    ← Matrix.transpose_sub]
  congr 1
  rw [Matrix.add_mul, Matrix.mul_assoc, sub_neg_eq_add, add_comm]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 8000000 in
/-- **`exactTEV` answers for a suitable basis of a non-constant curve** over an exponential. -/
theorem exactTEV_exists (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {a : LC m}
    (hk : ks m = .exp a) (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (f : List (LC (m + 1))) :
    ∃ (Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (dg : List (ℚ × ℚ × LC m))
      (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)),
      (exactTEV Fc ks m a rde dg r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f).isSome := by
  classical
  set h0 := h1.of_succ with hh0
  set Cq := T.codeVals m h0 with hCq
  letI := diffRat
  letI := diffAlgRat (L := L)
  letI dC : Differential Cq := differentialOfDerivClosed (T.derivClosed_codeVals m h0)
  letI dCL : DifferentialAlgebra Cq L :=
    differentialAlgebra_of_derivClosed (T.derivClosed_codeVals m h0)
  set K := AlgebraicClosure Cq with hKdef
  have hK : ∀ c : Cq, (algebraMap Cq K c)′ = algebraMap Cq K c′ := fun c ↦ deriv_algebraMap c
  set SQ := T.nkCurveQ m h1 Pp hsh θ hθ with hSQ
  set bQ : Cq := T.cv m h0 ((MO Fc ks m).deriv a) with hbQ
  have hx : SQ.x′ = aeval SQ.x (Polynomial.C bQ * X) := by
    rw [map_mul, aeval_C, aeval_X]
    change (T.ts m)′ = _
    rw [T.deriv_ts_L_exp m h0 hm hk]
    rfl
  have hsp := T.nkShape_spec m h0 Pp hsh
  have hsp0 := T.nkShape0_spec m h0 Pp hsh0
  set n := Pp.length with hn
  set d := degG (MO Fc ks m) (Pp.getD 0 []) with hd
  set d0 := trailG (MO Fc ks m) (Pp.getD 0 []) with hd0
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
  have hSQtr : ∀ i, (SQ.F.coeff i).natTrailingDegree = ((T.nkF m h0 Pp).coeff i).natTrailingDegree :=
    fun i ↦ by
      rw [show SQ.F = T.nkFQ m h0 Pp from rfl, ← T.nkFQ_coeff,
        natTrailingDegree_map_inj _ (T.codeIncl_injective m h0)]
  have hSQd0 : (SQ.F.coeff 0).natTrailingDegree = d0 := by rw [hSQtr]; exact hsp0.1
  have hSQw0 : ∀ i, 0 < i → i < n → SQ.F.coeff i = 0 ∨
      d0 * (n - i) < n * (SQ.F.coeff i).natTrailingDegree := fun i hi hin ↦ by
    rcases hsp0.2.1 i hi hin with h0' | h0'
    · left
      have := T.nkFQ_coeff m h0 Pp i
      have h0'' : (T.nkF m h0 Pp).coeff i = 0 := h0'
      rw [h0''] at this
      exact (Polynomial.map_eq_zero_iff (T.codeIncl_injective m h0)).mp this
    · right; rw [hSQtr]; exact h0'
  obtain ⟨w, r, S0, Pm, W, Q, hwB, hindw, hS00, hsq, hS0c, hder, hdeg, hrep, hwin, hdist, hnorm⟩ :=
    SQ.exists_nkBasisE (K := K) bQ hx hK n d hSQn hsp.1 hSQa0 hSQd hSQw hsp.2.2.2.2
  obtain ⟨A, B, Ai, Bi, hB, hBi, hwA, hTTi, hTiT⟩ := SQ.exists_coordMats w hindw
  -- the gauge at `t = 0`
  obtain ⟨U, Ui, Lam, hUUi, hUiU, hLam, htri0, hdiag0⟩ := SQ.exists_gauge0 (K := K) bQ hx hK n d0
    hSQn hsp.1 hSQa0 hSQd0 hSQw0 hsp0.2.2 w hwB S0 hS0c Pm hder
  -- sort by weight at infinity
  set v : Fin SQ.F.natDegree → ℤ := fun i ↦ (wtW n d (W i) : ℤ) - n * (Q i).natDegree with hv
  obtain ⟨σ, hσ⟩ := exists_sort_strict v (fun i j hij ↦ hdist i j hij)
  -- sort by decreasing order above `0`
  have hreminj : ∀ i j : Fin SQ.F.natDegree, (i : ℕ) * d0 % n = (j : ℕ) * d0 % n → i = j := by
    intro i j hij
    have h := Nat.ModEq.cancel_right_of_coprime hsp0.2.2 (hij : (i : ℕ) * d0 ≡ (j : ℕ) * d0 [MOD n])
    have hi : (i : ℕ) < n := hSQn ▸ i.2
    have hj : (j : ℕ) < n := hSQn ▸ j.2
    unfold Nat.ModEq at h
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
    exact Fin.ext h
  obtain ⟨τ, hτ⟩ := exists_sort_strict (fun i : Fin SQ.F.natDegree ↦ -(((i : ℕ) * d0 % n : ℕ) : ℤ))
    (fun i j hij ↦ hreminj i j (by
      have h' := neg_inj.mp hij
      exact_mod_cast h'))
  -- the curve over `Fₘ` and a branch above infinity
  set SF := T.nkCurve m h1 Pp hsh θ hθ with hSF
  set KF := AlgebraicClosure (T.F m) with hKFdef
  have hKF : ∀ c : T.F m, (algebraMap (T.F m) KF c)′ = algebraMap (T.F m) KF c′ :=
    fun c ↦ deriv_algebraMap c
  set bF : T.F m := (T.MP m h0).sem ((MO Fc ks m).deriv a) with hbF
  have hxF : SF.x′ = aeval SF.x (Polynomial.C bF * X) := by
    rw [map_mul, aeval_C, aeval_X]
    change (T.ts m)′ = _
    rw [T.deriv_ts_L_exp m h0 hm hk]
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
  set RF : Fin SQ.F.natDegree → (T.F m)[X] := fun i ↦ (X ^ r (σ i) * S0).map ι with hRF
  set PF : Fin SQ.F.natDegree → Fin SQ.F.natDegree → (T.F m)[X] := fun i j ↦
    (Curves.CurveData.pqE bQ r Pm S0 (σ i) (σ j)).map ι with hPF
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
    have := SQ.deriv_wTilE bQ hx w r S0 Pm hder (σ i)
    rw [hRF]; dsimp only
    rw [T.aeval_map_codeIncl]
    change (SQ.wTil w r (σ i) : L)′ * aeval SQ.x _ = _
    rw [this, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hPF]; dsimp only
    rw [T.aeval_map_codeIncl]
    rfl
  obtain ⟨htriF, hdiagF⟩ := SF.nk_inf_struct_exp (K := KF) bF hxF hKF
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
  -- the value at `t = 0`
  set M0 : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) Cq :=
    Matrix.of (fun i j ↦ (Pm i j).coeff 0 / S0.coeff 0) with hM0
  set M0Q : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) Cq := (M0.submatrix σ σ)ᵀ with hM0Q
  set M0v : ℕ → ℕ → T.F m := fun i j ↦ ι (M0Q (fi i) (fi j)) with hM0v
  have hsq' : ∀ i < P.length - 1, ∀ j < P.length - 1, ∃ A S : (T.F m)[X], Squarefree S ∧
      S.coeff 0 ≠ 0 ∧ A.coeff 0 = M0v j i * S.coeff 0 ∧ Mval i j = T.phi m A / T.phi m S :=
    fun i _ j _ ↦ ⟨(Pm (σ (fi i)) (σ (fi j))).map ι, S0.map ι, hsqF,
      by rw [Polynomial.coeff_map]; exact (map_ne_zero_iff _ hιi).mpr hS0c,
      by
        rw [Polynomial.coeff_map, Polynomial.coeff_map, hM0v, hM0Q]
        simp only [Matrix.transpose_apply, Matrix.submatrix_apply, hM0, Matrix.of_apply]
        rw [← map_mul, div_mul_cancel₀ _ hS0c], rfl⟩
  -- the limit matrix at infinity
  set Λ : ℕ → ℕ → T.F m := fun i j ↦
    (PF (fi i) (fi j)).coeff (RF (fi i)).natDegree / (RF (fi i)).leadingCoeff with hΛdef
  have hτ0 : T.tau m ≠ 0 := T.tau_ne_zero m htr
  have hσfi : ∀ i (hi : i < SQ.F.natDegree) j (hj : j < SQ.F.natDegree),
      σ (fi i) = σ (fi j) ↔ i = j := fun i hi j hj ↦ by
    rw [hfi i hi, hfi j hj, σ.injective.eq_iff, Fin.mk.injEq]
  have hprop : ∀ k < P.length - 1, ∀ l < P.length - 1, ∃ A' B' : (T.F m)[X], B' ≠ 0 ∧
      A'.natDegree ≤ B'.natDegree ∧ A'.coeff B'.natDegree / B'.leadingCoeff = Λ k l ∧
      T.tau m ^ (r' l - r' k) * Mval k l -
          (if k = l then (r' k : T.F (m + 1)) *
            T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a))) else 0) =
        T.phi m A' / T.phi m B' := by
    rw [hNP]
    intro i hi j hj
    refine ⟨PF (fi i) (fi j), RF (fi i), hRF0 _, hPRF _ _, rfl, ?_⟩
    have hX : T.phi m X = T.tau m := rfl
    have hφS0 : T.phi m (S0.map ι) ≠ 0 := fun h0' ↦
      hsqF.ne_zero (T.phi_injective htr (by rw [h0', map_zero]))
    simp only [hMvaldef, hPF, hRF, hr', Curves.CurveData.pqE, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, map_mul, map_sub, map_pow, hX]
    rw [zpow_sub₀ hτ0, zpow_natCast, zpow_natCast]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, Polynomial.map_mul, Polynomial.map_C, map_mul, map_natCast, map_pow,
        Polynomial.map_pow, Polynomial.map_X, hX]
      have hc : T.phi m (Polynomial.C (ι bQ)) =
          T.phi m (Polynomial.C ((T.MP m h0).sem ((MO Fc ks m).deriv a))) := rfl
      rw [Polynomial.map_natCast, map_natCast, hc]
      have hτr : T.tau m ^ r (σ (fi i)) ≠ 0 := pow_ne_zero _ hτ0
      field_simp
      push_cast
      ring
    · have hij' : ¬σ (fi i) = σ (fi j) := fun h ↦ hij ((hσfi i hi j hj).mp h)
      simp only [hij, hij', if_false, sub_zero, Polynomial.map_zero, map_zero]
      field_simp
  -- triangularity at infinity
  have htri : ∀ i < P.length - 1, ∀ j < P.length - 1, i < j → Λ i j = 0 := by
    rw [hNP]
    intro i hi j hj hij
    by_contra hne
    have h1' := htriF (fi i) (fi j) hne
    rw [hvF, hvF] at h1'
    have : v (σ (fi i)) < v (σ (fi j)) := hσ (by rw [hfi i hi, hfi j hj]; exact hij)
    exact absurd h1' (not_le.mpr this)
  -- the diagonal at infinity
  choose j0F hj0n hj0c hj0w hj0Λ using hdiagF
  set lead := leadG (MO Fc ks m) (Pp.getD 0 []) with hlead
  set dgL : List (ℚ × ℚ × LC m) := (List.range SQ.F.natDegree).map fun i ↦
    (((v (σ (fi i)) : ℤ) : ℚ) / n, (j0F (fi i) : ℚ) / n, lead) with hdgL
  have hdgAt : ∀ i (hi : i < SQ.F.natDegree), dgEAt Fc ks m dgL i =
      (((v (σ (fi i)) : ℤ) : ℚ) / n, (j0F (fi i) : ℚ) / n, lead) := fun i hi ↦ by
    rw [dgEAt, hdgL, NestTower.getD_range_map _ _ hi]
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
      (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dgL i))) := by
    rw [hNP]
    intro i hi
    rw [hdgAt i hi, sem_fCode]
    have hΛi := hj0Λ (fi i)
    rw [hβ1, Derivation.map_one_eq_zero, zero_div, zero_add, hvF] at hΛi
    rw [hΛdef]; dsimp only
    rw [hΛi]
    simp only [frE, logSumV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      CField.sem_mul, T.sem_mcst m h0, Differential.logDeriv, hlc, CField.sem_deriv, zero_add]
    rw [Derivation.leibniz, T.deriv_ratCast, smul_zero, add_zero, smul_eq_mul]
    push_cast
    have hn0' : (n : T.F m) ≠ 0 := by exact_mod_cast hsp.1.ne'
    field_simp
    rw [hbF, CField.sem_deriv]
    ring
  -- the gauge at `t = 0`
  set Uσ : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) Cq := U.submatrix τ σ with hUσ
  set Uiσ : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) Cq := Ui.submatrix σ τ with hUiσ
  set Cm := Uiσᵀ with hCm
  set Cim := Uσᵀ with hCim
  have hUσ1 : Uσ * Uiσ = 1 := by
    rw [hUσ, hUiσ, Matrix.submatrix_mul_equiv, hUUi, Matrix.submatrix_one_equiv]
  have hUiσ1 : Uiσ * Uσ = 1 := by
    rw [hUσ, hUiσ, Matrix.submatrix_mul_equiv, hUiU, Matrix.submatrix_one_equiv]
  have hGQ : Cm * M0Q * Cim - Cm.map (fun z ↦ z′) * Cim = (Lam.submatrix τ τ)ᵀ := by
    rw [hCm, hM0Q, hCim, gauge_transpose Uσ Uiσ (M0.submatrix σ σ) hUσ1, hLam]
    congr 1
    have e1 : (U.map (fun z ↦ z′) + U * M0).submatrix τ σ =
        Uσ.map (fun z ↦ z′) + Uσ * M0.submatrix σ σ := by
      rw [hUσ, Matrix.submatrix_mul_equiv]
      refine Matrix.ext fun i j ↦ ?_
      rfl
    rw [← Matrix.submatrix_mul_equiv (U.map (fun z ↦ z′) + U * M0) Ui τ σ τ, e1]
  have hCC : Cm * Cim = 1 := by rw [hCm, hCim, ← Matrix.transpose_mul, hUσ1, Matrix.transpose_one]
  have hCC' : Cim * Cm = 1 := by rw [hCm, hCim, ← Matrix.transpose_mul, hUiσ1, Matrix.transpose_one]
  set Cl : List (List (LC m)) := (List.range SQ.F.natDegree).map fun a ↦
    (List.range SQ.F.natDegree).map fun i ↦ T.cvCode (Cm (fi a) (fi i)) with hCl
  set Cil : List (List (LC m)) := (List.range SQ.F.natDegree).map fun i ↦
    (List.range SQ.F.natDegree).map fun a ↦ T.cvCode (Cim (fi i) (fi a)) with hCil
  have hcg : ∀ a i : Fin SQ.F.natDegree, (T.MP m h0).sem (cget Fc ks m Cl a i) = ι (Cm a i) :=
    fun a i ↦ by
      rw [cget, hCl, NestTower.getD_range_map _ _ a.2, NestTower.getD_range_map _ _ i.2,
        T.sem_cvCode, hfi a a.2, hfi i i.2]
  have hcig : ∀ i a : Fin SQ.F.natDegree, (T.MP m h0).sem (cget Fc ks m Cil i a) = ι (Cim i a) :=
    fun i a ↦ by
      rw [cget, hCil, NestTower.getD_range_map _ _ i.2, NestTower.getD_range_map _ _ a.2,
        T.sem_cvCode, hfi a a.2, hfi i i.2]
  have hC1 : ∀ i j : Fin (P.length - 1), ∑ k : Fin (P.length - 1),
      (T.MP m h1.of_succ).sem (cget Fc ks m Cl (i : ℕ) (k : ℕ)) *
      (T.MP m h1.of_succ).sem (cget Fc ks m Cil (k : ℕ) (j : ℕ)) = if i = j then 1 else 0 := by
    rw [hNP]
    intro i j
    have := congrFun (congrFun hCC i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [hcg, hcig, ← map_mul, ← map_sum, this]
    split_ifs <;> simp
  have hC2 : ∀ i j : Fin (P.length - 1), ∑ k : Fin (P.length - 1),
      (T.MP m h1.of_succ).sem (cget Fc ks m Cil (i : ℕ) (k : ℕ)) *
      (T.MP m h1.of_succ).sem (cget Fc ks m Cl (k : ℕ) (j : ℕ)) = if i = j then 1 else 0 := by
    rw [hNP]
    intro i j
    have := congrFun (congrFun hCC' i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [hcg, hcig, ← map_mul, ← map_sum, this]
    split_ifs <;> simp
  have hιd : ∀ z : Cq, (ι z)′ = ι (z′) := fun z ↦ rfl
  have hGF : ((Matrix.of fun i j : Fin SQ.F.natDegree ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Cl i j)) *
        Matrix.of (fun i j : Fin SQ.F.natDegree ↦ M0v i j) *
        (Matrix.of fun i j : Fin SQ.F.natDegree ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Cil i j)) -
        (Matrix.of fun i j : Fin SQ.F.natDegree ↦
          (T.MP m h1.of_succ).sem (cget Fc ks m Cl i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin SQ.F.natDegree ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Cil i j))) =
      ι.mapMatrix ((Lam.submatrix τ τ)ᵀ) := by
    have hCF : (Matrix.of fun i j : Fin SQ.F.natDegree ↦
        (T.MP m h1.of_succ).sem (cget Fc ks m Cl i j)) = ι.mapMatrix Cm := by
      refine Matrix.ext fun i j ↦ ?_; exact hcg i j
    have hCiF : (Matrix.of fun i j : Fin SQ.F.natDegree ↦
        (T.MP m h1.of_succ).sem (cget Fc ks m Cil i j)) = ι.mapMatrix Cim := by
      refine Matrix.ext fun i j ↦ ?_; exact hcig i j
    have hM0F : Matrix.of (fun i j : Fin SQ.F.natDegree ↦ M0v i j) = ι.mapMatrix M0Q := by
      refine Matrix.ext fun i j ↦ ?_
      simp only [hM0v, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hfi i i.2,
        hfi j j.2]
    have hdF : (ι.mapMatrix Cm).map (fun z ↦ z′) = ι.mapMatrix (Cm.map fun z ↦ z′) := by
      refine Matrix.ext fun i j ↦ ?_; exact hιd _
    rw [hCF, hM0F, hCiF, hdF, ← map_mul, ← map_mul, ← map_mul, ← map_sub, hGQ]
  have hgtri : ∀ i j : Fin (P.length - 1), j < i →
      ((Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Cl i j)) *
        Matrix.of (fun i j : Fin (P.length - 1) ↦ M0v i j) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Cil i j)) -
        (Matrix.of fun i j : Fin (P.length - 1) ↦
          (T.MP m h1.of_succ).sem (cget Fc ks m Cl i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Cil i j)))
          i j = 0 := by
    rw [hNP, hGF]
    intro i j hji
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.submatrix_apply]
    by_contra hne
    have h0' : Lam (τ j) (τ i) ≠ 0 := fun h ↦ hne (by rw [h, map_zero])
    have h1' := htri0 (τ j) (τ i) h0'
    have h2' := hτ hji
    simp only [Function.comp_apply] at h2'
    omega
  -- the diagonal at `t = 0`
  set cQ : Cq := (SQ.F.coeff 0).trailingCoeff with hcQ
  set dg0 : List (ℚ × ℚ × LC m) := (List.range SQ.F.natDegree).map fun a ↦
    ((((τ (fi a) : ℕ) * d0 % n : ℕ) : ℚ) / n, ((τ (fi a) : ℕ) : ℚ) / n, T.cvCode cQ) with hdg0
  have hdg0At : ∀ a (ha : a < SQ.F.natDegree), dgEAt Fc ks m dg0 a =
      ((((τ (fi a) : ℕ) * d0 % n : ℕ) : ℚ) / n, ((τ (fi a) : ℕ) : ℚ) / n, T.cvCode cQ) :=
    fun a ha ↦ by rw [dgEAt, hdg0, NestTower.getD_range_map _ _ ha]
  have hgdiag : ∀ i : Fin (P.length - 1),
      ((Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Cl i j)) *
        Matrix.of (fun i j : Fin (P.length - 1) ↦ M0v i j) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Cil i j)) -
        (Matrix.of fun i j : Fin (P.length - 1) ↦
          (T.MP m h1.of_succ).sem (cget Fc ks m Cl i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cget Fc ks m Cil i j)))
          i i =
      (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg0 (i : ℕ)))) := by
    rw [hNP, hGF]
    intro i
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.submatrix_apply]
    rw [hdiag0 (τ i), hdg0At i i.2, sem_fCode, hfi i i.2]
    simp only [frE, logSumV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      CField.sem_mul, T.sem_mcst m h0, Differential.logDeriv, T.sem_cvCode, zero_add]
    rw [Derivation.leibniz, T.deriv_ratCast, smul_zero, add_zero, smul_eq_mul, ← CField.sem_deriv]
    simp only [map_add, map_mul, map_div₀, map_natCast, ← hιd]
    have hbQι : ι bQ = (T.MP m h0).sem ((MO Fc ks m).deriv a) := T.codeIncl_cv m h0 _
    rw [hbQι]
    have eι : T.codeIncl m h1.of_succ cQ = ι cQ := rfl
    simp only [eι]
    push_cast
    have hn0' : (n : T.F m) ≠ 0 := by exact_mod_cast hsp.1.ne'
    have hcQ0 : ι cQ ≠ 0 := (map_ne_zero_iff _ hιi).mpr (trailingCoeff_nonzero_iff_nonzero.mpr hSQa0)
    field_simp
  have hgp : ∀ i : Fin (P.length - 1),
      (dgEAt Fc ks m dg0 (i : ℕ)).1.den ≠ 1 ∨ (dgEAt Fc ks m dg0 (i : ℕ)).1 ≤ 0 := by
    rw [hNP]
    intro i
    rw [hdg0At i i.2]
    dsimp only
    obtain ⟨q, hq⟩ : ∃ q : ℕ, (τ (fi i) : ℕ) * d0 % n = q := ⟨_, rfl⟩
    have hqn : q < n := hq ▸ Nat.mod_lt _ hsp.1
    rw [hq]
    by_cases hq0 : q = 0
    · right; simp [hq0]
    · left
      intro hden
      have hx := Rat.coe_int_num_of_den_eq_one hden
      have hnq : (0 : ℚ) < n := by exact_mod_cast hsp.1
      have h1' : (0 : ℚ) < (q : ℚ) / n := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hq0) hnq
      have h2' : (q : ℚ) / n < 1 := (div_lt_one hnq).mpr (by exact_mod_cast hqn)
      rw [← hx] at h1' h2'
      have h3 : (0 : ℤ) < ((q : ℚ) / n).num := by exact_mod_cast h1'
      have h4 : ((q : ℚ) / n).num < 1 := by exact_mod_cast h2'
      omega
  exact ⟨Tc, Ti, r', dgL, Cl, Cil, dg0, T.exactTEV_isSome h1 hm hk htr rde hrde dgL r' Cl Cil dg0
    P θ hP hPc (by omega) hind dθ hd Tc Ti hok f Mval hMval M0v hsq' hC1 hC2 hgtri hgdiag hgp Λ
    hprop htri hdiag⟩

end MTower

end Curves.MT
