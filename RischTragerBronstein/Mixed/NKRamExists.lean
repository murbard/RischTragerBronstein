import RischTragerBronstein.Mixed.NKExactTLVGExists
import RischTragerBronstein.Mixed.NKRamGauge
import RischTragerBronstein.Mixed.NKRamShape

/-!
# `exactTLVG` answers for curves with ramified places at infinity (logarithmic level)

**`exactTLVG_exists_ram`**: for `θⁿ + ∑ aᵢ(t) θⁱ = 0` over a logarithmic level with any
coefficients in `Fₘ[t]` (Eisenstein certificate) and a single slope `s'/e` at infinity with
rational places (`ramShapeC`), there are a basis, shifts, a gauge `C` at infinity and diagonal data
`dg` (`((t/e), γₖ)`: `(t/e) γₖ′/γₖ`) for which `exactTLVG` answers. The gauge is `ram_gauge`'s `A`
with its columns sorted by decreasing level; the limit system is non-degenerate because the jets
of `ram_gauge` (taken over the algebraic closure of `Fₘ`) make it gauge-trivial there
(`nondeg_of_gauge'`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

section Gauge'

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential C] [Differential K]

theorem nondeg_of_gauge' (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
    {ι : Type*} [Fintype ι] (Λ : ι → ι → C) {κ : Type*} (A : ι → κ → K)
    (hind : ∀ c : ι → K, (∀ k, ∑ i, c i * A i k = 0) → ∀ i, c i = 0)
    (hA : ∀ i k, (A i k)′ = ∑ j, algebraMap C K (Λ i j) * A j k)
    (η : C) (hη : ∀ a : K, a′ ≠ algebraMap C K η)
    (c : ι → C) (hc : c ≠ 0) (hhom : ∀ j, (c j)′ + ∑ i, Λ i j * c i = 0) :
    ¬∃ y : ι → C, ∀ j, (y j)′ + ∑ i, Λ i j * y i = η * c j := by
  classical
  rintro ⟨y, hy⟩
  have hvd : ∀ (z : ι → C) (g : ι → C), (∀ j, (z j)′ + ∑ i, Λ i j * z i = g j) → ∀ k,
      (∑ i, algebraMap C K (z i) * A i k)′ = ∑ j, algebraMap C K (g j) * A j k := by
    intro z g hz k
    have hg : ∀ j, g j = (z j)′ + ∑ i, Λ i j * z i := fun j ↦ (hz j).symm
    simp only [hg, map_sum, Derivation.leibniz, smul_eq_mul, hK, hA _ k, map_add, map_mul,
      add_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun i _ ↦ by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- a coefficient where the combination does not vanish
  have hcK : (fun i ↦ algebraMap C K (c i)) ≠ 0 := by
    intro h
    apply hc
    funext i
    have := congrFun h i
    exact (algebraMap C K).injective (by simpa using this)
  have : ∃ k, ∑ i, algebraMap C K (c i) * A i k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hcK (funext (hind _ hcon))
  obtain ⟨k, hv0⟩ := this
  have hv' := hvd c 0 (fun j ↦ by rw [hhom j]; rfl) k
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at hv'
  have hu' := hvd y (fun j ↦ η * c j) hy k
  apply hη ((∑ i, algebraMap C K (y i) * A i k) / ∑ i, algebraMap C K (c i) * A i k)
  rw [Derivation.leibniz_div, hv', hu', smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_zero, sub_zero]
  simp only [map_mul, mul_assoc, ← Finset.mul_sum]
  field_simp


end Gauge'

/-- The leading polynomial of weight `σ` commutes with coefficient maps. -/
lemma leadPolyR_map {A B : Type*} [Field A] [Field B] (φ : A →+* B) (N σ : ℕ) (F : A[X][X]) :
    (leadPolyR N σ F).map φ = leadPolyR N σ (F.map (mapRingHom φ)) := by
  rw [leadPolyR, leadPolyR, Polynomial.map_sum, natDegree_map_eq_of_injective
    (Polynomial.map_injective _ φ.injective)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, coeff_map,
    coe_mapRingHom]
  split_ifs <;> simp [coeff_map]

end Curves

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **`exactTLVG` answers for a suitable basis of a curve with ramified places at infinity**
(single slope `s'/e`, rational places, any coefficients). -/
theorem exactTLVG_exists_ram (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m}
    (hk : ks m = .prim η) (htr : Transcendental (T.F m) (T.ts m))
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h1.of_succ).sem η)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sR γs = true) (θ : L)
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
  set K := AlgebraicClosure (T.F m) with hKdef
  letI algCK : Algebra C K := ((algebraMap (T.F m) K).comp (T.codeIncl m h0)).toAlgebra
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (T.F m) K).injective
  have hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′ := fun c ↦ by
    show (algebraMap (T.F m) K (T.codeIncl m h0 c))′ = algebraMap (T.F m) K (T.codeIncl m h0 (c′))
    rw [deriv_algebraMap]; rfl
  set SQ := T.nkCurveQE m h1 Pp qE csE sE tE s2E t2E hck θ hθ with hSQ
  set ηQ : C := T.cv m h0 η with hηQ
  have hx : SQ.x′ = aeval SQ.x (Polynomial.C ηQ) := by
    rw [aeval_C]
    change (T.ts m)′ = _
    rw [T.deriv_ts_L m h0 hm hk]
    rfl
  obtain ⟨hn0, he, hedvd, hcopR, hlenγ, hdegF, hLF, hinjF, hγ0F⟩ :=
    T.ramShape_spec m h0 Pp e sR γs hram
  set n := Pp.length with hn
  have hSQn : SQ.F.natDegree = n := polyF_natDegree _ _
  set ι := T.codeIncl m h0 with hι
  have hιi := T.codeIncl_injective m h0
  have hFF : (T.nkF m h0 Pp).natDegree = n := polyF_natDegree _ _
  have hdegQ : ∀ i < SQ.F.natDegree, e * (SQ.F.coeff i).natDegree ≤ sR * (SQ.F.natDegree - i) := by
    intro i hi
    rw [show SQ.F = T.nkFQ m h0 Pp from rfl, T.nkFQ_natDegree_coeff]
    have := hdegF i (by rw [hFF]; rw [hSQn] at hi; exact hi)
    rw [hFF] at this
    rw [show (T.nkFQ m h0 Pp).natDegree = n from polyF_natDegree _ _]
    exact this
  obtain ⟨rr, hrr⟩ : ∃ rr, n / e = rr + 1 :=
    ⟨n / e - 1, by have := Nat.div_pos (Nat.le_of_dvd hn0 hedvd) he; omega⟩
  set γQ : Fin (rr + 1) → C := fun k ↦ T.cv m h0 (γs.getD k (MO Fc ks m).zero) with hγQ
  have hγι : ∀ k : Fin (rr + 1), ι (γQ k) = (T.MP m h0).sem (γs.getD k (MO Fc ks m).zero) :=
    fun k ↦ T.codeIncl_cv m h0 _
  have hinjQ : Function.Injective γQ := by
    intro k l hkl
    have h2 := congrArg ι hkl
    rw [hγι, hγι] at h2
    have := hinjF (a₁ := ⟨k, by rw [hrr]; exact k.2⟩) (a₂ := ⟨l, by rw [hrr]; exact l.2⟩) h2
    exact Fin.ext (by simpa using congrArg Fin.val this)
  have hγQ0 : ∀ k, γQ k ≠ 0 := fun k h ↦
    hγ0F ⟨k, by rw [hrr]; exact k.2⟩ (by rw [← hγι k, h, map_zero])
  have hLQ : leadPolyR e sR SQ.F = ∏ k, (X ^ e - Polynomial.C (γQ k)) := by
    apply Polynomial.map_injective _ hιi
    rw [leadPolyR_map, show SQ.F.map (mapRingHom ι) = T.nkF m h0 Pp from T.map_nkFQ m h0 Pp,
      hLF, Polynomial.map_prod]
    refine (Fintype.prod_equiv (finCongr hrr) _ _ fun k ↦ ?_)
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [hγι]; rfl
  obtain ⟨w, r, S0, Pm, hwB, hrw, hredw, hindw, hS00, hsq, hder, hdeg⟩ :=
    SQ.exists_nkBasisG (K := K) ηQ hx hK
  obtain ⟨Ag, Agi, Tg, hAAi, hAiA, hderA, hlowT, hdiagT, Jt, hindJ, hJder⟩ :=
    SQ.ram_gauge (K := K) ηQ hx hK e sR he hcopR γQ hinjQ hγQ0 hdegQ hLQ w r hrw hredw S0 hS00 Pm
      hder hdeg
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
  -- the gauge: the columns of `Ag` sorted by decreasing level
  have hne : SQ.F.natDegree = e * (rr + 1) := by rw [hSQn, ← hrr, Nat.mul_div_cancel' hedvd]
  set σI : Fin SQ.F.natDegree ≃ Fin e × Fin (rr + 1) :=
    (finCongr hne).trans (finProdFinEquiv.symm.trans (Equiv.prodCongr Fin.revPerm (Equiv.refl _)))
    with hσI
  have hσ1 : ∀ a : Fin SQ.F.natDegree, ((σI a).1 : ℕ) = e - 1 - (a : ℕ) / (rr + 1) := by
    intro a
    simp [hσI, Fin.rev]
    omega
  have hσlev : ∀ a b : Fin SQ.F.natDegree, b < a → (σI a).1 ≤ (σI b).1 := by
    intro a b hba
    rw [Fin.le_def, hσ1, hσ1]
    have : (b : ℕ) / (rr + 1) ≤ (a : ℕ) / (rr + 1) := Nat.div_le_div_right hba.le
    omega
  set U : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) C := fun a i ↦ Ag i (σI a) with hU
  set Ui : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) C := fun i a ↦ Agi (σI a) i with hUi
  have hUUi : U * Ui = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    have := congrFun (congrFun hAiA (σI b)) (σI a)
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [hU, hUi]
    rw [show (∑ i, Ag i (σI a) * Agi (σI b) i) = ∑ i, Agi (σI b) i * Ag i (σI a) from
      Finset.sum_congr rfl fun i _ ↦ mul_comm _ _, this]
    simp only [σI.injective.eq_iff, eq_comm]
  have hUiU : Ui * U = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hU, hUi]
    have := congrFun (congrFun hAAi j) i
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [show (∑ a, Agi (σI a) i * Ag j (σI a)) = ∑ x, Ag j x * Agi x i from
      Fintype.sum_equiv σI _ _ fun a ↦ mul_comm _ _, this]
    simp only [eq_comm]
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
  -- the gauged limit is `Tgᵀ`
  have hgC : ∀ x y : Fin e × Fin (rr + 1), ∑ k, ∑ l, Ag k y * ΛQ l k * Agi x l -
      ∑ k, (Ag k y)′ * Agi x k = Tg x y := by
    intro x y
    simp only [hderA, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    have e1 : ∑ k, ∑ j, ΛQ k j * Ag j y * Agi x k = ∑ k, ∑ l, Ag k y * ΛQ l k * Agi x l := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
    have e2 : ∑ k, ∑ c, Ag k c * Tg c y * Agi x k = Tg x y := by
      rw [Finset.sum_comm]
      have h3 : ∀ c, ∑ k, Ag k c * Tg c y * Agi x k = (Agi * Ag) x c * Tg c y := fun c ↦ by
        rw [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
      simp only [h3, hAiA, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    have hΛ' : ∀ k j, ΛQ k j = (Curves.CurveData.pqV ηQ r Pm S0 k j).coeff
        (X ^ (r k + 1) * S0).natDegree / (X ^ (r k + 1) * S0).leadingCoeff := fun k j ↦ rfl
    simp only [← hΛ']
    rw [e1, e2]
    ring
  have hgaugeT : ∀ a b : Fin SQ.F.natDegree, gaugeM
      (fun i j : Fin SQ.F.natDegree ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cl i j))
      (fun i j : Fin SQ.F.natDegree ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cil i j))
      (fun a b : Fin SQ.F.natDegree ↦ Λ b a) a b = ι (Tg (σI b) (σI a)) := by
    intro a b
    rw [← hgC (σI b) (σI a)]
    simp only [gaugeM, hcg, hcig, hΛι, hιd, map_sub, map_sum, map_mul, hU, hUi]
  -- the diagonal data
  choose t0 ht0 hlt0 using fun R : Fin e ↦ exists_levR e sR he hcopR R R.2
  set dgL : List (FRep (LC m)) := (List.range SQ.F.natDegree).map fun a ↦
    ⟨(MO Fc ks m).zero, [(mcst Fc ks m ((t0 (σI (fi a)).1 : ℚ) / e),
      γs.getD (σI (fi a)).2 (MO Fc ks m).zero)]⟩ with hdgL
  have hdgAt : ∀ a (ha : a < SQ.F.natDegree), dgAt Fc ks m dgL a =
      ⟨(MO Fc ks m).zero, [(mcst Fc ks m ((t0 (σI (fi a)).1 : ℚ) / e),
        γs.getD (σI (fi a)).2 (MO Fc ks m).zero)]⟩ := fun a ha ↦ by
    rw [dgAt, hdgL, NestTower.getD_range_map _ _ ha]
  have hdgAt' : ∀ a, SQ.F.natDegree ≤ a → dgAt Fc ks m dgL a = ⟨(MO Fc ks m).zero, []⟩ :=
    fun a ha ↦ by rw [dgAt, List.getD_eq_default _ _ (by simpa [hdgL] using ha)]
  have htri : ∀ a b : Fin (P.length - 1), b < a → gaugeM
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cl i j))
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cil i j))
      (fun a b : Fin (P.length - 1) ↦ Λ b a) a b = 0 := by
    rw [hNP]
    intro a b hba
    rw [hgaugeT a b]
    have hle := hσlev a b hba
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [hlowT (σI b) (σI a) hlt, map_zero]
    · have hy : σI a = ((σI b).1, (σI a).2) := Prod.ext heq rfl
      have hx : σI b = ((σI b).1, (σI b).2) := rfl
      have h2 := hdiagT (σI b).1 (σI b).2 (σI a).2 (t0 (σI b).1) (ht0 _) (hlt0 _)
      rw [hy]
      conv_lhs => rw [hx]
      rw [h2, if_neg, map_zero]
      intro hkk
      have : σI b = σI a := Prod.ext heq.symm hkk
      exact absurd (σI.injective this) (ne_of_lt hba)
  have hdiag : ∀ a : Fin (P.length - 1), gaugeM
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cl i j))
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cil i j))
      (fun a b : Fin (P.length - 1) ↦ Λ b a) a a =
        (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (dgAt Fc ks m dgL a)) := by
    rw [hNP]
    intro a
    rw [hgaugeT a a, hdgAt a a.2, sem_fCode, hfi a a.2]
    have hx : σI a = ((σI a).1, (σI a).2) := rfl
    have h2 := hdiagT (σI a).1 (σI a).2 (σI a).2 (t0 (σI a).1) (ht0 _) (hlt0 _)
    rw [if_pos rfl, ← hx] at h2
    rw [h2]
    simp only [Fin.eta, logSumV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      (T.MP m h1.of_succ).sem_zero, Derivation.map_zero, zero_add, T.sem_mcst m h0,
      Differential.logDeriv]
    rw [← hγι, map_mul, map_div₀, map_div₀, map_natCast, map_natCast, ← hιd]
    push_cast
    ring
  have hokd : ∀ i, ∀ cw ∈ (dgAt Fc ks m dgL i).logs, ((T.MP m h1.of_succ).sem cw.1)′ = 0 := by
    intro i cw hcw
    by_cases hi : i < SQ.F.natDegree
    · rw [hdgAt i hi] at hcw
      simp only [List.mem_singleton] at hcw
      rw [hcw, T.sem_mcst m h0]
      exact T.deriv_ratCast _
    · rw [hdgAt' i (by omega)] at hcw
      simp at hcw
  -- non-degeneracy, through the jets over the algebraic closure of `Fₘ`
  have hηK : ∀ a : K, a′ ≠ algebraMap (T.F m) K ((T.MP m h0).sem η) := fun a ↦
    not_deriv_of_integral _ hη a (Algebra.IsIntegral.isIntegral a)
  have hnd : ∀ c : Fin (P.length - 1) → T.F m, c ≠ 0 →
      (∀ a : Fin (P.length - 1), (c a)′ + ∑ b : Fin (P.length - 1), Λ b a * c b = 0) →
      ¬ ∃ y : Fin (P.length - 1) → T.F m, ∀ a : Fin (P.length - 1),
        (y a)′ + ∑ b : Fin (P.length - 1), Λ b a * y b = (T.MP m h1.of_succ).sem η * c a := by
    rw [hNP]
    intro c hc hhom
    refine nondeg_of_gauge' (C := T.F m) (K := K) (fun z ↦ deriv_algebraMap z)
      (fun i j : Fin SQ.F.natDegree ↦ Λ i j) Jt (fun c' hc' ↦ fun i ↦ congrFun (hindJ c' hc') i)
      (fun i b ↦ ?_) ((T.MP m h0).sem η) hηK c hc hhom
    rw [hJder i b]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hΛι]
    rfl
  exact ⟨Tc, Ti, r', Cl, Cil, dgL, T.exactTLVG_isSome h1 hm hk htr rde hrde dgL Cl Cil r'
    P θ hP hPc (by rw [hNP, hSQn]; exact hn0.ne') hind dθ hd Tc Ti hok f gs Mval hMval hsq' Λ hprop
    hinv htri hdiag hokd hnd⟩

end MTower

end Curves.MT
