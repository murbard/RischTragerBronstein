import RischTragerBronstein.Mixed.NKExactTLEVGSome
import RischTragerBronstein.Mixed.NKExactTEVExists
import RischTragerBronstein.Mixed.NKExactTLVGExists
import RischTragerBronstein.Mixed.NKSplitGaugeE
import RischTragerBronstein.Mixed.NKInfRVExp
import RischTragerBronstein.Mixed.NKExactTLEVGExists
import RischTragerBronstein.Mixed.NKExp0Split

/-!
# `exactTLEVG` answers for a curve split at infinity and above `t = 0` (exponential level)

`split0C Pp βs`: the fibre `θⁿ + ∑ aᵢ(0) θⁱ` is `∏ₖ (θ − βₖ)` with distinct `βₖ` (`split0_spec`;
`leadPoly 0 F` is the fibre at `0`, `leadPoly_zero`).

**`exactTLEVG_exists0`**: as `exactTLEVG_exists`, for a curve split at infinity and with a split
fibre above `t = 0` (`n` places above `0`) instead of a single place there: the gauge at `t = 0`
is that of `exists_gauge0_split` (the Lagrange elements of the fibre), whose limit vanishes, so
the diagonal data at `0` are zero.
-/

open Polynomial Differential IntermediateField
open scoped Matrix

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The split fibre check at `t = 0`**: `θⁿ + ∑ aᵢ(0) θⁱ = ∏ₖ (θ − βₖ)`, the `βₖ` distinct. -/
def split0C (m : ℕ) (Pp : List (GPoly (LC m))) (βs : List (LC m)) : Bool :=
  let O := MO Fc ks m
  let n := Pp.length
  decide (0 < n) && decide (βs.length = n) &&
  GPoly.isZero O (GPoly.sub O (leadPolyC Fc ks m Pp 0) (prodXG Fc ks m βs)) &&
  ((List.range n).all fun k ↦ (List.range n).all fun l ↦
    decide (k = l) || !O.isZero (O.add (βs.getD k O.zero) (O.neg (βs.getD l O.zero))))

end Codes

/-- `leadPoly 0 F` is the fibre of `F` at `0`. -/
lemma leadPoly_zero {A : Type*} [Field A] (F : A[X][X]) :
    leadPoly 0 F = F.map (Polynomial.evalRingHom 0) := by
  ext k
  rw [leadPoly, finsetSum_coeff, Polynomial.coeff_map, coe_evalRingHom, ← coeff_zero_eq_eval_zero]
  simp only [coeff_C_mul_X_pow, zero_mul]
  by_cases hk : k ≤ F.natDegree
  · rw [Finset.sum_eq_single k (fun j _ hjk ↦ by rw [if_neg (Ne.symm hjk)])
      (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h), if_pos rfl]
  · rw [Finset.sum_eq_zero fun j hj ↦ by
      rw [if_neg (by have := Finset.mem_range.mp hj; omega)],
      Polynomial.coeff_eq_zero_of_natDegree_lt (p := F) (by omega), Polynomial.coeff_zero]

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The meaning of the split fibre check.** -/
lemma split0_spec (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m))) (βs : List (LC m))
    (hsh : split0C Fc ks m Pp βs = true) :
    0 < Pp.length ∧ βs.length = Pp.length ∧
    leadPoly 0 (T.nkF m h Pp) =
      ∏ k : Fin Pp.length, (X - Polynomial.C ((T.MP m h).sem (βs.getD k (MO Fc ks m).zero))) ∧
    Function.Injective fun k : Fin Pp.length ↦ (T.MP m h).sem (βs.getD k (MO Fc ks m).zero) := by
  classical
  unfold split0C at hsh
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at hsh
  obtain ⟨⟨⟨hn0, hlen⟩, hlead⟩, hdist⟩ := hsh
  have hFn : (T.nkF m h Pp).natDegree = Pp.length := polyF_natDegree _ _
  refine ⟨hn0, hlen, ?_, ?_⟩
  · have h1 := (GPoly.isZero_iff (T.MP m h) _).mp hlead
    rw [GPoly.toPoly_sub, sub_eq_zero, T.toPoly_prodXG m h] at h1
    have hprod : (βs.map fun g ↦ X - Polynomial.C ((T.MP m h).sem g)).prod =
        ∏ k : Fin Pp.length, (X - Polynomial.C ((T.MP m h).sem (βs.getD k (MO Fc ks m).zero))) := by
      rw [← List.prod_ofFn]
      congr 1
      apply List.ext_getElem (by simp [hlen])
      intro k h1 h2
      have hk : k < βs.length := by simp at h1 h2; omega
      rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem _ _ hk]
    rw [← hprod, ← h1]
    ext k
    rw [leadPoly, finsetSum_coeff, coeff_toPoly_sem, hFn]
    simp only [coeff_C_mul_X_pow]
    by_cases hk : k ≤ Pp.length
    · rw [Finset.sum_eq_single k (fun j _ hjk ↦ by rw [if_neg (Ne.symm hjk)])
        (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h), if_pos rfl]
      rcases lt_or_eq_of_le hk with hk | hk
      · rw [nkF, polyF_coeff _ _ _ hk, coeff_toPoly_sem, leadPolyC,
          List.getD_append _ _ _ _ (by simpa using hk),
          List.getD_eq_getElem (l := (List.range Pp.length).map fun i ↦
            (Pp.getD i []).getD (0 * (Pp.length - i)) (MO Fc ks m).zero) _ (by simpa using hk),
          List.getElem_map, List.getElem_range]
      · subst hk
        have hmon := (polyF_monic (fun i ↦ GPoly.toPoly (T.MP m h) (Pp.getD i [])) Pp.length)
        have h1 : (T.nkF m h Pp).coeff Pp.length = 1 := by
          rw [← hFn]; exact hmon.coeff_natDegree
        rw [h1, Nat.sub_self, mul_zero, coeff_one_zero, leadPolyC,
          List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range,
          Nat.sub_self, List.getD_cons_zero, (T.MP m h).sem_one]
    · rw [Finset.sum_eq_zero fun j hj ↦ by
        rw [if_neg (by have := Finset.mem_range.mp hj; omega)], leadPolyC,
        List.getD_eq_default _ _ (by simp; omega), (T.MP m h).sem_zero]
  · intro k l hkl
    by_contra hne
    rcases hdist k k.2 l l.2 with h2 | h2
    · exact hne (Fin.ext h2)
    · have h3 : (MO Fc ks m).isZero ((MO Fc ks m).add (βs.getD k (MO Fc ks m).zero)
          ((MO Fc ks m).neg (βs.getD l (MO Fc ks m).zero))) = true := by
        rw [(T.MP m h).isZero_iff, (T.MP m h).sem_add, (T.MP m h).sem_neg, ← sub_eq_add_neg]
        exact sub_eq_zero.mpr hkl
      rw [h3] at h2
      exact Bool.noConfusion h2

set_option maxHeartbeats 8000000 in
/-- **`exactTLEVG` answers for a suitable basis of a curve split at infinity and above `t = 0`**
(exponential level, any coefficients). -/
theorem exactTLEVG_exists0 (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {a : LC m}
    (hk : ks m = .exp a) (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (s : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc ks m Pp s γs = true)
    (βs : List (LC m)) (hsp0 : split0C Fc ks m Pp βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    ∃ (Tc Ti : List (List (LC (m + 1)))) (r : ℕ → ℤ) (Cg Cgi C Ci : List (List (LC m)))
      (dg0 : List (ℚ × ℚ × LC m)),
      (exactTLEVG Fc ks m a rde [] Cg Cgi r C Ci dg0 (nkPC Fc ks m Pp) Tc Ti f gs).isSome := by
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
  set bQ : C := T.cv m h0 ((MO Fc ks m).deriv a) with hbQ
  have hx : SQ.x′ = aeval SQ.x (Polynomial.C bQ * X) := by
    rw [map_mul, aeval_C, aeval_X]
    change (T.ts m)′ = _
    rw [T.deriv_ts_L_exp m h0 hm hk]
    rfl
  obtain ⟨hn0, hlenγ, hdegF, hLF, hinjF⟩ := T.splitShape_spec m h0 Pp s γs hsplit
  set n := Pp.length with hn
  have hSQn : SQ.F.natDegree = n := polyF_natDegree _ _
  set ι := T.codeIncl m h0 with hι
  have hιi := T.codeIncl_injective m h0
  have hFF : (T.nkF m h0 Pp).natDegree = n := polyF_natDegree _ _
  have hdegQ : ∀ i < SQ.F.natDegree, (SQ.F.coeff i).natDegree ≤ s * (SQ.F.natDegree - i) := by
    intro i hi
    rw [show SQ.F = T.nkFQ m h0 Pp from rfl, T.nkFQ_natDegree_coeff]
    have := hdegF i (by rw [hFF]; rw [hSQn] at hi; exact hi)
    rw [hFF] at this
    rw [show (T.nkFQ m h0 Pp).natDegree = n from polyF_natDegree _ _]
    exact this
  set γQ : Fin SQ.F.natDegree → C := fun k ↦ T.cv m h0 (γs.getD k (MO Fc ks m).zero) with hγQ
  have hγι : ∀ k : Fin SQ.F.natDegree, ι (γQ k) = (T.MP m h0).sem (γs.getD k (MO Fc ks m).zero) :=
    fun k ↦ T.codeIncl_cv m h0 _
  have hinjQ : Function.Injective γQ := by
    intro k l hkl
    have h2 := congrArg ι hkl
    rw [hγι, hγι] at h2
    have := hinjF (a₁ := ⟨k, by rw [← hSQn]; exact k.2⟩) (a₂ := ⟨l, by rw [← hSQn]; exact l.2⟩) h2
    exact Fin.ext (by simpa using congrArg Fin.val this)
  have hLQ : leadPoly s SQ.F = ∏ k, (X - Polynomial.C (γQ k)) := by
    apply Polynomial.map_injective _ hιi
    rw [← leadPoly_map, show SQ.F.map (mapRingHom ι) = T.nkF m h0 Pp from T.map_nkFQ m h0 Pp,
      hLF, Polynomial.map_prod]
    refine (Fintype.prod_equiv (finCongr hSQn.symm) _ _ fun k ↦ ?_)
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  -- the split fibre above `t = 0`
  obtain ⟨-, hlenβ, hL0, hinj0⟩ := T.split0_spec m h0 Pp βs hsp0
  set βQ : Fin SQ.F.natDegree → C := fun k ↦ T.cv m h0 (βs.getD k (MO Fc ks m).zero) with hβQ
  have hβι : ∀ k : Fin SQ.F.natDegree, ι (βQ k) = (T.MP m h0).sem (βs.getD k (MO Fc ks m).zero) :=
    fun k ↦ T.codeIncl_cv m h0 _
  have hinjβ : Function.Injective βQ := by
    intro k l hkl
    have h2 := congrArg ι hkl
    rw [hβι, hβι] at h2
    have hk2 : (k : ℕ) < Pp.length := by have := k.2; have := hSQn; omega
    have hl2 : (l : ℕ) < Pp.length := by have := l.2; have := hSQn; omega
    have := hinj0 (a₁ := ⟨k, by omega⟩) (a₂ := ⟨l, by omega⟩) h2
    exact Fin.ext (by simpa using congrArg Fin.val this)
  have hfibQ : SQ.F.map (Polynomial.evalRingHom 0) = ∏ k, (X - Polynomial.C (βQ k)) := by
    apply Polynomial.map_injective _ hιi
    rw [← leadPoly_zero, ← leadPoly_map, show SQ.F.map (mapRingHom ι) = T.nkF m h0 Pp from
      T.map_nkFQ m h0 Pp, hL0, Polynomial.map_prod]
    refine (Fintype.prod_equiv (finCongr hSQn.symm) _ _ fun k ↦ ?_)
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  obtain ⟨w, r, S0, Pm, hwB, hrw, hredw, hindw, hS00, hsq, hS0c, hder, hdeg⟩ :=
    SQ.exists_nkBasisEG (K := K) bQ hx hK
  obtain ⟨Ag, hAg0, hAg'⟩ := SQ.split_gaugeE (K := K) bQ hx hK s hdegQ γQ hinjQ hLQ w r hrw hredw
    S0 hS00 Pm hder hdeg
  obtain ⟨A, B, Ai, Bi, hB, hBi, hwA, hTTi, hTiT⟩ := SQ.exists_coordMats w hindw
  -- the gauge at `t = 0`
  obtain ⟨U0, Ui0, hUUi0, hUiU0, hLam0⟩ := SQ.exists_gauge0_split (K := K) bQ hx hK βQ hinjβ hfibQ
    w hwB S0 hS0c Pm hder
  set Lam := (U0.map (fun z ↦ z′) + U0 * Matrix.of (fun i j ↦ (Pm i j).coeff 0 / S0.coeff 0)) * Ui0
    with hLam
  set τ : Equiv.Perm (Fin SQ.F.natDegree) := Equiv.refl _ with hτ
  set σ : Equiv.Perm (Fin SQ.F.natDegree) := Equiv.refl _ with hσdef
  set RF : Fin SQ.F.natDegree → (T.F m)[X] := fun i ↦ (X ^ r (σ i) * S0).map ι with hRF
  set PF : Fin SQ.F.natDegree → Fin SQ.F.natDegree → (T.F m)[X] := fun i j ↦
    (Curves.CurveData.pqE bQ r Pm S0 (σ i) (σ j)).map ι with hPF
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
  -- the value at `t = 0`
  set M0 : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) C :=
    Matrix.of (fun i j ↦ (Pm i j).coeff 0 / S0.coeff 0) with hM0
  set M0Q : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) C := (M0.submatrix σ σ)ᵀ with hM0Q
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
  -- the limit in terms of the code values
  set ΛQ : Fin SQ.F.natDegree → Fin SQ.F.natDegree → C := fun i j ↦
    (Curves.CurveData.pqE bQ r Pm S0 i j).coeff (X ^ r i * S0).natDegree /
      (X ^ r i * S0).leadingCoeff with hΛQ
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
  -- `U F = U′` with `F a b = Λ b a`
  have hUF : ∀ a b : Fin SQ.F.natDegree, ∑ k, U a k * ΛQ b k = (U a b)′ := by
    intro a b
    rw [hU, Matrix.transpose_apply, hAg' b a]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [Matrix.transpose_apply]; ring
  set Clg : List (List (LC m)) := (List.range SQ.F.natDegree).map fun a ↦
    (List.range SQ.F.natDegree).map fun b ↦ T.cvCode (U (fi a) (fi b)) with hClg
  set Cilg : List (List (LC m)) := (List.range SQ.F.natDegree).map fun a ↦
    (List.range SQ.F.natDegree).map fun b ↦ T.cvCode (Ui (fi a) (fi b)) with hCilg
  have hcg : ∀ a b : Fin SQ.F.natDegree, (T.MP m h0).sem (cgV Fc ks m Clg a b) = ι (U a b) :=
    fun a b ↦ by
      rw [cgV, hClg, NestTower.getD_range_map _ _ a.2, NestTower.getD_range_map _ _ b.2,
        T.sem_cvCode, hfi a a.2, hfi b b.2]
  have hcig : ∀ a b : Fin SQ.F.natDegree, (T.MP m h0).sem (cgV Fc ks m Cilg a b) = ι (Ui a b) :=
    fun a b ↦ by
      rw [cgV, hCilg, NestTower.getD_range_map _ _ a.2, NestTower.getD_range_map _ _ b.2,
        T.sem_cvCode, hfi a a.2, hfi b b.2]
  have hinvg : invOKG Fc ks m (P.length - 1) Clg Cilg = true := by
    rw [hNP]
    refine T.invOKG_of h0 Clg Cilg (fun i j ↦ ?_) (fun i j ↦ ?_)
    · simp only [hcg, hcig, ← map_mul, ← map_sum]
      have := congrFun (congrFun hUUi i) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      rw [this]; split_ifs <;> simp
    · simp only [hcg, hcig, ← map_mul, ← map_sum]
      have := congrFun (congrFun hUiU i) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      rw [this]; split_ifs <;> simp
  have hιd : ∀ z : C, (ι z)′ = ι (z′) := fun z ↦ rfl
  have hgauge : ∀ a b : Fin (P.length - 1), gaugeM
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Clg i j))
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cilg i j))
      (fun a b : Fin (P.length - 1) ↦ Λ b a) a b = 0 := by
    rw [hNP]
    intro a b
    simp only [gaugeM, hcg, hcig, hΛι, hιd]
    rw [sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← Finset.sum_mul, ← hUF a l]
    simp only [map_sum, map_mul]
  have htri : ∀ a b : Fin (P.length - 1), b < a → gaugeM
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Clg i j))
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cilg i j))
      (fun a b : Fin (P.length - 1) ↦ Λ b a) a b = 0 := fun a b _ ↦ hgauge a b
  have hdiag : ∀ i : Fin (P.length - 1), gaugeM
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Clg i j))
      (fun i j : Fin (P.length - 1) ↦ (T.MP m h1.of_succ).sem (cgV Fc ks m Cilg i j))
      (fun a b : Fin (P.length - 1) ↦ Λ b a) i i =
        (T.MP m h1.of_succ).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m [] i))) := fun i ↦ by
    rw [hgauge i i, sem_fCode]
    simp [frE, dgEAt, logSumV, T.sem_mcst m h0, CField.sem_mul]
  -- the gauge at `t = 0`
  set Uσ : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) C := U0.submatrix τ σ with hUσ
  set Uiσ : Matrix (Fin SQ.F.natDegree) (Fin SQ.F.natDegree) C := Ui0.submatrix σ τ with hUiσ
  set Cm := Uiσᵀ with hCm
  set Cim := Uσᵀ with hCim
  have hUσ1 : Uσ * Uiσ = 1 := by
    rw [hUσ, hUiσ, Matrix.submatrix_mul_equiv, hUUi0, Matrix.submatrix_one_equiv]
  have hUiσ1 : Uiσ * Uσ = 1 := by
    rw [hUσ, hUiσ, Matrix.submatrix_mul_equiv, hUiU0, Matrix.submatrix_one_equiv]
  have hGQ : Cm * M0Q * Cim - Cm.map (fun z ↦ z′) * Cim = (Lam.submatrix τ τ)ᵀ := by
    rw [hCm, hM0Q, hCim, gauge_transpose Uσ Uiσ (M0.submatrix σ σ) hUσ1, hLam]
    congr 1
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
  have hιd : ∀ z : C, (ι z)′ = ι (z′) := fun z ↦ rfl
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
    intro i j _
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.submatrix_apply]
    rw [hLam0, Matrix.zero_apply, map_zero]
  -- the diagonal at `t = 0`
  set dg0 : List (ℚ × ℚ × LC m) := (List.range SQ.F.natDegree).map fun _ ↦
    ((0 : ℚ), (0 : ℚ), (MO Fc ks m).one) with hdg0
  have hdg0At : ∀ a (ha : a < SQ.F.natDegree), dgEAt Fc ks m dg0 a =
      ((0 : ℚ), (0 : ℚ), (MO Fc ks m).one) :=
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
    rw [hLam0, Matrix.zero_apply, map_zero, hdg0At i i.2, sem_fCode]
    simp only [frE, logSumV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      CField.sem_mul, T.sem_mcst m h0, Differential.logDeriv, CField.sem_one]
    simp
  have hgp : ∀ i : Fin (P.length - 1),
      (dgEAt Fc ks m dg0 (i : ℕ)).1.den ≠ 1 ∨ (dgEAt Fc ks m dg0 (i : ℕ)).1 ≤ 0 := by
    rw [hNP]
    intro i
    rw [hdg0At i i.2]
    right; exact le_refl _
  exact ⟨Tc, Ti, r', Clg, Cilg, Cl, Cil, dg0, T.exactTLEVG_isSome h1 hm hk htr rde [] Clg Cilg r'
    Cl Cil dg0 P θ hP hPc (by rw [hNP, hSQn]; exact hn0.ne') hind dθ hd Tc Ti hok f gs Mval hMval M0v
    hsq' hC1 hC2 hgtri hgdiag hgp Λ hprop hinvg htri hdiag⟩

end MTower

end Curves.MT
