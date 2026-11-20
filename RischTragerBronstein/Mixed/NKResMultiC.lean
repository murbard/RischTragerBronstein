import RischTragerBronstein.Mixed.NKResMulti
import RischTragerBronstein.Mixed.NKResRamConjC
import RischTragerBronstein.Mixed.NKMultiRShape
import RischTragerBronstein.Mixed.KXSem

/-!
# Code-level zero-residue certificate for several Newton segments at infinity

`multiResCk Pp segs βs Θs M fp`: for every segment `(eₖ, sₖ, K₀ₖ, cₖ, Γₖ)` of `multiShapeRC` and every
place `γ ∈ Γₖ`, an `eₖ`-th root `β` of `γ` (a code), a truncation `Θ̃` of the segment root with
`Θ̃(0) = β`, `Q(τ, Θ̃) ≡ 0 mod τᴹ` (`segEvalC`), `∂Q(0, β) ≠ 0` (`segResidC`), and the derivative
test on `∑ⱼ ∑ₗ fⱼₗ [τ^{e + e l + s j}] Θ̃ʲ` (`segResC`). `zero_res_multiC`: then all residues of
`f` at infinity vanish (`zero_res_multi`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Tower.PrimN GTors Differential

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The code of `segCoef e s K₀ i a`. -/
def segCoefC (m e : ℕ) (s K0 : ℤ) (i : ℕ) (a : GPoly (LC m)) : GPoly (LC m) :=
  (List.range a.length).foldr (fun l acc ↦ GPoly.add (MO Fc ks m)
    (GPoly.mul (MO Fc ks m) [a.getD l (MO Fc ks m).zero]
      (monoG Fc ks m (K0 - i * s - e * l).toNat)) acc) []

/-- The coefficients of the segment polynomial. -/
def segPolyC (m e : ℕ) (s K0 : ℤ) (Pp : List (GPoly (LC m))) : List (GPoly (LC m)) :=
  (List.range (Pp.length + 1)).map fun i ↦ segCoefC Fc ks m e s K0 i (coefC Fc ks m Pp i)

/-- `Q(τ, Θ̃)`. -/
def segEvalC (m e : ℕ) (s K0 : ℤ) (Pp : List (GPoly (LC m))) (Θ : GPoly (LC m)) : GPoly (LC m) :=
  evalPolyC Fc ks m (segPolyC Fc ks m e s K0 Pp) Θ

/-- The residual polynomial `Q(0, Z)`. -/
def segResidC (m e : ℕ) (s K0 : ℤ) (Pp : List (GPoly (LC m))) : GPoly (LC m) :=
  (segPolyC Fc ks m e s K0 Pp).map fun p ↦ p.getD 0 (MO Fc ks m).zero

/-- The residue value `∑ⱼ ∑ₗ fⱼₗ [τ^{e + e l + s j}] Θʲ` (`0` at negative indices). -/
def segResC (m e : ℕ) (s : ℤ) (n : ℕ) (fp : List (GPoly (LC m))) (Θ : GPoly (LC m)) : LC m :=
  lsumC (MO Fc ks m) ((List.range n).map fun j ↦
    lsumC (MO Fc ks m) ((List.range (fp.getD j []).length).map fun l ↦
      (MO Fc ks m).mul ((fp.getD j []).getD l (MO Fc ks m).zero)
        (if 0 ≤ (e : ℤ) + e * l + s * j then
          (powG (MO Fc ks m) Θ j).getD ((e : ℤ) + e * l + s * j).toNat (MO Fc ks m).zero
        else (MO Fc ks m).zero)))

/-- **The zero-residue certificate for several segments.** -/
def multiResCk (m : ℕ) (Pp : List (GPoly (LC m))) (segs : List (SegRC m))
    (βs : List (List (LC m))) (Θs : List (List (GPoly (LC m)))) (M : ℕ)
    (fp : List (GPoly (LC m))) : Bool :=
  let O := MO Fc ks m
  let n := Pp.length
  (List.range segs.length).all fun k ↦
    let sg := segs.getD k (segRD Fc ks m)
    decide ((βs.getD k []).length = sg.2.2.2.2.length) &&
    (List.range sg.2.2.2.2.length).all (fun i ↦
      let β := (βs.getD k []).getD i O.zero
      let Θ := (Θs.getD k []).getD i []
      O.isZero (O.add (powC O β sg.1) (O.neg (sg.2.2.2.2.getD i O.zero))) &&
      O.isZero (O.add (Θ.getD 0 O.zero) (O.neg β)) &&
      truncOKC Fc ks m M (segEvalC Fc ks m sg.1 sg.2.1 sg.2.2.1 Pp Θ) &&
      !O.isZero (evalLC Fc ks m (GPoly.derivX O (segResidC Fc ks m sg.1 sg.2.1 sg.2.2.1 Pp)) β) &&
      derivTestC Fc ks lv m (segResC Fc ks m sg.1 sg.2.1 n fp Θ)) &&
    (List.range n).all fun j ↦ (List.range (max 1 (fp.getD j []).length)).all fun l ↦
      decide ((sg.1 : ℤ) + sg.1 * l + sg.2.1 * j < M)

/-- Newton lifting of a simple residual root `β` of a segment (untrusted, checked by
`multiResCk`). -/
def segHenselC (m e : ℕ) (s K0 : ℤ) (Pp : List (GPoly (LC m))) (M : ℕ) (β : LC m) : GPoly (LC m) :=
  let O := MO Fc ks m
  let Qc := segPolyC Fc ks m e s K0 Pp
  let d := O.inv (evalLC Fc ks m (GPoly.derivX O (segResidC Fc ks m e s K0 Pp)) β)
  ((List.range M).drop 1).foldl (fun Θ i ↦
    Θ ++ [O.neg (O.mul d ((evalPolyC Fc ks m Qc Θ).getD i O.zero))]) [β]

/-- The truncations of all places from the given `eₖ`-th roots. -/
def multiHensel (m : ℕ) (Pp : List (GPoly (LC m))) (segs : List (SegRC m))
    (βs : List (List (LC m))) (M : ℕ) : List (List (GPoly (LC m))) :=
  (List.range segs.length).map fun k ↦
    let sg := segs.getD k (segRD Fc ks m)
    (βs.getD k []).map (segHenselC Fc ks m sg.1 sg.2.1 sg.2.2.1 Pp M)

end Codes

section Sem

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {m : ℕ} {F : Type*} [Field F] [Differential F] (M : CField (LC m) F (MO Fc ks m))

lemma toPoly_monoG' (k : ℕ) : GPoly.toPoly M (monoG Fc ks m k) = X ^ k := by
  induction k with
  | zero => simp [monoG, GPoly.toPoly_cons, GPoly.toPoly_nil, M.sem_one]
  | succ k ih =>
    have e : monoG Fc ks m (k + 1) = (MO Fc ks m).zero :: monoG Fc ks m k := by
      simp [monoG, List.replicate_succ]
    rw [e, GPoly.toPoly_cons, ih, M.sem_zero, map_zero, zero_add, pow_succ, mul_comm]

lemma sum_range_toPoly_ext (a : GPoly (LC m)) (g : ℕ → F[X]) :
    ∑ l ∈ Finset.range a.length, Polynomial.C (M.sem (a.getD l (MO Fc ks m).zero)) * g l =
      ∑ l ∈ Finset.range ((GPoly.toPoly M a).natDegree + 1),
        Polynomial.C ((GPoly.toPoly M a).coeff l) * g l := by
  have hd := natDegree_toPoly_le M a
  rcases Nat.eq_zero_or_pos a.length with h0 | hpos
  · have ha : a = [] := List.length_eq_zero_iff.mp h0
    subst ha
    simp [GPoly.toPoly_nil]
  · symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) (fun l hl hnl ↦ ?_) |>.trans
      (Finset.sum_congr rfl fun l _ ↦ by rw [coeff_toPoly_sem])
    rw [coeff_eq_zero_of_natDegree_lt (by simpa using hnl), map_zero, zero_mul]

lemma toPoly_segCoefC (e : ℕ) (s K0 : ℤ) (i : ℕ) (a : GPoly (LC m)) :
    GPoly.toPoly M (segCoefC Fc ks m e s K0 i a) = segCoef e s K0 i (GPoly.toPoly M a) := by
  have h1 : segCoefC Fc ks m e s K0 i a = ((List.range a.length).map fun l ↦
      GPoly.mul (MO Fc ks m) [a.getD l (MO Fc ks m).zero]
        (monoG Fc ks m (K0 - i * s - e * l).toNat)).foldr (GPoly.add (MO Fc ks m)) [] := by
    rw [segCoefC, List.foldr_map]
  rw [h1, toPoly_foldr_addG, List.map_map, ← List.sum_toFinset _ List.nodup_range,
    List.toFinset_range, segCoef, ← sum_range_toPoly_ext M a]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [Function.comp_apply, GPoly.toPoly_mul, toPoly_monoG', GPoly.toPoly_cons,
    GPoly.toPoly_nil, mul_zero, add_zero]

lemma sem_segResC (e : ℕ) (s : ℤ) (n : ℕ) (fp : List (GPoly (LC m))) (Θ : GPoly (LC m)) :
    M.sem (segResC Fc ks m e s n fp Θ) = ∑ j ∈ Finset.range n,
      ∑ l ∈ Finset.range (fp.getD j []).length, M.sem ((fp.getD j []).getD l (MO Fc ks m).zero) *
        (if 0 ≤ (e : ℤ) + e * l + s * j then
          ((GPoly.toPoly M Θ) ^ j).coeff ((e : ℤ) + e * l + s * j).toNat else 0) := by
  unfold segResC
  rw [sem_lsumC, List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Function.comp_apply]
  rw [sem_lsumC, List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [Function.comp_apply]
  rw [M.sem_mul]
  congr 1
  split_ifs
  · rw [← coeff_toPoly_sem, toPoly_powGXP]
  · exact M.sem_zero

end Sem

universe u

section Tower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma segPoly_nkF (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m))) (e : ℕ) (s K0 : ℤ) (i : ℕ) :
    (segPoly e s K0 (T.nkF m h Pp)).coeff i =
      if i ≤ Pp.length then GPoly.toPoly (T.MP m h) ((segPolyC Fc ks m e s K0 Pp).getD i [])
      else 0 := by
  have hn : (T.nkF m h Pp).natDegree = Pp.length := polyF_natDegree _ _
  rw [coeff_segPoly, hn]
  split_ifs with hi
  · rw [T.nkF_coeff_coefC m h Pp i hi, segPolyC, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    rw [toPoly_segCoefC]
  · rfl

lemma eval_segPoly_nkF (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m))) (e : ℕ) (s K0 : ℤ)
    (Θ : GPoly (LC m)) :
    (segPoly e s K0 (T.nkF m h Pp)).eval (GPoly.toPoly (T.MP m h) Θ) =
      GPoly.toPoly (T.MP m h) (segEvalC Fc ks m e s K0 Pp Θ) := by
  have hn : (T.nkF m h Pp).natDegree = Pp.length := polyF_natDegree _ _
  have hlt : (segPoly e s K0 (T.nkF m h Pp)).natDegree < Pp.length + 1 := by
    have := natDegree_segPoly_le e s K0 (T.nkF m h Pp); omega
  rw [eval_eq_sum_range' hlt, segEvalC, toPoly_evalPolyC]
  have hlen : (segPolyC Fc ks m e s K0 Pp).length = Pp.length + 1 := by simp [segPolyC]
  rw [hlen]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [T.segPoly_nkF m h Pp e s K0 i, if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

lemma deriv_segPoly_nkF (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m))) (e : ℕ) (s K0 : ℤ)
    (Θ : GPoly (LC m)) :
    ((derivative (segPoly e s K0 (T.nkF m h Pp))).eval (GPoly.toPoly (T.MP m h) Θ)).coeff 0 =
      (T.MP m h).sem (evalLC Fc ks m (GPoly.derivX (MO Fc ks m)
        (segResidC Fc ks m e s K0 Pp)) (Θ.getD 0 (MO Fc ks m).zero)) := by
  set φ : (T.F m)[X] →+* T.F m := Polynomial.constantCoeff with hφ
  have h1 : ∀ (p : (T.F m)[X][X]) (q : (T.F m)[X]), (p.eval q).coeff 0 = (p.map φ).eval (φ q) :=
    fun p q ↦ by rw [eval_map, eval₂_hom]; rfl
  rw [h1, ← Polynomial.derivative_map, sem_evalLC, GPoly.toPoly_derivX]
  have hφq : φ (GPoly.toPoly (T.MP m h) Θ) = (T.MP m h).sem (Θ.getD 0 (MO Fc ks m).zero) := by
    rw [hφ, Polynomial.constantCoeff_apply, coeff_toPoly_sem]
  rw [hφq]
  congr 2
  ext i
  rw [Polynomial.coeff_map, T.segPoly_nkF m h Pp e s K0 i, coeff_toPoly_sem]
  split_ifs with hi
  · rw [hφ, Polynomial.constantCoeff_apply, coeff_toPoly_sem, segResidC]
    have hg := List.getD_map (fun p : GPoly (LC m) ↦ p.getD 0 (MO Fc ks m).zero)
      (l := segPolyC Fc ks m e s K0 Pp) (n := i) (d := [])
    simp only [List.getD_nil] at hg
    rw [hg]
  · rw [map_zero, segResidC, List.getD_eq_default _ _ (by simp [segPolyC]; omega), (T.MP m h).sem_zero]


set_option maxHeartbeats 1000000 in
/-- **A passing multi-segment certificate gives zero residues at infinity.** -/
theorem zero_res_multiC (m : ℕ) (h : T.Tr m) {L' : Type*} [Field L'] [CharZero L']
    [Algebra (T.F m) L'] [Differential L'] [DifferentialAlgebra (T.F m) L']
    (S : CurveData (T.F m) L') (Pp : List (GPoly (LC m))) (hSF : S.F = T.nkF m h Pp)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (βs : List (List (LC m))) (Θs : List (List (GPoly (LC m)))) (M : ℕ) (fp : List (GPoly (LC m)))
    (hck : multiResCk Fc ks lv m Pp segs βs Θs M fp = true)
    {Cs : Type*} [Field Cs] [CharZero Cs] (ι : Cs →+* T.F m)
    (hrde : RdeSpecK ι (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩))
      (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩))
    {Kb : Type*} [Field Kb] [CharZero Kb] [Algebra (T.F m) Kb] [Differential Kb] [IsAlgClosed Kb]
    (hK : ∀ c : T.F m, (algebraMap (T.F m) Kb c)′ = algebraMap (T.F m) Kb c′) :
    ∃ (N : ℕ) (hN : 0 < N) (li : List (LaurentSeries Kb)) (hli : S.F.map (infSub (K := Kb) N) =
      (li.map fun r ↦ X - Polynomial.C r).prod),
      ∀ r (hr : r ∈ li), ∃ b : Kb, (S.embG (infSub N) (infSub_injective N hN) r
        (S.root_of_mem hli hr) (S.evT (∑ j ∈ Finset.range Pp.length,
          Polynomial.C (GPoly.toPoly (T.MP m h) (fp.getD j [])) * X ^ j))).coeff (N : ℤ) = b′ := by
  classical
  obtain ⟨q, hq, hn0, hePos, hgcd, hdecS, hcne, hΓ, hbd, hres, htop, hchain, hlast⟩ :=
    T.multiShapeR_spec m h Pp segs hms
  simp only [multiResCk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at hck
  set sg : Fin (q + 1) → SegRC m := fun k ↦ segs.getD k (segRD Fc ks m) with hsg
  set n := Pp.length with hn
  set Q : (T.F m)[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly (T.MP m h) (fp.getD j [])) * X ^ j with hQ
  have hQc : ∀ j, Q.coeff j = if j < n then GPoly.toPoly (T.MP m h) (fp.getD j []) else 0 := by
    intro j
    rw [hQ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hQd : Q.natDegree < n := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := n - 1) fun j hj ↦ ?_)
      (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]; have := Finset.mem_range.mp hj; omega
  have hk : ∀ k : Fin (q + 1), (k : ℕ) < segs.length := fun k ↦ by rw [hq]; exact k.2
  -- the data per place
  set Γ : Fin (q + 1) → List (T.F m) := fun k ↦ (sg k).2.2.2.2.map (T.MP m h).sem with hΓdef
  have hΓlen : ∀ k, (Γ k).length = (sg k).2.2.2.2.length := fun k ↦ List.length_map _
  set β : ∀ k, Fin (Γ k).length → T.F m := fun k i ↦ (T.MP m h).sem ((βs.getD k []).getD i (MO Fc ks m).zero) with hβ
  set Θt : ∀ k, Fin (Γ k).length → (T.F m)[X] := fun k i ↦
    GPoly.toPoly (T.MP m h) ((Θs.getD k []).getD i []) with hΘt
  have hplace : ∀ k (i : Fin (Γ k).length), _ := fun k i ↦
    (hck k (hk k)).1.2 i (by rw [← hΓlen]; exact i.2)
  have hβe : ∀ k (i : Fin (Γ k).length), β k i ^ (sg k).1 = (Γ k)[(i : ℕ)] := by
    intro k i
    have A := (hplace k i).1.1.1.1
    rw [(T.MP m h).isZero_iff, (T.MP m h).sem_add, (T.MP m h).sem_neg, sem_powC, add_neg_eq_zero] at A
    simp only [hβ, hΓdef]
    rw [A, List.getElem_map, List.getD_eq_getElem]
  have hΘ0s : ∀ k (i : Fin (Γ k).length),
      (T.MP m h).sem (((Θs.getD k []).getD i []).getD 0 (MO Fc ks m).zero) = β k i := by
    intro k i
    have B := (hplace k i).1.1.1.2
    rw [(T.MP m h).isZero_iff, (T.MP m h).sem_add, (T.MP m h).sem_neg, add_neg_eq_zero] at B
    exact B
  have hΘ0 : ∀ k (i : Fin (Γ k).length), (Θt k i).coeff 0 = β k i := fun k i ↦ by
    rw [hΘt, coeff_toPoly_sem]; exact hΘ0s k i
  have hu : ∀ k (i : Fin (Γ k).length),
      ((derivative (segPoly (sg k).1 (sg k).2.1 (sg k).2.2.1 S.F)).eval (Θt k i)).coeff 0 ≠ 0 := by
    intro k i
    have D := (hplace k i).1.2
    rw [hSF, hΘt]
    beta_reduce
    rw [T.deriv_segPoly_nkF m h Pp, sem_evalLC, hΘ0s k i, hβ]
    rw [← sem_evalLC]
    intro h0
    rw [← (T.MP m h).isZero_iff] at h0
    rw [h0] at D
    exact absurd D (by simp)
  have hM : ∀ k (i : Fin (Γ k).length), ∀ n' < M,
      ((segPoly (sg k).1 (sg k).2.1 (sg k).2.2.1 S.F).eval (Θt k i)).coeff n' = 0 := by
    intro k i n' hn'
    have C := (hplace k i).1.1.2
    rw [hSF, hΘt]
    beta_reduce
    rw [T.eval_segPoly_nkF m h Pp, coeff_toPoly_sem]
    exact ((T.MP m h).isZero_iff _).mp (List.all_eq_true.mp C n' (List.mem_range.mpr hn'))
  have hMb : ∀ k, ∀ j ≤ Q.natDegree, ∀ l ≤ (Q.coeff j).natDegree,
      ((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j < M := by
    intro k j hj l hl
    have hjn : j < n := lt_of_le_of_lt hj hQd
    rw [hQc, if_pos hjn] at hl
    have h1 := natDegree_toPoly_le (T.MP m h) (fp.getD j [])
    exact (hck k (hk k)).2 j hjn l (by omega)
  have hz : ∀ k (i : Fin (Γ k).length), ∃ z : T.F m,
      z′ = (T.MP m h).sem (segResC Fc ks m (sg k).1 (sg k).2.1 n fp ((Θs.getD k []).getD i [])) :=
    fun k i ↦ derivTestC_sound ι (T.MP m h) hrde _ (hplace k i).2
  choose z hz using hz
  have hz' : ∀ k (i : Fin (Γ k).length), (z k i)′ = ∑ j ∈ Finset.range (Q.natDegree + 1),
      ∑ l ∈ Finset.range ((Q.coeff j).natDegree + 1), (Q.coeff j).coeff l *
        (if 0 ≤ ((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j then
          ((Θt k i) ^ j).coeff (((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j).toNat else 0) := by
    intro k i
    rw [hz k i, sem_segResC]
    have hstep : ∀ j ∈ Finset.range n,
        ∑ l ∈ Finset.range (fp.getD j []).length, (T.MP m h).sem ((fp.getD j []).getD l (MO Fc ks m).zero) *
          (if 0 ≤ ((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j then
            ((Θt k i) ^ j).coeff (((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j).toNat else 0) =
        ∑ l ∈ Finset.range ((Q.coeff j).natDegree + 1), (Q.coeff j).coeff l *
          (if 0 ≤ ((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j then
            ((Θt k i) ^ j).coeff (((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j).toNat else 0) := by
      intro j hj
      rw [hQc, if_pos (Finset.mem_range.mp hj)]
      exact sum_toPoly_coeff (T.MP m h) _ _
    rw [Finset.sum_congr rfl hstep]
    symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr (show Q.natDegree + 1 ≤ n by omega))
      fun j _ hnj ↦ ?_
    rw [coeff_eq_zero_of_natDegree_lt (by simpa using hnj)]
    simp
  have hbd' : ∀ k : Fin (q + 1), ∀ i ≤ S.F.natDegree, S.F.coeff i ≠ 0 →
      ((sg k).1 : ℤ) * (S.F.coeff i).natDegree + i * (sg k).2.1 ≤ (sg k).2.2.1 := by
    rw [hSF]; exact hbd
  have hres' : ∀ k : Fin (q + 1), ∑ i ∈ Finset.range (S.F.natDegree + 1),
      Polynomial.C (coeffZe (S.F.coeff i) (sg k).1 ((sg k).2.2.1 - i * (sg k).2.1)) * X ^ i =
        Polynomial.C ((T.MP m h).sem (sg k).2.2.2.1) * X ^ (loRC segs k) *
          ((Γ k).map fun γ ↦ X ^ (sg k).1 - Polynomial.C γ).prod := by
    rw [hSF]; exact hres
  have htop' : loRC segs ((0 : Fin (q + 1)) : ℕ) + (sg 0).1 * (Γ 0).length = S.F.natDegree := by
    rw [hSF]; exact htop
  obtain ⟨N, hN, li, hli, hzr⟩ := S.zero_res_multi (Kb := Kb) (fun k ↦ (sg k).1) hePos
    (fun k ↦ (sg k).2.1) hgcd hdecS (fun k ↦ (sg k).2.2.1) (fun k ↦ (T.MP m h).sem (sg k).2.2.2.1) hcne
    (fun k ↦ loRC segs k) Γ hΓ hbd' hres' htop' hchain hlast β hβe Θt hΘ0 hu M hM Q hMb z hz' hK
  exact ⟨N, hN, li, hli, hzr⟩

end MTower

end Tower

end Curves.MT
