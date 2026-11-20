import RischTragerBronstein.Mixed.NKResSplit
import RischTragerBronstein.Mixed.NKInfRVG

/-!
# Code-level zero-residue certificates at split places at infinity

`splitResCk`: for `θⁿ + ∑ aᵢ(t) θⁱ = 0` with `deg aᵢ ≤ (n − i) s`, the residual roots `γₖ`
(simple, distinct), truncations `Θ̃ₖ` of the inverted roots (`Θ̃ₖ(0) = γₖ`,
`Q(T, Θ̃ₖ) ≡ 0 mod Tᴹ`), and for each place the residue value
`cₖ = ∑ⱼ ∑ᵢ fⱼᵢ [T^{1+i+sj}] Θ̃ₖʲ` passing the derivative test (`derivTestC`: the parametric
Risch equation `y′ = cₖ` is solvable).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Tower.PrimN GTors Differential

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The code of `reflect N p`. -/
def revPadC (m N : ℕ) (p : GPoly (LC m)) : GPoly (LC m) :=
  (List.range (N + 1)).map fun k ↦ p.getD (N - k) (MO Fc ks m).zero

/-- The coefficients of the inverted polynomial `Q(T, Θ) = T^{ns} P(1/T, Θ/Tˢ)`. -/
def invCoeffsC (m s : ℕ) (Pp : List (GPoly (LC m))) : List (GPoly (LC m)) :=
  ((List.range Pp.length).map fun i ↦ revPadC Fc ks m ((Pp.length - i) * s) (Pp.getD i [])) ++
    [[(MO Fc ks m).one]]

/-- `∑ᵢ Qᵢ Θⁱ`. -/
def evalPolyC (m : ℕ) (Qc : List (GPoly (LC m))) (Θ : GPoly (LC m)) : GPoly (LC m) :=
  ((List.range Qc.length).map fun i ↦
    GPoly.mul (MO Fc ks m) (Qc.getD i []) (powG (MO Fc ks m) Θ i)).foldr (GPoly.add (MO Fc ks m)) []

/-- The first `M` coefficients vanish. -/
def truncOKC (m M : ℕ) (p : GPoly (LC m)) : Bool :=
  (List.range M).all fun k ↦ (MO Fc ks m).isZero (p.getD k (MO Fc ks m).zero)

/-- The residual polynomial `∑ᵢ aᵢ[(n − i) s] Zⁱ + Zⁿ`. -/
def residualC (m s : ℕ) (Pp : List (GPoly (LC m))) : GPoly (LC m) :=
  ((List.range Pp.length).map fun i ↦
    (Pp.getD i []).getD ((Pp.length - i) * s) (MO Fc ks m).zero) ++ [(MO Fc ks m).one]

/-- The value of a polynomial code at a code (Horner). -/
def evalLC (m : ℕ) (R : GPoly (LC m)) (γ : LC m) : LC m :=
  R.foldr (fun a acc ↦ (MO Fc ks m).add a ((MO Fc ks m).mul γ acc)) (MO Fc ks m).zero

/-- The residue value `∑ⱼ ∑ᵢ fⱼᵢ [T^{1+i+sj}] Θ̃ʲ` (`j < n`). -/
def resInfC (m s n : ℕ) (fp : List (GPoly (LC m))) (Θ : GPoly (LC m)) : LC m :=
  lsumC (MO Fc ks m) ((List.range n).map fun j ↦
    lsumC (MO Fc ks m) ((List.range (fp.getD j []).length).map fun i ↦
      (MO Fc ks m).mul ((fp.getD j []).getD i (MO Fc ks m).zero)
        ((powG (MO Fc ks m) Θ j).getD (1 + i + s * j) (MO Fc ks m).zero)))

/-- **The derivative test**: `y′ = c` is solvable in `Fₘ`. -/
def derivTestC (m : ℕ) (c : LC m) : Bool :=
  (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩ [c]).any fun r ↦ r.1.getD 0 0 != 0

/-- **The zero-residue certificate at split places at infinity.** -/
def splitResCk (m s M : ℕ) (Pp : List (GPoly (LC m))) (γs : List (LC m))
    (Θs : List (GPoly (LC m))) (fp : List (GPoly (LC m))) : Bool :=
  let O := MO Fc ks m
  let n := Pp.length
  let R := residualC Fc ks m s Pp
  decide (γs.length = n) &&
  (List.range n).all (fun i ↦ decide ((Pp.getD i []).length ≤ (n - i) * s + 1)) &&
  (List.range n).all (fun k ↦ O.isZero (evalLC Fc ks m R (γs.getD k O.zero)) &&
    !O.isZero (evalLC Fc ks m (GPoly.derivX O R) (γs.getD k O.zero))) &&
  (List.range n).all (fun k ↦ (List.range n).all fun l ↦
    decide (k = l) || !O.isZero (O.add (γs.getD k O.zero) (O.neg (γs.getD l O.zero)))) &&
  (List.range n).all (fun k ↦
    O.isZero (O.add ((Θs.getD k []).getD 0 O.zero) (O.neg (γs.getD k O.zero))) &&
    truncOKC Fc ks m M (evalPolyC Fc ks m (invCoeffsC Fc ks m s Pp) (Θs.getD k []))) &&
  (List.range n).all (fun j ↦ decide (max 1 (fp.getD j []).length + s * j < M)) &&
  (List.range n).all (fun k ↦ derivTestC Fc ks lv m (resInfC Fc ks m s n fp (Θs.getD k [])))

end Codes

section Sem

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {m : ℕ} {F : Type*} [Field F] [Differential F] (M : CField (LC m) F (MO Fc ks m))

lemma toPoly_revPadC (N : ℕ) (p : GPoly (LC m)) (hp : (GPoly.toPoly M p).natDegree ≤ N) :
    GPoly.toPoly M (revPadC Fc ks m N p) = reflect N (GPoly.toPoly M p) := by
  ext k
  rw [coeff_toPoly_sem, coeff_reflect]
  by_cases hk : k ≤ N
  · rw [revAt_le hk, coeff_toPoly_sem]
    congr 1
    rw [revPadC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · rw [revAt_eq_self_of_lt (by omega), revPadC, List.getD_eq_default _ _ (by simp; omega),
      M.sem_zero, coeff_eq_zero_of_natDegree_lt (by omega)]

lemma sem_evalLC (R : GPoly (LC m)) (γ : LC m) :
    M.sem (evalLC Fc ks m R γ) = (GPoly.toPoly M R).eval (M.sem γ) := by
  induction R with
  | nil => simp [evalLC, GPoly.toPoly_nil, M.sem_zero]
  | cons a R ih =>
    simp only [evalLC, List.foldr_cons] at ih ⊢
    rw [M.sem_add, M.sem_mul, ih, GPoly.toPoly_cons, eval_add, eval_mul, eval_C, eval_X]

lemma toPoly_foldr_addG (l : List (GPoly (LC m))) :
    GPoly.toPoly M (l.foldr (GPoly.add (MO Fc ks m)) []) = (l.map (GPoly.toPoly M)).sum := by
  induction l with
  | nil => simp [GPoly.toPoly_nil]
  | cons a l ih => rw [List.foldr_cons, GPoly.toPoly_add, ih, List.map_cons, List.sum_cons]

lemma toPoly_evalPolyC (Qc : List (GPoly (LC m))) (Θ : GPoly (LC m)) :
    GPoly.toPoly M (evalPolyC Fc ks m Qc Θ) =
      ∑ i ∈ Finset.range Qc.length, GPoly.toPoly M (Qc.getD i []) * GPoly.toPoly M Θ ^ i := by
  rw [evalPolyC, toPoly_foldr_addG, List.map_map, ← List.sum_toFinset _ List.nodup_range,
    List.toFinset_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Function.comp_apply]
  rw [GPoly.toPoly_mul, toPoly_powGXP]

lemma sem_resInfC (s n : ℕ) (fp : List (GPoly (LC m))) (Θ : GPoly (LC m)) :
    M.sem (resInfC Fc ks m s n fp Θ) = ∑ j ∈ Finset.range n,
      ∑ i ∈ Finset.range (fp.getD j []).length, M.sem ((fp.getD j []).getD i (MO Fc ks m).zero) *
        ((GPoly.toPoly M Θ) ^ j).coeff (1 + i + s * j) := by
  unfold resInfC
  rw [sem_lsumC, List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Function.comp_apply]
  rw [sem_lsumC, List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Function.comp_apply]
  rw [M.sem_mul]
  congr 1
  rw [← coeff_toPoly_sem, toPoly_powGXP]

end Sem

section Deriv

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m} {m : ℕ}
variable {Cs F : Type*} [Field Cs] [CharZero Cs] [Field F] [Differential F] [CharZero F] (ι : Cs →+* F)
  (M : CField (LC m) F (MO Fc ks m))

/-- **Soundness of the derivative test.** -/
lemma derivTestC_sound
    (hrde : RdeSpecK ι M (M.sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩))
      (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩))
    (c : LC m) (h : derivTestC Fc ks lv m c = true) : ∃ z : F, z′ = M.sem c := by
  obtain ⟨r, hr, hq⟩ := List.any_eq_true.mp h
  have hq' : r.1.getD 0 0 ≠ 0 := by simpa using hq
  have hs := hrde.sound [c] r hr
  have hf0 : M.sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩) = 0 := by
    rw [sem_fCode]
    simp [logSumV, M.sem_one]
  rw [hf0, zero_mul, add_zero, sQ] at hs
  simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero] at hs
  refine ⟨M.sem r.2 / (r.1.getD 0 0 : F), ?_⟩
  have hq0 : ((r.1.getD 0 0 : ℚ) : F) ≠ 0 := by exact_mod_cast hq'
  have hcst : ((r.1.getD 0 0 : ℚ) : F)′ = 0 := Differential.deriv_ratCast_K _
  rw [Derivation.leibniz_div, hcst, smul_zero, sub_zero, hs, smul_eq_mul]
  field_simp
  ring

end Deriv

section GetD

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {m : ℕ}

lemma getD_invCoeffsC_lt (s : ℕ) (Pp : List (GPoly (LC m))) {i : ℕ} (hi : i < Pp.length) :
    (invCoeffsC Fc ks m s Pp).getD i [] = revPadC Fc ks m ((Pp.length - i) * s) (Pp.getD i []) := by
  rw [invCoeffsC, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi)]
  simp [hi]

lemma getD_invCoeffsC_self (s : ℕ) (Pp : List (GPoly (LC m))) :
    (invCoeffsC Fc ks m s Pp).getD Pp.length [] = [(MO Fc ks m).one] := by
  simp [invCoeffsC, List.getD_eq_getElem?_getD]

lemma getD_invCoeffsC_gt (s : ℕ) (Pp : List (GPoly (LC m))) {i : ℕ} (hi : Pp.length < i) :
    (invCoeffsC Fc ks m s Pp).getD i [] = [] := by
  rw [List.getD_eq_default _ _ (by simp [invCoeffsC]; omega)]

lemma getD_revPadC_zero (N : ℕ) (p : GPoly (LC m)) :
    (revPadC Fc ks m N p).getD 0 (MO Fc ks m).zero = p.getD N (MO Fc ks m).zero := by
  simp [revPadC, List.getD_eq_getElem?_getD]

lemma getD_residualC_lt (s : ℕ) (Pp : List (GPoly (LC m))) {i : ℕ} (hi : i < Pp.length) :
    (residualC Fc ks m s Pp).getD i (MO Fc ks m).zero =
      (Pp.getD i []).getD ((Pp.length - i) * s) (MO Fc ks m).zero := by
  rw [residualC, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi)]
  simp [hi]

lemma getD_residualC_self (s : ℕ) (Pp : List (GPoly (LC m))) :
    (residualC Fc ks m s Pp).getD Pp.length (MO Fc ks m).zero = (MO Fc ks m).one := by
  simp [residualC, List.getD_eq_getElem?_getD]

lemma getD_residualC_gt (s : ℕ) (Pp : List (GPoly (LC m))) {i : ℕ} (hi : Pp.length < i) :
    (residualC Fc ks m s Pp).getD i (MO Fc ks m).zero = (MO Fc ks m).zero := by
  rw [List.getD_eq_default _ _ (by simp [residualC]; omega)]

end GetD

section Bridge

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {m : ℕ}
variable {F : Type*} [Field F] [Differential F] [CharZero F] (M : CField (LC m) F (MO Fc ks m))

/-- The polynomial coefficients `aᵢ` of the curve. -/
noncomputable def aPoly (Pp : List (GPoly (LC m))) (i : ℕ) : F[X] := GPoly.toPoly M (Pp.getD i [])

lemma natDegree_aPoly_le (Pp : List (GPoly (LC m))) (s : ℕ) (i : ℕ)
    (h : (Pp.getD i []).length ≤ (Pp.length - i) * s + 1) :
    (aPoly M Pp i).natDegree ≤ (Pp.length - i) * s :=
  (natDegree_toPoly_le M _).trans (by omega)

lemma coeff_invPS_polyF (Pp : List (GPoly (LC m))) (s : ℕ)
    (hlen : ∀ i < Pp.length, (Pp.getD i []).length ≤ (Pp.length - i) * s + 1) (i : ℕ) :
    (invPS Pp.length s (polyF (aPoly M Pp) Pp.length)).coeff i =
      GPoly.toPoly M ((invCoeffsC Fc ks m s Pp).getD i []) := by
  rw [coeff_invPS]
  rcases lt_trichotomy i Pp.length with hi | rfl | hi
  · rw [if_pos hi.le, polyF_coeff _ _ _ hi, invCoeffsC, List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
      toPoly_revPadC M _ _ (natDegree_aPoly_le M Pp s i (hlen i hi))]
    rfl
  · rw [if_pos le_rfl, Nat.sub_self, zero_mul]
    have hc : (polyF (aPoly M Pp) Pp.length).coeff Pp.length = 1 := by
      have := polyF_monic (aPoly M Pp) Pp.length
      rw [Monic, Polynomial.leadingCoeff, polyF_natDegree] at this
      exact this
    rw [hc, ← map_one Polynomial.C, reflect_C, pow_zero, mul_one, invCoeffsC,
      List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range, Nat.sub_self]
    simp [GPoly.toPoly_cons, GPoly.toPoly_nil, M.sem_one]
  · rw [if_neg (by omega), invCoeffsC, List.getD_eq_default _ _ (by simp; omega)]
    simp [GPoly.toPoly_nil]

end Bridge

section Bridge2

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {m : ℕ}
variable {F K : Type*} [Field F] [Differential F] [CharZero F] [Field K] [Algebra F K]
  (M : CField (LC m) F (MO Fc ks m))

lemma psSub_one_zero (q : F[X]) :
    psSub (C := F) 1 (0 : K) q = ((q.map (algebraMap F K) : K[X]) : PowerSeries K) := by
  rw [psSub]
  simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, coe_mapRingHom,
    coe_compRingHom, map_zero, zero_add, pow_one, comp_X]

lemma fibrePS_eval_coe (G : F[X][X]) (P : F[X]) :
    (fibrePS (K := K) G 0).eval ((P.map (algebraMap F K) : K[X]) : PowerSeries K) =
      (((G.eval P).map (algebraMap F K) : K[X]) : PowerSeries K) := by
  set ψ : F[X] →+* PowerSeries K :=
    (Polynomial.coeToPowerSeries.ringHom (R := K)).comp (mapRingHom (algebraMap F K)) with hψ
  have hps : psSub (C := F) 1 (0 : K) = ψ := RingHom.ext fun q ↦ by
    rw [psSub_one_zero, hψ]; rfl
  have h1 : ((P.map (algebraMap F K) : K[X]) : PowerSeries K) = ψ P := rfl
  have h2 : (((G.eval P).map (algebraMap F K) : K[X]) : PowerSeries K) = ψ (G.eval P) := rfl
  rw [h1, h2, fibrePS, hps, eval_map, Polynomial.eval₂_hom]

lemma dvd_of_truncOKC (Mn : ℕ) (p : GPoly (LC m)) (h : truncOKC Fc ks m Mn p = true) :
    (PowerSeries.X : PowerSeries K) ^ Mn ∣
      (((GPoly.toPoly M p).map (algebraMap F K) : K[X]) : PowerSeries K) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [Polynomial.coeff_coe, Polynomial.coeff_map, coeff_toPoly_sem,
    (M.isZero_iff _).mp (List.all_eq_true.mp h k (List.mem_range.mpr hk)), map_zero]

lemma fibreAt_invPS_polyF (Pp : List (GPoly (LC m))) (s : ℕ)
    (hlen : ∀ i < Pp.length, (Pp.getD i []).length ≤ (Pp.length - i) * s + 1) :
    fibreAt (K := K) (invPS Pp.length s (polyF (aPoly M Pp) Pp.length)) 0 =
      (GPoly.toPoly M (residualC Fc ks m s Pp)).map (algebraMap F K) := by
  ext i
  rw [fibreAt, Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map, coe_evalRingHom,
    ← coeff_zero_eq_eval_zero, coe_mapRingHom, Polynomial.coeff_map, coeff_invPS_polyF M Pp s hlen,
    coeff_toPoly_sem, coeff_toPoly_sem]
  congr 2
  rcases lt_trichotomy i Pp.length with hi | rfl | hi
  · rw [getD_invCoeffsC_lt s Pp hi, getD_revPadC_zero, getD_residualC_lt s Pp hi]
  · rw [getD_invCoeffsC_self, getD_residualC_self]; rfl
  · rw [getD_invCoeffsC_gt s Pp hi, getD_residualC_gt s Pp hi]; rfl

lemma fibreAt_derivative (G : F[X][X]) (a : K) :
    fibreAt (K := K) (derivative G) a = derivative (fibreAt (K := K) G a) := by
  rw [fibreAt, fibreAt, Polynomial.derivative_map, Polynomial.derivative_map]

lemma eval_invPS_polyF (Pp : List (GPoly (LC m))) (s : ℕ)
    (hlen : ∀ i < Pp.length, (Pp.getD i []).length ≤ (Pp.length - i) * s + 1) (Θ : GPoly (LC m)) :
    (invPS Pp.length s (polyF (aPoly M Pp) Pp.length)).eval (GPoly.toPoly M Θ) =
      GPoly.toPoly M (evalPolyC Fc ks m (invCoeffsC Fc ks m s Pp) Θ) := by
  have hmon := invPS_monic (polyF (aPoly M Pp) Pp.length) Pp.length s (polyF_monic _ _)
    (polyF_natDegree _ _)
  rw [eval_eq_sum_range, hmon.2, toPoly_evalPolyC]
  have hlenQ : (invCoeffsC Fc ks m s Pp).length = Pp.length + 1 := by simp [invCoeffsC]
  rw [hlenQ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_invPS_polyF M Pp s hlen]

end Bridge2

lemma sum_coeff_range_ext {F : Type*} [Field F] (p : F[X]) (g : ℕ → F) (N : ℕ)
    (hN : p.natDegree + 1 ≤ N) :
    ∑ i ∈ Finset.range N, p.coeff i * g i = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * g i := by
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hN) fun i hi hni ↦ ?_
  rw [coeff_eq_zero_of_natDegree_lt (by simpa using hni), zero_mul]

lemma sum_toPoly_coeff {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {m : ℕ} {F : Type*} [Field F]
    [Differential F] (M : CField (LC m) F (MO Fc ks m)) (p : GPoly (LC m)) (g : ℕ → F) :
    ∑ i ∈ Finset.range p.length, M.sem (p.getD i (MO Fc ks m).zero) * g i =
      ∑ i ∈ Finset.range ((GPoly.toPoly M p).natDegree + 1), (GPoly.toPoly M p).coeff i * g i := by
  rcases Nat.eq_zero_or_pos p.length with h0 | hpos
  · have hp : p = [] := List.length_eq_zero_iff.mp h0
    subst hp
    simp [GPoly.toPoly_nil]
  · rw [← sum_coeff_range_ext _ _ p.length (by have := natDegree_toPoly_le M p; omega)]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [coeff_toPoly_sem]

section Main

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m} {m : ℕ}
variable {F L' K : Type*} [Field F] [Differential F] [CharZero F]
  [Field L'] [CharZero L'] [Algebra F L'] [Differential L'] [DifferentialAlgebra F L']
  [Field K] [CharZero K] [Algebra F K] [Differential K] [IsAlgClosed K]

/-- **A passing zero-residue certificate gives zero residues** of `f = ∑ⱼ fⱼ θʲ` along the split
branch system above infinity. -/
theorem zero_res_codes (S : CurveData F L') (M : CField (LC m) F (MO Fc ks m))
    {Cs : Type*} [Field Cs] [CharZero Cs] (ι : Cs →+* F)
    (hrde : RdeSpecK ι M (M.sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩))
      (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩))
    (hK : ∀ c : F, (algebraMap F K c)′ = algebraMap F K c′)
    (Pp : List (GPoly (LC m))) (hSF : S.F = polyF (aPoly M Pp) Pp.length)
    (s Mn : ℕ) (γs : List (LC m)) (Θs fp : List (GPoly (LC m)))
    (hck : splitResCk Fc ks lv m s Mn Pp γs Θs fp = true) (hn0 : 0 < Pp.length) :
    ∃ li : List (LaurentSeries K), ∃ hli : S.F.map (infSub (K := K) 1) =
      (li.map fun r ↦ X - Polynomial.C r).prod,
      ∀ r (hr : r ∈ li), ∃ β : K, (S.embG (infSub 1) (infSub_injective 1 one_pos) r
        (S.root_of_mem hli hr) (S.evT (∑ j ∈ Finset.range Pp.length,
          Polynomial.C (GPoly.toPoly M (fp.getD j [])) * X ^ j))).coeff 1 = β′ := by
  classical
  simp only [splitResCk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at hck
  obtain ⟨⟨⟨⟨⟨⟨hγlen, hlen⟩, hroots⟩, hdist⟩, hΘ⟩, hMb⟩, hder⟩ := hck
  have hlen' : ∀ i < Pp.length, (Pp.getD i []).length ≤ (Pp.length - i) * s + 1 := hlen
  set γ : Fin Pp.length → F := fun k ↦ M.sem (γs.getD k (MO Fc ks m).zero) with hγ
  set Θt : Fin Pp.length → F[X] := fun k ↦ GPoly.toPoly M (Θs.getD k []) with hΘt
  set Q : F[X][X] := ∑ j ∈ Finset.range Pp.length, Polynomial.C (GPoly.toPoly M (fp.getD j [])) * X ^ j
    with hQ
  have hSn : S.F.natDegree = Pp.length := by rw [hSF, polyF_natDegree]
  have hdeg : ∀ i ≤ Pp.length, (S.F.coeff i).natDegree ≤ (Pp.length - i) * s := by
    intro i hi
    rw [hSF]
    rcases lt_or_eq_of_le hi with hi | rfl
    · rw [polyF_coeff _ _ _ hi]; exact natDegree_aPoly_le M Pp s i (hlen' i hi)
    · have := polyF_monic (aPoly M Pp) Pp.length
      rw [Monic, Polynomial.leadingCoeff, polyF_natDegree] at this
      rw [this]; simp
  have hγi : Function.Injective γ := by
    intro k l hkl
    by_contra hne
    have h := (hdist k k.2 l l.2).resolve_left (fun h ↦ hne (Fin.ext h))
    rw [Bool.eq_false_iff] at h
    apply h
    rw [M.isZero_iff, M.sem_add, M.sem_neg]
    simp only [hγ] at hkl
    rw [hkl, add_neg_cancel]
  have hfib := fibreAt_invPS_polyF (K := K) M Pp s hlen'
  have hγroot : ∀ k : Fin Pp.length, (fibreAt (K := K) (invPS Pp.length s S.F) 0).eval (algebraMap F K (γ k)) = 0 := by
    intro k
    rw [hSF, hfib, eval_map, eval₂_hom, hγ, ← sem_evalLC,
      (M.isZero_iff _).mp (hroots k k.2).1, map_zero]
  have hγroot' : ∀ k : Fin Pp.length,
      (fibreAt (K := K) (derivative (invPS Pp.length s S.F)) 0).eval (algebraMap F K (γ k)) ≠ 0 := by
    intro k
    rw [hSF, fibreAt_derivative, hfib, Polynomial.derivative_map,
      eval_map, eval₂_hom, hγ, ← GPoly.toPoly_derivX, ← sem_evalLC]
    intro h0
    have := (map_eq_zero_iff _ (algebraMap F K).injective).mp h0
    have h2 := (hroots k k.2).2
    rw [Bool.eq_false_iff] at h2
    exact h2 ((M.isZero_iff _).mpr this)
  have hΘ0 : ∀ k : Fin Pp.length, (Θt k).coeff 0 = γ k := by
    intro k
    rw [hΘt, coeff_toPoly_sem]
    have := (M.isZero_iff _).mp (hΘ k k.2).1
    rw [M.sem_add, M.sem_neg, add_neg_eq_zero] at this
    exact this
  have hΘM : ∀ k : Fin Pp.length, (PowerSeries.X : PowerSeries K) ^ Mn ∣
      (fibrePS (K := K) (invPS Pp.length s S.F) 0).eval (((Θt k).map (algebraMap F K) : K[X]) : PowerSeries K) := by
    intro k
    rw [fibrePS_eval_coe, hSF, hΘt, eval_invPS_polyF M Pp s hlen']
    exact dvd_of_truncOKC M Mn _ (hΘ k k.2).2
  set Q : F[X][X] := ∑ j ∈ Finset.range Pp.length,
    Polynomial.C (GPoly.toPoly M (fp.getD j [])) * X ^ j with hQ
  have hQc : ∀ j, Q.coeff j = if j < Pp.length then GPoly.toPoly M (fp.getD j []) else 0 := by
    intro j
    rw [hQ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hQd : Q.natDegree < Pp.length := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := Pp.length - 1) fun j hj ↦ ?_)
      (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]; have := Finset.mem_range.mp hj; omega
  have hM : ∀ j ≤ Q.natDegree, 1 + (Q.coeff j).natDegree + s * j < Mn := by
    intro j hj
    have hjn : j < Pp.length := lt_of_le_of_lt hj hQd
    rw [hQc, if_pos hjn]
    have h1 := natDegree_toPoly_le M (fp.getD j [])
    have h2 := hMb j hjn
    omega
  have hz : ∀ k : Fin Pp.length, ∃ z : F, z′ = M.sem (resInfC Fc ks m s Pp.length fp (Θs.getD k [])) :=
    fun k ↦ derivTestC_sound ι M hrde _ (hder k k.2)
  choose z hz using hz
  refine S.zero_res_split Pp.length s Mn hSn hdeg γ hγi hγroot hγroot' Θt hΘ0 hΘM Q hM z
    (fun k ↦ ?_) hK
  rw [hz k, sem_resInfC]
  simp only [hΘt]
  have hstep : ∀ j ∈ Finset.range Pp.length,
      ∑ i ∈ Finset.range (fp.getD j []).length, M.sem ((fp.getD j []).getD i (MO Fc ks m).zero) *
        ((GPoly.toPoly M (Θs.getD k [])) ^ j).coeff (1 + i + s * j) =
      ∑ i ∈ Finset.range ((Q.coeff j).natDegree + 1), (Q.coeff j).coeff i *
        ((GPoly.toPoly M (Θs.getD k [])) ^ j).coeff (1 + i + s * j) := by
    intro j hj
    rw [hQc, if_pos (Finset.mem_range.mp hj)]
    exact sum_toPoly_coeff M _ _
  rw [Finset.sum_congr rfl hstep]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (show Q.natDegree + 1 ≤ Pp.length by omega))
    fun j _ hnj ↦ ?_
  rw [coeff_eq_zero_of_natDegree_lt (by simpa using hnj)]
  simp

end Main

end Curves.MT

