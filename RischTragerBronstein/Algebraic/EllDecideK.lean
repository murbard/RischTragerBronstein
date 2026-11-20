import RischTragerBronstein.Algebraic.EllDecideF

/-!
# Elliptic integrals with simple poles over an arbitrary computable field of constants

`EllDecideF` for any field `K` of characteristic zero with computable arithmetic and a ℚ-basis
`b₁, …, bₙ` with computable coordinate functionals (`QCoords K`), e.g. `ℚ(√d)` or a number field
`ℚ[x]/(f)`. The residues `rᵢ ∈ K` are split along the basis, `rᵢ = ∑ⱼ λⱼ(rᵢ) bⱼ`. For each `j`
the point `Sⱼ = ∑ᵢ (Lⱼ λⱼ(rᵢ)) Pᵢ` is tested for torsion (a non-torsion `Sⱼ` refutes elementarity by
the functional criterion with `Λ = λⱼ`); otherwise each logarithmic part is removed by a
certificate and the polynomial remainder is reduced. `ellDecideK_spec`: every answer is correct;
`ellDecideK_ne_none`: valid data is always decided.
-/

open Polynomial Differential

namespace EllQuad

open CPoly EllDV

/-- A computable `ℚ`-basis with coordinate functionals. -/
class QCoords (K : Type*) [Field K] [CharZero K] where
  /-- the dimension -/
  dim : ℕ
  /-- the coordinates -/
  coord : Fin dim → K →ₗ[ℚ] ℚ
  /-- the basis -/
  bvec : Fin dim → K
  repr : ∀ z : K, z = ∑ i, (coord i z : K) * bvec i

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- The curve over `K`. -/
def pK (a b c : ℤ) : CPoly K := [(c : K), (b : K), (a : K), 1]

/-- Integer multiplicities `L · f(rᵢ)`. -/
def intPtsK (L : ℕ) (f : K → ℚ) (pts : List (K × K × K)) : List (K × K × ℤ) :=
  pts.map fun q ↦ (q.1, q.2.1, (f q.2.2 * L).num)

/-- The order of a point (searching `1, …, N`; `0` if not found). -/
def ordK (a b c : ℤ) (o : Option (K × K)) (N : ℕ) : ℕ :=
  (((List.range N).find? fun k ↦ (mulPtF a b c o (k + 1)).isNone).map (· + 1)).getD 0

/-- `∑ zᵢ Pᵢ` computed in `K`. -/
def sumPtK (a b c : ℤ) : List (K × K × ℤ) → Option (K × K)
  | [] => none
  | q :: t => addPtF a b c
      (mulPtF a b c (some (q.1, ((q.2.2.sign : ℤ) : K) * q.2.1)) q.2.2.natAbs) (sumPtK a b c t)

/-- The certificate for one component. -/
def partCertK (a b c : ℤ) (B : CPoly K) (L : ℕ) (pts : List (K × K × ℤ)) (n : ℕ) :
    Option (CPoly K) :=
  match EllAlgo.ellSolve (pK a b c) (EllAlgo.ptsQ pts n) with
  | some AB =>
    if EllAlgo.certCheck (pK a b c) AB (EllAlgo.fracG B L pts) (1 / ((n : K) * (L : K)))
    then some (EllAlgo.certR (pK a b c) AB (EllAlgo.fracG B L pts) (1 / ((n : K) * (L : K))))
    else none
  | none => none

/-- Validity of the data. -/
def validK (a b c : ℤ) (pts : List (K × K × K)) : Bool :=
  pts.all (fun q ↦ decide (q.2.1 * q.2.1 = q.1 ^ 3 + (a : K) * q.1 ^ 2 + (b : K) * q.1 + (c : K)
    ∧ q.2.1 ≠ 0)) && decide (pts.map Prod.fst).Nodup

/-! ### Basic facts -/

lemma toPoly_pK (a b c : ℤ) :
    toPoly (pK (K := K) a b c) = (toPoly (EllAlgo.pOf a b c)).map (algebraMap ℚ K) := by
  simp [pK, EllAlgo.pOf, CPoly.toPoly, map_intCast]

omit [DecidableEq K] in
lemma W_eqK (a b c : ℤ) : W K a b c = (⟨0, (a : K), 0, (b : K), (c : K)⟩ : WeierstrassCurve K) := by
  ext <;> simp [W, W0, WeierstrassCurve.baseChange, WeierstrassCurve.map]

lemma toPoly_pK' (a b c : ℤ) : toPoly (pK (K := K) a b c) =
    X ^ 3 + C (a : K) * X ^ 2 + C (b : K) * X + C (c : K) := by
  simp [pK, CPoly.toPoly]; ring

lemma squarefree_pK {a b c : ℤ}
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ))) :
    Squarefree (toPoly (pK (K := K) a b c)) := by
  rw [toPoly_pK, EllAlgo.toPoly_pOf]
  have hsep : (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)).Separable :=
    (PerfectField.separable_iff_squarefree).mpr hsq
  exact (hsep.map).squarefree

lemma evF_pK {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] (ι : K →+* Kc) (x : E)
    (a b c : ℤ) : evF ι x (pK a b c) = x ^ 3 + a * x ^ 2 + b * x + c := by
  simp [evF, pK, CPoly.toPoly, map_intCast]; ring

lemma ordK_spec (a b c : ℤ) {o : Option (K × K)} {P : (W K a b c).toAffine.Point}
    (hrep : RepF a b c o P) (N : ℕ) (ht : torsionTestF a b c o N = true) :
    1 ≤ ordK a b c o N ∧ ordK a b c o N • P = 0 := by
  simp only [torsionTestF, List.any_eq_true, List.mem_range] at ht
  obtain ⟨k, hk, hk'⟩ := ht
  have hsome : ((List.range N).find? fun k ↦ (mulPtF a b c o (k + 1)).isNone).isSome := by
    rw [List.find?_isSome]; exact ⟨k, List.mem_range.mpr hk, hk'⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsome
  have hj' := List.find?_some hj
  simp only [ordK, hj, Option.map_some, Option.getD_some]
  refine ⟨by omega, ?_⟩
  have hr := mulPtF_spec a b c hrep (j + 1)
  rcases hm : mulPtF a b c o (j + 1) with _ | ⟨u, w⟩
  · rw [hm] at hr; exact hr
  · rw [hm] at hj'; simp at hj'

omit [DecidableEq K] in
lemma intPt_valK (t : ℚ) (L : ℕ) (hd : t.den ∣ L) (hL : L ≠ 0) :
    (((t * L).num : ℤ) : K) / (L : K) = ((t : ℚ) : K) := by
  have h := EllAlgo.num_mul_of_den_dvd t L hd
  have h' : (((t * L).num : ℤ) : K) = ((t * L : ℚ) : K) := by
    rw [← h]; push_cast; rfl
  rw [h', Rat.cast_mul, Rat.cast_natCast]
  field_simp

/-! ### Point sums -/

/-- The point `(α, β)` (or `0`). -/
noncomputable def ptK (a b c : ℤ) (q : K × K × ℤ) : (W K a b c).toAffine.Point :=
  if h : q.2.1 * q.2.1 = q.1 ^ 3 + (a : K) * q.1 ^ 2 + (b : K) * q.1 + (c : K) ∧ q.2.1 ≠ 0 then
    WeierstrassCurve.Affine.Point.some _ _ (ns_of_eq a b c h.1 h.2) else 0

lemma mul_repK (a b c : ℤ) (q : K × K × ℤ)
    (hq : q.2.1 * q.2.1 = q.1 ^ 3 + (a : K) * q.1 ^ 2 + (b : K) * q.1 + (c : K) ∧ q.2.1 ≠ 0) :
    RepF a b c (mulPtF a b c (some (q.1, ((q.2.2.sign : ℤ) : K) * q.2.1)) q.2.2.natAbs)
      (q.2.2 • ptK a b c q) := by
  have hP : ptK a b c q = WeierstrassCurve.Affine.Point.some _ _ (ns_of_eq a b c hq.1 hq.2) := by
    simp only [ptK, dif_pos hq]
  rw [hP]
  rcases lt_trichotomy q.2.2 0 with hz | hz | hz
  · have e : ((q.2.2.sign : ℤ) : K) * q.2.1 = -q.2.1 := by
      rw [Int.sign_eq_neg_one_of_neg hz]; simp
    rw [e]
    have hneq : -q.2.1 * -q.2.1 = q.1 ^ 3 + (a : K) * q.1 ^ 2 + (b : K) * q.1 + (c : K) := by
      rw [neg_mul_neg]; exact hq.1
    have hns := ns_of_eq a b c hneq (neg_ne_zero.mpr hq.2)
    have hneg : -(WeierstrassCurve.Affine.Point.some _ _ (ns_of_eq a b c hq.1 hq.2) :
        (W K a b c).toAffine.Point) = WeierstrassCurve.Affine.Point.some _ _ hns := by
      rw [WeierstrassCurve.Affine.Point.neg_some]
      exact some_congrF a b c rfl (negY_W a b c _ _)
    have := mulPtF_spec a b c (o := some (q.1, -q.2.1)) (P := WeierstrassCurve.Affine.Point.some _ _ hns)
      ⟨hns, rfl⟩ q.2.2.natAbs
    rw [← hneg, ← natCast_zsmul, zsmul_neg, ← neg_zsmul, Int.natCast_natAbs, abs_of_neg hz,
      neg_neg] at this
    exact this
  · rw [hz]; simp [mulPtF, RepF]
  · have e : ((q.2.2.sign : ℤ) : K) * q.2.1 = q.2.1 := by
      rw [Int.sign_eq_one_of_pos hz]; simp
    rw [e]
    have := mulPtF_spec a b c (o := some (q.1, q.2.1))
      (P := WeierstrassCurve.Affine.Point.some _ _ (ns_of_eq a b c hq.1 hq.2)) ⟨_, rfl⟩ q.2.2.natAbs
    rw [← natCast_zsmul, Int.natCast_natAbs, abs_of_pos hz] at this
    exact this

/-- **`sumPtK` computes `∑ zᵢ Pᵢ`.** -/
lemma sumPtK_spec (a b c : ℤ) : ∀ pts : List (K × K × ℤ), (∀ q ∈ pts,
    q.2.1 * q.2.1 = q.1 ^ 3 + (a : K) * q.1 ^ 2 + (b : K) * q.1 + (c : K) ∧ q.2.1 ≠ 0) →
    RepF a b c (sumPtK a b c pts) ((pts.map fun q ↦ q.2.2 • ptK a b c q).sum)
  | [], _ => by simp [sumPtK, RepF]
  | q :: t, h => by
    rw [List.map_cons, List.sum_cons]
    exact addPtF_spec a b c (mul_repK a b c q (h q List.mem_cons_self))
      (sumPtK_spec a b c t fun q' hq' ↦ h q' (List.mem_cons_of_mem _ hq'))

/-! ### Existence of the certificate -/

set_option maxHeartbeats 1600000 in
/-- **A relation exists** when `n S = 0`. -/
lemma exists_relationK {a b c : ℤ}
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (pts : List (K × K × ℤ))
    (hon : ∀ q ∈ pts, q.2.1 * q.2.1 = q.1 ^ 3 + (a : K) * q.1 ^ 2 + (b : K) * q.1 + (c : K) ∧
      q.2.1 ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (hnS : n • (pts.map fun q ↦ q.2.2 • ptK a b c q).sum = 0) :
    ∃ cs : List K, cs.length = (EllAlgo.ellCols (pK a b c) (EllAlgo.ptsQ pts n) (EllAlgo.ellNa (EllAlgo.ptsQ pts n))
      (EllAlgo.ellNb (EllAlgo.ptsQ pts n))).length ∧
      CPoly.lcomb cs (EllAlgo.ellCols (pK a b c) (EllAlgo.ptsQ pts n) (EllAlgo.ellNa (EllAlgo.ptsQ pts n)) (EllAlgo.ellNb (EllAlgo.ptsQ pts n))) = 0 ∧
      CPoly.toPoly cs ≠ 0 := by
  classical
  set L := pts.length
  let α : Fin L → K := fun i ↦ pts[i].1
  let β : Fin L → K := fun i ↦ pts[i].2.1
  let z : Fin L → ℤ := fun i ↦ pts[i].2.2
  let y' : Fin L → K := fun i ↦ if z i = 0 then β i else ((z i).sign : K) * β i
  have honi : ∀ i : Fin L, β i * β i = α i ^ 3 + (a : K) * α i ^ 2 + (b : K) * α i + (c : K) ∧
      β i ≠ 0 := fun i ↦ hon _ (List.getElem_mem i.2)
  have hsgn : ∀ w : ℤ, w ≠ 0 → ((w.sign : ℤ) : K) * ((w.sign : ℤ) : K) = 1 := by
    intro w hw
    rcases lt_trichotomy w 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; simp
    · exact absurd h hw
    · rw [Int.sign_eq_one_of_pos h]; simp
  have hy'sq : ∀ i, y' i * y' i = β i * β i := by
    intro i; simp only [y']; split_ifs with h
    · rfl
    · rw [show ((z i).sign : K) * β i * (((z i).sign : K) * β i) =
        (((z i).sign : ℤ) : K) * (((z i).sign : ℤ) : K) * (β i * β i) by push_cast; ring, hsgn _ h,
        one_mul]
  have hy'0 : ∀ i, y' i ≠ 0 := by
    intro i h0
    have := hy'sq i
    rw [h0, zero_mul] at this
    exact (honi i).2 (mul_self_eq_zero.mp this.symm)
  have hns : ∀ i, (W K a b c).toAffine.Nonsingular (α i) (y' i) := fun i ↦
    ns_of_eq a b c (by rw [hy'sq]; exact (honi i).1) (hy'0 i)
  have hP : ∀ i, (W K a b c).toAffine.Nonsingular (α i) (β i) := fun i ↦
    ns_of_eq a b c (honi i).1 (honi i).2
  let m : Fin L → ℕ := fun i ↦ n * (z i).natAbs
  let s := (Finset.univ : Finset (Fin L)).filter fun i ↦ z i ≠ 0
  -- the relation `∑ mᵢ Qᵢ = 0`
  have hterm : ∀ i, (m i • (WeierstrassCurve.Affine.Point.some _ _ (hns i) : (W K a b c).toAffine.Point)) =
      (n : ℤ) • (z i • (WeierstrassCurve.Affine.Point.some _ _ (hP i) : (W K a b c).toAffine.Point)) := by
    intro i
    rw [smul_smul, ← natCast_zsmul]
    by_cases h0 : z i = 0
    · simp [m, h0]
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have hQ : (WeierstrassCurve.Affine.Point.some _ _ (hns i) : (W K a b c).toAffine.Point) = -WeierstrassCurve.Affine.Point.some _ _ (hP i) := by
        rw [WeierstrassCurve.Affine.Point.neg_some]
        simp only [WeierstrassCurve.Affine.Point.some.injEq, true_and, y', if_neg h0,
          Int.sign_eq_neg_one_of_neg hneg]
        rw [negY_W]; simp
      rw [hQ, zsmul_neg, ← neg_zsmul]
      congr 1
      simp only [m]
      push_cast
      rw [abs_of_neg hneg]; ring
    · have hQ : (WeierstrassCurve.Affine.Point.some _ _ (hns i) : (W K a b c).toAffine.Point) = WeierstrassCurve.Affine.Point.some _ _ (hP i) := by
        simp only [WeierstrassCurve.Affine.Point.some.injEq, true_and, y', if_neg h0,
          Int.sign_eq_one_of_pos hpos]
        simp
      rw [hQ]
      congr 1
      simp only [m]
      push_cast
      rw [abs_of_pos hpos]
  have hS : (pts.map fun q ↦ q.2.2 • ptK a b c q).sum =
      ∑ i : Fin L, z i • (WeierstrassCurve.Affine.Point.some _ _ (hP i) : (W K a b c).toAffine.Point) := by
    rw [EllAlgo.sum_map_eq_fin]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [ptK]
    split_ifs with hc
    · rfl
    · exact absurd (honi i) hc
  have hsum : ∑ i ∈ s, m i • (WeierstrassCurve.Affine.Point.some _ _ (hns i) : (W K a b c).toAffine.Point) = 0 := by
    rw [Finset.sum_filter]
    have : ∀ i, (if z i ≠ 0 then m i • (WeierstrassCurve.Affine.Point.some _ _ (hns i) : (W K a b c).toAffine.Point) else 0) =
        (n : ℤ) • (z i • (WeierstrassCurve.Affine.Point.some _ _ (hP i) : (W K a b c).toAffine.Point)) := by
      intro i
      split_ifs with h
      · exact hterm i
      · push_neg at h; simp only [h, zero_zsmul, smul_zero]
    rw [Finset.sum_congr rfl fun i _ ↦ this i, ← Finset.smul_sum, ← hS, natCast_zsmul, hnS]
  obtain ⟨A, B, hAB, hA, hB, hloc⟩ := EllAlgo.exists_localW (a : K) (b : K) (c : K) (pK a b c)
    (toPoly_pK' a b c) (W K a b c) (W_eqK a b c) (squarefree_pK hsq) s α y' hns (fun i _ ↦ hy'0 i) m hsum
  -- the sizes
  set na := EllAlgo.ellNa (EllAlgo.ptsQ pts n)
  set nb := EllAlgo.ellNb (EllAlgo.ptsQ pts n)
  have hM : ((EllAlgo.ptsQ pts n).map fun q ↦ q.2.2).sum = ∑ i ∈ s, m i := by
    rw [EllAlgo.ptsQ, List.map_map, EllAlgo.sum_map_eq_fin, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs with h
    · rfl
    · push_neg at h; simp [m, z]; exact Or.inr h
  have hna : na = (∑ i ∈ s, m i) / 2 + 1 := by
    show EllAlgo.ellNa (EllAlgo.ptsQ pts n) = _; unfold EllAlgo.ellNa; rw [hM]
  have hnb : nb = ((∑ i ∈ s, m i) - 1) / 2 := by
    show EllAlgo.ellNb (EllAlgo.ptsQ pts n) = _; unfold EllAlgo.ellNb; rw [hM]
  have hAd : A = 0 ∨ A.natDegree < na := Or.inr (by omega)
  have hBd : B = 0 ∨ B.natDegree < nb := hB.imp_right (by omega)
  refine ⟨(List.range na).map A.coeff ++ (List.range nb).map B.coeff, ?_, ?_, ?_⟩
  · rw [EllAlgo.length_ellCols]; simp
  · have h1 : ((List.range na).map A.coeff ++ (List.range nb).map B.coeff).take na =
        (List.range na).map A.coeff := by
      rw [List.take_left' (by simp)]
    have h2 : (((List.range na).map A.coeff ++ (List.range nb).map B.coeff).drop na).take nb =
        (List.range nb).map B.coeff := by
      rw [List.drop_left' (by simp), List.take_of_length_le (by simp)]
    rw [EllAlgo.lcomb_ellCols, h1, h2, EllAlgo.toPoly_range_coeff A na hAd,
      EllAlgo.toPoly_range_coeff B nb hBd]
    intro q hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq0
    set i : Fin L := ⟨j, hj⟩
    by_cases h0 : z i = 0
    · have : n * (pts[j].2.2).natAbs = 0 := by
        simp only [z, i] at h0; simp; exact Or.inr h0
      simp only [this, pow_zero, one_dvd]
    · have his : i ∈ s := by simp [s, h0]
      have hm : 1 ≤ m i := by
        simp only [m]
        exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (Int.natAbs_ne_zero.mpr h0))
      have := hloc i his hm
      simp only [y', if_neg h0] at this
      exact this
  · rw [CPoly.toPoly_append, EllAlgo.toPoly_range_coeff A na hAd,
      EllAlgo.toPoly_range_coeff B nb hBd]
    simp only [List.length_map, List.length_range]
    intro h0
    have hBz : B = 0 := by
      by_contra hB0
      have e : A = -(X ^ na * B) := by linear_combination h0
      have hdeg := congrArg natDegree e
      rw [natDegree_neg, natDegree_mul (pow_ne_zero _ X_ne_zero) hB0, natDegree_X_pow] at hdeg
      rcases hAd with hA0 | hAd
      · rw [hA0] at e
        have : X ^ na * B = 0 := by linear_combination e
        exact hB0 ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ X_ne_zero))
      · omega
    rw [hBz, mul_zero, add_zero] at h0
    exact hAB.elim (fun h ↦ h h0) (fun h ↦ h hBz)


set_option maxHeartbeats 1600000 in
/-- **The certificate of one component is found** when `n S = 0`. -/
lemma partCertK_ne_none {a b c : ℤ}
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (B : CPoly K) (L : ℕ) (hL : L ≠ 0) (pts : List (K × K × ℤ))
    (hon : ∀ q ∈ pts, q.2.1 * q.2.1 = q.1 ^ 3 + (a : K) * q.1 ^ 2 + (b : K) * q.1 + (c : K) ∧
      q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (n : ℕ) (hn : 1 ≤ n)
    (hnS : n • (pts.map fun q ↦ q.2.2 • ptK a b c q).sum = 0) :
    partCertK a b c B L pts n ≠ none := by
  obtain ⟨cs, hl, hrel, hne⟩ := exists_relationK hsq pts hon n hn hnS
  obtain ⟨w, hw, hwne⟩ := EllAlgo.exists_good_basis _ cs hl hrel hne
  rw [EllAlgo.length_ellCols] at hwne
  set pC := pK (K := K) a b c
  set na := EllAlgo.ellNa (EllAlgo.ptsQ pts n)
  set nb := EllAlgo.ellNb (EllAlgo.ptsQ pts n)
  have hsome : ((CPoly.nullBasis (EllAlgo.ellCols pC (EllAlgo.ptsQ pts n) na nb)).find?
      fun w ↦ !CPoly.isZero (w.take (na + nb))).isSome := by
    rw [List.find?_isSome]
    refine ⟨w, hw, ?_⟩
    have : CPoly.isZero (w.take (na + nb)) = false := by
      rcases h : CPoly.isZero (w.take (na + nb)) with _ | _
      · rfl
      · exact absurd ((CPoly.isZero_iff _).mp h) hwne
    simp [this]
  obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp hsome
  have hw'mem := List.mem_of_find?_eq_some hw'
  have hw'p := List.find?_some hw'
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hw'p
  have hw'ne : CPoly.toPoly (w'.take (na + nb)) ≠ 0 := by
    intro h0; rw [← CPoly.isZero_iff] at h0; rw [h0] at hw'p; exact Bool.noConfusion hw'p
  have hpC := toPoly_pK' (K := K) a b c
  have hp3 : (toPoly pC).natDegree = 3 := by rw [hpC]; compute_degree!
  have hon' : ∀ q ∈ pts, (toPoly pC).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0 := by
    intro q hq
    refine ⟨?_, (hon q hq).2⟩
    rw [hpC]; simp; linear_combination -(hon q hq).1
  have hcheck := EllAlgo.certCheck_ok_gen pC hp3 pts hon' hnd L hL n hn w'
    (CPoly.nullBasis_sound _ w' hw'mem) hw'ne B
  unfold partCertK EllAlgo.ellSolve
  rw [hw']
  simp only
  rw [if_pos hcheck]
  simp


/-! ### The procedure -/

variable [QCoords K]

open QCoords

/-- The common denominator of the `j`-th coordinates of the residues. -/
def denLK (j : Fin (dim K)) (pts : List (K × K × K)) : ℕ := denL (pts.map fun q ↦ coord j q.2.2)

/-- The `j`-th component: integer multiplicities `Lⱼ λⱼ(rᵢ)`. -/
def PjK (j : Fin (dim K)) (pts : List (K × K × K)) : List (K × K × ℤ) :=
  intPtsK (denLK j pts) (fun r ↦ coord j r) pts

/-- The certificates of the components `js`. -/
def certsK (a b c : ℤ) (pts : List (K × K × K)) (N : ℕ) :
    List (Fin (dim K)) → Option (List (Fin (dim K) × CPoly K))
  | [] => some []
  | j :: t =>
    match partCertK a b c [] (denLK j pts) (PjK j pts) (ordK a b c (sumPtK a b c (PjK j pts)) N),
      certsK a b c pts N t with
    | some R, some Rs => some ((j, R) :: Rs)
    | _, _ => none

/-- `∑ⱼ bⱼ Rⱼ`. -/
def sumBK : List (Fin (dim K) × CPoly K) → CPoly K
  | [] => []
  | (j, R) :: t => add (smul (bvec j) R) (sumBK t)

/-- **The procedure** (`N`: the torsion bound at an auxiliary prime; `none`: invalid data). -/
def ellDecideK (a b c : ℤ) (B : CPoly K) (pts : List (K × K × K)) (N : ℕ) : Option Bool :=
  if validK a b c pts then
    if (List.finRange (dim K)).any fun j ↦ !torsionTestF a b c (sumPtK a b c (PjK j pts)) N then
      some false
    else
      match certsK a b c pts N (List.finRange (dim K)) with
      | some Rs => some (isZero (hypRed (pK a b c) (add B (sumBK Rs))).2)
      | none => none
  else none



/-! ### Completeness -/

lemma certsK_ne_none {a b c : ℤ}
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (pts : List (K × K × K))
    (hon : ∀ q ∈ pts, q.2.1 * q.2.1 = q.1 ^ 3 + (a : K) * q.1 ^ 2 + (b : K) * q.1 + (c : K) ∧
      q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (N : ℕ) :
    ∀ js : List (Fin (dim K)), (∀ j ∈ js, torsionTestF a b c (sumPtK a b c (PjK j pts)) N = true) →
      certsK a b c pts N js ≠ none
  | [], _ => by simp [certsK]
  | j :: t, ht => by
    have honj : ∀ q ∈ PjK j pts, q.2.1 * q.2.1 = q.1 ^ 3 + (a : K) * q.1 ^ 2 + (b : K) * q.1 +
        (c : K) ∧ q.2.1 ≠ 0 := by
      intro q hq; obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq; exact hon q0 hq0
    have hndj : ((PjK j pts).map Prod.fst).Nodup := by
      rw [PjK, intPtsK, List.map_map]; exact hnd
    obtain ⟨hn1, hn⟩ := ordK_spec a b c (sumPtK_spec a b c _ honj) N (ht j List.mem_cons_self)
    obtain ⟨R, hR⟩ := Option.ne_none_iff_exists'.mp
      (partCertK_ne_none hsq [] (denLK j pts) (denL_ne_zero _) _ honj hndj _ hn1 hn)
    obtain ⟨Rs, hRs⟩ := Option.ne_none_iff_exists'.mp
      (certsK_ne_none hsq pts hon hnd N t fun j' hj' ↦ ht j' (List.mem_cons_of_mem _ hj'))
    simp [certsK, hR, hRs]

/-- **Completeness of `ellDecideK`**: on valid data it always answers. -/
theorem ellDecideK_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (B : CPoly K) (pts : List (K × K × K)) (N : ℕ) (hv : validK a b c pts = true) :
    ellDecideK a b c B pts N ≠ none := by
  have hv' := hv
  simp only [validK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv'
  obtain ⟨hon, hnd⟩ := hv'
  unfold ellDecideK
  rw [if_pos hv]
  split_ifs with hA
  · simp
  · have ht : ∀ j ∈ List.finRange (dim K), torsionTestF a b c (sumPtK a b c (PjK j pts)) N = true := by
      intro j hj
      by_contra h0
      exact hA (List.any_eq_true.mpr ⟨j, hj, by simpa using h0⟩)
    obtain ⟨Rs, hRs⟩ := Option.ne_none_iff_exists'.mp (certsK_ne_none hsq pts hon hnd N _ ht)
    rw [hRs]
    simp

section Spec

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **A certificate removes the logarithmic part of one component.** -/
lemma partCertK_spec (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (ι : K →+* Kc) (B : CPoly K) (L : ℕ)
    (pts : List (K × K × ℤ)) (n : ℕ) (R : CPoly K) (h : partCertK a b c B L pts n = some R) :
    ∃ w : E, HasElementaryIntegralIn w ∧
      (evF ι x B + (pts.map fun q ↦ algebraMap Kc E (ι ((q.2.2 : K) / L * q.2.1)) /
        (x - algebraMap Kc E (ι q.1))).sum) / y = evF ι x R / y + w := by
  unfold partCertK at h
  split at h
  swap
  · cases h
  rename_i AB hAB
  split_ifs at h with hchk
  simp only [Option.some.injEq] at h
  subst h
  set cc : K := 1 / ((n : K) * (L : K)) with hcc
  set G := EllAlgo.fracG B L pts with hGdef
  unfold EllAlgo.certCheck at hchk
  simp only [Bool.and_eq_true, Bool.not_eq_true', EllAlgo.certN, EllAlgo.certM] at hchk
  obtain ⟨⟨hN, hG⟩, hbeq⟩ := hchk
  have hN' : toPoly AB.1 ^ 2 - toPoly AB.2 ^ 2 * toPoly (pK a b c) ≠ 0 := by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hN; apply hN
    simp only [toPoly_sub, toPoly_mul]; linear_combination h0
  have hG' : toPoly G.2 ≠ 0 := by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hG; exact hG h0
  have hid := (beq_iff _ _).mp hbeq
  have h2 : toPoly ([2] : CPoly K) = 2 := by
    rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
  simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_smul, toPoly_deriv, h2] at hid
  have hidK := congrArg (Polynomial.map ι) hid
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
    map_C, Polynomial.map_ofNat, ← Polynomial.derivative_map] at hidK
  have hxa : ∀ z : K, x - algebraMap Kc E (ι z) ≠ 0 := fun z ↦ x_sub_const_ne hC x hx (ι z)
  have hpK : (toPoly (pK a b c)).map ι ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff ι.injective, toPoly_pK,
      Polynomial.map_ne_zero_iff (algebraMap ℚ K).injective, EllAlgo.toPoly_pOf]
    exact hsq.ne_zero
  have hyK : y ^ 2 = aeval x ((toPoly (pK a b c)).map ι) := by
    rw [hy]; exact (evF_pK ι x a b c).symm
  have hGK : (toPoly G.2).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hG'
  have hNK : ((toPoly AB.1).map ι) ^ 2 - ((toPoly AB.2).map ι) ^ 2 * (toPoly (pK a b c)).map ι ≠ 0 := by
    rw [← Polynomial.map_pow, ← Polynomial.map_pow, ← Polynomial.map_mul, ← Polynomial.map_sub]
    exact (Polynomial.map_ne_zero_iff ι.injective).mpr hN'
  obtain ⟨w, hw, key⟩ := ell_log_decompK hC x y hx _ hpK hyK ((toPoly G.1).map ι) ((toPoly G.2).map ι)
    ((toPoly AB.1).map ι) ((toPoly AB.2).map ι)
    ((toPoly (EllAlgo.certR (pK a b c) AB G cc)).map ι) (ι cc) hGK hNK (by linear_combination hidK)
  refine ⟨w, hw, ?_⟩
  obtain ⟨-, hfr⟩ := fracG_evF ι x hxa B L pts
  rw [← hGdef] at hfr
  rw [← hfr, div_div]
  exact key



/-- The `j`-th logarithmic component `∑ (zᵢ/Lⱼ) βᵢ / (x − αᵢ)`. -/
noncomputable def compK (ι : K →+* Kc) (x : E) (L : ℕ) (l : List (K × K × ℤ)) : E :=
  (l.map fun q ↦ algebraMap Kc E (ι ((q.2.2 : K) / L * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum

/-- **Splitting the residues along the basis.** -/
lemma split_residues (ι : K →+* Kc) (x : E) (pts : List (K × K × K)) (L : Fin (dim K) → ℕ)
    (hL0 : ∀ j, L j ≠ 0) :
    ∀ l : List (K × K × K), (∀ q ∈ l, ∀ j, (coord j q.2.2).den ∣ L j) →
    (l.map fun q ↦ algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum =
      ((List.finRange (dim K)).map fun j ↦ algebraMap Kc E (ι (bvec j)) *
        compK ι x (L j) (intPtsK (L j) (fun r ↦ coord j r) l)).sum
  | [], _ => by simp [compK, intPtsK]
  | q :: t, h => by
    simp only [List.map_cons, List.sum_cons, compK, intPtsK] at *
    rw [split_residues ι x pts L hL0 t fun q' hq' ↦ h q' (List.mem_cons_of_mem _ hq')]
    simp only [mul_add, List.sum_map_add]
    congr 1
    have hq := h q List.mem_cons_self
    conv_lhs => rw [QCoords.repr q.2.2]
    rw [Finset.sum_mul, map_sum, map_sum, Finset.sum_div, ← Fin.sum_univ_def]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [intPt_valK _ _ (hq j) (hL0 j)]
    simp only [map_mul]
    ring

/-- **The certificates remove every component.** -/
lemma certsK_decomp (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (ι : K →+* Kc) (pts : List (K × K × K))
    (N : ℕ) : ∀ (js : List (Fin (dim K))) (Rs : List (Fin (dim K) × CPoly K)),
    certsK a b c pts N js = some Rs →
    ∃ w : E, HasElementaryIntegralIn w ∧
      (js.map fun j ↦ algebraMap Kc E (ι (bvec j)) *
        compK ι x (denLK j pts) (PjK j pts)).sum / y = evF ι x (sumBK Rs) / y + w
  | [], Rs, h => by
    simp only [certsK, Option.some.injEq] at h; subst h
    exact ⟨0, hasElementaryIntegralIn_zero', by simp [sumBK, evF, CPoly.toPoly]⟩
  | j :: t, Rs, h => by
    simp only [certsK] at h
    split at h
    · rename_i R Rs' h1 h2
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨w1, hw1, e1⟩ := partCertK_spec hC x y hx a b c hsq hy ι [] _ _ _ R h1
      obtain ⟨w2, hw2, e2⟩ := certsK_decomp hC x y hx a b c hsq hy ι pts N t Rs' h2
      have he : evF ι x ([] : CPoly K) = 0 := by simp [evF, CPoly.toPoly]
      rw [he, zero_add] at e1
      have hc : (algebraMap Kc E (ι (bvec j)))′ = 0 := by rw [deriv_algebraMap, hC, map_zero]
      refine ⟨algebraMap Kc E (ι (bvec j)) * w1 + w2, (hw1.const_mul _ hc).add hw2, ?_⟩
      simp only [List.map_cons, List.sum_cons, sumBK, evF_add, evF_smul, add_div]
      rw [e2, mul_div_assoc]
      simp only [compK] at e1 ⊢
      rw [e1]
      ring
    · cases h

set_option maxHeartbeats 3200000 in
/-- **Correctness of `ellDecideK`**: an answer `some b` is the truth, for any embedding
`ι : K → Kc` of the coefficients into the constants. -/
theorem ellDecideK_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : K →+* Kc) (B : CPoly K) (pts : List (K × K × K)) (p0 : ℕ) [Fact p0.Prime]
    (hp02 : p0 ≠ 2) (hgood : goodRedMod p0 a b c) (φ : K →ₐ[ℚ] ℚ_[p0]) (N : ℕ)
    (hN : Fintype.card (Option (RedPts p0 a b c)) ≤ N)
    (ans : Bool) (h : ellDecideK a b c B pts N = some ans) :
    ans = true ↔ HasElementaryIntegral ((evF ι x B + (pts.map fun q ↦
      algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum) / y) := by
  classical
  have hL0 : ∀ j, denLK j pts ≠ 0 := fun j ↦ denL_ne_zero _
  have hd : ∀ q ∈ pts, ∀ j, (coord j q.2.2).den ∣ denLK j pts := fun q hq j ↦
    den_dvd_denL (List.mem_map_of_mem (f := fun q : K × K × K ↦ coord j q.2.2) hq)
  unfold ellDecideK at h
  split_ifs at h with hv htA
  simp only [validK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hon, hnd⟩ := hv
  · -- some component has infinite order
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.false_eq_true, false_iff]
    obtain ⟨j, -, hj⟩ := List.any_eq_true.mp htA
    simp only [Bool.not_eq_true'] at hj
    set n := pts.length
    have hP : ∀ i : Fin n, (W K a b c).toAffine.Nonsingular pts[i].1 pts[i].2.1 := fun i ↦
      ns_of_eq a b c (hon _ (List.getElem_mem i.2)).1 (hon _ (List.getElem_mem i.2)).2
    have hβ : ∀ i ∈ (Finset.univ : Finset (Fin n)), pts[i].2.1 ≠ 0 := fun i _ ↦
      (hon _ (List.getElem_mem i.2)).2
    have hinj : Set.InjOn (fun i : Fin n ↦ pts[i].1) ↑(Finset.univ : Finset (Fin n)) := by
      intro i _ k _ hik
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (hi := by rw [List.length_map]; exact i.2)
        (hj := by rw [List.length_map]; exact k.2)).mp (by simp only [List.getElem_map]; exact hik))
    have honj : ∀ q ∈ PjK j pts, q.2.1 * q.2.1 = q.1 ^ 3 + (a : K) * q.1 ^ 2 + (b : K) * q.1 +
        (c : K) ∧ q.2.1 ≠ 0 := by
      intro q hq; obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq; exact hon q0 hq0
    have hrep := sumPtK_spec a b c (PjK j pts) honj
    have hnt := (torsionTestF_spec a b c φ hp02 hgood hrep N hN).not.mp (by simp [hj])
    have hsum : ((PjK j pts).map fun q ↦ q.2.2 • ptK a b c q).sum =
        ∑ i : Fin n, (coord j pts[i].2.2 * denLK j pts).num •
          (WeierstrassCurve.Affine.Point.some _ _ (hP i) : (W K a b c).toAffine.Point) := by
      rw [PjK, intPtsK, List.map_map, EllAlgo.sum_map_eq_fin]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [Function.comp_apply, ptK]
      split_ifs with hc
      · rfl
      · exact absurd (hon _ (List.getElem_mem i.2)) hc
    rw [hsum] at hnt
    rw [EllAlgo.sum_map_eq_fin, show evF ι x B = aeval x ((toPoly B).map ι) from rfl]
    have key := not_elem_of_nontorsionK hC hCall x y hx a b c hsq hy hgen ι ((toPoly B).map ι)
      (Finset.univ : Finset (Fin n))
      (fun i ↦ pts[i].1) (fun i ↦ pts[i].2.1) (fun i ↦ pts[i].2.2) hP hβ hinj
      (coord j) (fun i ↦ (coord j pts[i].2.2 * denLK j pts).num) (denLK j pts) (hL0 j)
      (fun i _ ↦ (intPt_valQ _ _ (hd _ (List.getElem_mem i.2) j) (hL0 j)).symm) hnt
    exact key
  · -- the certificates
    split at h
    swap
    · cases h
    rename_i Rs hRs
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨w, hw, e⟩ := certsK_decomp hC x y hx a b c hsq hy ι pts N _ Rs hRs
    have hsplit : (evF ι x B + (pts.map fun q ↦ algebraMap Kc E (ι (q.2.2 * q.2.1)) /
        (x - algebraMap Kc E (ι q.1))).sum) / y = evF ι x (add B (sumBK Rs)) / y + w := by
      rw [split_residues ι x pts (fun j ↦ denLK j pts) hL0 pts fun q hq j ↦ hd q hq j, evF_add,
        add_div, add_div, add_assoc]
      congr 1
    rw [hsplit]
    have hpm : toPoly (pK (K := K) a b c) = (toPoly (EllAlgo.pOf a b c)).map (algebraMap ℚ K) :=
      toPoly_pK a b c
    have hdeg3 : (toPoly (EllAlgo.pOf a b c)).natDegree = 3 := by
      rw [EllAlgo.toPoly_pOf]; compute_degree!
    have hdec := hyp_decidesF hC hCall ι x y hx (EllAlgo.pOf a b c)
      (by rw [EllAlgo.toPoly_pOf]; exact hsq) (by rw [hdeg3]; decide)
      (by rw [EllAlgo.toPoly_pOf, hy]; simp) hgen (pK a b c) hpm (add B (sumBK Rs))
    rw [← hdec]
    constructor
    · intro h0; exact h0.add_in hw
    · intro h0
      have := h0.sub_in hw
      rwa [add_sub_cancel_right] at this

end Spec


/-! ### `ℚ(√d)` -/

instance quadCoords (d : ℤ) [Fact (¬IsSquare (d : ℚ))] : QCoords (QuadraticAlgebra ℚ (d : ℚ) 0) where
  dim := 2
  coord := ![QuadraticAlgebra.reₗ (d : ℚ) 0, QuadraticAlgebra.imₗ (d : ℚ) 0]
  bvec := ![1, ⟨0, 1⟩]
  repr z := by ext <;> simp [Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one]

end EllQuad
