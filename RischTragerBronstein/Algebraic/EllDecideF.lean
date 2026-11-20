import RischTragerBronstein.Algebraic.EllQuadDecide
import RischTragerBronstein.Algebraic.EllGenComplete

/-!
# Elliptic integrals with simple poles at points over `ℚ(√d)`

`∫ (B(x) + ∑ᵢ rᵢ βᵢ / (x − αᵢ)) dx / y` on `y² = x³ + ax² + bx + c`, with `Pᵢ = (αᵢ, βᵢ) ∈ E(F)`,
`F = ℚ(√d)`, `βᵢ ≠ 0`, distinct `αᵢ`, residues `rᵢ ∈ F` and `B ∈ F[x]`. Any number of rational
points and conjugate pairs may occur together. `ellDecideF` splits the residues along the
`ℚ`-basis `1, √d`: `rᵢ = uᵢ + vᵢ √d`. With `L₁ = lcm den uᵢ`, `L₂ = lcm den vᵢ`:

1. if `S₁ = ∑ (L₁uᵢ) Pᵢ` or `S₂ = ∑ (L₂vᵢ) Pᵢ` has infinite order (`torsionTestF` at an auxiliary
   prime), the integral is **not elementary** (`not_elem_of_nontorsion` with `Λ = re`, `im`);
2. otherwise both logarithmic parts are removed by certificates (`partCert`) and the polynomial
   remainder is reduced over `F`: the integral is elementary iff the holomorphic remainder is `0`.

`ellDecideF_spec`: every answer is correct; `ellDecideF_ne_none`: on valid data it always
answers (`ellDecideF_decides`).
-/

open Polynomial Differential

namespace EllQuad

open CPoly EllDV

variable {d : ℤ}

local notation "F" => QuadraticAlgebra ℚ (d : ℚ) 0

/-- `lcm` of the denominators. -/
def denL (qs : List ℚ) : ℕ := (qs.map Rat.den).foldr Nat.lcm 1

/-- Integer multiplicities `L · f(rᵢ)`. -/
def intPts (L : ℕ) (f : F → ℚ) (pts : List (F × F × F)) : List (F × F × ℤ) :=
  pts.map fun q ↦ (q.1, q.2.1, (f q.2.2 * L).num)

variable [Fact (¬IsSquare (d : ℚ))]

/-- `∑ zᵢ Pᵢ` computed in `F`. -/
def sumPtF (a b c : ℤ) : List (F × F × ℤ) → Option (F × F)
  | [] => none
  | q :: t => addPtF a b c
      (mulPtF a b c (some (q.1, ((q.2.2.sign : ℤ) : F) * q.2.1)) q.2.2.natAbs) (sumPtF a b c t)

/-- The certificate for one component: `A + B y`, check, and the remainder. -/
def partCert (a b c : ℤ) (B : CPoly F) (L : ℕ) (pts : List (F × F × ℤ)) (n : ℕ) :
    Option (CPoly F) :=
  match EllAlgo.ellSolve (pF a b c) (EllAlgo.ptsQ pts n) with
  | some AB =>
    if EllAlgo.certCheck (pF a b c) AB (EllAlgo.fracG B L pts) (1 / ((n : F) * (L : F)))
    then some (EllAlgo.certR (pF a b c) AB (EllAlgo.fracG B L pts) (1 / ((n : F) * (L : F))))
    else none
  | none => none

/-- Validity of the data. -/
def validF (a b c : ℤ) (pts : List (F × F × F)) : Bool :=
  pts.all (fun q ↦ decide (q.2.1 * q.2.1 = q.1 ^ 3 + (a : F) * q.1 ^ 2 + (b : F) * q.1 + (c : F)
    ∧ q.2.1 ≠ 0)) && decide (pts.map Prod.fst).Nodup

/-- **The procedure** (`none`: invalid input). -/
def ellDecideF (a b c : ℤ) (B : CPoly F) (pts : List (F × F × F)) (p0 : ℕ) [NeZero p0] :
    Option Bool :=
  if validF a b c pts then
    let L1 := denL (pts.map fun q ↦ q.2.2.re)
    let L2 := denL (pts.map fun q ↦ q.2.2.im)
    let P1 := intPts L1 (fun r ↦ r.re) pts
    let P2 := intPts L2 (fun r ↦ r.im) pts
    let N := redCount p0 a b c + 1
    if torsionTestF a b c (sumPtF a b c P1) N = false then some false
    else if torsionTestF a b c (sumPtF a b c P2) N = false then some false
    else
      match partCert a b c B L1 P1 (ordF a b c (sumPtF a b c P1) N),
        partCert a b c [] L2 P2 (ordF a b c (sumPtF a b c P2) N) with
      | some R1, some R2 => some (isZero (hypRed (pF a b c) (add R1 (smul ⟨0, 1⟩ R2))).2)
      | _, _ => none
  else none

/-! ### Denominators -/

lemma denL_ne_zero (qs : List ℚ) : denL qs ≠ 0 :=
  EllAlgo.foldr_lcm_ne_zero _ fun a ha ↦ by
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha; exact q.den_nz

lemma den_dvd_denL {qs : List ℚ} {q : ℚ} (h : q ∈ qs) : q.den ∣ denL qs :=
  EllAlgo.dvd_foldr_lcm (List.mem_map_of_mem h)

lemma intPt_val (t : ℚ) (L : ℕ) (hd : t.den ∣ L) (hL : L ≠ 0) :
    (((t * L).num : ℤ) : F) / (L : F) = ((t : ℚ) : F) := by
  have h := EllAlgo.num_mul_of_den_dvd t L hd
  have h' : (((t * L).num : ℤ) : F) = ((t * L : ℚ) : F) := by
    rw [← h]; push_cast; rfl
  rw [h', Rat.cast_mul, Rat.cast_natCast]
  field_simp

lemma intPt_valQ (t : ℚ) (L : ℕ) (hd : t.den ∣ L) (hL : L ≠ 0) :
    (((t * L).num : ℤ) : ℚ) / (L : ℚ) = t := by
  rw [EllAlgo.num_mul_of_den_dvd t L hd]; field_simp

/-! ### Point sums -/

/-- The point `(α, β)` (or `0`). -/
noncomputable def ptF (a b c : ℤ) (q : F × F × ℤ) : (W F a b c).toAffine.Point :=
  if h : q.2.1 * q.2.1 = q.1 ^ 3 + (a : F) * q.1 ^ 2 + (b : F) * q.1 + (c : F) ∧ q.2.1 ≠ 0 then
    WeierstrassCurve.Affine.Point.some _ _ (ns_of_eq a b c h.1 h.2) else 0

lemma mul_rep (a b c : ℤ) (q : F × F × ℤ)
    (hq : q.2.1 * q.2.1 = q.1 ^ 3 + (a : F) * q.1 ^ 2 + (b : F) * q.1 + (c : F) ∧ q.2.1 ≠ 0) :
    RepF a b c (mulPtF a b c (some (q.1, ((q.2.2.sign : ℤ) : F) * q.2.1)) q.2.2.natAbs)
      (q.2.2 • ptF (d := d) a b c q) := by
  have hP : ptF a b c q = WeierstrassCurve.Affine.Point.some _ _ (ns_of_eq a b c hq.1 hq.2) := by
    simp only [ptF, dif_pos hq]
  rw [hP]
  rcases lt_trichotomy q.2.2 0 with hz | hz | hz
  · have e : ((q.2.2.sign : ℤ) : F) * q.2.1 = -q.2.1 := by
      rw [Int.sign_eq_neg_one_of_neg hz]; simp
    rw [e]
    have hneq : -q.2.1 * -q.2.1 = q.1 ^ 3 + (a : F) * q.1 ^ 2 + (b : F) * q.1 + (c : F) := by
      rw [neg_mul_neg]; exact hq.1
    have hns := ns_of_eq a b c hneq (neg_ne_zero.mpr hq.2)
    have hneg : -(WeierstrassCurve.Affine.Point.some _ _ (ns_of_eq a b c hq.1 hq.2) :
        (W F a b c).toAffine.Point) = WeierstrassCurve.Affine.Point.some _ _ hns := by
      rw [WeierstrassCurve.Affine.Point.neg_some]
      exact some_congrF a b c rfl (negY_W a b c _ _)
    have := mulPtF_spec a b c (o := some (q.1, -q.2.1)) (P := WeierstrassCurve.Affine.Point.some _ _ hns)
      ⟨hns, rfl⟩ q.2.2.natAbs
    rw [← hneg, ← natCast_zsmul, zsmul_neg, ← neg_zsmul, Int.natCast_natAbs, abs_of_neg hz,
      neg_neg] at this
    exact this
  · rw [hz]; simp [mulPtF, RepF]
  · have e : ((q.2.2.sign : ℤ) : F) * q.2.1 = q.2.1 := by
      rw [Int.sign_eq_one_of_pos hz]; simp
    rw [e]
    have := mulPtF_spec a b c (o := some (q.1, q.2.1))
      (P := WeierstrassCurve.Affine.Point.some _ _ (ns_of_eq a b c hq.1 hq.2)) ⟨_, rfl⟩ q.2.2.natAbs
    rw [← natCast_zsmul, Int.natCast_natAbs, abs_of_pos hz] at this
    exact this

/-- **`sumPtF` computes `∑ zᵢ Pᵢ`.** -/
lemma sumPtF_spec (a b c : ℤ) : ∀ pts : List (F × F × ℤ), (∀ q ∈ pts,
    q.2.1 * q.2.1 = q.1 ^ 3 + (a : F) * q.1 ^ 2 + (b : F) * q.1 + (c : F) ∧ q.2.1 ≠ 0) →
    RepF a b c (sumPtF a b c pts) ((pts.map fun q ↦ q.2.2 • ptF (d := d) a b c q).sum)
  | [], _ => by simp [sumPtF, RepF]
  | q :: t, h => by
    rw [List.map_cons, List.sum_cons]
    exact addPtF_spec a b c (mul_rep a b c q (h q List.mem_cons_self))
      (sumPtF_spec a b c t fun q' hq' ↦ h q' (List.mem_cons_of_mem _ hq'))

/-! ### Existence of the certificate -/

set_option maxHeartbeats 1600000 in
/-- **A relation exists** when `n S = 0`. -/
lemma exists_relationF {a b c : ℤ}
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (pts : List (F × F × ℤ))
    (hon : ∀ q ∈ pts, q.2.1 * q.2.1 = q.1 ^ 3 + (a : F) * q.1 ^ 2 + (b : F) * q.1 + (c : F) ∧
      q.2.1 ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (hnS : n • (pts.map fun q ↦ q.2.2 • ptF (d := d) a b c q).sum = 0) :
    ∃ cs : List F, cs.length = (EllAlgo.ellCols (pF a b c) (EllAlgo.ptsQ pts n) (EllAlgo.ellNa (EllAlgo.ptsQ pts n))
      (EllAlgo.ellNb (EllAlgo.ptsQ pts n))).length ∧
      CPoly.lcomb cs (EllAlgo.ellCols (pF a b c) (EllAlgo.ptsQ pts n) (EllAlgo.ellNa (EllAlgo.ptsQ pts n)) (EllAlgo.ellNb (EllAlgo.ptsQ pts n))) = 0 ∧
      CPoly.toPoly cs ≠ 0 := by
  classical
  set L := pts.length
  let α : Fin L → F := fun i ↦ pts[i].1
  let β : Fin L → F := fun i ↦ pts[i].2.1
  let z : Fin L → ℤ := fun i ↦ pts[i].2.2
  let y' : Fin L → F := fun i ↦ if z i = 0 then β i else ((z i).sign : F) * β i
  have honi : ∀ i : Fin L, β i * β i = α i ^ 3 + (a : F) * α i ^ 2 + (b : F) * α i + (c : F) ∧
      β i ≠ 0 := fun i ↦ hon _ (List.getElem_mem i.2)
  have hsgn : ∀ w : ℤ, w ≠ 0 → ((w.sign : ℤ) : F) * ((w.sign : ℤ) : F) = 1 := by
    intro w hw
    rcases lt_trichotomy w 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; simp
    · exact absurd h hw
    · rw [Int.sign_eq_one_of_pos h]; simp
  have hy'sq : ∀ i, y' i * y' i = β i * β i := by
    intro i; simp only [y']; split_ifs with h
    · rfl
    · rw [show ((z i).sign : F) * β i * (((z i).sign : F) * β i) =
        (((z i).sign : ℤ) : F) * (((z i).sign : ℤ) : F) * (β i * β i) by push_cast; ring, hsgn _ h,
        one_mul]
  have hy'0 : ∀ i, y' i ≠ 0 := by
    intro i h0
    have := hy'sq i
    rw [h0, zero_mul] at this
    exact (honi i).2 (mul_self_eq_zero.mp this.symm)
  have hns : ∀ i, (W F a b c).toAffine.Nonsingular (α i) (y' i) := fun i ↦
    ns_of_eq a b c (by rw [hy'sq]; exact (honi i).1) (hy'0 i)
  have hP : ∀ i, (W F a b c).toAffine.Nonsingular (α i) (β i) := fun i ↦
    ns_of_eq a b c (honi i).1 (honi i).2
  let m : Fin L → ℕ := fun i ↦ n * (z i).natAbs
  let s := (Finset.univ : Finset (Fin L)).filter fun i ↦ z i ≠ 0
  -- the relation `∑ mᵢ Qᵢ = 0`
  have hterm : ∀ i, (m i • (WeierstrassCurve.Affine.Point.some _ _ (hns i) : (W F a b c).toAffine.Point)) =
      (n : ℤ) • (z i • (WeierstrassCurve.Affine.Point.some _ _ (hP i) : (W F a b c).toAffine.Point)) := by
    intro i
    rw [smul_smul, ← natCast_zsmul]
    by_cases h0 : z i = 0
    · simp [m, h0]
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have hQ : (WeierstrassCurve.Affine.Point.some _ _ (hns i) : (W F a b c).toAffine.Point) = -WeierstrassCurve.Affine.Point.some _ _ (hP i) := by
        rw [WeierstrassCurve.Affine.Point.neg_some]
        simp only [WeierstrassCurve.Affine.Point.some.injEq, true_and, y', if_neg h0,
          Int.sign_eq_neg_one_of_neg hneg]
        rw [negY_W]; simp
      rw [hQ, zsmul_neg, ← neg_zsmul]
      congr 1
      simp only [m]
      push_cast
      rw [abs_of_neg hneg]; ring
    · have hQ : (WeierstrassCurve.Affine.Point.some _ _ (hns i) : (W F a b c).toAffine.Point) = WeierstrassCurve.Affine.Point.some _ _ (hP i) := by
        simp only [WeierstrassCurve.Affine.Point.some.injEq, true_and, y', if_neg h0,
          Int.sign_eq_one_of_pos hpos]
        simp
      rw [hQ]
      congr 1
      simp only [m]
      push_cast
      rw [abs_of_pos hpos]
  have hS : (pts.map fun q ↦ q.2.2 • ptF (d := d) a b c q).sum =
      ∑ i : Fin L, z i • (WeierstrassCurve.Affine.Point.some _ _ (hP i) : (W F a b c).toAffine.Point) := by
    rw [EllAlgo.sum_map_eq_fin]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [ptF]
    split_ifs with hc
    · rfl
    · exact absurd (honi i) hc
  have hsum : ∑ i ∈ s, m i • (WeierstrassCurve.Affine.Point.some _ _ (hns i) : (W F a b c).toAffine.Point) = 0 := by
    rw [Finset.sum_filter]
    have : ∀ i, (if z i ≠ 0 then m i • (WeierstrassCurve.Affine.Point.some _ _ (hns i) : (W F a b c).toAffine.Point) else 0) =
        (n : ℤ) • (z i • (WeierstrassCurve.Affine.Point.some _ _ (hP i) : (W F a b c).toAffine.Point)) := by
      intro i
      split_ifs with h
      · exact hterm i
      · push_neg at h; simp only [h, zero_zsmul, smul_zero]
    rw [Finset.sum_congr rfl fun i _ ↦ this i, ← Finset.smul_sum, ← hS, natCast_zsmul, hnS]
  obtain ⟨A, B, hAB, hA, hB, hloc⟩ := EllAlgo.exists_localW (a : F) (b : F) (c : F) (pF a b c)
    (toPoly_pF' a b c) (W F a b c) W_eq (squarefree_pF hsq) s α y' hns (fun i _ ↦ hy'0 i) m hsum
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
lemma partCert_ne_none {a b c : ℤ}
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (B : CPoly F) (L : ℕ) (hL : L ≠ 0) (pts : List (F × F × ℤ))
    (hon : ∀ q ∈ pts, q.2.1 * q.2.1 = q.1 ^ 3 + (a : F) * q.1 ^ 2 + (b : F) * q.1 + (c : F) ∧
      q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (n : ℕ) (hn : 1 ≤ n)
    (hnS : n • (pts.map fun q ↦ q.2.2 • ptF (d := d) a b c q).sum = 0) :
    partCert a b c B L pts n ≠ none := by
  obtain ⟨cs, hl, hrel, hne⟩ := exists_relationF hsq pts hon n hn hnS
  obtain ⟨w, hw, hwne⟩ := EllAlgo.exists_good_basis _ cs hl hrel hne
  rw [EllAlgo.length_ellCols] at hwne
  set pC := pF (d := d) a b c
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
  have hpC := toPoly_pF' (d := d) a b c
  have hp3 : (toPoly pC).natDegree = 3 := by rw [hpC]; compute_degree!
  have hon' : ∀ q ∈ pts, (toPoly pC).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0 := by
    intro q hq
    refine ⟨?_, (hon q hq).2⟩
    rw [hpC]; simp; linear_combination -(hon q hq).1
  have hcheck := EllAlgo.certCheck_ok_gen pC hp3 pts hon' hnd L hL n hn w'
    (CPoly.nullBasis_sound _ w' hw'mem) hw'ne B
  unfold partCert EllAlgo.ellSolve
  rw [hw']
  simp only
  rw [if_pos hcheck]
  simp

/-- **Completeness of `ellDecideF`**: on valid input it always answers. -/
theorem ellDecideF_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (B : CPoly F) (pts : List (F × F × F)) (p0 : ℕ) [NeZero p0]
    (hv : validF (d := d) a b c pts = true) : ellDecideF (d := d) a b c B pts p0 ≠ none := by
  have hv' := hv
  simp only [validF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv'
  obtain ⟨hon, hnd⟩ := hv'
  unfold ellDecideF
  rw [if_pos hv]
  simp only
  generalize hL1 : denL (pts.map fun q ↦ q.2.2.re) = L1
  generalize hL2 : denL (pts.map fun q ↦ q.2.2.im) = L2
  have hL10 : L1 ≠ 0 := by rw [← hL1]; exact denL_ne_zero _
  have hL20 : L2 ≠ 0 := by rw [← hL2]; exact denL_ne_zero _
  have honI : ∀ (L : ℕ) (f : F → ℚ), ∀ q ∈ intPts L f pts,
      q.2.1 * q.2.1 = q.1 ^ 3 + (a : F) * q.1 ^ 2 + (b : F) * q.1 + (c : F) ∧ q.2.1 ≠ 0 := by
    intro L f q hq; obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq; exact hon q0 hq0
  have hndI : ∀ (L : ℕ) (f : F → ℚ), ((intPts L f pts).map Prod.fst).Nodup := by
    intro L f; rw [intPts, List.map_map]; exact hnd
  generalize redCount p0 a b c + 1 = N
  split_ifs with htA htB
  · simp
  · simp
  have e1 : partCert a b c B L1 (intPts L1 (fun r ↦ r.re) pts)
      (ordF a b c (sumPtF a b c (intPts L1 (fun r ↦ r.re) pts)) N) ≠ none := by
    obtain ⟨hn1, hn⟩ := ordF_spec a b c (sumPtF_spec a b c _ (honI L1 _)) N (by simpa using htA)
    exact partCert_ne_none hsq B L1 hL10 _ (honI L1 _) (hndI L1 _) _ hn1 hn
  have e2 : partCert a b c [] L2 (intPts L2 (fun r ↦ r.im) pts)
      (ordF a b c (sumPtF a b c (intPts L2 (fun r ↦ r.im) pts)) N) ≠ none := by
    obtain ⟨hn1, hn⟩ := ordF_spec a b c (sumPtF_spec a b c _ (honI L2 _)) N (by simpa using htB)
    exact partCert_ne_none hsq [] L2 hL20 _ (honI L2 _) (hndI L2 _) _ hn1 hn
  obtain ⟨R1, h1⟩ := Option.ne_none_iff_exists'.mp e1
  obtain ⟨R2, h2⟩ := Option.ne_none_iff_exists'.mp e2
  rw [h1, h2]
  simp

/-! ### Soundness -/

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **A certificate removes the logarithmic part of one component.** -/
lemma partCert_spec (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (ι : F →+* Kc) (B : CPoly F) (L : ℕ)
    (pts : List (F × F × ℤ)) (n : ℕ) (R : CPoly F) (h : partCert a b c B L pts n = some R) :
    ∃ w : E, HasElementaryIntegralIn w ∧
      (evF ι x B + (pts.map fun q ↦ algebraMap Kc E (ι ((q.2.2 : F) / L * q.2.1)) /
        (x - algebraMap Kc E (ι q.1))).sum) / y = evF ι x R / y + w := by
  unfold partCert at h
  split at h
  swap
  · cases h
  rename_i AB hAB
  split_ifs at h with hchk
  simp only [Option.some.injEq] at h
  subst h
  set cc : F := 1 / ((n : F) * (L : F)) with hcc
  set G := EllAlgo.fracG B L pts with hGdef
  unfold EllAlgo.certCheck at hchk
  simp only [Bool.and_eq_true, Bool.not_eq_true', EllAlgo.certN, EllAlgo.certM] at hchk
  obtain ⟨⟨hN, hG⟩, hbeq⟩ := hchk
  have hN' : toPoly AB.1 ^ 2 - toPoly AB.2 ^ 2 * toPoly (pF a b c) ≠ 0 := by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hN; apply hN
    simp only [toPoly_sub, toPoly_mul]; linear_combination h0
  have hG' : toPoly G.2 ≠ 0 := by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hG; exact hG h0
  have hid := (beq_iff _ _).mp hbeq
  have h2 : toPoly ([2] : CPoly F) = 2 := by
    rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
  simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_smul, toPoly_deriv, h2] at hid
  have hidK := congrArg (Polynomial.map ι) hid
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
    map_C, Polynomial.map_ofNat, ← Polynomial.derivative_map] at hidK
  have hxa : ∀ z : F, x - algebraMap Kc E (ι z) ≠ 0 := fun z ↦ x_sub_const_ne hC x hx (ι z)
  have hpK : (toPoly (pF a b c)).map ι ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff ι.injective, toPoly_pF,
      Polynomial.map_ne_zero_iff (algebraMap ℚ F).injective, EllAlgo.toPoly_pOf]
    exact hsq.ne_zero
  have hyK : y ^ 2 = aeval x ((toPoly (pF a b c)).map ι) := by
    rw [hy]; exact (evF_pF ι x a b c).symm
  have hGK : (toPoly G.2).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hG'
  have hNK : ((toPoly AB.1).map ι) ^ 2 - ((toPoly AB.2).map ι) ^ 2 * (toPoly (pF a b c)).map ι ≠ 0 := by
    rw [← Polynomial.map_pow, ← Polynomial.map_pow, ← Polynomial.map_mul, ← Polynomial.map_sub]
    exact (Polynomial.map_ne_zero_iff ι.injective).mpr hN'
  obtain ⟨w, hw, key⟩ := ell_log_decompK hC x y hx _ hpK hyK ((toPoly G.1).map ι) ((toPoly G.2).map ι)
    ((toPoly AB.1).map ι) ((toPoly AB.2).map ι)
    ((toPoly (EllAlgo.certR (pF a b c) AB G cc)).map ι) (ι cc) hGK hNK (by linear_combination hidK)
  refine ⟨w, hw, ?_⟩
  obtain ⟨-, hfr⟩ := fracG_evF ι x hxa B L pts
  rw [← hGdef] at hfr
  rw [← hfr, div_div]
  exact key

set_option maxHeartbeats 3200000 in
/-- **Correctness of `ellDecideF`**: an answer `some b` is the truth (for any embedding
`ι : ℚ(√d) → Kc` of the coefficients into the constants). -/
theorem ellDecideF_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : F →+* Kc) (B : CPoly F) (pts : List (F × F × F)) (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp02 : p0 ≠ 2) (hgood : goodRedMod p0 a b c) (s : ZMod p0) (hs : s ^ 2 = d)
    (hs' : 2 * s ≠ 0) (ans : Bool) (h : ellDecideF (d := d) a b c B pts p0 = some ans) :
    ans = true ↔ HasElementaryIntegral ((evF ι x B + (pts.map fun q ↦
      algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum) / y) := by
  classical
  obtain ⟨φ⟩ := exists_embed (d := d) s hs hs'
  unfold ellDecideF at h
  split_ifs at h with hv
  simp only [validF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hon, hnd⟩ := hv
  simp only at h
  generalize hL1 : denL (pts.map fun q ↦ q.2.2.re) = L1 at h
  generalize hL2 : denL (pts.map fun q ↦ q.2.2.im) = L2 at h
  generalize hP1 : intPts L1 (fun r ↦ r.re) pts = P1 at h
  generalize hP2 : intPts L2 (fun r ↦ r.im) pts = P2 at h
  generalize hNdef : redCount p0 a b c + 1 = N at h
  have hN : Fintype.card (Option (RedPts p0 a b c)) ≤ N := by
    rw [← hNdef, Fintype.card_option, card_RedPts]
  have hL10 : L1 ≠ 0 := by rw [← hL1]; exact denL_ne_zero _
  have hL20 : L2 ≠ 0 := by rw [← hL2]; exact denL_ne_zero _
  have hd1 : ∀ q ∈ pts, q.2.2.re.den ∣ L1 := fun q hq ↦ by
    rw [← hL1]; exact den_dvd_denL (List.mem_map_of_mem (f := fun q : F × F × F ↦ q.2.2.re) hq)
  have hd2 : ∀ q ∈ pts, q.2.2.im.den ∣ L2 := fun q hq ↦ by
    rw [← hL2]; exact den_dvd_denL (List.mem_map_of_mem (f := fun q : F × F × F ↦ q.2.2.im) hq)
  have hon1 : ∀ q ∈ P1, q.2.1 * q.2.1 = q.1 ^ 3 + (a : F) * q.1 ^ 2 + (b : F) * q.1 + (c : F) ∧
      q.2.1 ≠ 0 := by
    intro q hq; rw [← hP1] at hq; obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq; exact hon q0 hq0
  have hon2 : ∀ q ∈ P2, q.2.1 * q.2.1 = q.1 ^ 3 + (a : F) * q.1 ^ 2 + (b : F) * q.1 + (c : F) ∧
      q.2.1 ≠ 0 := by
    intro q hq; rw [← hP2] at hq; obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq; exact hon q0 hq0
  have hrep1 := sumPtF_spec a b c P1 hon1
  have hrep2 := sumPtF_spec a b c P2 hon2
  -- indexing by `Fin pts.length`
  set n := pts.length
  have hP : ∀ i : Fin n, (W F a b c).toAffine.Nonsingular pts[i].1 pts[i].2.1 := fun i ↦
    ns_of_eq a b c (hon _ (List.getElem_mem i.2)).1 (hon _ (List.getElem_mem i.2)).2
  have hβ : ∀ i ∈ (Finset.univ : Finset (Fin n)), pts[i].2.1 ≠ 0 := fun i _ ↦
    (hon _ (List.getElem_mem i.2)).2
  have hinj : Set.InjOn (fun i : Fin n ↦ pts[i].1) ↑(Finset.univ : Finset (Fin n)) := by
    intro i _ j _ hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (hi := by rw [List.length_map]; exact i.2)
      (hj := by rw [List.length_map]; exact j.2)).mp (by simp only [List.getElem_map]; exact hij))
  have hint : (pts.map fun q ↦ algebraMap Kc E (ι (q.2.2 * q.2.1)) /
      (x - algebraMap Kc E (ι q.1))).sum = ∑ i : Fin n, algebraMap Kc E (ι (pts[i].2.2 * pts[i].2.1)) /
      (x - algebraMap Kc E (ι pts[i].1)) := EllAlgo.sum_map_eq_fin _ pts
  have hB : evF ι x B = aeval x ((toPoly B).map ι) := rfl
  -- the sums of points, reindexed
  have hsum : ∀ (L : ℕ) (f : F → ℚ), ((intPts L f pts).map fun q ↦ q.2.2 • ptF (d := d) a b c q).sum =
      ∑ i : Fin n, (f pts[i].2.2 * L).num •
        (WeierstrassCurve.Affine.Point.some _ _ (hP i) : (W F a b c).toAffine.Point) := by
    intro L f
    rw [intPts, List.map_map, EllAlgo.sum_map_eq_fin]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Function.comp_apply, ptF]
    split_ifs with hc
    · rfl
    · exact absurd (hon _ (List.getElem_mem i.2)) hc
  split_ifs at h with htA htB
  · -- `S₁` has infinite order
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.false_eq_true, false_iff]
    have hnt := (torsionTestF_spec a b c φ hp02 hgood hrep1 N hN).not.mp (by simp [htA])
    rw [← hP1, hsum] at hnt
    rw [hint, hB]
    have key := not_elem_of_nontorsionK hC hCall x y hx a b c hsq hy hgen ι ((toPoly B).map ι)
      (Finset.univ : Finset (Fin n))
      (fun i ↦ pts[i].1) (fun i ↦ pts[i].2.1) (fun i ↦ pts[i].2.2) hP hβ hinj
      (QuadraticAlgebra.reₗ (d : ℚ) 0) (fun i ↦ (pts[i].2.2.re * L1).num) L1 hL10
      (fun i _ ↦ (intPt_valQ _ _ (hd1 _ (List.getElem_mem i.2)) hL10).symm) hnt
    exact key
  · -- `S₂` has infinite order
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.false_eq_true, false_iff]
    have hnt := (torsionTestF_spec a b c φ hp02 hgood hrep2 N hN).not.mp (by simp [htB])
    rw [← hP2, hsum] at hnt
    rw [hint, hB]
    have key := not_elem_of_nontorsionK hC hCall x y hx a b c hsq hy hgen ι ((toPoly B).map ι)
      (Finset.univ : Finset (Fin n))
      (fun i ↦ pts[i].1) (fun i ↦ pts[i].2.1) (fun i ↦ pts[i].2.2) hP hβ hinj
      (QuadraticAlgebra.imₗ (d : ℚ) 0) (fun i ↦ (pts[i].2.2.im * L2).num) L2 hL20
      (fun i _ ↦ (intPt_valQ _ _ (hd2 _ (List.getElem_mem i.2)) hL20).symm) hnt
    exact key
  · -- the certificates
    split at h
    swap
    · cases h
    rename_i R1 R2 h1 h2
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨w1, hw1, e1⟩ := partCert_spec hC x y hx a b c hsq hy ι B L1 P1 _ R1 h1
    obtain ⟨w2, hw2, e2⟩ := partCert_spec hC x y hx a b c hsq hy ι [] L2 P2 _ R2 h2
    set σ := algebraMap Kc E (ι ⟨0, 1⟩)
    have hσ : σ′ = 0 := by simp only [σ]; rw [deriv_algebraMap, hC, map_zero]
    have hlist : ∀ l : List (F × F × F), (∀ q ∈ l, q.2.2.re.den ∣ L1 ∧ q.2.2.im.den ∣ L2) →
        (l.map fun q ↦ algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum =
        ((intPts L1 (fun r ↦ r.re) l).map fun q ↦ algebraMap Kc E (ι ((q.2.2 : F) / L1 * q.2.1)) /
          (x - algebraMap Kc E (ι q.1))).sum +
        σ * ((intPts L2 (fun r ↦ r.im) l).map fun q ↦ algebraMap Kc E (ι ((q.2.2 : F) / L2 * q.2.1)) /
          (x - algebraMap Kc E (ι q.1))).sum := by
      intro l hl
      induction l with
      | nil => simp [intPts]
      | cons q t ih =>
        simp only [intPts, List.map_cons, List.sum_cons] at ih ⊢
        rw [ih fun q' hq' ↦ hl q' (List.mem_cons_of_mem _ hq')]
        obtain ⟨h1q, h2q⟩ := hl q List.mem_cons_self
        rw [intPt_val _ _ h1q hL10, intPt_val _ _ h2q hL20]
        have hr : q.2.2 = ((q.2.2.re : ℚ) : F) + ⟨0, 1⟩ * ((q.2.2.im : ℚ) : F) := by
          ext <;> simp
        have e : algebraMap Kc E (ι (q.2.2 * q.2.1)) = algebraMap Kc E (ι ((q.2.2.re : ℚ) * q.2.1)) +
            σ * algebraMap Kc E (ι ((q.2.2.im : ℚ) * q.2.1)) := by
          conv_lhs => rw [hr]
          simp only [σ, map_add, map_mul]; ring
        rw [e]
        ring
    have hsplit : (evF ι x B + (pts.map fun q ↦ algebraMap Kc E (ι (q.2.2 * q.2.1)) /
        (x - algebraMap Kc E (ι q.1))).sum) / y =
        evF ι x (add R1 (smul ⟨0, 1⟩ R2)) / y + (w1 + σ * w2) := by
      rw [hlist pts fun q hq ↦ ⟨hd1 q hq, hd2 q hq⟩, evF_add, evF_smul]
      have he : evF ι x ([] : CPoly F) = 0 := by simp [evF, CPoly.toPoly]
      rw [he, zero_add] at e2
      have e1' := e1
      rw [← hP1] at e1'
      rw [← hP2] at e2
      calc _ = (evF ι x B + ((intPts L1 (fun r ↦ r.re) pts).map fun q ↦
              algebraMap Kc E (ι ((q.2.2 : F) / L1 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum) / y +
            σ * (((intPts L2 (fun r ↦ r.im) pts).map fun q ↦
              algebraMap Kc E (ι ((q.2.2 : F) / L2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum / y) := by
            ring
        _ = _ := by rw [e1', e2]; ring
    rw [hsplit]
    have hpm : toPoly (pF (d := d) a b c) = (toPoly (EllAlgo.pOf a b c)).map (algebraMap ℚ F) :=
      toPoly_pF a b c
    have hdeg3 : (toPoly (EllAlgo.pOf a b c)).natDegree = 3 := by
      rw [EllAlgo.toPoly_pOf]; compute_degree!
    have hdec := hyp_decidesF hC hCall ι x y hx (EllAlgo.pOf a b c)
      (by rw [EllAlgo.toPoly_pOf]; exact hsq) (by rw [hdeg3]; decide)
      (by rw [EllAlgo.toPoly_pOf, hy]; simp) hgen (pF a b c) hpm (add R1 (smul ⟨0, 1⟩ R2))
    rw [← hdec]
    have hw := hw1.add (hw2.const_mul σ hσ)
    constructor
    · intro h0; exact h0.add_in hw
    · intro h0
      have := h0.sub_in hw
      rwa [add_sub_cancel_right] at this

/-- **`ellDecideF` decides**: on valid data it answers, and the answer is correct. -/
theorem ellDecideF_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : F →+* Kc) (B : CPoly F) (pts : List (F × F × F)) (hv : validF (d := d) a b c pts = true)
    (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp02 : p0 ≠ 2) (hgood : goodRedMod p0 a b c) (s : ZMod p0) (hs : s ^ 2 = d)
    (hs' : 2 * s ≠ 0) :
    ∃ ans, ellDecideF (d := d) a b c B pts p0 = some ans ∧
      (ans = true ↔ HasElementaryIntegral ((evF ι x B + (pts.map fun q ↦
        algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum) / y)) := by
  obtain ⟨ans, h⟩ := Option.ne_none_iff_exists'.mp (ellDecideF_ne_none a b c hsq B pts p0 hv)
  exact ⟨ans, h, ellDecideF_spec hC hCall x y hx a b c hsq hy hgen ι B pts p0 hp02 hgood s hs hs'
    ans h⟩

end EllQuad
