import RischTragerBronstein.Torsion.DecideLogT

/-!
# Möbius transformations of general curves

For a curve `F(x, y) = 0` and `c`, the substitution `t = 1/(x − c)`, `w = y tᵏ` gives the curve
`G(t, w) = t^M F(c + 1/t, w/tᵏ) = 0` (`invP (shiftP F c) k M`). The places above `x = ∞` become the
places above `t = 0`.

* `ev_invP`, `ev_shiftP`: evaluation of the inverted and shifted polynomials;
* `mobCurve`: the transformed curve as a `CurveData` on the same field.
-/

open Polynomial IntermediateField

namespace Curves

section Poly

variable {R : Type*} [CommRing R]

/-- `Σᵢ reflect_{M − k i}(Wᵢ) Yⁱ`. -/
noncomputable def invP (W : R[X][X]) (k M : ℕ) : R[X][X] :=
  ∑ i ∈ Finset.range (W.natDegree + 1), Polynomial.C (reflect (M - k * i) (W.coeff i)) * X ^ i

/-- `W(x + c, Y)`. -/
noncomputable def shiftP (W : R[X][X]) (c : R) : R[X][X] :=
  W.map (compRingHom (X + Polynomial.C c))

lemma coeff_invP (W : R[X][X]) (k M i : ℕ) :
    (invP W k M).coeff i = reflect (M - k * i) (W.coeff i) := by
  rw [invP, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hi : i < W.natDegree + 1
  · rw [Finset.sum_eq_single i (fun j _ hj ↦ if_neg (Ne.symm hj))
      (fun h ↦ absurd (Finset.mem_range.mpr hi) h), if_pos rfl]
  · rw [Finset.sum_eq_zero fun j hj ↦ if_neg (by have := Finset.mem_range.mp hj; omega),
      coeff_eq_zero_of_natDegree_lt (by omega), reflect_zero]

lemma natDegree_invP_le (W : R[X][X]) (k M : ℕ) : (invP W k M).natDegree ≤ W.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
    rw [coeff_invP, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hi), reflect_zero]

lemma coeff_shiftP (W : R[X][X]) (c : R) (i : ℕ) :
    (shiftP W c).coeff i = (W.coeff i).comp (X + Polynomial.C c) := by
  rw [shiftP, coeff_map, coe_compRingHom_apply]

lemma natDegree_shiftP_le (W : R[X][X]) (c : R) : (shiftP W c).natDegree ≤ W.natDegree :=
  natDegree_map_le

end Poly

section Eval

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- Evaluation of `Q(x, y)` at `(a, b)`. -/
noncomputable def ev (Q : K[X][X]) (a b : E) : E := (Q.map (aeval a).toRingHom).eval b

lemma ev_eq_sum (Q : K[X][X]) (a b : E) :
    ev Q a b = ∑ i ∈ Finset.range (Q.natDegree + 1), aeval a (Q.coeff i) * b ^ i := by
  rw [ev, eval_map, eval₂_eq_sum_range]
  rfl

lemma ev_shiftP (Q : K[X][X]) (c : K) (a b : E) :
    ev (shiftP Q c) a b = ev Q (a + algebraMap K E c) b := by
  rw [ev, ev, shiftP, Polynomial.map_map]
  congr 2
  exact RingHom.ext fun P ↦ by
    simp [aeval_comp, add_comm]

lemma aeval_reflect (P : K[X]) (N : ℕ) (hP : P.natDegree ≤ N) (t : E) (ht : t ≠ 0) :
    aeval t (reflect N P) = t ^ N * aeval (1 / t) P := by
  haveI : Invertible (1 / t) := invertibleOfNonzero (one_div_ne_zero ht)
  have h := eval₂_reflect_mul_pow (algebraMap K E) (1 / t) N P hP
  rw [invOf_eq_inv, one_div, inv_inv] at h
  rw [aeval_def, aeval_def, one_div, ← h]
  have h1 : t ^ N * t⁻¹ ^ N = 1 := by rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero N ht)]
  rw [mul_comm (eval₂ _ _ _), ← mul_assoc, h1, one_mul]

/-- **Evaluation of the inverted polynomial.** -/
lemma ev_invP (Q : K[X][X]) (k M : ℕ) (hQ : ∀ i ≤ Q.natDegree, (Q.coeff i).natDegree + k * i ≤ M)
    (t w : E)
    (ht : t ≠ 0) : ev (invP Q k M) t w = t ^ M * ev Q (1 / t) (w / t ^ k) := by
  rw [ev_eq_sum, ev_eq_sum, Finset.mul_sum]
  have hle := natDegree_invP_le Q k M
  rw [Finset.sum_subset (Finset.range_subset_range.mpr (by omega : (invP Q k M).natDegree + 1 ≤
    Q.natDegree + 1)) (fun i _ hi ↦ by
      rw [coeff_eq_zero_of_natDegree_lt (by simp at hi; omega), map_zero, zero_mul])]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ Q.natDegree := by have := Finset.mem_range.mp hi; omega
  rw [coeff_invP, aeval_reflect _ _ (by have := hQ i hi'; omega) t ht, div_pow, ← pow_mul]
  have hMi : M = (M - k * i) + k * i := by have := hQ i hi'; omega
  conv_rhs => rw [hMi, pow_add]
  field_simp

lemma shiftP_shiftP (Q : K[X][X]) (c : K) : shiftP (shiftP Q (-c)) c = Q := by
  ext1 i
  rw [coeff_shiftP, coeff_shiftP, comp_assoc,
    show ((X : K[X]) + Polynomial.C (-c)).comp (X + Polynomial.C c) = X by
      rw [add_comp, X_comp, C_comp, map_neg]; ring, comp_X]

lemma invP_eq_zero {Q : K[X][X]} {k M : ℕ} (h : invP Q k M = 0) : Q = 0 := by
  ext1 i
  have := congrArg (fun P ↦ P.coeff i) h
  simp only [coeff_invP, Polynomial.coeff_zero] at this
  rw [Polynomial.coeff_zero]
  exact (reflect_eq_zero_iff).mp this

/-- A uniform degree bound for `invP`. -/
lemma exists_invBound (Q : K[X][X]) (k : ℕ) :
    ∃ M, ∀ i ≤ Q.natDegree, (Q.coeff i).natDegree + k * i ≤ M := by
  refine ⟨(Finset.range (Q.natDegree + 1)).sup (fun i ↦ (Q.coeff i).natDegree) + k * Q.natDegree,
    fun i hi ↦ ?_⟩
  have h1 : (Q.coeff i).natDegree ≤
      (Finset.range (Q.natDegree + 1)).sup (fun i ↦ (Q.coeff i).natDegree) :=
    Finset.le_sup (f := fun i ↦ (Q.coeff i).natDegree) (Finset.mem_range.mpr (by omega))
  have h2 : k * i ≤ k * Q.natDegree := Nat.mul_le_mul_left k hi
  omega

end Eval

section Curve

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

lemma x_sub_ne (S : CurveData K L) (c : K) : S.x - algebraMap K L c ≠ 0 := fun h ↦ by
  apply S.htr
  rw [sub_eq_zero] at h
  rw [h]; exact isAlgebraic_algebraMap c

/-- **The Möbius-transformed curve** `t = 1/(x − c)`, `w = y tᵏ`. -/
noncomputable def mobCurve (S : CurveData K L) (c : K) (k M : ℕ)
    (hM : ∀ i ≤ (shiftP S.F c).natDegree, ((shiftP S.F c).coeff i).natDegree + k * i ≤ M)
    (hGm : (invP (shiftP S.F c) k M).Monic)
    (hGn : (invP (shiftP S.F c) k M).natDegree = S.F.natDegree) : CurveData K L where
  x := 1 / (S.x - algebraMap K L c)
  y := S.y * (1 / (S.x - algebraMap K L c)) ^ k
  F := invP (shiftP S.F c) k M
  htr := by
    intro halg
    apply S.htr
    have h1 : IsAlgebraic K (S.x - algebraMap K L c) := by
      rw [← IsAlgebraic.inv_iff]; simpa using halg
    have h2 := (isAlgebraic_iff_isIntegral.mp h1).add (isIntegral_algebraMap (x := c))
    rw [sub_add_cancel] at h2
    exact isAlgebraic_iff_isIntegral.mpr h2
  monic := hGm
  irr := by
    intro G hG hGy
    obtain ⟨M1, hM1⟩ := exists_invBound G k
    have hxc := x_sub_ne S c
    set H := shiftP (invP G k M1) (-c) with hH
    have hHy : ev H S.x S.y = 0 := by
      rw [hH, ev_shiftP, map_neg, ← sub_eq_add_neg, ev_invP G k M1 hM1 _ _ hxc]
      have hw : S.y / (S.x - algebraMap K L c) ^ k = S.y * (1 / (S.x - algebraMap K L c)) ^ k := by
        rw [div_pow, one_pow, mul_one_div]
      have : ev G (1 / (S.x - algebraMap K L c)) (S.y * (1 / (S.x - algebraMap K L c)) ^ k) = 0 :=
        hGy
      rw [hw, this, mul_zero]
    have hHd : H.natDegree < S.F.natDegree :=
      lt_of_le_of_lt ((natDegree_shiftP_le _ _).trans (natDegree_invP_le _ _ _)) (by rwa [hGn] at hG)
    have h0 := S.irr H hHd hHy
    have h1 : invP G k M1 = 0 := by rw [← shiftP_shiftP (invP G k M1) c, ← hH, h0]; simp [shiftP]
    exact invP_eq_zero h1
  root := by
    have hxc := x_sub_ne S c
    show ev (invP (shiftP S.F c) k M) _ _ = 0
    rw [ev_invP _ k M hM _ _ (one_div_ne_zero hxc), ev_shiftP]
    have e1 : 1 / (1 / (S.x - algebraMap K L c)) + algebraMap K L c = S.x := by
      rw [one_div_one_div, sub_add_cancel]
    have e2 : S.y * (1 / (S.x - algebraMap K L c)) ^ k / (1 / (S.x - algebraMap K L c)) ^ k =
        S.y := mul_div_cancel_right₀ _ (pow_ne_zero _ (one_div_ne_zero hxc))
    rw [e1, e2]
    have : ev S.F S.x S.y = 0 := S.root
    rw [this, mul_zero]

end Curve

section Maps

variable {R S : Type*} [CommRing R] [CommRing S]

lemma invP_map (φ : R →+* S) (W : R[X][X]) (k M : ℕ) :
    (invP W k M).map (mapRingHom φ) = invP (W.map (mapRingHom φ)) k M := by
  ext1 i
  rw [coeff_map, coeff_invP, coeff_invP, coeff_map, coe_mapRingHom, reflect_map]

lemma shiftP_map (φ : R →+* S) (W : R[X][X]) (c : R) :
    (shiftP W c).map (mapRingHom φ) = shiftP (W.map (mapRingHom φ)) (φ c) := by
  ext1 i
  rw [coeff_map, coeff_shiftP, coeff_shiftP, coeff_map, coe_mapRingHom, Polynomial.map_comp]
  simp

end Maps

section CPolyMob

open CPoly Sup

variable {F : Type*} [Field F] [DecidableEq F]

/-- `W(x + e, Y)` on lists. -/
def shiftB (W : BPoly F) (e : F) : BPoly F := W.map fun c ↦ compC c (shiftC e 1)

/-- Dropping the trailing zero coefficients (in `Y`) of a bivariate list. -/
def stripB (W : BPoly F) : BPoly F := (W.reverse.dropWhile fun P ↦ isZero P).reverse

lemma toB_append (W V : BPoly F) : toB (W ++ V) = toB W + X ^ W.length * toB V := by
  induction W with
  | nil => simp
  | cons c W ih =>
    rw [List.cons_append, toB_cons, toB_cons, ih, List.length_cons, pow_succ]
    ring

lemma toB_eq_zero_of_isZero {V : BPoly F} (h : ∀ P ∈ V, isZero P = true) : toB V = 0 := by
  induction V with
  | nil => simp
  | cons c V ih =>
    rw [toB_cons, (isZero_iff c).mp (h c List.mem_cons_self), map_zero, zero_add,
      ih fun P hP ↦ h P (List.mem_cons_of_mem _ hP), mul_zero]

/-- **Stripping keeps the polynomial.** -/
lemma toB_stripB (W : BPoly F) : toB (stripB W) = toB W := by
  conv_rhs => rw [← List.reverse_reverse W, ← List.takeWhile_append_dropWhile
    (p := fun P ↦ isZero P) (l := W.reverse), List.reverse_append]
  rw [toB_append, stripB, toB_eq_zero_of_isZero (V := (W.reverse.takeWhile fun P ↦ isZero P).reverse)
    (fun P hP ↦ by
      have := List.mem_takeWhile_imp (List.mem_reverse.mp hP)
      simpa using this), mul_zero, add_zero]

lemma toB_map_trim (W : BPoly F) : toB (W.map trim) = toB W := by
  induction W with
  | nil => rfl
  | cons c W ih => rw [List.map_cons, toB_cons, toB_cons, ih, toPoly_trim]

/-- The transformed numerator on lists: `−W(e + 1/t, Y)` inverted at `D_A`, with trimmed
coefficients and without trailing zero coefficients. -/
def mobA (A : BPoly F) (e : F) (k0 DA : ℕ) : BPoly F :=
  stripB ((smulB [-1] (invB (shiftB A e) k0 DA)).map trim)

lemma toB_mobA (A : BPoly F) (e : F) (k0 DA : ℕ) :
    toB (mobA A e k0 DA) = toB (smulB [-1] (invB (shiftB A e) k0 DA)) := by
  rw [mobA, toB_stripB, toB_map_trim]

lemma toB_shiftB (W : BPoly F) (e : F) : toB (shiftB W e) = shiftP (toB W) e := by
  ext1 i
  rw [coeff_toB, coeff_shiftP, coeff_toB]
  have h : (shiftB W e).getD i [] = compC (W.getD i []) (shiftC e 1) := by
    by_cases hi : i < W.length
    · rw [shiftB, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
        List.getD_eq_getElem _ _ hi]
    · rw [shiftB, List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by omega)]
      rfl
  rw [h, toPoly_compC, toPoly_shiftC, pow_one, add_comm]

lemma invBAux_getD (k M : ℕ) : ∀ (W : BPoly F) (j i : ℕ),
    (invBAux k M j W).getD i [] = if i < W.length then reflectC (M - k * (j + i)) (W.getD i [])
      else []
  | [], j, i => by simp [invBAux]
  | c :: W, j, 0 => by simp [invBAux]
  | c :: W, j, i + 1 => by
    rw [invBAux, List.getD_cons_succ, invBAux_getD k M W (j + 1) i, List.getD_cons_succ]
    simp only [List.length_cons, Nat.add_lt_add_iff_right]
    congr 3
    ring

lemma toB_invB (W : BPoly F) (k M : ℕ) (hW : InvOK k M 0 W) :
    toB (invB W k M) = invP (toB W) k M := by
  ext1 i
  rw [coeff_toB, coeff_invP, coeff_toB, invB, invBAux_getD, zero_add]
  split_ifs with hi
  · rw [toPoly_reflectC _ _ (by have := hW i hi; rw [zero_add] at this; omega)]
  · rw [List.getD_eq_default _ _ (by omega), toPoly_nil, reflect_zero]

/-- `InvOK` gives the degree bounds of `invP`. -/
lemma invBound_of_invOK (W : BPoly F) (k D : ℕ) (hW : InvOK k D 0 W) :
    ∀ i ≤ (toB W).natDegree, ((toB W).coeff i).natDegree + k * i ≤ D := by
  intro i hi
  by_cases h0 : toB W = 0
  · rw [h0, natDegree_zero] at hi
    rw [show i = 0 by omega, h0, Polynomial.coeff_zero, natDegree_zero]; simp
  set top := (toB W).natDegree with htop
  have htc : (toB W).coeff top ≠ 0 := by rw [htop, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr h0
  have hlen : ∀ j, (toB W).coeff j ≠ 0 → j < W.length ∧ 1 ≤ (W.getD j []).length := by
    intro j hj
    rw [coeff_toB] at hj
    by_cases hjl : j < W.length
    · refine ⟨hjl, ?_⟩
      by_contra h1
      have h2 : (W.getD j []).length = 0 := by omega
      rw [List.length_eq_zero_iff.mp h2] at hj
      exact hj toPoly_nil
    · rw [List.getD_eq_default _ _ (by omega)] at hj; exact absurd toPoly_nil hj
  obtain ⟨htl, htl1⟩ := hlen top htc
  have hktop : k * top ≤ D := by have := hW top htl; rw [zero_add] at this; omega
  by_cases hci : (toB W).coeff i = 0
  · rw [hci, natDegree_zero, zero_add]
    exact le_trans (Nat.mul_le_mul_left k hi) hktop
  · obtain ⟨hil, hil1⟩ := hlen i hci
    have h1 := hW i hil
    rw [zero_add] at h1
    have h2 := natDegree_toPoly_le_length (W.getD i [])
    rw [coeff_toB]
    omega

end CPolyMob

section MobCheck

open CPoly Sup

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- **The Möbius check**: `P'` is the transform of `P` by `t = 1/(x − e)`, `w = y tᵏ`
(`f dx = f' dt` with `f' = −f / t²`). -/
def mobCheck (P P' : CurveProb F) (e : F) (k0 DA : ℕ) : Bool :=
  decide (P'.n = P.n) &&
  decide (P'.Fc = invB (shiftB P.Fc e) k0 (k0 * P.n)) && invOKb k0 (k0 * P.n) (shiftB P.Fc e) &&
  decide (P'.A = mobA P.A e k0 DA) && invOKb k0 DA (shiftB P.A e) &&
  decide ((compC P.D (shiftC e 1)).length ≤ P.D.length - 1 + 1) &&
  decide (P.D.length - 1 ≤ DA + 2) &&
  decide (P'.D = mul (reflectC (P.D.length - 1) (compC P.D (shiftC e 1)))
    (xPowC (DA + 2 - (P.D.length - 1))))

omit [CharZero F] [EllQuad.QCoords F] in
lemma valid_of_decideLog {P : CurveProb F} [CharZero F] [EllQuad.QCoords F] {ws : List (LogWit F)}
    {b : Bool} (h : P.decideLog ws = some b) : P.valid = true := by
  unfold CurveProb.decideLog at h
  by_contra hv
  rw [if_neg hv] at h
  exact absurd h (by simp)

lemma valid_of_decideLogT {redAt : (p : ℕ) → Option (RedFns p F)} {P : CurveProb F}
    {ws : List (LogWit F)} {tws : List (TorsWit F)} {b : Bool}
    (h : decideLogT redAt P ws tws = some b) : P.valid = true := by
  unfold decideLogT at h
  split at h
  · rename_i b' hb'
    exact valid_of_decideLog hb'
  · split_ifs at h with hany
    obtain ⟨tw, -, htw⟩ := List.any_eq_true.mp hany
    simp only [torsOK, Bool.and_eq_true] at htw
    exact htw.1.1.1.1.1.1

end MobCheck

section MobMain

open CPoly Sup Differential

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

set_option maxHeartbeats 4000000 in
/-- **Deciding after a Möbius transformation**: if `P'` is the transform of `P` at `e`
(`mobCheck`), every answer of `decideLogT` for `P'` is the answer for `P`. -/
theorem decideLogT_mob_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (P P' : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι)) (e : F)
    (k0 DA : ℕ) (hmob : mobCheck P P' e k0 DA = true) (ws : List (LogWit F))
    (tws : List (TorsWit F)) (b : Bool) (h : decideLogT redAt P' ws tws = some b) :
    HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true := by
  classical
  simp only [mobCheck, Bool.and_eq_true, decide_eq_true_eq] at hmob
  obtain ⟨⟨⟨⟨⟨⟨⟨hn', hFc'⟩, hokF⟩, hA'⟩, hokA⟩, hsDl⟩, hdD⟩, hD'⟩ := hmob
  have hV' := P'.valid_spec (valid_of_decideLogT h)
  set c : Kc := ι e with hc
  -- the transformed curve
  have hFs : shiftP S.F c = (shiftP (toB P.Fc) e).map (mapRingHom ι) := by rw [hSF, shiftP_map]
  have hInvF : InvOK k0 (k0 * P.n) 0 (shiftB P.Fc e) := invOKb_spec hokF
  have hG : invP (shiftP S.F c) k0 (k0 * P.n) = (toB P'.Fc).map (mapRingHom ι) := by
    rw [hFs, ← invP_map, ← toB_shiftB, ← toB_invB _ _ _ hInvF, ← hFc']
  have hGdeg : (invP (shiftP S.F c) k0 (k0 * P.n)).natDegree = P.n := by
    rw [hG, hV'.mon.natDegree_map, hV'.deg, hn']
  have hGm : (invP (shiftP S.F c) k0 (k0 * P.n)).Monic := by rw [hG]; exact hV'.mon.map _
  have hnP : S.F.natDegree = P.n := by
    refine le_antisymm ?_ (by
      have := (natDegree_invP_le (shiftP S.F c) k0 (k0 * P.n)).trans (natDegree_shiftP_le _ _)
      rwa [hGdeg] at this)
    have hcoef : (invP (shiftP S.F c) k0 (k0 * P.n)).coeff S.F.natDegree ≠ 0 := by
      rw [coeff_invP, coeff_shiftP, S.monic.coeff_natDegree, one_comp]
      intro h0
      exact one_ne_zero ((reflect_eq_zero_iff).mp h0)
    have := le_natDegree_of_ne_zero hcoef
    rwa [hGdeg] at this
  have hM : ∀ i ≤ (shiftP S.F c).natDegree,
      ((shiftP S.F c).coeff i).natDegree + k0 * i ≤ k0 * P.n := by
    intro i hi
    have hb := invBound_of_invOK _ _ _ hInvF i (by
      rw [toB_shiftB]
      refine le_trans hi ?_
      rw [hFs]; exact natDegree_map_le)
    rw [hFs, coeff_map, ← toB_shiftB, coe_mapRingHom]
    have h2 := natDegree_map_le (f := ι) (p := (toB (shiftB P.Fc e)).coeff i)
    omega
  set S' := mobCurve S c k0 (k0 * P.n) hM hGm (by rw [hGdeg, hnP]) with hS'
  have hS'F : S'.F = (toB P'.Fc).map (mapRingHom ι) := hG
  -- the variables and the rescaled derivation
  set t : E := 1 / (S.x - algebraMap Kc E c) with ht
  set w : E := S.y * t ^ k0 with hw
  have hconstE : ∀ r : Kc, (algebraMap Kc E r)′ = 0 := fun r ↦ by
    rw [deriv_algebraMap, hC, map_zero]
  have hxc : S.x - algebraMap Kc E c ≠ 0 := x_sub_ne S c
  have ht0 : t ≠ 0 := one_div_ne_zero hxc
  have hxt : 1 / t + algebraMap Kc E c = S.x := by rw [ht, one_div_one_div, sub_add_cancel]
  have hwt : w / t ^ k0 = S.y := by rw [hw]; exact mul_div_cancel_right₀ _ (pow_ne_zero _ ht0)
  have ht' : t′ = -t ^ 2 := by
    rw [ht, Derivation.leibniz_div, map_sub, hx, hconstE]
    simp only [Derivation.map_one_eq_zero, smul_eq_mul, mul_zero, sub_zero, mul_one, zero_sub]
    field_simp
  set τ : E := -t ^ 2 with hτ
  have hτ0 : τ ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ ht0)
  let d0 : Derivation ℤ E E := Differential.deriv
  have hd0 : ∀ z : E, d0 z = z′ := fun _ ↦ rfl
  have hconst : ∀ r : Kc, d0 (algebraMap Kc E r) = 0 := fun r ↦ hconstE r
  let D' : Differential E := rescale ⟨d0⟩ (1 / τ)
  have hT' : D'.deriv S'.x = 1 := by
    show 1 / τ * d0 t = 1
    rw [hd0, ht']; exact one_div_mul_cancel hτ0
  have hDA' : @DifferentialAlgebra Kc E _ _ _ _ D' :=
    @DifferentialAlgebra.mk Kc E _ _ _ _ D' (fun r ↦ by
      show 1 / τ * d0 (algebraMap Kc E r) = algebraMap Kc E r′
      rw [hconst, hC, map_zero, mul_zero])
  have hgen' : ∀ z : E, z ∈ Kc⟮S'.x⟯⟮S'.y⟯ := by
    intro z
    have hz := hgen z
    rw [← IntermediateField.mem_restrictScalars Kc, adjoin_simple_adjoin_simple] at hz ⊢
    refine (adjoin_le_iff.mpr ?_) hz
    have htm : t ∈ Kc⟮S'.x, S'.y⟯ := subset_adjoin _ _ (Set.mem_insert _ _)
    have hwm : w ∈ Kc⟮S'.x, S'.y⟯ := subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
    intro v hv
    rcases hv with hv | hv
    · rw [hv, ← hxt]
      exact add_mem (div_mem (one_mem _) htm) (IntermediateField.algebraMap_mem _ _)
    · rw [Set.mem_singleton_iff] at hv
      rw [hv, ← hwt]
      exact div_mem hwm (pow_mem htm _)
  have key := @decideLogT_spec Kc E _ _ _ _ D' hDA' _ _ _ F _ _ _ _ hC S' hT' hgen' redAt hred P' ι
    hS'F ws tws b h
  -- the transformed integrand
  have hInvA : InvOK k0 DA 0 (shiftB P.A e) := invOKb_spec hokA
  have hAm : (toB P'.A).map (mapRingHom ι) = Polynomial.C (Polynomial.C (-1)) *
      invP (shiftP ((toB P.A).map (mapRingHom ι)) c) k0 DA := by
    rw [hA', toB_mobA, toB_smulB, Polynomial.map_mul, toB_invB _ _ _ hInvA, invP_map, toB_shiftB,
      shiftP_map]
    simp [CPoly.toPoly]
    rfl
  have hAb : ∀ i ≤ (shiftP ((toB P.A).map (mapRingHom ι)) c).natDegree,
      ((shiftP ((toB P.A).map (mapRingHom ι)) c).coeff i).natDegree + k0 * i ≤ DA := by
    intro i hi
    have hsm : shiftP ((toB P.A).map (mapRingHom ι)) c = (toB (shiftB P.A e)).map (mapRingHom ι) := by
      rw [toB_shiftB, shiftP_map]
    rw [hsm] at hi ⊢
    have hb := invBound_of_invOK _ _ _ hInvA i (le_trans hi natDegree_map_le)
    rw [coeff_map, coe_mapRingHom]
    have h2 := natDegree_map_le (f := ι) (p := (toB (shiftB P.A e)).coeff i)
    omega
  have hevA : S'.evXY ((toB P'.A).map (mapRingHom ι)) =
      -(t ^ DA * S.evXY ((toB P.A).map (mapRingHom ι))) := by
    show ev _ t w = _
    rw [hAm]
    have e1 : ev (Polynomial.C (Polynomial.C (-1)) *
        invP (shiftP ((toB P.A).map (mapRingHom ι)) c) k0 DA) t w =
        -ev (invP (shiftP ((toB P.A).map (mapRingHom ι)) c) k0 DA) t w := by
      simp [ev, Polynomial.map_mul]
    rw [e1, ev_invP _ k0 DA hAb t w ht0, ev_shiftP, hxt, hwt]
    rfl
  set dD := P.D.length - 1 with hdDdef
  have hevD : aeval S'.x ((toPoly P'.D).map ι) =
      t ^ dD * aeval S.x ((toPoly P.D).map ι) * t ^ (DA + 2 - dD) := by
    show aeval t _ = _
    rw [hD', toPoly_mul, toPoly_reflectC _ _ hsDl, toPoly_xPowC, toPoly_compC, toPoly_shiftC,
      Polynomial.map_mul, map_mul, Polynomial.map_pow, map_X, map_pow, aeval_X, ← reflect_map,
      aeval_reflect _ _ _ t ht0]
    · rw [Polynomial.map_comp, aeval_comp]
      congr 2
      simp [← hxt, add_comm]
      rfl
    · refine natDegree_map_le.trans ?_
      rw [← toPoly_shiftC, ← toPoly_compC]
      refine (natDegree_toPoly_le_length _).trans ?_
      omega
  have hid : (S'.fE P' ι : E) = 1 / τ * (S.fE P ι : E) := by
    show S'.evXY _ / aeval S'.x _ = 1 / τ * (S.evXY _ / aeval S.x _)
    rw [hevA, hevD, hτ]
    have hm : dD + (DA + 2 - dD) = DA + 2 := by omega
    by_cases hDx : aeval S.x ((toPoly P.D).map ι) = 0
    · rw [hDx]; simp
    · rw [show t ^ dD * aeval S.x ((toPoly P.D).map ι) * t ^ (DA + 2 - dD) =
        aeval S.x ((toPoly P.D).map ι) * t ^ (dD + (DA + 2 - dD)) by ring, hm, pow_add]
      field_simp
  rw [← key, hid]
  exact (hasElementaryIntegral_rescale_iff ⟨d0⟩ (1 / τ) _ (one_div_ne_zero hτ0)).symm

end MobMain

end Curves
