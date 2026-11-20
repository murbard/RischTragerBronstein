import RischTragerBronstein.Computable.MixNComplete
import RischTragerBronstein.Computable.MixNHexp
import RischTragerBronstein.Computable.PrimNComplete
import RischTragerBronstein.RDE.ExponentialTwoProper

/-!
# Mixed towers: completeness of parametric limited integration

Ported from `PrimNComplete` (base `Kc(x)`, primitive levels), plus the exponential levels:
a solution `y` of `y′ + ∑ cᵢ wᵢ = A` in `F m (tₘ)`, `tₘ′ = bₘ tₘ`, differs from the Hermite
part by a Laurent polynomial (`deriv_eq_laurent_add_two_proper_exp`), whose coefficients solve the
Risch equations `Yₑ′ + e bₘ Yₑ = Λₑ` (`e ≠ 0`, found by `rdeM`, complete) and the limited problem
for `e = 0` one level down.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.MixN

open Tower.PrimN

namespace MixTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : List Kind} (T : MixTower Kc E ks)

/-- `∑ cᵢ wᵢ` in `E`, constants `cᵢ ∈ Kc`. -/
noncomputable def zsumK (c : List Kc) (W : List (Code 1)) : E :=
  (List.zipWith (fun (c : Kc) w ↦ algebraMap Kc E c * evx Kc T.x w) c W).sum

lemma coe_zipWithK_sum {m : ℕ} (h : T.Tr m) :
    ∀ (c : List Kc) (W : List (Code 1)),
      (((List.zipWith (fun (c : Kc) w ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem (lift m w))
        c W).sum : T.F m) : E) = T.zsumK c W
  | [], W => by cases W <;> rfl
  | _ :: _, [] => rfl
  | c :: cs, w :: W => by
    have := coe_zipWithK_sum h cs W
    simp only [zsumK] at this ⊢
    simp only [List.zipWith_cons_cons, List.sum_cons, IntermediateField.coe_add,
      IntermediateField.coe_mul, T.sem_lift_code, this]
    rfl

/-- A solution of the limited-integration problem at level `m`, with constants in `Kc`. -/
def LimSol (m : ℕ) (h : T.Tr m) (A : Code (m + 1)) (W : List (Code 1)) : Prop :=
  ∃ y ∈ T.F m, ∃ c : List Kc, c.length = W.length ∧
    y′ + T.zsumK c W = (((T.MP m h).sem A : T.F m) : E)

lemma deriv_algebraMap_Kc {m : ℕ} (κ : Kc) : (algebraMap Kc (T.F m) κ)′ = 0 :=
  Subtype.ext (by
    rw [coe_deriv]
    change (algebraMap Kc E κ)′ = 0
    rw [deriv_algebraMap, T.hC, map_zero])

lemma const_F {m : ℕ} (y : T.F m) (hy : y′ = 0) : ∃ κ : Kc, y = algebraMap Kc (T.F m) κ := by
  obtain ⟨κ, hκ⟩ := T.hCall (y : E) (by rw [← coe_deriv, hy]; rfl)
  exact ⟨κ, Subtype.ext hκ.symm⟩

/-! ### The base -/

/-- **Completeness at the base** `Kc(x)`. -/
theorem limIntM_complete_zero (h : T.Tr 0) (A : Code 1) (W : List (Code 1))
    (hsol : T.LimSol 0 h A W) : limIntM ks 0 A W ≠ none := by
  obtain ⟨y, hy, c, hlen, hyeq⟩ := hsol
  simp only [limIntM]
  split
  swap
  · simp
  rename_i hnone
  exfalso
  letI : Differential Kc[X] := polynomialOfDeriv 1
  haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
  have hD : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
  obtain ⟨hA, hsA, hdA⟩ := T.ratInt_spec A
  have hηs : ∀ η ∈ W.map (fun w ↦ ((ratInt w).r, (ratInt w).s)),
      Squarefree ((CPoly.toPoly η.2).map (algebraMap ℚ Kc)) ∧
        ((CPoly.toPoly η.1).map (algebraMap ℚ Kc)).degree <
          ((CPoly.toPoly η.2).map (algebraMap ℚ Kc)).degree := by
    intro η hη
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hη
    exact ⟨(T.ratInt_spec w).2.1, (T.ratInt_spec w).2.2⟩
  refine CPoly.limitedCritN_none (K := T.F 0) (algebraMap ℚ Kc) hD hsA hdA hηs hnone
    (T.model0.sem (ratPart (ratInt A)))
    (fun i ↦ T.model0.sem (ratPart (ratInt (W[i.1]'(by simpa using i.2)))))
    (fun i ↦ c.getD i 0) ⟨y, hy⟩ ?_
  apply Subtype.ext
  rw [coe_deriv]
  change y′ = _
  have hsum : ∑ i : Fin (W.map fun w ↦ ((ratInt w).r, (ratInt w).s)).length,
      algebraMap Kc[X] (T.F 0) (C (c.getD i 0)) *
        ((T.model0.sem (ratPart (ratInt (W[i.1]'(by simpa using i.2)))))′ +
          algebraMap Kc[X] (T.F 0) ((CPoly.toPoly
            (W.map fun w ↦ ((ratInt w).r, (ratInt w).s))[i].1).map (algebraMap ℚ Kc)) /
          algebraMap Kc[X] (T.F 0) ((CPoly.toPoly
            (W.map fun w ↦ ((ratInt w).r, (ratInt w).s))[i].2).map (algebraMap ℚ Kc))) =
      (List.zipWith (fun (c : Kc) w ↦ algebraMap Kc (T.F 0) c * (T.MP 0 h).sem (lift 0 w))
        c W).sum := by
    rw [← sum_fin_map_eq_zipWith' (fun w ↦ ((ratInt w).r, (ratInt w).s)) _ c W hlen]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    · apply Subtype.ext
      rw [← phi0, coe_phi0, aeval_C]
      rfl
    · refine Eq.trans ?_ ((T.ratInt_spec (W[i.1]'(by simpa using i.2))).1).symm
      simp [List.getElem_map, phi0]
  have hAv : (T.model0.sem (ratPart (ratInt A)))′ +
      algebraMap Kc[X] (T.F 0) ((CPoly.toPoly (ratInt A).r).map (algebraMap ℚ Kc)) /
        algebraMap Kc[X] (T.F 0) ((CPoly.toPoly (ratInt A).s).map (algebraMap ℚ Kc)) =
      T.model0.sem A := hA.symm
  rw [hsum, hAv]
  have hcs : (((T.model0.sem A - (List.zipWith (fun (c : Kc) w ↦ algebraMap Kc (T.F 0) c *
      (T.MP 0 h).sem (lift 0 w)) c W).sum : T.F 0)) : E) = ((T.model0.sem A : T.F 0) : E) -
      (((List.zipWith (fun (c : Kc) w ↦ algebraMap Kc (T.F 0) c *
      (T.MP 0 h).sem (lift 0 w)) c W).sum : T.F 0) : E) := rfl
  rw [hcs, T.coe_zipWithK_sum]
  change _ = ((T.MP 0 h).sem A : E) - _
  rw [← hyeq]
  ring

/-! ### The step -/

/-- The proper part of a derivative in `F m (tₘ)` vanishes (primitive level), and its polynomial
part integrates to a polynomial. -/
lemma proper_step (m : ℕ) (htr : Transcendental (T.F m) (T.ts m)) {η : Code 1}
    (hk : kind ks m = .prim η) (Aq b s : (T.F m)[X]) (hs : Squarefree s)
    (hdeg : b.degree < s.degree) (z : E) (hz : z ∈ T.F (m + 1))
    (h : z′ = aeval (T.ts m) Aq + aeval (T.ts m) b / aeval (T.ts m) s) :
    b = 0 ∧ ∃ P : (T.F m)[X], z = aeval (T.ts m) P ∧ implicitDeriv (T.wPoly m) P = Aq := by
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) (T.ts m)
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮T.ts m⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple (T.ts m) _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮T.ts m⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮T.ts m⟯ :=
    differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ P : (T.F m)⟮T.ts m⟯) : E) =
      aeval (T.ts m) P := algebraMap_adjoinSimple _
  obtain ⟨hb, P, hP, hPd⟩ := deriv_eq_poly_add_proper (K := (T.F m)⟮T.ts m⟯)
    (fun p hp ↦ T.normal_prim m htr hk p hp) Aq b s hs hdeg ⟨z, (T.mem_F_succ).mp hz⟩
    (Subtype.ext (by
      change z′ = _
      rw [h, IntermediateField.coe_add, IntermediateField.coe_div, hcoe, hcoe, hcoe]))
  refine ⟨hb, P, ?_, hPd⟩
  have := congrArg Subtype.val hP
  rw [hcoe] at this
  exact this

/-- **Completeness, inductive step.** -/
theorem limIntM_complete_prim (m : ℕ) (hnd : T.ND (m + 1)) {η : Code 1}
    (hk : kind ks m = .prim η)
    (ihs : ∀ A W cs Y, limIntM ks m A W = some (cs, Y) →
      T.LimSound m (T.tr_noHom_of_ND m (hnd.mono (Nat.le_succ m))).1 A W cs Y)
    (ihc : ∀ A W, T.LimSol m (T.tr_noHom_of_ND m (hnd.mono (Nat.le_succ m))).1 A W →
      limIntM ks m A W ≠ none)
    (A : Code (m + 2)) (W : List (Code 1)) (hsol : T.LimSol (m + 1) (T.tr_noHom_of_ND (m + 1) hnd).1 A W) :
    limIntM ks (m + 1) A W ≠ none := by
  set hm := (T.tr_noHom_of_ND m (hnd.mono (Nat.le_succ m))).1 with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) (T.tr_noHom_of_ND (m + 1) hnd).1 with hM'
  have htr : Transcendental (T.F m) (T.ts m) := (T.tr_noHom_of_ND (m + 1) hnd).1 m (Nat.lt_succ_self m)
  have hη : ∀ y : T.F m, y′ ≠ T.ratF m η := by
    have := hnd.2 m (Nat.lt_succ_self m)
    simp only [hk] at this
    exact this
  have hwP : T.wPoly m = C (T.ratF m η) := by simp only [wPoly, hk]
  have hsem : ∀ q : Code (m + 2),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  have hsem' : ∀ q : GPoly (Code (m + 1)) × GPoly (Code (m + 1)),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  obtain ⟨y, hy, c, hlen, hyeq⟩ := hsol
  simp only [limIntM, hk]
  by_cases hz : GPoly.isZero (opsM ks m) A.2 = true
  · simp [hz]
  rw [if_neg hz]
  have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr A.1 A.2 hA2 (fun p hp _ ↦ T.normal_prim m htr hk p hp)
  generalize GPoly.hermite (opsM ks m) (wK ks m) A.1 A.2 = hr at hval hsq ⊢
  have hdm := GPoly.divMod_spec M hr.b hr.s
  have hdeg := GPoly.divMod_degree_lt M hr.b hr.s hsq.ne_zero
  generalize GPoly.divMod (opsM ks m) hr.b hr.s = qr at hdm hdeg ⊢
  set ηv := T.ratF m η with hηdef
  set SK := (List.zipWith (fun (c : Kc) w ↦ algebraMap Kc (T.F m) c * M.sem (lift m w)) c W).sum
    with hSK
  have hSKc : ((SK : T.F m) : E) = T.zsumK c W := T.coe_zipWithK_sum hm c W
  -- `y` minus the Hermite part
  set g : T.F (m + 1) := T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd) with hg
  have hz' : y - (g : E) ∈ T.F (m + 1) := sub_mem hy g.2
  have hinjt : Function.Injective (aeval (R := T.F m) (T.ts m)) :=
    transcendental_iff_injective.mp htr
  have hst : aeval (T.ts m) (GPoly.toPoly M hr.s) ≠ 0 := fun h0 ↦
    hsq.ne_zero (hinjt (h0.trans (map_zero _).symm))
  have hzd : (y - (g : E))′ = aeval (T.ts m) (GPoly.toPoly M qr.1 - C SK) +
      aeval (T.ts m) (GPoly.toPoly M qr.2) / aeval (T.ts m) (GPoly.toPoly M hr.s) := by
    have e1 : (((M'.sem A : T.F (m + 1))) : E) = ((g′ : T.F (m + 1)) : E) +
        aeval (T.ts m) (GPoly.toPoly M hr.b) / aeval (T.ts m) (GPoly.toPoly M hr.s) := by
      rw [hsem, hval, IntermediateField.coe_add, IntermediateField.coe_div, coe_phi, coe_phi]
    have hy' : y′ = ((M'.sem A : T.F (m + 1)) : E) - T.zsumK c W := by rw [← hyeq]; ring
    rw [map_sub, hy', e1, coe_deriv, hdm, map_sub, map_add, map_mul, aeval_C,
      show algebraMap (T.F m) E SK = (SK : E) from rfl, hSKc]
    field_simp
    ring
  obtain ⟨hr0, P, hPz, hPd⟩ := T.proper_step m htr hk _ _ _ hsq hdeg _ hz' hzd
  rw [hwP] at hPd
  split_ifs with hq
  swap
  · exact absurd ((GPoly.isZero_iff M _).mpr hr0) hq
  -- the coefficients of the true polynomial part
  have hcoeffD : ∀ k, (P.coeff k)′ + ηv * (P.coeff (k + 1) * (k + 1)) =
      (GPoly.toPoly M qr.1 - C SK).coeff k := fun k ↦ by
    rw [← coeff_implicitDeriv_C, hPd]
  have hP : ∀ k, 1 ≤ k → (P.coeff k)′ + ((k : T.F m) + 1) * P.coeff (k + 1) *
      M.sem (lift m η) = M.sem (qr.1.getD k (opsM ks m).zero) := by
    intro k hk
    have := hcoeffD k
    rw [coeff_sub, coeff_C, if_neg (by omega), sub_zero, coeff_toPoly_getD] at this
    rw [T.sem_lift_F m hm η]
    linear_combination this
  have hconstP : ∀ Q : (T.F m)[X], implicitDeriv (C ηv) Q = 0 → ∃ e : T.F m, Q = C e :=
    fun Q hQ ↦ const_of_implicitDeriv_eq_zero ηv hη hQ
  have hdegP : P.natDegree ≤ qr.1.length - 1 + 1 := by
    refine natDegree_le_succ_of_natDegree_deriv_le ηv hconstP ?_
    rw [hPd]
    refine (natDegree_sub_le _ _).trans (max_le (natDegree_toPoly_le M _) ?_)
    rw [natDegree_C]
    exact Nat.zero_le _
  have htop : (P.coeff (qr.1.length - 1 + 1))′ = 0 := by
    have := hcoeffD (qr.1.length - 1 + 1)
    rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < qr.1.length - 1 + 1 + 1),
      zero_mul, mul_zero, add_zero, coeff_sub, coeff_C, if_neg (by omega), sub_zero,
      coeff_toPoly_getD, List.getD_eq_default _ _ (by omega), M.sem_zero] at this
    exact this
  obtain ⟨κ₀, hκ₀⟩ := T.const_F _ htop
  -- `polyDown` succeeds
  have hsolve : ∀ G W r, limIntM ks m G W = some r → r.1.length = W.length ∧
      (M.sem r.2)′ + (List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * M.sem (lift m w)) r.1 W).sum =
        M.sem G := by
    intro G W r hr
    obtain ⟨h1, h2⟩ := ihs G W r.1 r.2 hr
    refine ⟨h1, Subtype.ext ?_⟩
    rw [IntermediateField.coe_add, coe_deriv, T.coe_zipWith_sum]
    exact h2
  have hcomp : ∀ G W (y : T.F m) (c : List Kc), c.length = W.length →
      y′ + (List.zipWith (fun (c : Kc) w ↦ algebraMap Kc (T.F m) c * M.sem (lift m w)) c W).sum =
        M.sem G → limIntM ks m G W ≠ none := by
    intro G W y c hl hy
    refine ihc G W ⟨y, y.2, c, hl, ?_⟩
    have := congrArg Subtype.val hy
    rw [IntermediateField.coe_add, T.coe_zipWithK_sum] at this
    exact this
  obtain ⟨Q', Ys', hpd, κ, hκ⟩ := polyDown_complete M (lift m η) η
    (fun w ↦ M.sem (lift m w)) (limIntM ks m) (constC (m + 1)) hsolve hcomp rfl
    (by rw [show M.sem (lift m η) = T.ratF m η from T.sem_lift_F m hm η]; exact hη) T.const_F
    T.deriv_algebraMap_Kc T.deriv_ratCast qr.1 P hP
    (qr.1.length - 1) (opsM ks m).zero [] ⟨-κ₀, by rw [M.sem_zero, hκ₀, map_neg]; ring⟩
  rw [hpd]
  simp only
  -- the final call at level `m`
  have hF : (P.coeff 0)′ + (algebraMap Kc (T.F m) (-κ) * ηv + SK) =
      M.sem ((opsM ks m).add (qr.1.getD 0 (opsM ks m).zero)
        ((opsM ks m).neg ((opsM ks m).mul Q' (lift m η)))) := by
    have h0 := hcoeffD 0
    rw [coeff_sub, coeff_C_zero, coeff_toPoly_getD] at h0
    rw [M.sem_add, M.sem_neg, M.sem_mul, hκ, T.sem_lift_F m hm η, map_neg]
    push_cast at h0
    linear_combination h0
  have hfin : T.LimSol m hm ((opsM ks m).add (qr.1.getD 0 (opsM ks m).zero)
      ((opsM ks m).neg ((opsM ks m).mul Q' (lift m η)))) (η :: W) := by
    refine ⟨(P.coeff 0 : E), (P.coeff 0).2, (-κ) :: c, by simp [hlen], ?_⟩
    have hz : T.zsumK ((-κ) :: c) (η :: W) =
        ((algebraMap Kc (T.F m) (-κ) * ηv + SK : T.F m) : E) := by
      rw [IntermediateField.coe_add, hSKc]
      simp only [zsumK, List.zipWith_cons_cons, List.sum_cons]
      rfl
    rw [hz, ← coe_deriv, ← IntermediateField.coe_add]
    exact congrArg Subtype.val hF
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (ihc _ _ hfin)
  obtain ⟨hlen', -⟩ := ihs _ _ _ _ hr
  rw [hr]
  obtain ⟨cs, Y₀⟩ := r
  cases cs with
  | nil => simp at hlen'
  | cons e cs => simp


lemma laurentSolve_isSome {α : Type} (O : COps α) (b : Code 1) (rde : Code 1 → α → Option α)
    (Λ : GPoly α) (k : ℕ) : ∀ N : ℕ,
    (∀ j < N, j ≠ k → (rde (smulQ (((j : ℤ) - k : ℤ) : ℚ) b) (Λ.getD j O.zero)).isSome) →
    (laurentSolve O b rde Λ k N).isSome := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h
    obtain ⟨Ys, hYs⟩ := Option.isSome_iff_exists.mp (ih fun j hj hjk ↦ h j (by omega) hjk)
    simp only [laurentSolve, hYs]
    split_ifs with hNk
    · rfl
    · obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.mp (h N (by omega) hNk)
      rw [hY]
      rfl

/-- **Completeness, exponential step.** -/
theorem limIntM_complete_exp (m : ℕ) (hnd : T.ND (m + 1)) {b : Code 1}
    (hk : kind ks m = .exp b)
    (ihc : ∀ A W, T.LimSol m (T.tr_noHom_of_ND m (hnd.mono (Nat.le_succ m))).1 A W →
      limIntM ks m A W ≠ none)
    (A : Code (m + 2)) (W : List (Code 1))
    (hsol : T.LimSol (m + 1) (T.tr_noHom_of_ND (m + 1) hnd).1 A W) :
    limIntM ks (m + 1) A W ≠ none := by
  obtain ⟨hm, hnh⟩ := T.tr_noHom_of_ND m (hnd.mono (Nat.le_succ m))
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) (T.tr_noHom_of_ND (m + 1) hnd).1 with hM'
  have htr : Transcendental (T.F m) (T.ts m) := (T.tr_noHom_of_ND (m + 1) hnd).1 m (by omega)
  have hbD : T.Adm b := T.adm_of_kind hk
  have hbN : T.NotSpan (expsBelow ks m) b := by
    have := hnd.2 m (Nat.lt_succ_self m)
    rw [hk] at this
    exact this
  set bv := T.ratF m b with hbv
  have hwP : T.wPoly m = C bv * X := by simp only [wPoly, hk]; rfl
  have hsem : ∀ q : Code (m + 2),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  obtain ⟨y, hy, c, hlen, hyeq⟩ := hsol
  simp only [limIntM, hk]
  by_cases hz : GPoly.isZero (opsM ks m) A.2 = true
  · simp [hz]
  rw [if_neg hz]
  have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M A.1 A.2 hA2
  generalize GPoly.expSplit (opsM ks m) A.1 A.2 = sp at hsp1 hsp2 hsp3 ⊢
  obtain ⟨u, v, k, d₁⟩ := sp
  simp only at hsp1 hsp2 hsp3 ⊢
  have hd₁ : GPoly.toPoly M d₁ ≠ 0 := fun h0 ↦ hA2 (by rw [hsp2, h0, mul_zero])
  have hsdvd := GPoly.hermite_s_dvd M (wK ks m) u d₁ hd₁
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr u d₁ hd₁ (fun p hp hpd hdvd ↦
    T.normal_exp m htr hk p hp (fun hXp ↦ hsp3 (hXp.trans hpd)) hdvd)
  generalize GPoly.hermite (opsM ks m) (wK ks m) u d₁ = hr at hval hsq hsdvd ⊢
  rw [← hM] at hval hsq
  have hsX : ¬X ∣ GPoly.toPoly M hr.s := fun h ↦ hsp3 (h.trans hsdvd)
  have hdm := GPoly.divMod_spec M hr.b hr.s
  have hdeg := GPoly.divMod_degree_lt M hr.b hr.s hsq.ne_zero
  generalize GPoly.divMod (opsM ks m) hr.b hr.s = qr at hdm hdeg ⊢
  set Λ := GPoly.add (opsM ks m) (GPoly.mul (opsM ks m) qr.1 (GPoly.monomial (opsM ks m) k
    (opsM ks m).one)) v with hΛ
  have hΛp : GPoly.toPoly M Λ = GPoly.toPoly M qr.1 * X ^ k + GPoly.toPoly M v := by
    rw [hΛ, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M.sem_one, C_1, one_mul]
  set SK := (List.zipWith (fun (c : Kc) w ↦ algebraMap Kc (T.F m) c * M.sem (lift m w)) c W).sum
    with hSK
  have hSKc : ((SK : T.F m) : E) = T.zsumK c W := T.coe_zipWithK_sum hm c W
  -- the fraction field `F m (tₘ)`
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) (T.ts m)
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮T.ts m⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple (T.ts m) _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮T.ts m⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮T.ts m⟯ :=
    differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ P : (T.F m)⟮T.ts m⟯) : E) =
      aeval (T.ts m) P := algebraMap_adjoinSimple _
  have hinjK : Function.Injective (algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯) :=
    IsFractionRing.injective _ _
  have hD : ∀ P : (T.F m)[X], P′ = implicitDeriv (C bv * X) P := fun P ↦ by
    change implicitDeriv (T.wPoly m) P = _; rw [hwP]
  have hnorm : ∀ p : (T.F m)[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′ := fun p hpm hp hpX ↦ by
    change ¬p ∣ implicitDeriv (T.wPoly m) p
    refine T.normal_exp m htr hk p hp fun hXp ↦ hpX ?_
    exact eq_of_monic_of_associated hpm monic_X
      (associated_of_dvd_dvd (irreducible_X.dvd_symm hp hXp) hXp)
  have hη : ∀ r : ℕ, 0 < r → ∀ e : T.F m, e ≠ 0 → e′ - r * bv * e ≠ 0 := fun r hr e he he' ↦ by
    have hr' : (-(r : ℚ)) ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
    refine he (hnh _ (hbD.smul _) (hbN.smul hr') e ?_)
    rw [T.ratF_smulQ]
    push_cast
    linear_combination he'
  -- `y` minus the Hermite part is a Laurent polynomial
  set g : T.F (m + 1) := T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd) with hg
  have hzK : y - (g : E) ∈ (T.F m)⟮T.ts m⟯ := (T.mem_F_succ).mp (sub_mem hy g.2)
  have hts0 : T.ts m ≠ 0 := T.hts0 m b hk
  have hst : aeval (T.ts m) (GPoly.toPoly M hr.s) ≠ 0 := fun h0 ↦
    hsq.ne_zero ((transcendental_iff_injective.mp htr) (h0.trans (map_zero _).symm))
  have hd₁t : aeval (T.ts m) (GPoly.toPoly M d₁) ≠ 0 := fun h0 ↦
    hd₁ ((transcendental_iff_injective.mp htr) (h0.trans (map_zero _).symm))
  have hvalA : ((M'.sem A : T.F (m + 1)) : E) = (g : E)′ +
      aeval (T.ts m) (GPoly.toPoly M Λ) / T.ts m ^ k +
        aeval (T.ts m) (GPoly.toPoly M qr.2) / aeval (T.ts m) (GPoly.toPoly M hr.s) := by
    have hv' : aeval (T.ts m) (GPoly.toPoly M u) / aeval (T.ts m) (GPoly.toPoly M d₁) =
        (g : E)′ + aeval (T.ts m) (GPoly.toPoly M qr.1) +
          aeval (T.ts m) (GPoly.toPoly M qr.2) / aeval (T.ts m) (GPoly.toPoly M hr.s) := by
      have := congrArg (fun z : T.F (m + 1) ↦ (z : E)) hval
      simp only [IntermediateField.coe_add, IntermediateField.coe_div, coe_deriv, coe_phi] at this
      rw [this, hdm, map_add, map_mul]
      field_simp
      ring
    rw [hsem, IntermediateField.coe_div, coe_phi, coe_phi, ← hsp1, hsp2, hΛp]
    simp only [map_add, map_mul, map_pow, aeval_X] at hv' ⊢
    have hv'' : aeval (T.ts m) (GPoly.toPoly M u) = ((g : E)′ + aeval (T.ts m)
        (GPoly.toPoly M qr.1) + aeval (T.ts m) (GPoly.toPoly M qr.2) /
          aeval (T.ts m) (GPoly.toPoly M hr.s)) * aeval (T.ts m) (GPoly.toPoly M d₁) := by
      rw [← hv']; field_simp
    rw [hv'']
    field_simp
    ring
  have hEq : (⟨y - (g : E), hzK⟩ : (T.F m)⟮T.ts m⟯)′ =
      algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ (GPoly.toPoly M Λ - C SK * X ^ k) /
          algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ X ^ k +
        algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ (GPoly.toPoly M qr.2) /
          algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ (GPoly.toPoly M hr.s) +
        algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ 0 / algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ 1 :=
    Subtype.ext (by
      change (y - (g : E))′ = _
      simp only [IntermediateField.coe_add, IntermediateField.coe_div, SubmonoidClass.coe_pow,
        AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hcoe, map_sub, map_mul, map_pow, aeval_C,
        aeval_X, map_zero, map_one, zero_div, add_zero]
      have hy' : y′ = ((M'.sem A : T.F (m + 1)) : E) - T.zsumK c W := by rw [← hyeq]; ring
      rw [hy', hvalA, show algebraMap (T.F m) E SK = (SK : E) from rfl, hSKc]
      have hk0 : (T.ts m) ^ k ≠ 0 := pow_ne_zero k hts0
      field_simp
      ring)
  obtain ⟨hb0, P, hP⟩ := deriv_eq_laurent_add_two_proper_exp (K := (T.F m)⟮T.ts m⟯) bv hD hnorm hη
    (GPoly.toPoly M Λ - C SK * X ^ k) (GPoly.toPoly M qr.2) (GPoly.toPoly M hr.s) 0 1 k hsq
    squarefree_one hsX (Prime.not_dvd_one prime_X) hdeg (by simp) _ hEq
  simp only [mul_one, zero_mul, add_zero] at hb0
  rw [if_pos ((GPoly.isZero_iff M _).mpr hb0)]
  -- the Laurent identity
  have hXK : algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ X ≠ 0 := (map_ne_zero_iff _ hinjK).mpr X_ne_zero
  have hPid : implicitDeriv (C bv * X) P - C ((k : T.F m) * bv) * P =
      GPoly.toPoly M Λ - C SK * X ^ k := by
    apply hinjK
    have h2 := hEq
    rw [hP, hb0] at h2
    simp only [map_zero, zero_div, add_zero] at h2
    rw [Derivation.leibniz_div, deriv_algebraMap, ← map_pow, deriv_algebraMap, hD, hD,
      deriv_X_pow] at h2
    simp only [smul_eq_mul, map_mul, map_pow, map_sub] at h2 ⊢
    field_simp at h2
    linear_combination h2
  have hcoef : ∀ j, (P.coeff j)′ + (((j : ℤ) - k : ℤ) : T.F m) * bv * P.coeff j =
      M.sem (Λ.getD j (opsM ks m).zero) - (if j = k then SK else 0) := fun j ↦ by
    have := congrArg (fun Q ↦ Q.coeff j) hPid
    simp only [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul, coeff_X_pow, mul_ite, mul_one,
      mul_zero, coeff_toPoly_getD] at this
    push_cast
    linear_combination this
  -- the Laurent coefficients `e ≠ 0` by `rdeM`
  have hls := laurentSolve_isSome (opsM ks m) b (rdeM ks m) Λ k (max Λ.length (k + 1))
    fun j _ hjk ↦ by
      rw [Option.isSome_iff_ne_none]
      have hz0 : ((((j : ℤ) - k : ℤ) : ℚ)) ≠ 0 := by
        have : ((j : ℤ) - k : ℤ) ≠ 0 := by omega
        exact_mod_cast this
      refine T.rdeM_complete m (hnd.mono (Nat.le_succ m)) _ (hbD.smul _) (hbN.smul hz0) _
        (P.coeff j) ?_
      rw [T.ratF_smulQ]
      have := hcoef j
      rw [if_neg hjk, sub_zero] at this
      push_cast at this ⊢
      linear_combination this
  -- the coefficient of `t⁰` by limited integration one level down
  have hli := ihc (Λ.getD k (opsM ks m).zero) W ⟨(P.coeff k : E), (P.coeff k).2, c, hlen, by
    have := hcoef k
    rw [if_pos rfl, sub_self, Int.cast_zero, zero_mul, zero_mul, add_zero] at this
    have h3 := congrArg Subtype.val this
    rw [← coe_deriv, h3, AddSubgroupClass.coe_sub, hSKc]
    ring⟩
  obtain ⟨Ys, hYs⟩ := Option.isSome_iff_exists.mp hls
  obtain ⟨⟨cs', Y₀⟩, hY₀⟩ := Option.ne_none_iff_exists'.mp hli
  rw [hYs, hY₀]
  simp

/-- **Completeness of parametric limited integration** in `F m`. -/
theorem limIntM_complete : ∀ (m : ℕ) (hnd : T.ND m) (A : Code (m + 1)) (W : List (Code 1)),
    T.LimSol m (T.tr_noHom_of_ND m hnd).1 A W → limIntM ks m A W ≠ none
  | 0, _, A, W, h => T.limIntM_complete_zero _ A W h
  | m + 1, hnd, A, W, h => by
    have ihc := limIntM_complete m (hnd.mono (Nat.le_succ m))
    cases hk : kind ks m with
    | prim η =>
      exact T.limIntM_complete_prim m hnd hk (T.limIntM_sound m _) ihc A W h
    | exp b => exact T.limIntM_complete_exp m hnd hk ihc A W h

lemma lcombS_id (cs : List ℚ) (vs : List (CPoly ℚ)) :
    CPoly.lcombS (RingHom.id ℚ) cs vs = CPoly.lcomb cs vs := by
  simp [CPoly.lcombS, CPoly.lcomb]

/-- **The independence certificate is sound.** -/
theorem notSpan_of_cert (bs : List (GFrac ℚ)) (b : GFrac ℚ) (h : notSpanCert bs b = true) :
    T.NotSpan bs b := by
  intro cs hl heq
  unfold notSpanCert at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hall, hlin⟩ := h
  set D := denProdQ (b :: bs) with hD
  set P : GFrac ℚ → CPoly ℚ := fun q ↦ CPoly.mul q.1 (CPoly.divMod D q.2).1 with hPdef
  have hden : ∀ q ∈ b :: bs, CPoly.toPoly q.2 ≠ 0 := fun q hq h0 ↦ by
    have := (hall q hq).1
    simp [(CPoly.isZero_iff _).mpr h0] at this
  have hD0 : CPoly.toPoly D ≠ 0 := by
    rw [hD, toPoly_denProdQ]
    intro h0
    rw [List.prod_eq_zero_iff] at h0
    obtain ⟨q, hq, hq0⟩ := List.mem_map.mp h0
    exact hden q hq hq0
  have hP : ∀ q ∈ b :: bs,
      T.ratF 0 q * T.psi0 (CPoly.toPoly D) = T.psi0 (CPoly.toPoly (P q)) := fun q hq ↦ by
    have e1 : CPoly.toPoly D = CPoly.toPoly (CPoly.divMod D q.2).1 * CPoly.toPoly q.2 := by
      rw [CPoly.divMod_spec D q.2, (CPoly.isZero_iff _).mp (hall q hq).2, add_zero]
    have hq0 : T.psi0 (CPoly.toPoly q.2) ≠ 0 :=
      (map_ne_zero_iff _ T.phi0_map_injective).mpr (hden q hq)
    rw [T.ratF0_eq, hPdef]
    simp only [CPoly.toPoly_mul]
    rw [e1, map_mul, map_mul]
    field_simp
  have hC : ∀ c : ℚ, T.psi0 (C c) = (c : T.F 0) := fun c ↦ eq_ratCast (T.psi0.comp C) c
  have hsum : ∀ (cs : List ℚ) (bs' : List (GFrac ℚ)), (∀ q ∈ bs', q ∈ b :: bs) →
      T.lcombF cs bs' * T.psi0 (CPoly.toPoly D) = T.psi0 (CPoly.lcomb cs (bs'.map P)) := by
    intro cs bs' hsub
    induction bs' generalizing cs with
    | nil =>
      refine (congrArg (· * T.psi0 (CPoly.toPoly D)) (T.lcombF_nil_right cs)).trans ?_
      cases cs <;> simp [CPoly.lcomb]
    | cons q bs' ih =>
      cases cs with
      | nil =>
        refine (congrArg (· * T.psi0 (CPoly.toPoly D)) (T.lcombF_nil_left _)).trans ?_
        simp [CPoly.lcomb]
      | cons c cs =>
        have ih' := ih cs fun r hr ↦ hsub r (List.mem_cons_of_mem _ hr)
        have hq := hP q (hsub q List.mem_cons_self)
        refine (congrArg (· * T.psi0 (CPoly.toPoly D)) (T.lcombF_cons c cs q bs')).trans ?_
        simp only [CPoly.lcomb, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih' ⊢
        rw [add_mul, ih', map_add, map_mul, hC]
        linear_combination (c : T.F 0) * hq
  have h1 : T.psi0 (CPoly.lcomb cs (bs.map P)) = T.psi0 (CPoly.toPoly (P b)) := by
    rw [← hsum cs bs fun q hq ↦ List.mem_cons_of_mem _ hq, heq]
    exact hP b List.mem_cons_self
  have h2 : CPoly.lcomb cs (bs.map P) = CPoly.toPoly (P b) := T.phi0_map_injective h1
  refine absurd (Option.isNone_iff_eq_none.mp hlin)
    (CPoly.linSolve_complete_map (RingHom.id ℚ) _ _ cs (by rw [List.length_map]; exact hl) ?_)
  rw [lcombS_id, Polynomial.map_id]
  exact h2

/-- **The derivative certificate is sound.** -/
theorem isDer_of_cert (b : Code 1) (h : derivCert b = true) : T.IsDerF b := by
  obtain ⟨hspec, -, -⟩ := T.ratInt_spec b
  refine ⟨T.model0.sem (ratPart (ratInt b)), ?_⟩
  rw [T.ratF_zero_eq, hspec, (CPoly.isZero_iff _).mp h]
  simp

/-- **The independence certificate modulo logarithmic derivatives is sound.** -/
theorem logIndep_of_cert (h : logIndepCert (allExps ks) = true) : T.LogIndep := by
  rw [logIndepCert, Bool.or_eq_true] at h
  rcases h with h | h
  · exact T.logIndep_of_isDerF fun b hb ↦ T.isDer_of_cert b (List.all_eq_true.mp h b hb)
  · exact T.logIndep_of_hermKernelCert h

/-- **The certificate proves the tower**: primitives are not derivatives, the exponents are
independent modulo logarithmic derivatives, and each is not a combination of the previous ones. -/
theorem nd_of_mixCert (n : ℕ) (h : mixCert ks n = true) : T.ND n := by
  simp only [mixCert, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hL, hlev⟩ := h
  have hLI := T.logIndep_of_cert hL
  have key : ∀ i, i ≤ n → T.ND i := by
    intro i
    induction i with
    | zero => exact fun _ ↦ ⟨hLI, fun j hj ↦ absurd hj (Nat.not_lt_zero j)⟩
    | succ i ih =>
      intro hi
      have hnd := ih (by omega)
      refine ⟨hLI, fun j hj ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hnd.2 j hj
      · have h2 := hlev j (by omega)
        revert h2
        cases hk : kind ks j with
        | prim η =>
          intro h2
          simp only [hk]
          intro y hy
          refine T.limIntM_complete j hnd _ [] ⟨(y : E), y.2, [], rfl, ?_⟩
            (Option.isNone_iff_eq_none.mp h2)
          rw [T.sem_lift_code, ← coe_deriv, hy]
          simp only [zsumK]
          exact add_zero _
        | exp b =>
          intro h2
          simp only [expCert, Bool.and_eq_true] at h2
          exact T.notSpan_of_cert _ _ h2.2
  exact key n le_rfl

end MixTower

end Tower.MixN
