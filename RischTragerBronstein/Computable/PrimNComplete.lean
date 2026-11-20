import RischTragerBronstein.Computable.PrimNSound
import RischTragerBronstein.Computable.PrimNPolyComplete
import RischTragerBronstein.Liouville.ProperFraction

/-!
# Towers of `n` primitives: completeness of parametric limited integration

`limIntP_complete`: if `y′ + ∑ cᵢ wᵢ = A` has a solution with `y ∈ F m` and **constants**
`cᵢ ∈ Kc` (any constants, not only rational ones), then `limIntP ηs m A W` does not fail.

Base: `limitedCritN` is complete over any constant field. Step: a solution `y` of the problem in
`F m (tₘ)` forces the proper part of the Hermite-reduced integrand to vanish
(`deriv_eq_poly_add_proper`), and `y` minus the Hermite part is a polynomial `P` in `tₘ` whose
coefficients solve the polynomial-part equations; then `polyDown` succeeds
(`polyDown_complete`), and so does the final call at level `m`, with the constant of the `t⁰`
coefficient absorbed by the extra parameter `η`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.PrimN

lemma sum_fin_map_eq_zipWith' {β γ R M : Type*} [Zero R] [AddCommMonoid M] (f : β → γ)
    (F : R → β → M) : ∀ (cs : List R) (W : List β), cs.length = W.length →
      ∑ i : Fin (W.map f).length, F (cs.getD i 0) (W[i.1]'(by simpa using i.2)) =
        (List.zipWith F cs W).sum
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, w :: W, h => by
    show ∑ i : Fin ((W.map f).length + 1), F ((c :: cs).getD i 0)
      ((w :: W)[i.1]'(by have := i.2; simp at this ⊢; omega)) = _
    rw [Fin.sum_univ_succ]
    simp only [List.zipWith_cons_cons, List.sum_cons]
    rw [← sum_fin_map_eq_zipWith' f F cs W (by simpa using h)]
    simp

section Coeff

variable {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma coeff_toPoly_getD (p : GPoly α) (k : ℕ) :
    (GPoly.toPoly M p).coeff k = M.sem (p.getD k O.zero) := by
  rw [GPoly.coeff_toPoly]
  by_cases hk : k < p.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getD_eq_getElem _ _ hk]
  · rw [List.getD_eq_default _ _ (by simpa using hk), List.getD_eq_default _ _ (by omega),
      M.sem_zero]

lemma natDegree_toPoly_le (p : GPoly α) : (GPoly.toPoly M p).natDegree ≤ p.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_toPoly_getD, List.getD_eq_default _ _ (by omega), M.sem_zero]

end Coeff

namespace PrimTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ηs : List (Code 1)} (T : PrimTower Kc E ηs)

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
      IntermediateField.coe_mul, T.sem_lift, this]
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
theorem limIntP_complete_zero (h : T.Tr 0) (A : Code 1) (W : List (Code 1))
    (hsol : T.LimSol 0 h A W) : limIntP ηs 0 A W ≠ none := by
  obtain ⟨y, hy, c, hlen, hyeq⟩ := hsol
  simp only [limIntP]
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

/-- The proper part of a derivative in `F m (tₘ)` vanishes, and its polynomial part integrates
to a polynomial. -/
lemma proper_step (m : ℕ) (htr : Transcendental (T.F m) (T.ts m))
    (hη : ∀ y : T.F m, y′ ≠ T.etaF m m) (Aq b s : (T.F m)[X]) (hs : Squarefree s)
    (hdeg : b.degree < s.degree) (z : E) (hz : z ∈ T.F (m + 1))
    (h : z′ = aeval (T.ts m) Aq + aeval (T.ts m) b / aeval (T.ts m) s) :
    b = 0 ∧ ∃ P : (T.F m)[X], z = aeval (T.ts m) P ∧ implicitDeriv (C (T.etaF m m)) P = Aq := by
  have hw : (T.ts m)′ = aeval (T.ts m) (C (T.etaF m m)) := by rw [aeval_C]; exact T.ht m
  let _ := algebraAdjoinSimple (F := T.F m) (T.ts m)
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (C (T.etaF m m))
  let _ : Differential (T.F m)⟮T.ts m⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple (T.ts m) _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮T.ts m⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮T.ts m⟯ :=
    differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮T.ts m⟯ P : (T.F m)⟮T.ts m⟯) : E) =
      aeval (T.ts m) P := algebraMap_adjoinSimple _
  obtain ⟨hb, P, hP, hPd⟩ := deriv_eq_poly_add_proper (K := (T.F m)⟮T.ts m⟯)
    (fun p hp ↦ T.normal hη p hp) Aq b s hs hdeg ⟨z, (T.mem_F_succ).mp hz⟩ (Subtype.ext (by
      change z′ = _
      rw [h, IntermediateField.coe_add, IntermediateField.coe_div, hcoe, hcoe, hcoe]))
  refine ⟨hb, P, ?_, hPd⟩
  have := congrArg Subtype.val hP
  rw [hcoe] at this
  exact this

/-- **Completeness, inductive step.** -/
theorem limIntP_complete_succ (m : ℕ) (hnd : T.ND (m + 1))
    (ihs : ∀ A W cs Y, limIntP ηs m A W = some (cs, Y) →
      T.LimSound m (T.tr_of_ND (hnd.mono (Nat.le_succ m))) A W cs Y)
    (ihc : ∀ A W, T.LimSol m (T.tr_of_ND (hnd.mono (Nat.le_succ m))) A W →
      limIntP ηs m A W ≠ none)
    (A : Code (m + 2)) (W : List (Code 1)) (hsol : T.LimSol (m + 1) (T.tr_of_ND hnd) A W) :
    limIntP ηs (m + 1) A W ≠ none := by
  set hm := T.tr_of_ND (hnd.mono (Nat.le_succ m)) with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) (T.tr_of_ND hnd) with hM'
  have htr : Transcendental (T.F m) (T.ts m) := T.tr_of_ND hnd m (Nat.lt_succ_self m)
  have hη : ∀ y : T.F m, y′ ≠ T.etaF m m := hnd m (Nat.lt_succ_self m)
  have hsem : ∀ q : Code (m + 2),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  have hsem' : ∀ q : GPoly (Code (m + 1)) × GPoly (Code (m + 1)),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  obtain ⟨y, hy, c, hlen, hyeq⟩ := hsol
  simp only [limIntP]
  by_cases hz : GPoly.isZero (opsP ηs m) A.2 = true
  · simp [hz]
  rw [if_neg hz]
  have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr hη A.1 A.2 hA2
  generalize GPoly.hermite (opsP ηs m) (wP ηs m) A.1 A.2 = hr at hval hsq ⊢
  have hdm := GPoly.divMod_spec M hr.b hr.s
  have hdeg := GPoly.divMod_degree_lt M hr.b hr.s hsq.ne_zero
  generalize GPoly.divMod (opsP ηs m) hr.b hr.s = qr at hdm hdeg ⊢
  set η := T.etaF m m with hηdef
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
  obtain ⟨hr0, P, hPz, hPd⟩ := T.proper_step m htr hη _ _ _ hsq hdeg _ hz' hzd
  split_ifs with hq
  swap
  · exact absurd ((GPoly.isZero_iff M _).mpr hr0) hq
  -- the coefficients of the true polynomial part
  have hcoeffD : ∀ k, (P.coeff k)′ + η * (P.coeff (k + 1) * (k + 1)) =
      (GPoly.toPoly M qr.1 - C SK).coeff k := fun k ↦ by
    rw [← coeff_implicitDeriv_C, hPd]
  have hP : ∀ k, 1 ≤ k → (P.coeff k)′ + ((k : T.F m) + 1) * P.coeff (k + 1) *
      M.sem (lift m (eta ηs m)) = M.sem (qr.1.getD k (opsP ηs m).zero) := by
    intro k hk
    have := hcoeffD k
    rw [coeff_sub, coeff_C, if_neg (by omega), sub_zero, coeff_toPoly_getD] at this
    rw [T.sem_lift_eta]
    linear_combination this
  have hconstP : ∀ Q : (T.F m)[X], implicitDeriv (C η) Q = 0 → ∃ e : T.F m, Q = C e :=
    fun Q hQ ↦ const_of_implicitDeriv_eq_zero η hη hQ
  have hdegP : P.natDegree ≤ qr.1.length - 1 + 1 := by
    refine natDegree_le_succ_of_natDegree_deriv_le η hconstP ?_
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
  have hsolve : ∀ G W r, limIntP ηs m G W = some r → r.1.length = W.length ∧
      (M.sem r.2)′ + (List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * M.sem (lift m w)) r.1 W).sum =
        M.sem G := by
    intro G W r hr
    obtain ⟨h1, h2⟩ := ihs G W r.1 r.2 hr
    refine ⟨h1, Subtype.ext ?_⟩
    rw [IntermediateField.coe_add, coe_deriv, T.coe_zipWith_sum]
    exact h2
  have hcomp : ∀ G W (y : T.F m) (c : List Kc), c.length = W.length →
      y′ + (List.zipWith (fun (c : Kc) w ↦ algebraMap Kc (T.F m) c * M.sem (lift m w)) c W).sum =
        M.sem G → limIntP ηs m G W ≠ none := by
    intro G W y c hl hy
    refine ihc G W ⟨y, y.2, c, hl, ?_⟩
    have := congrArg Subtype.val hy
    rw [IntermediateField.coe_add, T.coe_zipWithK_sum] at this
    exact this
  obtain ⟨Q', Ys', hpd, κ, hκ⟩ := polyDown_complete M (lift m (eta ηs m)) (eta ηs m)
    (fun w ↦ M.sem (lift m w)) (limIntP ηs m) (constC (m + 1)) hsolve hcomp rfl
    (by rw [T.sem_lift_eta]; exact hη) T.const_F T.deriv_algebraMap_Kc T.deriv_ratCast qr.1 P hP
    (qr.1.length - 1) (opsP ηs m).zero [] ⟨-κ₀, by rw [M.sem_zero, hκ₀, map_neg]; ring⟩
  rw [hpd]
  simp only
  -- the final call at level `m`
  have hF : (P.coeff 0)′ + (algebraMap Kc (T.F m) (-κ) * η + SK) =
      M.sem ((opsP ηs m).add (qr.1.getD 0 (opsP ηs m).zero)
        ((opsP ηs m).neg ((opsP ηs m).mul Q' (lift m (eta ηs m))))) := by
    have h0 := hcoeffD 0
    rw [coeff_sub, coeff_C_zero, coeff_toPoly_getD] at h0
    rw [M.sem_add, M.sem_neg, M.sem_mul, hκ, T.sem_lift_eta, map_neg]
    push_cast at h0
    linear_combination h0
  have hfin : T.LimSol m hm ((opsP ηs m).add (qr.1.getD 0 (opsP ηs m).zero)
      ((opsP ηs m).neg ((opsP ηs m).mul Q' (lift m (eta ηs m))))) (eta ηs m :: W) := by
    refine ⟨(P.coeff 0 : E), (P.coeff 0).2, (-κ) :: c, by simp [hlen], ?_⟩
    have hz : T.zsumK ((-κ) :: c) (eta ηs m :: W) =
        ((algebraMap Kc (T.F m) (-κ) * η + SK : T.F m) : E) := by
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

/-- **Completeness of parametric limited integration** in `F m`: a solution with constants in
`Kc` forces `limIntP` to succeed. -/
theorem limIntP_complete : ∀ (m : ℕ) (hnd : T.ND m) (A : Code (m + 1)) (W : List (Code 1)),
    T.LimSol m (T.tr_of_ND hnd) A W → limIntP ηs m A W ≠ none
  | 0, _, A, W, h => T.limIntP_complete_zero _ A W h
  | m + 1, hnd, A, W, h =>
    T.limIntP_complete_succ m hnd (T.limIntP_sound m (hnd.mono (Nat.le_succ m)))
      (limIntP_complete m (hnd.mono (Nat.le_succ m))) A W h

/-- **The certificate proves the tower**: each `ηₘ` (`m < n`) is not a derivative in `F m`; hence
each `tₘ` is transcendental over `F m` and introduces no new constant. -/
theorem nd_of_primCert : ∀ n : ℕ, primCert ηs n = true → T.ND n
  | 0, _ => fun i hi ↦ absurd hi (Nat.not_lt_zero i)
  | n + 1, h => by
    have h' : primCert ηs n = true ∧ (limIntP ηs n (lift n (eta ηs n)) []).isNone = true := by
      simp only [primCert, List.range_succ, List.all_append, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true] at h
      exact h
    have hnd := nd_of_primCert n h'.1
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hnd i hi
    · intro y hy
      refine T.limIntP_complete i hnd _ [] ⟨(y : E), y.2, [], rfl, ?_⟩
        (Option.isNone_iff_eq_none.mp h'.2)
      rw [T.sem_lift, ← coe_deriv, hy]
      simp only [zsumK, etaF]
      exact add_zero _

end PrimTower

end Tower.PrimN
