import RischTragerBronstein.Mixed.MTRdeP5
import RischTragerBronstein.Computable.NestXRdeP

/-!
# Mixed towers over a curve (`RdeP`)

Ported from `Tower.NestX` (`NestXRdeP`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u


namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]
variable (T : MTower Fc ks Cc L)


/-- The shape of the output of `prdePrimC`. -/
lemma prdePrimX_memXP (m : ℕ) (η v : LC m)
    (lower : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (lim : List (LC m) → List (List ℚ × LC m))
    (fr : FRep (LC (m + 1))) (W : List (LC (m + 1))) (r : List ℚ × LC (m + 1))
    (hr : r ∈ prdePrimC Fc ks m η v lower lim fr W) :
    ∃ Bs : List (List ℚ × GPoly (LC m)), r ∈ peOutC Fc ks m (wKC (MO Fc ks m) (ks m))
      (peA (MO Fc ks m) (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr)
          (peDX (MO Fc ks m) (wKC (MO Fc ks m) (ks m))
            (lcmList (MO Fc ks m) ((W.map (cleanG (MO Fc ks m))).map Prod.snd))
            (logPoly (MO Fc ks m) false fr.logs) (logBoundC Fc ks m fr.logs)))
        (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (W.map (cleanG (MO Fc ks m)))
          (peDX (MO Fc ks m) (wKC (MO Fc ks m) (ks m))
            (lcmList (MO Fc ks m) ((W.map (cleanG (MO Fc ks m))).map Prod.snd))
            (logPoly (MO Fc ks m) false fr.logs) (logBoundC Fc ks m fr.logs))))
      (peB (MO Fc ks m) (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr)
          (peDX (MO Fc ks m) (wKC (MO Fc ks m) (ks m))
            (lcmList (MO Fc ks m) ((W.map (cleanG (MO Fc ks m))).map Prod.snd))
            (logPoly (MO Fc ks m) false fr.logs) (logBoundC Fc ks m fr.logs)))
        (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (W.map (cleanG (MO Fc ks m)))
          (peDX (MO Fc ks m) (wKC (MO Fc ks m) (ks m))
            (lcmList (MO Fc ks m) ((W.map (cleanG (MO Fc ks m))).map Prod.snd))
            (logPoly (MO Fc ks m) false fr.logs) (logBoundC Fc ks m fr.logs))))
      (peCs (MO Fc ks m) (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr)
          (peDX (MO Fc ks m) (wKC (MO Fc ks m) (ks m))
            (lcmList (MO Fc ks m) ((W.map (cleanG (MO Fc ks m))).map Prod.snd))
            (logPoly (MO Fc ks m) false fr.logs) (logBoundC Fc ks m fr.logs)))
        (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (W.map (cleanG (MO Fc ks m)))
          (peDX (MO Fc ks m) (wKC (MO Fc ks m) (ks m))
            (lcmList (MO Fc ks m) ((W.map (cleanG (MO Fc ks m))).map Prod.snd))
            (logPoly (MO Fc ks m) false fr.logs) (logBoundC Fc ks m fr.logs))))
      (W.map (cleanG (MO Fc ks m))).length
      (peDX (MO Fc ks m) (wKC (MO Fc ks m) (ks m))
        (lcmList (MO Fc ks m) ((W.map (cleanG (MO Fc ks m))).map Prod.snd))
        (logPoly (MO Fc ks m) false fr.logs) (logBoundC Fc ks m fr.logs)) Bs := by
  simp only [prdePrimC] at hr
  split at hr
  · simp at hr
  · exact ⟨_, hr⟩

section Help

variable (m : ℕ) (h : T.Tr (m + 1))

/-- The denominator `peDX` is monic. -/
lemma peDX_monicXP (e L : GPoly (LC m)) (N : ℕ) (he : GPoly.toPoly (T.MX m h) e ≠ 0)
    (hL : GPoly.toPoly (T.MX m h) L ≠ 0) :
    (GPoly.toPoly (T.MX m h) (peDX (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) e L N)).Monic := by
  set g := (GPoly.egcd (MO Fc ks m) e (GPoly.derivT (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) e)).1
  have hge : GPoly.toPoly (T.MX m h) g ∣ GPoly.toPoly (T.MX m h) e := (GPoly.egcd_dvd _ _ _).1
  have hg0 : GPoly.toPoly (T.MX m h) g ≠ 0 := fun h0 ↦ he (zero_dvd_iff.mp (h0 ▸ hge))
  have hGL0 : GPoly.toPoly (T.MX m h) (GPoly.mul (MO Fc ks m) g (powG (MO Fc ks m) L N)) ≠ 0 := by
    rw [GPoly.toPoly_mul, toPoly_powGXP]; exact mul_ne_zero hg0 (pow_ne_zero _ hL)
  exact (toPoly_monicG (T.MX m h) _ hGL0).2

/-- `sQ` does not see the cleaning of the weights. -/
lemma sQ_cleanXP (e : List ℚ) (W : List (GPX m)) :
    sQ (T.M1X m h) e (W.map (cleanG (MO Fc ks m))) = sQ (T.M1X m h) e W := by
  unfold sQ
  rw [List.length_map]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  congr 1
  rw [NestTower.getD_map' _ _ ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))).zero _ hi',
    T.semX_cleanG]

/-- `sC` does not see the cleaning of the weights. -/
lemma sC_cleanXP (c : List Cc) (W : List (GPX m)) :
    sC (algebraMap Cc (T.F (m + 1))) (T.M1X m h) c (W.map (cleanG (MO Fc ks m))) =
      sC (algebraMap Cc (T.F (m + 1))) (T.M1X m h) c W := by
  unfold sC
  rw [List.length_map]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  congr 1
  rw [NestTower.getD_map' _ _ ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))).zero _ hi',
    T.semX_cleanG]

end Help

section Sound

variable (m : ℕ) (h : T.Tr (m + 1)) {η : LC m} (hk : ks m = .prim η)

include hk in
/-- **Soundness of `prdePrimC`.** -/
theorem prdePrimX_soundXP (v : LC m)
    (lower : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (lim : List (LC m) → List (List ℚ × LC m))
    (fr : FRep (LC (m + 1))) (W : List (LC (m + 1))) (r : List ℚ × LC (m + 1))
    (hr : r ∈ prdePrimC Fc ks m η v lower lim fr W) :
    ((T.MP (m + 1) h).sem r.2)′ + (T.MP (m + 1) h).sem (fCode (MO Fc ks (m + 1)) fr) *
      (T.MP (m + 1) h).sem r.2 = sQ (T.MP (m + 1) h) r.1 W := by
  obtain ⟨Bs, hBs⟩ := prdePrimX_memXP m η v lower lim fr W r hr
  have hWc0 : ∀ q ∈ ((W.map (cleanG (MO Fc ks m))).map Prod.snd),
      GPoly.toPoly (T.MX m h) q ≠ 0 := fun q hq ↦ by
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq'
    intro h0; exact T.σX_cleanG_ne m h w (by rw [σX, h0, map_zero])
  obtain ⟨-, he0, -⟩ := GPolyLcm.lcmList_spec (T.MX m h) _ hWc0
  have hmon := T.peDX_monicXP m h _ (logPoly (MO Fc ks m) false fr.logs) (logBoundC Fc ks m fr.logs)
    he0 (toPoly_logPoly_ne (T.MX m h) _)
  have hQ0 : T.σX m h (peDX (MO Fc ks m) (wKC (MO Fc ks m) (ks m))
      (lcmList (MO Fc ks m) ((W.map (cleanG (MO Fc ks m))).map Prod.snd))
      (logPoly (MO Fc ks m) false fr.logs) (logBoundC Fc ks m fr.logs)) ≠ 0 := by
    rw [σX, Ne, map_eq_zero_iff _ (T.phi_injX m h)]; exact hmon.ne_zero
  have := T.peOut_soundXP m h (primShape (T.ηX m h η)) (T.wPoly_eq_ηX m h hk)
    (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) (W.map (cleanG (MO Fc ks m))) _ hQ0
    Bs r hBs
  exact this.trans (T.sQ_cleanXP m h r.1 W)

end Sound

section Complete

variable (m : ℕ) (h : T.Tr (m + 1)) {η : LC m} (hk : ks m = .prim η)

include hk in
set_option maxHeartbeats 6400000 in
/-- **Completeness of `prdePrimC`**, given a complete Risch solver and a complete limited
integration one level down. -/
theorem prdePrimX_completeXP (hnd : ∀ y : T.F m, y′ ≠ T.ηX m h η) (v : LC m)
    (hlv : (T.MX m h).sem η = logDeriv ((T.MX m h).sem v))
    (lower : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hlower : ∀ fr' : FRep (LC m), FRepOK (T.MX m h) fr' →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MX m h) ((T.MX m h).sem (fCode (MO Fc ks m) fr'))
        (lower fr'))
    (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MX m h) lim)
    (fr : FRep (GPX m)) (hok : FRepOK (T.M1X m h) fr) (W : List (GPX m)) (c : List Cc)
    (hcW : ∀ i, W.length ≤ i → c.getD i 0 = 0) (y : T.F (m + 1))
    (hy : y′ + (T.M1X m h).sem (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) * y =
      sC (algebraMap Cc (T.F (m + 1))) (T.M1X m h) c W) :
    ∃ γ : List Cc,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range (prdePrimC Fc ks m η v lower lim fr W).length,
        γ.getD k 0 * algebraMap ℚ Cc (((prdePrimC Fc ks m η v lower lim fr W).getD k
          ([], ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))).zero)).1.getD i 0)) ∧
      y = ∑ k ∈ Finset.range (prdePrimC Fc ks m η v lower lim fr W).length,
        algebraMap Cc (T.F (m + 1)) (γ.getD k 0) *
          (T.M1X m h).sem ((prdePrimC Fc ks m η v lower lim fr W).getD k
            ([], ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))).zero)).2 := by
  classical
  have hcst : ∀ q, (T.MX m h).sem (mcst Fc ks m q) = (q : T.F m) := T.sem_cstX m h
  have hred : ∀ a, (T.MX m h).sem (redL Fc ks m a) = (T.MX m h).sem a := fun a ↦
    Subtype.ext (by
      rw [T.sem_MP m _, T.sem_MP m _]
      exact T.ev_redL m (fun i hi ↦ h i (by omega)) a)
  have hw := T.toPoly_wK_DS m h (primShape (T.ηX m h η)) (T.wPoly_eq_ηX m h hk)
  -- the pieces of the algorithm
  obtain ⟨Wc, hWc⟩ : ∃ Wc : List (GPX m), Wc = W.map (cleanG (MO Fc ks m)) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = lcmList (MO Fc ks m) (Wc.map Prod.snd) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = peDX (MO Fc ks m) (wKC (MO Fc ks m) (ks m)) e
      (logPoly (MO Fc ks m) false fr.logs) (logBoundC Fc ks m fr.logs) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
      (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) D := ⟨_, rfl⟩
  obtain ⟨Rs, hRs⟩ : ∃ Rs, Rs = peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
      Wc D := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = peA (MO Fc ks m) F Rs := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = peB (MO Fc ks m) F Rs := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = peCs (MO Fc ks m) F Rs := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = (Cs.map (degG (MO Fc ks m))).foldr max 0 := ⟨_, rfl⟩
  obtain ⟨lowF, hlowF⟩ : ∃ lowF, lowF = lowFXC Fc ks m v fr := ⟨_, rfl⟩
  obtain ⟨Finf, hFinf⟩ : ∃ Finf, Finf = (MO Fc ks m).mul (leadG (MO Fc ks m) B)
      ((MO Fc ks m).inv (leadG (MO Fc ks m) A)) := ⟨_, rfl⟩
  obtain ⟨Nb, hNb⟩ : ∃ Nb, Nb = primNbXP (MO Fc ks m) lim η A B R := ⟨_, rfl⟩
  obtain ⟨alg, halg⟩ : ∃ alg, alg = (!GPoly.isZero (MO Fc ks m) B &&
      decide (degG (MO Fc ks m) A < degG (MO Fc ks m) B)) := ⟨_, rfl⟩
  obtain ⟨bal, hbal⟩ : ∃ bal, bal = (!GPoly.isZero (MO Fc ks m) B &&
      decide (degG (MO Fc ks m) A = degG (MO Fc ks m) B)) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = if alg then degG (MO Fc ks m) B else degG (MO Fc ks m) A := ⟨_, rfl⟩
  obtain ⟨lower', hlower'⟩ : ∃ lower' : ℕ → List (LC m) → List (List ℚ × LC m),
      lower' = fun (_ : ℕ) ws ↦ if bal then lower lowF (ws.map (redL Fc ks m))
        else lim (ws.map (redL Fc ks m)) ++ [([], (MO Fc ks m).one)] :=
    ⟨_, rfl⟩
  obtain ⟨init, hinit⟩ : ∃ init, init = (List.range Wc.length).map fun i ↦
      (unitV Wc.length i, ([] : GPoly (LC m))) := ⟨_, rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ Bs, Bs = match Nb with
      | none => init
      | some N => rdeLoop (MO Fc ks m) (mcst Fc ks m) (wKC (MO Fc ks m) (ks m)) A B Cs Wc.length δ alg
          (leadG (MO Fc ks m) A) (leadG (MO Fc ks m) B) lower' (N + 1) init := ⟨_, rfl⟩
  have hunf : prdePrimC Fc ks m η v lower lim fr W =
      if (bal && !(MO Fc ks m).isZero ((MO Fc ks m).add (fCode (MO Fc ks m) lowF)
        ((MO Fc ks m).neg Finf))) = true then []
      else peOutC Fc ks m (wKC (MO Fc ks m) (ks m)) A B Cs Wc.length D Bs := by
    subst hBs hinit hlower' hδ hbal halg hNb hFinf hlowF hR hCs hB hA hRs hF hD he hWc
    rfl
  rw [hunf]
  -- basic facts
  have hWc0 : ∀ q ∈ Wc, GPoly.toPoly (T.MX m h) q.2 ≠ 0 := fun q hq ↦ by
    rw [hWc] at hq
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    intro h0; exact T.σX_cleanG_ne m h w (by rw [σX, h0, map_zero])
  obtain ⟨-, he0, -⟩ := GPolyLcm.lcmList_spec (T.MX m h) (Wc.map Prod.snd) (fun p hp ↦ by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; exact hWc0 q hq)
  rw [← he] at he0
  have hDm : (GPoly.toPoly (T.MX m h) D).Monic := by
    rw [hD]; exact T.peDX_monicXP m h e _ _ he0 (toPoly_logPoly_ne (T.MX m h) _)
  have hQ0 : T.σX m h D ≠ 0 := by
    rw [σX, Ne, map_eq_zero_iff _ (T.phi_injX m h)]; exact hDm.ne_zero
  have hRs2 : ∀ p ∈ Rs, T.σX m h p.2 ≠ 0 := fun p hp ↦ by
    rw [hRs] at hp
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
    exact T.σX_cleanG_ne m h _
  have hP : GPoly.toPoly (T.MX m h) (prodD (GPoly.mul (MO Fc ks m)) [(MO Fc ks m).one] Rs) ≠ 0 := by
    have := σ_prodD_ne_zero (GPoly.mul (MO Fc ks m)) [(MO Fc ks m).one] (T.σX m h) (T.σX_mul m h)
      (T.σX_one m h) _ hRs2
    intro h0; exact this (by rw [σX, h0, map_zero])
  have hF2 : GPoly.toPoly (T.MX m h) F.2 ≠ 0 := by
    rw [hF]; intro h0; exact T.σX_peFX_ne m h _ D (by rw [σX, h0, map_zero])
  have hA0 : GPoly.toPoly (T.MX m h) A ≠ 0 := by
    rw [hA, peA, GPoly.toPoly_mul]; exact mul_ne_zero hF2 hP
  have hlW : Wc.length = W.length := by rw [hWc, List.length_map]
  have hlCs : Cs.length = Wc.length := by simp [hCs, peCs, length_cross, hRs, peRsX]
  have hlcA := sem_leadGXP (T.MX m h) A
  have hlcB := sem_leadGXP (T.MX m h) B
  have hFinfv : (T.MX m h).sem Finf = (GPoly.toPoly (T.MX m h) B).leadingCoeff /
      (GPoly.toPoly (T.MX m h) A).leadingCoeff := by
    rw [hFinf, (T.MX m h).sem_mul, (T.MX m h).sem_inv, hlcA, hlcB, div_eq_mul_inv]
  -- the balanced case
  have hbalF : bal = true → FRepOK (T.MX m h) lowF ∧ (T.MX m h).sem (fCode (MO Fc ks m) lowF) =
      (GPoly.toPoly (T.MX m h) B).leadingCoeff / (GPoly.toPoly (T.MX m h) A).leadingCoeff := by
    intro hb
    rw [hbal] at hb
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
    obtain ⟨hBz, hdeq⟩ := hb
    have hB0 : GPoly.toPoly (T.MX m h) B ≠ 0 := fun h0 ↦ by
      rw [(GPoly.isZero_iff (T.MX m h) _).mpr h0] at hBz; exact Bool.noConfusion hBz
    rw [degG_eq (T.MX m h), degG_eq (T.MX m h)] at hdeq
    have := T.prim_balXP m h hk hnd v hlv fr hok D hDm Rs hP
      (by rw [← hF, ← hB]; exact hB0) (by rw [← hF, ← hA, ← hB]; exact hdeq)
    rw [← hF, ← hA, ← hB, ← hlowF] at this
    exact this
  split_ifs with hbad
  · -- the balanced check always passes
    exfalso
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hbad
    obtain ⟨hb, hok'⟩ := hbad
    obtain ⟨-, hv'⟩ := hbalF hb
    have : (MO Fc ks m).isZero ((MO Fc ks m).add (fCode (MO Fc ks m) lowF) ((MO Fc ks m).neg Finf))
        = true := by
      rw [(T.MX m h).isZero_iff, (T.MX m h).sem_add, (T.MX m h).sem_neg, hv', hFinfv,
        add_neg_cancel]
    rw [this] at hok'; exact Bool.noConfusion hok'
  -- the equation with the cleaned data
  have hgd : ∀ i < Wc.length, Wc.getD i ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))).zero =
      Wc.getD i ([], []) := fun i hi ↦ by
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]
  have hy' : y′ + (T.M1X m h).sem (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) * y =
      ∑ i ∈ Finset.range Wc.length, algebraMap Cc (T.F (m + 1)) (c.getD i 0) *
        (T.M1X m h).sem (Wc.getD i ([], [])) := by
    rw [hy, ← T.sC_cleanXP m h, ← hWc, sC]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hgd i (Finset.mem_range.mp hi)]
  obtain ⟨Yv, hYv⟩ := T.prim_denominatorXP m h hk fr hok Wc hWc0 (fun i ↦ c.getD i 0) y hy'
  rw [← he, ← hD] at hYv
  have hyQ : T.phi m Yv / T.σX m h D = y := by rw [← hYv]; field_simp
  -- the polynomial equation
  have hid := T.pe_identityXP m h (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) Wc D
    hQ0 Yv (fun i ↦ c.getD i 0)
  rw [← hF, ← hRs, ← hA, ← hB, ← hCs, hyQ] at hid
  have hbr : y′ + (T.M1X m h).sem (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) * y -
      ∑ i ∈ Finset.range Wc.length, algebraMap Cc (T.F (m + 1)) (c.getD i 0) *
        (T.M1X m h).sem (Wc.getD i ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))).zero) = 0 := by
    rw [hy', sub_eq_zero]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hgd i (Finset.mem_range.mp hi)]
  rw [hbr, mul_zero] at hid
  have hpoly := (map_eq_zero_iff _ (T.phi_injX m h)).mp hid
  set DS := primShape (T.ηX m h η) with hDS
  have hwP : T.wPoly m = DS.W := T.wPoly_eq_ηX m h hk
  have hresC : resCX (algebraMap Cc (T.F m)) (T.MX m h) DS A B Cs c Yv = 0 := by
    unfold resCX DzX; rw [hlCs, ← hwP]; exact hpoly
  -- the degree bound
  obtain ⟨r, hr⟩ : ∃ r, r = ∑ i ∈ Finset.range Cs.length,
      C (algebraMap Cc (T.F m) (c.getD i 0)) * GPoly.toPoly (T.MX m h) (Cs.getD i []) := ⟨_, rfl⟩
  have hrR : r.natDegree ≤ R := by
    rw [hr]
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ natDegree_C_mul_le _ _ |>.trans ?_
    rw [hR]; exact natDegree_le_R (T.MX m h) Cs i (Finset.mem_range.mp hi)
  have heq : GPoly.toPoly (T.MX m h) A * implicitDeriv (C (T.ηX m h η)) Yv +
      GPoly.toPoly (T.MX m h) B * Yv = r := by
    rw [hr]; unfold resCX at hresC; exact sub_eq_zero.mp hresC
  have hNbs := T.prim_NbXP m h hnd lim hlim A B hA0 Yv r R hrR heq
  rw [← hNb] at hNbs
  have hιd : ∀ κ : Cc, (algebraMap Cc (T.F m) κ)′ = 0 := T.deriv_algebraMap_Cc
  have hιrat : ∀ q : ℚ, algebraMap Cc (T.F m) (algebraMap ℚ Cc q) = (q : T.F m) :=
    fun q ↦ T.algebraMap_ratX q
  have hcCs : ∀ i, Cs.length ≤ i → c.getD i 0 = 0 := fun i hi ↦ hcW i (by omega)
  have hinit' : init = rdeInit (α := LC m) Cs.length := by rw [hinit, hlCs]; rfl
  -- the basis spans the solutions
  have hstage : ∃ β : List Cc, (∀ i, c.getD i 0 = ∑ k ∈ Finset.range Bs.length,
      β.getD k 0 * algebraMap ℚ Cc ((Bs.getD k ([], [])).1.getD i 0)) ∧
      Yv = ∑ l ∈ Finset.range Bs.length, C (algebraMap Cc (T.F m) (β.getD l 0)) *
        GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2 := by
    cases hNbv : Nb with
    | none =>
      rw [hNbv] at hBs
      simp only at hBs
      have hY0 := hNbs.2 hNbv
      obtain ⟨β, hβc, -⟩ := rdeInit_completeX (algebraMap Cc (T.F m)) (M := T.MX m h) DS A B
        Cs δ 0 c hcCs Yv (by rw [hY0, natDegree_zero]) (fun d _ ↦ by rw [hresC, coeff_zero])
      rw [← hinit', ← hBs] at hβc
      refine ⟨β, hβc, ?_⟩
      rw [hY0]
      symm
      refine Finset.sum_eq_zero fun l hl ↦ ?_
      have hl' : l < Wc.length := by simpa [hBs, hinit] using hl
      rw [hBs, hinit, NestTower.getD_range_map _ _ hl']
      simp
    | some N =>
      rw [hNbv] at hBs
      simp only at hBs
      have hYN := hNbs.1 N hNbv
      have hge := primNb_geXP _ _ _ _ _ _ _ (hNb.symm.trans hNbv)
      rw [← halg, ← hδ] at hge
      have hC : ∀ i < Cs.length, (GPoly.toPoly (T.MX m h) (Cs.getD i [])).natDegree ≤ N + δ :=
        fun i hi ↦ (natDegree_le_R (T.MX m h) Cs i hi).trans (by rw [← hR]; exact hge)
      have hδ' : δ = if alg then (GPoly.toPoly (T.MX m h) B).natDegree
          else (GPoly.toPoly (T.MX m h) A).natDegree := by
        rw [hδ, degG_eq (T.MX m h), degG_eq (T.MX m h)]
      rw [← hlCs, hinit'] at hBs
      have hsh : ∀ k : ℕ, DS.sh k = 0 := fun _ ↦ rfl
      cases hag : alg with
      | true =>
        rw [hag] at hδ' halg hBs
        simp only [if_true] at hδ'
        simp only [Bool.true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at halg
        obtain ⟨hBz, hlt⟩ := halg
        rw [degG_eq (T.MX m h), degG_eq (T.MX m h)] at hlt
        have hB0 : GPoly.toPoly (T.MX m h) B ≠ 0 := fun h0 ↦ by
          rw [(GPoly.isZero_iff (T.MX m h) _).mpr h0] at hBz; exact Bool.noConfusion hBz
        obtain ⟨-, hcomp⟩ := rdeLoop_stageX (ι := algebraMap Cc (T.F m)) (M := T.MX m h)
          (cst := mcst Fc ks m) (DS := DS) (A := A) (B := B) (Cl := Cs) (δ := δ) (hcst := hcst)
          (w := wKC (MO Fc ks m) (ks m)) (hw := hw) (hιd := hιd) (hιrat := hιrat)
          (by rw [hδ']; exact hlt.le) (by rw [hδ']) true (leadG (MO Fc ks m) A)
          (leadG (MO Fc ks m) B) lower'
          (fun _ ↦ ⟨coeff_eq_zero_of_natDegree_lt (by rw [hδ']; exact hlt), by rw [hlcB, hδ']; rfl,
            by rw [hlcB]; exact leadingCoeff_ne_zero.mpr hB0⟩)
          (fun h' ↦ by cases h') N (N + 1) (rdeInit Cs.length)
          (rdeInit_soundX (M := T.MX m h) DS A B Cs δ N hC)
          (rdeInit_completeX (algebraMap Cc (T.F m)) (M := T.MX m h) DS A B Cs δ N)
        rw [← hBs] at hcomp
        obtain ⟨β, hβc, hcoef⟩ := hcomp c hcCs Yv hYN (fun d _ ↦ by rw [hresC, coeff_zero])
        refine ⟨β, hβc, ?_⟩
        ext i
        rw [hcoef i (Nat.zero_le _), finset_sum_coeff]
        simp only [coeff_C_mul]
      | false =>
        rw [hag] at hδ' halg hBs
        simp only [Bool.false_eq_true, if_false] at hδ'
        have hBle : (GPoly.toPoly (T.MX m h) B).natDegree ≤
            (GPoly.toPoly (T.MX m h) A).natDegree := by
          by_cases hz : GPoly.isZero (MO Fc ks m) B = true
          · rw [(GPoly.isZero_iff _ _).mp hz, natDegree_zero]; exact Nat.zero_le _
          · by_contra hlt
            push Not at hlt
            rw [degG_eq (T.MX m h), degG_eq (T.MX m h)] at halg
            simp [hz, hlt] at halg
        have hdiff : false = false → (T.MX m h).sem (leadG (MO Fc ks m) A) =
            (GPoly.toPoly (T.MX m h) A).coeff δ ∧ (T.MX m h).sem (leadG (MO Fc ks m) A) ≠ 0 ∧
            ∀ k : ℕ, ∃ f : T.F m,
              (∀ z : T.F m, (GPoly.toPoly (T.MX m h) A).coeff δ * (z′ + DS.sh k * z) +
                (GPoly.toPoly (T.MX m h) B).coeff δ * z =
                  (GPoly.toPoly (T.MX m h) A).coeff δ * (z′ + f * z)) ∧
              RdeSpecK (algebraMap Cc (T.F m)) (T.MX m h) f (lower' k) := by
          intro _
          refine ⟨by rw [hlcA, hδ']; rfl, by rw [hlcA]; exact leadingCoeff_ne_zero.mpr hA0,
            fun k ↦ ?_⟩
          cases hbv : bal with
          | true =>
            obtain ⟨hOK, hval⟩ := hbalF hbv
            have hb' := hbv
            rw [hbal] at hb'
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb'
            obtain ⟨-, hdeq⟩ := hb'
            rw [degG_eq (T.MX m h), degG_eq (T.MX m h)] at hdeq
            refine ⟨(T.MX m h).sem (fCode (MO Fc ks m) lowF), fun z ↦ ?_, ?_⟩
            · have hlA : (GPoly.toPoly (T.MX m h) A).coeff δ =
                  (GPoly.toPoly (T.MX m h) A).leadingCoeff := by rw [hδ']; rfl
              have hlB : (GPoly.toPoly (T.MX m h) B).coeff δ =
                  (GPoly.toPoly (T.MX m h) B).leadingCoeff := by rw [hδ', hdeq]; rfl
              have hA0' : (GPoly.toPoly (T.MX m h) A).leadingCoeff ≠ 0 :=
                leadingCoeff_ne_zero.mpr hA0
              rw [hlA, hlB, hval, hsh]
              field_simp
              ring
            · have hl : lower' k = fun ws ↦ lower lowF (ws.map (redL Fc ks m)) := by
                funext ws; rw [hlower']; simp [hbv]
              rw [hl]; exact (hlower lowF hOK).map_input _ _ _ hred
          | false =>
            refine ⟨0, fun z ↦ ?_, ?_⟩
            · have hBc0 : (GPoly.toPoly (T.MX m h) B).coeff δ = 0 := by
                by_cases hz : GPoly.isZero (MO Fc ks m) B = true
                · rw [(GPoly.isZero_iff _ _).mp hz, coeff_zero]
                · have hne : (GPoly.toPoly (T.MX m h) B).natDegree ≠
                      (GPoly.toPoly (T.MX m h) A).natDegree := by
                    intro hdeq
                    rw [hbal, degG_eq (T.MX m h), degG_eq (T.MX m h)] at hbv
                    simp [hz, hdeq] at hbv
                  rw [hδ']; exact coeff_eq_zero_of_natDegree_lt (by omega)
              rw [hBc0, hsh]
              ring
            · have hl : lower' k = fun ws ↦ (fun ws ↦ lim ws ++ [([], (MO Fc ks m).one)])
                  (ws.map (redL Fc ks m)) := by
                funext ws; rw [hlower']; simp [hbv]
              rw [hl]
              exact (rdeSpec_of_limSpec (algebraMap Cc (T.F m)) (T.MX m h) lim hlim
                (fun y hy ↦ T.const_F y hy)).map_input _ _ _ hred
        obtain ⟨-, hcomp⟩ := rdeLoop_stageX (ι := algebraMap Cc (T.F m)) (M := T.MX m h)
          (cst := mcst Fc ks m) (DS := DS) (A := A) (B := B) (Cl := Cs) (δ := δ) (hcst := hcst)
          (w := wKC (MO Fc ks m) (ks m)) (hw := hw) (hιd := hιd) (hιrat := hιrat) (by rw [hδ'])
          (by rw [hδ']; exact hBle) false (leadG (MO Fc ks m) A) (leadG (MO Fc ks m) B) lower'
          (fun h' ↦ by cases h') hdiff N (N + 1) (rdeInit Cs.length)
          (rdeInit_soundX (M := T.MX m h) DS A B Cs δ N hC)
          (rdeInit_completeX (algebraMap Cc (T.F m)) (M := T.MX m h) DS A B Cs δ N)
        rw [← hBs] at hcomp
        obtain ⟨β, hβc, hcoef⟩ := hcomp c hcCs Yv hYN (fun d _ ↦ by rw [hresC, coeff_zero])
        refine ⟨β, hβc, ?_⟩
        ext i
        rw [hcoef i (Nat.zero_le _), finset_sum_coeff]
        simp only [coeff_C_mul]
  obtain ⟨β, hβc, hYvs⟩ := hstage
  have hres' : ∑ l ∈ Finset.range Bs.length, C (algebraMap Cc (T.F m) (β.getD l 0)) *
      resQX (T.MX m h) DS A B Cs (Bs.getD l ([], [])).1
        (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2) = 0 := by
    have := resC_combX (algebraMap Cc (T.F m)) (M := T.MX m h) DS A B Cs hιd hιrat Bs c β hβc 0
    rw [add_zero, ← hYvs, hresC, show LopX (T.MX m h) DS A B 0 = 0 by simp [LopX, DzX],
      add_zero] at this
    exact this.symm
  exact T.peOut_completeXP m h DS hwP A B Cs Wc.length D hQ0 Bs c (fun i hi ↦ hcW i (by omega)) β
    hβc Yv hYvs hres' y hYv

end Complete

/-- **The parametric Risch equation over a logarithmic level is solved**: `prdePrimC` is sound,
and complete over the constants, for every coefficient `f = h′ + ∑ cⱼ wⱼ′ / wⱼ` with constant
`cⱼ`, given a complete solver one level down and limited integration one level down. -/
theorem prdePrimX_spec (m : ℕ) (hM : T.MixHyp (m + 1)) {η : LC m} (hk : ks m = .prim η)
    (v : LC m) (hv : (T.MX m hM.tr).sem v ≠ 0)
    (hlv : (T.MX m hM.tr).sem η = logDeriv ((T.MX m hM.tr).sem v))
    (lower : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hlower : ∀ fr' : FRep (LC m), FRepOK (T.MX m hM.tr) fr' →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MX m hM.tr) ((T.MX m hM.tr).sem (fCode (MO Fc ks m) fr'))
        (lower fr'))
    (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MX m hM.tr) lim)
    (fr : FRep (LC (m + 1))) (hok : FRepOK (T.MP (m + 1) hM.tr) fr) :
    RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hM.tr)
      ((T.MP (m + 1) hM.tr).sem (fCode (MO Fc ks (m + 1)) fr)) (prdePrimC Fc ks m η v lower lim fr) :=
  ⟨fun W r hr ↦ T.prdePrimX_soundXP m hM.tr hk v lower lim fr W r hr,
    fun W c hc y hy ↦ T.prdePrimX_completeXP m hM.tr hk (MixHyp.ndX T hM (Nat.lt_succ_self m) hk hM.tr) v
      hlv lower hlower lim hlim fr hok W c hc y hy⟩


end MTower

end Curves.MT
