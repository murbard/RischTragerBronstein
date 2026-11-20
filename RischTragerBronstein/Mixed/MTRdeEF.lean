import RischTragerBronstein.Mixed.MTRdeEC
import RischTragerBronstein.Computable.NestXRdeEF

/-!
# Mixed towers over a curve (`RdeEF`)

Ported from `Tower.NestX` (`NestXRdeEF`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

/-- The shape of the output of `prdeExpC`. -/
lemma prdeExpX_memXEC (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) (a : LC m)
    (lower : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (fr : FRep (LC (m + 1))) (W : List (LC (m + 1))) (r : List ℚ × LC (m + 1))
    (hr : r ∈ prdeExpC Fc ks m a lower fr W) :
    ∃ (kap : ℕ) (Bs : List (List ℚ × GPoly (LC m))),
      r ∈ peOutC Fc ks m (wKC (MO Fc ks m) (ks m))
        (peA (MO Fc ks m) (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr)
          (peQ (MO Fc ks m) kap (DXEC Fc ks m (W.map (cleanG (MO Fc ks m))) fr.logs)))
          (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
            (W.map (cleanG (MO Fc ks m)))
            (peQ (MO Fc ks m) kap (DXEC Fc ks m (W.map (cleanG (MO Fc ks m))) fr.logs))))
        (peB (MO Fc ks m) (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr)
          (peQ (MO Fc ks m) kap (DXEC Fc ks m (W.map (cleanG (MO Fc ks m))) fr.logs)))
          (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
            (W.map (cleanG (MO Fc ks m)))
            (peQ (MO Fc ks m) kap (DXEC Fc ks m (W.map (cleanG (MO Fc ks m))) fr.logs))))
        (peCs (MO Fc ks m) (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr)
          (peQ (MO Fc ks m) kap (DXEC Fc ks m (W.map (cleanG (MO Fc ks m))) fr.logs)))
          (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
            (W.map (cleanG (MO Fc ks m)))
            (peQ (MO Fc ks m) kap (DXEC Fc ks m (W.map (cleanG (MO Fc ks m))) fr.logs))))
        (W.map (cleanG (MO Fc ks m))).length
        (peQ (MO Fc ks m) kap (DXEC Fc ks m (W.map (cleanG (MO Fc ks m))) fr.logs)) Bs := by
  have key : ∀ (c : Bool) (L : List (List ℚ × LC (m + 1))),
      r ∈ (if c = true then [] else L) → r ∈ L := by
    intro c L h'
    split_ifs at h'
    · simp at h'
    · exact h'
  exact ⟨_, _, key _ _ hr⟩



namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]
variable (T : MTower Fc ks Cc L)


section Final

variable (m : ℕ) (h : T.Tr (m + 1))

set_option maxHeartbeats 1600000 in
/-- **The final constant system is complete**: a solution `y = Yv / Q` whose polynomial `Yv` is a
constant combination of the basis `Bs` with vanishing residual is a combination of the output. -/
theorem peOut_completeXE (DS : DShape (T.F m)) (hDS : DS.W = T.wPoly m)
    (A B : GPoly (LC m)) (Cs : List (GPoly (LC m))) (n : ℕ)
    (Q : GPoly (LC m)) (hQ0 : T.σX m h Q ≠ 0)
    (Bs : List (List ℚ × GPoly (LC m))) (c : List Cc)
    (hcn : ∀ i, n ≤ i → c.getD i 0 = 0) (β : List Cc)
    (hβc : ∀ i, c.getD i 0 = ∑ k ∈ Finset.range Bs.length,
      β.getD k 0 * algebraMap ℚ Cc ((Bs.getD k ([], [])).1.getD i 0))
    (Yv : (T.F m)[X])
    (hYv : Yv = ∑ l ∈ Finset.range Bs.length, C (algebraMap Cc (T.F m) (β.getD l 0)) *
      GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2)
    (hres : ∑ l ∈ Finset.range Bs.length, C (algebraMap Cc (T.F m) (β.getD l 0)) *
        resQX (T.MX m h) DS A B Cs (Bs.getD l ([], [])).1
          (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2) = 0)
    (y : T.F (m + 1)) (hy : y * T.σX m h Q = T.phi m Yv) :
    ∃ γ : List Cc,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range
          (peOutC Fc ks m (wKC (MO Fc ks m) (ks m)) A B Cs n Q Bs).length,
        γ.getD k 0 * algebraMap ℚ Cc (((peOutC Fc ks m (wKC (MO Fc ks m) (ks m)) A B Cs n Q
          Bs).getD k ([], ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))).zero)).1.getD
            i 0)) ∧
      y = ∑ k ∈ Finset.range (peOutC Fc ks m (wKC (MO Fc ks m) (ks m)) A B Cs n Q Bs).length,
        algebraMap Cc (T.F (m + 1)) (γ.getD k 0) *
          (T.M1X m h).sem ((peOutC Fc ks m (wKC (MO Fc ks m) (ks m)) A B Cs n Q Bs).getD k
            ([], ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))).zero)).2 := by
  classical
  set O := MO Fc ks m with hO
  have hcst : ∀ q, (T.MX m h).sem (mcst Fc ks m q) = (q : T.F m) := T.sem_cstX m h
  have hw : GPoly.toPoly (T.MX m h) (wKC O (ks m)) = DS.W := by rw [hDS, T.toPoly_wKX]
  have hqK : ∀ q : ℚ, algebraMap Cc (T.F (m + 1)) (algebraMap ℚ Cc q) = (q : T.F (m + 1)) :=
    fun q ↦ T.algebraMap_ratX q
  have hphiq : ∀ q : ℚ, T.phi m (C (q : T.F m)) = (q : T.F (m + 1)) := T.phi_C_ratX m
  obtain ⟨vs, hvs⟩ : ∃ vs : List (LC (m + 1)), vs = Bs.map fun b ↦
      ((residE O (mcst Fc ks m) (wKC O (ks m)) A B Cs b, [O.one]) : LC (m + 1)) := ⟨_, rfl⟩
  have hlv : vs.length = Bs.length := by rw [hvs]; exact List.length_map _
  obtain ⟨U, hU⟩ : ∃ U, U = mrel Fc ks (m + 1) vs := ⟨_, rfl⟩
  set f : CPoly ℚ → List ℚ × LC (m + 1) := fun u ↦
    (vcomb n ((List.range Bs.length).map (u.getD · 0)) (Bs.map Prod.fst),
      ((lcombGP O (mcst Fc ks m) ((List.range Bs.length).map (u.getD · 0)) (Bs.map Prod.snd), Q) :
        LC (m + 1))) with hf
  have hout : peOutC Fc ks m (wKC O (ks m)) A B Cs n Q Bs = U.map f := by
    rw [hU, hvs]; rfl
  rw [hout]
  set βt := (List.range Bs.length).map (β.getD · 0) with hβt
  have hsemv : ∀ l < Bs.length, (T.MP (m + 1) h).sem (vs.getD l (MO Fc ks (m + 1)).zero) =
      T.phi m (resQX (T.MX m h) DS A B Cs (Bs.getD l ([], [])).1
        (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2)) := fun l hl ↦ by
    have hvl : vs.getD l (MO Fc ks (m + 1)).zero =
        ((residE O (mcst Fc ks m) (wKC O (ks m)) A B Cs (Bs.getD l ([], [])), [O.one]) : LC (m + 1)) := by
      rw [hvs]; exact NestTower.getD_map' _ Bs ([], []) _ hl
    rw [hvl]
    change T.σX m h _ / T.σX m h [O.one] = _
    rw [T.σX_one, div_one, σX, toPoly_residEX DS A B Cs hcst (wKC O (ks m)) hw]
  have h0 : (List.zipWith (fun c v ↦ algebraMap Cc (T.F (m + 1)) c * (T.MP (m + 1) h).sem v)
      βt vs).sum = 0 := by
    rw [NestTower.zipWith_sum_range _ 0 (MO Fc ks (m + 1)).zero _ _ (by simp [hβt, hlv])]
    have e : ∀ l ∈ Finset.range βt.length, algebraMap Cc (T.F (m + 1)) (βt.getD l 0) *
        (T.MP (m + 1) h).sem (vs.getD l (MO Fc ks (m + 1)).zero) =
        T.phi m (C (algebraMap Cc (T.F m) (β.getD l 0)) *
          resQX (T.MX m h) DS A B Cs (Bs.getD l ([], [])).1
            (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2)) := fun l hl ↦ by
      have hl' : l < Bs.length := by simpa [hβt] using hl
      rw [hsemv l hl', NestTower.getD_range_map _ _ hl', map_mul, ← T.algebraMap_succ]
    rw [Finset.sum_congr rfl e, ← map_sum, show βt.length = Bs.length by simp [hβt], hres, map_zero]
  obtain ⟨γ, hγl, hγ⟩ := T.consys_complete (m + 1) h vs βt (by simp [hβt, hlv]) h0
  rw [← hU] at hγl hγ
  have hβγ : ∀ l < Bs.length, β.getD l 0 = ∑ k ∈ Finset.range U.length,
      γ.getD k 0 * algebraMap ℚ Cc ((U.getD k []).getD l 0) := fun l hl ↦ by
    have := hγ l
    rw [NestTower.getD_range_map _ _ hl, NestTower.zipWith_sum_range _ 0 [] _ _ hγl, hγl] at this
    exact this
  have hlen : (U.map f).length = U.length := List.length_map _
  have hgetD : ∀ k < U.length, (U.map f).getD k ([], (O.monomial (wKC O (ks m))).zero) =
      f (U.getD k []) := fun k hk ↦ NestTower.getD_map' _ _ [] _ hk
  refine ⟨γ, fun i ↦ ?_, ?_⟩
  · rw [hlen]
    have e : ∀ k ∈ Finset.range U.length, γ.getD k 0 * algebraMap ℚ Cc
        (((U.map f).getD k ([], (O.monomial (wKC O (ks m))).zero)).1.getD i 0) =
        γ.getD k 0 * algebraMap ℚ Cc ((vcomb n ((List.range Bs.length).map ((U.getD k []).getD · 0))
          (Bs.map Prod.fst)).getD i 0) := fun k hk ↦ by
      rw [hgetD k (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl e]
    by_cases hi : i < n
    · rw [hβc i]
      simp only [getD_vcomb, if_pos hi, map_sum, map_mul, Finset.mul_sum, List.length_map]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hl' := Finset.mem_range.mp hl
      rw [hβγ l hl', Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [NestTower.getD_range_map _ _ hl', NestTower.getD_map' _ _ ([], []) [] hl']
      ring
    · rw [hcn i (by omega)]
      symm
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [getD_vcomb, if_neg hi, map_zero, mul_zero]
  · set g : ℕ → T.F (m + 1) := fun l ↦ T.phi m (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2) /
      T.σX m h Q with hg
    have hyv : y = ∑ l ∈ Finset.range Bs.length, algebraMap Cc (T.F (m + 1)) (β.getD l 0) * g l := by
      rw [eq_div_iff hQ0 |>.mpr hy, hYv, map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [map_mul, ← T.algebraMap_succ, hg, mul_div_assoc]
    have hsk : ∀ k < U.length, (T.M1X m h).sem (f (U.getD k [])).2 =
        ∑ l ∈ Finset.range Bs.length, (((U.getD k []).getD l 0 : ℚ) : T.F (m + 1)) * g l :=
      fun k hk ↦ by
      rw [hf]
      simp only
      rw [T.semX, σX, toPoly_lcombGP (T.MX m h) (mcst Fc ks m) hcst,
        zipWith_sum_getD (fun (q : ℚ) (p : GPoly (LC m)) ↦
          C (q : T.F m) * GPoly.toPoly (T.MX m h) p) 0 [] (by simp), List.length_map, map_sum,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hl' := Finset.mem_range.mp hl
      rw [NestTower.getD_range_map _ _ hl', NestTower.getD_map' _ _ ([], []) [] hl', map_mul,
        hphiq, hg, mul_div_assoc]
    rw [hlen, hyv]
    have e : ∀ k ∈ Finset.range U.length, algebraMap Cc (T.F (m + 1)) (γ.getD k 0) *
        (T.M1X m h).sem ((U.map f).getD k ([], (O.monomial (wKC O (ks m))).zero)).2 =
        ∑ l ∈ Finset.range Bs.length, algebraMap Cc (T.F (m + 1)) (γ.getD k 0 *
          algebraMap ℚ Cc ((U.getD k []).getD l 0)) * g l := fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      rw [hgetD k hk', hsk k hk', Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [map_mul, hqK]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [hβγ l (Finset.mem_range.mp hl), map_sum, Finset.sum_mul]

end Final




section Main

variable (m : ℕ) (hM : T.MixHyp (m + 1)) {a : LC m} (hk : ks m = .exp a)

include hk in
/-- **Soundness of `prdeExpC`** (whatever the solver one level down). -/
theorem prdeExpX_soundXE
    (lower : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (fr : FRep (LC (m + 1))) (W : List (LC (m + 1))) :
    ∀ r ∈ prdeExpC Fc ks m a lower fr W,
      ((T.M1X m hM.tr).sem r.2)′ + (T.M1X m hM.tr).sem
        (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) * (T.M1X m hM.tr).sem r.2 =
        sQ (T.M1X m hM.tr) r.1 W := by
  intro r hr
  set h := hM.tr with hh
  obtain ⟨kap, Bs, hr'⟩ := prdeExpX_memXEC Fc ks m a lower fr W r hr
  have hWc0 : ∀ q ∈ W.map (cleanG (MO Fc ks m)), GPoly.toPoly (T.MX m h) q.2 ≠ 0 := fun q hq ↦ by
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hq
    have := T.σX_cleanG_ne m h v
    intro h0; exact this (by rw [σX, h0, map_zero])
  obtain ⟨he0, -⟩ := T.peE_specXE m h _ hWc0
  obtain ⟨-, -, hDm⟩ := T.DXE_spec m h (W.map (cleanG (MO Fc ks m))) fr.logs he0
  have hQ0 : T.σX m h (peQ (MO Fc ks m) kap (DXEC Fc ks m (W.map (cleanG (MO Fc ks m))) fr.logs)) ≠ 0 := by
    rw [σX, map_ne_zero_iff _ (T.phi_injX m h), T.toPoly_peQX]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) hDm.ne_zero
  exact T.peOut_soundXE m h (expShape (T.bX m h a)) (by rw [T.wPoly_eq_bX m h hk]; rfl)
    _ W _ hQ0 Bs r hr'

include hk in
set_option maxHeartbeats 12800000 in
/-- **Completeness of `prdeExpC`**, given a complete solver one level down. -/
theorem prdeExpX_completeXE
    (hc2 : ∀ u ∈ mrel Fc ks m ((MO Fc ks m).deriv a :: gensDC Fc ks m), u.getD 0 0 = 0)
    (lower : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hlower : ∀ fr' : FRep (LC m), FRepOK (T.MX m hM.tr) fr' →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MX m hM.tr) ((T.MX m hM.tr).sem (fCode (MO Fc ks m) fr'))
        (lower fr'))
    (fr : FRep (LC (m + 1))) (hok : ∀ cw ∈ fr.logs, ((T.M1X m hM.tr).sem cw.1)′ = 0)
    (W : List (PrXEC m)) (c : List Cc)
    (hcW : ∀ i, W.length ≤ i → c.getD i 0 = 0) (y : T.F (m + 1))
    (hy : y′ + (T.M1X m hM.tr).sem (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) * y =
      sC (algebraMap Cc (T.F (m + 1))) (T.M1X m hM.tr) c W) :
    ∃ γ : List Cc,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range (prdeExpC Fc ks m a lower fr W).length,
        γ.getD k 0 * algebraMap ℚ Cc (((prdeExpC Fc ks m a lower fr W).getD k
          ([], ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))).zero)).1.getD i 0)) ∧
      y = ∑ k ∈ Finset.range (prdeExpC Fc ks m a lower fr W).length,
        algebraMap Cc (T.F (m + 1)) (γ.getD k 0) *
          (T.M1X m hM.tr).sem ((prdeExpC Fc ks m a lower fr W).getD k
            ([], ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))).zero)).2 := by
  classical
  set h := hM.tr with hh
  have hm : T.Tr m := fun i hi ↦ h i (by omega)
  set O := MO Fc ks m with hO
  set wk := wKC O (ks m) with hwk
  set O' := O.monomial wk with hO'
  have hcst : ∀ q, (T.MX m h).sem (mcst Fc ks m q) = (q : T.F m) := T.sem_cstX m h
  have hw : GPoly.toPoly (T.MX m h) wk = (expShape (T.bX m h a)).W := T.toPoly_wK_exp m h hk
  -- the pieces of the algorithm
  obtain ⟨fc, hfcd⟩ : ∃ fc, fc = fCode O' fr := ⟨_, rfl⟩
  obtain ⟨hc, hhc⟩ : ∃ hc : PrXEC m, hc = cleanG O fr.h := ⟨_, rfl⟩
  obtain ⟨Wc, hWc⟩ : ∃ Wc : List (PrXEC m), Wc = W.map (cleanG O) := ⟨_, rfl⟩
  obtain ⟨eps, heps⟩ : ∃ eps, eps = peEps O Wc := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = DXEC Fc ks m Wc fr.logs := ⟨_, rfl⟩
  obtain ⟨dD, hdD⟩ : ∃ dD, dD = degG O D := ⟨_, rfl⟩
  obtain ⟨logsC, hlogsC⟩ : ∃ logsC, logsC = logsCXE O fr.logs := ⟨_, rfl⟩
  obtain ⟨kap, hkap⟩ : ∃ kap, kap = kapXEC Fc ks m a hc eps (sumOrdXEC Fc ks m logsC) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = peQ O kap D := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = peFX O O' fc Q := ⟨_, rfl⟩
  obtain ⟨Rs, hRs⟩ : ∃ Rs, Rs = peRsX O O' Wc Q := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = peA O F Rs := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = peB O F Rs := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = peCs O F Rs := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = (Cs.map (degG O)).foldr max 0 := ⟨_, rfl⟩
  obtain ⟨hInf, hhInf⟩ : ∃ hInf, hInf = peHinf O hc := ⟨_, rfl⟩
  obtain ⟨sumDeg, hsumDeg⟩ : ∃ sumDeg, sumDeg = sumDegXEC Fc ks m logsC := ⟨_, rfl⟩
  obtain ⟨hBc, hhBc⟩ : ∃ hBc, hBc = O.add hInf (O.mul (O.add sumDeg
      (mcst Fc ks m (-((dD + kap : ℕ) : ℚ)))) a) := ⟨_, rfl⟩
  obtain ⟨logsL, hlogsL⟩ : ∃ logsL, logsL = logsC.map fun cw ↦ (cw.1, lcC O cw.2) := ⟨_, rfl⟩
  obtain ⟨Nb, hNb⟩ : ∃ Nb, Nb = peNbE O (pldC Fc ks m hInf a) (ratValC Fc ks m sumDeg) A B R (dD + kap) :=
    ⟨_, rfl⟩
  obtain ⟨alg, halg⟩ : ∃ alg, alg = (!GPoly.isZero O B && decide (degG O A < degG O B)) :=
    ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = if alg then degG O B else degG O A := ⟨_, rfl⟩
  obtain ⟨lower', hlower'⟩ : ∃ lower' : ℕ → List (LC m) → List (List ℚ × LC m),
      lower' = fun (k : ℕ) ws ↦ if GPoly.isZero O B || decide (degG O B < degG O A) then
        lower ⟨O.mul (mcst Fc ks m (k : ℚ)) a, []⟩ ws
        else lower ⟨O.add hBc (O.mul (mcst Fc ks m (k : ℚ)) a), logsL⟩ ws := ⟨_, rfl⟩
  obtain ⟨init, hinit⟩ : ∃ init, init =
      (List.range Wc.length).map fun i ↦ (unitV Wc.length i, ([] : GPoly (LC m))) :=
    ⟨_, rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ Bs, Bs = match Nb with
      | none => init
      | some N => rdeLoop O (mcst Fc ks m) wk A B Cs Wc.length δ alg (leadG O A) (leadG O B)
          lower' (N + 1) init := ⟨_, rfl⟩
  have hunf : prdeExpC Fc ks m a lower fr W =
      if (!GPoly.isZero O B && !alg && decide (degG O A = degG O B) &&
        !O.isZero (O.add (fCode O ⟨hBc, logsL⟩) (O.neg (O.mul (leadG O B) (O.inv (leadG O A))))))
          = true then []
      else peOutC Fc ks m wk A B Cs Wc.length Q Bs := by
    subst hBs hinit hlower' hδ halg hNb hlogsL hhBc hsumDeg hhInf hR hCs hB hA hRs hF hQ hkap
      hlogsC hdD hD heps hWc hhc hfcd
    rfl
  rw [hunf]
  -- basic facts
  have hWc0 : ∀ q ∈ Wc, GPoly.toPoly (T.MX m h) q.2 ≠ 0 := fun q hq ↦ by
    rw [hWc] at hq
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hq
    have := T.σX_cleanG_ne m h v
    intro h0
    exact this (by rw [σX, h0, map_zero])
  have hhc0 : GPoly.toPoly (T.MX m h) hc.2 ≠ 0 := by
    have := T.σX_cleanG_ne m h fr.h
    rw [← hhc] at this
    intro h0; exact this (by rw [σX, h0, map_zero])
  obtain ⟨he0, -⟩ := T.peE_specXE m h Wc hWc0
  obtain ⟨-, -, hDm⟩ := T.DXE_spec m h Wc fr.logs he0
  rw [← hD] at hDm
  have hQp : GPoly.toPoly (T.MX m h) Q = X ^ kap * GPoly.toPoly (T.MX m h) D := by
    rw [hQ, T.toPoly_peQX]
  have hQm : (GPoly.toPoly (T.MX m h) Q).Monic := by rw [hQp]; exact (monic_X_pow kap).mul hDm
  have hQ0 : T.σX m h Q ≠ 0 := by
    rw [σX, map_ne_zero_iff _ (T.phi_injX m h)]; exact hQm.ne_zero
  have hdDk : (GPoly.toPoly (T.MX m h) Q).natDegree = dD + kap := by
    rw [hQp, (monic_X_pow kap).natDegree_mul hDm, natDegree_X_pow, hdD, degG_eq (T.MX m h)]; ring
  have hRs2 : ∀ p ∈ Rs, T.σX m h p.2 ≠ 0 := by rw [hRs]; exact T.peRsX_ne_XE m h Wc Q
  have hP : GPoly.toPoly (T.MX m h) (prodD (GPoly.mul O) [O.one] Rs) ≠ 0 := by
    have := σ_prodD_ne_zero (GPoly.mul O) [O.one] (T.σX m h) (T.σX_mul m h) (T.σX_one m h) _ hRs2
    intro h0; exact this (by rw [σX, h0, map_zero])
  have hF2 : GPoly.toPoly (T.MX m h) F.2 ≠ 0 := by
    have := T.peFX_ne_XE m h fc Q
    rw [← hF] at this
    intro h0; exact this (by rw [σX, h0, map_zero])
  have hA0 : GPoly.toPoly (T.MX m h) A ≠ 0 := by
    rw [hA, peA, GPoly.toPoly_mul]; exact mul_ne_zero hF2 hP
  have hlW : Wc.length = W.length := by rw [hWc, List.length_map]
  have hlCs : Cs.length = Wc.length := by simp [hCs, peCs, length_cross, hRs, peRsX]
  -- the coefficient `f`
  have hfc : (T.M1X m h).sem fc = ((T.M1X m h).sem hc)′ + logSumV (T.M1X m h) fr.logs := by
    rw [hfcd]
    refine (sem_fCode (T.M1X m h) fr).trans ?_
    rw [hhc]
    exact congrArg (fun z ↦ z′ + logSumV (T.M1X m h) fr.logs) (T.semX_cleanG m h fr.h).symm
  set d : LgXEC m := (([], [O.one]), ([], [O.one])) with hd
  obtain ⟨κ, hκ⟩ := T.exists_consts_XE m h fr.logs hok d
  have hlead := T.pe_bal_leadXE m hM hk fc hc hhc0 fr.logs d κ hκ hfc Q hQm (dD + kap) hdDk Rs hP
  rw [← hF, ← hA, ← hB, ← hlogsC, ← hsumDeg, ← hhInf, ← hhBc, ← hlogsL] at hlead
  split_ifs with hbad
  · -- the balanced check always passes
    exfalso
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hbad
    obtain ⟨⟨⟨hBz, -⟩, hdeq⟩, hok'⟩ := hbad
    have hB0 : GPoly.toPoly (T.MX m h) B ≠ 0 := fun h0 ↦ by
      rw [(GPoly.isZero_iff (T.MX m h) _).mpr h0] at hBz; exact Bool.noConfusion hBz
    rw [degG_eq (T.MX m h), degG_eq (T.MX m h)] at hdeq
    obtain ⟨-, hl⟩ := hlead hB0 hdeq
    have : O.isZero (O.add (fCode O ⟨hBc, logsL⟩) (O.neg (O.mul (leadG O B) (O.inv (leadG O A)))))
        = true := by
      rw [(T.MX m h).isZero_iff, (T.MX m h).sem_add, (T.MX m h).sem_neg, (T.MX m h).sem_mul,
        (T.MX m h).sem_inv, sem_leadG _ _ hB0, sem_leadG _ _ hA0, hl]
      ring
    rw [this] at hok'; exact Bool.noConfusion hok'
  -- the equation with the cleaned data
  have hgd : ∀ i < Wc.length, Wc.getD i O'.zero = Wc.getD i ([], []) := fun i hi ↦ by
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]
  have hy' : y′ + (((T.M1X m h).sem hc)′ + logSumV (T.M1X m h) fr.logs) * y =
      ∑ i ∈ Finset.range Wc.length, algebraMap Cc (T.F (m + 1)) (c.getD i 0) *
        (T.M1X m h).sem (Wc.getD i ([], [])) := by
    rw [← hfc, hfcd]
    refine hy.trans ?_
    rw [sC, hlW]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    congr 1
    have hi2 : i < Wc.length := by rw [hlW]; exact hi'
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi2]
    simp only [hWc, List.getElem_map]
    rw [T.semX_cleanG]
  obtain ⟨Yv, hYv⟩ := T.pe_denominatorXE m hM hk hc2 hc hhc0 fr.logs hok Wc hWc0
    (fun i ↦ c.getD i 0) y hy'
  rw [← heps, ← hlogsC, ← hkap, ← hD, ← hQ] at hYv
  have hyQ : T.phi m Yv / T.σX m h Q = y := by rw [← hYv]; field_simp
  -- the polynomial equation
  have hid := T.pe_identityXE m h fc Wc Q hQ0 Yv (fun i ↦ c.getD i 0)
  rw [← hF, ← hRs, ← hA, ← hB, ← hCs, hyQ] at hid
  have hbr : y′ + (T.M1X m h).sem fc * y - ∑ i ∈ Finset.range Wc.length,
      algebraMap Cc (T.F (m + 1)) (c.getD i 0) * (T.M1X m h).sem (Wc.getD i O'.zero) = 0 := by
    rw [hfc, hy', sub_eq_zero]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hgd i (Finset.mem_range.mp hi)]
  rw [hbr, mul_zero] at hid
  have hpoly := (map_eq_zero_iff _ (T.phi_injX m h)).mp hid
  have hwb : T.wPoly m = C (T.bX m h a) * X := T.wPoly_eq_bX m h hk
  have hresC : resCX (algebraMap Cc (T.F m)) (T.MX m h) (expShape (T.bX m h a)) A B Cs c Yv = 0 := by
    unfold resCX DzX
    rw [hlCs]
    change GPoly.toPoly (T.MX m h) A * implicitDeriv (C (T.bX m h a) * X) Yv + _ - _ = 0
    rw [← hwb]
    exact hpoly
  -- the degree bound
  obtain ⟨r, hr⟩ : ∃ r, r = ∑ i ∈ Finset.range Cs.length,
      C (algebraMap Cc (T.F m) (c.getD i 0)) * GPoly.toPoly (T.MX m h) (Cs.getD i []) := ⟨_, rfl⟩
  have hrR : r.natDegree ≤ R := by
    rw [hr]
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ natDegree_C_mul_le _ _ |>.trans ?_
    rw [hR]; exact natDegree_le_R (T.MX m h) Cs i (Finset.mem_range.mp hi)
  have heq : GPoly.toPoly (T.MX m h) A * implicitDeriv (C (T.bX m h a) * X) Yv +
      GPoly.toPoly (T.MX m h) B * Yv = r := by
    rw [hr]; unfold resCX DzX at hresC; exact sub_eq_zero.mp hresC
  have hNbs := T.pe_NbXE m hM hk hc2 fc hc hhc0 fr.logs d κ hκ hfc Q hQm (dD + kap) hdDk Rs hP
    Yv r R hrR (by rw [← hF, ← hA, ← hB]; exact heq)
  rw [← hF, ← hA, ← hB, ← hhInf, ← hlogsC, ← hsumDeg, ← hNb] at hNbs
  have hιd : ∀ κ : Cc, (algebraMap Cc (T.F m) κ)′ = 0 := fun κ ↦ T.deriv_algebraMap_Cc κ
  have hιrat : ∀ q : ℚ, algebraMap Cc (T.F m) (algebraMap ℚ Cc q) = (q : T.F m) :=
    fun q ↦ T.algebraMap_ratX q
  have hcCs : ∀ i, Cs.length ≤ i → c.getD i 0 = 0 := fun i hi ↦ hcW i (by omega)
  have hinit' : init = rdeInit (α := LC m) Cs.length := by rw [hinit, hlCs]; rfl
  -- the logarithms of the balanced lower coefficient have constant coefficients
  have hokL : ∀ cw ∈ logsL, ((T.MX m h).sem cw.1)′ = 0 := by
    intro cw hcw
    rw [hlogsL, hlogsC] at hcw
    unfold logsCXE at hcw
    obtain ⟨cw1, hcw1, rfl⟩ := List.mem_map.mp hcw
    obtain ⟨cw2, hcw2, rfl⟩ := List.mem_map.mp hcw1
    have hmem := (List.mem_filter.mp hcw2).1
    obtain ⟨κ0, hκ0⟩ := T.const_F _ (hok _ hmem)
    simp only
    rw [T.sem_lcC_constXE m h _ κ0 hκ0]
    exact hιd κ0
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
      obtain ⟨β, hβc, -⟩ := rdeInit_completeX (algebraMap Cc (T.F m)) (M := T.MX m h)
        (expShape (T.bX m h a)) A B Cs δ 0 c hcCs Yv (by rw [hY0, natDegree_zero])
        (fun d _ ↦ by rw [hresC, coeff_zero])
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
      have hge := peNbE_geXE _ _ _ _ _ _ _ _ (hNb.symm.trans hNbv)
      rw [← halg, ← hδ] at hge
      have hC : ∀ i < Cs.length, (GPoly.toPoly (T.MX m h) (Cs.getD i [])).natDegree ≤ N + δ :=
        fun i hi ↦ (natDegree_le_R (T.MX m h) Cs i hi).trans (by rw [← hR]; exact hge)
      have hδ' : δ = if alg then (GPoly.toPoly (T.MX m h) B).natDegree
          else (GPoly.toPoly (T.MX m h) A).natDegree := by
        rw [hδ, degG_eq (T.MX m h), degG_eq (T.MX m h)]
      rw [degG_eq (T.MX m h), degG_eq (T.MX m h)] at halg hlower'
      have hlowk : ∀ k : ℕ, (GPoly.isZero O B || decide ((GPoly.toPoly (T.MX m h) B).natDegree <
          (GPoly.toPoly (T.MX m h) A).natDegree)) = true →
          lower' k = lower ⟨O.mul (mcst Fc ks m (k : ℚ)) a, []⟩ := fun k hk' ↦ by
        funext ws; simp only [hlower']; rw [if_pos hk']
      have hlowk' : ∀ k : ℕ, ¬(GPoly.isZero O B || decide ((GPoly.toPoly (T.MX m h) B).natDegree <
          (GPoly.toPoly (T.MX m h) A).natDegree)) = true →
          lower' k = lower ⟨O.add hBc (O.mul (mcst Fc ks m (k : ℚ)) a), logsL⟩ := fun k hk' ↦ by
        funext ws; simp only [hlower']; rw [if_neg hk']
      rw [← hlCs, hinit'] at hBs
      have hlcA := sem_leadG (T.MX m h) A hA0
      cases alg with
      | true =>
        simp only [if_true] at hδ'
        simp only [Bool.true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at halg
        obtain ⟨hBz, hlt⟩ := halg
        have hB0 : GPoly.toPoly (T.MX m h) B ≠ 0 := fun h0 ↦ by
          rw [(GPoly.isZero_iff (T.MX m h) _).mpr h0] at hBz; exact Bool.noConfusion hBz
        have hlcB := sem_leadG (T.MX m h) B hB0
        obtain ⟨-, hcomp⟩ := rdeLoop_stageX (ι := algebraMap Cc (T.F m)) (M := T.MX m h)
          (cst := mcst Fc ks m) (DS := expShape (T.bX m h a)) (A := A) (B := B) (Cl := Cs) (δ := δ)
          (hcst := hcst) (w := wk) (hw := hw) (hιd := hιd) (hιrat := hιrat)
          (by rw [hδ']; exact hlt.le) (by rw [hδ']) true (leadG O A) (leadG O B) lower'
          (fun _ ↦ ⟨coeff_eq_zero_of_natDegree_lt (by rw [hδ']; exact hlt), by rw [hlcB, hδ']; rfl,
            by rw [hlcB]; exact leadingCoeff_ne_zero.mpr hB0⟩)
          (fun h' ↦ by cases h') N (N + 1) (rdeInit Cs.length)
          (rdeInit_soundX (M := T.MX m h) (expShape (T.bX m h a)) A B Cs δ N hC)
          (rdeInit_completeX (algebraMap Cc (T.F m)) (M := T.MX m h) (expShape (T.bX m h a))
            A B Cs δ N)
        rw [← hBs] at hcomp
        obtain ⟨β, hβc, hcoef⟩ := hcomp c hcCs Yv hYN (fun d _ ↦ by rw [hresC, coeff_zero])
        refine ⟨β, hβc, ?_⟩
        ext i
        rw [hcoef i (Nat.zero_le _), finset_sum_coeff]
        simp only [coeff_C_mul]
      | false =>
        simp only [Bool.false_eq_true, if_false] at hδ'
        have hBle : (GPoly.toPoly (T.MX m h) B).natDegree ≤ (GPoly.toPoly (T.MX m h) A).natDegree := by
          by_cases hz : GPoly.isZero O B = true
          · rw [(GPoly.isZero_iff _ _).mp hz, natDegree_zero]; exact Nat.zero_le _
          · by_contra hlt
            push_neg at hlt
            simp [hz, hlt] at halg
        have hdiff : false = false → (T.MX m h).sem (leadG O A) = (GPoly.toPoly (T.MX m h) A).coeff δ ∧
            (T.MX m h).sem (leadG O A) ≠ 0 ∧ ∀ k : ℕ, ∃ f : T.F m,
              (∀ z : T.F m, (GPoly.toPoly (T.MX m h) A).coeff δ *
                (z′ + (expShape (T.bX m h a)).sh k * z) + (GPoly.toPoly (T.MX m h) B).coeff δ * z =
                  (GPoly.toPoly (T.MX m h) A).coeff δ * (z′ + f * z)) ∧
              RdeSpecK (algebraMap Cc (T.F m)) (T.MX m h) f (lower' k) := by
          intro _
          refine ⟨by rw [hlcA, hδ']; rfl, by rw [hlcA]; exact leadingCoeff_ne_zero.mpr hA0,
            fun k ↦ ?_⟩
          have hsh : (expShape (T.bX m h a)).sh k = (k : T.F m) * T.bX m h a := rfl
          have hka : ((T.MX m h).sem (O.mul (mcst Fc ks m (k : ℚ)) a))′ = (k : T.F m) * T.bX m h a := by
            rw [(T.MX m h).sem_mul, hcst, Derivation.leibniz, deriv_ratCastK]
            simp only [smul_eq_mul, mul_zero, add_zero]
            push_cast
            rfl
          by_cases hcase : (GPoly.isZero O B || decide ((GPoly.toPoly (T.MX m h) B).natDegree <
              (GPoly.toPoly (T.MX m h) A).natDegree)) = true
          · refine ⟨(T.MX m h).sem (fCode O ⟨O.mul (mcst Fc ks m (k : ℚ)) a, []⟩), fun z ↦ ?_, ?_⟩
            · have hBc0 : (GPoly.toPoly (T.MX m h) B).coeff δ = 0 := by
                simp only [Bool.or_eq_true, decide_eq_true_eq] at hcase
                rcases hcase with hz | hlt
                · rw [(GPoly.isZero_iff _ _).mp hz, coeff_zero]
                · rw [hδ']; exact coeff_eq_zero_of_natDegree_lt hlt
              rw [hBc0, sem_fCode, hka, hsh]
              simp [logSumV]
            · rw [hlowk k hcase]
              exact hlower _ (fun cw hcw ↦ by simp at hcw)
          · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hcase
            obtain ⟨hz, hnlt⟩ := hcase
            have hB0 : GPoly.toPoly (T.MX m h) B ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff _ _).mpr h0)
            have hdeq : (GPoly.toPoly (T.MX m h) A).natDegree =
                (GPoly.toPoly (T.MX m h) B).natDegree := by omega
            obtain ⟨-, hl⟩ := hlead hB0 hdeq
            refine ⟨(T.MX m h).sem (fCode O ⟨O.add hBc (O.mul (mcst Fc ks m (k : ℚ)) a), logsL⟩),
              fun z ↦ ?_, ?_⟩
            · have hlA : (GPoly.toPoly (T.MX m h) A).coeff δ =
                  (GPoly.toPoly (T.MX m h) A).leadingCoeff := by rw [hδ']; rfl
              have hlB : (GPoly.toPoly (T.MX m h) B).coeff δ =
                  (GPoly.toPoly (T.MX m h) B).leadingCoeff := by rw [hδ', hdeq]; rfl
              have hA0' : (GPoly.toPoly (T.MX m h) A).leadingCoeff ≠ 0 :=
                leadingCoeff_ne_zero.mpr hA0
              have hf1 := sem_fCode (T.MX m h) (⟨hBc, logsL⟩ : FRep (LC m))
              have hf2 := sem_fCode (T.MX m h)
                (⟨O.add hBc (O.mul (mcst Fc ks m (k : ℚ)) a), logsL⟩ : FRep (LC m))
              simp only at hf1 hf2
              rw [hlA, hlB, hf2, (T.MX m h).sem_add, map_add, hka, hsh]
              rw [hl] at hf1
              have hq : (GPoly.toPoly (T.MX m h) B).leadingCoeff =
                  (GPoly.toPoly (T.MX m h) A).leadingCoeff *
                    (((T.MX m h).sem hBc)′ + logSumV (T.MX m h) logsL) := by
                rw [← hf1]; field_simp
              linear_combination z * hq
            · rw [hlowk' k (by simp [hz, hnlt])]
              exact hlower _ hokL
        obtain ⟨-, hcomp⟩ := rdeLoop_stageX (ι := algebraMap Cc (T.F m)) (M := T.MX m h)
          (cst := mcst Fc ks m) (DS := expShape (T.bX m h a)) (A := A) (B := B) (Cl := Cs) (δ := δ)
          (hcst := hcst) (w := wk) (hw := hw) (hιd := hιd) (hιrat := hιrat) (by rw [hδ'])
          (by rw [hδ']; exact hBle) false (leadG O A) (leadG O B) lower'
          (fun h' ↦ by cases h') hdiff N (N + 1) (rdeInit Cs.length)
          (rdeInit_soundX (M := T.MX m h) (expShape (T.bX m h a)) A B Cs δ N hC)
          (rdeInit_completeX (algebraMap Cc (T.F m)) (M := T.MX m h) (expShape (T.bX m h a))
            A B Cs δ N)
        rw [← hBs] at hcomp
        obtain ⟨β, hβc, hcoef⟩ := hcomp c hcCs Yv hYN (fun d _ ↦ by rw [hresC, coeff_zero])
        refine ⟨β, hβc, ?_⟩
        ext i
        rw [hcoef i (Nat.zero_le _), finset_sum_coeff]
        simp only [coeff_C_mul]
  obtain ⟨β, hβc, hYvs⟩ := hstage
  have hres' : ∑ l ∈ Finset.range Bs.length, C (algebraMap Cc (T.F m) (β.getD l 0)) *
      resQX (T.MX m h) (expShape (T.bX m h a)) A B Cs (Bs.getD l ([], [])).1
        (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2) = 0 := by
    have := resC_combX (algebraMap Cc (T.F m)) (M := T.MX m h) (expShape (T.bX m h a)) A B Cs
      hιd hιrat Bs c β hβc 0
    rw [add_zero, ← hYvs, hresC,
      show LopX (T.MX m h) (expShape (T.bX m h a)) A B 0 = 0 by simp [LopX, DzX], add_zero] at this
    exact this.symm
  exact T.peOut_completeXE m h (expShape (T.bX m h a)) (by rw [hwb]; rfl) A B Cs Wc.length Q hQ0
    Bs c (fun i hi ↦ hcW i (by omega)) β hβc Yv hYvs hres' y hYv

end Main

/-- **The parametric Risch equation over an exponential level of a mixed tower**: `prdeExpC` is
sound, and complete over the constants, given such a solver one level down. -/
theorem prdeExpX_spec (m : ℕ) (hM : T.MixHyp (m + 1)) {a : LC m} (hk : ks m = .exp a)
    (hc2 : ∀ u ∈ mrel Fc ks m ((MO Fc ks m).deriv a :: gensDC Fc ks m), u.getD 0 0 = 0)
    (lower : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hlower : ∀ fr' : FRep (LC m), FRepOK (T.MX m hM.tr) fr' →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MX m hM.tr) ((T.MX m hM.tr).sem (fCode (MO Fc ks m) fr'))
        (lower fr'))
    (fr : FRep (LC (m + 1))) (hok : FRepOK (T.MP (m + 1) hM.tr) fr) :
    RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hM.tr)
      ((T.MP (m + 1) hM.tr).sem (fCode (MO Fc ks (m + 1)) fr)) (prdeExpC Fc ks m a lower fr) :=
  ⟨fun ws r hr ↦ T.prdeExpX_soundXE m hM hk lower fr ws r hr,
    fun ws c hc z hz ↦ T.prdeExpX_completeXE m hM hk hc2 lower hlower fr hok ws c hc z hz⟩


end MTower

end Curves.MT
