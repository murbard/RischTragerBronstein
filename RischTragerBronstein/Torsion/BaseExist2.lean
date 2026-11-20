import RischTragerBronstein.Torsion.BaseExist1

/-!
# Base-point data exist (2): from admissible non-special fibres to `Char0Base`

**`exists_char0Base`**: `g ≥ 1` admissible fibres over `F` (split into simple roots of the
curve, `D ≠ 0`, invertible basis matrices) with distinct abscissas, non-special for the integral
basis of a global certificate `T` (`kerSp ≤ span e0`), give base-point data passing all the
characteristic-`0` checks (`Char0Base`): the non-speciality coefficients (`nsCheck_complete`),
left inverses (`detCheck_complete`), a subset certificate at the first fibre (`irrAt_complete`),
the unit at infinity and the Newton values.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Base

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [Field L] [Algebra C L]

lemma ys_nodup_of_det {n : ℕ} {B : Fin n → F[X][X]} (fb : AdmFib B) :
    Function.Injective fb.ys := by
  intro k k' h
  by_contra hne
  apply fb.hdet
  exact Matrix.det_zero_of_row_eq hne (by ext j; simp [h])

/-- **Base-point data from admissible non-special fibres.** -/
theorem exists_char0Base (S : CurveData C L) (ψ : F →+* C) (T : GlobalCert F)
    (hT : T.globalCheck = true) (hαL : T.αL = []) (hyL : T.yL = [])
    (hSF : S.F = (toB T.Fc).map (mapRingHom ψ)) (hn0 : 0 < T.n) {g : ℕ} (hg0 : 0 < g)
    (hg : (∑ j ∈ Finset.range T.n, T.I.δL.getD j 0) + 1 = g + T.n)
    (f : Fin g → AdmFib (fun j : Fin T.n ↦ toB (T.I.Bc.getD j [])))
    (hinj : Function.Injective fun l ↦ (f l).x)
    (hroot : ∀ l k, evalB T.Fc (f l).x ((f l).ys k) = 0)
    (hsimple : ∀ l k, evalB (derivYB T.Fc) (f l).x ((f l).ys k) ≠ 0)
    (hD : ∀ l, Kron.evalC T.I.Dc (f l).x ≠ 0)
    (hns : kerSp (fun j ↦ T.I.δL.getD j 0) g g f (fun _ ↦ ⟨0, hn0⟩) ≤ F ∙ e0 hn0 f) :
    ∃ (xs : List F) (ys : List (List F)) (lam : List (List F)) (Ls : List (List (List F)))
      (irrP : ℕ), Char0Base T xs ys lam Ls irrP ∧ xs = List.ofFn fun l ↦ (f l).x := by
  classical
  have hTf := globalCheck_spec hT
  obtain ⟨-, hmon, hdeg, -⟩ := hTf.shape
  set xs : List F := List.ofFn fun l ↦ (f l).x with hxs
  set ys : List (List F) := List.ofFn fun l ↦ List.ofFn (f l).ys with hys
  have hxl : xs.length = g := by simp [hxs]
  have hyl : ys.length = g := by simp [hys]
  have hxget : ∀ l : Fin g, xs.getD l 0 = (f l).x := fun l ↦ by
    rw [hxs, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hyget : ∀ l : Fin g, ys.getD l [] = List.ofFn (f l).ys := fun l ↦ by
    rw [hys, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hyget' : ∀ (l : Fin g) (k : Fin T.n), (ys.getD l []).getD k 0 = (f l).ys k := fun l k ↦ by
    rw [hyget, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  -- non-speciality coefficients
  obtain ⟨lam, hlam⟩ := nsCheck_complete hn0 T.I.δL T.I.Bc xs ys f (fun l ↦ (hxget l).symm)
    (fun l k ↦ (hyget' l k).symm) hns
  -- left inverses
  obtain ⟨Ls, hLs⟩ := detCheck_complete T.n g T.I.Bc xs ys fun i hi ↦ by
    have e : (Matrix.of fun k j : Fin T.n ↦ detMat T.I.Bc xs ys i k j) =
        Matrix.of fun (k j : Fin T.n) ↦ evalW (toB (T.I.Bc.getD j [])) (f ⟨i, hi⟩).x
          ((f ⟨i, hi⟩).ys k) := by
      ext k j
      have hx' : xs.getD i 0 = (f ⟨i, hi⟩).x := hxget ⟨i, hi⟩
      have hy' : (ys.getD i []).getD k 0 = (f ⟨i, hi⟩).ys k := hyget' ⟨i, hi⟩ k
      simp only [Matrix.of_apply, detMat, evalB_eq]
      rw [hx', hy']
    rw [e]; exact (f ⟨i, hi⟩).hdet
  -- the subset certificate at the first fibre
  set l0 : Fin g := ⟨0, hg0⟩
  have hys0 : ys.getD 0 [] = List.ofFn (f l0).ys := hyget l0
  have hxs0 : xs.getD 0 0 = (f l0).x := hxget l0
  have hmem0 : ∀ y0 ∈ ys.getD 0 [], ∃ k, (f l0).ys k = y0 := fun y0 hy0 ↦ by
    rw [hys0] at hy0; exact List.mem_ofFn.mp hy0
  obtain ⟨p₀, hp₀⟩ := irrAt_complete S T.Fc ψ hSF T.n T.kD hmon hdeg
    (fun q hq ↦ by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
      have := hTf.kF j hj
      rwa [List.getD_eq_getElem _ _ hj] at this)
    (xs.getD 0 0) (ys.getD 0 []) (by rw [hys0]; simp)
    (by rw [hys0]; exact List.nodup_ofFn.mpr (ys_nodup_of_det (f l0)))
    (fun y0 hy0 ↦ by obtain ⟨k, rfl⟩ := hmem0 y0 hy0; rw [hxs0]; exact hroot l0 k)
    (fun y0 hy0 ↦ by obtain ⟨k, rfl⟩ := hmem0 y0 hy0; rw [hxs0]; exact hsimple l0 k)
  set irrP := p₀ + 1
  -- the unit at infinity
  have hinfN : 0 < T.I.infc.N := by
    have hib := hTf.ib
    simp only [ibCheckR, Bool.and_eq_true] at hib
    have hc := hib.1.2
    simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.1.1
  refine ⟨xs, ys, lam, Ls, irrP, ⟨hTf, hαL, hyL, hn0, by rw [hxl]; exact hg, ?_, by rw [hxl, hyl],
    fun i hi ↦ ?_, by rw [hxl]; exact hLs, by rw [hxl]; exact hlam, Nat.succ_pos _,
    hp₀ irrP (Nat.le_succ _), infU0_ne_zero T.I hTf.Dlast hinfN, fun y0 hy0 v hv ↦ ?_,
    globalCheck_ib hT⟩, rfl⟩
  · exact List.nodup_ofFn.mpr hinj
  · rw [hxl] at hi
    set l : Fin g := ⟨i, hi⟩
    have hx' : xs.getD i 0 = (f l).x := hxget l
    have hy' : ys.getD i [] = List.ofFn (f l).ys := hyget l
    rw [hx', hy']
    refine ⟨by simp, List.nodup_ofFn.mpr (ys_nodup_of_det (f l)), hD l, fun k hk ↦ ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
    exact ⟨hroot l ⟨k, hk⟩, hsimple l ⟨k, hk⟩⟩
  · obtain ⟨k, rfl⟩ := hmem0 y0 hy0
    rw [newtonVals_eq T.Fc (xs.getD 0 0) ((f l0).ys k) (by rw [hxs0]; exact hroot l0 k)
      (Nat.succ_pos _) _ [(f l0).ys k] rfl v hv, hxs0]
    exact hsimple l0 k

end Base

end Curves
