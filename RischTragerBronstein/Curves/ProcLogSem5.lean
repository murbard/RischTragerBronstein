import RischTragerBronstein.Curves.ProcLogSem4

/-!
# The logarithmic remainder vanishes if `f` is elementary

* `lb_h_fin_all`, `lb_h_inf_all`: `φ(h) dX̂` has at most simple poles along every branch;
* `eq_log_of_rows` (**core**): over the constants of a Liouville extension, with verified
  witnesses and a solution of the rows, an elementary `f` satisfies `h = 0`, i.e.
  `f = v′ + ∑ c_j u_j′/u_j` (second kind for `h`, then regularity of the primitive).
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries

section Core

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L) {P : CurveProb F} {ψ₀ : F →+* C}

lemma lb_logs (ws : List (LogWit F)) (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0)
    (hu : ∀ j : Fin (dim F), S.embG g hg Y hY (S.uE ψ₀ (CurveProb.witAt ws j)) ≠ 0) :
    LowerBd (∑ j : Fin (dim F), HahnSeries.C (algebraMap C K (cj ψ₀ ws j)) *
      (LaurentSeries.derivation (S.embG g hg Y hY (S.uE ψ₀ (CurveProb.witAt ws j))) /
        S.embG g hg Y hY (S.uE ψ₀ (CurveProb.witAt ws j)))) (-1) := by
  refine lowerBd_sum _ _ fun j _ ↦ ?_
  have := (lowerBd_C (algebraMap C K (cj ψ₀ ws j))).mul (lowerBd_logDeriv _ (hu j))
  rw [zero_add, ← LaurentSeries.derivation_apply] at this
  exact this

lemma embG_uE_ne_zero (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true) (g : C[X] →+* LaurentSeries K)
    (hg : Function.Injective g) (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0)
    (j : Fin (dim F)) : S.embG g hg Y hY (S.uE ψ₀ (CurveProb.witAt ws j)) ≠ 0 :=
  (map_ne_zero_iff _ (S.embG g hg Y hY).injective).mpr fun h ↦
    S.uE_ne_zero hSF hV _ j (P.witCheck_spec ws hwit j) (congrArg Subtype.val h)

/-- **Simple poles of `h` along every finite branch.** -/
theorem lb_h_fin_all (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true)
    (hrows : ∀ r ∈ P.allRows, ∑ b ∈ Finset.range P.basisIdx.length,
      ψ₀ (cs.getD b 0) * ψ₀ (r.1.getD b 0) = ψ₀ r.2)
    (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx' : x ∈ l) :
    LowerBd (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) x
        (S.root_of_mem hl hx') ⟨S.hL P ψ₀ cs ws, S.hL_mem hC hx cs ws⟩ *
        LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K))) (-1) := by
  rw [S.expand_h hC hx hSF hV cs ws hwit _ (hX_fin N (Nat.pos_of_ne_zero hN) a) _ _
    (fun Q ↦ by rw [SuperData.branchSub_eq_subst]) _ _]
  refine LowerBd.sub ?_ (S.lb_logs ws _ _ _ _ (S.embG_uE_ne_zero hSF hV ws hwit _ _ _ _))
  exact S.simpleFin_all P ψ₀ hSF hV (S.fE P ψ₀) (S.fE_spec P ψ₀ hV) (S.bE P ψ₀)
    (S.bE_spec P ψ₀ hV) (fun b ↦ ψ₀ (cs.getD b 0)) hrows a N hN l hl x hx'

/-- **Simple poles of `h` along every branch above infinity.** -/
theorem lb_h_inf_all (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true)
    (hrows : ∀ r ∈ P.allRows, ∑ b ∈ Finset.range P.basisIdx.length,
      ψ₀ (cs.getD b 0) * ψ₀ (r.1.getD b 0) = ψ₀ r.2)
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx' : x ∈ l) :
    LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) x
        (S.root_of_mem hl hx') ⟨S.hL P ψ₀ cs ws, S.hL_mem hC hx cs ws⟩ *
        LaurentSeries.derivation (single (-(N : ℤ)) (1 : K))) (-1) := by
  rw [S.expand_h hC hx hSF hV cs ws hwit _ (hX_inf N (Nat.pos_of_ne_zero hN)) _ _
    (fun Q ↦ by rw [SuperData.infSub_eq_subst]) _ _]
  refine LowerBd.sub ?_ (S.lb_logs ws _ _ _ _ (S.embG_uE_ne_zero hSF hV ws hwit _ _ _ _))
  exact S.simpleInf_all P ψ₀ hSF hV (S.fE P ψ₀) (S.fE_spec P ψ₀ hV) (S.bE P ψ₀)
    (S.bE_spec P ψ₀ hV) (fun b ↦ ψ₀ (cs.getD b 0)) hrows N hN l hl x hx'

end CurveData

end Core

section Lifted

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

namespace CurveData

variable (S : CurveData C L) {P : CurveProb F} {ψ₀ : F →+* C}

/-- **Core**: an elementary `f` makes the logarithmic remainder vanish. -/
theorem eq_log_of_rows (K : Type*) [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]
    (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true)
    (hrows : ∀ r ∈ P.allRows, ∑ b ∈ Finset.range P.basisIdx.length,
      ψ₀ (cs.getD b 0) * ψ₀ (r.1.getD b 0) = ψ₀ r.2)
    (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) {ι : Type*} (sI : Finset ι) (d w : ι → L)
    (hd : ∀ i ∈ sI, (d i)′ = 0) (hw : ∀ i ∈ sI, w i ≠ 0 ∧ w i ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : (S.fE P ψ₀ : L) = v′ + ∑ i ∈ sI, d i * logDeriv (w i)) :
    S.hL P ψ₀ cs ws = 0 := by
  classical
  have hdc := S.derivClosedXY hC hx
  set h := S.hL P ψ₀ cs ws with hhdef
  have hhm : h ∈ C⟮S.x⟯⟮S.y⟯ := S.hL_mem hC hx cs ws
  set vv := (S.vvE P ψ₀ cs : L) with hvv
  have hvvm : vv ∈ C⟮S.x⟯⟮S.y⟯ := (S.vvE P ψ₀ cs).2
  -- `h` as a Liouville form
  let c' : ι ⊕ Fin (dim F) → L := Sum.elim d fun j ↦ -algebraMap C L (cj ψ₀ ws j)
  let u' : ι ⊕ Fin (dim F) → L := Sum.elim w fun j ↦ (S.uE ψ₀ (CurveProb.witAt ws j) : L)
  have hform : h = (v - vv)′ + ∑ i ∈ sI.disjSum Finset.univ, c' i * logDeriv (u' i) := by
    rw [Finset.sum_disjSum, hhdef, CurveData.hL, heq, map_sub]
    simp only [c', u', Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, logDeriv]
    ring
  have hc' : ∀ i ∈ sI.disjSum Finset.univ, (c' i)′ = 0 := by
    intro i hi
    rcases i with i | j
    · exact hd i (Finset.inl_mem_disjSum.mp hi)
    · simp only [c', Sum.elim_inr, map_neg, deriv_algebraMap, hC, map_zero, neg_zero]
  have hu' : ∀ i ∈ sI.disjSum Finset.univ, u' i ≠ 0 ∧ u' i ∈ C⟮S.x⟯⟮S.y⟯ := by
    intro i hi
    rcases i with i | j
    · exact hw i (Finset.inl_mem_disjSum.mp hi)
    · exact ⟨S.uE_ne_zero hSF hV _ j (P.witCheck_spec ws hwit j), (S.uE ψ₀ _).2⟩
  -- second kind: `h = (v − vv)′`
  have hsk : h = (v - vv)′ :=
    S.curve_second_kind (K := K) hC hx hconst h (v - vv) hhm (sub_mem hv hvvm) _ c' u' hc' hu'
      hform (fun a N hN l hl r hr ↦ S.res_h_fin_all hC hx hSF hV cs ws hwit a N hN l hl r hr)
      (fun N hN l hl r hr ↦ S.res_h_inf_all hC hx hSF hV cs ws hwit N hN l hl r hr)
  -- `v − vv` has no poles
  have heq0 : h = (v - vv)′ + ∑ i ∈ (∅ : Finset Unit),
      algebraMap C L ((fun _ ↦ 0) i) * (((fun _ ↦ (1 : L)) i)′ / (fun _ ↦ (1 : L)) i) := by
    rw [Finset.sum_empty, add_zero]; exact hsk
  have hreg : ∀ (Xh : LaurentSeries K) (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
      (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0),
      LaurentSeries.derivation Xh ≠ 0 → (∀ Q, g Q = substHom Xh Q) →
      LowerBd (S.embG g hg Y hY ⟨h, hhm⟩ * LaurentSeries.derivation Xh) (-1) →
      0 ≤ (S.embG g hg Y hY ⟨v - vv, sub_mem hv hvvm⟩).order := by
    intro Xh g hg Y hY hX hgX hlb
    have hexp := S.expand_liouville Xh hX g hg hgX hC hx Y hY ∅ (fun _ ↦ 0) (fun _ ↦ (1 : L))
      (fun _ ↦ one_mem _) (fun _ ↦ one_ne_zero) (v - vv) h (sub_mem hv hvvm) hhm heq0
    rw [Finset.sum_empty, add_zero] at hexp
    refine order_nonneg_of_lowerBd _ (lowerBd_of_derivation _ ?_)
    rw [← hexp]; exact hlb
  have hfin : S.RegularFinite K ⟨v - vv, sub_mem hv hvvm⟩ := by
    intro a N hN l hl r hr
    exact hreg _ _ _ _ _ (hX_fin N (Nat.pos_of_ne_zero hN) a)
      (fun Q ↦ by rw [SuperData.branchSub_eq_subst])
      (S.lb_h_fin_all hC hx hSF hV cs ws hwit hrows a N hN l hl r hr)
  have hinf : S.RegularInf K ⟨v - vv, sub_mem hv hvvm⟩ := by
    intro N hN l hl r hr
    exact hreg _ _ _ _ _ (hX_inf N (Nat.pos_of_ne_zero hN))
      (fun Q ↦ by rw [SuperData.infSub_eq_subst])
      (S.lb_h_inf_all hC hx hSF hV cs ws hwit hrows N hN l hl r hr)
  have h0 := S.deriv_eq_zero_of_regular (K := K) hC _ hfin hinf
  rw [hsk]
  exact h0

end CurveData

end Lifted

end Curves
