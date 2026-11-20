import RischTragerBronstein.Curves.ProcLogSem3

/-!
# The logarithmic remainder has no residues and at most simple poles

For verified witnesses (`witCheck`) and a solution of the rows, the remainder
`h = f − v′ − ∑ c_j u_j′/u_j` satisfies, along every branch of every system:

* `res_h_fin_all`, `res_h_inf_all`: `res (φ(h) dX̂) = 0` (certified branches: the divisor check and
  `coord`-expansion of the residues; other branches: transfer; regular points: no poles, and the
  `u_j` are units by the norm check);
* `lb_h_fin_all`, `lb_h_inf_all`: `φ(h) dX̂` has at most a simple pole.
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential LaurentSeries

section Facts

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

namespace CurveProb

variable (P : CurveProb F)

/-- The content of `witOK`. -/
structure WitFacts (w : LogWit F) (j : Fin (dim F)) : Prop where
  m_pos : 0 < w.m
  Q0 : toPoly w.Q ≠ 0
  fin : ∀ ac ∈ P.pts, ∀ yt ∈ ac.2.ys, P.witFinOK w j ac.1 ac.2 yt = true
  inf : ∀ wt ∈ P.inf.ys, P.witInfOK w j wt = true
  cover : coverCheck (mul (normRC P.Fc w.W P.n P.k) w.Q) (P.pts.map Prod.fst) = true

lemma witOK_spec (w : LogWit F) (j : Fin (dim F)) (h : P.witOK w j = true) : P.WitFacts w j := by
  simp only [witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true]
    at h
  obtain ⟨⟨⟨⟨hm, hQ⟩, hfin⟩, hinf⟩, hcov⟩ := h
  exact ⟨hm, fun h0 ↦ by rw [(isZero_iff _).mpr h0] at hQ; exact Bool.noConfusion hQ,
    fun ac hac yt hyt ↦ hfin ac hac yt hyt, hinf, hcov⟩

lemma witCheck_spec (ws : List (LogWit F)) (h : P.witCheck ws = true) (j : Fin (dim F)) :
    P.WitFacts (witAt ws j) j :=
  P.witOK_spec _ j (List.all_eq_true.mp h j (List.mem_finRange j))

end CurveProb

/-- The residue identity `r = ∑_j (b_j/m_j) (m_j coord_j r)`. -/
lemma repr_cLog (ws : List (LogWit F)) (hm : ∀ j : Fin (dim F), 0 < (CurveProb.witAt ws j).m)
    (r : F) :
    ∑ j : Fin (dim F), CurveProb.cLog (CurveProb.witAt ws j) j *
      (((CurveProb.witAt ws j).m * coord j r : ℚ) : F) = r := by
  conv_rhs => rw [repr r]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hm0 : ((CurveProb.witAt ws j).m : F) ≠ 0 := by exact_mod_cast (hm j).ne'
  rw [CurveProb.cLog]
  push_cast
  field_simp

end Facts

section Res

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L) {P : CurveProb F} {ψ₀ : F →+* C}

/-- The coefficient `c_j` in `C`. -/
def cj (ψ₀ : F →+* C) (ws : List (LogWit F)) (j : Fin (dim F)) : C :=
  ψ₀ (CurveProb.cLog (CurveProb.witAt ws j) j)

/-- The remainder `h = f − v′ − ∑ c_j u_j′/u_j`. -/
noncomputable def hL (P : CurveProb F) (ψ₀ : F →+* C) (cs : List F) (ws : List (LogWit F)) : L :=
  (S.fE P ψ₀ : L) - (S.vvE P ψ₀ cs : L)′ - ∑ j : Fin (dim F), algebraMap C L (cj ψ₀ ws j) *
    ((S.uE ψ₀ (CurveProb.witAt ws j) : L)′ / (S.uE ψ₀ (CurveProb.witAt ws j) : L))

lemma hL_mem (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (cs : List F) (ws : List (LogWit F)) :
    S.hL P ψ₀ cs ws ∈ C⟮S.x⟯⟮S.y⟯ := by
  have hdc := S.derivClosedXY hC hx
  refine sub_mem (sub_mem (S.fE P ψ₀).2 (hdc _ (S.vvE P ψ₀ cs).2)) (sum_mem fun j _ ↦ ?_)
  exact mul_mem (S.const_mem _) (div_mem (hdc _ (S.uE ψ₀ _).2) (S.uE ψ₀ _).2)

/-- The witnesses are nonzero. -/
lemma wE_ne_zero (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts)
    (w : LogWit F)
    (hcov : coverCheck (mul (normRC P.Fc w.W P.n P.k) w.Q) (P.pts.map Prod.fst) = true) :
    (S.wE ψ₀ w.W : L) ≠ 0 := by
  have hn := S.natDegree_F_eq P ψ₀ hSF hV
  have h0 := coverCheck_ne_zero _ _ hcov
  rw [toPoly_mul, mul_ne_zero_iff] at h0
  have hR : resultant S.F ((toB w.W).map (mapRingHom ψ₀)) S.F.natDegree (w.W.length - 1) ≠ 0 := by
    have e : resultant S.F ((toB w.W).map (mapRingHom ψ₀)) S.F.natDegree (w.W.length - 1) =
        (resultant (toB P.Fc) (toB w.W) P.n (w.W.length - 1)).map ψ₀ := by
      rw [hn, hSF, resultant_map_map]; rfl
    rw [e, ← toPoly_normRC P.Fc w.W P.n P.k hV.mon hV.deg
      (fun i ↦ by rw [coeff_toB]; exact hV.kF i)]
    exact (Polynomial.map_ne_zero_iff ψ₀.injective).mpr h0.1
  exact S.evXY_ne_zero_of_resultant _ _ (natDegree_map_le.trans (natDegree_toB_le_len w.W)) hR

lemma qE_ne_zero (Q : CPoly F) (hQ : toPoly Q ≠ 0) : (S.qE ψ₀ Q : L) ≠ 0 :=
  S.aeval_x_ne_zero _ ((Polynomial.map_ne_zero_iff ψ₀.injective).mpr hQ)

lemma uE_ne_zero (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts)
    (w : LogWit F) (j : Fin (dim F)) (hw : P.WitFacts w j) : (S.uE ψ₀ w : L) ≠ 0 := by
  rw [uE, IntermediateField.coe_div]
  exact div_ne_zero (S.wE_ne_zero hSF hV w hw.cover) (S.qE_ne_zero w.Q hw.Q0)

/-- **The branch expansion of `h`.** -/
lemma expand_h (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true)
    (Xh : LaurentSeries K) (hX : LaurentSeries.derivation Xh ≠ 0)
    (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ Q, g Q = substHom Xh Q)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) :
    S.embG g hg Y hY ⟨S.hL P ψ₀ cs ws, S.hL_mem hC hx cs ws⟩ * LaurentSeries.derivation Xh =
      S.embG g hg Y hY (S.fE P ψ₀) * LaurentSeries.derivation Xh -
        LaurentSeries.derivation (S.embG g hg Y hY (S.vvE P ψ₀ cs)) -
        ∑ j : Fin (dim F), HahnSeries.C (algebraMap C K (cj ψ₀ ws j)) *
          (LaurentSeries.derivation (S.embG g hg Y hY (S.uE ψ₀ (CurveProb.witAt ws j))) /
            S.embG g hg Y hY (S.uE ψ₀ (CurveProb.witAt ws j))) := by
  have hdc := S.derivClosedXY hC hx
  have hrest : (S.fE P ψ₀ : L) - S.hL P ψ₀ cs ws ∈ C⟮S.x⟯⟮S.y⟯ :=
    sub_mem (S.fE P ψ₀).2 (S.hL_mem hC hx cs ws)
  have hexp := S.expand_liouville Xh hX g hg hgX hC hx Y hY Finset.univ (cj ψ₀ ws)
    (fun j ↦ (S.uE ψ₀ (CurveProb.witAt ws j) : L)) (fun j ↦ (S.uE ψ₀ _).2)
    (fun j ↦ S.uE_ne_zero hSF hV _ j (P.witCheck_spec ws hwit j)) _ _ (S.vvE P ψ₀ cs).2 hrest
    (by rw [hL]; ring)
  have e : (⟨(S.fE P ψ₀ : L) - S.hL P ψ₀ cs ws, hrest⟩ : C⟮S.x⟯⟮S.y⟯) =
      S.fE P ψ₀ - ⟨S.hL P ψ₀ cs ws, S.hL_mem hC hx cs ws⟩ := rfl
  rw [e, map_sub, sub_mul] at hexp
  rw [show S.embG g hg Y hY (S.vvE P ψ₀ cs) = S.embG g hg Y hY ⟨_, (S.vvE P ψ₀ cs).2⟩ from rfl]
  simp only [Subtype.coe_eta] at hexp
  linear_combination -hexp

/-- **The residue of `h`** from the residue of `f` and the orders of the `u_j`. -/
lemma res_h_eq (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true)
    (Xh : LaurentSeries K) (hX : LaurentSeries.derivation Xh ≠ 0)
    (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ Q, g Q = substHom Xh Q)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) :
    LaurentSeries.res (S.embG g hg Y hY ⟨S.hL P ψ₀ cs ws, S.hL_mem hC hx cs ws⟩ *
        LaurentSeries.derivation Xh) =
      LaurentSeries.res (S.embG g hg Y hY (S.fE P ψ₀) * LaurentSeries.derivation Xh) -
        ∑ j : Fin (dim F), algebraMap C K (cj ψ₀ ws j) *
          (((S.embG g hg Y hY (S.wE ψ₀ (CurveProb.witAt ws j).W)).order -
            (S.embG g hg Y hY (S.qE ψ₀ (CurveProb.witAt ws j).Q)).order : ℤ) : K) := by
  rw [S.expand_h hC hx hSF hV cs ws hwit Xh hX g hg hgX Y hY]
  simp only [LaurentSeries.res, HahnSeries.coeff_sub, coeff_derivation, HahnSeries.coeff_sum]
  simp only [show ((-1 : ℤ) + 1) = 0 by norm_num, Int.cast_zero, zero_mul, sub_zero]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hw := P.witCheck_spec ws hwit j
  have hW0 : S.embG g hg Y hY (S.wE ψ₀ (CurveProb.witAt ws j).W) ≠ 0 :=
    (map_ne_zero_iff _ (S.embG g hg Y hY).injective).mpr fun h ↦
      S.wE_ne_zero hSF hV _ hw.cover (congrArg Subtype.val h)
  have hQ0 : S.embG g hg Y hY (S.qE ψ₀ (CurveProb.witAt ws j).Q) ≠ 0 :=
    (map_ne_zero_iff _ (S.embG g hg Y hY).injective).mpr fun h ↦
      S.qE_ne_zero _ hw.Q0 (congrArg Subtype.val h)
  have hu : S.embG g hg Y hY (S.uE ψ₀ (CurveProb.witAt ws j)) =
      S.embG g hg Y hY (S.wE ψ₀ (CurveProb.witAt ws j).W) /
        S.embG g hg Y hY (S.qE ψ₀ (CurveProb.witAt ws j).Q) := by
    rw [uE, map_div₀]
  have hu0 : S.embG g hg Y hY (S.uE ψ₀ (CurveProb.witAt ws j)) ≠ 0 := by
    rw [hu]; exact div_ne_zero hW0 hQ0
  rw [coeff_C_mul', ← LaurentSeries.res, LaurentSeries.derivation_apply, res_logDeriv _ hu0, hu,
    div_eq_mul_inv, HahnSeries.order_mul hW0 (inv_ne_zero hQ0), order_inv_laurent _ hQ0]
  push_cast; ring

/-- The final residue identity. -/
lemma res_combine (ws : List (LogWit F)) (hm : ∀ j : Fin (dim F), 0 < (CurveProb.witAt ws j).m)
    (r : F) (e : Fin (dim F) → ℤ)
    (he : ∀ j, (e j : ℚ) = (CurveProb.witAt ws j).m * coord j r) :
    (algebraMap C K) (ψ₀ r) - ∑ j : Fin (dim F), algebraMap C K (cj ψ₀ ws j) * ((e j : ℤ) : K) =
      0 := by
  rw [sub_eq_zero]
  conv_lhs => rw [← repr_cLog ws hm r]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [cj, map_mul, map_mul, map_ratCast, map_ratCast, ← he j]
  push_cast; rfl

/-- **No residue along a certified finite branch.** -/
lemma res_h_cert_fin (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true)
    (a : F) (c : BranchCert F) (hac : (a, c) ∈ P.pts) (hN : 0 < c.N) (Y : PowerSeries K)
    (hY : (S.F.map (branchSub c.N (algebraMap C K (ψ₀ a)))).eval
      (HahnSeries.ofPowerSeries ℤ K Y) = 0) (yt : CPoly F) (hyt : yt ∈ c.ys)
    (hy : (PowerSeries.X : PowerSeries K) ^ c.prec ∣
      Y - thetaT ((algebraMap C K).comp ψ₀) (toPoly yt)) :
    LaurentSeries.res (S.embG (branchSub c.N (algebraMap C K (ψ₀ a)))
        (branchSub_injective c.N hN _) (HahnSeries.ofPowerSeries ℤ K Y) hY
          ⟨S.hL P ψ₀ cs ws, S.hL_mem hC hx cs ws⟩ *
        LaurentSeries.derivation (HahnSeries.C (algebraMap C K (ψ₀ a)) + single (c.N : ℤ) (1 : K))) =
      0 := by
  rw [S.res_h_eq hC hx hSF hV cs ws hwit _ (hX_fin c.N hN _) _ _
    (fun Q ↦ by rw [SuperData.branchSub_eq_subst]) _ hY]
  obtain ⟨-, hμf, -, hQfl⟩ := hV.prec _ hac
  rw [S.resFin_sem P ψ₀ hSF a c hN Y hY yt hy hμf hQfl _ (S.fE_spec P ψ₀ hV), RingHom.comp_apply]
  have hord : ∀ j : Fin (dim F), ∃ e : ℤ,
      (S.embG (branchSub c.N (algebraMap C K (ψ₀ a))) (branchSub_injective c.N hN _)
        (HahnSeries.ofPowerSeries ℤ K Y) hY (S.wE ψ₀ (CurveProb.witAt ws j).W)).order -
      (S.embG (branchSub c.N (algebraMap C K (ψ₀ a))) (branchSub_injective c.N hN _)
        (HahnSeries.ofPowerSeries ℤ K Y) hY (S.qE ψ₀ (CurveProb.witAt ws j).Q)).order = e ∧
      (e : ℚ) = (CurveProb.witAt ws j).m * coord j (P.resFin a c yt) := fun j ↦ by
    have hw := P.witCheck_spec ws hwit j
    have hok := hw.fin _ hac yt hyt
    simp only [CurveProb.witFinOK] at hok
    cases hoW : ordWFin (CurveProb.witAt ws j).W a c yt with
    | none => rw [hoW] at hok; exact absurd hok (by simp)
    | some o =>
      rw [hoW, decide_eq_true_eq] at hok
      refine ⟨(o : ℤ) - ordQFin (CurveProb.witAt ws j).Q a c.N, ?_, by exact_mod_cast hok⟩
      rw [S.ordWFin_spec ψ₀ _ a c hN Y hY yt hy o hoW, S.embG_qE, ordQFin_spec ψ₀ _ hw.Q0 a c.N hN]
  choose e he using hord
  simp only [fun j ↦ (he j).1]
  exact res_combine ws (fun j ↦ (P.witCheck_spec ws hwit j).m_pos) _ e (fun j ↦ (he j).2)

/-- **No residue along a certified branch above infinity.** -/
lemma res_h_cert_inf (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true) (w : PowerSeries K)
    (hY : (S.F.map (infSub P.inf.N)).eval
      (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) = 0)
    (wt : CPoly F) (hwt : wt ∈ P.inf.ys)
    (hw : (PowerSeries.X : PowerSeries K) ^ P.inf.prec ∣
      w - thetaT ((algebraMap C K).comp ψ₀) (toPoly wt)) :
    LaurentSeries.res (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hV.infN)
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY
          ⟨S.hL P ψ₀ cs ws, S.hL_mem hC hx cs ws⟩ *
        LaurentSeries.derivation (single (-(P.inf.N : ℤ)) (1 : K))) = 0 := by
  rw [S.res_h_eq hC hx hSF hV cs ws hwit _ (hX_inf P.inf.N hV.infN) _ _
    (fun Q ↦ by rw [SuperData.infSub_eq_subst]) _ hY]
  rw [S.resInf_sem P ψ₀ hSF hV.infN w hY wt hw hV.sf hV.Dl hV.okA _ (S.fE_spec P ψ₀ hV),
    RingHom.comp_apply]
  have hord : ∀ j : Fin (dim F), ∃ e : ℤ,
      (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hV.infN)
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY
          (S.wE ψ₀ (CurveProb.witAt ws j).W)).order -
      (S.embG (infSub P.inf.N) (infSub_injective P.inf.N hV.infN)
        (single (-((P.k * P.inf.N : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K w) hY
          (S.qE ψ₀ (CurveProb.witAt ws j).Q)).order = e ∧
      (e : ℚ) = (CurveProb.witAt ws j).m * coord j (P.resInf wt) := fun j ↦ by
    have hwj := P.witCheck_spec ws hwit j
    have hok := hwj.inf wt hwt
    simp only [CurveProb.witInfOK] at hok
    cases hoW : ordWInf (CurveProb.witAt ws j).W P.k P.inf wt with
    | none => rw [hoW] at hok; exact absurd hok (by simp)
    | some o =>
      rw [hoW, decide_eq_true_eq] at hok
      refine ⟨o + ((P.inf.N * degT (CurveProb.witAt ws j).Q : ℕ) : ℤ), ?_, by exact_mod_cast hok⟩
      rw [S.ordWInf_spec ψ₀ _ P.k P.inf hV.infN w hY wt hw o hoW, S.embG_qE,
        order_Q_inf ψ₀ _ hwj.Q0 P.inf.N hV.infN, degT_eq]
      ring
  choose e he using hord
  simp only [fun j ↦ (he j).1]
  exact res_combine ws (fun j ↦ (P.witCheck_spec ws hwit j).m_pos) _ e (fun j ↦ (he j).2)

/-- Away from the special points the norm and `Q` do not vanish. -/
lemma cover_eval_ne (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts)
    (w : LogWit F)
    (hcov : coverCheck (mul (normRC P.Fc w.W P.n P.k) w.Q) (P.pts.map Prod.fst) = true)
    (a : K) (hns : ∀ ac ∈ P.pts, a ≠ algebraMap C K (ψ₀ ac.1)) :
    ((resultant S.F ((toB w.W).map (mapRingHom ψ₀)) S.F.natDegree (w.W.length - 1)).map
        (algebraMap C K)).eval a ≠ 0 ∧
      ((((toPoly w.Q).map ψ₀)).map (algebraMap C K)).eval a ≠ 0 := by
  have hn := S.natDegree_F_eq P ψ₀ hSF hV
  have hev : ((toPoly (mul (normRC P.Fc w.W P.n P.k) w.Q)).map
      ((algebraMap C K).comp ψ₀)).eval a ≠ 0 := by
    intro h0
    obtain ⟨a0, ha0, hae⟩ := coverCheck_spec _ _ hcov _ a h0
    obtain ⟨ac, hac, rfl⟩ := List.mem_map.mp ha0
    exact hns ac hac hae
  have e : resultant S.F ((toB w.W).map (mapRingHom ψ₀)) S.F.natDegree (w.W.length - 1) =
      (toPoly (normRC P.Fc w.W P.n P.k)).map ψ₀ := by
    rw [toPoly_normRC P.Fc w.W P.n P.k hV.mon hV.deg (fun i ↦ by rw [coeff_toB]; exact hV.kF i),
      hn, hSF, resultant_map_map]; rfl
  rw [toPoly_mul, Polynomial.map_mul, eval_mul, mul_ne_zero_iff, ← Polynomial.map_map,
    ← Polynomial.map_map] at hev
  rw [e]
  exact hev

/-- **No residue at a regular point.** -/
lemma res_h_regular (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true)
    (a : K) (hns : ∀ ac ∈ P.pts, a ≠ algebraMap C K (ψ₀ ac.1)) (N : ℕ) (hN : 0 < N)
    (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx' : x ∈ l) :
    LaurentSeries.res (S.embG (branchSub N a) (branchSub_injective N hN a) x (S.root_of_mem hl hx')
        ⟨S.hL P ψ₀ cs ws, S.hL_mem hC hx cs ws⟩ *
        LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K))) = 0 := by
  rw [S.res_h_eq hC hx hSF hV cs ws hwit _ (hX_fin N hN a) _ _
    (fun Q ↦ by rw [SuperData.branchSub_eq_subst]) _ _]
  have hsp : ((toPoly (mul P.D (discRC P.Fc P.n P.k))).map
      ((algebraMap C K).comp ψ₀)).eval a ≠ 0 := by
    intro h0
    obtain ⟨a0, ha0, hae⟩ := coverCheck_spec _ _ hV.cover _ a h0
    obtain ⟨ac, hac, rfl⟩ := List.mem_map.mp ha0
    exact hns ac hac hae
  have hDd : toPoly P.D ∣ toPoly (mul P.D (discRC P.Fc P.n P.k)) := ⟨_, toPoly_mul _ _⟩
  have h1 := (S.lb_regular P ψ₀ hSF hV P.D hDd hV.D0 (S.fE P ψ₀) P.A (S.fE_spec P ψ₀ hV) a hsp
    N hN x (S.root_of_mem hl hx')).mul (lowerBd_single ((N : ℤ) - 1) (N : K))
  rw [SuperData.derivation_branchX N hN a]
  have hr : LaurentSeries.res (S.embG (branchSub N a) (branchSub_injective N hN a) x
      (S.root_of_mem hl hx') (S.fE P ψ₀) * single ((N : ℤ) - 1) (N : K)) = 0 :=
    h1 (-1) (by omega)
  rw [hr, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have hw := P.witCheck_spec ws hwit j
  obtain ⟨hRa, hQa⟩ := S.cover_eval_ne hSF hV _ hw.cover a hns
  rw [S.order_wE_eq_zero _ _ (natDegree_map_le.trans (natDegree_toB_le_len _)) a N hN l hl hRa x
    hx' _ rfl, S.embG_qE, order_branchSub_eq_zero _ a N hN hQa]
  simp

/-- **No residue along any finite branch.** -/
theorem res_h_fin_all (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true)
    (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx' : x ∈ l) :
    LaurentSeries.res (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) x
        (S.root_of_mem hl hx') ⟨S.hL P ψ₀ cs ws, S.hL_mem hC hx cs ws⟩ *
        LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K))) = 0 := by
  by_cases hsp : ∃ ac ∈ P.pts, a = algebraMap C K (ψ₀ ac.1)
  · obtain ⟨⟨a1, c⟩, hac, rfl⟩ := hsp
    obtain ⟨hl0, hN0⟩ := CurveProb.length_ys_of_cert (hV.certs _ hac)
    obtain ⟨y, hy, hs0⟩ := S.certFinSys (K := K) P ψ₀ hSF hV a1 c hac
    obtain ⟨k, hk⟩ := S.fin_rel_list _ c.N hN0 _ hs0 N hN l hl x hx'
    refine transfer_res0 c.N N hN0 (Nat.pos_of_ne_zero hN) _ _ _ _ (hk _)
      (by rw [lsub_Xfin, lsub_Xfin, mul_comm]) ?_
    exact S.res_h_cert_fin hC hx hSF hV cs ws hwit a1 c hac hN0 (y k) (S.root_of_split _ _ hs0 k)
      _ (S.getD_mem_ys P ψ₀ hSF hV c.ys hl0 k) (hy k)
  · push Not at hsp
    exact S.res_h_regular hC hx hSF hV cs ws hwit a hsp N (Nat.pos_of_ne_zero hN) l hl x hx'

/-- **No residue along any branch above infinity.** -/
theorem res_h_inf_all (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true)
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (x : LaurentSeries K) (hx' : x ∈ l) :
    LaurentSeries.res (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) x
        (S.root_of_mem hl hx') ⟨S.hL P ψ₀ cs ws, S.hL_mem hC hx cs ws⟩ *
        LaurentSeries.derivation (single (-(N : ℤ)) (1 : K))) = 0 := by
  obtain ⟨hl0, -⟩ := CurveProb.length_ys_of_cert hV.certInf
  obtain ⟨w, hw, hs0⟩ := S.certInfSys (K := K) P ψ₀ hSF hV
  obtain ⟨k, hk⟩ := S.inf_rel_list P.inf.N hV.infN _ hs0 N hN l hl x hx'
  refine transfer_res0 P.inf.N N hV.infN (Nat.pos_of_ne_zero hN) _ _ _ _ (hk _)
    (by rw [lsub_Xinf, lsub_Xinf, mul_comm]) ?_
  exact S.res_h_cert_inf hC hx hSF hV cs ws hwit (w k) (S.root_of_split _ _ hs0 k) _
    (S.getD_mem_ys P ψ₀ hSF hV P.inf.ys hl0 k) (hw k)

end CurveData

end Res

end Curves
