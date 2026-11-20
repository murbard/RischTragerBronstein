import RischTragerBronstein.Algebraic.SuperBase
import RischTragerBronstein.Curves.Integral

/-!
# Orders of lines on `y² = p(x)` (Abel bridge, step B1)

For the line `ℓ = y − (λx + ν)` and a non-branch point `P = (α, β)` (`β ≠ 0`):
`ord_P ℓ = mult_α ((λX + ν)² − p)` if `β = λα + ν` (the line passes through `P`), and `0`
otherwise (`ordAt_line`). Proof: `ℓ · ℓ̄ = (λx + ν)² − p(x)` with `ℓ̄ = −y − (λx + ν)`, and `ℓ̄`
does not vanish at `P` (`ℓ̄(P) = −2β`); a Laurent expansion with non-zero constant term has order `0`
(`order_ofPS_eq_zero`).
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]
variable (S : SuperData C L)

lemma order_ofPS_eq_zero (f : PowerSeries K) (hf : PowerSeries.constantCoeff f ≠ 0) :
    (ofPowerSeries ℤ K f).order = 0 := by
  have hc : (ofPowerSeries ℤ K f).coeff 0 ≠ 0 := by
    have := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) f 0
    simp only [Nat.cast_zero] at this
    rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hf
  have h1 : (ofPowerSeries ℤ K f).order ≤ 0 := HahnSeries.order_le_of_coeff_ne_zero hc
  have h2 : (0 : ℤ) ≤ (ofPowerSeries ℤ K f).order := Curves.order_ofPS_nonneg f
  omega

/-- The generator `y` as an element of `C⟮x⟯⟮y⟯`. -/
noncomputable def yG : C⟮S.x⟯⟮S.y⟯ := AdjoinSimple.gen C⟮S.x⟯ S.y

/-- The line `y − (λx + ν)`. -/
noncomputable def lineF (lam nu : C) : C⟮S.x⟯⟮S.y⟯ :=
  S.yG - S.polyX (Polynomial.C lam * X + Polynomial.C nu)

/-- Its conjugate `−y − (λx + ν)`. -/
noncomputable def lineB (lam nu : C) : C⟮S.x⟯⟮S.y⟯ :=
  -S.yG - S.polyX (Polynomial.C lam * X + Polynomial.C nu)

lemma polyX_val (P : C[X]) : ((S.polyX P : C⟮S.x⟯⟮S.y⟯) : L) = aeval S.x P := by
  letI := algebraAdjoinSimple (F := C) S.x
  change ((algebraMap C[X] C⟮S.x⟯ P : C⟮S.x⟯) : L) = _
  rw [algebraMap_adjoinSimple]

lemma yG_sq (hn2 : S.n = 2) : S.yG ^ 2 = S.polyX S.p := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, polyX_val, yG, AdjoinSimple.coe_gen, ← hn2, S.hy]

lemma line_mul (hn2 : S.n = 2) (lam nu : C) :
    S.lineF lam nu * S.lineB lam nu = S.polyX ((Polynomial.C lam * X + Polynomial.C nu) ^ 2 - S.p) := by
  have h1 : S.polyX ((Polynomial.C lam * X + Polynomial.C nu) ^ 2 - S.p) =
      S.polyX (Polynomial.C lam * X + Polynomial.C nu) ^ 2 - S.polyX S.p := by
    simp [polyX]
  rw [h1, ← S.yG_sq hn2, lineF, lineB]; ring

lemma embXY_polyXL (α β : K) (hβ : β ≠ 0) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (P : C[X]) : S.embXY α β hβ hv (S.polyX P) = ofPowerSeries ℤ K (pShift P α) := by
  rw [polyX, S.embXY_algebraMap, S.embX_algebraMap, shiftHom_eq_pShift]

lemma embXY_lineF (α β : K) (hβ : β ≠ 0) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (lam nu : C) : S.embXY α β hβ hv (S.lineF lam nu) = ofPowerSeries ℤ K
      (branchY S.n S.hn (S.hnK K) S.p α β hβ hv - pShift (Polynomial.C lam * X + Polynomial.C nu) α) := by
  rw [lineF, map_sub, yG, S.embXY_gen, embXY_polyXL, map_sub]

lemma embXY_lineB (α β : K) (hβ : β ≠ 0) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
    (lam nu : C) : S.embXY α β hβ hv (S.lineB lam nu) = ofPowerSeries ℤ K
      (-branchY S.n S.hn (S.hnK K) S.p α β hβ hv - pShift (Polynomial.C lam * X + Polynomial.C nu) α) := by
  rw [lineB, map_sub, map_neg, yG, S.embXY_gen, embXY_polyXL, map_sub, map_neg]

lemma cc_line (α : K) (lam nu : C) :
    PowerSeries.constantCoeff (pShift (Polynomial.C lam * X + Polynomial.C nu) α) =
      algebraMap C K lam * α + algebraMap C K nu := by
  rw [constantCoeff_pShift]; simp

open Classical in
/-- **B1: orders of a line at non-branch points.** -/
theorem ordAt_line [CharZero K] (hn2 : S.n = 2) (lam nu : C)
    (hq : (Polynomial.C lam * X + Polynomial.C nu) ^ 2 - S.p ≠ 0) (α β : K) (hβ : β ≠ 0)
    (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K (S.lineF lam nu) α β =
      if β = algebraMap C K lam * α + algebraMap C K nu then
        ((((Polynomial.C lam * X + Polynomial.C nu) ^ 2 - S.p).map (algebraMap C K)).rootMultiplicity α : ℤ)
      else 0 := by
  have hY := branchY_const S.n S.hn (S.hnK K) S.p α β hβ hv
  split_ifs with hpass
  · -- the conjugate does not vanish
    have hB : S.ordAt K (S.lineB lam nu) α β = 0 := by
      rw [S.ordAt_nb _ α β hβ hv, embXY_lineB]
      refine order_ofPS_eq_zero _ ?_
      rw [map_sub, map_neg, hY, cc_line, ← hpass]
      intro h0; apply hβ
      have : (2 : K) * β = 0 := by linear_combination -h0
      rcases mul_eq_zero.mp this with h2 | h2
      · exact absurd h2 two_ne_zero
      · exact h2
    have hF0 : S.lineF lam nu ≠ 0 := by
      intro h0
      have := S.line_mul hn2 lam nu
      rw [h0, zero_mul] at this
      exact S.polyX_ne_zero hq this.symm
    have hB0 : S.lineB lam nu ≠ 0 := by
      intro h0
      have := S.line_mul hn2 lam nu
      rw [h0, mul_zero] at this
      exact S.polyX_ne_zero hq this.symm
    have hm := S.ordAt_mul (K := K) (α := α) (β := β) hv hF0 hB0
    rw [S.line_mul hn2, S.ordAt_polyX _ hq α β hv, if_neg hβ, one_mul, hB, add_zero] at hm
    exact hm.symm
  · rw [S.ordAt_nb _ α β hβ hv, embXY_lineF]
    refine order_ofPS_eq_zero _ ?_
    rw [map_sub, hY, cc_line]
    exact sub_ne_zero.mpr hpass

lemma embB_lineF (e γ : K) (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) (lam nu : C) :
    S.embB e γ he hγ hγp (S.lineF lam nu) =
      S.branchYe e γ hγ hγp + -branchSub S.n e (Polynomial.C lam * X + Polynomial.C nu) := by
  unfold embB
  rw [lineF, map_sub, yG, S.embG_gen, polyX, S.embG_algebraMap, S.embXG_algebraMap, sub_eq_add_neg]

lemma orderTop_eq_order {f : LaurentSeries K} (hf : f ≠ 0) : f.orderTop = (f.order : WithTop ℤ) :=
  (HahnSeries.order_eq_orderTop_of_ne_zero hf).symm

open Classical in
/-- **B1 at branch points**: at `(e, 0)` (`p(e) = 0`) the line has order
`mult_e ((λX + ν)² − p)` (which is `1`) if it passes through the point, `0` otherwise. -/
theorem ordAt_line_br [CharZero K] (hn2 : S.n = 2) (lam nu : C) (e : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) :
    S.ordAt K (S.lineF lam nu) e 0 =
      if (0 : K) = algebraMap C K lam * e + algebraMap C K nu then
        ((((Polynomial.C lam * X + Polynomial.C nu) ^ 2 - S.p).map (algebraMap C K)).rootMultiplicity e : ℤ)
      else 0 := by
  obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma e he
  rw [S.ordAt_br _ e γ he hγ hγp, embB_lineF]
  have hY : (S.branchYe e γ hγ hγp).orderTop = 1 := by
    rw [orderTop_eq_order (S.branchYe_ne_zero e γ hγ hγp), S.order_branchYe]; rfl
  set Lp : C[X] := Polynomial.C lam * X + Polynomial.C nu with hLp
  have hLe : (Lp.map (algebraMap C K)).eval e = algebraMap C K lam * e + algebraMap C K nu := by
    simp [hLp]
  split_ifs with hpass
  · -- the line passes through the branch point: order `1`, multiplicity `1`
    have hB : 1 < (-branchSub S.n e Lp).orderTop := by
      by_cases hL0 : Lp = 0
      · rw [hL0, map_zero, neg_zero, HahnSeries.orderTop_zero]; exact WithTop.coe_lt_top 1
      have hbs : branchSub S.n e Lp ≠ 0 := (map_ne_zero_iff _ (branchSub_injective S.n S.hn e)).mpr hL0
      rw [HahnSeries.orderTop_neg, orderTop_eq_order hbs, order_branchSub S.n S.hn e Lp hL0]
      have hroot : 0 < (Lp.map (algebraMap C K)).rootMultiplicity e := by
        rw [rootMultiplicity_pos ((Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hL0)]
        rw [IsRoot, hLe, ← hpass]
      rw [hn2]; norm_cast; omega
    have hsum := HahnSeries.orderTop_add_eq_left (lt_of_eq_of_lt hY hB)
    have hord : (S.branchYe e γ hγ hγp + -branchSub S.n e Lp).order = 1 := by
      have := order_eq_of_orderTop_eq (f := S.branchYe e γ hγ hγp + -branchSub S.n e Lp)
        (g := S.branchYe e γ hγ hγp) (by rw [hsum])
      rw [this, S.order_branchYe]
    rw [hord]
    -- the multiplicity is `1`
    have hsep : S.p.Separable := PerfectField.separable_iff_squarefree.mpr S.hsq
    have hd : (Polynomial.derivative (S.p.map (algebraMap C K))).eval e ≠ 0 := by
      rw [derivative_map, eval_map_algebraMap]
      exact hsep.aeval_derivative_ne_zero (by rwa [← eval_map_algebraMap])
    set q := ((Lp ^ 2 - S.p).map (algebraMap C K)) with hqdef
    have hq0 : q.eval e = 0 := by
      rw [hqdef, Polynomial.map_sub, Polynomial.map_pow, eval_sub, eval_pow, hLe, ← hpass, he]; ring
    have hqd : (Polynomial.derivative q).eval e ≠ 0 := by
      rw [hqdef, Polynomial.map_sub, Polynomial.map_pow, derivative_sub, derivative_pow, eval_sub]
      simp only [eval_mul, eval_pow, hLe, ← hpass]
      simpa using hd
    have hqne : q ≠ 0 := by
      intro h0; apply hqd; rw [h0]; simp
    have hpos : 0 < q.rootMultiplicity e := (rootMultiplicity_pos hqne).mpr hq0
    have hle : ¬ 1 < q.rootMultiplicity e := by
      rw [one_lt_rootMultiplicity_iff_isRoot hqne]; exact fun h ↦ hqd h.2
    have : q.rootMultiplicity e = 1 := by omega
    rw [this]; rfl
  · -- the line misses the point: the expansion has non-zero constant term
    have hL0 : Lp ≠ 0 := by
      intro h0; apply hpass; rw [← hLe, h0]; simp
    have hbs : branchSub S.n e Lp ≠ 0 := (map_ne_zero_iff _ (branchSub_injective S.n S.hn e)).mpr hL0
    have hmult : (Lp.map (algebraMap C K)).rootMultiplicity e = 0 := by
      rw [rootMultiplicity_eq_zero_iff]; intro hr; exact absurd (by rw [IsRoot, hLe] at hr; exact hr.symm) hpass
    have hB : (-branchSub S.n e Lp).orderTop = 0 := by
      rw [HahnSeries.orderTop_neg, orderTop_eq_order hbs, order_branchSub S.n S.hn e Lp hL0, hmult]
      rfl
    have hsum : (-branchSub S.n e Lp + S.branchYe e γ hγ hγp).orderTop = 0 := by
      rw [HahnSeries.orderTop_add_eq_left (by rw [hB, hY]; exact WithTop.coe_lt_coe.mpr one_pos), hB]
    rw [add_comm]
    have hne : -branchSub S.n e Lp + S.branchYe e γ hγ hγp ≠ 0 := by
      intro h0; rw [h0, HahnSeries.orderTop_zero] at hsum; exact WithTop.top_ne_coe hsum
    rw [orderTop_eq_order hne] at hsum
    exact_mod_cast hsum

end SuperData

end Differential
