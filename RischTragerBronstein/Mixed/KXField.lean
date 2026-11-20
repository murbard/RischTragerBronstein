import RischTragerBronstein.Mixed.MTTower
import RischTragerBronstein.Mixed.CodeFr
import RischTragerBronstein.Mixed.EllBaseChange

/-!
# The base field of a tower over a linear curve is a rational function field

For a linear base curve `Fc = [c₀, [1]]` (`y = −c₀(x)`), the base level `T.F 0 = Cc(x, y)` equals
`Cc(x)` (`F0_linear`), hence `T.F 0 ≃ Cc(X)` (`phi0`, through Mathlib's `algEquivOfTranscendental`).
The isomorphism sends the value of a level-0 code to its executable fraction over `ℚ`, mapped to
`Cc(X)` (`phi0_sem`). This is the identification `C ≃ k(X)` used by the height certificate of the
Mordell–Weil exception (`KXHeight.toShort`, `EllBaseChange`).
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- `y ∈ Cc(x)` on a linear base. -/
lemma y_mem (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) : T.S.y ∈ Cc⟮T.S.x⟯ := by
  rw [← y_linear T.S Fc T.hSF c0 hFc, psiX_val T.S _ (by simp [Fr.ok, CPoly.toPoly])]
  refine div_mem ?_ ?_ <;>
    simp only [evx, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  · exact Curves.aeval_x_mem T.S _
  · exact Curves.aeval_x_mem T.S _

/-- **On a linear base, `F 0 = Cc(x)`.** -/
theorem F0_linear (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) : T.F 0 = Cc⟮T.S.x⟯ := by
  show (Cc⟮T.S.x⟯⟮T.S.y⟯).restrictScalars Cc = _
  have : (Cc⟮T.S.x⟯)⟮T.S.y⟯ = ⊥ := by
    rw [adjoin_simple_eq_bot_iff, IntermediateField.mem_bot]
    exact ⟨⟨T.S.y, T.y_mem c0 hFc⟩, rfl⟩
  rw [this, restrictScalars_bot_eq_self]

/-- **`T.F 0 ≃ Cc(X)`** on a linear base. -/
noncomputable def phi0 (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) : T.F 0 ≃+* RatFunc Cc :=
  (IntermediateField.equivOfEq (F0_linear T c0 hFc)).toRingEquiv.trans
    (RatFunc.algEquivOfTranscendental T.S.x T.S.htr).symm.toRingEquiv

/-- The composite `ℚ(X) → Cc(X) ≃ Cc(x) ⊆ L` is `ψ`. -/
lemma algEquiv_ratMap (r : RatFunc ℚ) :
    ((RatFunc.algEquivOfTranscendental T.S.x T.S.htr (ratMap (algebraMap ℚ Cc) r) : Cc⟮T.S.x⟯) : L) =
      psiX T.S r := by
  have key : ((Cc⟮T.S.x⟯).val.toRingHom.comp
      ((RatFunc.algEquivOfTranscendental T.S.x T.S.htr).toRingEquiv.toRingHom.comp
        (ratMap (algebraMap ℚ Cc)))) = psiX T.S := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X]) (RingHom.ext fun p ↦ ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, ratMap_alg,
      RatFunc.algEquivOfTranscendental_algebraMap]
    rw [psiX, RatFunc.liftRingHom_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, map_one,
      div_one]
    simp [evx, aeval_algebraMap_apply, Polynomial.aeval_map_algebraMap]
    exact (aeval_algHom_apply ((Cc⟮T.S.x⟯).val.restrictScalars ℚ) (AdjoinSimple.gen Cc T.S.x) p).symm
  exact congrArg (fun φ : RatFunc ℚ →+* L ↦ φ r) key

/-- **`phi0` sends the value of a code to its executable fraction** (mapped to `Cc(X)`). -/
theorem phi0_sem (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) (a : GPoly (GFrac ℚ))
    (ha : ∀ q ∈ a, CPoly.toPoly q.2 ≠ 0) :
    T.phi0 c0 hFc ⟨(cM T.hC T.S T.hx Fc T.hSF).sem a, sem_mem_cF T.hC T.S T.hx Fc T.hSF a⟩ =
      ratMap (algebraMap ℚ Cc) (Fr.val (codeFr (CPoly.neg c0, [1]) a)) := by
  apply (RatFunc.algEquivOfTranscendental T.S.x T.S.htr).injective
  apply Subtype.ext
  rw [algEquiv_ratMap, codeFr_spec T.hC T.S T.hx Fc T.hSF _ (by simp [Fr.ok, CPoly.toPoly])
    (y_linear T.S Fc T.hSF c0 hFc) a ha]
  simp [phi0]

/-- **`phi0` on code values** (via `T.val`). -/
theorem phi0_val (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) (q : GPoly (GFrac ℚ))
    (hq : ∀ r ∈ q, CPoly.toPoly r.2 ≠ 0) :
    T.phi0 c0 hFc (T.val 0 q) = ratMap (algebraMap ℚ Cc) (Fr.val (codeFr (CPoly.neg c0, [1]) q)) := by
  rw [← phi0_sem T c0 hFc q hq]
  rfl

omit [Differential Cc] in
/-- Coefficient maps out of `ℚ` compose. -/
lemma ratMap_comp {k₀ : Type*} [Field k₀] [CharZero k₀] (j : k₀ →+* Cc) (r : RatFunc ℚ) :
    ratMap j (ratMap (algebraMap ℚ k₀) r) = ratMap (algebraMap ℚ Cc) r := by
  have key : (ratMap j).comp (ratMap (algebraMap ℚ k₀)) = ratMap (algebraMap ℚ Cc) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X]) (RingHom.ext fun p ↦ ?_)
    simp only [RingHom.comp_apply, ratMap_alg, Polynomial.map_map]
    congr 2
    exact RingHom.ext_rat _ _
  exact congrArg (fun φ : RatFunc ℚ →+* RatFunc Cc ↦ φ r) key

/-- The executable `x`-coordinate `u²(c₃ c_q + c₂/3)` of a certificate point. -/
def xFr (yF uF : Fr ℚ) (c3 c2 cq : GPoly (GFrac ℚ)) : Fr ℚ :=
  Fr.mul (Fr.mul uF uF) (Fr.add (Fr.mul (codeFr yF c3) (codeFr yF cq)) (Fr.smulC (1 / 3) (codeFr yF c2)))

lemma codes_ok (yF : Fr ℚ) (hy : Fr.ok yF) (q : GPoly (GFrac ℚ)) (hq : ∀ r ∈ q, CPoly.toPoly r.2 ≠ 0) :
    Fr.ok (codeFr yF q) := codeFr_ok yF hy q hq

/-- **The image of the executable `x`-coordinate.** -/
theorem xFr_spec (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) (uF : Fr ℚ) (ouF : Fr.ok uF)
    (c3 c2 cq : GPoly (GFrac ℚ)) (h3 : ∀ r ∈ c3, CPoly.toPoly r.2 ≠ 0)
    (h2 : ∀ r ∈ c2, CPoly.toPoly r.2 ≠ 0) (hq : ∀ r ∈ cq, CPoly.toPoly r.2 ≠ 0) :
    ratMap (algebraMap ℚ Cc) (Fr.val (xFr (CPoly.neg c0, [1]) uF c3 c2 cq)) =
      (ratMap (algebraMap ℚ Cc) (Fr.val uF)) ^ 2 *
        (T.phi0 c0 hFc (T.val 0 c3 * T.val 0 cq) + T.phi0 c0 hFc (T.val 0 c2) / 3) := by
  have hy : Fr.ok ((CPoly.neg c0, [1]) : Fr ℚ) := by simp [Fr.ok, CPoly.toPoly]
  have o3 := codes_ok _ hy c3 h3
  have o2 := codes_ok _ hy c2 h2
  have oq := codes_ok _ hy cq hq
  rw [xFr, Fr.val_mul (Fr.ok_mul ouF ouF) (Fr.ok_add (Fr.ok_mul o3 oq) (Fr.ok_smulC _ o2)),
    Fr.val_mul ouF ouF, Fr.val_add (Fr.ok_mul o3 oq) (Fr.ok_smulC _ o2), Fr.val_mul o3 oq,
    Fr.val_smulC, map_mul, map_mul, map_add, map_mul, map_mul, map_mul,
    T.phi0_val c0 hFc c3 h3, T.phi0_val c0 hFc cq hq, T.phi0_val c0 hFc c2 h2]
  simp only [one_div, map_inv₀, map_ofNat]
  ring

/-- Horner evaluation of a polynomial with code coefficients at an executable fraction. -/
def hornerFr (yF : Fr ℚ) (x : Fr ℚ) : List (LC 0) → Fr ℚ
  | [] => Fr.ofPoly []
  | b :: B => Fr.add (codeFr yF (show GPoly (GFrac ℚ) from b)) (Fr.mul x (hornerFr yF x B))

/-- Non-zero denominators of a code. -/
def codeOK (b : LC 0) : Prop := ∀ r ∈ (show GPoly (GFrac ℚ) from b), CPoly.toPoly r.2 ≠ 0

lemma hornerFr_ok (yF x : Fr ℚ) (hy : Fr.ok yF) (hx : Fr.ok x) :
    ∀ B : List (LC 0), (∀ b ∈ B, codeOK b) → Fr.ok (hornerFr yF x B)
  | [], _ => Fr.ok_ofPoly _
  | b :: B, h => Fr.ok_add (codeFr_ok yF hy _ (h b List.mem_cons_self))
      (Fr.ok_mul hx (hornerFr_ok yF x hy hx B fun b' hb' ↦ h b' (List.mem_cons_of_mem _ hb')))

/-- **Horner evaluation commutes with `phi0`.** -/
theorem hornerFr_spec (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) (h0 : T.Tr 0) (x : Fr ℚ) (ox : Fr.ok x)
    (xv : T.F 0) (hxv : T.phi0 c0 hFc xv = ratMap (algebraMap ℚ Cc) (Fr.val x)) :
    ∀ B : GPoly (LC 0), (∀ b ∈ B, codeOK b) →
      ratMap (algebraMap ℚ Cc) (Fr.val (hornerFr (CPoly.neg c0, [1]) x B)) =
        T.phi0 c0 hFc ((GPoly.toPoly (T.MP 0 h0) B).eval xv)
  | [], _ => by
    simp only [hornerFr, Fr.val_ofPoly, GPoly.toPoly, eval_zero, map_zero]
    simp [CPoly.toPoly]
  | b :: B, h => by
    have hy : Fr.ok ((CPoly.neg c0, [1]) : Fr ℚ) := by simp [Fr.ok, CPoly.toPoly]
    have hb := h b List.mem_cons_self
    have hB : ∀ b' ∈ B, codeOK b' := fun b' hb' ↦ h b' (List.mem_cons_of_mem _ hb')
    rw [hornerFr, Fr.val_add (codeFr_ok _ hy _ hb) (Fr.ok_mul ox (hornerFr_ok _ x hy ox B hB)),
      Fr.val_mul ox (hornerFr_ok _ x hy ox B hB), map_add, map_mul,
      hornerFr_spec c0 hFc h0 x ox xv hxv B hB, ← hxv, ← T.phi0_val c0 hFc _ hb, ← map_mul, ← map_add,
      GPoly.toPoly_cons, eval_add, eval_C, eval_mul, eval_X, T.sem_MP_F]

/-- The executable `ℚ`-part `u³ c₃ D R / B(c_q)` of a `y`-coordinate. -/
def yBaseFr (yF uF : Fr ℚ) (c3 Dc Rc cq : LC 0) (B : List (LC 0)) : Fr ℚ :=
  Fr.mul (Fr.mul uF (Fr.mul uF uF))
    (Fr.mul (codeFr yF (show GPoly (GFrac ℚ) from c3))
      (Fr.div (Fr.mul (codeFr yF (show GPoly (GFrac ℚ) from Dc)) (codeFr yF (show GPoly (GFrac ℚ) from Rc)))
        (hornerFr yF (codeFr yF (show GPoly (GFrac ℚ) from cq)) B)))

/-- **The image of the `ℚ`-part of a `y`-coordinate.** -/
theorem yBaseFr_spec (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) (h0 : T.Tr 0) (uF : Fr ℚ) (ouF : Fr.ok uF)
    (c3 Dc Rc cq : LC 0) (B : GPoly (LC 0)) (h3 : codeOK c3) (hD : codeOK Dc) (hR : codeOK Rc)
    (hq : codeOK cq) (hB : ∀ b ∈ B, codeOK b)
    (hB0 : (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 cq) ≠ 0) :
    ratMap (algebraMap ℚ Cc) (Fr.val (yBaseFr (CPoly.neg c0, [1]) uF c3 Dc Rc cq B)) =
      (ratMap (algebraMap ℚ Cc) (Fr.val uF)) ^ 3 *
        T.phi0 c0 hFc (T.val 0 c3 * (T.val 0 Dc * T.val 0 Rc /
          (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 cq))) := by
  have hy : Fr.ok ((CPoly.neg c0, [1]) : Fr ℚ) := by simp [Fr.ok, CPoly.toPoly]
  have o3 := codeFr_ok _ hy _ h3
  have oD := codeFr_ok _ hy _ hD
  have oR := codeFr_ok _ hy _ hR
  have oq := codeFr_ok _ hy _ hq
  have oH := hornerFr_ok _ _ hy oq B hB
  have hH := T.hornerFr_spec c0 hFc h0 _ oq (T.val 0 cq) (T.phi0_val c0 hFc _ hq) B hB
  have hH0 : Fr.val (hornerFr (CPoly.neg c0, [1]) (codeFr (CPoly.neg c0, [1]) cq) B) ≠ 0 := by
    intro h0'
    apply hB0
    have := hH
    rw [h0', map_zero] at this
    exact (map_eq_zero_iff _ (T.phi0 c0 hFc).injective).mp this.symm
  rw [yBaseFr, Fr.val_mul (Fr.ok_mul ouF (Fr.ok_mul ouF ouF))
      (Fr.ok_mul o3 (Fr.ok_div (Fr.ok_mul oD oR) hH0)),
    Fr.val_mul ouF (Fr.ok_mul ouF ouF), Fr.val_mul ouF ouF,
    Fr.val_mul o3 (Fr.ok_div (Fr.ok_mul oD oR) hH0), Fr.val_div (Fr.ok_mul oD oR) oH hH0,
    Fr.val_mul oD oR]
  simp only [map_mul, map_div₀]
  rw [T.phi0_val c0 hFc _ h3, T.phi0_val c0 hFc _ hD, T.phi0_val c0 hFc _ hR, hH]
  ring

/-- **`phi0` fixes the constants.** -/
lemma phi0_const (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) (c : Cc) :
    T.phi0 c0 hFc (algebraMap Cc (T.F 0) c) = algebraMap Cc (RatFunc Cc) c := by
  simp only [phi0, RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes]

end MTower

end Curves.MT
