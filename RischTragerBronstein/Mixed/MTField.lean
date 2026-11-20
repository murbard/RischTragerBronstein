import RischTragerBronstein.Mixed.KEMain
import RischTragerBronstein.Mixed.EllBaseChange

/-!
# The fields of the tower above level `0` as rational function fields

For a realization `T` with `tₘ` transcendental over `Fₘ`, `F(m+1) = Fₘ(tₘ) ≃ Fₘ(X)` (`phiS`, through
Mathlib's `algEquivOfTranscendental`). A code of level `m + 1` (a fraction of polynomials over
level-`m` codes) translates to an executable fraction over the computable field `Kₘ` (`trFr`), and
`phiS` sends its value to the image of that fraction under the evaluation `psiF : Kₘ → Fₘ`
(`phiS_val`). This is the identification `C ≃ k(X)` used by the height certificates at levels
`m + 1` (`k = Fₘ`, certificate field `k₀ = Kₘ`).
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)

lemma psiF_coe' (m : ℕ) (h : T.Tr m) (z : KF Fc m) : ((T.psiF m h z : T.F m) : L) = T.psiC m h z :=
  rfl

/-- `F(m+1) = Fₘ(tₘ)` as rings. -/
def eS (m : ℕ) : T.F (m + 1) ≃+* (T.F m)⟮T.ts m⟯ where
  toFun x := ⟨(x : L), (T.mem_F_succ).mp x.2⟩
  invFun x := ⟨(x : L), (T.mem_F_succ).mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **`F(m+1) ≃ Fₘ(X)`.** -/
noncomputable def phiS (m : ℕ) (h : T.Tr (m + 1)) : T.F (m + 1) ≃+* RatFunc (T.F m) :=
  (T.eS m).trans (RatFunc.algEquivOfTranscendental (T.ts m) (h m (Nat.lt_succ_self m))).symm.toRingEquiv

lemma algEquiv_phiS (m : ℕ) (h : T.Tr (m + 1)) (x : T.F (m + 1)) :
    ((RatFunc.algEquivOfTranscendental (T.ts m) (h m (Nat.lt_succ_self m)) (T.phiS m h x) :
      (T.F m)⟮T.ts m⟯) : L) = x := by
  simp only [phiS, RingEquiv.trans_apply]
  rw [show (RatFunc.algEquivOfTranscendental (T.ts m) (h m (Nat.lt_succ_self m)))
      ((RatFunc.algEquivOfTranscendental (T.ts m) (h m (Nat.lt_succ_self m))).symm.toRingEquiv
        (T.eS m x)) = T.eS m x from AlgEquiv.apply_symm_apply _ _]
  rfl

/-- Codes of level `m + 1` as fractions over `Kₘ`. -/
def trFr (m : ℕ) (q : LC (m + 1)) : Fr (KF Fc m) := (q.1.map (trC Fc m), q.2.map (trC Fc m))

lemma transc_psiC (m : ℕ) (h : T.Tr (m + 1)) : RFC.Transc (T.psiC m h.of_succ) (T.ts m) :=
  fun P hP h0 ↦ by
    apply h m (Nat.lt_succ_self m)
    refine ⟨P.map (T.psiF m h.of_succ), (Polynomial.map_ne_zero_iff (T.psiF m h.of_succ).injective).mpr
      hP, ?_⟩
    rw [aeval_def, eval₂_map]
    exact h0

/-- The composite `Kₘ(X) → Fₘ(X) ≃ Fₘ(tₘ) ⊆ L` is the evaluation at `tₘ`. -/
lemma algEquiv_ratMapS (m : ℕ) (h : T.Tr (m + 1)) (r : RatFunc (KF Fc m)) :
    ((RatFunc.algEquivOfTranscendental (T.ts m) (h m (Nat.lt_succ_self m))
      (ratMap (T.psiF m h.of_succ) r) : (T.F m)⟮T.ts m⟯) : L) =
      RFC.evalRF (T.transc_psiC m h) r := by
  have key : ((T.F m)⟮T.ts m⟯).val.toRingHom.comp
      ((RatFunc.algEquivOfTranscendental (T.ts m) (h m (Nat.lt_succ_self m))).toRingEquiv.toRingHom.comp
        (ratMap (T.psiF m h.of_succ))) = RFC.evalRF (T.transc_psiC m h) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (KF Fc m)[X]) (RingHom.ext fun p ↦ ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, ratMap_alg,
      RatFunc.algEquivOfTranscendental_algebraMap, RFC.evalRF_algebraMap]
    show (((aeval (AdjoinSimple.gen (T.F m) (T.ts m)) (p.map (T.psiF m h.of_succ))) :
      (T.F m)⟮T.ts m⟯) : L) = _
    rw [← IntermediateField.coe_val, ← aeval_algHom_apply, IntermediateField.coe_val,
      AdjoinSimple.coe_gen, aeval_def, eval₂_map]
    rfl
  exact congrArg (fun φ : RatFunc (KF Fc m) →+* L ↦ φ r) key

/-- **`phiS` sends the value of a code to its fraction over `Kₘ`.** -/
theorem phiS_val (m : ℕ) (h : T.Tr (m + 1)) (q : LC (m + 1)) :
    T.phiS m h (T.val (m + 1) q) = ratMap (T.psiF m h.of_succ) (Fr.val (trFr m q)) := by
  apply (RatFunc.algEquivOfTranscendental (T.ts m) (h m (Nat.lt_succ_self m))).injective
  apply Subtype.ext
  rw [algEquiv_ratMapS, algEquiv_phiS]
  show T.ev (m + 1) q = _
  rw [← T.psiC_trC (m + 1) h q]
  show RFC.evalHom _ (RFC.mk (q.1.map (trC Fc m)) (q.2.map (trC Fc m))) = _
  rw [RFC.evalHom_mk, Fr.val, trFr, map_div₀, RFC.evalRF_algebraMap, RFC.evalRF_algebraMap]
  rfl

/-- **`phiS` fixes `Fₘ`.** -/
lemma phiS_base (m : ℕ) (h : T.Tr (m + 1)) (c : T.F m) :
    T.phiS m h ⟨(c : L), T.le_succ m c.2⟩ = algebraMap (T.F m) (RatFunc (T.F m)) c := by
  apply (RatFunc.algEquivOfTranscendental (T.ts m) (h m (Nat.lt_succ_self m))).injective
  apply Subtype.ext
  rw [algEquiv_phiS, AlgEquiv.commutes]
  rfl

/-! ### Executable coordinates at level `m + 1` -/

/-- Non-zero denominator of a translated code. -/
def okS (m : ℕ) (q : LC (m + 1)) : Bool := !CPoly.isZero (trFr (Fc := Fc) m q).2

lemma okS_spec {m : ℕ} {q : LC (m + 1)} (h : okS (Fc := Fc) m q = true) : Fr.ok (trFr (Fc := Fc) m q) :=
  fun h0 ↦ by
    rw [← CPoly.isZero_iff] at h0
    simp only [okS, h0, Bool.not_true] at h
    exact absurd h (by decide)

/-- The executable `x`-coordinate `u²(c₃ c_q + c₂/3)`. -/
def xFrS (m : ℕ) (uF : Fr (KF Fc m)) (c3 c2 cq : LC (m + 1)) : Fr (KF Fc m) :=
  Fr.mul (Fr.mul uF uF) (Fr.add (Fr.mul (trFr m c3) (trFr m cq)) (Fr.smulC (1 / 3) (trFr m c2)))

theorem xFrS_spec (m : ℕ) (h : T.Tr (m + 1)) (uF : Fr (KF Fc m)) (ouF : Fr.ok uF)
    (c3 c2 cq : LC (m + 1)) (h3 : okS (Fc := Fc) m c3 = true) (h2 : okS (Fc := Fc) m c2 = true)
    (hq : okS (Fc := Fc) m cq = true) :
    ratMap (T.psiF m h.of_succ) (Fr.val (xFrS m uF c3 c2 cq)) =
      (ratMap (T.psiF m h.of_succ) (Fr.val uF)) ^ 2 *
        (T.phiS m h (T.val (m + 1) c3 * T.val (m + 1) cq) + T.phiS m h (T.val (m + 1) c2) / 3) := by
  have o3 := okS_spec (Fc := Fc) h3
  have o2 := okS_spec (Fc := Fc) h2
  have oq := okS_spec (Fc := Fc) hq
  rw [xFrS, Fr.val_mul (Fr.ok_mul ouF ouF) (Fr.ok_add (Fr.ok_mul o3 oq) (Fr.ok_smulC _ o2)),
    Fr.val_mul ouF ouF, Fr.val_add (Fr.ok_mul o3 oq) (Fr.ok_smulC _ o2), Fr.val_mul o3 oq,
    Fr.val_smulC, map_mul, map_mul, map_add, map_mul, map_mul, map_mul,
    T.phiS_val m h c3, T.phiS_val m h cq, T.phiS_val m h c2]
  simp only [one_div, map_inv₀, map_ofNat, ratMap_alg, Polynomial.map_C]
  ring

/-- Horner evaluation with code coefficients at a fraction. -/
def hornerFrS (m : ℕ) (x : Fr (KF Fc m)) : List (LC (m + 1)) → Fr (KF Fc m)
  | [] => Fr.ofPoly []
  | b :: B => Fr.add (trFr m b) (Fr.mul x (hornerFrS m x B))

lemma hornerFrS_ok (m : ℕ) (x : Fr (KF Fc m)) (hx : Fr.ok x) :
    ∀ B : List (LC (m + 1)), (∀ b ∈ B, okS (Fc := Fc) m b = true) → Fr.ok (hornerFrS m x B)
  | [], _ => Fr.ok_ofPoly _
  | b :: B, hB => Fr.ok_add (okS_spec (Fc := Fc) (hB b List.mem_cons_self))
      (Fr.ok_mul hx (hornerFrS_ok m x hx B fun b' hb' ↦ hB b' (List.mem_cons_of_mem _ hb')))

theorem hornerFrS_spec (m : ℕ) (h : T.Tr (m + 1)) (x : Fr (KF Fc m)) (ox : Fr.ok x)
    (xv : T.F (m + 1)) (hxv : T.phiS m h xv = ratMap (T.psiF m h.of_succ) (Fr.val x)) :
    ∀ B : GPoly (LC (m + 1)), (∀ b ∈ B, okS (Fc := Fc) m b = true) →
      ratMap (T.psiF m h.of_succ) (Fr.val (hornerFrS m x B)) =
        T.phiS m h ((GPoly.toPoly (T.MP (m + 1) h) B).eval xv)
  | [], _ => by
    simp only [hornerFrS, Fr.val_ofPoly, GPoly.toPoly, eval_zero, map_zero]
    simp [CPoly.toPoly]
  | b :: B, hB => by
    have hb := okS_spec (Fc := Fc) (hB b List.mem_cons_self)
    have hB' : ∀ b' ∈ B, okS (Fc := Fc) m b' = true := fun b' hb' ↦ hB b' (List.mem_cons_of_mem _ hb')
    rw [hornerFrS, Fr.val_add hb (Fr.ok_mul ox (hornerFrS_ok m x ox B hB')),
      Fr.val_mul ox (hornerFrS_ok m x ox B hB'), map_add, map_mul,
      hornerFrS_spec m h x ox xv hxv B hB', ← hxv, ← T.phiS_val m h b, ← map_mul, ← map_add,
      GPoly.toPoly_cons, eval_add, eval_C, eval_mul, eval_X, T.sem_MP_F]

/-- The executable base part `u³ c₃ D R / B(c_q)` of a `y`-coordinate. -/
def yBaseFrS (m : ℕ) (uF : Fr (KF Fc m)) (c3 Dc Rc cq : LC (m + 1)) (B : List (LC (m + 1))) :
    Fr (KF Fc m) :=
  Fr.mul (Fr.mul uF (Fr.mul uF uF))
    (Fr.mul (trFr m c3) (Fr.div (Fr.mul (trFr m Dc) (trFr m Rc)) (hornerFrS m (trFr m cq) B)))

theorem yBaseFrS_spec (m : ℕ) (h : T.Tr (m + 1)) (uF : Fr (KF Fc m)) (ouF : Fr.ok uF)
    (c3 Dc Rc cq : LC (m + 1)) (B : GPoly (LC (m + 1))) (h3 : okS (Fc := Fc) m c3 = true)
    (hD : okS (Fc := Fc) m Dc = true) (hR : okS (Fc := Fc) m Rc = true)
    (hq : okS (Fc := Fc) m cq = true) (hB : ∀ b ∈ B, okS (Fc := Fc) m b = true)
    (hB0 : (GPoly.toPoly (T.MP (m + 1) h) B).eval (T.val (m + 1) cq) ≠ 0) :
    ratMap (T.psiF m h.of_succ) (Fr.val (yBaseFrS m uF c3 Dc Rc cq B)) =
      (ratMap (T.psiF m h.of_succ) (Fr.val uF)) ^ 3 *
        T.phiS m h (T.val (m + 1) c3 * (T.val (m + 1) Dc * T.val (m + 1) Rc /
          (GPoly.toPoly (T.MP (m + 1) h) B).eval (T.val (m + 1) cq))) := by
  have o3 := okS_spec (Fc := Fc) h3
  have oD := okS_spec (Fc := Fc) hD
  have oR := okS_spec (Fc := Fc) hR
  have oq := okS_spec (Fc := Fc) hq
  have oH := hornerFrS_ok (Fc := Fc) m _ oq B hB
  have hH := T.hornerFrS_spec m h _ oq (T.val (m + 1) cq) (T.phiS_val m h cq) B hB
  have hH0 : Fr.val (hornerFrS (Fc := Fc) m (trFr (Fc := Fc) m cq) B) ≠ 0 := by
    intro h0'
    apply hB0
    have := hH
    rw [h0', map_zero] at this
    exact (map_eq_zero_iff _ (T.phiS m h).injective).mp this.symm
  rw [yBaseFrS, Fr.val_mul (Fr.ok_mul ouF (Fr.ok_mul ouF ouF))
      (Fr.ok_mul o3 (Fr.ok_div (Fr.ok_mul oD oR) hH0)),
    Fr.val_mul ouF (Fr.ok_mul ouF ouF), Fr.val_mul ouF ouF,
    Fr.val_mul o3 (Fr.ok_div (Fr.ok_mul oD oR) hH0), Fr.val_div (Fr.ok_mul oD oR) oH hH0,
    Fr.val_mul oD oR]
  simp only [map_mul, map_div₀]
  rw [T.phiS_val m h c3, T.phiS_val m h Dc, T.phiS_val m h Rc, hH]
  ring

end MTower

end Curves.MT
