import RischTragerBronstein.Mixed.MTTower
import RischTragerBronstein.Computable.NFK

/-!
# The codes of a mixed tower as a computable field

For the base curve `F(x, y) = 0` (`Fc`, irreducible over `ℚ(x)`), the computable fields
`K₀ = ℚ(x)[y]/(F)` (`NFK.NF` over `RatFuncC ℚ`) and `Kₘ₊₁ = Kₘ(t)` (`RatFuncC`) carry the codes:
`trC m : LC m → Kₘ`. For a realization `T` of the tower, `psiC T m` is an injective ring
homomorphism `Kₘ → L` (evaluation at `x, y, t₀, …`) with `psiC (trC q) = T.ev m q` and image in
`T.F m`. This is what makes the torsion oracles over computable fields (`torsOracle`) available on
curves over the fields of the tower.
-/

open Polynomial CPoly IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT

/-- A computable field of characteristic zero. -/
structure CompF (T : Type) where
  fld : Field T
  deq : DecidableEq T
  cz : letI := fld; CharZero T

variable (Fc : BPoly ℚ)

/-- The coefficients of the base curve over `ℚ(x)`. -/
def fKc : CPoly (RFC.RatFuncC ℚ) := Fc.map fun c ↦ RFC.mk c [1]

variable [hF : Fact (Irreducible (toPoly (fKc Fc)))]

/-- The fields `Kₘ` with their structure. -/
@[reducible] def KB : ℕ → Σ T : Type, CompF T
  | 0 => ⟨NFK.NF (fKc Fc), ⟨inferInstance, inferInstance, inferInstance⟩⟩
  | m + 1 =>
    letI := (KB m).2.fld
    letI := (KB m).2.deq
    letI := (KB m).2.cz
    ⟨RFC.RatFuncC (KB m).1, ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- **The field of level `m`.** -/
abbrev KF (m : ℕ) : Type := (KB Fc m).1

instance KF.field (m : ℕ) : Field (KF Fc m) := (KB Fc m).2.fld
instance KF.deq (m : ℕ) : DecidableEq (KF Fc m) := (KB Fc m).2.deq
instance KF.cz (m : ℕ) : CharZero (KF Fc m) := (KB Fc m).2.cz

/-- `ℚ(x)`-fractions. -/
def trX (q : GFrac ℚ) : RFC.RatFuncC ℚ := RFC.mk q.1 q.2

/-- **The translation of codes.** -/
def trC : (m : ℕ) → LC m → KF Fc m
  | 0, a => NFK.mk (fKc Fc) (a.map trX)
  | m + 1, q => (RFC.mk (q.1.map (trC m)) (q.2.map (trC m)) : RFC.RatFuncC (KF Fc m))

/-- Linear base curves `y = g(x)` are irreducible. -/
lemma fKc_irr_linear (c0 : CPoly ℚ) : Irreducible (toPoly (fKc [c0, [1]])) := by
  refine Polynomial.irreducible_of_degree_eq_one ?_
  have h1 : RFC.mk ([1] : CPoly ℚ) [1] = (1 : RFC.RatFuncC ℚ) := rfl
  simp only [fKc, List.map_cons, List.map_nil, toPoly_cons, toPoly_nil, mul_zero, add_zero, h1,
    map_one, mul_one]
  rw [add_comm, degree_X_add_C]


/-- `ℚ(x)`-elements as fractions (canonical representative). -/
def unX (c : RFC.RatFuncC ℚ) : GFrac ℚ := RFC.canon c

/-- **Back to codes.** -/
def unTr : (m : ℕ) → KF Fc m → LC m
  | 0, z => (z.1.map unX : GPoly (GFrac ℚ))
  | m + 1, z =>
    let c := RFC.canon (K := KF Fc m) z
    ((c.1.map (unTr m), c.2.map (unTr m)) : GFrac (LC m))

namespace MTower

universe u

variable {Fc} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L]
  [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

lemma eval₂_mem {K : Type} [CommRing K] (φ : K →+* L) (S : IntermediateField Cc L) (z : L)
    (hz : z ∈ S) (hφ : ∀ c, φ c ∈ S) (P : K[X]) : P.eval₂ φ z ∈ S := by
  rw [eval₂_eq_sum_range]
  exact sum_mem fun i _ ↦ mul_mem (hφ _) (pow_mem hz _)

lemma transc_x : RFC.Transc (algebraMap ℚ L) T.S.x := fun P hP h ↦
  T.S.htr ⟨P.map (algebraMap ℚ Cc), (Polynomial.map_ne_zero_iff (algebraMap ℚ Cc).injective).mpr hP,
    by rw [aeval_map_algebraMap, aeval_def]; exact h⟩

/-- `ℚ(x) → L`. -/
noncomputable def psiX : RFC.RatFuncC ℚ →+* L := RFC.evalHom T.transc_x

lemma psiX_trX (q : GFrac ℚ) :
    T.psiX (trX q) = aeval T.S.x ((toPoly q.1).map (algebraMap ℚ Cc)) /
      aeval T.S.x ((toPoly q.2).map (algebraMap ℚ Cc)) := by
  rw [psiX, trX, RFC.evalHom_mk, aeval_map_algebraMap, aeval_map_algebraMap, aeval_def, aeval_def]

lemma eval₂_toPoly_map {A B E : Type*} [CommRing A] [CommRing E] (g : B → A) (ψ : A →+* E) (z : E) :
    ∀ l : List B, (toPoly (l.map g)).eval₂ ψ z = l.foldr (fun a acc ↦ ψ (g a) + z * acc) 0
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, toPoly_cons, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
      eval₂_toPoly_map g ψ z l, List.foldr_cons]

lemma x_mem0 : T.S.x ∈ T.F 0 :=
  (Cc⟮T.S.x⟯⟮T.S.y⟯).algebraMap_mem ⟨T.S.x, IntermediateField.mem_adjoin_simple_self Cc T.S.x⟩

lemma y_mem0 : T.S.y ∈ T.F 0 := IntermediateField.mem_adjoin_simple_self _ T.S.y

lemma psiX_mem (c : RFC.RatFuncC ℚ) : T.psiX c ∈ T.F 0 := by
  induction c using Quotient.inductionOn with
  | h a =>
    rw [psiX, RFC.evalHom_quot]
    have hq : ∀ c : ℚ, algebraMap ℚ L c ∈ T.F 0 := fun c ↦ by
      rw [show algebraMap ℚ L c = algebraMap Cc L (algebraMap ℚ Cc c) from
        (IsScalarTower.algebraMap_apply ℚ Cc L c)]
      exact T.const_mem 0 _
    exact div_mem (eval₂_mem _ _ _ T.x_mem0 hq _) (eval₂_mem _ _ _ T.x_mem0 hq _)

lemma foldr_curve (Fc' : BPoly ℚ) :
    (((toB Fc').map (mapRingHom (algebraMap ℚ Cc))).map (aeval T.S.x).toRingHom).eval T.S.y =
      Fc'.foldr (fun c acc ↦ aeval T.S.x ((toPoly c).map (algebraMap ℚ Cc)) + T.S.y * acc) 0 := by
  induction Fc' with
  | nil => simp
  | cons c l ih =>
    rw [toB_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_mul,
      eval_add, eval_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X, Polynomial.map_X,
      eval_C, eval_X, ih, List.foldr_cons]
    rfl

lemma psiX_root : (toPoly (fKc Fc)).eval₂ T.psiX T.S.y = 0 := by
  rw [fKc, eval₂_toPoly_map]
  have h := T.S.root
  rw [T.hSF, foldr_curve] at h
  rw [← h]
  congr 1
  funext c acc
  rw [show RFC.mk c [1] = trX (c, [1]) from rfl, psiX_trX]
  simp [CPoly.toPoly]

/-- The evaluation of level `0`. -/
noncomputable def psi0 : KF Fc 0 →+* L :=
  (AdjoinRoot.lift T.psiX T.S.y T.psiX_root).comp (NFK.toARHom (fKc Fc))

lemma psi0_apply (z : KF Fc 0) : T.psi0 z = (toPoly z.1).eval₂ T.psiX T.S.y := by
  show AdjoinRoot.lift T.psiX T.S.y T.psiX_root (AdjoinRoot.mk _ (toPoly z.1)) = _
  rw [AdjoinRoot.lift_mk]

lemma psi0_mem (z : KF Fc 0) : T.psi0 z ∈ T.F 0 := by
  rw [psi0_apply]; exact eval₂_mem _ _ _ T.y_mem0 T.psiX_mem _

lemma psi0_trC (a : LC 0) : T.psi0 (trC Fc 0 a) = T.ev 0 a := by
  show T.psi0 (NFK.mk (fKc Fc) (a.map trX)) =
    (GPoly.toPoly (xModel (algebraMap ℚ Cc) T.hC T.S T.hx) a).eval T.S.y
  rw [psi0, RingHom.comp_apply, show NFK.toARHom (fKc Fc) (NFK.mk (fKc Fc) (a.map trX)) =
    NFK.toAR (fKc Fc) (NFK.mk (fKc Fc) (a.map trX)) from rfl, NFK.toAR_mk, AdjoinRoot.lift_mk]
  have key : ∀ l : List (GFrac ℚ), (toPoly (l.map trX)).eval₂ T.psiX T.S.y =
      (GPoly.toPoly (xModel (algebraMap ℚ Cc) T.hC T.S T.hx) l).eval T.S.y := by
    intro l
    induction l with
    | nil => simp
    | cons q l ih =>
      rw [List.map_cons, toPoly_cons, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, ih,
        GPoly.toPoly_cons, eval_add, eval_mul, eval_C, eval_X, psiX_trX, sem_xModel]
  exact key a

/-- **The evaluations** `Kₘ → L`, with image in `T.F m`. -/
noncomputable def psiS : (m : ℕ) → T.Tr m → {ψ : KF Fc m →+* L // ∀ z, ψ z ∈ T.F m}
  | 0, _ => ⟨T.psi0, T.psi0_mem⟩
  | m + 1, h =>
    let ψ := psiS m h.of_succ
    have hz : RFC.Transc ψ.1 (T.ts m) := fun P hP h0 ↦ by
      let ψ' : KF Fc m →+* T.F m := ψ.1.codRestrict (T.F m).toSubring ψ.2
      apply h m (Nat.lt_succ_self m)
      refine ⟨P.map ψ', (Polynomial.map_ne_zero_iff ψ'.injective).mpr hP, ?_⟩
      rw [aeval_def, eval₂_map]
      exact h0
    ⟨RFC.evalHom hz, fun z ↦ by
      induction z using Quotient.inductionOn with
      | h a =>
        rw [RFC.evalHom_quot]
        have hmem : ∀ c, ψ.1 c ∈ T.F (m + 1) := fun c ↦ T.le_succ m (ψ.2 c)
        exact div_mem (eval₂_mem _ _ _ (T.ts_mem m) hmem _) (eval₂_mem _ _ _ (T.ts_mem m) hmem _)⟩

/-- The evaluation of level `m`. -/
noncomputable def psiC (m : ℕ) (h : T.Tr m) : KF Fc m →+* L := (T.psiS m h).1

lemma psiC_mem (m : ℕ) (h : T.Tr m) (z : KF Fc m) : T.psiC m h z ∈ T.F m := (T.psiS m h).2 z

/-- **The evaluation of the translation is the value of the code.** -/
theorem psiC_trC : ∀ (m : ℕ) (h : T.Tr m) (q : LC m), T.psiC m h (trC Fc m q) = T.ev m q
  | 0, _, q => T.psi0_trC q
  | m + 1, h, q => by
    have IH := psiC_trC m h.of_succ
    show RFC.evalHom _ (RFC.mk (q.1.map (trC Fc m)) (q.2.map (trC Fc m))) = _
    rw [RFC.evalHom_mk, eval₂_toPoly_map, eval₂_toPoly_map]
    show _ = evPL _ T.ts m q.1 / evPL _ T.ts m q.2
    simp only [evPL]
    congr 1
    · congr 1; funext a acc; exact congrArg (fun w ↦ w + T.ts m * acc) (IH a)
    · congr 1; funext a acc; exact congrArg (fun w ↦ w + T.ts m * acc) (IH a)


lemma psiX_unX (c : RFC.RatFuncC ℚ) : T.psiX c = T.psiX (trX (unX c)) := by
  obtain ⟨-, -, -, hc⟩ := RFC.canon_spec c
  rw [psiX, trX, unX, RFC.evalHom_mk, RFC.evalHom_apply, hc, map_div₀, RFC.evalRF_algebraMap,
    RFC.evalRF_algebraMap]

/-- **The codes of an element evaluate to its image.** -/
theorem ev_unTr : ∀ (m : ℕ) (h : T.Tr m) (z : KF Fc m), T.ev m (unTr Fc m z) = T.psiC m h z
  | 0, _, z => by
    show (GPoly.toPoly (xModel (algebraMap ℚ Cc) T.hC T.S T.hx) (z.1.map unX)).eval T.S.y = T.psi0 z
    rw [psi0_apply]
    have key : ∀ l : List (RFC.RatFuncC ℚ),
        (GPoly.toPoly (xModel (algebraMap ℚ Cc) T.hC T.S T.hx) (l.map unX)).eval T.S.y =
          (toPoly l).eval₂ T.psiX T.S.y := by
      intro l
      induction l with
      | nil => simp
      | cons c l ih =>
        rw [List.map_cons, GPoly.toPoly_cons, eval_add, eval_mul, eval_C, eval_X, ih, toPoly_cons,
          eval₂_add, eval₂_mul, eval₂_C, eval₂_X, sem_xModel, psiX_unX, psiX_trX]
    exact key z.1
  | m + 1, h, z => by
    have IH := ev_unTr m h.of_succ
    obtain ⟨-, -, -, hc⟩ := RFC.canon_spec (K := KF Fc m) z
    have hl : ∀ l : List (KF Fc m), evPL (cM T.hC T.S T.hx Fc T.hSF).sem T.ts m
        (l.map (unTr Fc m)) = (toPoly l).eval₂ (T.psiC m h.of_succ) (T.ts m) := by
      intro l
      induction l with
      | nil => simp [evPL]
      | cons a l ih =>
        simp only [evPL, List.map_cons, List.foldr_cons] at ih ⊢
        rw [ih, toPoly_cons, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
        congr 1
        exact IH a
    show evPL _ T.ts m _ / evPL _ T.ts m _ = (T.psiS (m + 1) h).1 z
    rw [psiS]
    dsimp only
    rw [RFC.evalHom_apply, hc, map_div₀, RFC.evalRF_algebraMap, RFC.evalRF_algebraMap]
    have e1 : (unTr Fc (m + 1) z).1 = (RFC.canon z).1.map (unTr Fc m) := rfl
    have e2 : (unTr Fc (m + 1) z).2 = (RFC.canon z).2.map (unTr Fc m) := rfl
    rw [e1, e2]
    erw [hl, hl]
    rfl

end MTower

end Curves.MT
