import RischTragerBronstein.Mixed.KZMain

/-!
# Changing the base curve: the translation of codes

For a new base curve `Fc'` and a code `Yc` of `Fc'` (the old `y` as a function on the new curve),
`tauC` translates the codes of every level: `y ↦ Yc` at level `0`, coefficientwise above; `tauK`
translates the kinds of the levels. `tau_evL`: the values correspond whenever they do at level `0`
(`sem_tau0`: the value of `tau0 a` is `a` evaluated at the value of `Yc`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT

section Codes

variable (Fc' : BPoly ℚ) (Yc : GPoly (GFrac ℚ))

/-- `a(x, Yc)` on the new curve. -/
def tau0 (a : GPoly (GFrac ℚ)) : GPoly (GFrac ℚ) :=
  a.foldr (fun c acc ↦ (curveOps Fc').add [c] ((curveOps Fc').mul Yc acc)) (curveOps Fc').zero

/-- The translation of the codes of every level. -/
def tauC : (m : ℕ) → LC m → LC m
  | 0 => tau0 Fc' Yc
  | m + 1 => fun q ↦ (q.1.map (tauC m), q.2.map (tauC m))

/-- The translation of the kinds. -/
def tauK (ks : (m : ℕ) → KindC m) (m : ℕ) : KindC m :=
  match ks m with
  | .prim η => .prim (tauC Fc' Yc m η)
  | .exp a => .exp (tauC Fc' Yc m a)

end Codes

section Eval

variable {L L' : Type*} [Field L] [Field L'] [Differential L] [Differential L']

/-- **Values of translated codes.** -/
lemma tau_evL (Fc' : BPoly ℚ) (Yc : GPoly (GFrac ℚ)) (j : L →+* L') (M0 : LC 0 → L) (M0' : LC 0 → L')
    (h0 : ∀ a, M0' (tau0 Fc' Yc a) = j (M0 a)) (ts : ℕ → L) :
    ∀ (m : ℕ) (q : LC m), evL M0' (fun i ↦ j (ts i)) m (tauC Fc' Yc m q) = j (evL M0 ts m q)
  | 0, q => h0 q
  | m + 1, q => by
    have hP : ∀ p : GPoly (LC m), (p.map (tauC Fc' Yc m)).foldr
        (fun a acc ↦ evL M0' (fun i ↦ j (ts i)) m a + j (ts m) * acc) 0 =
          j (p.foldr (fun a acc ↦ evL M0 ts m a + ts m * acc) 0) := by
      intro p
      induction p with
      | nil => simp
      | cons a p ih =>
        simp only [List.map_cons, List.foldr_cons, ih, tau_evL Fc' Yc j M0 M0' h0 ts m a, map_add,
          map_mul]
    show evPL _ _ m _ / evPL _ _ m _ = _
    rw [evL_succ, map_div₀]
    exact congrArg₂ (· / ·) (hP q.1) (hP q.2)

end Eval

section Sem

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1) (Fc' : BPoly ℚ)
  (hSF : S.F = (toB Fc').map (mapRingHom (algebraMap ℚ Kc)))

/-- **The value of `tau0 a`**: `a` evaluated at `(x, Yc)`. -/
lemma sem_tau0 (Yc : GPoly (GFrac ℚ)) (a : GPoly (GFrac ℚ)) :
    (cM hC S hx Fc' hSF).sem (tau0 Fc' Yc a) =
      (GPoly.toPoly (xM hC S hx) a).eval ((cM hC S hx Fc' hSF).sem Yc) := by
  induction a with
  | nil => simp [tau0, (cM hC S hx Fc' hSF).sem_zero]
  | cons c a ih =>
    simp only [tau0, List.foldr_cons] at ih ⊢
    rw [(cM hC S hx Fc' hSF).sem_add, (cM hC S hx Fc' hSF).sem_mul, ih, GPoly.toPoly_cons,
      sem_cM]
    simp [GPoly.toPoly_cons]

end Sem

end Curves.MT
