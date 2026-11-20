import RischTragerBronstein.Mixed.FrontExpr

/-!
# The front end with a radical of a rational function

Expressions `RE` over `x` with `exp`, `log` and radicals `root n a` (`a^{1/n}`) of rational
functions `a(x)`. If a single radical `root n a` occurs, `a = p/q` is computed (`ratOf`) and the
base curve is `yⁿ = p qⁿ⁻¹` (`curveOf`), on which `y/q` is an `n`-th root of `a`
(`root_value`); the radical is replaced by `y/q` (`toEE`) and `frontDecide` runs on that curve.
Without radicals the base curve is the line `y = x`.

`frontDecideR_sound`: every answer is correct for every realization of the compiled tower over that
curve.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup

/-- Expressions with radicals of rational functions. -/
inductive RE where
  | x
  | cst (c : ℚ)
  | add (a b : RE)
  | mul (a b : RE)
  | neg (a : RE)
  | inv (a : RE)
  | exp (a : RE)
  | log (a : RE)
  | root (n : ℕ) (a : RE)
  deriving DecidableEq, Repr

namespace RE

/-- The radicals of an expression. -/
def radicals : RE → List (ℕ × RE)
  | x => []
  | cst _ => []
  | add a b => radicals a ++ radicals b
  | mul a b => radicals a ++ radicals b
  | neg a => radicals a
  | inv a => radicals a
  | exp a => radicals a
  | log a => radicals a
  | root n a => [(n, a)]

/-- The value of a rational function of `x` (no `exp`, `log`, radicals). -/
def ratOf : RE → Option (GFrac ℚ)
  | x => some ([0, 1], [1])
  | cst c => some ([c], [1])
  | add a b => do let u ← ratOf a; let v ← ratOf b; pure ((xOpsR ℚ).add u v)
  | mul a b => do let u ← ratOf a; let v ← ratOf b; pure ((xOpsR ℚ).mul u v)
  | neg a => (ratOf a).map (xOpsR ℚ).neg
  | inv a => (ratOf a).map (xOpsR ℚ).inv
  | _ => none

/-- Translation, with the radical `rad` replaced by `r`. -/
def toEE (rad : ℕ × RE) (r : EE) : RE → Option EE
  | x => some EE.x
  | cst c => some (EE.cst c)
  | add a b => do let u ← toEE rad r a; let v ← toEE rad r b; pure (EE.add u v)
  | mul a b => do let u ← toEE rad r a; let v ← toEE rad r b; pure (EE.mul u v)
  | neg a => (toEE rad r a).map EE.neg
  | inv a => (toEE rad r a).map EE.inv
  | exp a => (toEE rad r a).map EE.exp
  | log a => (toEE rad r a).map EE.log
  | root n a => if (n, a) = rad then some r else none

end RE

/-- A polynomial in `x` as an expression (Horner). -/
def polyEE (q : CPoly ℚ) : EE := q.foldr (fun c acc ↦ EE.add (EE.cst c) (EE.mul EE.x acc)) (EE.cst 0)

/-- Powers of a polynomial code. -/
def cpow (q : CPoly ℚ) : ℕ → CPoly ℚ
  | 0 => [1]
  | k + 1 => CPoly.mul (cpow q k) q

lemma toPoly_cpow (q : CPoly ℚ) : ∀ k, CPoly.toPoly (cpow q k) = (CPoly.toPoly q) ^ k
  | 0 => by simp [cpow, CPoly.toPoly]
  | k + 1 => by rw [cpow, CPoly.toPoly_mul, toPoly_cpow q k, pow_succ]

/-- The curve `yⁿ − c₀ = 0`. -/
def curveOf (n : ℕ) (c0 : CPoly ℚ) : BPoly ℚ := (CPoly.neg c0 :: List.replicate (n - 1) []) ++ [[1]]

/-- The line `y − x = 0`. -/
def lineFc : BPoly ℚ := [[0, -1], [1]]

/-- **The preparation**: the base curve and the expression over it. -/
def radPrep (e : RE) : Option (BPoly ℚ × EE) :=
  match e.radicals.dedup with
  | [] => (e.toEE (0, RE.x) EE.x).map fun e' ↦ (lineFc, e')
  | [(n, a)] =>
    if 2 ≤ n then
      match a.ratOf with
      | some (p, q) =>
        if CPoly.trim q = [] then none else
        (e.toEE (n, a) (EE.mul EE.y (EE.inv (polyEE q)))).map fun e' ↦
          (curveOf n (CPoly.mul p (cpow q (n - 1))), e')
      | none => none
    else none
  | _ => none

/-- **The front end with radicals.** -/
def frontDecideR (e : RE) (N : ℕ) : Option Bool :=
  (radPrep e).bind fun P ↦ frontDecide P.1 P.2 N

/-! ### The curves are monic -/

lemma toB_replicate_nil {F : Type*} [Field F] (k : ℕ) (W : BPoly F) :
    toB (List.replicate k [] ++ W) = X ^ k * toB W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, toB_cons, ih, pow_succ]
    simp [CPoly.toPoly]; ring

lemma toB_curveOf (n : ℕ) (hn : 1 ≤ n) (c0 : CPoly ℚ) :
    toB (curveOf n c0) = Polynomial.C (CPoly.toPoly (CPoly.neg c0)) + X ^ n := by
  rw [curveOf, List.cons_append, toB_cons, toB_replicate_nil]
  have : toB ([[1]] : BPoly ℚ) = 1 := by simp [CPoly.toPoly]
  rw [this, mul_one, ← pow_succ']
  congr 2; omega

lemma curveOf_facts (n : ℕ) (hn : 1 ≤ n) (c0 : CPoly ℚ) :
    (toB (curveOf n c0)).Monic ∧ (toB (curveOf n c0)).natDegree = cvN (curveOf n c0) := by
  rw [toB_curveOf n hn]
  have hm : (Polynomial.C (CPoly.toPoly (CPoly.neg c0)) + X ^ n : (ℚ[X])[X]).Monic := by
    rw [add_comm]; exact monic_X_pow_add_C _ (by omega)
  refine ⟨hm, ?_⟩
  rw [add_comm, natDegree_X_pow_add_C, cvN, curveOf]
  simp; omega

lemma lineFc_facts : (toB lineFc).Monic ∧ (toB lineFc).natDegree = cvN lineFc := by
  have e : toB lineFc = X + Polynomial.C (-X) := by
    simp [lineFc, toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

/-! ### Soundness -/

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **Every answer of the front end with radicals is correct**: the prepared curve and expression
`radPrep e = (Fc, e')`, and for every realization of the tower of `e'` over `Fc` generated by it,
`∫ e'` is elementary iff the answer is `true`. -/
theorem frontDecideR_sound (e : RE) (N : ℕ) (b : Bool) (h : frontDecideR e N = some b) :
    ∃ Fc e', radPrep e = some (Fc, e') ∧
      ∀ (T : MTower Fc (ksOf Fc e') Cc L), T.n = e'.nodesOf.length →
        (∀ z : L, z ∈ T.F e'.nodesOf.length) →
        (HasElementaryIntegral (evE Fc T e'.nodesOf e') ↔ b = true) := by
  unfold frontDecideR at h
  rcases hP : radPrep e with _ | ⟨Fc, e'⟩
  · rw [hP] at h; cases h
  rw [hP, Option.bind_some] at h
  refine ⟨Fc, e', rfl, fun T hn hgen ↦ ?_⟩
  -- the curve is monic
  have hF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
    unfold radPrep at hP
    split at hP
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hP
      obtain ⟨_, _, rfl, -⟩ := hP
      exact lineFc_facts
    · split_ifs at hP with hn2
      split at hP
      · split_ifs at hP
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hP
        obtain ⟨_, _, rfl, -⟩ := hP
        exact curveOf_facts _ (by omega) _
      · cases hP
    · cases hP
  exact front_sound Fc hF.1 hF.2 e' N b h T hn hgen

/-- **The radical**: on the curve `yⁿ = p qⁿ⁻¹`, `y/q` is an `n`-th root of `p/q`. -/
theorem root_value {Fc' : BPoly ℚ} {ks : (m : ℕ) → KindC m} (n : ℕ) (hn : 1 ≤ n)
    (p q : CPoly ℚ) (T : MTower (curveOf n (CPoly.mul p (cpow q (n - 1)))) ks Cc L)
    (hq : aeval T.S.x ((CPoly.toPoly q).map (algebraMap ℚ Cc)) ≠ 0) :
    (T.S.y / aeval T.S.x ((CPoly.toPoly q).map (algebraMap ℚ Cc))) ^ n =
      aeval T.S.x ((CPoly.toPoly p).map (algebraMap ℚ Cc)) /
        aeval T.S.x ((CPoly.toPoly q).map (algebraMap ℚ Cc)) := by
  have hr := T.S.root
  rw [T.hSF, toB_curveOf n hn] at hr
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    eval_add, eval_pow, eval_X, eval_C, CPoly.toPoly_neg, CPoly.toPoly_mul, toPoly_cpow, eval_neg, eval_mul,
    coe_mapRingHom, Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_pow, map_neg, map_mul,
    map_pow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hr
  set Q := aeval T.S.x ((CPoly.toPoly q).map (algebraMap ℚ Cc))
  set P := aeval T.S.x ((CPoly.toPoly p).map (algebraMap ℚ Cc))
  have hy : T.S.y ^ n = P * Q ^ (n - 1) := by linear_combination hr
  rw [div_pow, hy]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  field_simp

end Curves.MT.Front
