import RischTragerBronstein.Mixed.MTWitSound
import RischTragerBronstein.Computable.RationalComplete
import RischTragerBronstein.Liouville.PartialFractionsSplit

/-!
# The base part explicitly, when the curve is a line

When the base curve is a line `y + a₀(x) = 0` (the base field is `ℚ(x)`), the remaining integrand
of `elMW` is a rational function `A/D` of `x` (`lineEval`), and `integrateRational` integrates
it: `A/D = (gn/gd + Q)′ + r/s` with `s` squarefree, `deg r < deg s` (`baseRat_spec`), and
`r/s = ∑_{s(a)=0} (r(a)/s′(a)) · (x − a)′/(x − a)` with constant coefficients in any extension
where `s` splits (`ratLog_explicit`). So the whole antiderivative is explicit.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT

section Generic

variable {E : Type*} [Field E] [CharZero E] [Differential E]

lemma deriv_ratCast_E (q : ℚ) : (q : E)′ = 0 := by
  have hn : ∀ n : ℕ, ((n : E))′ = 0 := fun n ↦ by
    induction n with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, map_add, ih, Derivation.map_one_eq_zero, add_zero]
  have hz : ∀ z : ℤ, ((z : E))′ = 0 := fun z ↦ by
    rcases Int.eq_nat_or_neg z with ⟨k, rfl | rfl⟩
    · exact_mod_cast hn k
    · push_cast; rw [map_neg, hn, neg_zero]
  rw [← Rat.num_div_den q]
  push_cast
  rw [Derivation.leibniz_div, hz, hn]
  simp

/-- `(p(z))′ = p′(z) z′` for `p ∈ ℚ[X]`. -/
lemma aeval_deriv_rat (z : E) (p : ℚ[X]) : (aeval z p)′ = aeval z (derivative p) * z′ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, add_mul]
  | monomial n a =>
    simp only [aeval_monomial, derivative_monomial, eq_ratCast]
    rw [Derivation.leibniz, Derivation.leibniz_pow, deriv_ratCast_E]
    simp only [smul_eq_mul, mul_zero, add_zero]
    rcases n with _ | n
    · simp
    · push_cast
      ring

/-- **Hermite's identity evaluated at `x`** (`x′ = 1`, `x` transcendental over `ℚ`). -/
lemma hermiteCheck_eval (x : E) (hx : x′ = 1) (htr : Transcendental ℚ x) (A D : CPoly ℚ)
    (h : HermiteResult ℚ) (hc : hermiteCheck A D h = true) :
    aeval x (toPoly A) / aeval x (toPoly D) =
      (aeval x (toPoly h.gn) / aeval x (toPoly h.gd))′ + aeval x (toPoly h.b) / aeval x (toPoly h.s) := by
  simp only [hermiteCheck, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
    CPoly.isZero_iff, CPoly.beq_iff] at hc
  obtain ⟨⟨⟨⟨hD, hgd⟩, hs⟩, hid⟩, -⟩ := hc
  have hne : ∀ p : ℚ[X], p ≠ 0 → aeval x p ≠ 0 := fun p hp h0 ↦ htr ⟨p, hp, h0⟩
  have hD' := hne _ hD
  have hgd' := hne _ hgd
  have hs' := hne _ hs
  have e := congrArg (aeval x) hid
  simp only [CPoly.toPoly_mul, CPoly.toPoly_add, CPoly.toPoly_sub, CPoly.toPoly_deriv, map_mul,
    map_add, map_sub] at e
  rw [Derivation.leibniz_div, aeval_deriv_rat, aeval_deriv_rat, hx, mul_one, mul_one]
  simp only [smul_eq_mul]
  field_simp
  linear_combination e

/-- **The logarithmic part of a rational function**: in any differential field where `s`
splits, with `x′ = 1`, `r(x)/s(x) = ∑_{s(a)=0} (r(a)/s′(a)) (x − a)′/(x − a)`, the coefficients
constant. -/
theorem ratLog_explicit [DecidableEq E] (x : E) (hx : x′ = 1) (r s : ℚ[X]) (hsq : Squarefree s)
    (hdeg : r.degree < s.degree) (hsplit : (s.map (algebraMap ℚ E)).Splits)
    (hst : aeval x s ≠ 0) :
    (∀ a ∈ (s.map (algebraMap ℚ E)).roots.toFinset,
      (aeval a r / aeval a (derivative s))′ = 0 ∧ x - a ≠ 0) ∧
    aeval x r / aeval x s = ∑ a ∈ (s.map (algebraMap ℚ E)).roots.toFinset,
      aeval a r / aeval a (derivative s) * logDeriv (x - a) := by
  classical
  have hsep : s.Separable := PerfectField.separable_iff_squarefree.mpr hsq
  have hsepE : (s.map (algebraMap ℚ E)).Separable := hsep.map
  have hstE : eval x (s.map (algebraMap ℚ E)) ≠ 0 := by rwa [eval_map_algebraMap]
  have hpf := eval_div_eq_sum_roots (q := r.map (algebraMap ℚ E)) hsplit hsepE
    (by rw [degree_map, degree_map]; exact hdeg) hstE
  simp only [eval_map_algebraMap, derivative_map] at hpf
  have hroot : ∀ a ∈ (s.map (algebraMap ℚ E)).roots.toFinset, aeval a s = 0 := fun a ha ↦ by
    rw [Multiset.mem_toFinset, mem_roots hsepE.ne_zero, IsRoot.def, eval_map_algebraMap] at ha
    exact ha
  have hkey : ∀ a ∈ (s.map (algebraMap ℚ E)).roots.toFinset, a′ = 0 ∧ x - a ≠ 0 := by
    intro a ha
    have ha0 := hroot a ha
    have hd : aeval a (derivative s) ≠ 0 := hsep.aeval_derivative_ne_zero ha0
    have h1 := aeval_deriv_rat a s
    rw [ha0, Derivation.map_zero] at h1
    refine ⟨(mul_eq_zero.mp h1.symm).resolve_left hd, fun h0 ↦ hstE ?_⟩
    rw [sub_eq_zero] at h0
    rw [eval_map_algebraMap, h0]
    exact ha0
  refine ⟨fun a ha ↦ ⟨?_, (hkey a ha).2⟩, ?_⟩
  · rw [Derivation.leibniz_div, aeval_deriv_rat, aeval_deriv_rat, (hkey a ha).1]
    simp
  · rw [hpf]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [logDeriv, map_sub, hx, (hkey a ha).1, sub_zero, one_div]

end Generic

section Codes

/-- `y = −a₀(x)` on the line `y + a₀(x) = 0`. -/
def lineY (Fc : BPoly ℚ) : GFrac ℚ := (CPoly.smul (-1) (Fc.getD 0 []), [1])

/-- The value of a polynomial in `y` on the line, as a rational function of `x`. -/
def lineEvalP (Fc : BPoly ℚ) (c : GPoly (GFrac ℚ)) : GFrac ℚ :=
  c.foldr (fun ci acc ↦ xOps.add ci (xOps.mul (lineY Fc) acc)) xOps.zero

/-- The value of a level-`0` code on the line, as a rational function of `x`. -/
def lineEval (Fc : BPoly ℚ) (c : LC 0) : GFrac ℚ := lineEvalP Fc (c : GPoly (GFrac ℚ))

/-- The curve is the line `y + a₀(x) = 0`. -/
def isLine (Fc : BPoly ℚ) : Bool := Fc.length == 2 && Fc.getD 1 [] == [1]

/-- **The base part on a line**: the rational integral of the remaining integrand. -/
def baseRat (Fc : BPoly ℚ) (c : LC 0) : Option (RationalIntegral ℚ × GFrac ℚ) :=
  if isLine Fc then
    let R := lineEval Fc c
    if CPoly.isZero R.2 then none else some (integrateRational R.1 R.2, R)
  else none

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma transcendental_x_rat : Transcendental ℚ T.S.x := by
  rintro ⟨p, hp, h0⟩
  apply T.S.htr
  refine ⟨p.map (algebraMap ℚ Cc), (Polynomial.map_ne_zero_iff (algebraMap ℚ Cc).injective).mpr hp, ?_⟩
  rw [aeval_map_algebraMap]
  exact h0

lemma xM_sem_q (q : GFrac ℚ) :
    (xM T.hC T.S T.hx).sem q = aeval T.S.x (toPoly q.1) / aeval T.S.x (toPoly q.2) := by
  rw [sem_xModel, aeval_map_algebraMap, aeval_map_algebraMap]

lemma line_y (hl : isLine Fc = true) : T.S.y = -aeval T.S.x (toPoly (Fc.getD 0 [])) := by
  have hr := T.S.root
  simp only [isLine, Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨hlen, h1⟩ := hl
  obtain ⟨a0, a1, rfl⟩ : ∃ a0 a1, Fc = [a0, a1] := by
    match Fc, hlen with
    | [a0, a1], _ => exact ⟨a0, a1, rfl⟩
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h1
  subst h1
  rw [T.hSF] at hr
  simp only [toB, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_zero, mul_zero, add_zero, eval_add, eval_mul, eval_C, eval_X] at hr
  simp only [List.getD_cons_zero]
  have e1 : (toPoly ([1] : CPoly ℚ)) = 1 := by simp [CPoly.toPoly]
  rw [e1] at hr
  simp only [coe_mapRingHom, Polynomial.map_one, map_one, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, mul_one] at hr
  rw [aeval_map_algebraMap] at hr
  linear_combination hr

/-- The value of a level-`0` code on a line. -/
lemma ev0_lineEval (hl : isLine Fc = true) (c : LC 0) :
    T.ev 0 c = aeval T.S.x (toPoly (lineEval Fc c).1) / aeval T.S.x (toPoly (lineEval Fc c).2) := by
  obtain ⟨d, rfl⟩ : ∃ d : GPoly (GFrac ℚ), (d : LC 0) = c := ⟨c, rfl⟩
  rw [← xM_sem_q]
  show (cM T.hC T.S T.hx Fc T.hSF).sem d = (xM T.hC T.S T.hx).sem (lineEvalP Fc d)
  rw [sem_cM]
  have hy : (xM T.hC T.S T.hx).sem (lineY Fc) = T.S.y := by
    have hneg : ∀ p : CPoly ℚ, toPoly (p.map fun z ↦ -z) = -toPoly p := by
      intro p
      induction p with
      | nil => simp [CPoly.toPoly]
      | cons a p ih => simp only [List.map_cons, CPoly.toPoly_cons, ih, map_neg]; ring
    rw [xM_sem_q, T.line_y hl, lineY]
    simp [CPoly.toPoly, CPoly.smul, hneg]
  induction d with
  | nil => simp [lineEvalP, CField.sem_zero]
  | cons ci rest ih =>
    rw [GPoly.toPoly_cons, eval_add, eval_mul, eval_C, eval_X, ih]
    show _ = (xM T.hC T.S T.hx).sem (xOps.add ci (xOps.mul (lineY Fc) (lineEvalP Fc rest)))
    rw [CField.sem_add, CField.sem_mul, hy]

/-- **The base part on a line, explicitly**: `q = (gn/gd + Q)′ + r/s` at level `0`. -/
theorem baseRat_spec (hl : isLine Fc = true) (c : LC 0) (I : RationalIntegral ℚ) (R : GFrac ℚ)
    (h : baseRat Fc c = some (I, R)) :
    T.ev 0 c = (aeval T.S.x (toPoly I.gn) / aeval T.S.x (toPoly I.gd) +
        aeval T.S.x (toPoly I.Q))′ + aeval T.S.x (toPoly I.r) / aeval T.S.x (toPoly I.s) ∧
      Squarefree (toPoly I.s) ∧ (toPoly I.r).degree < (toPoly I.s).degree ∧
      aeval T.S.x (toPoly I.s) ≠ 0 := by
  simp only [baseRat, hl, if_true] at h
  split_ifs at h with hz
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hD : toPoly (lineEval Fc c).2 ≠ 0 := fun h0 ↦ hz ((CPoly.isZero_iff _).mpr h0)
  set A := (lineEval Fc c).1
  set D := (lineEval Fc c).2
  have hrc := rationalCheck_integrateRational A D hD
  simp only [rationalCheck, Bool.and_eq_true, decide_eq_true_eq] at hrc
  obtain ⟨hh, -⟩ := hrc
  letI : Differential ℚ := ⟨0⟩
  obtain ⟨-, hsq, hdeg, -⟩ := integrateRational_correct (R := ℚ) (fun _ ↦ rfl) A D hD
  have htr := T.transcendental_x_rat
  have hs0 : aeval T.S.x (toPoly (integrateRational A D).s) ≠ 0 := fun h0 ↦
    htr ⟨_, hsq.ne_zero, h0⟩
  refine ⟨?_, hsq, hdeg, hs0⟩
  rw [T.ev0_lineEval hl, hermiteCheck_eval T.S.x T.hx htr A D _ hh, Derivation.map_add,
    aeval_deriv_rat T.S.x (toPoly (integrateRational A D).Q), T.hx, mul_one]
  simp only [CPoly.toPoly_add, CPoly.toPoly_mul, CPoly.toPoly_deriv, map_add, map_mul]
  field_simp
  ring

end MTower

end Curves.MT
