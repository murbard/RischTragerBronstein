import RischTragerBronstein.Algebraic.EllDecideF
import Mathlib.LinearAlgebra.Lagrange

/-!
# From `A / (D y)` to the partial-fraction data of `ellDecideF`

`ellDecideAD` factors `D` over `ℚ` (Kronecker, `Kron.factorQ`), takes the roots of its linear and
quadratic factors in `F = ℚ(√d)`, the ordinates `β = √p(α)` (`sqrtF`) and the residues
`r = A(α) / (D′(α) β)`, and runs `ellDecideF` on `(A div D, [(α, β, r)])`. The partial-fraction
identity `R / D = ∑ R(α) / (D′(α)(x − α))` (`partial_frac`, from Lagrange interpolation) makes it
a decision for `∫ A dx / (D y)`.
-/

open Polynomial Differential

/-- **Partial fractions over the roots** (Lagrange): if `D = c ∏ (X − vᵢ)` with distinct `vᵢ` and
`deg R < #s`, then `R(x) / D(x) = ∑ R(vᵢ) / (D′(vᵢ) (x − vᵢ))` away from the nodes. -/
theorem partial_frac {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → K)
    (hv : Set.InjOn v s) (lc : K) (hlc : lc ≠ 0) (D R : K[X])
    (hD : D = C lc * ∏ i ∈ s, (X - C (v i))) (hR : R.degree < s.card) (x : K)
    (hx : ∀ i ∈ s, x ≠ v i) :
    R.eval x / D.eval x = ∑ i ∈ s, R.eval (v i) / ((derivative D).eval (v i) * (x - v i)) := by
  have hnod : Lagrange.nodal s v = ∏ i ∈ s, (X - C (v i)) := Lagrange.nodal_eq s v
  rw [← hnod] at hD
  have hint := Lagrange.eval_interpolate_not_at_node (fun i ↦ R.eval (v i)) hx
  rw [← Lagrange.eq_interpolate hv hR] at hint
  have hnx : (Lagrange.nodal s v).eval x ≠ 0 := Lagrange.eval_nodal_not_at_node hx
  rw [hint, hD, eval_mul, eval_C, derivative_mul, derivative_C, zero_mul, zero_add, Finset.mul_sum,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hw := Lagrange.nodalWeight_ne_zero hv hi
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hi] at hw ⊢
  have hw' : eval (v i) (derivative (Lagrange.nodal s v)) ≠ 0 := fun h0 ↦ hw (by rw [h0, inv_zero])
  have hxi : x - v i ≠ 0 := sub_ne_zero.mpr (hx i hi)
  rw [eval_mul, eval_C]
  field_simp

namespace EllQuad

open CPoly EllDV

variable {d : ℤ}

local notation "F" => QuadraticAlgebra ℚ (d : ℚ) 0

/-- The roots in `F` of a linear or quadratic rational polynomial (`none` otherwise). -/
def rootsFac (f : CPoly ℚ) : Option (List F) :=
  if Kron.degC f = 1 then some [(((-(f.getD 0 0) / f.getD 1 0 : ℚ)) : F)]
  else if Kron.degC f = 2 then
    let g0 := f.getD 0 0
    let g1 := f.getD 1 0
    let g2 := f.getD 2 0
    match EllAlgo.qsqrt ((g1 ^ 2 - 4 * g0 * g2) / d) with
    | some k => if k = 0 then none else
        some [⟨-g1 / (2 * g2), k / (2 * g2)⟩, ⟨-g1 / (2 * g2), -k / (2 * g2)⟩]
    | none => none
  else none

/-- The roots of a list of factors. -/
def rootsL : List (CPoly ℚ) → Option (List F)
  | [] => some []
  | f :: t =>
    match rootsFac (d := d) f, rootsL t with
    | some l, some m => some (l ++ m)
    | _, _ => none

/-- The roots of `D` in `F`. -/
def rootsD (D : CPoly ℚ) : Option (List F) :=
  if Kron.degC D = 0 then some [] else rootsL (d := d) (Kron.factorQ (Kron.degC D + 1) D)

variable [Fact (¬IsSquare (d : ℚ))]

/-- The partial-fraction data at the roots. -/
def ptsL (a b c : ℤ) (A D : CPoly ℚ) : List F → Option (List (F × F × F))
  | [] => some []
  | α :: t =>
    match sqrtF (d := d) (α ^ 3 + (a : F) * α ^ 2 + (b : F) * α + (c : F)), ptsL a b c A D t with
    | some β, some m => some ((α, β, evalQF A α / (evalQF (CPoly.deriv D) α * β)) :: m)
    | _, _ => none

/-- **The procedure for `∫ A dx / (D y)`** (`none`: `D = 0`, or `D` does not split over `F`
into distinct roots over which `p` takes non-zero square values). -/
def ellDecideAD (a b c : ℤ) (A D : CPoly ℚ) (p0 : ℕ) [NeZero p0] : Option Bool :=
  if isZero D then none else
  match rootsD (d := d) D with
  | none => none
  | some rs =>
    match ptsL a b c A D rs with
    | some pts => ellDecideF a b c (liftF (divMod A D).1) pts p0
    | none => none

/-! ### The roots -/

lemma toPoly_ne_zero_of_degC {f : CPoly ℚ} (h : 1 ≤ Kron.degC f) : toPoly f ≠ 0 := fun h0 ↦ by
  have := (trim_eq_nil_iff f).mpr h0
  simp [Kron.degC, this] at h

lemma toPoly_quad {f : CPoly ℚ} (h : (toPoly f).natDegree ≤ 2) :
    toPoly f = C (f.getD 0 0) + C (f.getD 1 0) * X + C (f.getD 2 0) * X ^ 2 := by
  ext n
  rcases n with _ | _ | _ | n
  · simp [coeff_toPoly]
  · simp [coeff_toPoly]
  · simp [coeff_toPoly]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [coeff_X_pow]

/-- **The roots of one factor.** -/
lemma rootsFac_spec {f : CPoly ℚ} {l : List F} (h : rootsFac (d := d) f = some l) :
    ∃ lc : F, lc ≠ 0 ∧ (toPoly f).map (algebraMap ℚ F) = C lc * (l.map fun r ↦ X - C r).prod := by
  unfold rootsFac at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq] at h; subst h
    have hf0 := toPoly_ne_zero_of_degC (f := f) (by omega)
    have hdeg : (toPoly f).natDegree = 1 := by rw [← Kron.degC_eq f hf0, h1]
    have hq := toPoly_quad (f := f) (by omega)
    have hc2 : f.getD 2 0 = 0 := by
      rw [← coeff_toPoly]; exact coeff_eq_zero_of_natDegree_lt (by omega)
    have hc1 : f.getD 1 0 ≠ 0 := by
      rw [← coeff_toPoly, ← hdeg]; exact leadingCoeff_ne_zero.mpr hf0
    refine ⟨algebraMap ℚ F (f.getD 1 0), (map_ne_zero_iff _ (algebraMap ℚ F).injective).mpr hc1, ?_⟩
    rw [hq, hc2]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_X, Polynomial.map_pow, map_zero,
      C_0, zero_mul, add_zero]
    rw [show ((((-(f.getD 0 0) / f.getD 1 0 : ℚ)) : F)) = algebraMap ℚ F (-(f.getD 0 0) / f.getD 1 0)
      from rfl]
    rw [mul_sub, ← C_mul, ← map_mul, show f.getD 1 0 * (-f.getD 0 0 / f.getD 1 0) = -f.getD 0 0 by
      field_simp, map_neg, C_neg]
    ring
  · dsimp only at h
    split at h
    · rename_i k hk
      split_ifs at h with hk0
      simp only [Option.some.injEq] at h; subst h
      have hk2 := EllAlgo.qsqrt_spec hk
      have hf0 := toPoly_ne_zero_of_degC (f := f) (by omega)
      have hdeg : (toPoly f).natDegree = 2 := by rw [← Kron.degC_eq f hf0, h2]
      have hq := toPoly_quad (f := f) (by omega)
      have hc2 : f.getD 2 0 ≠ 0 := by
        rw [← coeff_toPoly, ← hdeg]; exact leadingCoeff_ne_zero.mpr hf0
      set g0 := f.getD 0 0
      set g1 := f.getD 1 0
      set g2 := f.getD 2 0
      have hd : (d : ℚ) ≠ 0 := fun h0 ↦ (Fact.out : ¬IsSquare (d : ℚ)) ⟨0, by rw [h0]; ring⟩
      set r1 : F := ⟨-g1 / (2 * g2), k / (2 * g2)⟩
      set r2 : F := ⟨-g1 / (2 * g2), -k / (2 * g2)⟩
      have e1 : algebraMap ℚ F g2 * (r1 + r2) = -algebraMap ℚ F g1 := by
        ext
        · simp [r1, r2, Algebra.algebraMap_eq_smul_one]; field_simp; ring
        · simp [r1, r2, Algebra.algebraMap_eq_smul_one]; right; ring
      have e2 : algebraMap ℚ F g2 * (r1 * r2) = algebraMap ℚ F g0 := by
        have hdk : (d : ℚ) * k ^ 2 = g1 ^ 2 - 4 * g0 * g2 := by
          rw [hk2]; field_simp
        ext
        · simp [r1, r2, Algebra.algebraMap_eq_smul_one]
          field_simp
          linear_combination (-1 : ℚ) * hdk
        · simp [r1, r2, Algebra.algebraMap_eq_smul_one]; right; ring
      refine ⟨algebraMap ℚ F g2, (map_ne_zero_iff _ (algebraMap ℚ F).injective).mpr hc2, ?_⟩
      rw [hq]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_X, Polynomial.map_pow]
      rw [show algebraMap ℚ F g0 = algebraMap ℚ F g2 * (r1 * r2) from e2.symm,
        show algebraMap ℚ F g1 = -(algebraMap ℚ F g2 * (r1 + r2)) by rw [e1]; ring]
      simp only [map_neg, map_mul, map_add]
      ring
    · cases h

lemma rootsL_spec : ∀ {fs : List (CPoly ℚ)} {rs : List F}, rootsL (d := d) fs = some rs →
    ∃ lc : F, lc ≠ 0 ∧ ((fs.map toPoly).prod).map (algebraMap ℚ F) =
      C lc * (rs.map fun r ↦ X - C r).prod
  | [], rs, h => by
    simp only [rootsL, Option.some.injEq] at h; subst h
    exact ⟨1, one_ne_zero, by simp⟩
  | f :: t, rs, h => by
    simp only [rootsL] at h
    split at h
    · rename_i l m h1 h2
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨c1, hc1, e1⟩ := rootsFac_spec h1
      obtain ⟨c2, hc2, e2⟩ := rootsL_spec h2
      refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
      rw [List.map_cons, List.prod_cons, Polynomial.map_mul, e1, e2, List.map_append,
        List.prod_append, C_mul]
      ring
    · cases h

/-- **`D` splits over `F` along the computed roots.** -/
lemma rootsD_spec {D : CPoly ℚ} (hD : toPoly D ≠ 0) {rs : List F} (h : rootsD (d := d) D = some rs) :
    ∃ lc : F, lc ≠ 0 ∧ (toPoly D).map (algebraMap ℚ F) = C lc * (rs.map fun r ↦ X - C r).prod := by
  unfold rootsD at h
  split_ifs at h with h0
  · simp only [Option.some.injEq] at h; subst h
    have hdeg : (toPoly D).natDegree = 0 := by rw [← Kron.degC_eq D hD, h0]
    refine ⟨algebraMap ℚ F ((toPoly D).coeff 0), ?_, ?_⟩
    · refine (map_ne_zero_iff _ (algebraMap ℚ F).injective).mpr fun h1 ↦ hD ?_
      rw [eq_C_of_natDegree_eq_zero hdeg, h1, C_0]
    · conv_lhs => rw [eq_C_of_natDegree_eq_zero hdeg]
      simp
  · have hpos : 0 < (toPoly D).natDegree := by rw [← Kron.degC_eq D hD]; omega
    obtain ⟨-, k, hk, hDk⟩ := Kron.factorQ_spec (Kron.degC D + 1) D hpos
      (by rw [← Kron.degC_eq D hD]; omega)
    obtain ⟨lc, hlc, e⟩ := rootsL_spec h
    refine ⟨algebraMap ℚ F k * lc, mul_ne_zero ((map_ne_zero_iff _ (algebraMap ℚ F).injective).mpr hk)
      hlc, ?_⟩
    rw [hDk, Polynomial.map_mul, map_C, e, C_mul]
    ring

/-- **The sum over the partial-fraction data.** -/
lemma ptsL_sum {a b c : ℤ} {A D : CPoly ℚ} {E : Type*} [Field E] (ιE : F →+* E) (x : E) :
    ∀ {rs : List F} {pts : List (F × F × F)}, ptsL a b c A D rs = some pts →
    (∀ q ∈ pts, q.2.1 ≠ 0) →
    pts.map Prod.fst = rs ∧
      (pts.map fun q ↦ ιE (q.2.2 * q.2.1) / (x - ιE q.1)).sum =
      (rs.map fun α ↦ ιE (evalQF A α / evalQF (CPoly.deriv D) α) / (x - ιE α)).sum
  | [], pts, h, _ => by
    simp only [ptsL, Option.some.injEq] at h; subst h; simp
  | α :: t, pts, h, hβ => by
    simp only [ptsL] at h
    split at h
    · rename_i β m h1 h2
      simp only [Option.some.injEq] at h; subst h
      have hβ0 : β ≠ 0 := hβ _ List.mem_cons_self
      obtain ⟨e1, e2⟩ := ptsL_sum ιE x h2 fun q hq ↦ hβ q (List.mem_cons_of_mem _ hq)
      refine ⟨by simp [e1], ?_⟩
      simp only [List.map_cons, List.sum_cons, e2]
      congr 3
      field_simp
    · cases h


section Spec

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma validF_of_some {a b c : ℤ} {B : CPoly F} {pts : List (F × F × F)} {p0 : ℕ} [NeZero p0]
    {ans : Bool} (h : ellDecideF (d := d) a b c B pts p0 = some ans) :
    validF (d := d) a b c pts = true := by
  unfold ellDecideF at h
  split_ifs at h with hv
  exact hv

set_option maxHeartbeats 3200000 in
/-- **The integrand as partial fractions over the roots.** -/
lemma integrand_pf (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : F →+* Kc)
    (A D : CPoly ℚ) (hD0 : toPoly D ≠ 0) (rs : List F) (hnd : rs.Nodup) (lc : F) (hlc : lc ≠ 0)
    (hsplit : (toPoly D).map (algebraMap ℚ F) = C lc * (rs.map fun r ↦ X - C r).prod) :
    aeval x (toPoly A) / (aeval x (toPoly D) * y) =
      (evF ι x (liftF (divMod A D).1) + (rs.map fun α ↦ algebraMap Kc E
        (ι (evalQF A α / evalQF (CPoly.deriv D) α)) / (x - algebraMap Kc E (ι α))).sum) / y := by
  classical
  set ιE : F →+* E := (algebraMap Kc E).comp ι with hιE
  have hmapE : ∀ P : ℚ[X], (P.map (algebraMap ℚ F)).map ιE = P.map (algebraMap ℚ E) := by
    intro P; rw [Polynomial.map_map]; congr 1; exact RingHom.ext_rat _ _
  have haev : ∀ P : ℚ[X], aeval x P = (P.map (algebraMap ℚ E)).eval x := fun P ↦ by
    rw [eval_map_algebraMap]
  have haevF : ∀ (P : ℚ[X]) (z : F), ιE (aeval z P) = (P.map (algebraMap ℚ E)).eval (ιE z) := by
    intro P z
    rw [eval_map_algebraMap]
    exact (aeval_algHom_apply ιE.toRatAlgHom z P).symm
  set n := rs.length
  set v : Fin n → E := fun i ↦ ιE rs[i]
  have hv : Set.InjOn v ↑(Finset.univ : Finset (Fin n)) := by
    intro i _ j _ hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp (ιE.injective hij))
  set DE := (toPoly D).map (algebraMap ℚ E)
  have hDE : DE = C (ιE lc) * ∏ i : Fin n, (X - C (v i)) := by
    show (toPoly D).map (algebraMap ℚ E) = _
    rw [← hmapE, hsplit, Polynomial.map_mul, map_C, EllAlgo.prod_map_eq_fin, Polynomial.map_prod]
    simp [v]
    left; rfl
  -- the division
  set q := (divMod A D).1
  set R := (divMod A D).2
  have hAR : toPoly A = toPoly q * toPoly D + toPoly R := divMod_spec A D
  have hRdeg := divMod_degree_lt A D hD0
  have hDn : (toPoly D).natDegree = n := by
    have h1 : DE.natDegree = (toPoly D).natDegree :=
      natDegree_map_eq_of_injective (algebraMap ℚ E).injective _
    have h2 : DE.natDegree = n := by
      rw [hDE, natDegree_C_mul ((map_ne_zero_iff _ ιE.injective).mpr hlc),
        natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C _]
      simp
    omega
  set RE := (toPoly R).map (algebraMap ℚ E)
  have hRE : RE.degree < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin, degree_map]
    calc (toPoly R).degree < (toPoly D).degree := hRdeg
      _ = n := by rw [degree_eq_natDegree hD0, hDn]
  have hxv : ∀ i ∈ (Finset.univ : Finset (Fin n)), x ≠ v i := fun i _ ↦
    sub_ne_zero.mp (x_sub_const_ne hC x hx (ι rs[i]))
  have hpf := partial_frac Finset.univ v hv (ιE lc) ((map_ne_zero_iff _ ιE.injective).mpr hlc) DE RE
    hDE hRE x hxv
  -- evaluate
  have hDx : aeval x (toPoly D) ≠ 0 := by
    rw [haev]
    change DE.eval x ≠ 0
    rw [hDE, eval_mul, eval_C, eval_prod]
    refine mul_ne_zero ((map_ne_zero_iff _ ιE.injective).mpr hlc)
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_)
    simp only [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr (hxv i (Finset.mem_univ _))
  rw [evF_liftF, EllAlgo.sum_map_eq_fin]
  have hA : aeval x (toPoly A) / aeval x (toPoly D) = aeval x (toPoly q) +
      RE.eval x / DE.eval x := by
    rw [hAR, map_add, map_mul, add_div, mul_div_cancel_right₀ _ hDx, haev (toPoly R),
      haev (toPoly D)]
  rw [← div_div, hA, hpf]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hroot : (toPoly D).eval₂ (algebraMap ℚ F) rs[i] = 0 := by
    rw [← eval_map, hsplit, eval_mul, eval_list_prod]
    apply mul_eq_zero_of_right
    apply List.prod_eq_zero
    simp only [List.map_map, List.mem_map, Function.comp_apply, eval_sub, eval_X, eval_C]
    exact ⟨rs[i], List.getElem_mem _, sub_self _⟩
  have hRi : RE.eval (v i) = ιE (evalQF A rs[i]) := by
    rw [evalQF_eq, haevF, hAR]
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, RE]
    rw [← haevF (toPoly D), aeval_def, hroot, map_zero, mul_zero, zero_add]
  have hDi : (derivative DE).eval (v i) = ιE (evalQF (CPoly.deriv D) rs[i]) := by
    rw [evalQF_eq, haevF, toPoly_deriv, derivative_map]
  rw [hRi, hDi]
  simp only [ιE, RingHom.comp_apply, map_div₀, v]
  field_simp


/-- **Correctness of `ellDecideAD`**: an answer `some b` is the truth about `∫ A dx / (D y)`. -/
theorem ellDecideAD_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : F →+* Kc) (A D : CPoly ℚ) (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp02 : p0 ≠ 2) (hgood : goodRedMod p0 a b c) (s : ZMod p0) (hs : s ^ 2 = d)
    (hs' : 2 * s ≠ 0) (ans : Bool) (h : ellDecideAD (d := d) a b c A D p0 = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold ellDecideAD at h
  split_ifs at h with hz
  split at h
  · cases h
  rename_i rs hr
  split at h
  swap
  · cases h
  rename_i pts hp
  have hD0 : toPoly D ≠ 0 := fun h0 ↦ hz ((isZero_iff _).mpr h0)
  have hv := validF_of_some h
  simp only [validF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hon, hnd⟩ := hv
  obtain ⟨e1, e2⟩ := ptsL_sum ((algebraMap Kc E).comp ι) x hp fun q hq ↦ (hon q hq).2
  simp only [RingHom.comp_apply] at e2
  have hnd' : rs.Nodup := e1 ▸ hnd
  obtain ⟨lc, hlc, hsplit⟩ := rootsD_spec hD0 hr
  rw [ellDecideF_spec hC hCall x y hx a b c hsq hy hgen ι _ pts p0 hp02 hgood s hs hs' ans h,
    integrand_pf hC x y hx ι A D hD0 rs hnd' lc hlc hsplit, e2]

end Spec


/-! ### Completeness -/

/-- **An irreducible rational polynomial with a root in `F` has degree `≤ 2`**; in degree `2`
the root is irrational. -/
lemma natDegree_le_two_of_root {f : ℚ[X]} (hf : Irreducible f) {α : F} (hα : aeval α f = 0) :
    f.natDegree = 1 ∨ (f.natDegree = 2 ∧ α.im ≠ 0) := by
  by_cases him : α.im = 0
  · left
    have hαr : α = algebraMap ℚ F α.re := by ext <;> simp [him, Algebra.algebraMap_eq_smul_one]
    have hroot : f.IsRoot α.re := by
      have h1 : algebraMap ℚ F (f.eval α.re) = 0 := by
        rw [← coe_aeval_eq_eval, ← aeval_algebraMap_apply, ← hαr]; exact hα
      exact (map_eq_zero_iff _ (algebraMap ℚ F).injective).mp h1
    have := degree_eq_one_of_irreducible_of_root hf hroot
    exact natDegree_eq_of_degree_eq_some this
  · right
    set m : ℚ[X] := X ^ 2 - C (2 * α.re) * X + C (α.re ^ 2 - d * α.im ^ 2) with hm
    have hmα : aeval α m = 0 := by
      simp only [hm, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, sq]
      ext <;> simp [Algebra.algebraMap_eq_smul_one, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat] <;> ring
    have hmdeg : m.natDegree = 2 := by rw [hm]; compute_degree!
    have hdvd : f ∣ m := by
      by_contra hnd
      obtain ⟨u, v, huv⟩ := (hf.coprime_iff_not_dvd).mpr hnd
      have := congrArg (aeval α) huv
      simp only [map_add, map_mul, hα, hmα, mul_zero, add_zero, map_one] at this
      exact zero_ne_one this
    have hm0 : m ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hmdeg; omega
    have hle := natDegree_le_of_dvd hdvd hm0
    have hne1 : f.natDegree ≠ 1 := by
      intro h1
      -- a linear rational polynomial has only rational roots
      have hf1 := eq_X_add_C_of_natDegree_le_one (show f.natDegree ≤ 1 by omega)
      have hc1 : f.coeff 1 ≠ 0 := by
        rw [← h1]; exact leadingCoeff_ne_zero.mpr hf.ne_zero
      rw [hf1] at hα
      simp only [map_add, map_mul, aeval_C, aeval_X] at hα
      have := congrArg QuadraticAlgebra.im hα
      simp [Algebra.algebraMap_eq_smul_one] at this
      rcases this with h | h
      · exact hc1 h
      · exact him h
    have hne0 : f.natDegree ≠ 0 := fun h0 ↦
      hf.not_isUnit (isUnit_iff_degree_eq_zero.mpr (by
        rw [degree_eq_natDegree hf.ne_zero, h0]; rfl))
    exact ⟨by omega, him⟩


lemma rootsFac_ne_none {f : CPoly ℚ} (hirr : Irreducible (toPoly f)) {α : F}
    (hα : aeval α (toPoly f) = 0) : rootsFac (d := d) f ≠ none := by
  have hf0 := hirr.ne_zero
  have hdeg := Kron.degC_eq f hf0
  unfold rootsFac
  rcases natDegree_le_two_of_root hirr hα with h1 | ⟨h2, him⟩
  · rw [if_pos (by omega)]; simp
  · rw [if_neg (by omega), if_pos (by omega)]
    dsimp only
    have hq := toPoly_quad (f := f) (by omega)
    have hc2 : f.getD 2 0 ≠ 0 := by
      rw [← coeff_toPoly, ← h2]; exact leadingCoeff_ne_zero.mpr hf0
    set g0 := f.getD 0 0
    set g1 := f.getD 1 0
    set g2 := f.getD 2 0
    have hd : (d : ℚ) ≠ 0 := fun h0 ↦ (Fact.out : ¬IsSquare (d : ℚ)) ⟨0, by rw [h0]; ring⟩
    rw [hq] at hα
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X] at hα
    have hre := congrArg QuadraticAlgebra.re hα
    have hi := congrArg QuadraticAlgebra.im hα
    simp [Algebra.algebraMap_eq_smul_one, sq] at hre hi
    have hs : α.re = -g1 / (2 * g2) := by
      have : α.im * (g1 + 2 * g2 * α.re) = 0 := by linear_combination hi
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h him
      · field_simp; linarith
    have hdisc : (g1 ^ 2 - 4 * g0 * g2) / d = (2 * g2 * α.im) ^ 2 := by
      rw [div_eq_iff hd]
      rw [hs] at hre
      field_simp at hre
      linear_combination (-1 : ℚ) * hre
    rw [hdisc]
    obtain ⟨k, hk, hk2⟩ := qsqrt_sq_eq (2 * g2 * α.im)
    rw [hk]
    have hk0 : k ≠ 0 := by
      intro h0; rw [h0] at hk2
      have : 2 * g2 * α.im = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by rw [← hk2]; ring)
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · norm_num at h'
        · exact hc2 h'
      · exact him h
    simp [hk0]


omit [Fact (¬IsSquare (d : ℚ))] in
lemma isCoprime_list_prod {K : Type*} [Field K] (g : K[X]) :
    ∀ rs : List K, (∀ r ∈ rs, g.eval r ≠ 0) → IsCoprime g (rs.map fun r ↦ X - C r).prod
  | [], _ => by simp [isCoprime_one_right]
  | r :: t, h => by
    rw [List.map_cons, List.prod_cons]
    refine IsCoprime.mul_right ?_ (isCoprime_list_prod g t fun r' hr' ↦ h r' (List.mem_cons_of_mem _ hr'))
    refine IsCoprime.symm ((irreducible_X_sub_C r).coprime_iff_not_dvd.mpr ?_)
    rw [dvd_iff_isRoot]; exact h r List.mem_cons_self

/-- **A non-constant divisor of a split polynomial has one of its roots.** -/
lemma exists_root_of_dvd {f D : ℚ[X]} (hf : 0 < f.natDegree) (hdvd : f ∣ D) {lc : F} (hlc : lc ≠ 0)
    {rs : List F} (hsplit : D.map (algebraMap ℚ F) = C lc * (rs.map fun r ↦ X - C r).prod) :
    ∃ α ∈ rs, aeval α f = 0 := by
  by_contra hno
  push_neg at hno
  have hco : IsCoprime (f.map (algebraMap ℚ F)) (D.map (algebraMap ℚ F)) := by
    rw [hsplit]
    refine IsCoprime.mul_right ?_ (isCoprime_list_prod _ rs fun r hr ↦ ?_)
    · exact isCoprime_one_right.of_isCoprime_of_dvd_right (by
        rw [← isUnit_iff_dvd_one]; exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlc))
    · rw [eval_map_algebraMap]; exact hno r hr
  have hu := hco.isUnit_of_dvd' (dvd_refl _) (Polynomial.map_dvd _ hdvd)
  have := natDegree_eq_zero_of_isUnit hu
  rw [natDegree_map_eq_of_injective (algebraMap ℚ F).injective] at this
  omega

lemma root_of_mem {D : ℚ[X]} {lc : F} {rs : List F}
    (hsplit : D.map (algebraMap ℚ F) = C lc * (rs.map fun r ↦ X - C r).prod) {α : F} (hα : α ∈ rs) :
    aeval α D = 0 := by
  rw [← eval_map_algebraMap, hsplit, eval_mul]
  apply mul_eq_zero_of_right
  rw [eval_list_prod]
  apply List.prod_eq_zero
  simp only [List.map_map, List.mem_map, Function.comp_apply, eval_sub, eval_X, eval_C]
  exact ⟨α, hα, sub_self _⟩

/-- **Distinct roots**: a squarefree polynomial splits with distinct roots. -/
lemma nodup_of_squarefree {D : ℚ[X]} (hsq : Squarefree D) {lc : F} {rs : List F}
    (hsplit : D.map (algebraMap ℚ F) = C lc * (rs.map fun r ↦ X - C r).prod) : rs.Nodup := by
  have hsqF : Squarefree (D.map (algebraMap ℚ F)) :=
    ((PerfectField.separable_iff_squarefree).mpr hsq).map.squarefree
  rw [List.nodup_iff_sublist]
  intro r hr
  have hsub := hr.map (fun r ↦ X - C r)
  have hdvd : (X - C r) * (X - C r) ∣ D.map (algebraMap ℚ F) := by
    rw [hsplit]
    refine Dvd.dvd.mul_left ?_ _
    have := hsub.prod_dvd_prod
    simpa using this
  exact (irreducible_X_sub_C r).not_isUnit (hsqF _ hdvd)


lemma rootsL_ne_none {D : ℚ[X]} {lc : F} (hlc : lc ≠ 0) {rs : List F}
    (hsplit : D.map (algebraMap ℚ F) = C lc * (rs.map fun r ↦ X - C r).prod) :
    ∀ fs : List (CPoly ℚ), (∀ f ∈ fs, Irreducible (toPoly f) ∧ toPoly f ∣ D) →
      rootsL (d := d) fs ≠ none
  | [], _ => by simp [rootsL]
  | f :: t, h => by
    obtain ⟨hirr, hdvd⟩ := h f List.mem_cons_self
    have hpos : 0 < (toPoly f).natDegree := by
      by_contra h0
      exact hirr.not_isUnit (isUnit_iff_degree_eq_zero.mpr (by
        rw [degree_eq_natDegree hirr.ne_zero]; simp; omega))
    obtain ⟨α, -, hα⟩ := exists_root_of_dvd hpos hdvd hlc hsplit
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp (rootsFac_ne_none (d := d) hirr hα)
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp
      (rootsL_ne_none hlc hsplit t fun f' hf' ↦ h f' (List.mem_cons_of_mem _ hf'))
    simp [rootsL, hl, hm]

lemma rootsD_ne_none {D : CPoly ℚ} (hD : toPoly D ≠ 0) {lc : F} (hlc : lc ≠ 0) {rs : List F}
    (hsplit : (toPoly D).map (algebraMap ℚ F) = C lc * (rs.map fun r ↦ X - C r).prod) :
    rootsD (d := d) D ≠ none := by
  unfold rootsD
  split_ifs with h0
  · simp
  · have hpos : 0 < (toPoly D).natDegree := by rw [← Kron.degC_eq D hD]; omega
    obtain ⟨hirr, k, hk, hDk⟩ := Kron.factorQ_spec (Kron.degC D + 1) D hpos
      (by rw [← Kron.degC_eq D hD]; omega)
    refine rootsL_ne_none hlc hsplit _ fun f hf ↦ ⟨Kron.irredQ_sound f (hirr f hf), ?_⟩
    rw [hDk]
    exact Dvd.dvd.mul_left (List.dvd_prod (List.mem_map_of_mem hf)) _

lemma ptsL_fst {a b c : ℤ} {A D : CPoly ℚ} : ∀ {rs : List F} {pts : List (F × F × F)},
    ptsL a b c A D rs = some pts → pts.map Prod.fst = rs ∧
      ∀ q ∈ pts, q.2.1 * q.2.1 = q.1 ^ 3 + (a : F) * q.1 ^ 2 + (b : F) * q.1 + (c : F)
  | [], pts, h => by simp only [ptsL, Option.some.injEq] at h; subst h; simp
  | α :: t, pts, h => by
    simp only [ptsL] at h
    split at h
    · rename_i β m h1 h2
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, e2⟩ := ptsL_fst h2
      refine ⟨by simp [e1], ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact sqrtF_sound h1
      · exact e2 q hq
    · cases h

lemma ptsL_ne_none {a b c : ℤ} {A D : CPoly ℚ} : ∀ {rs : List F},
    (∀ α ∈ rs, ∃ β : F, β * β = α ^ 3 + (a : F) * α ^ 2 + (b : F) * α + (c : F)) →
      ptsL a b c A D rs ≠ none
  | [], _ => by simp [ptsL]
  | α :: t, h => by
    obtain ⟨β, hβ⟩ := h α List.mem_cons_self
    obtain ⟨β0, h0⟩ := Option.ne_none_iff_exists'.mp (sqrtF_complete (d := d) β)
    rw [hβ] at h0
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp
      (ptsL_ne_none (A := A) (D := D) fun α' hα' ↦ h α' (List.mem_cons_of_mem _ hα'))
    simp [ptsL, h0, hm]

/-- **Completeness of `ellDecideAD`**: if `D` is squarefree and splits over `F`, and `p` takes a
non-zero square value in `F` at every root of `D`, the procedure answers. -/
theorem ellDecideAD_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hDsq : Squarefree (toPoly D)) (lc : F) (hlc : lc ≠ 0) (rs : List F)
    (hsplit : (toPoly D).map (algebraMap ℚ F) = C lc * (rs.map fun r ↦ X - C r).prod)
    (hpt : ∀ α : F, aeval α (toPoly D) = 0 →
      ∃ β : F, β ≠ 0 ∧ β * β = α ^ 3 + (a : F) * α ^ 2 + (b : F) * α + (c : F))
    (p0 : ℕ) [NeZero p0] : ellDecideAD (d := d) a b c A D p0 ≠ none := by
  have hD0 : toPoly D ≠ 0 := hDsq.ne_zero
  unfold ellDecideAD
  rw [if_neg (fun h ↦ hD0 ((isZero_iff _).mp h))]
  obtain ⟨rs', hr⟩ := Option.ne_none_iff_exists'.mp (rootsD_ne_none (d := d) hD0 hlc hsplit)
  rw [hr]
  simp only
  obtain ⟨lc', hlc', hsplit'⟩ := rootsD_spec hD0 hr
  have hroots : ∀ α ∈ rs', aeval α (toPoly D) = 0 := fun α hα ↦ root_of_mem hsplit' hα
  obtain ⟨pts, hp⟩ := Option.ne_none_iff_exists'.mp (ptsL_ne_none (a := a) (b := b) (c := c)
    (A := A) (D := D) fun α hα ↦ by
      obtain ⟨β, -, hβ⟩ := hpt α (hroots α hα); exact ⟨β, hβ⟩)
  rw [hp]
  simp only
  obtain ⟨e1, e2⟩ := ptsL_fst hp
  refine ellDecideF_ne_none a b c hsq _ pts p0 ?_
  simp only [validF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun q hq ↦ ⟨e2 q hq, fun h0 ↦ ?_⟩, ?_⟩
  · have hmem : q.1 ∈ rs' := e1 ▸ List.mem_map_of_mem hq
    obtain ⟨β, hβ0, hβ⟩ := hpt q.1 (hroots _ hmem)
    have := e2 q hq
    rw [h0, zero_mul, ← hβ] at this
    exact hβ0 (mul_self_eq_zero.mp this.symm)
  · rw [e1]; exact nodup_of_squarefree hDsq hsplit'


section Decides

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ A dx / (D √p)` is decided** when `D` is squarefree and splits over `ℚ(√d)`, and `p` takes
non-zero square values in `ℚ(√d)` at the roots of `D`. -/
theorem ellDecideAD_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : F →+* Kc) (A D : CPoly ℚ) (hDsq : Squarefree (toPoly D)) (lc : F) (hlc : lc ≠ 0)
    (rs : List F) (hsplit : (toPoly D).map (algebraMap ℚ F) = C lc * (rs.map fun r ↦ X - C r).prod)
    (hpt : ∀ α : F, aeval α (toPoly D) = 0 →
      ∃ β : F, β ≠ 0 ∧ β * β = α ^ 3 + (a : F) * α ^ 2 + (b : F) * α + (c : F))
    (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp02 : p0 ≠ 2) (hgood : goodRedMod p0 a b c) (s : ZMod p0) (hs : s ^ 2 = d)
    (hs' : 2 * s ≠ 0) :
    ∃ ans, ellDecideAD (d := d) a b c A D p0 = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨ans, h⟩ := Option.ne_none_iff_exists'.mp
    (ellDecideAD_ne_none a b c hsq A D hDsq lc hlc rs hsplit hpt p0)
  exact ⟨ans, h, ellDecideAD_spec hC hCall x y hx a b c hsq hy hgen ι A D p0 hp02 hgood s hs hs'
    ans h⟩

end Decides

end EllQuad
