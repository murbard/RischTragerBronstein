import RischTragerBronstein.Algebraic.SupTorsionDecide
import RischTragerBronstein.Algebraic.HypGlue

/-!
# Computable bivariate polynomials on `yⁿ = f(x)`

`BPoly F = List (CPoly F)` (coefficients of `y⁰, y¹, …`), with semantics `toB : BPoly F → F[X][X]`:

* `addB`, `smulB` (by a polynomial in `x`), `mulB`: exact (`toB_addB`, `toB_smulB`, `toB_mulB`);
* `reduceB f n`: reduction modulo `Yⁿ − f`, `toB (reduceB W) ≡ toB W` (`toB_reduceB`) and the result
  has `y`-degree `< n`;
* `derivB f n`: `f ∂ₓ + (1/n) f′ Y ∂_Y`, the derivative multiplied by `f` (`toB_derivB`).
-/

open Polynomial

namespace Sup

/-- Bivariate polynomials, as lists of `y`-coefficients. -/
abbrev BPoly (F : Type*) := List (CPoly F)

section Ring

variable {F : Type*} [CommRing F]

/-- The semantics. -/
noncomputable def toB : BPoly F → F[X][X]
  | [] => 0
  | a :: W => Polynomial.C (CPoly.toPoly a) + X * toB W

@[simp] lemma toB_nil : toB ([] : BPoly F) = 0 := rfl
@[simp] lemma toB_cons (a : CPoly F) (W : BPoly F) :
    toB (a :: W) = Polynomial.C (CPoly.toPoly a) + X * toB W := rfl

/-- Sum. -/
def addB : BPoly F → BPoly F → BPoly F
  | [], V => V
  | W, [] => W
  | a :: W, b :: V => CPoly.add a b :: addB W V

@[simp] lemma toB_addB : ∀ W V : BPoly F, toB (addB W V) = toB W + toB V
  | [], V => by simp [addB]
  | a :: W, [] => by simp [addB]
  | a :: W, b :: V => by
    simp only [addB, toB_cons, CPoly.toPoly_add, toB_addB W V, map_add]; ring

/-- Multiplication by a polynomial in `x`. -/
def smulB (c : CPoly F) (W : BPoly F) : BPoly F := W.map (CPoly.mul c)

@[simp] lemma toB_smulB (c : CPoly F) : ∀ W : BPoly F,
    toB (smulB c W) = Polynomial.C (CPoly.toPoly c) * toB W
  | [] => by simp [smulB]
  | a :: W => by
    have := toB_smulB c W
    simp only [smulB, List.map_cons, toB_cons, CPoly.toPoly_mul, map_mul] at this ⊢
    rw [this]; ring

/-- Product. -/
def mulB : BPoly F → BPoly F → BPoly F
  | [], _ => []
  | a :: W, V => addB (smulB a V) ([] :: mulB W V)

@[simp] lemma toB_mulB : ∀ W V : BPoly F, toB (mulB W V) = toB W * toB V
  | [], V => by simp [mulB]
  | a :: W, V => by
    simp only [mulB, toB_addB, toB_smulB, toB_cons, CPoly.toPoly_nil, map_zero, zero_add,
      toB_mulB W V]
    ring

lemma toB_append (W V : BPoly F) : toB (W ++ V) = toB W + X ^ W.length * toB V := by
  induction W with
  | nil => simp
  | cons a W ih => simp only [List.cons_append, toB_cons, ih, List.length_cons, pow_succ]; ring

lemma length_addB : ∀ W V : BPoly F, (addB W V).length = max W.length V.length
  | [], V => by simp [addB]
  | a :: W, [] => by simp [addB]
  | a :: W, b :: V => by simp [addB, length_addB W V, Nat.succ_max_succ]

/-- Reduction modulo `Yⁿ − f`. -/
def reduceB (f : CPoly F) (n : ℕ) (hn : 0 < n) (W : BPoly F) : BPoly F :=
  if h : W.length ≤ n then W
  else reduceB f n hn (addB (W.take n) (smulB f (W.drop n)))
termination_by W.length
decreasing_by
  rw [length_addB, List.length_take, smulB, List.length_map, List.length_drop]
  omega

lemma length_reduceB (f : CPoly F) (n : ℕ) (hn : 0 < n) (W : BPoly F) :
    (reduceB f n hn W).length ≤ n := by
  induction W using (measure List.length).wf.induction with
  | h W ih =>
    rw [reduceB]
    split_ifs with h
    · exact h
    · apply ih
      show (addB (W.take n) (smulB f (W.drop n))).length < W.length
      rw [length_addB, List.length_take, smulB, List.length_map, List.length_drop]
      omega

/-- The reduction preserves the class modulo `Yⁿ − f`. -/
lemma toB_reduceB (f : CPoly F) (n : ℕ) (hn : 0 < n) (W : BPoly F) :
    (X ^ n - Polynomial.C (CPoly.toPoly f)) ∣ toB (reduceB f n hn W) - toB W := by
  induction W using (measure List.length).wf.induction with
  | h W ih =>
    rw [reduceB]
    split_ifs with h
    · simp
    · have h1 := ih (addB (W.take n) (smulB f (W.drop n))) (by
        show (addB (W.take n) (smulB f (W.drop n))).length < W.length
        rw [length_addB, List.length_take, smulB, List.length_map, List.length_drop]
        omega)
      have h2 : toB W = toB (W.take n) + X ^ n * toB (W.drop n) := by
        conv_lhs => rw [← List.take_append_drop n W]
        rw [toB_append, List.length_take, min_eq_left (by omega)]
      have h3 : toB (addB (W.take n) (smulB f (W.drop n))) - toB W =
          -((X ^ n - Polynomial.C (CPoly.toPoly f)) * toB (W.drop n)) := by
        rw [toB_addB, toB_smulB, h2]; ring
      have := dvd_add h1 (show (X ^ n - Polynomial.C (CPoly.toPoly f)) ∣
        toB (addB (W.take n) (smulB f (W.drop n))) - toB W by
          rw [h3]; exact (dvd_mul_right _ _).neg_right)
      rwa [sub_add_sub_cancel] at this

end Ring

section Deriv

variable {F : Type*} [Field F]

/-- The entries of `f ∂ₓ + (1/n) f′ Y ∂_Y`, starting at `y`-degree `l`. -/
def derivBAux (f : CPoly F) (n : ℕ) : ℕ → BPoly F → BPoly F
  | _, [] => []
  | l, a :: W => CPoly.add (CPoly.mul f (CPoly.deriv a))
      (CPoly.smul ((l : F) / n) (CPoly.mul (CPoly.deriv f) a)) :: derivBAux f n (l + 1) W

/-- `f ∂ₓ + (1/n) f′ Y ∂_Y`. -/
def derivB (f : CPoly F) (n : ℕ) (W : BPoly F) : BPoly F := derivBAux f n 0 W

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero E]

/-- Evaluation at `(x, y)`, through `ι : F → Kc`. -/
noncomputable def evalE (ι : F →+* Kc) (x y : E) : F[X][X] →+* E :=
  Polynomial.eval₂RingHom (((aeval x : Kc[X] →ₐ[Kc] E) : Kc[X] →+* E).comp (mapRingHom ι)) y

lemma evalE_C (ι : F →+* Kc) (x y : E) (P : F[X]) :
    evalE ι x y (Polynomial.C P) = aeval x (P.map ι) := by
  simp [evalE]

lemma evalE_X (ι : F →+* Kc) (x y : E) : evalE ι x y X = y := by simp [evalE]

lemma evalE_cons (ι : F →+* Kc) (x y : E) (a : CPoly F) (W : BPoly F) :
    evalE ι x y (toB (a :: W)) = aeval x ((CPoly.toPoly a).map ι) + y * evalE ι x y (toB W) := by
  rw [toB_cons, map_add, map_mul, evalE_C, evalE_X]

/-- The derivative of `yˡ`: `f (yˡ)′ = (l/n) f′ yˡ`. -/
lemma deriv_y_pow (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : F →+* Kc) (f : F[X])
    {n : ℕ} (hn : 0 < n) (hy0 : y ≠ 0) (hy : y ^ n = aeval x (f.map ι)) (l : ℕ) :
    aeval x (f.map ι) * (y ^ l)′ =
      ((l : E) / n) * aeval x (derivative (f.map ι)) * y ^ l := by
  have hn0 : (n : E) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hyd : ((k + 1 : ℕ) : E) * y ^ k * y′ = aeval x (derivative (f.map ι)) := by
    have h1 : (y ^ (k + 1))′ = (aeval x (f.map ι))′ := by rw [hy]
    rw [deriv_aeval_x x hC hx, Derivation.leibniz_pow, nsmul_eq_mul, Nat.add_sub_cancel,
      smul_eq_mul] at h1
    rw [← h1]; ring
  have hne : ((k + 1 : ℕ) : E) * y ^ k ≠ 0 := mul_ne_zero hn0 (pow_ne_zero _ hy0)
  apply mul_left_cancel₀ hne
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [Derivation.leibniz_pow, nsmul_eq_mul, Nat.add_sub_cancel, smul_eq_mul]
  have e : ((k + 1 : ℕ) : E) * y ^ k * (((m + 1 : ℕ) : E) / ((k + 1 : ℕ) : E) *
      aeval x (derivative (f.map ι)) * y ^ (m + 1)) =
      ((m + 1 : ℕ) : E) * y ^ k * aeval x (derivative (f.map ι)) * y ^ (m + 1) := by
    field_simp
  rw [e]
  linear_combination (((m + 1 : ℕ) : E) * aeval x (f.map ι) * y ^ m) * hyd -
    (((m + 1 : ℕ) : E) * aeval x (derivative (f.map ι)) * y ^ m) * hy

/-- **The derivative formula**: `f (yˡ W)′ = yˡ (derivBAux l W)`. -/
lemma evalE_derivBAux (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : F →+* Kc)
    (f : CPoly F) {n : ℕ} (hn : 0 < n) (hy0 : y ≠ 0)
    (hy : y ^ n = aeval x ((CPoly.toPoly f).map ι)) :
    ∀ (l : ℕ) (W : BPoly F), aeval x ((CPoly.toPoly f).map ι) * (y ^ l * evalE ι x y (toB W))′ =
      y ^ l * evalE ι x y (toB (derivBAux f n l W))
  | l, [] => by simp [derivBAux]
  | l, a :: W => by
    have ih := evalE_derivBAux hC x y hx ι f hn hy0 hy (l + 1) W
    rw [evalE_cons, derivBAux, evalE_cons]
    have hdy := deriv_y_pow hC x y hx ι (CPoly.toPoly f) hn hy0 hy l
    have hda : (aeval x ((CPoly.toPoly a).map ι))′ = aeval x (derivative ((CPoly.toPoly a).map ι)) :=
      deriv_aeval_x x hC hx _
    have e1 : y ^ l * (aeval x ((CPoly.toPoly a).map ι) + y * evalE ι x y (toB W)) =
        y ^ l * aeval x ((CPoly.toPoly a).map ι) + y ^ (l + 1) * evalE ι x y (toB W) := by ring
    rw [e1, map_add, mul_add, ih, Derivation.leibniz, hda]
    simp only [CPoly.toPoly_add, CPoly.toPoly_mul, CPoly.toPoly_deriv, CPoly.toPoly_smul,
      Polynomial.map_add, Polynomial.map_mul, derivative_map, Polynomial.map_C, map_add, map_mul,
      aeval_C, smul_eq_mul]
    have hc : algebraMap Kc E (ι ((l : F) / n)) = (l : E) / n := by simp
    rw [hc]
    rw [derivative_map] at hdy
    linear_combination (aeval x ((CPoly.toPoly a).map ι)) * hdy

end Deriv

section Enc

variable {F : Type*} [Field F]

/-- `Xᴰ` as a computable polynomial. -/
def xpowC (D : ℕ) : CPoly F := List.replicate D 0 ++ [1]

lemma toPoly_xpowC (D : ℕ) : CPoly.toPoly (xpowC D : CPoly F) = X ^ D := by
  induction D with
  | zero => simp [xpowC]
  | succ D ih =>
    simp only [xpowC, List.replicate_succ, List.cons_append, CPoly.toPoly_cons, map_zero,
      zero_add] at ih ⊢
    rw [ih, pow_succ]; ring

/-- Kronecker flattening `Y ↦ Xᴰ`. -/
def encB (D : ℕ) : BPoly F → CPoly F
  | [] => []
  | a :: W => CPoly.add a (CPoly.mul (xpowC D) (encB D W))

lemma toPoly_encB (D : ℕ) : ∀ W : BPoly F,
    CPoly.toPoly (encB D W) = (toB W).eval (X ^ D)
  | [] => by simp only [encB, CPoly.toPoly_nil, toB_nil, eval_zero]
  | a :: W => by
    rw [encB, CPoly.toPoly_add, CPoly.toPoly_mul, toPoly_xpowC, toPoly_encB D W, toB_cons,
      eval_add, eval_mul, eval_C, eval_X]

lemma kron_step (D : ℕ) (P : F[X][X]) (hD : ∀ l, (P.coeff l).natDegree < D)
    (h0 : P.eval (X ^ D) = 0) : P.coeff 0 = 0 ∧ P.divX.eval (X ^ D) = 0 := by
  have e : P.eval (X ^ D) = P.coeff 0 + X ^ D * P.divX.eval (X ^ D) := by
    conv_lhs => rw [← X_mul_divX_add P]
    rw [eval_add, eval_mul, eval_X, eval_C, add_comm]
  have hc0 : P.coeff 0 = 0 := by
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < D
    · have := congrArg (fun Q : F[X] ↦ Q.coeff k) (e.symm.trans h0)
      simp only [coeff_add, coeff_X_pow_mul', if_neg (by omega : ¬ D ≤ k), add_zero,
        Polynomial.coeff_zero] at this
      exact this
    · exact coeff_eq_zero_of_natDegree_lt (by have := hD 0; omega)
  refine ⟨hc0, ?_⟩
  rw [e, hc0, zero_add] at h0
  exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ X_ne_zero)

/-- **Kronecker flattening is injective** on coefficients of degree `< D`. -/
lemma kron_inj (D N : ℕ) : ∀ P : F[X][X], P.natDegree ≤ N →
    (∀ l, (P.coeff l).natDegree < D) → P.eval (X ^ D) = 0 → P = 0 := by
  induction N with
  | zero =>
    intro P hN hD h0
    obtain ⟨hc0, -⟩ := kron_step D P hD h0
    rw [eq_C_of_natDegree_eq_zero (p := P) (by omega), hc0, map_zero]
  | succ N ih =>
    intro P hN hD h0
    obtain ⟨hc0, hQ⟩ := kron_step D P hD h0
    have hdiv : P.divX = 0 := ih P.divX (by rw [natDegree_divX_eq_natDegree_tsub_one]; omega)
      (fun l ↦ by rw [coeff_divX]; exact hD _) hQ
    rw [← X_mul_divX_add P, hdiv, hc0]; simp

/-- The monomial `xᵃ yˡ`. -/
def monoB (a l : ℕ) : BPoly F := List.replicate l [] ++ [xpowC a]

lemma toB_monoB (a : ℕ) : ∀ l : ℕ, toB (monoB a l : BPoly F) = Polynomial.C (X ^ a) * X ^ l
  | 0 => by simp [monoB, toPoly_xpowC]
  | l + 1 => by
    have := toB_monoB a l
    simp only [monoB, List.replicate_succ, List.cons_append, toB_cons, CPoly.toPoly_nil,
      map_zero, zero_add] at this ⊢
    rw [this, pow_succ]; ring

lemma coeff_toB : ∀ (W : BPoly F) (l : ℕ), (toB W).coeff l = CPoly.toPoly (W.getD l [])
  | [], l => by simp
  | a :: W, 0 => by simp
  | a :: W, l + 1 => by
    rw [toB_cons, coeff_add, coeff_C, if_neg (by omega), zero_add, coeff_X_mul, coeff_toB W l]
    rfl

/-- The maximal length of the entries. -/
def maxLenB (W : BPoly F) : ℕ := (W.map List.length).foldr max 0

lemma length_le_maxLenB : ∀ (W : BPoly F) (l : ℕ), (W.getD l []).length ≤ maxLenB W
  | [], l => by simp [maxLenB]
  | a :: W, 0 => by simp [maxLenB]
  | a :: W, l + 1 => by
    have := length_le_maxLenB W l
    simp only [maxLenB, List.map_cons, List.foldr_cons] at this ⊢
    exact this.trans (le_max_right _ _)

lemma natDegree_coeff_toB_lt (W : BPoly F) {D : ℕ} (hD : maxLenB W < D) (l : ℕ) :
    ((toB W).coeff l).natDegree < D := by
  rw [coeff_toB]
  have h := length_le_maxLenB W l
  by_cases h0 : CPoly.toPoly (W.getD l []) = 0
  · rw [h0, natDegree_zero]; omega
  · have h1 : (CPoly.toPoly (W.getD l [])).natDegree < (W.getD l []).length := by
      by_contra hc
      push_neg at hc
      have := leadingCoeff_ne_zero.mpr h0
      rw [leadingCoeff, CPoly.coeff_toPoly, List.getD_eq_default _ _ hc] at this
      exact this rfl
    omega

/-- `∑ cᵢ Wᵢ`. -/
noncomputable def combB (cs : List F) (cols : List (BPoly F)) : F[X][X] :=
  (List.zipWith (fun c W ↦ Polynomial.C (Polynomial.C c) * toB W) cs cols).sum

lemma eval_combB (D : ℕ) : ∀ (cs : List F) (cols : List (BPoly F)),
    (combB cs cols).eval (X ^ D) = CPoly.lcomb cs (cols.map (encB D))
  | [], _ => by simp [combB, CPoly.lcomb]
  | _ :: _, [] => by simp [combB, CPoly.lcomb]
  | c :: cs, W :: cols => by
    have := eval_combB D cs cols
    simp only [combB, CPoly.lcomb, List.zipWith_cons_cons, List.sum_cons, List.map_cons] at this ⊢
    rw [eval_add, eval_mul, eval_C, toPoly_encB, this]

lemma natDegree_coeff_combB {D : ℕ} (hD : 0 < D) : ∀ (cs : List F) (cols : List (BPoly F)),
    (∀ W ∈ cols, maxLenB W < D) → ∀ l, ((combB cs cols).coeff l).natDegree < D
  | [], _, _, l => by simp [combB]; omega
  | _ :: _, [], _, l => by simp [combB]; omega
  | c :: cs, W :: cols, h, l => by
    have ih := natDegree_coeff_combB hD cs cols (fun V hV ↦ h V (List.mem_cons_of_mem _ hV)) l
    have hW := natDegree_coeff_toB_lt W (h W List.mem_cons_self) l
    simp only [combB, List.zipWith_cons_cons, List.sum_cons, coeff_add, coeff_C_mul] at ih ⊢
    exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt
      (lt_of_le_of_lt (natDegree_C_mul_le _ _) hW) ih)

variable [DecidableEq F]

/-- The columns `M · (f v′)` for the monomials `v = xᵃ yˡ` of the basis, reduced. -/
def exactCols (f : CPoly F) (n : ℕ) (hn : 0 < n) (Mm : BPoly F) (basis : List (ℕ × ℕ)) :
    List (BPoly F) :=
  basis.map fun al ↦ reduceB f n hn (mulB Mm (derivB f n (monoB al.1 al.2)))

/-- The block size. -/
def exactD (cols : List (BPoly F)) (T : BPoly F) : ℕ :=
  1 + max (maxLenB T) ((cols.map maxLenB).foldr max 0)

lemma maxLen_lt_exactD (cols : List (BPoly F)) (T : BPoly F) :
    maxLenB T < exactD cols T ∧ ∀ W ∈ cols, maxLenB W < exactD cols T := by
  refine ⟨by unfold exactD; omega, fun W hW ↦ ?_⟩
  have : maxLenB W ≤ (cols.map maxLenB).foldr max 0 := by
    clear T
    induction cols with
    | nil => simp at hW
    | cons V cols ih =>
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp hW with rfl | hW
      · exact le_max_left _ _
      · exact (ih hW).trans (le_max_right _ _)
  unfold exactD; omega

/-- **The exactness test**: solve `M · (f v′) ≡ T (mod yⁿ − f)` for `v` in the span of the
monomials `basis`. -/
def exactTest (f : CPoly F) (n : ℕ) (hn : 0 < n) (Mm T : BPoly F) (basis : List (ℕ × ℕ)) :
    Option (List F) :=
  CPoly.linSolve ((exactCols f n hn Mm basis).map (encB (exactD (exactCols f n hn Mm basis)
    (reduceB f n hn T)))) (encB (exactD (exactCols f n hn Mm basis) (reduceB f n hn T))
      (reduceB f n hn T))

/-- **Soundness of the exactness test.** -/
theorem exactTest_sound (f : CPoly F) (n : ℕ) (hn : 0 < n) (Mm T : BPoly F)
    (basis : List (ℕ × ℕ)) {cs : List F} (h : exactTest f n hn Mm T basis = some cs) :
    cs.length = basis.length ∧
      combB cs (exactCols f n hn Mm basis) = toB (reduceB f n hn T) := by
  set cols := exactCols f n hn Mm basis
  set T' := reduceB f n hn T
  set D := exactD cols T'
  obtain ⟨hlen, hlc⟩ := CPoly.linSolve_sound _ _ _ h
  refine ⟨by simpa [cols, exactCols] using hlen, ?_⟩
  obtain ⟨hT', hcols⟩ := maxLen_lt_exactD cols T'
  rw [← eval_combB, toPoly_encB] at hlc
  have h0 : (combB cs cols - toB T').eval (X ^ D) = 0 := by rw [eval_sub, hlc, sub_self]
  have := kron_inj D _ _ le_rfl (fun l ↦ by
    rw [coeff_sub]
    exact lt_of_le_of_lt (natDegree_sub_le _ _)
      (max_lt (natDegree_coeff_combB (by unfold exactD; omega) cs cols hcols l) (natDegree_coeff_toB_lt T' hT' l))) h0
  exact sub_eq_zero.mp this

end Enc


section Sem

open Differential

variable {F : Type*} [Field F] [DecidableEq F]
variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero E]

lemma evalE_reduceB (ι : F →+* Kc) (x y : E) (f : CPoly F) {n : ℕ} (hn : 0 < n)
    (hy : y ^ n = aeval x ((CPoly.toPoly f).map ι)) (W : BPoly F) :
    evalE ι x y (toB (reduceB f n hn W)) = evalE ι x y (toB W) := by
  obtain ⟨Q, hQ⟩ := toB_reduceB f n hn W
  have h0 : evalE ι x y (X ^ n - Polynomial.C (CPoly.toPoly f)) = 0 := by
    rw [map_sub, map_pow, evalE_X, evalE_C, hy, sub_self]
  rw [← sub_eq_zero, ← map_sub, hQ, map_mul, h0, zero_mul]

lemma evalE_derivB (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : F →+* Kc)
    (f : CPoly F) {n : ℕ} (hn : 0 < n) (hy0 : y ≠ 0)
    (hy : y ^ n = aeval x ((CPoly.toPoly f).map ι)) (W : BPoly F) :
    evalE ι x y (toB (derivB f n W)) =
      aeval x ((CPoly.toPoly f).map ι) * (evalE ι x y (toB W))′ := by
  have := evalE_derivBAux hC x y hx ι f hn hy0 hy 0 W
  simpa [derivB] using this.symm

lemma evalE_monoB (ι : F →+* Kc) (x y : E) (a l : ℕ) :
    evalE ι x y (toB (monoB a l : BPoly F)) = x ^ a * y ^ l := by
  rw [toB_monoB, map_mul, evalE_C, map_pow, evalE_X]; simp

/-- The value `∑ cᵢ xᵃⁱ yˡⁱ`. -/
noncomputable def valB (ι : F →+* Kc) (x y : E) (cs : List F) (basis : List (ℕ × ℕ)) : E :=
  (List.zipWith (fun c al ↦ algebraMap Kc E (ι c) * (x ^ al.1 * y ^ al.2)) cs basis).sum

/-- **The exactness test, in the differential field**: `M · f · v′ = T`. -/
theorem exactTest_sound_E (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : F →+* Kc)
    (f : CPoly F) {n : ℕ} (hn : 0 < n) (hy0 : y ≠ 0)
    (hy : y ^ n = aeval x ((CPoly.toPoly f).map ι)) (Mm T : BPoly F) (basis : List (ℕ × ℕ))
    {cs : List F} (h : exactTest f n hn Mm T basis = some cs) :
    evalE ι x y (toB Mm) * (aeval x ((CPoly.toPoly f).map ι) * (valB ι x y cs basis)′) =
      evalE ι x y (toB T) := by
  obtain ⟨-, hcomb⟩ := exactTest_sound f n hn Mm T basis h
  have e := congrArg (evalE ι x y) hcomb
  rw [evalE_reduceB ι x y f hn hy] at e
  rw [← e]
  unfold combB valB exactCols
  clear e hcomb h
  induction cs generalizing basis with
  | nil => simp
  | cons c cs ih =>
    cases basis with
    | nil => simp
    | cons al basis =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, map_add, mul_add]
      rw [← ih basis]
      congr 1
      have hk : (algebraMap Kc E (ι c) * (x ^ al.1 * y ^ al.2))′ =
          algebraMap Kc E (ι c) * (x ^ al.1 * y ^ al.2)′ := by
        rw [Derivation.leibniz, deriv_algebraMap, hC, map_zero, smul_zero, add_zero, smul_eq_mul]
      rw [hk, map_mul (evalE ι x y), evalE_C, Polynomial.map_C, aeval_C,
        evalE_reduceB ι x y f hn hy, toB_mulB, map_mul (evalE ι x y),
        evalE_derivB hC x y hx ι f hn hy0 hy, evalE_monoB]
      ring

lemma eval_map_Xpow {K' : Type*} [Field K'] (φ : F →+* K') (D : ℕ) (P : F[X][X]) :
    (P.eval (X ^ D)).map φ = (P.map (mapRingHom φ)).eval (X ^ D) := by
  rw [eval_map, show (X ^ D : K'[X]) = mapRingHom φ (X ^ D) by simp, eval₂_hom]
  rfl

/-- `∑ cᵢ Wᵢ` with coefficients in an extension. -/
noncomputable def combBS {K' : Type*} [Field K'] (φ : F →+* K') (cs : List K')
    (cols : List (BPoly F)) : K'[X][X] :=
  (List.zipWith (fun c W ↦ Polynomial.C (Polynomial.C c) * (toB W).map (mapRingHom φ)) cs cols).sum

lemma eval_combBS {K' : Type*} [Field K'] (φ : F →+* K') (D : ℕ) : ∀ (cs : List K')
    (cols : List (BPoly F)), (combBS φ cs cols).eval (X ^ D) = CPoly.lcombS φ cs (cols.map (encB D))
  | [], _ => by simp [combBS, CPoly.lcombS]
  | _ :: _, [] => by simp [combBS, CPoly.lcombS]
  | c :: cs, W :: cols => by
    have := eval_combBS φ D cs cols
    simp only [combBS, CPoly.lcombS, List.zipWith_cons_cons, List.sum_cons, List.map_cons]
      at this ⊢
    rw [eval_add, eval_mul, eval_C, this, toPoly_encB, eval_map_Xpow]

/-- **Completeness of the exactness test**: a solution over any extension field is found. -/
theorem exactTest_complete {K' : Type*} [Field K'] (φ : F →+* K') (f : CPoly F) (n : ℕ)
    (hn : 0 < n) (Mm T : BPoly F) (basis : List (ℕ × ℕ)) (cs : List K')
    (hlen : cs.length = basis.length)
    (h : combBS φ cs (exactCols f n hn Mm basis) = (toB (reduceB f n hn T)).map (mapRingHom φ)) :
    exactTest f n hn Mm T basis ≠ none := by
  classical
  unfold exactTest
  refine CPoly.linSolve_complete_map φ _ _ cs (by rw [List.length_map, exactCols, List.length_map, hlen]) ?_
  rw [← eval_combBS, h, toPoly_encB, eval_map_Xpow]

end Sem

end Sup
