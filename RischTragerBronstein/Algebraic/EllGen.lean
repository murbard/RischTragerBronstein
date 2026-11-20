import RischTragerBronstein.Algebraic.EllComplete
import RischTragerBronstein.Computable.RatRoots

/-!
# General elliptic integrands `∫ A(x) / (D(x) √p(x)) dx`

`ellDecideGen a b c A D fuel`: an (untrusted) Hermite reduction with `V = D` writes

  `A / (D y) = (W/D · y)′ + (B₀ + ∑_α c_α / (x − α)) / y`

over the rational roots `α` of `D` (`deg B₀ ≤ 1`); each residue `c_α = (z_α/D′) β_α` with
`β_α = √p(α) ∈ ℚ`; the identity is checked by the kernel, and `ellDecide` decides the remainder.
`ellDecideGen_spec`: an answer `some b` is always correct.
-/

open Polynomial

namespace EllAlgo

open CPoly

/-- The exact rational square root, if any. -/
def qsqrt (q : ℚ) : Option ℚ :=
  if 0 ≤ q ∧ q.num.natAbs.sqrt * q.num.natAbs.sqrt = q.num.natAbs ∧ q.den.sqrt * q.den.sqrt = q.den
  then some ((q.num.natAbs.sqrt : ℚ) / q.den.sqrt) else none

lemma qsqrt_spec {q β : ℚ} (h : qsqrt q = some β) : β ^ 2 = q := by
  unfold qsqrt at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨h0, h1, h2⟩ := hc
  have hn : ((q.num.natAbs.sqrt : ℚ)) ^ 2 = (q.num.natAbs : ℚ) := by
    rw [sq]; exact_mod_cast h1
  have hd : ((q.den.sqrt : ℚ)) ^ 2 = (q.den : ℚ) := by
    rw [sq]; exact_mod_cast h2
  have hnum : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast Rat.num_nonneg.mpr h0)]
  rw [div_pow, hn, hd, hnum]
  exact Rat.num_div_den q

lemma qsqrt_sq (β : ℚ) : (qsqrt (β ^ 2)).isSome := by
  unfold qsqrt
  rw [if_pos]
  · rfl
  refine ⟨sq_nonneg β, ?_, ?_⟩
  · rw [Rat.num_pow, Int.natAbs_pow, Nat.sqrt_eq', sq]
  · rw [Rat.den_pow, Nat.sqrt_eq', sq]

/-- `∏ (x − α)`. -/
def linProd (αs : List ℚ) : CPoly ℚ := (αs.map fun α ↦ ([-α, 1] : CPoly ℚ)).foldr mul [1]

/-- The columns of the Hermite system `2 A V² L = D L (2(W′V − WV′)p + WVp′) + 2 D V² L B₀ +
2 D V² ∑ c_α L/(x − α)` (`V = D`, `L = ∏ (x − α)`). -/
def genCols (p A D : CPoly ℚ) (αs : List ℚ) (dW nB : ℕ) : List (CPoly ℚ) :=
  let L := linProd αs
  mul [2] (mul A (mul (mul D D) L)) ::
    ((List.range (dW + 1)).map fun i ↦ mul (mul D L)
      (add (mul [2] (mul (sub (mul (deriv (monomial i 1)) D) (mul (monomial i 1) (deriv D))) p))
        (mul (mul (monomial i 1) D) (deriv p)))) ++
    ((List.range nB).map fun j ↦ mul [2] (mul (monomial j 1) (mul (mul D D) (mul D L)))) ++
    ((List.range αs.length).map fun k ↦ mul [2] (mul (mul D D) (mul D
      (linProd (αs.eraseIdx k)))))

/-- The rational points and integer residues from the residues `c_α` (`z/D′ · β = c`). -/
def residuePts (p : CPoly ℚ) (αs cs : List ℚ) : Option (List (ℚ × ℚ × ℤ) × ℕ) :=
  let data := (αs.zip cs).filter fun q ↦ q.2 ≠ 0
  let betas := data.map fun q ↦ qsqrt (evalQ p q.1)
  if betas.all (fun o ↦ o.isSome && o != some 0) then
    let rs := (data.zip betas).map fun q ↦ (q.1.1, (q.2.getD 1), q.1.2 / q.2.getD 1)
    let D' := (rs.map fun q ↦ q.2.2.den).foldr Nat.lcm 1
    some (rs.map fun q ↦ (q.1, q.2.1, (q.2.2 * (D' : ℚ)).num), D')
  else none
where
  /-- Evaluation. -/
  evalQ (P : CPoly ℚ) (q : ℚ) : ℚ := P.foldr (fun a acc ↦ a + q * acc) 0

/-- **Untrusted Hermite solver**: `(W, B₀, pts, D′)`. -/
def ellHermite (p A D : CPoly ℚ) : Option (CPoly ℚ × CPoly ℚ × List (ℚ × ℚ × ℤ) × ℕ) :=
  let αs := (ratRootsQ D).dedup.filter fun α ↦ residuePts.evalQ D α == 0 &&
    residuePts.evalQ p α != 0
  let nB := (trim p).length - 2
  let dW := A.length + D.length
  match (nullBasis (genCols p A D αs dW nB)).find? (fun u ↦ u.getD 0 0 ≠ 0) with
  | some u =>
    let co := fun k ↦ -(u.getD k 0) / u.getD 0 0
    let W := (List.range (dW + 1)).map fun i ↦ co (i + 1)
    let B₀ := (List.range nB).map fun j ↦ co (dW + 2 + j)
    let cs := (List.range αs.length).map fun k ↦ co (dW + 2 + nB + k)
    match residuePts p αs cs with
    | some (pts, D') => some (W, B₀, pts, D')
    | none => none
  | none => none

/-- The kernel check `A · 2 V² Gd = D ((2(W′V − WV′)p + WVp′) Gd + 2 Gn V²)`, `V = D`. -/
def genCheck (p A D W : CPoly ℚ) (G : CPoly ℚ × CPoly ℚ) : Bool :=
  !isZero D && !isZero G.2 && beq (mul (mul A [2]) (mul (mul D D) G.2))
    (mul D (add (mul (add (mul (mul [2] (sub (mul (deriv W) D) (mul W (deriv D)))) p)
      (mul (mul W D) (deriv p))) G.2) (mul (mul [2] G.1) (mul D D))))

/-- **The decision procedure for `∫ A / (D y)`** (`none`: outside the class or out of fuel). -/
def ellDecideGen (a b c : ℤ) (A D : CPoly ℚ) (fuel : ℕ) : Option Bool :=
  match ellHermite (pOf a b c) A D with
  | some (W, B₀, pts, D') =>
    if genCheck (pOf a b c) A D W (fracG B₀ D' pts) then ellDecide a b c B₀ pts D' fuel
    else none
  | none => none

/-! ### Correctness -/

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

omit [Algebra Kc E] [Differential Kc] [DifferentialAlgebra Kc E] [CharZero Kc] in
/-- `A / (D y) = (W/V · y)′ + (Gn/Gd) / y` from the polynomial identity. -/
lemma gen_identity (x y : E) (hx : x′ = 1) (p A D W V Gn Gd : ℚ[X])
    (hy : y ^ 2 = aeval x p) (hy0 : y ≠ 0) (hD : aeval x D ≠ 0) (hV : aeval x V ≠ 0)
    (hGd : aeval x Gd ≠ 0)
    (hid : A * 2 * V ^ 2 * Gd = D * ((2 * (derivative W * V - W * derivative V) * p +
      W * V * derivative p) * Gd + 2 * Gn * V ^ 2)) :
    aeval x A / (aeval x D * y) = (aeval x W / aeval x V * y)′ + aeval x Gn / aeval x Gd / y := by
  have hyd : y′ = aeval x (derivative p) / (2 * y) := by
    have := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul] at this
    rw [deriv_aeval_rat x hx] at this
    rw [eq_div_iff (mul_ne_zero two_ne_zero hy0)]
    linear_combination this
  have h2 := congrArg (aeval x) hid
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat] at h2
  rw [Derivation.leibniz, Derivation.leibniz_div, hyd, deriv_aeval_rat x hx,
    deriv_aeval_rat x hx]
  simp only [smul_eq_mul]
  rw [← hy] at h2
  field_simp
  linear_combination h2

lemma hasElementaryIntegral_deriv_add_iff' {F : Type*} [Field F] [Differential F] (g β : F) :
    HasElementaryIntegral (g′ + β) ↔ HasElementaryIntegral β := by
  constructor
  · intro h
    have := h.sub_in (hasElementaryIntegralIn_deriv g)
    rwa [add_sub_cancel_left] at this
  · intro h
    rw [add_comm]
    exact h.add_in (hasElementaryIntegralIn_deriv g)

/-- **Correctness of `ellDecideGen`**: an answer `some b` is the truth about `∫ A / (D y)`. -/
theorem ellDecideGen_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (fuel : ℕ) (ans : Bool) (h : ellDecideGen a b c A D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hp : toPoly (pOf a b c) = X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) :=
    toPoly_pOf a b c
  have hy' : y ^ 2 = aeval x (toPoly (pOf a b c)) := by rw [hp, hy]; simp
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hne _ (show toPoly (pOf a b c) ≠ 0 by rw [hp]; exact hsq.ne_zero)
    rw [← hy']; ring
  unfold ellDecideGen at h
  split at h
  · rename_i W B₀ pts D' _
    split_ifs at h with hchk
    have hans := ellDecide_spec hC hCall x y hx a b c hsq hy hgen B₀ pts D' fuel ans h
    unfold genCheck at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, isZero_iff] at hchk
    obtain ⟨⟨hD0, hG0⟩, hbeq⟩ := hchk
    have hid := (beq_iff _ _).mp hbeq
    have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
      rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
    simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, h2] at hid
    have e := gen_identity x y hx (toPoly (pOf a b c)) (toPoly A) (toPoly D) (toPoly W) (toPoly D)
      (toPoly (fracG B₀ D' pts).1) (toPoly (fracG B₀ D' pts).2) hy' hy0 (hne _ hD0) (hne _ hD0)
      (hne _ hG0) (by linear_combination hid)
    obtain ⟨_, hfr⟩ := fracG_spec x hne B₀ D' pts
    rw [e, hasElementaryIntegral_deriv_add_iff', hfr]
    exact hans
  · exact absurd h (by simp)

end Spec

end EllAlgo
