import RischTragerBronstein.Algebraic.EllLog
import RischTragerBronstein.Algebraic.EllDecide
import RischTragerBronstein.Elliptic.NLBound
import RischTragerBronstein.Computable.NullSpace

/-!
# The decision procedure for elliptic integrals with rational logarithmic part

Integrands `(B(x) + ∑ᵢ (zᵢ/D) βᵢ / (x − αᵢ)) / y` on `y² = x³ + ax² + bx + c` (`a, b, c ∈ ℤ`,
squarefree), `Pᵢ = (αᵢ, βᵢ) ∈ E(ℚ)`, `βᵢ ≠ 0`, `αᵢ` distinct. `ellDecide`:

1. the Nagell–Lutz torsion test on `S = ∑ zᵢ Pᵢ`; if `S` has infinite order the integral is not
   elementary (`ell_torsion_of_elementary`);
2. if `n S = 0`: an (untrusted) linear solve for `u = A + B y` vanishing to order `n |zᵢ|` at
   `(αᵢ, sign(zᵢ) βᵢ)` (Hensel-lifted local expansions of `y`), the remainder `R` of
   `G − (1/(nD)) M/N`, and the kernel check of `G = (1/(nD)) M/N + R`; then the integral is
   elementary iff `∫ R/y` is (`ell_log_reduce`), which `hypRed` decides (`hyp_decides`).

`ellDecide_spec`: `some b` is always the correct answer.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace EllAlgo

open CPoly

variable {K : Type*} [Field K] [DecidableEq K]

/-- `p(t + α)` (Horner). -/
def shiftPoly (p : CPoly K) (α : K) : CPoly K :=
  p.foldr (fun c acc ↦ add [c] (mul [α, 1] acc)) []

/-- The first `m` coefficients (padded). -/
def padTo (m : ℕ) (l : CPoly K) : CPoly K := l.take m ++ List.replicate (m - l.length) 0

/-- One Hensel step: fix the `tᵏ` coefficient of `Y²` to be that of `pt`. -/
def sqrtStep (pt : CPoly K) (y₀ : K) (Y : CPoly K) (k : ℕ) : CPoly K :=
  add Y (monomial k ((sub pt (mul Y Y)).getD k 0 / (2 * y₀)))

/-- `Y` with `Y(0) = y₀` and `Y² ≡ pt mod tᵐ` (when `pt(0) = y₀² ≠ 0`): the Taylor expansion of
`√(p(t + α))`. -/
def sqrtSeries (pt : CPoly K) (y₀ : K) (m : ℕ) : CPoly K :=
  ((List.range (m - 1)).map (· + 1)).foldl (sqrtStep pt y₀) [y₀]

/-- The local conditions of `xʲ` (`isB = false`) or `xʲ y` (`isB = true`) at the points
`(α, y₀, m)`: the first `m` Taylor coefficients at `α`. -/
def colOf (p : CPoly K) (pts : List (K × K × ℕ)) (isB : Bool) (j : ℕ) : CPoly K :=
  (pts.map fun q ↦
    let xj := shiftPoly (monomial j 1) q.1
    padTo q.2.2 (if isB then mul xj (sqrtSeries (shiftPoly p q.1) q.2.1 q.2.2) else xj)).flatten

/-- The number of coefficients of `A` (`deg A ≤ M₀/2`, `M₀ = ∑ m`). -/
def ellNa (pts : List (K × K × ℕ)) : ℕ := (pts.map fun q ↦ q.2.2).sum / 2 + 1

/-- The number of coefficients of `B` (`deg B ≤ (M₀ − 3)/2`). -/
def ellNb (pts : List (K × K × ℕ)) : ℕ := ((pts.map fun q ↦ q.2.2).sum - 1) / 2

/-- The unknowns: `xʲ` (`false`) and `xʲ y` (`true`). -/
def ellIdx (na nb : ℕ) : List (Bool × ℕ) :=
  (List.range na).map (fun j ↦ (false, j)) ++ (List.range nb).map (fun j ↦ (true, j))

/-- The columns of the linear system. -/
def ellCols (p : CPoly K) (pts : List (K × K × ℕ)) (na nb : ℕ) : List (CPoly K) :=
  (ellIdx na nb).map fun bj ↦ colOf p pts bj.1 bj.2

/-- **Untrusted solver**: `A + B y` vanishing to order `m` at each `(α, y₀)`, with
`deg A ≤ M₀/2`, `deg B ≤ (M₀ − 3)/2`, `M₀ = ∑ m`. -/
def ellSolve (p : CPoly K) (pts : List (K × K × ℕ)) : Option (CPoly K × CPoly K) :=
  match (nullBasis (ellCols p pts (ellNa pts) (ellNb pts))).find?
      (fun w ↦ !isZero (w.take (ellNa pts + ellNb pts))) with
  | some w => some (w.take (ellNa pts), (w.drop (ellNa pts)).take (ellNb pts))
  | none => none

/-- `G = Gn / Gd = B + ∑ (z/D) β / (x − α)`. -/
def fracG (B : CPoly K) (D : ℕ) : List (K × K × ℤ) → CPoly K × CPoly K
  | [] => (B, [1])
  | q :: t => (add (mul (fracG B D t).1 [-q.1, 1]) (smul ((q.2.2 : K) / D * q.2.1) (fracG B D t).2),
      mul (fracG B D t).2 [-q.1, 1])

/-- `x³ + ax² + bx + c`. -/
def pOf (a b c : ℤ) : CPoly ℚ := [(c : ℚ), b, a, 1]

lemma nonsingular_of (a b c : ℤ) {x y : ℚ} (h : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c ∧ y ≠ 0) :
    (EllNL.W a b c).toAffine.Nonsingular x y := by
  rw [nonsingular_iff']
  refine ⟨(EllNL.equation_W a b c).mpr h.1, Or.inr ?_⟩
  simp only [EllNL.W, zero_mul, add_zero]
  exact mul_ne_zero two_ne_zero h.2

/-- The point `(α, β)` (or `0` if it is not a point with `β ≠ 0`). -/
def ptOf (a b c : ℤ) (q : ℚ × ℚ × ℤ) : (EllNL.W a b c).toAffine.Point :=
  if h : q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0 then
    Point.some _ _ (nonsingular_of a b c h) else 0

/-- The order of a torsion point (searching `1, …, fuel`). -/
def ordOf {a b c : ℤ} (S : (EllNL.W a b c).toAffine.Point) (fuel : ℕ) : ℕ :=
  (((List.range fuel).find? fun k ↦ decide ((k + 1) • S = 0)).map (· + 1)).getD 0

/-- The norm `A² − B² p`. -/
def certN (p : CPoly K) (AB : CPoly K × CPoly K) : CPoly K :=
  sub (mul AB.1 AB.1) (mul (mul AB.2 AB.2) p)

/-- `M = 2p(AB′ − A′B) + ABp′`. -/
def certM (p : CPoly K) (AB : CPoly K × CPoly K) : CPoly K :=
  add (mul (mul [2] p) (sub (mul AB.1 (deriv AB.2)) (mul (deriv AB.1) AB.2)))
    (mul (mul AB.1 AB.2) (deriv p))

/-- The remainder `R = G − c M/N` (a polynomial when the certificate is right). -/
def certR (p : CPoly K) (AB : CPoly K × CPoly K) (G : CPoly K × CPoly K) (cc : K) : CPoly K :=
  (divMod (sub (mul G.1 (certN p AB)) (mul G.2 (smul cc (certM p AB))))
    (mul G.2 (certN p AB))).1

/-- The kernel check `Gn N = Gd (c M + R N)`. -/
def certCheck (p : CPoly K) (AB : CPoly K × CPoly K) (G : CPoly K × CPoly K) (cc : K) : Bool :=
  !isZero (certN p AB) && !isZero G.2 && beq (mul G.1 (certN p AB))
    (mul G.2 (add (smul cc (certM p AB)) (mul (certR p AB G cc) (certN p AB))))

/-- The local data `(αᵢ, sign(zᵢ) βᵢ, n |zᵢ|)` of the function `u` to find. -/
def ptsQ (pts : List (K × K × ℤ)) (n : ℕ) : List (K × K × ℕ) :=
  pts.map fun q ↦ (q.1, (Int.sign q.2.2 : K) * q.2.1, n * q.2.2.natAbs)

/-- The certificate step: `some (R-reduction is zero)` after a successful kernel check. -/
def ellCert (a b c : ℤ) (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ)) (D n : ℕ) : Option Bool :=
  match ellSolve (pOf a b c) (ptsQ pts n) with
  | none => none
  | some AB =>
    if certCheck (pOf a b c) AB (fracG B D pts) (1 / ((n : ℚ) * D)) then
      some (isZero (hypRed (pOf a b c) (certR (pOf a b c) AB (fracG B D pts) (1 / ((n : ℚ) * D)))).2)
    else none

/-- **The decision procedure** (`none`: invalid input or fuel exhausted). -/
def ellDecide (a b c : ℤ) (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ)) (D fuel : ℕ) : Option Bool :=
  if pts.all (fun q ↦ decide (q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)) &&
      decide (pts.map Prod.fst).Nodup && decide (D ≠ 0) then
    let S := (pts.map fun q ↦ q.2.2 • ptOf a b c q).sum
    match EllNL.torsionTest a b c S fuel with
    | some false => some false
    | some true => ellCert a b c B pts D (ordOf S fuel)
    | none => none
  else none

/-! ### Correctness -/

lemma toPoly_pOf (a b c : ℤ) :
    toPoly (pOf a b c) = X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) := by
  simp only [pOf, toPoly_cons, toPoly_nil, map_one]; ring

lemma toPoly_lin (α : K) : toPoly ([-α, 1] : CPoly K) = X - C α := by
  simp only [toPoly_cons, toPoly_nil, map_one, map_neg]; ring

lemma sum_map_eq_fin {M : Type*} [AddCommMonoid M] {β : Type*} (g : β → M) :
    ∀ l : List β, (l.map g).sum = ∑ i : Fin l.length, g l[i]
  | [] => by simp
  | q :: t => by
    rw [List.map_cons, List.sum_cons, sum_map_eq_fin g t]
    show _ = ∑ i : Fin (t.length + 1), g (q :: t)[i]
    rw [Fin.sum_univ_succ]
    simp

open Differential in
lemma fracG_spec {E : Type*} [Field E] [CharZero E] (x : E) (hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0)
    (B : CPoly ℚ) (D : ℕ) : ∀ pts : List (ℚ × ℚ × ℤ),
    toPoly (fracG B D pts).2 ≠ 0 ∧ aeval x (toPoly (fracG B D pts).1) /
      aeval x (toPoly (fracG B D pts).2) = aeval x (toPoly B) + (pts.map fun q ↦
        (((q.2.2 : ℚ) / D * q.2.1 : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum
  | [] => by
    refine ⟨by simp [fracG], ?_⟩
    simp [fracG]
  | q :: t => by
    obtain ⟨h0, h1⟩ := fracG_spec x hne B D t
    have hl : X - C q.1 ≠ 0 := X_sub_C_ne_zero _
    have hlx : x - ((q.1 : ℚ) : E) ≠ 0 := by
      have := hne _ hl; simpa using this
    have hdx := hne _ h0
    refine ⟨?_, ?_⟩
    · simp only [fracG, toPoly_mul, toPoly_lin]; exact mul_ne_zero h0 hl
    · simp only [fracG, toPoly_mul, toPoly_add, toPoly_smul, toPoly_lin, map_mul, map_add,
        map_sub, aeval_X, aeval_C, eq_ratCast, List.map_cons, List.sum_cons]
      rw [add_left_comm, ← h1]
      push_cast
      field_simp
      ring

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `ellDecide`**: an answer `some b` is the truth. -/
theorem ellDecide_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (B : CPoly ℚ) (pts : List (ℚ × ℚ × ℤ)) (D fuel : ℕ) (ans : Bool)
    (h : ellDecide a b c B pts D fuel = some ans) :
    ans = true ↔ HasElementaryIntegral ((aeval x (toPoly B) + (pts.map fun q ↦
      (((q.2.2 : ℚ) / D * q.2.1 : ℚ) : E) / (x - ((q.1 : ℚ) : E))).sum) / y) := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hp : toPoly (pOf a b c) = X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) :=
    toPoly_pOf a b c
  have hy' : y ^ 2 = aeval x (toPoly (pOf a b c)) := by rw [hp, hy]; simp
  unfold ellDecide at h
  split_ifs at h with hval
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hval
  obtain ⟨⟨hon, hnd⟩, hD⟩ := hval
  dsimp only at h
  split at h
  · -- infinite order
    rename_i hT
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.false_eq_true, false_iff]
    intro hf
    have hns := EllNL.torsionTest_spec a b c _ fuel false hT
    simp only [Bool.false_eq_true, false_iff] at hns
    apply hns
    have hP : ∀ i : Fin pts.length, (EllNL.W a b c).toAffine.Nonsingular pts[i].1 pts[i].2.1 :=
      fun i ↦ nonsingular_of a b c (hon _ (List.getElem_mem _))
    have hinj : Set.InjOn (fun i : Fin pts.length ↦ pts[i].1)
        ((Finset.univ : Finset (Fin pts.length)) : Set (Fin pts.length)) := by
      intro i _ j _ hij
      have := (List.Nodup.getElem_inj_iff hnd (i := i) (j := j)
        (hi := by simp) (hj := by simp)).mp (by simpa using hij)
      exact Fin.ext this
    have key := ell_torsion_of_elementary hC hCall x y hx a b c hsq hy hgen (toPoly B)
      (Finset.univ : Finset (Fin pts.length)) (fun i ↦ pts[i].1) (fun i ↦ pts[i].2.1) hP
      (fun i _ ↦ (hon _ (List.getElem_mem _)).2) hinj (fun i ↦ pts[i].2.2) D hD (by
        rw [sum_map_eq_fin] at hf; exact hf)
    rw [sum_map_eq_fin]
    convert key using 2 with i
    rw [ptOf]
    split_ifs with hh
    · rfl
    · exact absurd (hon _ (List.getElem_mem _)) hh
  · -- torsion: the certificate
    rename_i hT
    unfold ellCert at h
    split at h
    · exact absurd h (by simp)
    rename_i AB hAB
    split_ifs at h with hchk
    simp only [Option.some.injEq] at h
    subst h
    set cc : ℚ := 1 / ((ordOf (pts.map fun q ↦ q.2.2 • ptOf a b c q).sum fuel : ℚ) * D)
    unfold certCheck at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, certN, certM] at hchk
    obtain ⟨⟨hN, hG⟩, hbeq⟩ := hchk
    have hN' : toPoly AB.1 ^ 2 - toPoly AB.2 ^ 2 * toPoly (pOf a b c) ≠ 0 := by
      intro h0; rw [← Bool.not_eq_true, isZero_iff] at hN; apply hN
      simp only [toPoly_sub, toPoly_mul]; linear_combination h0
    have hG' : toPoly (fracG B D pts).2 ≠ 0 := by
      intro h0; rw [← Bool.not_eq_true, isZero_iff] at hG; exact hG h0
    have hid := (beq_iff _ _).mp hbeq
    have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
      rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
    simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_smul, toPoly_deriv, h2] at hid
    have hp0 : toPoly (pOf a b c) ≠ 0 := by rw [hp]; exact hsq.ne_zero
    have hred := ell_log_reduce hC x y hx (toPoly (pOf a b c)) hp0 hy'
      (toPoly (fracG B D pts).1) (toPoly (fracG B D pts).2) (toPoly AB.1) (toPoly AB.2)
      (toPoly (certR (pOf a b c) AB (fracG B D pts) cc)) cc hG' hN'
      (by linear_combination hid)
    have hdeg3 : (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) : ℚ[X]).natDegree = 3 := by
      compute_degree!
    have hdec := hyp_decides hC hCall x y hx (pOf a b c) (by rw [hp]; exact hsq)
      (by rw [hp, hdeg3]; decide) hy' hgen (certR (pOf a b c) AB (fracG B D pts) cc)
    obtain ⟨_, hfr⟩ := fracG_spec x hne B D pts
    rw [← hfr, div_div, hred, hdec]
  · exact absurd h (by simp)

end Spec

end EllAlgo
