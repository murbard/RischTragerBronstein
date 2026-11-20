import RischTragerBronstein.Algebraic.EllQuadOrbit
import RischTragerBronstein.Elliptic.DV.ChainF
import RischTragerBronstein.Algebraic.EllQuadCert
import RischTragerBronstein.Algebraic.EllComplete
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# The decision procedure for a quadratic orbit of poles

`∫ A(x) dx / (D(x) √p(x))`, `p = x³ + ax² + bx + c`, `D` a monic irreducible quadratic whose roots
`α, σα` lie in `F = ℚ(√d)` and whose poles lie over points `P = (α, β)`, `σP` of `E(F)`. The
residue `r = A(α)/(D′(α) β) = u + v√d` is split along `1, √d`:

* if `u ≠ 0` and `P + σP` has infinite order, or `v ≠ 0` and `P − σP` has infinite order
  (verified torsion test at an auxiliary prime `p₀`): **not elementary** (`pair_not_elem`);
* otherwise, with `n` the order of the point, the linear solve over `F` finds `A + B y` with
  divisor `n([P] + [σP]) − 2n[O]` (resp. `n([P] + [−σP]) − 2n[O]`) and the kernel check removes the
  logarithmic part (`certPart_spec`); the polynomial remainder is reduced by `hypRed` over `F`,
  and the integral is elementary iff the holomorphic remainder vanishes (`quadCert_spec`,
  `hyp_decidesF`).

`quadOrbitDecide_spec`: every answer is correct. `quadOrbitDecide_ne_none` and
`orbitData_ne_none`: on the class the procedure always answers (`certPart_ne_none` uses the
Dedekind-domain existence argument `EllAlgo.exists_localW` over `F`). `quadOrbitDecide_decides`
combines both.
-/

open Polynomial Differential

namespace EllQuad

open CPoly EllDV

variable {d : ℤ}

local notation "F" => QuadraticAlgebra ℚ (d : ℚ) 0

/-- Evaluation of a rational polynomial at a point of `F`. -/
def evalQF (q : CPoly ℚ) (z : F) : F := q.foldr (fun (t : ℚ) (acc : F) ↦ (t : F) + z * acc) 0

/-- A square root in `F` (if any): `(u + v√d)² = R + I√d`. -/
def sqrtF (w : F) : Option F :=
  let R := w.re
  let I := w.im
  match EllAlgo.qsqrt (R ^ 2 - d * I ^ 2) with
  | some n =>
    let cands : List F := [(R + n) / 2, (R - n) / 2].filterMap fun t ↦
      match EllAlgo.qsqrt t with
      | some u => if u = 0 then (match EllAlgo.qsqrt (R / d) with
          | some v => some ⟨0, v⟩ | none => none) else some ⟨u, I / (2 * u)⟩
      | none => none
    cands.find? fun z ↦ z * z = w
  | none => none

/-- The number of affine points of the reduced curve (computable). -/
def redCount (p : ℕ) [NeZero p] (a b c : ℤ) : ℕ :=
  (Finset.univ.filter fun st : ZMod p × ZMod p ↦
    st.2 ^ 2 = st.1 ^ 3 + (a : ZMod p) * st.1 ^ 2 + (b : ZMod p) * st.1 + (c : ZMod p)).card

/-- The data: `α, σα, β, σβ, r`. -/
def orbitData (a b c : ℤ) (A D : CPoly ℚ) : Option (F × F × F × F × F) :=
  if D.length = 3 ∧ D.getD 2 0 = 1 then
    let e := D.getD 1 0
    let g := D.getD 0 0
    match EllAlgo.qsqrt ((e ^ 2 - 4 * g) / d) with
    | some k =>
      if k = 0 then none else
        let α : F := ⟨-e / 2, k / 2⟩
        let σα : F := ⟨-e / 2, -k / 2⟩
        let pa : F := α ^ 3 + (a : F) * α ^ 2 + (b : F) * α + (c : F)
        match sqrtF pa with
        | some β =>
          if β = 0 ∨ β * β ≠ pa ∨ evalQF (CPoly.deriv D) α = 0 then none else
            let σβ : F := ⟨β.re, -β.im⟩
            some (α, σα, β, σβ, evalQF A α / (evalQF (CPoly.deriv D) α * β))
        | none => none
    | none => none
  else none

variable [Fact (¬IsSquare (d : ℚ))]

/-- The curve over `F`. -/
def pF (a b c : ℤ) : CPoly F := [(c : F), (b : F), (a : F), 1]

/-- A rational polynomial over `F`. -/
def liftF (q : CPoly ℚ) : CPoly F := q.map fun (t : ℚ) ↦ (t : F)

/-- The order of a point of `E(F)` (searching `1, …, N`; `0` if not found). -/
def ordF (a b c : ℤ) (o : Option (F × F)) (N : ℕ) : ℕ :=
  (((List.range N).find? fun k ↦ (mulPtF a b c o (k + 1)).isNone).map (· + 1)).getD 0

/-- The logarithmic certificate for a pair of points with residue `1` each (`n` = torsion order):
`A + B y` from the linear solve, then the remainder `R` of `G − (1/n) M/N` after the kernel check. -/
def certPart (a b c : ℤ) (pts : List (F × F × ℤ)) (n : ℕ) : Option (CPoly F) :=
  match EllAlgo.ellSolve (pF a b c) (EllAlgo.ptsQ pts n) with
  | some AB =>
    if EllAlgo.certCheck (pF a b c) AB (EllAlgo.fracG [] 1 pts) (1 / ((n : F) * ((1 : ℕ) : F)))
    then some (EllAlgo.certR (pF a b c) AB (EllAlgo.fracG [] 1 pts) (1 / ((n : F) * ((1 : ℕ) : F))))
    else none
  | none => none

/-- The certificate branch: remove both logarithmic parts, then reduce the polynomial remainder. -/
def quadCert (a b c : ℤ) (A D : CPoly ℚ) (α σα β σβ r : F) (N : ℕ) : Option Bool :=
  let R1 : Option (CPoly F) := if r.re = 0 then some [] else
    certPart a b c [(α, β, 1), (σα, σβ, 1)]
      (ordF a b c (addPtF a b c (some (α, β)) (some (σα, σβ))) N)
  let R2 : Option (CPoly F) := if r.im = 0 then some [] else
    certPart a b c [(α, β, 1), (σα, -σβ, 1)]
      (ordF a b c (addPtF a b c (some (α, β)) (some (σα, -σβ))) N)
  match R1, R2 with
  | some R1, some R2 =>
    some (isZero (hypRed (pF a b c)
      (add (liftF (divMod A D).1) (add (smul ((r.re : ℚ) : F) R1) (smul ⟨0, r.im⟩ R2)))).2)
  | _, _ => none

/-- **The procedure.** `some false`: not elementary; `some true`: elementary; `none`: undecided
(input outside the class, or no certificate found). -/
def quadOrbitDecide (a b c : ℤ) (A D : CPoly ℚ) (p0 : ℕ) [NeZero p0] : Option Bool :=
  match orbitData (d := d) a b c A D with
  | none => none
  | some (α, σα, β, σβ, r) =>
    let N := redCount p0 a b c + 1
    if r.re ≠ 0 ∧ torsionTestF a b c (addPtF a b c (some (α, β)) (some (σα, σβ))) N = false then
      some false
    else if r.im ≠ 0 ∧ torsionTestF a b c (addPtF a b c (some (α, β)) (some (σα, -σβ))) N = false
      then some false
    else quadCert a b c A D α σα β σβ r N

/-! ### Specification -/

lemma evalQF_eq (q : CPoly ℚ) (z : F) : evalQF q z = aeval z (toPoly q) := by
  induction q with
  | nil => simp [evalQF, CPoly.toPoly]
  | cons t q ih =>
    simp only [evalQF, List.foldr_cons] at ih ⊢
    rw [ih, toPoly_cons, map_add, map_mul, aeval_C, aeval_X]
    simp [Algebra.algebraMap_eq_smul_one]

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [CharZero Kc] [CharZero E]

lemma aeval_ringHom (ι : F →+* Kc) (q : ℚ[X]) (z : F) :
    ι (aeval z q) = aeval (ι z) q := by
  induction q using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial n t => simp [map_ratCast]

lemma evF_liftF (ι : F →+* Kc) (x : E) (q : CPoly ℚ) : evF ι x (liftF q) = aeval x (toPoly q) := by
  induction q with
  | nil => simp [evF, liftF, CPoly.toPoly]
  | cons t q ih =>
    simp only [evF, liftF, List.map_cons, toPoly_cons, Polynomial.map_add, Polynomial.map_mul,
      map_C, Polynomial.map_X, map_add, map_mul, aeval_C, aeval_X] at ih ⊢
    rw [ih, map_ratCast]
    simp

lemma evF_pF (ι : F →+* Kc) (x : E) (a b c : ℤ) :
    evF ι x (pF a b c) = x ^ 3 + a * x ^ 2 + b * x + c := by
  simp [evF, pF, CPoly.toPoly, map_intCast]; ring

/-- **Hensel's embedding** `ℚ(√d) → ℚ_p` from a simple square root of `d` modulo `p`. -/
lemma exists_embed {p : ℕ} [Fact p.Prime] (s : ZMod p) (hs : s ^ 2 = d) (hs' : 2 * s ≠ 0) :
    Nonempty (F →ₐ[ℚ] ℚ_[p]) := by
  obtain ⟨z, hz⟩ := hensel_root (f := X ^ 2 - C d) s (by simp [hs]) (by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, Polynomial.map_mul,
      Polynomial.map_ofNat, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X, eval_ofNat]
    simpa using hs')
  have hz2 : (z : ℚ_[p]) * z = ((d : ℚ) : ℚ_[p]) := by
    have := congrArg (fun w : ℤ_[p] ↦ (w : ℚ_[p])) hz
    simp only [map_sub, map_pow, aeval_X, aeval_C, PadicInt.coe_sub, PadicInt.coe_pow,
      PadicInt.coe_zero] at this
    simp only [algebraMap_int_eq, eq_intCast, map_intCast] at this
    push_cast at this ⊢
    rw [← sq]; linear_combination this
  exact ⟨QuadraticAlgebra.lift ⟨(z : ℚ_[p]), by rw [hz2]; simp⟩⟩

lemma d_ne_zero : (d : ℚ) ≠ 0 := fun h ↦ (Fact.out : ¬IsSquare (d : ℚ)) ⟨0, by rw [h]; ring⟩

/-- **What `orbitData` guarantees.** -/
lemma orbitData_spec {a b c : ℤ} {A D : CPoly ℚ} {α σα β σβ r : F}
    (h : orbitData (d := d) a b c A D = some (α, σα, β, σβ, r)) :
    σα = star α ∧ σβ = star β ∧ α ≠ σα ∧ β ≠ 0 ∧
      β * β = α ^ 3 + (a : F) * α ^ 2 + (b : F) * α + (c : F) ∧
      evalQF (CPoly.deriv D) α ≠ 0 ∧ r = evalQF A α / (evalQF (CPoly.deriv D) α * β) ∧
      (toPoly D).map (algebraMap ℚ F) = (X - C α) * (X - C σα) := by
  unfold orbitData at h
  split_ifs at h with hD
  obtain ⟨hlen, hlead⟩ := hD
  dsimp only at h
  split at h
  swap
  · cases h
  rename_i k hk
  split_ifs at h with hk0
  split at h
  swap
  · cases h
  rename_i β0 hβ0
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  push_neg at hc
  obtain ⟨hβne, hββ, hder⟩ := hc
  have hk2 : k ^ 2 = ((D.getD 1 0) ^ 2 - 4 * D.getD 0 0) / d := EllAlgo.qsqrt_spec hk
  have hd := d_ne_zero (d := d)
  refine ⟨?_, ?_, ?_, hβne, by rw [hββ], hder, rfl, ?_⟩
  · ext <;> simp [QuadraticAlgebra.star_mk] <;> ring
  · ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  · intro h0
    have := congrArg QuadraticAlgebra.im h0
    simp only at this
    exact hk0 (by linarith)
  · -- `D = X² + eX + g`
    have hDpoly : toPoly D = C (D.getD 0 0) + C (D.getD 1 0) * X + X ^ 2 := by
      obtain ⟨g0, e0, l, rfl⟩ : ∃ g0 e0 l, D = g0 :: e0 :: l := by
        match D, hlen with
        | g0 :: e0 :: l, _ => exact ⟨g0, e0, l, rfl⟩
      obtain ⟨t, rfl⟩ : ∃ t, l = [t] := by
        match l, hlen with
        | [t], _ => exact ⟨t, rfl⟩
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hlead ⊢
      simp [CPoly.toPoly, hlead]; ring
    rw [hDpoly]
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X]
    have e1 : (algebraMap ℚ F (D.getD 1 0)) = -((⟨-(D.getD 1 0) / 2, k / 2⟩ : F) +
        ⟨-(D.getD 1 0) / 2, -k / 2⟩) := by
      ext <;> simp [Algebra.algebraMap_eq_smul_one] <;> ring
    have e0 : (algebraMap ℚ F (D.getD 0 0)) = (⟨-(D.getD 1 0) / 2, k / 2⟩ : F) *
        ⟨-(D.getD 1 0) / 2, -k / 2⟩ := by
      ext
      · simp [Algebra.algebraMap_eq_smul_one]
        field_simp
        rw [eq_div_iff hd] at hk2
        simp only [List.getD_eq_getElem?_getD] at hk2
        linear_combination hk2
      · simp [Algebra.algebraMap_eq_smul_one]; ring
    rw [e1, e0, C_mul, C_neg, C_add]
    ring

lemma star_aeval (q : ℚ[X]) (z : F) : star (aeval z q) = aeval (star z) q := by
  induction q using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial n t =>
    simp only [aeval_monomial, star_mul', star_pow]
    congr 1
    ext <;> simp [Algebra.algebraMap_eq_smul_one]

lemma monic_of_fac {D : CPoly ℚ} {α σα : F}
    (hfac : (toPoly D).map (algebraMap ℚ F) = (X - C α) * (X - C σα)) : (toPoly D).Monic := by
  have := congrArg Polynomial.leadingCoeff hfac
  rw [leadingCoeff_map_of_injective (algebraMap ℚ F).injective] at this
  have h1 : ((X - C α) * (X - C σα) : F[X]).leadingCoeff = 1 := by
    rw [leadingCoeff_mul, leadingCoeff_X_sub_C, leadingCoeff_X_sub_C, one_mul]
  rw [h1] at this
  exact (algebraMap ℚ F).injective (by rw [this, map_one])

set_option maxHeartbeats 1600000 in
/-- **The partial fraction decomposition over the orbit.** -/
lemma integrand_split (ιE : F →+* E) (x y : E) (A D : CPoly ℚ) {α σα β σβ r : F}
    (hσα : σα = star α) (hσβ : σβ = star β) (hne : α ≠ σα) (hβ : β ≠ 0)
    (hder : evalQF (CPoly.deriv D) α ≠ 0) (hr : r = evalQF A α / (evalQF (CPoly.deriv D) α * β))
    (hfac : (toPoly D).map (algebraMap ℚ F) = (X - C α) * (X - C σα))
    (hxa : ∀ z : F, x - ιE z ≠ 0) :
    aeval x (toPoly A) / (aeval x (toPoly D) * y) =
      (aeval x (toPoly A /ₘ toPoly D) + ιE (r * β) / (x - ιE α) +
        ιE (star r * star β) / (x - ιE σα)) / y := by
  have hιQ : ∀ q : ℚ[X], aeval x q = ((q.map (algebraMap ℚ F)).eval₂ ιE x) := by
    intro q
    rw [eval₂_map, aeval_def]
    congr 1
    exact RingHom.ext_rat _ _
  have hDx : aeval x (toPoly D) = (x - ιE α) * (x - ιE σα) := by
    rw [hιQ, hfac]; simp
  have hmon : (toPoly D).Monic := by
    have := congrArg Polynomial.leadingCoeff hfac
    rw [leadingCoeff_map_of_injective (algebraMap ℚ F).injective] at this
    have h1 : ((X - C α) * (X - C σα) : F[X]).leadingCoeff = 1 := by
      rw [leadingCoeff_mul, leadingCoeff_X_sub_C, leadingCoeff_X_sub_C, one_mul]
    rw [h1] at this
    exact (algebraMap ℚ F).injective (by rw [this, map_one])
  have h2 : (toPoly D).natDegree = 2 := by
    have := congrArg natDegree hfac
    rwa [natDegree_map_eq_of_injective (algebraMap ℚ F).injective,
      natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), natDegree_X_sub_C,
      natDegree_X_sub_C] at this
  have hRdeg : (toPoly A %ₘ toPoly D).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt (toPoly A) hmon (by
      intro h1; rw [h1, natDegree_one] at h2; omega)
    omega
  have hAR := (modByMonic_add_div (toPoly A) (toPoly D)).symm
  generalize toPoly A %ₘ toPoly D = R at hAR hRdeg
  generalize toPoly A /ₘ toPoly D = Bq at hAR ⊢
  obtain ⟨R1, R0, hR10⟩ : ∃ R1 R0 : ℚ, R = C R1 * X + C R0 :=
    ⟨_, _, eq_X_add_C_of_natDegree_le_one hRdeg⟩
  -- values at the roots
  have hDα : aeval α (toPoly D) = 0 := by
    have := congrArg (fun P : F[X] ↦ P.eval α) hfac
    simp only [eval_map, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at this
    rw [aeval_def]; exact this
  have hAα : evalQF A α = (R1 : F) * α + R0 := by
    rw [evalQF_eq, hAR, map_add, map_mul, hDα, zero_mul, add_zero, hR10]
    simp [Algebra.algebraMap_eq_smul_one]
  have hD'α : evalQF (CPoly.deriv D) α = α - σα := by
    rw [evalQF_eq, toPoly_deriv]
    have := congrArg (fun P : F[X] ↦ (derivative P).eval α) hfac
    simp only [derivative_map, eval_map, derivative_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, one_mul, mul_one, eval_add, eval_sub, eval_X, eval_C, sub_self,
      add_zero] at this
    rw [aeval_def]; exact this
  have hrβ : r * β = ((R1 : F) * α + R0) / (α - σα) := by
    rw [hr, hD'α, hAα]; field_simp
  have hsrβ : star r * star β = ((R1 : F) * σα + R0) / (σα - α) := by
    rw [← star_mul', hrβ, star_div₀, hσα]
    simp only [star_add, star_mul', star_sub, star_star]
    congr 1 <;> ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  have hσ : α - σα ≠ 0 := sub_ne_zero.mpr hne
  have hσ' : σα - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hισ : ιE α - ιE σα ≠ 0 := by rw [← map_sub]; exact (map_ne_zero ιE).mpr hσ
  have h1 := hxa α
  have h2 := hxa σα
  rw [hrβ, hsrβ, hDx, map_div₀, map_div₀, map_add, map_add, map_mul, map_mul, map_sub, map_sub]
  simp only [map_ratCast]
  have hAx : aeval x (toPoly A) = (R1 : E) * x + R0 + (x - ιE α) * (x - ιE σα) * aeval x Bq := by
    rw [hAR, map_add, map_mul, hDx, hR10]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [hAx, ← div_div]
  congr 1
  have hισ' : ιE σα - ιE α ≠ 0 := by rw [← map_sub]; exact (map_ne_zero ιE).mpr hσ'
  field_simp
  ring

lemma card_RedPts (p : ℕ) [Fact p.Prime] [NeZero p] (a b c : ℤ) :
    Fintype.card (RedPts p a b c) = redCount p a b c := by
  rw [redCount, Fintype.card_congr' (show RedPts p a b c =
    {st : ZMod p × ZMod p // st.2 ^ 2 = st.1 ^ 3 + (a : ZMod p) * st.1 ^ 2 + (b : ZMod p) * st.1 +
      (c : ZMod p)} from rfl), Fintype.card_subtype]

lemma ns_of_eq {K : Type*} [Field K] [CharZero K] [DecidableEq K] (a b c : ℤ) {u w : K}
    (he : w * w = u ^ 3 + (a : K) * u ^ 2 + (b : K) * u + (c : K)) (hw : w ≠ 0) :
    (W K a b c).toAffine.Nonsingular u w := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  refine ⟨(equation_W a b c).mpr (by unfold OnCurve; rw [sq]; exact he), Or.inr ?_⟩
  simp only [W, W0, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₃, map_zero, zero_mul, add_zero]
  exact mul_ne_zero two_ne_zero hw

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma x_sub_const_ne (hC : ∀ c : Kc, c′ = 0) (x : E) (hx : x′ = 1) (k : Kc) :
    x - algebraMap Kc E k ≠ 0 := fun h0 ↦ by
  have := congrArg (fun t : E ↦ t′) h0
  simp only [map_sub, hx, deriv_algebraMap, hC, map_zero, sub_zero] at this
  exact one_ne_zero this

lemma toPoly_pF (a b c : ℤ) :
    toPoly (pF (d := d) a b c) = (toPoly (EllAlgo.pOf a b c)).map (algebraMap ℚ F) := by
  simp [pF, EllAlgo.pOf, CPoly.toPoly, map_intCast]

lemma W_eq : W F a b c = (⟨0, (a : F), 0, (b : F), (c : F)⟩ : WeierstrassCurve F) := by
  ext <;> simp [W, W0, WeierstrassCurve.baseChange, WeierstrassCurve.map]

lemma toPoly_pF' (a b c : ℤ) : toPoly (pF (d := d) a b c) =
    X ^ 3 + C (a : F) * X ^ 2 + C (b : F) * X + C (c : F) := by
  simp [pF, CPoly.toPoly]; ring

lemma squarefree_pF {a b c : ℤ}
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ))) :
    Squarefree (toPoly (pF (d := d) a b c)) := by
  rw [toPoly_pF, EllAlgo.toPoly_pOf]
  have hsep : (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)).Separable :=
    (PerfectField.separable_iff_squarefree).mpr hsq
  exact (hsep.map).squarefree

set_option maxHeartbeats 3200000 in
/-- **Completeness of the certificate step**: if `n (P₁ + P₂) = 0` the certificate is found. -/
lemma certPart_ne_none {a b c : ℤ}
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    {α1 β1 α2 β2 : F} (hne : α1 ≠ α2) (hβ1 : β1 ≠ 0) (hβ2 : β2 ≠ 0)
    (h1 : (W F a b c).toAffine.Nonsingular α1 β1) (h2 : (W F a b c).toAffine.Nonsingular α2 β2)
    (n : ℕ) (hn : 1 ≤ n) (hrel : n • (WeierstrassCurve.Affine.Point.some α1 β1 h1 + WeierstrassCurve.Affine.Point.some α2 β2 h2) = 0) :
    certPart a b c [(α1, β1, 1), (α2, β2, 1)] n ≠ none := by
  set pts : List (F × F × ℤ) := [(α1, β1, 1), (α2, β2, 1)] with hpts
  have hQ : EllAlgo.ptsQ pts n = [(α1, β1, n), (α2, β2, n)] := by
    simp [EllAlgo.ptsQ, hpts]
  set pC := pF (d := d) a b c
  have hpC := toPoly_pF' (d := d) a b c
  have hsqF := squarefree_pF (d := d) hsq
  -- the function `A + B y`
  let α : Fin 2 → F := ![α1, α2]
  let yv : Fin 2 → F := ![β1, β2]
  let m : Fin 2 → ℕ := ![n, n]
  have hns : ∀ i, (W F a b c).toAffine.Nonsingular (α i) (yv i) := by
    intro i; fin_cases i; exacts [h1, h2]
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 2)), m i •
      (WeierstrassCurve.Affine.Point.some _ _ (hns i) : (W F a b c).toAffine.Point) = 0 := by
    rw [Fin.sum_univ_two, ← hrel, nsmul_add]; rfl
  obtain ⟨A, B, hAB, hA, hB, hloc⟩ := EllAlgo.exists_localW (a : F) (b : F) (c : F) pC hpC
    (W F a b c) W_eq hsqF Finset.univ α yv hns (by intro i _; fin_cases i; exacts [hβ1, hβ2]) m hsum
  have hM : ∑ i ∈ (Finset.univ : Finset (Fin 2)), m i = 2 * n := by
    rw [Fin.sum_univ_two]; simp [m]; ring
  rw [hM] at hA hB
  set na := EllAlgo.ellNa (EllAlgo.ptsQ pts n)
  set nb := EllAlgo.ellNb (EllAlgo.ptsQ pts n)
  have hna : na = n + 1 := by
    show EllAlgo.ellNa _ = _; rw [hQ]; simp [EllAlgo.ellNa]; omega
  have hnb : nb = n - 1 := by
    show EllAlgo.ellNb _ = _; rw [hQ]; simp [EllAlgo.ellNb]; omega
  have hAd : A = 0 ∨ A.natDegree < na := Or.inr (by omega)
  have hBd : B = 0 ∨ B.natDegree < nb := hB.imp_right (by omega)
  set cs : List F := (List.range na).map A.coeff ++ (List.range nb).map B.coeff with hcs
  have h1' : cs.take na = (List.range na).map A.coeff := by
    rw [hcs, List.take_left' (by simp)]
  have h2' : (cs.drop na).take nb = (List.range nb).map B.coeff := by
    rw [hcs, List.drop_left' (by simp), List.take_of_length_le (by simp)]
  have hl : cs.length = (EllAlgo.ellCols pC (EllAlgo.ptsQ pts n) na nb).length := by
    rw [EllAlgo.length_ellCols]; simp [hcs]
  have hrelc : CPoly.lcomb cs (EllAlgo.ellCols pC (EllAlgo.ptsQ pts n) na nb) = 0 := by
    rw [EllAlgo.lcomb_ellCols, h1', h2', EllAlgo.toPoly_range_coeff A na hAd,
      EllAlgo.toPoly_range_coeff B nb hBd, hQ]
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hloc 0 (Finset.mem_univ _) (by simp [m]; omega)
    · exact hloc 1 (Finset.mem_univ _) (by simp [m]; omega)
  have hne0 : CPoly.toPoly cs ≠ 0 := by
    rw [hcs, CPoly.toPoly_append, EllAlgo.toPoly_range_coeff A na hAd,
      EllAlgo.toPoly_range_coeff B nb hBd]
    simp only [List.length_map, List.length_range]
    intro h0
    have hBz : B = 0 := by
      by_contra hB0
      have e : A = -(X ^ na * B) := by linear_combination h0
      have hdeg := congrArg natDegree e
      rw [natDegree_neg, natDegree_mul (pow_ne_zero _ X_ne_zero) hB0, natDegree_X_pow] at hdeg
      rcases hAd with hA0 | hAd
      · rw [hA0] at e
        have : X ^ na * B = 0 := by linear_combination e
        exact hB0 ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ X_ne_zero))
      · omega
    rw [hBz, mul_zero, add_zero] at h0
    exact hAB.elim (fun h ↦ h h0) (fun h ↦ h hBz)
  obtain ⟨w, hw, hwne⟩ := EllAlgo.exists_good_basis _ cs hl hrelc hne0
  rw [EllAlgo.length_ellCols] at hwne
  have hsome : ((CPoly.nullBasis (EllAlgo.ellCols pC (EllAlgo.ptsQ pts n) na nb)).find?
      fun w ↦ !CPoly.isZero (w.take (na + nb))).isSome := by
    rw [List.find?_isSome]
    refine ⟨w, hw, ?_⟩
    have : CPoly.isZero (w.take (na + nb)) = false := by
      rcases h : CPoly.isZero (w.take (na + nb)) with _ | _
      · rfl
      · exact absurd ((CPoly.isZero_iff _).mp h) hwne
    simp [this]
  obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp hsome
  have hw'mem := List.mem_of_find?_eq_some hw'
  have hw'p := List.find?_some hw'
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hw'p
  have hw'ne : CPoly.toPoly (w'.take (na + nb)) ≠ 0 := by
    intro h0; rw [← CPoly.isZero_iff] at h0; rw [h0] at hw'p; exact Bool.noConfusion hw'p
  have hp3 : (toPoly pC).natDegree = 3 := by rw [hpC]; compute_degree!
  have hon : ∀ q ∈ pts, (toPoly pC).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0 := by
    intro q hq
    simp only [hpts, List.mem_cons, List.not_mem_nil, or_false] at hq
    have key : ∀ {u w : F}, (W F a b c).toAffine.Nonsingular u w → w ≠ 0 →
        (toPoly pC).eval u = w ^ 2 ∧ w ≠ 0 := by
      intro u w hns hw0
      have := (equation_W a b c).mp hns.1
      unfold OnCurve at this
      refine ⟨?_, hw0⟩
      rw [hpC]; simp; linear_combination -this
    rcases hq with rfl | rfl
    · exact key h1 hβ1
    · exact key h2 hβ2
  have hnd : (pts.map Prod.fst).Nodup := by simp [hpts, hne]
  have hcheck := EllAlgo.certCheck_ok_gen pC hp3 pts hon hnd 1 one_ne_zero n hn w'
    (CPoly.nullBasis_sound _ w' hw'mem) hw'ne []
  unfold certPart EllAlgo.ellSolve
  rw [hw']
  simp only
  rw [if_pos hcheck]
  simp

set_option maxHeartbeats 1600000 in
/-- **A certificate for a pair of points removes their logarithmic part.** -/
lemma certPart_spec (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (ι : F →+* Kc) (α1 β1 α2 β2 : F) (n : ℕ)
    (R : CPoly F) (h : certPart a b c [(α1, β1, 1), (α2, β2, 1)] n = some R) :
    ∃ w : E, HasElementaryIntegralIn w ∧
      (algebraMap Kc E (ι β1) / (x - algebraMap Kc E (ι α1)) +
        algebraMap Kc E (ι β2) / (x - algebraMap Kc E (ι α2))) / y = evF ι x R / y + w := by
  unfold certPart at h
  split at h
  swap
  · cases h
  rename_i AB hAB
  split_ifs at h with hchk
  simp only [Option.some.injEq] at h
  subst h
  set pts : List (F × F × ℤ) := [(α1, β1, 1), (α2, β2, 1)] with hpts
  set cc : F := 1 / ((n : F) * ((1 : ℕ) : F)) with hcc
  set G := EllAlgo.fracG [] 1 pts with hGdef
  unfold EllAlgo.certCheck at hchk
  simp only [Bool.and_eq_true, Bool.not_eq_true', EllAlgo.certN, EllAlgo.certM] at hchk
  obtain ⟨⟨hN, hG⟩, hbeq⟩ := hchk
  have hN' : toPoly AB.1 ^ 2 - toPoly AB.2 ^ 2 * toPoly (pF a b c) ≠ 0 := by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hN; apply hN
    simp only [toPoly_sub, toPoly_mul]; linear_combination h0
  have hG' : toPoly G.2 ≠ 0 := by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hG; exact hG h0
  have hid := (beq_iff _ _).mp hbeq
  have h2 : toPoly ([2] : CPoly F) = 2 := by
    rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
  simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_smul, toPoly_deriv, h2] at hid
  have hidK := congrArg (Polynomial.map ι) hid
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    map_C, Polynomial.map_ofNat, ← Polynomial.derivative_map] at hidK
  have hxa : ∀ z : F, x - algebraMap Kc E (ι z) ≠ 0 := fun z ↦ x_sub_const_ne hC x hx (ι z)
  have hpK : (toPoly (pF a b c)).map ι ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff ι.injective, toPoly_pF,
      Polynomial.map_ne_zero_iff (algebraMap ℚ F).injective, EllAlgo.toPoly_pOf]
    exact hsq.ne_zero
  have hyK : y ^ 2 = aeval x ((toPoly (pF a b c)).map ι) := by
    rw [hy]; exact (evF_pF ι x a b c).symm
  have hGK : (toPoly G.2).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hG'
  have hNK : ((toPoly AB.1).map ι) ^ 2 - ((toPoly AB.2).map ι) ^ 2 * (toPoly (pF a b c)).map ι ≠ 0 := by
    rw [← Polynomial.map_pow, ← Polynomial.map_pow, ← Polynomial.map_mul, ← Polynomial.map_sub]
    exact (Polynomial.map_ne_zero_iff ι.injective).mpr hN'
  obtain ⟨w, hw, key⟩ := ell_log_decompK hC x y hx _ hpK hyK ((toPoly G.1).map ι) ((toPoly G.2).map ι)
    ((toPoly AB.1).map ι) ((toPoly AB.2).map ι)
    ((toPoly (EllAlgo.certR (pF a b c) AB G cc)).map ι) (ι cc) hGK hNK (by linear_combination hidK)
  refine ⟨w, hw, ?_⟩
  obtain ⟨-, hfr⟩ := fracG_evF ι x hxa [] 1 pts
  simp only [hpts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.cast_one,
    Nat.cast_one, div_one, one_mul, add_zero] at hfr
  rw [← hGdef] at hfr
  have he : evF ι x ([] : CPoly F) = 0 := by simp [evF, CPoly.toPoly]
  rw [he, zero_add] at hfr
  rw [← hfr, div_div]
  exact key

omit [Fact (¬IsSquare (d : ℚ))] in
lemma toPoly_divMod_fst (A D : CPoly ℚ) (hmon : (toPoly D).Monic) :
    toPoly (divMod A D).1 = toPoly A /ₘ toPoly D :=
  ((Polynomial.div_modByMonic_unique _ _ hmon ⟨by rw [divMod_spec A D]; ring,
    divMod_degree_lt A D hmon.ne_zero⟩).1).symm

lemma hasElementaryIntegralIn_zero' : HasElementaryIntegralIn (0 : E) :=
  (hasElementaryIntegralIn_logDeriv₂ (0 : E) 0 1 1 (by simp) (by simp) one_ne_zero
    one_ne_zero).congr (by simp)

set_option maxHeartbeats 3200000 in
/-- **Correctness of the certificate branch.** -/
lemma quadCert_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : F →+* Kc) (A D : CPoly ℚ) (hmon : (toPoly D).Monic) (α σα β σβ r : F) (N : ℕ)
    (ans : Bool) (h : quadCert a b c A D α σα β σβ r N = some ans) :
    ans = true ↔ HasElementaryIntegral ((aeval x (toPoly A /ₘ toPoly D) +
      algebraMap Kc E (ι (r * β)) / (x - algebraMap Kc E (ι α)) +
      algebraMap Kc E (ι (star r * σβ)) / (x - algebraMap Kc E (ι σα))) / y) := by
  unfold quadCert at h
  dsimp only at h
  split at h
  swap
  · cases h
  rename_i R1 R2 h1 h2
  simp only [Option.some.injEq] at h
  subst h
  set ιE : F → E := fun z ↦ algebraMap Kc E (ι z) with hιE
  have hconst : ∀ z : F, (ιE z)′ = 0 := fun z ↦ by rw [hιE]; simp only; rw [deriv_algebraMap, hC, map_zero]
  set U := ιE ((r.re : ℚ) : F)
  set V := ιE ⟨0, r.im⟩
  set T1 := (ιE β / (x - ιE α) + ιE σβ / (x - ιE σα)) / y
  set T2 := (ιE β / (x - ιE α) + ιE (-σβ) / (x - ιE σα)) / y
  have p1 : ∃ w, HasElementaryIntegralIn w ∧ U * T1 = U * (evF ι x R1 / y) + w := by
    by_cases hu : r.re = 0
    · rw [if_pos hu] at h1
      simp only [Option.some.injEq] at h1
      subst h1
      refine ⟨0, hasElementaryIntegralIn_zero', ?_⟩
      simp [U, hu, hιE]
    · rw [if_neg hu] at h1
      obtain ⟨w, hw, key⟩ := certPart_spec hC x y hx a b c hsq hy ι α β σα σβ _ R1 h1
      exact ⟨U * w, hw.const_mul U (hconst _), by simp only [T1, hιE] at key ⊢; rw [key]; ring⟩
  have p2 : ∃ w, HasElementaryIntegralIn w ∧ V * T2 = V * (evF ι x R2 / y) + w := by
    by_cases hv : r.im = 0
    · rw [if_pos hv] at h2
      simp only [Option.some.injEq] at h2
      subst h2
      refine ⟨0, hasElementaryIntegralIn_zero', ?_⟩
      have : (⟨0, r.im⟩ : F) = 0 := by ext <;> simp [hv]
      simp [V, this, hιE]
    · rw [if_neg hv] at h2
      obtain ⟨w, hw, key⟩ := certPart_spec hC x y hx a b c hsq hy ι α β σα (-σβ) _ R2 h2
      exact ⟨V * w, hw.const_mul V (hconst _), by simp only [T2, hιE] at key ⊢; rw [key]; ring⟩
  obtain ⟨w1, hw1, e1⟩ := p1
  obtain ⟨w2, hw2, e2⟩ := p2
  have hr : r = ((r.re : ℚ) : F) + ⟨0, r.im⟩ := by ext <;> simp
  have hsr : star r = ((r.re : ℚ) : F) - ⟨0, r.im⟩ := by ext <;> simp
  have hy0 : y ≠ 0 := by
    rintro rfl
    have hpx := evF_pF ι x a b c
    have hne : evF ι x (pF a b c) ≠ 0 := by
      have htrK : Transcendental Kc x :=
        transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
      refine aeval_ne_zero_of_tr x htrK ?_
      rw [Polynomial.map_ne_zero_iff ι.injective, toPoly_pF,
        Polynomial.map_ne_zero_iff (algebraMap ℚ F).injective, EllAlgo.toPoly_pOf]
      exact hsq.ne_zero
    apply hne; rw [hpx, ← hy]; ring
  have hxa := fun z : F ↦ x_sub_const_ne hC x hx (ι z)
  have hsplit : (aeval x (toPoly A /ₘ toPoly D) +
      algebraMap Kc E (ι (r * β)) / (x - algebraMap Kc E (ι α)) +
      algebraMap Kc E (ι (star r * σβ)) / (x - algebraMap Kc E (ι σα))) / y =
      evF ι x (add (liftF (divMod A D).1) (add (smul ((r.re : ℚ) : F) R1) (smul ⟨0, r.im⟩ R2))) / y
        + (w1 + w2) := by
    rw [evF_add, evF_add, evF_smul, evF_smul, evF_liftF, toPoly_divMod_fst A D hmon]
    have e1' := e1
    have e2' := e2
    simp only [T1, T2, U, V, hιE] at e1' e2'
    rw [show r * β = ((r.re : ℚ) : F) * β + ⟨0, r.im⟩ * β by rw [← add_mul, ← hr],
      show star r * σβ = ((r.re : ℚ) : F) * σβ - ⟨0, r.im⟩ * σβ by rw [← sub_mul, ← hsr]]
    simp only [map_add, map_sub, map_mul, map_neg] at e1' e2' ⊢
    linear_combination e1' + e2'
  rw [hsplit]
  have hpm : toPoly (pF (d := d) a b c) = (toPoly (EllAlgo.pOf a b c)).map (algebraMap ℚ F) :=
    toPoly_pF a b c
  have hdeg3 : (toPoly (EllAlgo.pOf a b c)).natDegree = 3 := by
    rw [EllAlgo.toPoly_pOf]; compute_degree!
  have hdec := hyp_decidesF hC hCall ι x y hx (EllAlgo.pOf a b c)
    (by rw [EllAlgo.toPoly_pOf]; exact hsq) (by rw [hdeg3]; decide)
    (by rw [EllAlgo.toPoly_pOf, hy]; simp) hgen (pF a b c) hpm
    (add (liftF (divMod A D).1) (add (smul ((r.re : ℚ) : F) R1) (smul ⟨0, r.im⟩ R2)))
  rw [← hdec]
  have hw := hw1.add hw2
  constructor
  · intro h0; exact h0.add_in hw
  · intro h0
    have := h0.sub_in hw
    rwa [add_sub_cancel_right] at this

/-- A conjugate pair of residues whose `Λ`-parts agree and whose points sum to a non-torsion
point gives a non-elementary integral. -/
lemma pair_not_elem (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : F →+* Kc) (B : ℚ[X]) {α σα β β1 r r1 : F} (hne : α ≠ σα)
    (hPe : β * β = α ^ 3 + (a : F) * α ^ 2 + (b : F) * α + (c : F)) (hβ : β ≠ 0)
    (hP1e : β1 * β1 = σα ^ 3 + (a : F) * σα ^ 2 + (b : F) * σα + (c : F)) (hβ1 : β1 ≠ 0)
    (Λ : F →ₗ[ℚ] ℚ) (u : ℚ) (hu : u ≠ 0) (hΛ0 : Λ r = u) (hΛ1 : Λ r1 = u)
    (hnt : ¬IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some α β (ns_of_eq a b c hPe hβ) +
      WeierstrassCurve.Affine.Point.some σα β1 (ns_of_eq a b c hP1e hβ1) : (W F a b c).toAffine.Point)) :
    ¬HasElementaryIntegral ((aeval x B + algebraMap Kc E (ι (r * β)) / (x - algebraMap Kc E (ι α)) +
      algebraMap Kc E (ι (r1 * β1)) / (x - algebraMap Kc E (ι σα))) / y) := by
  classical
  have hPf : ∀ i, (W F a b c).toAffine.Nonsingular (![α, σα] i) (![β, β1] i) := by
    intro i; fin_cases i
    exacts [ns_of_eq a b c hPe hβ, ns_of_eq a b c hP1e hβ1]
  have hβf : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ![β, β1] i ≠ 0 := by
    intro i _; fin_cases i; exacts [hβ, hβ1]
  have hinj : Set.InjOn ![α, σα] ↑(Finset.univ : Finset (Fin 2)) := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hΛf : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      Λ (![r, r1] i) = ((![u.num, u.num] i : ℤ) : ℚ) / (u.den : ℚ) := by
    intro i _; fin_cases i <;> simp [hΛ0, hΛ1, Rat.num_div_den]
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 2)), ![u.num, u.num] i •
      (WeierstrassCurve.Affine.Point.some _ _ (hPf i) : (W F a b c).toAffine.Point) =
      u.num • (WeierstrassCurve.Affine.Point.some α β (ns_of_eq a b c hPe hβ) +
        WeierstrassCurve.Affine.Point.some σα β1 (ns_of_eq a b c hP1e hβ1)) := by
    rw [Fin.sum_univ_two, smul_add]; rfl
  have hntf : ¬IsOfFinAddOrder (∑ i ∈ (Finset.univ : Finset (Fin 2)), ![u.num, u.num] i •
      (WeierstrassCurve.Affine.Point.some _ _ (hPf i) : (W F a b c).toAffine.Point)) := by
    rw [hsum]
    intro ht
    apply hnt
    obtain ⟨n, hn, hn'⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.mp ht
    exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr
      ⟨n * u.num, mul_ne_zero hn (Rat.num_ne_zero.mpr hu), by rw [mul_smul]; exact hn'⟩
  have key := not_elem_of_nontorsion hC hCall x y hx a b c hsq hy hgen ι B Finset.univ
    ![α, σα] ![β, β1] ![r, r1] hPf hβf hinj Λ ![u.num, u.num] u.den u.den_nz hΛf hntf
  intro h
  apply key
  convert h using 2
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

set_option maxHeartbeats 3200000 in
/-- **Correctness of the quadratic-orbit procedure.** -/
theorem quadOrbitDecide_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (s2 : Kc) (hs2 : s2 ^ 2 = d) (A D : CPoly ℚ) (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp02 : p0 ≠ 2) (hgood : goodRedMod p0 a b c) (s : ZMod p0) (hs : s ^ 2 = d)
    (hs' : 2 * s ≠ 0) (ans : Bool) (h : quadOrbitDecide (d := d) a b c A D p0 = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  classical
  let ι : F →+* Kc := (QuadraticAlgebra.lift ⟨s2, by rw [← sq, hs2]; simp⟩ : F →ₐ[ℚ] Kc).toRingHom
  let ιE : F →+* E := (algebraMap Kc E).comp ι
  obtain ⟨φ⟩ := exists_embed (d := d) s hs hs'
  unfold quadOrbitDecide at h
  split at h
  · cases h
  rename_i α σα β σβ r hdata
  obtain ⟨hσα, hσβ, hne, hβ, hβeq, hder, hr, hfac⟩ := orbitData_spec hdata
  have hxa : ∀ z : F, x - ιE z ≠ 0 := fun z ↦ x_sub_const_ne hC x hx (ι z)
  have hsplit := integrand_split ιE x y A D hσα hσβ hne hβ hder hr hfac hxa
  -- the points
  have hσeq : σβ * σβ = σα ^ 3 + (a : F) * σα ^ 2 + (b : F) * σα + (c : F) := by
    rw [hσβ, hσα, ← star_mul', hβeq]; simp [star_pow]
  have hσβ0 : σβ ≠ 0 := by rw [hσβ]; exact star_ne_zero.mpr hβ
  have hP := ns_of_eq (K := F) a b c hβeq hβ
  have hσP := ns_of_eq (K := F) a b c hσeq hσβ0
  have hN : Fintype.card (Option (RedPts p0 a b c)) ≤ redCount p0 a b c + 1 := by
    rw [Fintype.card_option, card_RedPts]
  dsimp only at h
  rw [← hσβ] at hsplit
  split_ifs at h with htA htB
  · simp only [Option.some.injEq] at h; subst h
    obtain ⟨hre, ht⟩ := htA
    have hrep := addPtF_spec a b c (o₁ := some (α, β)) (o₂ := some (σα, σβ))
      (P₁ := WeierstrassCurve.Affine.Point.some α β hP) (P₂ := WeierstrassCurve.Affine.Point.some σα σβ hσP) ⟨hP, rfl⟩ ⟨hσP, rfl⟩
    have hnt : ¬IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some α β hP + WeierstrassCurve.Affine.Point.some σα σβ hσP) := fun h' ↦ by
      rw [(torsionTestF_spec a b c φ hp02 hgood hrep _ hN).mpr h'] at ht
      exact Bool.noConfusion ht
    rw [hsplit]
    refine ⟨fun h0 ↦ Bool.noConfusion h0, fun he ↦ absurd he ?_⟩
    exact pair_not_elem hC hCall x y hx a b c hsq hy hgen ι (toPoly A /ₘ toPoly D) hne hβeq hβ
      hσeq hσβ0 (QuadraticAlgebra.reₗ (d : ℚ) 0) r.re hre (by simp) (by simp) hnt
  · simp only [Option.some.injEq] at h; subst h
    obtain ⟨him, ht⟩ := htB
    have hσeq' : -σβ * -σβ = σα ^ 3 + (a : F) * σα ^ 2 + (b : F) * σα + (c : F) := by
      rw [neg_mul_neg]; exact hσeq
    have hσβ0' : -σβ ≠ 0 := neg_ne_zero.mpr hσβ0
    have hσP' := ns_of_eq (K := F) a b c hσeq' hσβ0'
    have hrep := addPtF_spec a b c (o₁ := some (α, β)) (o₂ := some (σα, -σβ))
      (P₁ := WeierstrassCurve.Affine.Point.some α β hP) (P₂ := WeierstrassCurve.Affine.Point.some σα (-σβ) hσP') ⟨hP, rfl⟩ ⟨hσP', rfl⟩
    have hnt : ¬IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some α β hP + WeierstrassCurve.Affine.Point.some σα (-σβ) hσP') := fun h' ↦ by
      rw [(torsionTestF_spec a b c φ hp02 hgood hrep _ hN).mpr h'] at ht
      exact Bool.noConfusion ht
    rw [hsplit, show star r * σβ = -star r * -σβ by ring]
    refine ⟨fun h0 ↦ Bool.noConfusion h0, fun he ↦ absurd he ?_⟩
    exact pair_not_elem hC hCall x y hx a b c hsq hy hgen ι (toPoly A /ₘ toPoly D) hne hβeq hβ
      hσeq' hσβ0' (QuadraticAlgebra.imₗ (d : ℚ) 0) r.im him (by simp) (by simp) hnt
  · rw [hsplit]
    exact quadCert_spec hC hCall x y hx a b c hsq hy hgen ι A D (monic_of_fac hfac) α σα β σβ r _
      ans h

/-! ### Completeness -/

lemma qsqrt_sq_eq (q : ℚ) : ∃ k : ℚ, EllAlgo.qsqrt (q ^ 2) = some k ∧ k ^ 2 = q ^ 2 := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (EllAlgo.qsqrt_sq q)
  exact ⟨k, hk, EllAlgo.qsqrt_spec hk⟩

/-- **`sqrtF` finds a square root of every square of `F`.** -/
lemma sqrtF_complete (z : F) : sqrtF (d := d) (z * z) ≠ none := by
  have hR : (z * z).re = z.re ^ 2 + d * z.im ^ 2 := by simp; ring
  have hI : (z * z).im = 2 * z.re * z.im := by simp; ring
  obtain ⟨n, hn, hn2⟩ := qsqrt_sq_eq (z.re ^ 2 - d * z.im ^ 2)
  have hdisc : (z * z).re ^ 2 - d * (z * z).im ^ 2 = (z.re ^ 2 - d * z.im ^ 2) ^ 2 := by
    rw [hR, hI]; ring
  unfold sqrtF
  simp only
  rw [hdisc, hn]
  simp only
  rw [ne_eq, List.find?_eq_none]
  push_neg
  have ht : z.re ^ 2 ∈ [((z * z).re + n) / 2, ((z * z).re - n) / 2] := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hn2 with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      left; rw [hR, h]; ring
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      right; rw [hR, h]; ring
  obtain ⟨u', hu', hu'2⟩ := qsqrt_sq_eq z.re
  by_cases hu0 : u' = 0
  · have hu : z.re = 0 := by
      rw [hu0] at hu'2; exact pow_eq_zero_iff two_ne_zero |>.mp hu'2.symm
    have hd := d_ne_zero (d := d)
    obtain ⟨v', hv', hv'2⟩ := qsqrt_sq_eq z.im
    have hRd : (z * z).re / d = z.im ^ 2 := by rw [hR, hu]; field_simp; ring
    refine ⟨⟨0, v'⟩, List.mem_filterMap.mpr ⟨z.re ^ 2, ht, ?_⟩, ?_⟩
    · rw [hu']; dsimp only; rw [if_pos hu0, hRd, hv']
    · simp only [decide_eq_true_eq]
      ext
      · simp only [QuadraticAlgebra.re_mul, hu]; linear_combination (d : ℚ) * hv'2
      · simp only [QuadraticAlgebra.im_mul, hu]; ring
  · have hu : z.re ≠ 0 := by
      intro h0; rw [h0] at hu'2; exact hu0 (pow_eq_zero_iff two_ne_zero |>.mp (by rw [hu'2]; ring))
    refine ⟨⟨u', (z * z).im / (2 * u')⟩, List.mem_filterMap.mpr ⟨z.re ^ 2, ht, ?_⟩, ?_⟩
    · rw [hu']; dsimp only; rw [if_neg hu0]
    · simp only [decide_eq_true_eq]
      rw [hI]
      ext
      · simp only [QuadraticAlgebra.re_mul]
        have hq : 2 * z.re * z.im / (2 * u') * (2 * z.re * z.im / (2 * u')) = z.im ^ 2 := by
          rw [div_mul_div_comm, div_eq_iff (mul_ne_zero (mul_ne_zero two_ne_zero hu0)
            (mul_ne_zero two_ne_zero hu0))]
          linear_combination (-4 * z.im ^ 2) * hu'2
        linear_combination hu'2 + (d : ℚ) * hq
      · simp only [QuadraticAlgebra.im_mul]
        field_simp
        ring

omit [Fact (¬IsSquare (d : ℚ))] in
lemma sqrtF_sound {w β0 : F} (h : sqrtF (d := d) w = some β0) : β0 * β0 = w := by
  unfold sqrtF at h
  simp only at h
  split at h
  · have := List.find?_some h
    simpa using this
  · cases h

set_option maxHeartbeats 1600000 in
/-- **`orbitData` answers on its class**: `D` monic quadratic with a root `α ∈ F \ ℚ` over which
`p` takes a non-zero square value. -/
lemma orbitData_ne_none (a b c : ℤ) (A D : CPoly ℚ) (hlen : D.length = 3) (hlead : D.getD 2 0 = 1)
    (α : F) (him : α.im ≠ 0) (hroot : evalQF D α = 0) (β : F) (hβ : β ≠ 0)
    (hβeq : β * β = α ^ 3 + (a : F) * α ^ 2 + (b : F) * α + (c : F)) :
    orbitData (d := d) a b c A D ≠ none := by
  obtain ⟨g, e, t, rfl⟩ : ∃ g e t, D = [g, e, t] := by
    match D, hlen with
    | [g, e, t], _ => exact ⟨g, e, t, rfl⟩
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hlead
  subst hlead
  have hd := d_ne_zero (d := d)
  -- the root equations
  have hroot' : α * α + (e : F) * α + (g : F) = 0 := by
    simp only [evalQF, List.foldr_cons, List.foldr_nil, mul_zero, add_zero] at hroot
    rw [← hroot]; push_cast; ring
  have hre := congrArg QuadraticAlgebra.re hroot'
  have hi := congrArg QuadraticAlgebra.im hroot'
  simp at hre hi
  have hαre : α.re = -e / 2 := by
    have : α.im * (2 * α.re + e) = 0 := by linear_combination hi
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h him
    · linarith
  have hdisc : (e ^ 2 - 4 * g) / d = (2 * α.im) ^ 2 := by
    rw [div_eq_iff (by exact_mod_cast hd)]
    rw [hαre] at hre
    linear_combination (-4) * hre
  obtain ⟨k, hk, hk2⟩ := qsqrt_sq_eq (2 * α.im)
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0] at hk2
    exact him (by nlinarith [sq_nonneg α.im])
  unfold orbitData
  simp only [List.length_cons, List.length_nil, List.getD_cons_succ, List.getD_cons_zero,
    zero_add, Nat.reduceAdd, and_self, if_true]
  rw [hdisc, hk]
  simp only [if_neg hk0]
  -- the root chosen by the procedure is `α` or `star α`
  set α' : F := ⟨-e / 2, k / 2⟩ with hα'
  have hchoice : α' = α ∨ α' = star α := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hk2 with h | h
    · left; ext <;> simp [hα', hαre, h]
    · right; ext <;> simp [hα', hαre, h] <;> ring
  obtain ⟨β', hβ'0, hβ'eq⟩ : ∃ β' : F, β' ≠ 0 ∧
      β' * β' = α' ^ 3 + (a : F) * α' ^ 2 + (b : F) * α' + (c : F) := by
    rcases hchoice with h | h
    · exact ⟨β, hβ, by rw [h]; exact hβeq⟩
    · refine ⟨star β, star_ne_zero.mpr hβ, ?_⟩
      rw [h, ← star_mul', hβeq]; simp [star_pow]
  rw [← hβ'eq]
  obtain ⟨β0, hβ0⟩ := Option.ne_none_iff_exists'.mp (sqrtF_complete (d := d) β')
  rw [hβ0]
  have hβ0eq := sqrtF_sound hβ0
  have hβ00 : β0 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hβ0eq; exact hβ'0 (mul_self_eq_zero.mp hβ0eq.symm)
  have hder : evalQF (CPoly.deriv [g, e, 1]) α' ≠ 0 := by
    rw [evalQF_eq, toPoly_deriv]
    have : toPoly ([g, e, 1] : CPoly ℚ) = C g + C e * X + X ^ 2 := by
      simp [CPoly.toPoly]; ring
    rw [this]
    simp only [derivative_add, derivative_C, derivative_mul, derivative_X, derivative_X_pow,
      zero_add, zero_mul, mul_one, map_add, map_mul, aeval_C, aeval_X, map_pow, Nat.cast_ofNat]
    intro h0
    have := congrArg QuadraticAlgebra.im h0
    simp [hα', Algebra.algebraMap_eq_smul_one, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat] at this
    exact hk0 this
  simp [hβ00, hβ0eq, hder]

lemma ordF_spec (a b c : ℤ) {o : Option (F × F)} {P : (W F a b c).toAffine.Point}
    (hrep : RepF a b c o P) (N : ℕ) (ht : torsionTestF a b c o N = true) :
    1 ≤ ordF a b c o N ∧ ordF a b c o N • P = 0 := by
  simp only [torsionTestF, List.any_eq_true, List.mem_range] at ht
  obtain ⟨k, hk, hk'⟩ := ht
  have hsome : ((List.range N).find? fun k ↦ (mulPtF a b c o (k + 1)).isNone).isSome := by
    rw [List.find?_isSome]; exact ⟨k, List.mem_range.mpr hk, hk'⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsome
  have hj' := List.find?_some hj
  simp only [ordF, hj, Option.map_some, Option.getD_some]
  refine ⟨by omega, ?_⟩
  have hr := mulPtF_spec a b c hrep (j + 1)
  rcases hm : mulPtF a b c o (j + 1) with _ | ⟨u, w⟩
  · rw [hm] at hr; exact hr
  · rw [hm] at hj'; simp at hj'

/-- **Completeness**: once the orbit data is found, the procedure always answers. -/
theorem quadOrbitDecide_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (p0 : ℕ) [NeZero p0] (hdata : orbitData (d := d) a b c A D ≠ none) :
    quadOrbitDecide (d := d) a b c A D p0 ≠ none := by
  obtain ⟨⟨α, σα, β, σβ, r⟩, hd⟩ := Option.ne_none_iff_exists'.mp hdata
  obtain ⟨hσα, hσβ, hne, hβ, hβeq, hder, hr, hfac⟩ := orbitData_spec hd
  have hσeq : σβ * σβ = σα ^ 3 + (a : F) * σα ^ 2 + (b : F) * σα + (c : F) := by
    rw [hσβ, hσα, ← star_mul', hβeq]; simp [star_pow]
  have hσβ0 : σβ ≠ 0 := by rw [hσβ]; exact star_ne_zero.mpr hβ
  have hP := ns_of_eq (K := F) a b c hβeq hβ
  have hσP := ns_of_eq (K := F) a b c hσeq hσβ0
  have hσeq' : -σβ * -σβ = σα ^ 3 + (a : F) * σα ^ 2 + (b : F) * σα + (c : F) := by
    rw [neg_mul_neg]; exact hσeq
  have hσβ0' : -σβ ≠ 0 := neg_ne_zero.mpr hσβ0
  have hσP' := ns_of_eq (K := F) a b c hσeq' hσβ0'
  unfold quadOrbitDecide
  rw [hd]
  dsimp only
  split_ifs with htA htB
  · simp
  · simp
  unfold quadCert
  dsimp only
  set N := redCount p0 a b c + 1
  have e1 : (if r.re = 0 then some [] else certPart a b c [(α, β, 1), (σα, σβ, 1)]
      (ordF a b c (addPtF a b c (some (α, β)) (some (σα, σβ))) N)) ≠ none := by
    by_cases hu : r.re = 0
    · rw [if_pos hu]; simp
    · rw [if_neg hu]
      have ht : torsionTestF a b c (addPtF a b c (some (α, β)) (some (σα, σβ))) N = true := by
        by_contra h0; exact htA ⟨hu, by simpa using h0⟩
      have hrep := addPtF_spec a b c (o₁ := some (α, β)) (o₂ := some (σα, σβ))
        (P₁ := WeierstrassCurve.Affine.Point.some α β hP)
        (P₂ := WeierstrassCurve.Affine.Point.some σα σβ hσP) ⟨hP, rfl⟩ ⟨hσP, rfl⟩
      obtain ⟨hn1, hn⟩ := ordF_spec a b c hrep N ht
      exact certPart_ne_none hsq hne hβ hσβ0 hP hσP _ hn1 hn
  have e2 : (if r.im = 0 then some [] else certPart a b c [(α, β, 1), (σα, -σβ, 1)]
      (ordF a b c (addPtF a b c (some (α, β)) (some (σα, -σβ))) N)) ≠ none := by
    by_cases hv : r.im = 0
    · rw [if_pos hv]; simp
    · rw [if_neg hv]
      have ht : torsionTestF a b c (addPtF a b c (some (α, β)) (some (σα, -σβ))) N = true := by
        by_contra h0; exact htB ⟨hv, by simpa using h0⟩
      have hrep := addPtF_spec a b c (o₁ := some (α, β)) (o₂ := some (σα, -σβ))
        (P₁ := WeierstrassCurve.Affine.Point.some α β hP)
        (P₂ := WeierstrassCurve.Affine.Point.some σα (-σβ) hσP') ⟨hP, rfl⟩ ⟨hσP', rfl⟩
      obtain ⟨hn1, hn⟩ := ordF_spec a b c hrep N ht
      exact certPart_ne_none hsq hne hβ hσβ0' hP hσP' _ hn1 hn
  obtain ⟨R1, h1⟩ := Option.ne_none_iff_exists'.mp e1
  obtain ⟨R2, h2⟩ := Option.ne_none_iff_exists'.mp e2
  rw [h1, h2]
  simp

/-- **The quadratic-orbit procedure decides** its class: `D` a monic quadratic with a root
`α ∈ ℚ(√d) \ ℚ` over which `p = x³ + ax² + bx + c` takes a non-zero square value `β²`. It returns
an answer, and the answer is correct. -/
theorem quadOrbitDecide_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (s2 : Kc) (hs2 : s2 ^ 2 = d) (A D : CPoly ℚ) (hlen : D.length = 3) (hlead : D.getD 2 0 = 1)
    (α : F) (him : α.im ≠ 0) (hroot : evalQF D α = 0) (β : F) (hβ : β ≠ 0)
    (hβeq : β * β = α ^ 3 + (a : F) * α ^ 2 + (b : F) * α + (c : F))
    (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp02 : p0 ≠ 2) (hgood : goodRedMod p0 a b c) (s : ZMod p0) (hs : s ^ 2 = d)
    (hs' : 2 * s ≠ 0) :
    ∃ ans, quadOrbitDecide (d := d) a b c A D p0 = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨ans, h⟩ := Option.ne_none_iff_exists'.mp (quadOrbitDecide_ne_none a b c hsq A D p0
    (orbitData_ne_none a b c A D hlen hlead α him hroot β hβ hβeq))
  exact ⟨ans, h, quadOrbitDecide_spec hC hCall x y hx a b c hsq hy hgen s2 hs2 A D p0 hp02 hgood
    s hs hs' ans h⟩

end EllQuad
