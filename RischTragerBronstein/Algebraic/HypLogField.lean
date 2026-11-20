import RischTragerBronstein.Algebraic.HypLogSearch

/-!
# Logarithmic certificates with coefficients in a number field

For `y² = p(x)` and a computable field `F` embedded in the constants (`ι : F →+* Kc`), e.g.
`F = ℚ(√d)`: a certificate `A/(Dy) = (W/V · y)′ + ∑ κₖ uₖ′/uₖ` with `uₖ = (aₖ + bₖ y)/dₖ`,
`aₖ, bₖ, dₖ, W, V ∈ F[x]`, `κₖ ∈ F`, reduces to polynomial identities over `F`
(`logCheckF`, sound by `logCheckF_sound`). The untrusted search `logCertF` is the Riemann–Roch
search of `HypLogSearch` over `F` (points with coordinates in `F`, integer multiplicities).
This handles irrational residues: residues `u + v√d` split into two logarithms with rational
multiplicities, `(1/N) log u_A + (√d/N) log u_B`.
-/

open Polynomial Differential

namespace CPoly

section Defs

variable {F : Type*} [Field F] [DecidableEq F]

/-- The inverse of `u` modulo `f`. -/
def modInvF (u f : CPoly F) : CPoly F :=
  let e := egcd u f
  (divMod (smul (lead (trim e.1))⁻¹ e.2.1) f).2

/-- `P ^ n`. -/
def powF (P : CPoly F) : ℕ → CPoly F
  | 0 => [1]
  | n + 1 => mul P (powF P n)

/-- The Lagrange basis polynomial. -/
def basisLF (pts : List F) (i : ℕ) : CPoly F :=
  ((List.range pts.length).filter (· ≠ i)).foldr (fun j acc ↦
    mul (smul (1 / (pts.getD i 0 - pts.getD j 0)) [-(pts.getD j 0), 1]) acc) [1]

/-- The Lagrange interpolant. -/
def lagrF (pts vals : List F) : CPoly F :=
  (List.range pts.length).foldr (fun i acc ↦ add (smul (vals.getD i 0) (basisLF pts i)) acc) []

/-- Newton's iteration for `V² ≡ p (mod U)`. -/
def sqrtNewtonF (p U : CPoly F) : ℕ → CPoly F → CPoly F
  | 0, V => V
  | k + 1, V =>
    sqrtNewtonF p U k (divMod (sub V (mul (sub (mul V V) p) (modInvF (smul 2 V) U))) U).2

/-- The coefficient vector of `q mod U`. -/
def coeffVecF (U q : CPoly F) (N : ℕ) : CPoly F :=
  (List.range N).map fun i ↦ ((divMod q U).2).getD i 0

/-- **The untrusted search**: `u = (a + b y)/d` with divisor `∑ nᵢ ([Pᵢ] − [P̄ᵢ])`, points
`Pᵢ = (αᵢ, βᵢ)` over `F`. -/
def logCertF (p : CPoly F) (pts : List (F × F × ℤ)) : Option (CPoly F × CPoly F × CPoly F) :=
  let U := pts.foldr (fun m acc ↦ mul (powF [-m.1, 1] (2 * m.2.2.natAbs)) acc) [1]
  let d := pts.foldr (fun m acc ↦ mul (powF [-m.1, 1] m.2.2.natAbs) acc) [1]
  let N := (trim U).length - 1
  let V0 := lagrF (pts.map (·.1)) (pts.map fun m ↦ if 0 < m.2.2 then m.2.1 else -m.2.1)
  let V := sqrtNewtonF p U (Nat.log 2 N + 2) V0
  let degp := (trim p).length - 1
  let da := N / 2
  let nb := if degp ≤ N then (N - degp) / 2 + 1 else 0
  let cols := (List.range (da + 1)).map (fun j ↦ coeffVecF U (monomial j 1) N) ++
    (List.range nb).map (fun k ↦ coeffVecF U (mul (monomial k 1) V) N)
  match (nullBasis cols).find? (fun v ↦ !isZero (v.drop (da + 1))) with
  | some v => some (v.take (da + 1), v.drop (da + 1), d)
  | none => none

/-- `N = a² − b² p`, `M = 2p(ab′ − a′b) + abp′`. -/
def logN (p a b : CPoly F) : CPoly F := sub (mul a a) (mul (mul b b) p)
def logM (p a b : CPoly F) : CPoly F :=
  add (mul (smul 2 p) (sub (mul a (deriv b)) (mul (deriv a) b))) (mul (mul a b) (deriv p))

/-- The product of the norms. -/
def prodN (p : CPoly F) (logs : List (F × CPoly F × CPoly F × CPoly F)) : CPoly F :=
  logs.foldr (fun l acc ↦ mul (logN p l.2.1 l.2.2.1) acc) [1]

/-- `∑ₖ κₖ Mₖ ∏_{l ≠ k} N_l`. -/
def sumMN (p : CPoly F) : List (F × CPoly F × CPoly F × CPoly F) → CPoly F
  | [] => []
  | l :: ls => add (mul (smul l.1 (logM p l.2.1 l.2.2.1)) (prodN p ls))
      (mul (logN p l.2.1 l.2.2.1) (sumMN p ls))

/-- **The certificate check.** -/
def logCheckF (p A D W V : CPoly F) (logs : List (F × CPoly F × CPoly F × CPoly F)) : Bool :=
  !isZero p && !isZero D && !isZero V &&
  logs.all (fun l ↦ !isZero (logN p l.2.1 l.2.2.1) && !isZero l.2.2.2 &&
    beq (mul (deriv (logN p l.2.1 l.2.2.1)) l.2.2.2)
      (mul (smul 2 (logN p l.2.1 l.2.2.1)) (deriv l.2.2.2))) &&
  beq (mul (smul 2 (mul A (mul V V))) (prodN p logs))
    (mul D (add (mul (add (mul (smul 2 (sub (mul (deriv W) V) (mul W (deriv V)))) p)
      (mul (mul W V) (deriv p))) (prodN p logs)) (mul (mul V V) (sumMN p logs))))

/-- **The certificate check with a remainder** `A/(Dy) = (W/V·y)′ + ∑ κₖ uₖ′/uₖ + B₀/y`. -/
def logCheckFB (p A D W V B0 : CPoly F) (logs : List (F × CPoly F × CPoly F × CPoly F)) : Bool :=
  !isZero p && !isZero D && !isZero V &&
  logs.all (fun l ↦ !isZero (logN p l.2.1 l.2.2.1) && !isZero l.2.2.2 &&
    beq (mul (deriv (logN p l.2.1 l.2.2.1)) l.2.2.2)
      (mul (smul 2 (logN p l.2.1 l.2.2.1)) (deriv l.2.2.2))) &&
  beq (mul (smul 2 (mul A (mul V V))) (prodN p logs))
    (mul D (add (add (mul (add (mul (smul 2 (sub (mul (deriv W) V) (mul W (deriv V)))) p)
      (mul (mul W V) (deriv p))) (prodN p logs)) (mul (mul V V) (sumMN p logs)))
      (mul (smul 2 (mul B0 (mul V V))) (prodN p logs))))

end Defs

section Sound

variable {F : Type*} [Field F] [DecidableEq F]
variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- The value of an `F`-polynomial at `x`. -/
noncomputable def evF (ι : F →+* Kc) (x : E) (q : CPoly F) : E := aeval x ((toPoly q).map ι)

variable (hC : ∀ c : Kc, c′ = 0) (ι : F →+* Kc) (x y : E) (hx : x′ = 1)
include hC hx

omit [DecidableEq F] in
lemma evF_deriv (q : CPoly F) : (evF ι x q)′ = evF ι x (deriv q) := by
  rw [evF, evF, toPoly_deriv, ← derivative_map]
  exact Differential.deriv_aeval_x x hC hx _

omit [DecidableEq F] hC hx
lemma evF_add (q r : CPoly F) : evF ι x (add q r) = evF ι x q + evF ι x r := by
  simp [evF, toPoly_add]
lemma evF_sub (q r : CPoly F) : evF ι x (sub q r) = evF ι x q - evF ι x r := by
  simp [evF, toPoly_sub]
lemma evF_mul (q r : CPoly F) : evF ι x (mul q r) = evF ι x q * evF ι x r := by
  simp [evF, toPoly_mul]
lemma evF_smul (t : F) (q : CPoly F) : evF ι x (smul t q) = algebraMap Kc E (ι t) * evF ι x q := by
  simp [evF, toPoly_smul]
lemma evF_one : evF ι x ([1] : CPoly F) = 1 := by simp [evF, CPoly.toPoly]

omit [DecidableEq F] in
lemma evF_sumMN (p : CPoly F) : ∀ logs : List (F × CPoly F × CPoly F × CPoly F),
    (∀ l ∈ logs, evF ι x (logN p l.2.1 l.2.2.1) ≠ 0) →
    evF ι x (sumMN p logs) = evF ι x (prodN p logs) *
      (logs.map fun l ↦ algebraMap Kc E (ι l.1) * evF ι x (logM p l.2.1 l.2.2.1) /
        evF ι x (logN p l.2.1 l.2.2.1)).sum
  | [], _ => by simp [sumMN, prodN, evF, CPoly.toPoly]
  | l :: ls, h => by
    have hl := h l List.mem_cons_self
    have ih := evF_sumMN p ls fun l' hl' ↦ h l' (List.mem_cons_of_mem _ hl')
    have hpc : prodN p (l :: ls) = mul (logN p l.2.1 l.2.2.1) (prodN p ls) := rfl
    rw [hpc]
    simp only [sumMN, List.map_cons, List.sum_cons, evF_add, evF_mul, evF_smul]
    rw [ih]
    field_simp

end Sound

section Sound2

variable {F : Type*} [Field F] [DecidableEq F]
variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Certificates over `F` prove elementarity.** -/
theorem logCheckF_sound (hC : ∀ c : Kc, c′ = 0) (ι : F →+* Kc) (x y : E) (hx : x′ = 1)
    (p A D W V : CPoly F) (logs : List (F × CPoly F × CPoly F × CPoly F))
    (hy : y ^ 2 = evF ι x p) (h : logCheckF p A D W V logs = true) :
    HasElementaryIntegral (evF ι x A / (evF ι x D * y)) := by
  classical
  simp only [logCheckF, Bool.and_eq_true, Bool.not_eq_true', beq_iff, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hp0, hD0⟩, hV0⟩, hlogs⟩, hmain⟩ := h
  have nz : ∀ q : CPoly F, isZero q = false → toPoly q ≠ 0 := fun q hq h0 ↦ by
    rw [(isZero_iff _).mpr h0] at hq; exact Bool.noConfusion hq
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ q : CPoly F, toPoly q ≠ 0 → evF ι x q ≠ 0 := fun q hq ↦
    aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff ι.injective).mpr hq)
  have hP0 := hne p (nz p hp0)
  have hy0 : y ≠ 0 := by rintro rfl; apply hP0; rw [← hy]; ring
  have hder := evF_deriv hC ι x hx
  set r := evF ι x (deriv p) / (2 * evF ι x p) with hr
  have hyd : y′ = r * y := by
    have := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul] at this
    rw [hder] at this
    rw [hr, ← hy]
    field_simp
    linear_combination this
  -- each logarithm
  have hlog : ∀ l ∈ logs, (evF ι x l.2.1 + evF ι x l.2.2.1 * y) / evF ι x l.2.2.2 ≠ 0 ∧
      logDeriv ((evF ι x l.2.1 + evF ι x l.2.2.1 * y) / evF ι x l.2.2.2) =
        evF ι x (logM p l.2.1 l.2.2.1) / (2 * evF ι x (logN p l.2.1 l.2.2.1)) *
          (y / evF ι x p) := by
    intro l hl
    obtain ⟨⟨hN0, hd0⟩, h1⟩ := hlogs l hl
    obtain ⟨κ, a, b, d⟩ := l
    simp only at hN0 hd0 h1 ⊢
    have hNx := hne _ (nz _ hN0)
    have hNe : evF ι x (logN p a b) = evF ι x a ^ 2 - evF ι x b ^ 2 * evF ι x p := by
      simp only [logN, evF_sub, evF_mul]; ring
    have hdx := hne _ (nz _ hd0)
    have hab0 : evF ι x a + evF ι x b * y ≠ 0 := by
      intro h0; apply hNx; rw [hNe, ← hy, show evF ι x a = -(evF ι x b * y) by
        linear_combination h0]; ring
    refine ⟨div_ne_zero hab0 hdx, ?_⟩
    set A' := evF ι x a
    set B' := evF ι x b
    set Pp := evF ι x p
    set D' := evF ι x d
    have e1 : (evF ι x (logN p a b))′ * D' = 2 * evF ι x (logN p a b) * D'′ := by
      have := congrArg (fun P : F[X] ↦ aeval x (P.map ι)) h1
      simp only [toPoly_mul, toPoly_smul, Polynomial.map_mul, map_mul, map_C, aeval_C] at this
      change evF ι x (deriv (logN p a b)) * D' = _ * evF ι x (logN p a b) * evF ι x (deriv d) at this
      rw [← hder, ← hder] at this
      rw [this]
      simp only [map_ofNat]
      rfl
    rw [hNe] at e1
    simp only [map_sub, map_mul, pow_two, Derivation.leibniz, smul_eq_mul] at e1
    have hPd : Pp′ = evF ι x (deriv p) := hder p
    rw [hPd] at e1
    have hC0 : (A' * A'′ - B' * (B'′ + B' * r) * Pp) / (A' ^ 2 - B' ^ 2 * Pp) - D'′ / D' = 0 := by
      rw [hr]
      rw [← hNe]
      field_simp
      rw [hNe]
      linear_combination e1
    have hM : evF ι x (logM p a b) = 2 * Pp * (A' * B'′ - A'′ * B') + A' * B' * evF ι x (deriv p) := by
      simp only [logM, evF_add, evF_mul, evF_smul, evF_sub, ← hder, map_ofNat]
      rfl
    have hY : (A' * (B'′ + B' * r) - A'′ * B') / (A' ^ 2 - B' ^ 2 * Pp) * y =
        evF ι x (logM p a b) / (2 * evF ι x (logN p a b)) * (y / Pp) := by
      rw [hM, hNe, hr]
      field_simp
      ring
    rw [logDeriv_div _ _ hab0 hdx, logDeriv_ab y _ _ Pp r hy hyd (by rw [← hNe]; exact hNx)]
    unfold logDeriv
    linear_combination hC0 + hY
  -- the main identity
  have hNl : ∀ l ∈ logs, evF ι x (logN p l.2.1 l.2.2.1) ≠ 0 := fun l hl ↦ hne _ (nz _ (hlogs l hl).1.1)
  have hprod0 : ∀ ls : List (F × CPoly F × CPoly F × CPoly F), (∀ l ∈ ls,
      evF ι x (logN p l.2.1 l.2.2.1) ≠ 0) → evF ι x (prodN p ls) ≠ 0 := by
    intro ls
    induction ls with
    | nil => intro _; simp [prodN, evF, CPoly.toPoly]
    | cons l ls ih =>
      intro h
      have hpc : prodN p (l :: ls) = mul (logN p l.2.1 l.2.2.1) (prodN p ls) := rfl
      rw [hpc, evF_mul]
      exact mul_ne_zero (h l List.mem_cons_self) (ih fun l' hl' ↦ h l' (List.mem_cons_of_mem _ hl'))
  have hP := hprod0 logs hNl
  set S := (logs.map fun l ↦ algebraMap Kc E (ι l.1) * evF ι x (logM p l.2.1 l.2.2.1) /
    evF ι x (logN p l.2.1 l.2.2.1)).sum with hS
  have hm := congrArg (fun P : F[X] ↦ aeval x (P.map ι)) hmain
  change evF ι x _ = evF ι x _ at hm
  simp only [evF_mul, evF_smul, evF_add, evF_sub, map_ofNat] at hm
  rw [evF_sumMN ι x p logs hNl, ← hS] at hm
  rw [← hder W, ← hder V, ← hder p] at hm
  have hVx := hne V (nz V hV0)
  have hDx := hne D (nz D hD0)
  have hid : 2 * evF ι x A * evF ι x V ^ 2 = evF ι x D * (2 * ((evF ι x W)′ * evF ι x V -
      evF ι x W * (evF ι x V)′) * evF ι x p + evF ι x W * evF ι x V * (evF ι x p)′ +
        evF ι x V ^ 2 * S) := by
    refine mul_right_cancel₀ hP ?_
    linear_combination hm
  set u : F × CPoly F × CPoly F × CPoly F → E :=
    fun l ↦ (evF ι x l.2.1 + evF ι x l.2.2.1 * y) / evF ι x l.2.2.2 with hu
  have hsum : (logs.map fun l ↦ algebraMap Kc E (ι l.1) * logDeriv (u l)).sum =
      S / 2 * (y / evF ι x p) := by
    have e1 : ∀ l ∈ logs, algebraMap Kc E (ι l.1) * logDeriv (u l) =
        (algebraMap Kc E (ι l.1) * evF ι x (logM p l.2.1 l.2.2.1) / evF ι x (logN p l.2.1 l.2.2.1)) *
          (1 / 2 * (y / evF ι x p)) := by
      intro l hl
      show algebraMap Kc E (ι l.1) * logDeriv ((evF ι x l.2.1 + evF ι x l.2.2.1 * y) /
        evF ι x l.2.2.2) = _
      rw [(hlog l hl).2]
      have := hNl l hl
      field_simp
    rw [List.map_congr_left e1, List.sum_map_mul_right, hS]
    ring
  have key : evF ι x A / (evF ι x D * y) = (evF ι x W / evF ι x V * y)′ +
      (logs.map fun l ↦ algebraMap Kc E (ι l.1) * logDeriv (u l)).sum := by
    rw [hsum, Derivation.leibniz, Derivation.leibniz_div, hyd, hr]
    simp only [smul_eq_mul]
    rw [hder p] at hid
    field_simp
    linear_combination (evF ι x p) * hid - (evF ι x D * (2 * ((evF ι x W)′ * evF ι x V -
      evF ι x W * (evF ι x V)′) * evF ι x p + evF ι x W * evF ι x V * evF ι x (deriv p) +
        evF ι x V ^ 2 * S)) * hy
  rw [key]
  have := hasElementaryIntegral_of_liouville_form (evF ι x W / evF ι x V * y)
    (logs.map fun l ↦ (algebraMap Kc E (ι l.1), u l)) (by
      intro q hq
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
      exact ⟨by rw [deriv_algebraMap, hC, map_zero], (hlog l hl).1⟩)
  rw [List.map_map] at this
  exact this

set_option maxHeartbeats 1600000 in
/-- **Certificates with remainder: the decomposition.** -/
theorem logCheckFB_decomp (hC : ∀ c : Kc, c′ = 0) (ι : F →+* Kc) (x y : E) (hx : x′ = 1)
    (p A D W V B0 : CPoly F) (logs : List (F × CPoly F × CPoly F × CPoly F))
    (hy : y ^ 2 = evF ι x p) (h : logCheckFB p A D W V B0 logs = true) :
    (∀ l ∈ logs, (evF ι x l.2.1 + evF ι x l.2.2.1 * y) / evF ι x l.2.2.2 ≠ 0) ∧
    evF ι x A / (evF ι x D * y) = (evF ι x W / evF ι x V * y)′ +
      (logs.map fun l ↦ algebraMap Kc E (ι l.1) *
        logDeriv ((evF ι x l.2.1 + evF ι x l.2.2.1 * y) / evF ι x l.2.2.2)).sum +
      evF ι x B0 / y := by
  classical
  simp only [logCheckFB, Bool.and_eq_true, Bool.not_eq_true', beq_iff, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hp0, hD0⟩, hV0⟩, hlogs⟩, hmain⟩ := h
  have nz : ∀ q : CPoly F, isZero q = false → toPoly q ≠ 0 := fun q hq h0 ↦ by
    rw [(isZero_iff _).mpr h0] at hq; exact Bool.noConfusion hq
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ q : CPoly F, toPoly q ≠ 0 → evF ι x q ≠ 0 := fun q hq ↦
    aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff ι.injective).mpr hq)
  have hP0 := hne p (nz p hp0)
  have hy0 : y ≠ 0 := by rintro rfl; apply hP0; rw [← hy]; ring
  have hder := evF_deriv hC ι x hx
  set r := evF ι x (deriv p) / (2 * evF ι x p) with hr
  have hyd : y′ = r * y := by
    have := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul] at this
    rw [hder] at this
    rw [hr, ← hy]
    field_simp
    linear_combination this
  -- each logarithm
  have hlog : ∀ l ∈ logs, (evF ι x l.2.1 + evF ι x l.2.2.1 * y) / evF ι x l.2.2.2 ≠ 0 ∧
      logDeriv ((evF ι x l.2.1 + evF ι x l.2.2.1 * y) / evF ι x l.2.2.2) =
        evF ι x (logM p l.2.1 l.2.2.1) / (2 * evF ι x (logN p l.2.1 l.2.2.1)) *
          (y / evF ι x p) := by
    intro l hl
    obtain ⟨⟨hN0, hd0⟩, h1⟩ := hlogs l hl
    obtain ⟨κ, a, b, d⟩ := l
    simp only at hN0 hd0 h1 ⊢
    have hNx := hne _ (nz _ hN0)
    have hNe : evF ι x (logN p a b) = evF ι x a ^ 2 - evF ι x b ^ 2 * evF ι x p := by
      simp only [logN, evF_sub, evF_mul]; ring
    have hdx := hne _ (nz _ hd0)
    have hab0 : evF ι x a + evF ι x b * y ≠ 0 := by
      intro h0; apply hNx; rw [hNe, ← hy, show evF ι x a = -(evF ι x b * y) by
        linear_combination h0]; ring
    refine ⟨div_ne_zero hab0 hdx, ?_⟩
    set A' := evF ι x a
    set B' := evF ι x b
    set Pp := evF ι x p
    set D' := evF ι x d
    have e1 : (evF ι x (logN p a b))′ * D' = 2 * evF ι x (logN p a b) * D'′ := by
      have := congrArg (fun P : F[X] ↦ aeval x (P.map ι)) h1
      simp only [toPoly_mul, toPoly_smul, Polynomial.map_mul, map_mul, map_C, aeval_C] at this
      change evF ι x (deriv (logN p a b)) * D' = _ * evF ι x (logN p a b) * evF ι x (deriv d) at this
      rw [← hder, ← hder] at this
      rw [this]
      simp only [map_ofNat]
      rfl
    rw [hNe] at e1
    simp only [map_sub, map_mul, pow_two, Derivation.leibniz, smul_eq_mul] at e1
    have hPd : Pp′ = evF ι x (deriv p) := hder p
    rw [hPd] at e1
    have hC0 : (A' * A'′ - B' * (B'′ + B' * r) * Pp) / (A' ^ 2 - B' ^ 2 * Pp) - D'′ / D' = 0 := by
      rw [hr]
      rw [← hNe]
      field_simp
      rw [hNe]
      linear_combination e1
    have hM : evF ι x (logM p a b) = 2 * Pp * (A' * B'′ - A'′ * B') + A' * B' * evF ι x (deriv p) := by
      simp only [logM, evF_add, evF_mul, evF_smul, evF_sub, ← hder, map_ofNat]
      rfl
    have hY : (A' * (B'′ + B' * r) - A'′ * B') / (A' ^ 2 - B' ^ 2 * Pp) * y =
        evF ι x (logM p a b) / (2 * evF ι x (logN p a b)) * (y / Pp) := by
      rw [hM, hNe, hr]
      field_simp
      ring
    rw [logDeriv_div _ _ hab0 hdx, logDeriv_ab y _ _ Pp r hy hyd (by rw [← hNe]; exact hNx)]
    unfold logDeriv
    linear_combination hC0 + hY
  -- the main identity
  have hNl : ∀ l ∈ logs, evF ι x (logN p l.2.1 l.2.2.1) ≠ 0 := fun l hl ↦ hne _ (nz _ (hlogs l hl).1.1)
  have hprod0 : ∀ ls : List (F × CPoly F × CPoly F × CPoly F), (∀ l ∈ ls,
      evF ι x (logN p l.2.1 l.2.2.1) ≠ 0) → evF ι x (prodN p ls) ≠ 0 := by
    intro ls
    induction ls with
    | nil => intro _; simp [prodN, evF, CPoly.toPoly]
    | cons l ls ih =>
      intro h
      have hpc : prodN p (l :: ls) = mul (logN p l.2.1 l.2.2.1) (prodN p ls) := rfl
      rw [hpc, evF_mul]
      exact mul_ne_zero (h l List.mem_cons_self) (ih fun l' hl' ↦ h l' (List.mem_cons_of_mem _ hl'))
  have hP := hprod0 logs hNl
  set S := (logs.map fun l ↦ algebraMap Kc E (ι l.1) * evF ι x (logM p l.2.1 l.2.2.1) /
    evF ι x (logN p l.2.1 l.2.2.1)).sum with hS
  have hm := congrArg (fun P : F[X] ↦ aeval x (P.map ι)) hmain
  change evF ι x _ = evF ι x _ at hm
  simp only [evF_mul, evF_smul, evF_add, evF_sub, map_ofNat] at hm
  rw [evF_sumMN ι x p logs hNl, ← hS] at hm
  rw [← hder W, ← hder V, ← hder p] at hm
  have hVx := hne V (nz V hV0)
  have hDx := hne D (nz D hD0)
  have hid : 2 * evF ι x A * evF ι x V ^ 2 = evF ι x D * (2 * ((evF ι x W)′ * evF ι x V -
      evF ι x W * (evF ι x V)′) * evF ι x p + evF ι x W * evF ι x V * (evF ι x p)′ +
        evF ι x V ^ 2 * S + 2 * evF ι x B0 * evF ι x V ^ 2) := by
    refine mul_right_cancel₀ hP ?_
    linear_combination hm
  set u : F × CPoly F × CPoly F × CPoly F → E :=
    fun l ↦ (evF ι x l.2.1 + evF ι x l.2.2.1 * y) / evF ι x l.2.2.2 with hu
  have hsum : (logs.map fun l ↦ algebraMap Kc E (ι l.1) * logDeriv (u l)).sum =
      S / 2 * (y / evF ι x p) := by
    have e1 : ∀ l ∈ logs, algebraMap Kc E (ι l.1) * logDeriv (u l) =
        (algebraMap Kc E (ι l.1) * evF ι x (logM p l.2.1 l.2.2.1) / evF ι x (logN p l.2.1 l.2.2.1)) *
          (1 / 2 * (y / evF ι x p)) := by
      intro l hl
      show algebraMap Kc E (ι l.1) * logDeriv ((evF ι x l.2.1 + evF ι x l.2.2.1 * y) /
        evF ι x l.2.2.2) = _
      rw [(hlog l hl).2]
      have := hNl l hl
      field_simp
    rw [List.map_congr_left e1, List.sum_map_mul_right, hS]
    ring
  have key : evF ι x A / (evF ι x D * y) = (evF ι x W / evF ι x V * y)′ +
      (logs.map fun l ↦ algebraMap Kc E (ι l.1) * logDeriv (u l)).sum + evF ι x B0 / y := by
    rw [hsum, Derivation.leibniz, Derivation.leibniz_div, hyd, hr]
    simp only [smul_eq_mul]
    rw [hder p] at hid
    field_simp
    linear_combination (evF ι x p) * hid - (evF ι x D * (2 * ((evF ι x W)′ * evF ι x V -
      evF ι x W * (evF ι x V)′) * evF ι x p + evF ι x W * evF ι x V * evF ι x (deriv p) +
        evF ι x V ^ 2 * S)) * hy
  exact ⟨fun l hl ↦ (hlog l hl).1, key⟩

end Sound2

end CPoly
