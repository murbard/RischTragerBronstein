import RischTragerBronstein.Algebraic.HypLog
import RischTragerBronstein.Algebraic.HypCertComplete
import RischTragerBronstein.Algebraic.EllOrbit

/-!
# Hyperelliptic logarithmic parts of any genus: searching the torsion certificate

For `y² = p(x)` (any degree, any genus) and `∫ A / (D y)` with simple poles at rational points
`(αᵢ, βᵢ)` (`D` split and coprime to `p`, `p(αᵢ) = βᵢ²`), the residues `rᵢ = A(αᵢ) / (D′(αᵢ) βᵢ)`
are rational. For `K = n · lcm(den rᵢ)` (`n = 1, 2, …`) the search looks for
`u = (a + b y) / d` with divisor `K ∑ rᵢ ([Pᵢ] − [P̄ᵢ])`:

* `a + b y` must vanish to order `2|K rᵢ|` at `Qᵢ = (αᵢ, ±βᵢ)` (sign of `rᵢ`): with `V` a square
  root of `p` modulo `U = ∏ (x − αᵢ)^{2|K rᵢ|}` (Lagrange interpolation, then Newton's iteration),
  this is `U ∣ a + b V`, a linear system over the Riemann–Roch basis `xʲ, xᵏ y`;
* `d = ∏ (x − αᵢ)^{|K rᵢ|}`, and the Hermite part `W` (with `V = D`) solves a linear system.

A solution exists exactly when `∑ rᵢ ([Pᵢ] − [P̄ᵢ])` is torsion of order dividing `n`
(Abel–Jacobi); every candidate is checked by the polynomial identities of `hyp_log_cert`, so a
`true` answer is a proof of elementarity (`hypLogElem_sound`). The converse (a proof of
non-elementarity when no `n` works) needs a bound on the torsion of the Jacobian and is not provided.

`hypDecideLog` combines this with `hypCertDecide` (no logarithmic part: decided in both directions).
-/

open Polynomial Differential

namespace CPoly

open EllAlgo

/-! ### The search -/

/-- The distinct rational roots of `P`. -/
def ratRootsD (P : CPoly ℚ) : List ℚ :=
  ((ratRootsQ P).filter fun q ↦ Kron.evalC P q == 0).dedup

/-- `P ^ n`. -/
def powLog (P : CPoly ℚ) : ℕ → CPoly ℚ
  | 0 => [1]
  | n + 1 => mul P (powLog P n)

/-- Newton's iteration for `V² ≡ p (mod U)`. -/
def sqrtNewton (p U : CPoly ℚ) : ℕ → CPoly ℚ → CPoly ℚ
  | 0, V => V
  | k + 1, V =>
    sqrtNewton p U k (divMod (sub V (mul (sub (mul V V) p) (modInv (smul 2 V) U))) U).2

/-- The coefficient vector (length `N`) of `q mod U`. -/
def coeffVec (U q : CPoly ℚ) (N : ℕ) : CPoly ℚ :=
  (List.range N).map fun i ↦ ((divMod q U).2).getD i 0

/-- The log certificate `(a, b, d, K)` for a given `K`, if the divisor is principal. -/
def logCertFor (p : CPoly ℚ) (pts : List (ℚ × ℚ × ℚ)) (K : ℚ) : Option (CPoly ℚ × CPoly ℚ × CPoly ℚ) :=
  let ms := pts.map fun t ↦ (t.1, t.2.1, (K * t.2.2).num)
  let U := ms.foldr (fun m acc ↦ mul (powLog [-m.1, 1] (2 * m.2.2.natAbs)) acc) [1]
  let d := ms.foldr (fun m acc ↦ mul (powLog [-m.1, 1] m.2.2.natAbs) acc) [1]
  let N := 2 * (ms.map fun m ↦ m.2.2.natAbs).sum
  let V0 := Kron.lagr (ms.map (·.1)) (ms.map fun m ↦ if 0 < m.2.2 then m.2.1 else -m.2.1)
  let V := sqrtNewton p U (Nat.log 2 N + 2) V0
  let degp := (trim p).length - 1
  let da := N / 2
  let db := (N - degp) / 2
  let nb := if degp ≤ N then db + 1 else 0
  let cols := (List.range (da + 1)).map (fun j ↦ coeffVec U (monomial j 1) N) ++
    (List.range nb).map (fun k ↦ coeffVec U (mul (monomial k 1) V) N)
  match (nullBasis cols).find? (fun v ↦ !isZero (v.drop (da + 1))) with
  | some v => some (v.take (da + 1), v.drop (da + 1), d)
  | none => none

/-- The Hermite part `W` (with `V = D`) for a log certificate. -/
def logW (p A D a b : CPoly ℚ) (K : ℚ) : Option (CPoly ℚ) :=
  let N := sub (mul a a) (mul (mul b b) p)
  let M := add (mul (mul [2] p) (sub (mul a (deriv b)) (mul (deriv a) b))) (mul (mul a b) (deriv p))
  let dW := A.length + D.length + p.length
  let cols := (List.range (dW + 1)).map fun i ↦
    mul D (mul (mul [K] N) (add (mul (mul [2] (sub (mul (deriv (monomial i 1)) D)
      (mul (monomial i 1) (deriv D)))) p) (mul (mul (monomial i 1) D) (deriv p))))
  let target := sub (mul (mul (mul (mul [2] A) (mul D D)) N) [K]) (mul D (mul (mul D D) M))
  (linSolve cols target).map fun cs ↦ cs

/-- **The certificate check** (the hypotheses of `hyp_log_cert` with `V = D`). -/
def hypLogCheck (p A D W a b d : CPoly ℚ) (K : ℚ) : Bool :=
  let V := D
  let N := sub (mul a a) (mul (mul b b) p)
  let M := add (mul (mul [2] p) (sub (mul a (deriv b)) (mul (deriv a) b))) (mul (mul a b) (deriv p))
  !isZero p && !isZero D && !isZero d && decide (K ≠ 0) && !isZero N &&
    beq (mul (deriv N) d) (mul (mul [2] N) (deriv d)) &&
    beq (mul (mul (mul (mul [2] A) (mul V V)) N) [K])
      (mul D (add (mul (mul [K] N) (add (mul (mul [2] (sub (mul (deriv W) V) (mul W (deriv V)))) p)
        (mul (mul W V) (deriv p)))) (mul (mul V V) M)))

/-- The poles with their `y`-values and residues, when all are at rational non-branch points. -/
def logPts (p A D : CPoly ℚ) : Option (List (ℚ × ℚ × ℚ)) :=
  let rs := ratRootsD D
  if rs.length + 1 = (trim D).length then
    rs.mapM fun α ↦
      match qsqrt (Kron.evalC p α) with
      | some β => if β = 0 then none else
          some (α, β, Kron.evalC A α / (Kron.evalC (deriv D) α * β))
      | none => none
  else none

/-- **The search**: try `K = n · lcm(den rᵢ)` for `n = 1, …, nmax`. -/
def hypLogFind (p A D : CPoly ℚ) (nmax : ℕ) :
    Option (CPoly ℚ × CPoly ℚ × CPoly ℚ × CPoly ℚ × ℚ) :=
  match logPts p A D with
  | some pts =>
    let L : ℕ := pts.foldr (fun t acc ↦ Nat.lcm t.2.2.den acc) 1
    (List.range nmax).findSome? fun n ↦
      let K : ℚ := ((n + 1) * L : ℕ)
      match logCertFor p pts K with
      | some (a, b, d) =>
        match logW p A D a b K with
        | some W => if hypLogCheck p A D W a b d K then some (W, a, b, d, K) else none
        | none => none
      | none => none
  | none => none

/-- `true` when a checked logarithmic certificate is found. -/
def hypLogElem (p A D : CPoly ℚ) (nmax : ℕ) : Bool := (hypLogFind p A D nmax).isSome

/-- **The combined procedure**: `hypCertDecide` (no log part, both directions), else the torsion
certificate (elementary), else unknown. -/
def hypDecideLog (p A D : CPoly ℚ) (nmax : ℕ) : Option Bool :=
  match hypCertDecide p A D with
  | some b => some b
  | none => if hypLogElem p A D nmax then some true else none

/-! ### Soundness -/

section Sound

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma hypLogFind_check {p A D : CPoly ℚ} {nmax : ℕ} {W a b d : CPoly ℚ} {K : ℚ}
    (h : hypLogFind p A D nmax = some (W, a, b, d, K)) : hypLogCheck p A D W a b d K = true := by
  unfold hypLogFind at h
  split at h
  · obtain ⟨n, -, hn⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hn
    split at hn
    · split at hn
      · split_ifs at hn with hc
        cases hn
        exact hc
      · cases hn
    · cases hn
  · cases h

/-- **A checked log certificate proves elementarity.** -/
theorem hypLogCheck_sound (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : CPoly ℚ)
    (hy : y ^ 2 = aeval x (toPoly p)) (A D W a b d : CPoly ℚ) (K : ℚ)
    (h : hypLogCheck p A D W a b d K = true) :
    HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  simp only [hypLogCheck, Bool.and_eq_true, Bool.not_eq_true', beq_iff, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hp, hD⟩, hd⟩, hK⟩, hN⟩, h1⟩, h2⟩ := h
  have nz : ∀ q : CPoly ℚ, isZero q = false → toPoly q ≠ 0 := fun q hq h0 ↦ by
    rw [(isZero_iff _).mpr h0] at hq; exact Bool.noConfusion hq
  have hK' : toPoly ([K] : CPoly ℚ) = C K := by simp [toPoly]
  have h2' : toPoly ([2] : CPoly ℚ) = 2 := by simp [toPoly]; rfl
  simp only [toPoly_mul, toPoly_sub, toPoly_add, toPoly_deriv, hK', h2'] at h1 h2 hN
  refine hyp_log_cert hC x y hx (toPoly p) (nz _ hp) hy (toPoly A) (toPoly D) (toPoly W)
    (toPoly D) (toPoly a) (toPoly b) (toPoly d) K (nz _ hD) (nz _ hD) (nz _ hd) hK ?_ ?_ ?_
  · have := nz _ hN
    simpa [toPoly_sub, toPoly_mul, sq] using this
  · rw [sq, sq]; linear_combination h1
  · rw [sq, sq]; linear_combination h2

theorem hypLogElem_sound (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : CPoly ℚ)
    (hy : y ^ 2 = aeval x (toPoly p)) (A D : CPoly ℚ) (nmax : ℕ) (h : hypLogElem p A D nmax = true) :
    HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold hypLogElem at h
  obtain ⟨⟨W, a, b, d, K⟩, hf⟩ := Option.isSome_iff_exists.mp h
  exact hypLogCheck_sound hC x y hx p hy A D W a b d K (hypLogFind_check hf)

/-- **Correctness of the combined procedure** (any genus, `p` squarefree of odd degree). -/
theorem hypDecideLog_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (p : CPoly ℚ) (hp : Squarefree (toPoly p)) (hodd : Odd (toPoly p).natDegree)
    (hy : y ^ 2 = aeval x (toPoly p)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (nmax : ℕ) (ans : Bool) (h : hypDecideLog p A D nmax = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold hypDecideLog at h
  split at h
  · rename_i b hb
    cases h
    obtain ⟨W, V, B0, hD', hV, hid, hdeg, hbB⟩ := hypCertDecide_spec _ _ _ _ hb
    rw [hbB, Differential.hyp_decides_cert hC hCall x y hx p hp hodd hy hgen _ _ _ _ _ hD' hV hid
      hdeg]
  · split_ifs at h with hl
    cases h
    exact ⟨fun _ ↦ hypLogElem_sound hC x y hx p hy A D nmax hl, fun _ ↦ rfl⟩

end Sound

/-! ### Galois orbits of poles -/

/-- For each irreducible factor `f` of `D`: `(f, g, z)` with `y ≡ g (mod f)` at the poles and the
rational residue `z` (checked later by `hypLogCheck`). -/
def logOrbs (p A D : CPoly ℚ) : Option (List (CPoly ℚ × CPoly ℚ × ℚ)) :=
  (Kron.factorQ (Kron.degC D + 1) D).mapM fun f ↦
    let fd := deriv f
    let Dd := (divMod (deriv D) f).2
    let w := (divMod (mul (mul A A) (modInv (mul (mul Dd Dd) p) f)) f).2
    match trim w with
    | [c0] =>
      match qsqrt c0 with
      | some z => if z = 0 then none else
          some (f, (divMod (mul A (modInv (smul z Dd) f)) f).2, z)
      | none => none
    | _ => let _ := fd; none

/-- The log certificate for orbits and a given `K`. -/
def logCertOrb (p : CPoly ℚ) (orbs : List (CPoly ℚ × CPoly ℚ × ℚ)) (K : ℚ) :
    Option (CPoly ℚ × CPoly ℚ × CPoly ℚ) :=
  let ms := orbs.map fun t ↦ (t.1, t.2.1, (K * t.2.2).num)
  let U := ms.foldr (fun m acc ↦ mul (powLog m.1 (2 * m.2.2.natAbs)) acc) [1]
  let d := ms.foldr (fun m acc ↦ mul (powLog m.1 m.2.2.natAbs) acc) [1]
  let N := (trim U).length - 1
  let Fp := ms.foldr (fun m acc ↦ mul m.1 acc) [1]
  let V0 := ms.foldr (fun m acc ↦
    let co := (divMod Fp m.1).1
    add (mul (smul (if 0 < m.2.2 then 1 else -1) m.2.1) (mul co (modInv co m.1))) acc) []
  let V := sqrtNewton p U (Nat.log 2 N + 2) (divMod V0 U).2
  let degp := (trim p).length - 1
  let da := N / 2
  let db := (N - degp) / 2
  let nb := if degp ≤ N then db + 1 else 0
  let cols := (List.range (da + 1)).map (fun j ↦ coeffVec U (monomial j 1) N) ++
    (List.range nb).map (fun k ↦ coeffVec U (mul (monomial k 1) V) N)
  match (nullBasis cols).find? (fun v ↦ !isZero (v.drop (da + 1))) with
  | some v => some (v.take (da + 1), v.drop (da + 1), d)
  | none => none

/-- **The search over Galois orbits.** -/
def hypLogFindOrb (p A D : CPoly ℚ) (nmax : ℕ) :
    Option (CPoly ℚ × CPoly ℚ × CPoly ℚ × CPoly ℚ × ℚ) :=
  match logOrbs p A D with
  | some orbs =>
    let L : ℕ := orbs.foldr (fun t acc ↦ Nat.lcm t.2.2.den acc) 1
    (List.range nmax).findSome? fun n ↦
      let K : ℚ := ((n + 1) * L : ℕ)
      match logCertOrb p orbs K with
      | some (a, b, d) =>
        match logW p A D a b K with
        | some W => if hypLogCheck p A D W a b d K then some (W, a, b, d, K) else none
        | none => none
      | none => none
  | none => none

lemma hypLogFindOrb_check {p A D : CPoly ℚ} {nmax : ℕ} {W a b d : CPoly ℚ} {K : ℚ}
    (h : hypLogFindOrb p A D nmax = some (W, a, b, d, K)) : hypLogCheck p A D W a b d K = true := by
  unfold hypLogFindOrb at h
  split at h
  · obtain ⟨n, -, hn⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hn
    split at hn
    · split at hn
      · split_ifs at hn with hc
        cases hn
        exact hc
      · cases hn
    · cases hn
  · cases h

/-- `true` when a checked certificate is found over Galois orbits. -/
def hypLogElemOrb (p A D : CPoly ℚ) (nmax : ℕ) : Bool := (hypLogFindOrb p A D nmax).isSome

section SoundOrb

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

theorem hypLogElemOrb_sound (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p : CPoly ℚ)
    (hy : y ^ 2 = aeval x (toPoly p)) (A D : CPoly ℚ) (nmax : ℕ)
    (h : hypLogElemOrb p A D nmax = true) :
    HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold hypLogElemOrb at h
  obtain ⟨⟨W, a, b, d, K⟩, hf⟩ := Option.isSome_iff_exists.mp h
  exact hypLogCheck_sound hC x y hx p hy A D W a b d K (hypLogFindOrb_check hf)

end SoundOrb

/-- **The combined hyperelliptic procedure**: no log part (both directions), else a torsion
certificate at rational points or over Galois orbits (elementary), else unknown. -/
def hypDecideAllLog (p A D : CPoly ℚ) (nmax : ℕ) : Option Bool :=
  match hypCertDecide p A D with
  | some b => some b
  | none => if hypLogElem p A D nmax || hypLogElemOrb p A D nmax then some true else none

section SoundAll

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Correctness of the combined procedure** (any genus). -/
theorem hypDecideAllLog_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (p : CPoly ℚ) (hp : Squarefree (toPoly p)) (hodd : Odd (toPoly p).natDegree)
    (hy : y ^ 2 = aeval x (toPoly p)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (nmax : ℕ) (ans : Bool) (h : hypDecideAllLog p A D nmax = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold hypDecideAllLog at h
  split at h
  · rename_i b hb
    cases h
    obtain ⟨W, V, B0, hD', hV, hid, hdeg, hbB⟩ := hypCertDecide_spec _ _ _ _ hb
    rw [hbB, Differential.hyp_decides_cert hC hCall x y hx p hp hodd hy hgen _ _ _ _ _ hD' hV hid
      hdeg]
  · split_ifs at h with hl
    cases h
    refine ⟨fun _ ↦ ?_, fun _ ↦ rfl⟩
    rcases Bool.or_eq_true_iff.mp hl with hl | hl
    · exact hypLogElem_sound hC x y hx p hy A D nmax hl
    · exact hypLogElemOrb_sound hC x y hx p hy A D nmax hl

end SoundAll

end CPoly
