import RischTragerBronstein.Algebraic.SupDecideQ
import RischTragerBronstein.Algebraic.SupMobius

/-!
# Superelliptic integrals with rational data: `gcd(n, deg f) = 1` or `n ∣ deg f`

`superDecideMobQ` handles `n ∣ deg f`: it builds a number field containing `ζₙ`, the roots of
`f`, the non-branch roots of `D`, `n`-th roots of `f` there and an `n`-th root of the leading
coefficient of `f` (the value of `w` at the new point `t = 0`), takes a root `e` of `f` and runs
`superFrontMob` (branch point `e` moved to infinity). `superDecideAll` dispatches between
`superDecideQ` (`gcd(n, deg f) = 1`) and `superDecideMobQ` (`n ∣ deg f`).

* `superDecideMobQ_spec`, `superDecideAll_spec`: every answer is correct.

For prime `n` the two cases cover every squarefree `f`. The case `1 < gcd(n, deg f) < n` has
several ramified places over infinity, and so does every Möbius image of it; it is not handled.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac NFC

namespace Sup

/-- The field for `n ∣ deg f`: `ζₙ`, the roots of `f` and of `S`, `n`-th roots of `f` at the
roots of `S`, and an `n`-th root of the leading coefficient `c` of `f`. -/
noncomputable def buildFieldMob (f S : CPoly ℚ) (n fuel : ℕ) :
    Option (Σ' M : CPoly ℚ, Kron.irredQ M = true) :=
  match splitLoop (xnMinus n 1) fuel [0, 1] irredQ_X with
  | some ⟨M1, h1⟩ =>
    match splitLoop f fuel M1 h1 with
    | some ⟨M2, h2⟩ =>
      match splitLoop S fuel M2 h2 with
      | some ⟨M3, h3⟩ =>
        match nthLoop f S n fuel M3 h3 with
        | some ⟨M4, h4⟩ => nthLoop [f.getLastD 0] [0, 1] n fuel M4 h4
        | none => none
      | none => none
    | none => none
  | none => none

/-- **The procedure over a given field `K = ℚ[θ]/(M)`** for `n ∣ deg f`. -/
noncomputable def superDecideMobM (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (f : CPoly ℚ)
    (n : ℕ) (A : List (CPoly ℚ)) (D : CPoly ℚ) (B : ℕ) : Option Bool :=
  match rootsIn M (liftK (K := NF M) (xnMinus n 1)), rootsIn M (liftK (K := NF M) f) with
  | some rz, some (e :: _) =>
    match rz.find? (isPrimRoot M n) with
    | some ζ =>
      if isPrimRoot M n ζ then
        superFrontMob (liftK (K := NF M) f) n ζ
          (fun P ↦ torsOracle (nfRedAt (M := M) (M.map Rat.num)) (primesBelow B) B P n)
          (fun S ↦ (rootsIn M S).getD [])
          (fun c ↦ ((rootsIn M (xnMinus n c)).bind List.head?).getD 0)
          e (A.map (liftK (K := NF M))) (liftK (K := NF M) D)
      else none
    | none => none
  | _, _ => none

/-- **The procedure for `n ∣ deg f`** (`B`: bound for primes and orders; `fuel`: field loops). -/
noncomputable def superDecideMobQ (f : CPoly ℚ) (n : ℕ) (A : List (CPoly ℚ)) (D : CPoly ℚ)
    (B fuel : ℕ) : Option Bool :=
  match buildFieldMob f (nbPartK f D) n fuel with
  | none => none
  | some ⟨M, hM⟩ =>
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    superDecideMobM M f n A D B

/-- Staged evaluation (as `superDecideQ_eq`). -/
lemma superDecideMobQ_eq {f : CPoly ℚ} {n : ℕ} {A : List (CPoly ℚ)} {D : CPoly ℚ} {B fuel : ℕ}
    {M : CPoly ℚ} (hM : Kron.irredQ M = true)
    (h : (buildFieldMob f (nbPartK f D) n fuel).map PSigma.fst = some M) :
    superDecideMobQ f n A D B fuel =
      @superDecideMobM M ⟨Kron.irredQ_sound M hM⟩ f n A D B := by
  unfold superDecideMobQ
  rcases e : buildFieldMob f (nbPartK f D) n fuel with _ | ⟨M', hM'⟩
  · simp [e] at h
  · simp only [e, Option.map_some, Option.some.injEq] at h
    subst h
    rfl

/-- **The dispatcher**: `gcd(n, deg f) = 1` → `superDecideQ`; `n ∣ deg f` → `superDecideMobQ`. -/
noncomputable def superDecideAll (f : CPoly ℚ) (n : ℕ) (A : List (CPoly ℚ)) (D : CPoly ℚ)
    (B fuel : ℕ) : Option Bool :=
  if Nat.Coprime n (f.length - 1) then superDecideQ f n A D B fuel
  else if (f.length - 1) % n = 0 then superDecideMobQ f n A D B fuel
  else none

section Spec

open Differential IntermediateField

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `superDecideMobM`**, over any number field. -/
theorem superDecideMobM_spec [IsAlgClosed Kc] (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]
    (hM : Kron.irredQ M = true) (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (f : CPoly ℚ) {n : ℕ} (hn : 0 < n) (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ)
    (B : ℕ) (ans : Bool) (h : superDecideMobM M f n A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  unfold superDecideMobM at h
  split at h
  swap
  · cases h
  rename_i rz e _ _ _
  split at h
  swap
  · cases h
  rename_i ζ _
  split_ifs at h with hζ
  let ι : NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NF M) (M := Kc)).toRingHom
  have hmZ : toPoly M = (toPoly (M.map Rat.num)).map (Int.castRingHom ℚ) :=
    (Kron.polyZ_map M (int_of_irredQ hM)).symm
  have hyK : y ^ n = aeval x ((toPoly (liftK (K := NF M) f)).map ι) := by
    rw [map_liftK_comp]; exact hy
  have hspec := superFrontMob_spec hC x y hx ι (liftK (K := NF M) f) hn hyK hgen
    (isPrimRoot_spec hn hζ) _
    (fun P hsq hcop ↦ torsOracle_spec (nfRedAt (M := M) (M.map Rat.num))
      (fun p _ R hR ↦ nfRedAt_valid _ hmZ p R hR) (primesBelow B) B hsq hcop)
    _ _ e _ _ ans h
  rw [hspec]
  have hA : ∀ j, (toPoly ((A.map (liftK (K := NF M))).getD j [])).map ι =
      (toPoly (A.getD j [])).map (algebraMap ℚ Kc) := fun j ↦ by
    rw [show ([] : CPoly (NF M)) = liftK (K := NF M) [] from rfl, List.getD_map, map_liftK_comp]
  simp only [hA, map_liftK_comp]

/-- **Correctness of `superDecideMobQ`**: every answer is correct. -/
theorem superDecideMobQ_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (f : CPoly ℚ) {n : ℕ} (hn : 0 < n) (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ)
    (B fuel : ℕ) (ans : Bool) (h : superDecideMobQ f n A D B fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  unfold superDecideMobQ at h
  split at h
  · cases h
  rename_i M hM _
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  exact superDecideMobM_spec M hM hC x y hx f hn hy hgen A D B ans h

/-- **Correctness of `superDecideAll`**: for `f ∈ ℚ[x]` squarefree of positive degree, every
answer is correct. -/
theorem superDecideAll_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (f : CPoly ℚ) {n : ℕ} (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hdeg : (toPoly f).natDegree = f.length - 1) (hpd : 0 < f.length - 1)
    (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ) (hD : toPoly D ≠ 0)
    (B fuel : ℕ) (ans : Bool) (h : superDecideAll f n A D B fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  unfold superDecideAll at h
  split_ifs at h with hcop hdiv
  · exact superDecideQ_spec hC x y hx f hn hsq hdeg hpd hcop hy hgen A D hD B fuel ans h
  · exact superDecideMobQ_spec hC x y hx f hn hy hgen A D B fuel ans h

end Spec

end Sup
