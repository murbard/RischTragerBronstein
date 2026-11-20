import RischTragerBronstein.Algebraic.SupFrontEvent
import RischTragerBronstein.Jacobian.HypDecideNF

/-!
# Superelliptic integrals with rational data

`superDecideQ f n A D B fuel` decides `∫ ∑_{j<n} (Aⱼ(x)/D(x)) yʲ dx` on `yⁿ = f(x)` for
`f, Aⱼ, D ∈ ℚ[x]`: it builds a number field `K = ℚ[θ]/(M)` containing the `n`-th roots of unity,
the roots `aᵢ` of the non-branch part of `D` and `n`-th roots `bᵢ` of `f(aᵢ)` (`splitLoop`,
`nthLoop`, via `rootsIn` and `extStep`), checks the data, and runs `superFront` over `K` with the
two-prime torsion oracle. `superDecideQ_spec`: every answer is correct (constants algebraically
closed).
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac NFC

namespace Sup

/-- `Xⁿ − c`. -/
def xnMinus {K : Type*} [Field K] (n : ℕ) (c : K) : CPoly K := (-c) :: (List.replicate (n - 1) 0 ++ [1])

/-- **The `n`-th root loop**: adjoin `n`-th roots of `f(α)` at the roots `α` of `S`. -/
noncomputable def nthLoop (f S : CPoly ℚ) (n : ℕ) : ℕ → (M : CPoly ℚ) → Kron.irredQ M = true →
    Option (Σ' M : CPoly ℚ, Kron.irredQ M = true)
  | 0, _, _ => none
  | k + 1, M, hM =>
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    match rootsIn M (liftK (K := NF M) S) with
    | none => none
    | some rs =>
      match rs.dedup.find? (fun α ↦
          ((rootsIn M (xnMinus n (evalC (liftK (K := NF M) f) α))).bind List.head?).isNone) with
      | none => some ⟨M, hM⟩
      | some α0 =>
        match extStep M (xnMinus n (evalC (liftK (K := NF M) f) α0)) with
        | some ⟨M', hM'⟩ => nthLoop f S n k M' hM'
        | none => none

/-- **The field**: `ζₙ`, the roots of `S`, `n`-th roots of `f` there. -/
noncomputable def buildField (f S : CPoly ℚ) (n fuel : ℕ) : Option (Σ' M : CPoly ℚ, Kron.irredQ M = true) :=
  match splitLoop (xnMinus n 1) fuel [0, 1] irredQ_X with
  | some ⟨M1, h1⟩ =>
    match splitLoop S fuel M1 h1 with
    | some ⟨M2, h2⟩ => nthLoop f S n fuel M2 h2
    | none => none
  | none => none

section Data

variable (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]

/-- Is `ζ` a primitive `n`-th root of unity? -/
def isPrimRoot (n : ℕ) (ζ : NF M) : Bool :=
  decide (ζ ^ n = 1) && (List.range n).all fun l ↦ l == 0 || decide (ζ ^ l ≠ 1)

/-- The data in `K`: `ζ`, the roots `aᵢ` of `S` and `n`-th roots `bᵢ` of `f(aᵢ)`. -/
noncomputable def fieldData (f S : CPoly ℚ) (n : ℕ) : Option (NF M × List (NF M) × List (NF M)) :=
  match rootsIn M (liftK (K := NF M) (xnMinus n 1)), rootsIn M (liftK (K := NF M) S) with
  | some rz, some ra =>
    match rz.find? (isPrimRoot M n) with
    | some ζ =>
      let as := ra.dedup
      some (ζ, as, as.map fun α ↦
        ((rootsIn M (xnMinus n (evalC (liftK (K := NF M) f) α))).bind List.head?).getD 0)
    | none => none
  | _, _ => none

end Data

/-- **The procedure over a given field** `K = ℚ[θ]/(M)`: find the data in `K`, check it and run
`superFront` with the two-prime torsion oracle. -/
noncomputable def superDecideM (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (f : CPoly ℚ) (n : ℕ)
    (A : List (CPoly ℚ)) (D : CPoly ℚ) (B : ℕ) : Option Bool :=
  match fieldData M f (nbPartK f D) n with
  | none => none
  | some (ζ, as, bs) =>
    let a : Fin as.length → NF M := fun i ↦ as.get i
    let b : Fin as.length → NF M := fun i ↦ bs.getD i 0
    if isPrimRoot M n ζ && decide as.Nodup &&
        (List.finRange as.length).all (fun i ↦
          decide (b i ≠ 0 ∧ b i ^ n = evalC (liftK (K := NF M) f) (a i))) then
      superFront (liftK (K := NF M) f) n ζ
        (torsOracle (nfRedAt (M := M) (M.map Rat.num)) (primesBelow B) B (liftK f) n)
        (A.map (liftK (K := NF M))) (liftK (K := NF M) D) a b
    else none

/-- **The procedure** (`B`: bound for primes and orders; `fuel`: for the field loops): build the
field, then run `superDecideM`. -/
noncomputable def superDecideQ (f : CPoly ℚ) (n : ℕ) (A : List (CPoly ℚ)) (D : CPoly ℚ)
    (B fuel : ℕ) : Option Bool :=
  match buildField f (nbPartK f D) n fuel with
  | none => none
  | some ⟨M, hM⟩ =>
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    superDecideM M f n A D B

/-- **Staged evaluation**: once the field `M` built by `superDecideQ` is known, the procedure is
`superDecideM M` (lets the kernel evaluate the field once, then work over a literal `M`). -/
lemma superDecideQ_eq {f : CPoly ℚ} {n : ℕ} {A : List (CPoly ℚ)} {D : CPoly ℚ} {B fuel : ℕ}
    {M : CPoly ℚ} (hM : Kron.irredQ M = true)
    (h : (buildField f (nbPartK f D) n fuel).map PSigma.fst = some M) :
    superDecideQ f n A D B fuel =
      @superDecideM M ⟨Kron.irredQ_sound M hM⟩ f n A D B := by
  unfold superDecideQ
  rcases e : buildField f (nbPartK f D) n fuel with _ | ⟨M', hM'⟩
  · simp [e] at h
  · simp only [e, Option.map_some, Option.some.injEq] at h
    subst h
    rfl

section Spec

open Differential IntermediateField

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma isPrimRoot_spec {M : CPoly ℚ} [Fact (Irreducible (toPoly M))] {n : ℕ} (hn : 0 < n)
    {ζ : NF M} (h : isPrimRoot M n ζ = true) : IsPrimitiveRoot ζ n := by
  simp only [isPrimRoot, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at h
  refine IsPrimitiveRoot.mk_of_lt ζ hn h.1 fun l hl hln he ↦ ?_
  rcases h.2 l hln with h0 | h1
  · omega
  · exact h1 he

lemma map_liftK_comp {K : Type*} [Field K] [CharZero K] [DecidableEq K] (ι : K →+* Kc) (q : CPoly ℚ) :
    (toPoly (liftK (K := K) q)).map ι = (toPoly q).map (algebraMap ℚ Kc) := by
  rw [toPoly_liftK, Polynomial.map_map]
  congr 1
  exact RingHom.ext_rat _ _

set_option maxHeartbeats 4000000 in
/-- **Correctness of `superDecideM`**: every answer is correct, over any number field. -/
theorem superDecideM_spec [IsAlgClosed Kc] (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]
    (hM : Kron.irredQ M = true) (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (f : CPoly ℚ) {n : ℕ} (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hdeg : (toPoly f).natDegree = f.length - 1) (hpd : 0 < f.length - 1)
    (hcop : Nat.Coprime n (f.length - 1)) (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ) (hD : toPoly D ≠ 0)
    (B : ℕ) (ans : Bool) (h : superDecideM M f n A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  unfold superDecideM at h
  split at h
  · cases h
  rename_i ζ as bs _
  simp only at h
  split_ifs at h with hv
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at hv
  obtain ⟨⟨hζ, hnd⟩, hab⟩ := hv
  let ι : NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NF M) (M := Kc)).toRingHom
  set fK := liftK (K := NF M) f
  have hlen : fK.length = f.length := by simp [fK, liftK]
  have hsqK : Squarefree (toPoly fK) := by
    rw [toPoly_liftK]
    exact ((PerfectField.separable_iff_squarefree.mpr hsq).map).squarefree
  have hdegK : (toPoly fK).natDegree = fK.length - 1 := by
    rw [toPoly_liftK, natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective, hlen, hdeg]
  have hmZ : toPoly M = (toPoly (M.map Rat.num)).map (Int.castRingHom ℚ) :=
    (Kron.polyZ_map M (int_of_irredQ hM)).symm
  have htors := torsOracle_spec (nfRedAt (M := M) (M.map Rat.num))
    (fun p _ R hR ↦ nfRedAt_valid _ hmZ p R hR) (primesBelow B) B hsqK (by rw [hlen]; exact hcop)
  have hyK : y ^ n = aeval x ((toPoly fK).map ι) := by rw [map_liftK_comp]; exact hy
  have hDK : toPoly (liftK (K := NF M) D) ≠ 0 := by
    rw [toPoly_liftK]; exact (Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective).mpr hD
  have hinj : Function.Injective fun i : Fin as.length ↦ as.get i :=
    fun i j hij ↦ (List.Nodup.get_inj_iff hnd).mp hij
  have hspec := superFront_spec hC x y hx ι fK hn hsqK hdegK (by rw [hlen]; exact hpd)
    (by rw [hlen]; exact hcop) hyK hgen (isPrimRoot_spec hn hζ) _ htors
    (A.map (liftK (K := NF M))) (liftK (K := NF M) D) hDK (fun i ↦ as.get i) (fun i ↦ bs.getD i 0)
    hinj (fun i ↦ (hab i).1) (fun i ↦ by rw [← evalC_eq]; exact (hab i).2) ans h
  rw [hspec]
  have hA : ∀ j, (toPoly ((A.map (liftK (K := NF M))).getD j [])).map ι =
      (toPoly (A.getD j [])).map (algebraMap ℚ Kc) := fun j ↦ by
    rw [show ([] : CPoly (NF M)) = liftK (K := NF M) [] from rfl, List.getD_map, map_liftK_comp]
  simp only [hA, map_liftK_comp]

/-- **Correctness of `superDecideQ`**: every answer is correct. -/
theorem superDecideQ_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (f : CPoly ℚ) {n : ℕ} (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hdeg : (toPoly f).natDegree = f.length - 1) (hpd : 0 < f.length - 1)
    (hcop : Nat.Coprime n (f.length - 1)) (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ) (hD : toPoly D ≠ 0)
    (B fuel : ℕ) (ans : Bool) (h : superDecideQ f n A D B fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  unfold superDecideQ at h
  split at h
  · cases h
  rename_i M hM _
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  exact superDecideM_spec M hM hC x y hx f hn hsq hdeg hpd hcop hy hgen A D hD B ans h

end Spec

end Sup
