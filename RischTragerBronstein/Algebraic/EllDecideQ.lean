import RischTragerBronstein.Algebraic.NFSplit
import RischTragerBronstein.Algebraic.GoodPrime

/-!
# The automatic decision for `∫ A dx / (D √p)` over `ℚ`

`ellDecideQ a b c A D B`:
1. builds a number field `K = ℚ[x]/(M)` over which `D` splits and `p` is a non-zero square at every
   root of `D` (`splitField`: Trager's primitive elements and norms);
2. searches a prime `p₀ < B` of good reduction at which `M` has a simple root modulo `p₀`
   (`goodPrimeB`; such primes exist by Schur's theorem, `exists_good_prime`);
3. runs `ellDecideNF` over `K` with the torsion bound at `p₀`.

`ellDecideQ_spec`: every answer is correct (constants algebraically closed).
`ellDecideQ_complete`: for `D` squarefree and coprime to `p`, every large enough search bound
gives an answer.
-/

open Polynomial Differential

namespace EllQuad

open CPoly EllDV NFC

/-- `F` reduced modulo `p`. -/
def modP (p : ℕ) (F : CPoly ℚ) : CPoly (ZMod p) := F.map fun q ↦ ((q.num : ℤ) : ZMod p)

/-- The computable test for a good auxiliary prime. -/
def goodPrimeB (F : CPoly ℚ) (a b c : ℤ) (p : ℕ) : Bool :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    decide (p ≠ 2) && decide (EllDV.goodRedMod p a b c) &&
      decide (∃ s : ZMod p, Kron.evalC (modP p F) s = 0 ∧
        Kron.evalC (CPoly.deriv (modP p F)) s ≠ 0)
  else false

lemma toPoly_modP (p : ℕ) (F : CPoly ℚ) :
    toPoly (modP p F) = (Kron.polyZ F).map (Int.castRingHom (ZMod p)) := by
  rw [Kron.polyZ, ← toPoly_map', modP, List.map_map]; rfl

lemma goodPrimeB_iff (F : CPoly ℚ) (a b c : ℤ) (p : ℕ) :
    goodPrimeB F a b c p = true ↔ Schur.GoodPrime (Kron.polyZ F) a b c p := by
  unfold goodPrimeB Schur.GoodPrime
  by_cases hp : p.Prime
  · rw [dif_pos hp]
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Kron.evalC_eq, toPoly_deriv, toPoly_modP,
      derivative_map]
    tauto
  · rw [dif_neg hp]; simp [hp]


/-- **The procedure** (`B`: the bound for the auxiliary prime). -/
noncomputable def ellDecideQ (a b c : ℤ) (A D : CPoly ℚ) (B : ℕ) : Option Bool :=
  match splitField a b c D with
  | none => none
  | some ⟨M, hM⟩ =>
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    match (List.range B).find? (goodPrimeB M a b c) with
    | none => none
    | some p0 =>
      if hp : p0 ≠ 0 then
        haveI : NeZero p0 := ⟨hp⟩
        ellDecideNF M a b c A D (redCount p0 a b c + 1)
      else none

lemma int_of_irredQ {M : CPoly ℚ} (hM : Kron.irredQ M = true) : ∀ q ∈ M, q.den = 1 := by
  simp only [Kron.irredQ, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hM
  exact fun q hq ↦ by simpa using hM.1.1.1 q hq

instance nf_isAlgebraic (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] :
    Algebra.IsAlgebraic ℚ (NF M) := by
  haveI : Module.Finite ℚ (AdjoinRoot (toPoly M)) :=
    (AdjoinRoot.powerBasis (f_ne_zero M)).finite
  exact ⟨fun x ↦ (isAlgebraic_algHom_iff (toARHom M).toRatAlgHom (toAR_injective M)).mp
    (Algebra.IsAlgebraic.isAlgebraic _)⟩

lemma split_of_hasRoots {K : Type*} [Field K] {P : K[X]} (hP : P ≠ 0) {l : List K} (hl : l.Nodup)
    (hlen : P.natDegree ≤ l.length) (hr : ∀ a ∈ l, P.eval a = 0) :
    P = C P.leadingCoeff * (l.map fun r ↦ X - C r).prod := by
  have hle : (l : Multiset K) ≤ P.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hl)]
    intro a ha; exact (mem_roots hP).mpr (hr a ha)
  have heq : (l : Multiset K) = P.roots := Multiset.eq_of_le_of_card_le hle (by
    simpa using (card_roots' P).trans hlen)
  have hcard : Multiset.card P.roots = P.natDegree := by
    rw [← heq]; simp only [Multiset.coe_card]
    exact le_antisymm (by rw [← Multiset.coe_card, heq]; exact card_roots' P) hlen
  have := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [← heq] at this
  simpa [Multiset.map_coe, Multiset.prod_coe] using this.symm

section Spec

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `ellDecideQ`** (algebraically closed constants). -/
theorem ellDecideQ_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (B : ℕ) (ans : Bool) (h : ellDecideQ a b c A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold ellDecideQ at h
  split at h
  · cases h
  rename_i M hM hsplit
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  split at h
  · cases h
  rename_i p0 hfind
  split_ifs at h with hp0
  haveI : NeZero p0 := ⟨hp0⟩
  have hgood := (goodPrimeB_iff M a b c p0).mp (List.find?_some hfind)
  obtain ⟨hprime, hp2, hred, s, hs, hs'⟩ := hgood
  haveI : Fact p0.Prime := ⟨hprime⟩
  obtain ⟨φ⟩ := exists_embedNF M (Kron.polyZ M) (Kron.polyZ_map M (int_of_irredQ hM)).symm s hs hs'
  let ι : NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NF M) (M := Kc)).toRingHom
  exact ellDecideNF_spec M hC hCall x y hx a b c hsq hy hgen ι A D p0 hp2 hred φ _
    (by rw [Fintype.card_option, card_RedPts]) ans h

end Spec

/-- **Completeness of `ellDecideQ`**: for `D` squarefree and coprime to `p`, every large enough
search bound gives an answer. -/
theorem ellDecideQ_complete (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hDsq : Squarefree (toPoly D))
    (hcop : IsCoprime (toPoly D) (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ))) :
    ∃ B0, ∀ B, B0 ≤ B → ellDecideQ a b c A D B ≠ none := by
  classical
  obtain ⟨M, hM, hsf, hroots, hpt⟩ := splitField_spec a b c D hDsq hcop
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  have hZ := Kron.polyZ_map M (int_of_irredQ hM)
  have hdegZ : 0 < (Kron.polyZ M).natDegree := by
    rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)), hZ]
    exact Nat.pos_of_ne_zero fun h ↦ (Kron.irredQ_sound M hM).not_isUnit
      (isUnit_iff_degree_eq_zero.mpr (by rw [degree_eq_natDegree (f_ne_zero M), h]; rfl))
  obtain ⟨p, hp⟩ := Schur.exists_good_prime (Kron.polyZ M) hdegZ
    (by rw [hZ]; exact (Kron.irredQ_sound M hM).separable) a b c hsq
  refine ⟨p + 1, fun B hB ↦ ?_⟩
  have hpB : (goodPrimeB M a b c p) = true := (goodPrimeB_iff M a b c p).mpr hp
  obtain ⟨p0, hp0⟩ : ∃ p0, (List.range B).find? (goodPrimeB M a b c) = some p0 := by
    apply Option.isSome_iff_exists.mp
    rw [List.find?_isSome]
    exact ⟨p, List.mem_range.mpr (by omega), hpB⟩
  have hgood0 := (goodPrimeB_iff M a b c p0).mp (List.find?_some hp0)
  have hp00 : p0 ≠ 0 := hgood0.1.ne_zero
  -- the splitting data
  obtain ⟨l, hl, hlen, hr⟩ := hroots
  have hDK0 : (toPoly D).map (algebraMap ℚ (NF M)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective).mpr hDsq.ne_zero
  have hsplitK := split_of_hasRoots hDK0 hl
    (by rw [natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective]; exact hlen)
    (fun a ha ↦ by rw [eval_map_algebraMap]; exact hr a ha)
  unfold ellDecideQ
  rw [hsf]
  simp only
  rw [hp0]
  simp only
  rw [dif_pos hp00]
  haveI : NeZero p0 := ⟨hp00⟩
  exact ellDecideNF_ne_none M a b c hsq A D hDsq _ l hsplitK
    (fun α hα ↦ by obtain ⟨β, hβ0, hβ⟩ := hpt α hα; exact ⟨β, hβ0, by simpa [pVal] using hβ⟩) _

end EllQuad
