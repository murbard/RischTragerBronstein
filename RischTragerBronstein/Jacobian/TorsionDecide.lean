import RischTragerBronstein.Jacobian.NonElemCheck
import RischTragerBronstein.Jacobian.PicFinite
import RischTragerBronstein.Jacobian.Cantor

/-!
# Deciding torsion in hyperelliptic Jacobians over `ℚ`

For `y² = f(x)`, `f ∈ ℤ[x]` of degree `2g + 1`, and a divisor `Γ` on integral non-branch points,
let `p ≠ q` be good primes (`goodPrime`: `baseCheck` and `f` squarefree modulo `p`). Then

* `orderMod p …`: the order of `Γ̄` in the Jacobian over `𝔽_p`, computed by `Nat.find` over the
  computable test `principalC` — it exists because `Pic⁰(𝔽_p)` is finite (`exists_principalMul`);
* `torsionDecide`: one more `principalC` test over `ℚ`, at `orderMod p · orderMod q`;
* `torsionDecide_iff`: `torsionDecide = true ↔ ∃ n ≥ 1, n Γ principal` (`torsion_iff_two_primes`).
-/

open Polynomial CPoly CPoly.Kron

namespace Jac

/-- Principality of `n Γ` is exactly the success of `principalC` with the pole bounds. -/
lemma principalMul_iff_principalC {K : Type*} [Field K] [DecidableEq K] (f : CPoly K) (g : ℕ)
    (Γ : EDiv K)
    (hΓ : ∀ n, ∀ q ∈ escale n Γ, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = (toPoly f).eval q.1) (n : ℕ) :
    PrincipalMul (toPoly f) g Γ n ↔
      (principalC f (escale n Γ) (boundA (n * edeg Γ)) (boundB g (n * edeg Γ))).isSome := by
  constructor
  · rintro ⟨ψ, h0, hpl, hv⟩
    obtain ⟨hA, hB⟩ := degree_lt_of_poleLE hpl
    have := principalC_complete (RingHom.id K) f _ _ _ (hΓ n) ψ h0 hA hB
      (by rwa [Polynomial.map_id, emap_id])
    exact Option.isSome_iff_ne_none.mpr this
  · intro h
    obtain ⟨⟨j, cs⟩, hjc⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨ψ, h0, hA, hB, hv⟩ := principalC_sound f _ _ _ (hΓ n) hjc
    refine ⟨ψ, h0, ⟨?_, ?_⟩, hv⟩
    · have : ψ.1.natDegree < boundA (n * edeg Γ) := by
        by_cases h1 : ψ.1 = 0
        · rw [h1, natDegree_zero]; unfold boundA; omega
        · exact (natDegree_lt_iff_degree_lt h1).mpr hA
      unfold boundA at this; omega
    · by_cases h2 : ψ.2 = 0
      · exact Or.inl h2
      · right
        have := (natDegree_lt_iff_degree_lt h2).mpr hB
        unfold boundB at this; omega

/-- A good prime for the torsion decision. -/
abbrev goodPrime (p : ℕ) [Fact p.Prime] (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (xs ys : List ℤ) :
    Prop :=
  baseCheck p f g Γ xs ys ∧ squarefreeCheck (castL p f) = true

section Order

variable {p : ℕ} [hp : Fact p.Prime] {f : List ℤ} {g : ℕ} {Γ : EDiv ℤ} {xs ys : List ℤ}

lemma two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

lemma exists_order_mod (hg : goodPrime p f g Γ xs ys) :
    ∃ m, 1 ≤ m ∧ (principalC (castL p f) (escale m (emap (Int.castRingHom (ZMod p)) Γ))
      (boundA (m * edeg Γ)) (boundB g (m * edeg Γ))).isSome := by
  have B := baseCheck_spec hg.1
  obtain ⟨m, hm1, hm⟩ := exists_principalMul (two_ne_zero_zmod B.hp2) B.hdegZ
    (squarefreeCheck_sound hg.2) B.honZ B.hndZ
  refine ⟨m, hm1, ?_⟩
  have := (principalMul_iff_principalC (castL p f) g _ B.hΓp m).mp hm
  rwa [edeg_emap] at this

/-- The test "`m Γ̄` is principal" over `𝔽_p`. -/
def prinTest (p : ℕ) [Fact p.Prime] (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (m : ℕ) : Bool :=
  (principalC (castL p f) (escale m (emap (Int.castRingHom (ZMod p)) Γ))
    (boundA (m * edeg Γ)) (boundB g (m * edeg Γ))).isSome

/-- An order proposed by Cantor's algorithm (untrusted). -/
def orderCand (p : ℕ) [Fact p.Prime] (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) : Option ℕ :=
  Cantor.orderJ (castL p f) g (Cantor.classOf (castL p f) g (emap (Int.castRingHom (ZMod p)) Γ))
    ((4 * p) ^ g + 10)

/-- Verification of an exact order: `m Γ̄` principal, `(m/r) Γ̄` not for divisors `r ≥ 2`. -/
def orderOk (p : ℕ) [Fact p.Prime] (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (m : ℕ) : Bool :=
  decide (1 ≤ m) && prinTest p f g Γ m &&
    (List.range (m + 1)).all fun r ↦ !decide (2 ≤ r ∧ r ∣ m) || !prinTest p f g Γ (m / r)

/-- **The order of `Γ̄` in the Jacobian over `𝔽_p`**: Cantor's candidate if it verifies,
otherwise the least `m` found by `Nat.find`. -/
def orderMod (p : ℕ) [Fact p.Prime] (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (xs ys : List ℤ)
    (hg : goodPrime p f g Γ xs ys) : ℕ :=
  match orderCand p f g Γ with
  | some m => if orderOk p f g Γ m then m else Nat.find (exists_order_mod hg)
  | none => Nat.find (exists_order_mod hg)

/-- The order facts over `𝔽_p`. -/
lemma orderMod_zmod (hg : goodPrime p f g Γ xs ys) :
    1 ≤ orderMod p f g Γ xs ys hg ∧
    PrincipalMul (toPoly (castL p f)) g (emap (Int.castRingHom (ZMod p)) Γ)
      (orderMod p f g Γ xs ys hg) ∧
    ∀ m', 1 ≤ m' → m' < orderMod p f g Γ xs ys hg →
      ¬ PrincipalMul (toPoly (castL p f)) g (emap (Int.castRingHom (ZMod p)) Γ) m' := by
  have B := baseCheck_spec hg.1
  have hiff : ∀ m, PrincipalMul (toPoly (castL p f)) g (emap (Int.castRingHom (ZMod p)) Γ) m ↔
      prinTest p f g Γ m = true := fun m ↦ by
    rw [principalMul_iff_principalC (castL p f) g _ B.hΓp m, edeg_emap]; rfl
  have hfind : 1 ≤ Nat.find (exists_order_mod hg) ∧
      PrincipalMul (toPoly (castL p f)) g (emap (Int.castRingHom (ZMod p)) Γ)
        (Nat.find (exists_order_mod hg)) ∧
      ∀ m', 1 ≤ m' → m' < Nat.find (exists_order_mod hg) →
        ¬ PrincipalMul (toPoly (castL p f)) g (emap (Int.castRingHom (ZMod p)) Γ) m' := by
    obtain ⟨h1, h2⟩ := Nat.find_spec (exists_order_mod hg)
    refine ⟨h1, (hiff _).mpr h2, fun m' hm1 hm2 hP ↦ ?_⟩
    exact Nat.find_min (exists_order_mod hg) hm2 ⟨hm1, (hiff m').mp hP⟩
  unfold orderMod
  split
  · rename_i m _
    split_ifs with hok
    · simp only [orderOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hok
      obtain ⟨⟨hm1, hm⟩, hdiv⟩ := hok
      have hP := (hiff m).mpr hm
      refine ⟨hm1, hP, exact_order B.hdegZ B.honZ B.hndZ hP fun r hr hrd hP' ↦ ?_⟩
      rcases hdiv r (Nat.lt_succ_of_le (Nat.le_of_dvd hm1 hrd)) with h | h
      · exact h ⟨hr.two_le, hrd⟩
      · rw [(hiff _).mp hP'] at h; exact Bool.noConfusion h
    · exact hfind
  · exact hfind

lemma orderMod_spec (hg : goodPrime p f g Γ xs ys) :
    1 ≤ orderMod p f g Γ xs ys hg ∧
    PrincipalMul (((toPoly f).map (Int.castRingHom ℤ_[p])).map (IsLocalRing.residue ℤ_[p])) g
      (emap (IsLocalRing.residue ℤ_[p]) (emap (Int.castRingHom ℤ_[p]) Γ))
      (orderMod p f g Γ xs ys hg) := by
  have B := baseCheck_spec hg.1
  obtain ⟨h1, h2, -⟩ := orderMod_zmod hg
  refine ⟨h1, ?_⟩
  apply principal_residue_of_zmod
  rw [B.ef, B.eΓ]
  exact h2

lemma orderMod_min (hg : goodPrime p f g Γ xs ys) :
    ∀ m', 1 ≤ m' → m' < orderMod p f g Γ xs ys hg →
      ¬ PrincipalMul (((toPoly f).map (Int.castRingHom ℤ_[p])).map (IsLocalRing.residue ℤ_[p])) g
        (emap (IsLocalRing.residue ℤ_[p]) (emap (Int.castRingHom ℤ_[p]) Γ)) m' := by
  have B := baseCheck_spec hg.1
  intro m' h1 h2 hP
  have hP' := principal_zmod_of_residue _ _ hP
  rw [B.ef, B.eΓ] at hP'
  exact (orderMod_zmod hg).2.2 m' h1 h2 hP'

end Order

lemma findWitness_spec {p q mp mq : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : (findWitness p q mp mq).isSome) :
    ∀ c d, mp * p ^ c ≠ mq * q ^ d := by
  obtain ⟨rk, hrk⟩ := Option.isSome_iff_exists.mp h
  have hp := List.find?_some hrk
  simp only [decide_eq_true_eq] at hp
  obtain ⟨hr, h1 | h2⟩ := hp
  · exact ne_of_prime_pow_left (p := p) (q := q) hq hr h1.1 h1.2.1 h1.2.2
  · exact ne_of_prime_pow_right hp hr h2.1 h2.2.1 h2.2.2

/-- **The torsion decision.** -/
def torsionDecide (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (xp yp xq yq : List ℤ) (hp : goodPrime p f g Γ xp yp) (hq : goodPrime q f g Γ xq yq) :
    Bool :=
  let mp := orderMod p f g Γ xp yp hp
  let mq := orderMod q f g Γ xq yq hq
  if (findWitness p q mp mq).isSome then false
  else
    (principalC (f.map (Int.castRingHom ℚ)) (escale (mp * mq) (emap (Int.castRingHom ℚ) Γ))
      (boundA (mp * mq * edeg Γ)) (boundB g (mp * mq * edeg Γ))).isSome

/-- **Soundness and completeness of `torsionDecide`.** -/
theorem torsionDecide_iff {f : List ℤ} {g : ℕ} {Γ : EDiv ℤ} {p q : ℕ} [hp : Fact p.Prime]
    [hq : Fact q.Prime] (hpq : p ≠ q) {xp yp xq yq : List ℤ} (hgp : goodPrime p f g Γ xp yp)
    (hgq : goodPrime q f g Γ xq yq) :
    torsionDecide f g Γ p q xp yp xq yq hgp hgq = true ↔
      ∃ n, 1 ≤ n ∧ PrincipalMul ((toPoly f).map (Int.castRingHom ℚ)) g
        (emap (Int.castRingHom ℚ) Γ) n := by
  have Bp := baseCheck_spec hgp.1
  have Bq := baseCheck_spec hgq.1
  obtain ⟨hp2, hdp, hlcp, ⟨xp', yp', hyup, hyfp, hxp, hΓEp⟩, honp, hΓxp, hΓZ, hΓne, -, -, -, -,
    -, -⟩ := Bp
  obtain ⟨hq2, hdq, hlcq, ⟨xq', yq', hyuq, hyfq, hxq, hΓEq⟩, honq, hΓxq, -, -, -, -, -, -, -,
    -⟩ := Bq
  obtain ⟨hmp1, hmp⟩ := orderMod_spec hgp
  obtain ⟨hmq1, hmq⟩ := orderMod_spec hgq
  have hfK : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1 := by
    rw [natDegree_map_eq_of_injective (RingHom.injective_int _), ← hdp,
      natDegree_map_eq_of_injective (RingHom.injective_int _)]
  have hmapf : ∀ (s : ℕ) [Fact s.Prime],
      ((toPoly f).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[s]) =
        ((toPoly f).map (Int.castRingHom ℤ_[s])).map (algebraMap ℤ_[s] ℚ_[s]) := by
    intro s _
    rw [Polynomial.map_map, Polynomial.map_map]; congr 1
  have hmapΓ : ∀ (s : ℕ) [Fact s.Prime],
      emap (algebraMap ℚ ℚ_[s]) (emap (Int.castRingHom ℚ) Γ) =
        emap (algebraMap ℤ_[s] ℚ_[s]) (emap (Int.castRingHom ℤ_[s]) Γ) := by
    intro s _
    rw [emap_emap, emap_emap]; congr 1
  have hΓK : ∀ t ∈ emap (Int.castRingHom ℚ) Γ, 2 * t.2.1 ≠ 0 ∧
      t.2.1 ^ 2 = ((toPoly f).map (Int.castRingHom ℚ)).eval t.1 := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    obtain ⟨h1, h2⟩ := hΓZ t' ht'
    refine ⟨?_, ?_⟩
    · show (2 : ℚ) * ((t'.2.1 : ℤ) : ℚ) ≠ 0
      exact_mod_cast h1
    · show ((t'.2.1 : ℤ) : ℚ) ^ 2 = ((toPoly f).map (Int.castRingHom ℚ)).eval
        (Int.castRingHom ℚ t'.1)
      rw [eval_map, eval₂_at_apply, ← h2]; simp
  have hΓnd : ((emap (Int.castRingHom ℚ) Γ).map Prod.fst).Nodup := by
    simp only [emap, List.map_map, List.Nodup]
    rw [List.pairwise_map]
    exact hΓne.imp fun h he ↦ h (by simpa using he)
  unfold torsionDecide
  dsimp only
  split_ifs with hw
  · simp only [false_iff]
    rintro ⟨n, hn1, hn⟩
    exact not_torsion_of_orders hp2 hq2 (algebraMap ℚ ℚ_[p]) (algebraMap ℚ ℚ_[q]) _ hfK _ hΓK
      hΓnd _ hdp hlcp (hmapf p) xp' yp' hyup hyfp hxp _ (hmapΓ p) honp hΓxp hΓEp _ hmp1 hmp
      (orderMod_min hgp) _ hdq hlcq (hmapf q) xq' yq' hyuq hyfq hxq _ (hmapΓ q) honq hΓxq hΓEq
      _ hmq1 hmq (orderMod_min hgq) (findWitness_spec hp.out hq.out hw) n hn1 hn
  rw [torsion_iff_two_primes hp2 hq2 hpq (algebraMap ℚ ℚ_[p]) (algebraMap ℚ ℚ_[q]) _ hfK _ hΓK
    hΓnd _ hdp hlcp (hmapf p) xp' yp' hyup hyfp hxp _ (hmapΓ p) honp hΓxp hΓEp _ hmp1 hmp
    _ hdq hlcq (hmapf q) xq' yq' hyuq hyfq hxq _ (hmapΓ q) honq hΓxq hΓEq _ hmq1 hmq]
  have hΓQ : ∀ n, ∀ t ∈ escale n (emap (Int.castRingHom ℚ) Γ), 2 * t.2.1 ≠ 0 ∧
      t.2.1 ^ 2 = (toPoly (f.map (Int.castRingHom ℚ))).eval t.1 := by
    intro n t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    rw [toPoly_map_list]
    exact hΓK t' ht'
  have := principalMul_iff_principalC (f.map (Int.castRingHom ℚ)) g _ hΓQ
    (orderMod p f g Γ xp yp hgp * orderMod q f g Γ xq yq hgq)
  rw [toPoly_map_list, edeg_emap] at this
  rw [this]

end Jac
