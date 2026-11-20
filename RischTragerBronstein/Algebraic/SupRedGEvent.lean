import RischTragerBronstein.Algebraic.SupRedGNF

/-!
# The global-certificate torsion oracle eventually answers

`torsOracleG_eventually`: over `K = NF M`, with global base points and a global non-speciality
certificate, the oracle `torsOracleC (nfRedAt mZ) (globalCert …)` run on the primes below `B` with
order bound `B` answers (`some _`) for every large `B`.
-/

open Polynomial CPoly CPoly.Kron

namespace Sup

/-- The primes below `B`. -/
def primesBelow (B : ℕ) : List ℕ := (List.range B).filter Nat.Prime

lemma find?_prefix {α : Type*} {P : α → Bool} {l₁ l₂ : List α} (h : l₁ <+: l₂) {x : α}
    (hx : l₁.find? P = some x) : l₂.find? P = some x := by
  obtain ⟨t, rfl⟩ := h
  rw [List.find?_append, hx]; rfl

lemma primesBelow_prefix {B B' : ℕ} (h : B ≤ B') : primesBelow B <+: primesBelow B' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [primesBelow, primesBelow, List.range_add, List.filter_append]
  exact List.prefix_append _ _

lemma mem_primesBelow {p B : ℕ} (hp : p.Prime) (hB : p < B) : p ∈ primesBelow B := by
  simp [primesBelow, hp, hB]

lemma find?_isSome_of_mem {α : Type*} {P : α → Bool} {l : List α} {x : α} (hx : x ∈ l)
    (hP : P x = true) : (l.find? P).isSome := List.find?_isSome.mpr ⟨x, hx, hP⟩

section Order

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [DecidableEq K]

lemma orderSearchR_isSome (R : RedFns p K) (fK : CPoly K) (n : ℕ) {r : ℕ} (α β : Fin r → K)
    (mq : Fin r → ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hm : prinTestR R fK n α β mq m = true) {bound : ℕ}
    (hb : m ≤ bound) : (orderSearchR R fK n α β mq bound).isSome := by
  unfold orderSearchR
  rw [Option.isSome_map]
  refine find?_isSome_of_mem (x := m - 1) (List.mem_range.mpr (by omega)) ?_
  rw [show m - 1 + 1 = m by omega]; exact hm

end Order

section Main

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

set_option maxHeartbeats 4000000 in
/-- **The global-certificate oracle eventually answers.** -/
theorem torsOracleG_eventually {mZl : List ℤ}
    (hmZ : toPoly M = (toPoly mZl).map (Int.castRingHom ℚ)) (hM1 : 0 < (toPoly mZl).natDegree)
    {fK : CPoly (NFC.NF M)} {n : ℕ} (hn2 : 2 ≤ n) (hd : 0 < fK.length - 1)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hsq : Squarefree (toPoly fK))
    (hcop : Nat.Coprime n (fK.length - 1))
    {ζ : NFC.NF M} (hζn : ζ ^ n = 1) (hζl : ∀ l, 0 < l → l < n → ζ ^ l ≠ 1)
    {xs ys : List (NFC.NF M)} (hgen : (n - 1) * (fK.length - 1 - 1) ≤ 2 * xs.length)
    (hlen : ys.length = xs.length)
    (hE : ∀ i < xs.length, ys.getD i 0 ≠ 0 ∧ ys.getD i 0 ^ n = evalC fK (xs.getD i 0))
    (hxd : ∀ i < xs.length, ∀ j < xs.length, i ≠ j → xs.getD i 0 ≠ xs.getD j 0)
    {lam : List (List (NFC.NF M))}
    (hcert : ∀ i < xs.length, ∀ ai ∈ basisN n (fK.length - 1) (n * xs.length),
      xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2 =
        ∑ i' ∈ Finset.range xs.length, ∑ k ∈ Finset.Ico 1 n, lamK lam n i i' k *
          (xs.getD i' 0 ^ ai.1 * (ζ ^ k * ys.getD i' 0) ^ ai.2))
    {r : ℕ} (α β : Fin r → NFC.NF M) (mq : Fin r → ℕ)
    (hΓ : ∀ q, β q ≠ 0 ∧ β q ^ n = evalC fK (α q) ∧ ∀ x ∈ xs, α q ≠ x)
    (hinj : Function.Injective fun q ↦ (α q, β q)) :
    ∃ B0, ∀ B, B0 ≤ B → (torsOracleC (nfRedAt (M := M) mZl) (globalCert ζ xs ys lam)
      (primesBelow B) B fK n (gammaL α β mq 1)).isSome := by
  classical
  set l := gammaL α β mq 1 with hl
  have hlen' : l.length = r := by simp [hl, gammaL]
  set e : Fin l.length ≃ Fin r := finCongr hlen' with he
  have hget : ∀ q : Fin l.length, l.get q = (α (e q), β (e q), 1 * mq (e q)) := by
    intro q; simp [hl, gammaL, he]; exact ⟨rfl, rfl, rfl⟩
  set α' : Fin l.length → NFC.NF M := fun q ↦ (l.get q).1 with hα'
  set β' : Fin l.length → NFC.NF M := fun q ↦ (l.get q).2.1 with hβ'
  set mu' : Fin l.length → ℕ := fun q ↦ (l.get q).2.2 with hmu'
  have eα : ∀ q, α' q = α (e q) := fun q ↦ by simp only [hα', hget]
  have eβ : ∀ q, β' q = β (e q) := fun q ↦ by simp only [hβ', hget]
  have hΓ' : ∀ q, β' q ≠ 0 ∧ β' q ^ n = evalC fK (α' q) ∧ ∀ x ∈ xs, α' q ≠ x := fun q ↦ by
    rw [eα, eβ]; exact hΓ (e q)
  have hinj' : Function.Injective fun q ↦ (α' q, β' q) := by
    intro i j h
    simp only [eα, eβ] at h
    exact e.injective (hinj h)
  have hn : 0 < n := by omega
  obtain ⟨T0, hT0⟩ := goodPrime_eventually hmZ hn2 hd hlc hsq hζn hζl hgen hlen hE hxd hΓ' hinj'
    hcert
  obtain ⟨p1, hp1T, hp1, s1, hs1, hs1'⟩ := exists_simple_root_prime (M := M) (toPoly mZl) hmZ hM1 T0
  obtain ⟨p2, hp2T, hp2, s2, hs2, hs2'⟩ := exists_simple_root_prime (M := M) (toPoly mZl) hmZ hM1 p1
  have hg1 := hT0 p1 hp1T hp1 ⟨s1, hs1, hs1'⟩
  have hg2 := hT0 p2 (by omega) hp2 ⟨s2, hs2, hs2'⟩
  set good := goodPrime (nfRedAt (M := M) mZl) (globalCert ζ xs ys lam) fK n α' β' with hgood
  set B1 := p2 + 1
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
    (find?_isSome_of_mem (P := good) (mem_primesBelow hp1 (show p1 < B1 by omega)) hg1)
  have hpq : ∃ q', q' ∈ (primesBelow B1).filter (· ≠ p) ∧ good q' = true := by
    by_cases h : p1 = p
    · exact ⟨p2, List.mem_filter.mpr ⟨mem_primesBelow hp2 (by omega), by simp; omega⟩, hg2⟩
    · exact ⟨p1, List.mem_filter.mpr ⟨mem_primesBelow hp1 (by omega), by simpa using h⟩, hg1⟩
  obtain ⟨q', hq'mem, hq'g⟩ := hpq
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (find?_isSome_of_mem (P := good) hq'mem hq'g)
  have hgp := List.find?_some hp
  have hgq := List.find?_some hq
  obtain ⟨hpr, Rp, hRp, gp, xsp, ysp, ζp, lamp, hcp⟩ := goodPrime_spec _ _ hgp
  obtain ⟨hqr, Rq, hRq, gq, xsq, ysq, ζq, lamq, hcq⟩ := goodPrime_spec _ _ hgq
  haveI : Fact p.Prime := ⟨hpr⟩
  haveI : Fact q.Prime := ⟨hqr⟩
  obtain ⟨φp, hφp⟩ := nfRedAt_valid mZl hmZ p Rp hRp
  obtain ⟨φq, hφq⟩ := nfRedAt_valid mZl hmZ q Rq hRq
  obtain ⟨mp, hmp1, hmp⟩ := exists_orderR Rp φp hφp mu' hcp hcop
  obtain ⟨mq', hmq1, hmq⟩ := exists_orderR Rq φq hφq mu' hcq hcop
  refine ⟨max B1 (max mp mq'), fun B hB ↦ ?_⟩
  have hB1 : B1 ≤ B := le_trans (le_max_left _ _) hB
  have hpB := find?_prefix (primesBelow_prefix hB1) hp
  have hqB := find?_prefix ((primesBelow_prefix hB1).filter _) hq
  show (torsOracleC (nfRedAt (M := M) mZl) (globalCert ζ xs ys lam) (primesBelow B) B fK n l).isSome
  unfold torsOracleC
  simp only []
  rw [hgood] at hpB hqB
  rw [show (fun q ↦ (l.get q).1) = α' from rfl, show (fun q ↦ (l.get q).2.1) = β' from rfl, hpB]
  dsimp only
  rw [hqB]
  dsimp only
  unfold torsWith
  rw [dif_pos hpr, dif_pos hqr]
  simp only [hRp, hRq]
  unfold torsDecideR
  obtain ⟨op, hop⟩ := Option.isSome_iff_exists.mp
    (orderSearchR_isSome Rp fK n α' β' mu' hmp1 hmp (bound := B) (by omega))
  obtain ⟨oq, hoq⟩ := Option.isSome_iff_exists.mp
    (orderSearchR_isSome Rq fK n α' β' mu' hmq1 hmq (bound := B) (by omega))
  rw [hop, hoq]
  simp only []
  split_ifs <;> rfl

end Main

end Sup
