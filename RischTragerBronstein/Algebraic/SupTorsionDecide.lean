import RischTragerBronstein.Algebraic.SupCheck
import RischTragerBronstein.Jacobian.NonElemCheck

/-!
# Deciding torsion in superelliptic Jacobians over `ℚ`

For `yⁿ = f(x)`, `f ∈ ℤ[x]`, and a divisor `Γ = ∑ m_q (α_q, β_q)` on integral non-branch points,
let `p ≠ q` be good primes (`supBaseCheck`). Then

* `orderModN`: the order of `Γ̄` modulo `p`, by `Nat.find` over the computable test `supPrincipalC`
  (it exists: `Pic⁰(𝔽_p)` is finite, `exists_principalMulN`);
* `torsionDecideN`: one `supPrincipalC` test over `ℚ` at `orderModN p · orderModN q`;
* `torsionDecideN_iff`: `torsionDecideN = true ↔ ∃ N ≥ 1, N Γ principal`
  (`torsion_iff_two_primes_N`).
-/

open Polynomial

namespace Sup

/-- The divisor `s Γ` as a list, for `supPrincipalC`. -/
def gammaL {F : Type*} {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ) (s : ℕ) :
    List (F × F × ℕ) :=
  List.ofFn fun q ↦ (α q, β q, s * mq q)

/-- Principality of `s Γ` is exactly the success of the linear-algebra test. -/
theorem principalMulN_iff_test {F : Type*} [Field F] [DecidableEq F] (fC : CPoly F) {n : ℕ}
    (hn : 0 < n) (d : ℕ) {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ)
    (hΓ : ∀ q, (n : F) * β q ^ (n - 1) ≠ 0 ∧ β q ^ n = (CPoly.toPoly fC).eval (α q)) (s : ℕ) :
    PrincipalMulN (CPoly.toPoly fC) n d α β mq s ↔
      (supPrincipalC fC n d (gammaL α β mq s) (s * ∑ q, mq q)).isSome := by
  have hΓ' : ∀ P ∈ gammaL α β mq s, (n : F) * P.2.1 ^ (n - 1) ≠ 0 ∧
      P.2.1 ^ n = (CPoly.toPoly fC).eval P.1 := by
    intro P hP
    obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hP
    exact hΓ q
  constructor
  · rintro ⟨W, hW0, hWs, hWv⟩
    refine Option.isSome_iff_ne_none.mpr (supPrincipalC_complete (RingHom.id F) fC n hn d _ _ hΓ'
      W hW0 hWs fun P hP ↦ ?_)
    obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hP
    simpa using hWv q
  · intro h
    obtain ⟨⟨j, cs⟩, hjc⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨W, hW0, hWs, hWv⟩ := supPrincipalC_sound fC n hn d _ _ hΓ' hjc
    exact ⟨W, hW0, hWs, fun q ↦ hWv _ (List.mem_ofFn.mpr ⟨q, rfl⟩)⟩

section Order

variable {p : ℕ} [hp : Fact p.Prime] {f : List ℤ} {n g r : ℕ} {α β : Fin r → ℤ} {mq : Fin r → ℕ}
  {xs ys : List ℤ} {ζ0 : ℤ} {lam : List (List ℤ)}

/-- The test "`m Γ̄` is principal" over `𝔽_p`. -/
def prinTestN (p : ℕ) [Fact p.Prime] (f : List ℤ) (n : ℕ) {r : ℕ} (α β : Fin r → ℤ)
    (mq : Fin r → ℕ) (m : ℕ) : Bool :=
  (supPrincipalC (Jac.castL p f) n (f.length - 1)
    (gammaL (fun q ↦ (α q : ZMod p)) (fun q ↦ (β q : ZMod p)) mq m) (m * ∑ q, mq q)).isSome

/-- The facts modulo `p` behind `supBaseCheck`. -/
lemma zmod_facts (hg : supBaseCheck p f n g α β xs ys ζ0 lam) :
    (CPoly.toPoly (Jac.castL p f)).natDegree = f.length - 1 ∧
    Squarefree (CPoly.toPoly (Jac.castL p f)) ∧ ((n : ℕ) : ZMod p) ≠ 0 ∧
    Function.Injective (fun q ↦ ((α q : ZMod p), (β q : ZMod p))) ∧ (∀ q, (β q : ZMod p) ≠ 0) ∧
    (∀ q, (β q : ZMod p) ^ n = (CPoly.toPoly (Jac.castL p f)).eval (α q : ZMod p)) := by
  obtain ⟨hn2, hpn, hd, hlc, -, hsq, -, -, -, -, -, -, hΓ, hΓd, hΓβ, -⟩ := hg
  have hcoef : ∀ m, (CPoly.toPoly (Jac.castL p f)).coeff m = ((f.getD m 0 : ℤ) : ZMod p) := by
    intro m; rw [Jac.castL_eq, coeff_map, CPoly.coeff_toPoly]; rfl
  have hlc0 : (CPoly.toPoly (Jac.castL p f)).coeff (f.length - 1) ≠ 0 := by
    rw [hcoef, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hlc
  refine ⟨?_, CPoly.squarefreeCheck_sound hsq, ?_, ?_, ?_, ?_⟩
  · refine le_antisymm ?_ (le_natDegree_of_ne_zero hlc0)
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have hm' : f.length - 1 < m := by exact_mod_cast hm
    rw [hcoef, List.getD_eq_default _ _ (by omega), Int.cast_zero]
  · intro h0
    apply hpn
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h0
  · intro q q' h
    have h1 : ((α q : ℤ) : ZMod p) = (α q' : ℤ) := congrArg Prod.fst h
    have h2 : ((β q : ℤ) : ZMod p) = (β q' : ℤ) := congrArg Prod.snd h
    have hαe : α q = α q' := by
      rcases hΓd q q' with h' | h'
      · exact h'
      · exact absurd (by rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact sub_eq_zero.mpr h1) h'
    by_contra hne
    exact hΓβ q q' hne hαe (by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact sub_eq_zero.mpr h2)
  · intro q h0
    exact (hΓ q).1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0)
  · intro q
    rw [Jac.castL_eq, eval_map, show (α q : ZMod p) = Int.castRingHom (ZMod p) (α q) from rfl,
      eval₂_at_apply, ← CPoly.Kron.evalC_eq, ← (hΓ q).2.1, map_pow]
    rfl

lemma exists_orderN (hg : supBaseCheck p f n g α β xs ys ζ0 lam)
    (hcop : Nat.Coprime n (f.length - 1)) : ∃ m, 1 ≤ m ∧ prinTestN p f n α β mq m = true := by
  obtain ⟨hdeg, hsq, hnk, hαk, hβk, hβf⟩ := zmod_facts hg
  have hn2 : 2 ≤ n := hg.1
  have hn : 0 < n := by omega
  obtain ⟨m, hm1, hm⟩ := exists_principalMulN (CPoly.toPoly (Jac.castL p f)) hn hsq
    (by rw [hdeg]; exact hg.2.2.1) (by rw [hdeg]; exact hcop) hnk _ _ mq hn2 hαk hβk hβf
  refine ⟨m, hm1, ?_⟩
  rw [hdeg] at hm
  exact (principalMulN_iff_test (Jac.castL p f) hn _ _ _ mq
    (fun q ↦ ⟨mul_ne_zero hnk (pow_ne_zero _ (hβk q)), hβf q⟩) m).mp hm

/-- **The order of `Γ̄` modulo `p`.** -/
def orderModN (hg : supBaseCheck p f n g α β xs ys ζ0 lam)
    (hcop : Nat.Coprime n (f.length - 1)) : ℕ :=
  Nat.find (exists_orderN (mq := mq) hg hcop)

lemma orderModN_spec (hg : supBaseCheck p f n g α β xs ys ζ0 lam)
    (hcop : Nat.Coprime n (f.length - 1))
    (D : SupGoodData p (algebraMap ℚ ℚ_[p]) ((CPoly.toPoly f).map (Int.castRingHom ℚ)) n
      (fun q ↦ (α q : ℚ)) (fun q ↦ (β q : ℚ)))
    (hDf : D.f = (CPoly.toPoly f).map (Int.castRingHom ℤ_[p]))
    (hDα : D.α = fun q ↦ ((α q : ℤ) : ℤ_[p])) (hDβ : D.β = fun q ↦ ((β q : ℤ) : ℤ_[p])) :
    1 ≤ orderModN (mq := mq) hg hcop ∧
    PrincipalMulN (D.f.map (IsLocalRing.residue ℤ_[p])) n (f.length - 1)
      (fun i ↦ IsLocalRing.residue ℤ_[p] (D.α i)) (fun i ↦ IsLocalRing.residue ℤ_[p] (D.β i)) mq
      (orderModN (mq := mq) hg hcop) := by
  obtain ⟨hdeg, hsq, hnk, hαk, hβk, hβf⟩ := zmod_facts hg
  obtain ⟨h1, h2⟩ := Nat.find_spec (exists_orderN (mq := mq) hg hcop)
  refine ⟨h1, ?_⟩
  have hP := (principalMulN_iff_test (Jac.castL p f) (by have := hg.1; omega) _ _ _ mq
    (fun q ↦ ⟨mul_ne_zero hnk (pow_ne_zero _ (hβk q)), hβf q⟩) _).mpr h2
  have hP' := hP.map (PadicInt.residueField (p := p)).symm.toRingHom
  have e1 : (CPoly.toPoly (Jac.castL p f)).map (PadicInt.residueField (p := p)).symm.toRingHom =
      D.f.map (IsLocalRing.residue ℤ_[p]) := by
    rw [hDf, Jac.castL_eq, Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have e2 : ∀ z : ℤ, (PadicInt.residueField (p := p)).symm.toRingHom (z : ZMod p) =
      IsLocalRing.residue ℤ_[p] (z : ℤ_[p]) := fun z ↦ by simp
  rw [e1] at hP'
  rw [hDα, hDβ]
  simp only [e2] at hP'
  exact hP'

end Order

/-- **The torsion decision** for `Γ` on `yⁿ = f(x)` over `ℚ`, given two good primes. -/
def torsionDecideN (f : List ℤ) (n : ℕ) {r : ℕ} (α β : Fin r → ℤ) (mq : Fin r → ℕ)
    (hcop : Nat.Coprime n (f.length - 1)) (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    {g g' : ℕ} {xs ys xs' ys' : List ℤ} {ζp ζq : ℤ} {lp lq : List (List ℤ)}
    (hp : supBaseCheck p f n g α β xs ys ζp lp) (hq : supBaseCheck q f n g' α β xs' ys' ζq lq) :
    Bool :=
  let mp := orderModN (mq := mq) hp hcop
  let mq' := orderModN (mq := mq) hq hcop
  (supPrincipalC (f.map (Int.castRingHom ℚ)) n (f.length - 1)
    (gammaL (fun i ↦ (α i : ℚ)) (fun i ↦ (β i : ℚ)) mq (mp * mq')) (mp * mq' * ∑ i, mq i)).isSome

/-- **Soundness and completeness of `torsionDecideN`.** -/
theorem torsionDecideN_iff {f : List ℤ} {n r : ℕ} {α β : Fin r → ℤ} {mq : Fin r → ℕ}
    (hcop : Nat.Coprime n (f.length - 1)) {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hsqQ : CPoly.squarefreeCheck (f.map (Int.castRingHom ℚ)) = true)
    {g g' : ℕ} {xs ys xs' ys' : List ℤ} {ζp ζq : ℤ} {lp lq : List (List ℤ)}
    (hgp : supBaseCheck p f n g α β xs ys ζp lp) (hgq : supBaseCheck q f n g' α β xs' ys' ζq lq) :
    torsionDecideN f n α β mq hcop p q hgp hgq = true ↔
      ∃ N, 1 ≤ N ∧ PrincipalMulN ((CPoly.toPoly f).map (Int.castRingHom ℚ)) n (f.length - 1)
        (fun i ↦ (α i : ℚ)) (fun i ↦ (β i : ℚ)) mq N := by
  obtain ⟨Dp, hDpf, hDpα, hDpβ⟩ := supBaseCheck_spec hgp
  obtain ⟨Dq, hDqf, hDqα, hDqβ⟩ := supBaseCheck_spec hgq
  obtain ⟨hmp1, hmp⟩ := orderModN_spec (mq := mq) hgp hcop Dp hDpf hDpα hDpβ
  obtain ⟨hmq1, hmq⟩ := orderModN_spec (mq := mq) hgq hcop Dq hDqf hDqα hDqβ
  have H := hgp
  obtain ⟨hn2, -, hd, hlc, -, -, -, -, -, -, -, -, hΓ, hΓd, hΓβ, -⟩ := H
  have hn : 0 < n := by omega
  have hfKd : ((CPoly.toPoly f).map (Int.castRingHom ℚ)).natDegree = f.length - 1 := by
    have hlc0 : ((CPoly.toPoly f).map (Int.castRingHom ℚ)).coeff (f.length - 1) ≠ 0 := by
      rw [coeff_map, CPoly.coeff_toPoly]
      intro h0
      apply hlc
      have : ((f.getD (f.length - 1) 0 : ℤ) : ℚ) = 0 := h0
      rw [Int.cast_eq_zero.mp this]; exact dvd_zero _
    refine le_antisymm ?_ (le_natDegree_of_ne_zero hlc0)
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have hm' : f.length - 1 < m := by exact_mod_cast hm
    rw [coeff_map, CPoly.coeff_toPoly, List.getD_eq_default _ _ (by omega)]
    simp
  have hsqK : Squarefree ((CPoly.toPoly f).map (Int.castRingHom ℚ)) := by
    have := CPoly.squarefreeCheck_sound hsqQ
    rwa [Jac.toPoly_map_list] at this
  have hnK : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hαK : Function.Injective fun i ↦ (((α i : ℤ) : ℚ), ((β i : ℤ) : ℚ)) := by
    intro i j h
    have h1 : α i = α j := by simpa using congrArg Prod.fst h
    have h2 : β i = β j := by simpa using congrArg Prod.snd h
    by_contra hne
    exact hΓβ i j hne h1 (by rw [h2, sub_self]; exact dvd_zero _)
  have hβK : ∀ i, ((β i : ℤ) : ℚ) ≠ 0 := fun i h0 ↦ (hΓ i).1 (by
    rw [Int.cast_eq_zero.mp h0]; exact dvd_zero _)
  have hvalK : ∀ i, ((β i : ℤ) : ℚ) ^ n = ((CPoly.toPoly f).map (Int.castRingHom ℚ)).eval ((α i : ℤ) : ℚ) := by
    intro i
    rw [eval_map, show ((α i : ℤ) : ℚ) = Int.castRingHom ℚ (α i) from rfl,
      eval₂_at_apply, ← CPoly.Kron.evalC_eq, ← (hΓ i).2.1]
    simp
  have hΓK : ∀ i, ((n : ℕ) : ℚ) * ((β i : ℤ) : ℚ) ^ (n - 1) ≠ 0 ∧
      ((β i : ℤ) : ℚ) ^ n = ((CPoly.toPoly f).map (Int.castRingHom ℚ)).eval ((α i : ℤ) : ℚ) :=
    fun i ↦ ⟨mul_ne_zero hnK (pow_ne_zero _ (hβK i)), hvalK i⟩
  have key := torsion_iff_two_primes_N hpq (algebraMap ℚ ℚ_[p]) (algebraMap ℚ ℚ_[q]) ((CPoly.toPoly f).map (Int.castRingHom ℚ)) hn hsqK
    (by rw [hfKd]; exact hd) (by rw [hfKd]; exact hcop) hnK _ _ mq hαK hβK hΓK Dp Dq _ hmp1
    (by rw [hfKd]; exact hmp) _ hmq1 (by rw [hfKd]; exact hmq)
  rw [hfKd] at key
  rw [key]
  unfold torsionDecideN
  have hfQ : CPoly.toPoly (f.map (Int.castRingHom ℚ)) = ((CPoly.toPoly f).map (Int.castRingHom ℚ)) := Jac.toPoly_map_list _ _
  have := principalMulN_iff_test (f.map (Int.castRingHom ℚ)) hn (f.length - 1)
    (fun i ↦ ((α i : ℤ) : ℚ)) (fun i ↦ ((β i : ℤ) : ℚ)) mq (by rw [hfQ]; exact hΓK)
    (orderModN (mq := mq) hgp hcop * orderModN (mq := mq) hgq hcop)
  rw [hfQ] at this
  rw [this]

end Sup
