import RischTragerBronstein.Jacobian.CertCheckKF
import RischTragerBronstein.Jacobian.HypDecideKF

/-!
# The torsion oracle for a curve over a number field

As `torsNF`, for `y² = f(x)` with `f ∈ K[x]`, `K = NF M`: the curve is reduced coefficientwise
(`redF`), base points are searched on an integer lift of the reduced curve (`findE0K`), and
`baseCheckKF` certifies good reduction. `torsNFF_spec`: a `TorsSpecF` oracle.
-/

open Polynomial CPoly CPoly.Kron EllAlgo

namespace Jac

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

/-- Integer representatives of a list over `𝔽_p`. -/
def liftZ {p : ℕ} (l : CPoly (ZMod p)) : List ℤ := l.map fun c ↦ (c.val : ℤ)

/-- Good-prime data at `p` for the divisor `Γ` over `K`. -/
def goodKF (mZ : List ℤ) (f : CPoly (NFC.NF M)) (g : ℕ) (Γ : EDiv (NFC.NF M)) (p : ℕ) :
    Option (ZMod p × List ℤ × List ℤ) :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    (List.range p).findSome? fun s0 : ℕ ↦
      let s : ZMod p := s0
      match findE0K p (liftZ (redF p s f)) g (Γ.map fun q ↦ redL p s q.1.1) with
      | some (xs, ys) =>
        if baseCheckKF p mZ s f g Γ xs ys ∧ squarefreeCheck (redF p s f) = true then some (s, xs, ys)
        else none
      | none => none
  else none


/-- The first good prime above `lo` (below `B`). -/
def firstGoodF (mZ : List ℤ) (f : CPoly (NFC.NF M)) (g : ℕ) (Γ : EDiv (NFC.NF M)) (lo B : ℕ) :
    Option PData :=
  (List.range B).findSome? fun p ↦
    if lo < p then (goodKF mZ f g Γ p).map fun d ↦ (⟨p, d⟩ : PData) else none

/-- The answer from two good primes. -/
noncomputable def torsFromF (f : CPoly (NFC.NF M)) (g : ℕ) (Γ : EDiv (NFC.NF M)) (B : ℕ) (P Q : PData) :
    Option (Option ℕ) :=
  if hp : P.1.Prime ∧ Q.1.Prime then
    haveI : Fact P.1.Prime := ⟨hp.1⟩
    haveI : Fact Q.1.Prime := ⟨hp.2⟩
    match ordZ P.1 (redF P.1 P.2.1 f) g (redΓ P.1 P.2.1 Γ) B,
      ordZ Q.1 (redF Q.1 Q.2.1 f) g (redΓ Q.1 Q.2.1 Γ) B with
    | some mp, some mq =>
      if (findWitness P.1 Q.1 mp mq).isSome then some none
      else if 1 ≤ Nat.lcm mp mq ∧ (principalC f (escale (Nat.lcm mp mq) Γ)
          (boundA (Nat.lcm mp mq * edeg Γ)) (boundB g (Nat.lcm mp mq * edeg Γ))).isSome then
        some (some (Nat.lcm mp mq))
      else if (principalC f (escale (mp * mq) Γ) (boundA (mp * mq * edeg Γ))
          (boundB g (mp * mq * edeg Γ))).isSome then some (some (mp * mq))
      else some none
    | _, _ => none
  else none

/-- **The torsion oracle over `NF M`** (search bound `B`). -/
noncomputable def torsNFF (mZ : List ℤ) (f : CPoly (NFC.NF M)) (g : ℕ) (B : ℕ) (l : List (NFC.NF M × NFC.NF M × ℤ)) :
    Option (Option ℕ) :=
  let Γ := ptsQ l 1
  match firstGoodF mZ f g Γ 0 B with
  | none => none
  | some P =>
    match firstGoodF mZ f g Γ P.1 B with
    | none => none
    | some Q => torsFromF f g Γ B P Q

lemma goodKF_spec {mZ : List ℤ} {f : CPoly (NFC.NF M)} {g : ℕ} {Γ : EDiv (NFC.NF M)} {p : ℕ}
    {d : ZMod p × List ℤ × List ℤ} (h : goodKF mZ f g Γ p = some d) :
    ∃ hp : p.Prime, @baseCheckKF M _ p ⟨hp⟩ mZ d.1 f g Γ d.2.1 d.2.2 := by
  unfold goodKF at h
  split_ifs at h with hp
  refine ⟨hp, ?_⟩
  obtain ⟨s0, -, hs⟩ := List.exists_of_findSome?_eq_some h
  dsimp only at hs
  split at hs
  · rename_i xs ys _
    split_ifs at hs with hb
    cases hs
    exact hb.1
  · cases hs

lemma firstGoodF_spec {mZ : List ℤ} {f : CPoly (NFC.NF M)} {g : ℕ} {Γ : EDiv (NFC.NF M)} {lo B : ℕ} {P : PData}
    (h : firstGoodF mZ f g Γ lo B = some P) :
    lo < P.1 ∧ ∃ hp : P.1.Prime, @baseCheckKF M _ P.1 ⟨hp⟩ mZ P.2.1 f g Γ P.2.2.1 P.2.2.2 := by
  unfold firstGoodF at h
  obtain ⟨p, -, hp⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at hp with hlo
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact ⟨hlo, goodKF_spec hd⟩

set_option maxHeartbeats 1600000 in
/-- **Correctness of the two-prime answer.** -/
theorem torsFromF_spec {mZ : List ℤ} (hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ))
    {f : CPoly (NFC.NF M)} {g : ℕ} (hdeg : (toPoly (f)).natDegree = 2 * g + 1)
    {l : List (NFC.NF M × NFC.NF M × ℤ)}
    (hon : ∀ q ∈ l, (toPoly (f)).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0 ∧
      q.2.2 ≠ 0) (hnd : (l.map Prod.fst).Nodup) (B : ℕ) {P Q : PData} (hPQ : P.1 < Q.1)
    (hPp : P.1.Prime) (hPb : @baseCheckKF M _ P.1 ⟨hPp⟩ mZ P.2.1 f g (ptsQ l 1) P.2.2.1 P.2.2.2)
    (hQp : Q.1.Prime) (hQb : @baseCheckKF M _ Q.1 ⟨hQp⟩ mZ Q.2.1 f g (ptsQ l 1) Q.2.2.1 Q.2.2.2) :
    (∀ n, torsFromF f g (ptsQ l 1) B P Q = some (some n) → 1 ≤ n ∧
      PrincipalMul (toPoly (f)) g (ptsQ l 1) n) ∧
    (torsFromF f g (ptsQ l 1) B P Q = some none → ∀ n, 1 ≤ n →
      ¬ PrincipalMul (toPoly (f)) g (ptsQ l 1) n) := by
  classical
  obtain ⟨p, s, xs, ys⟩ := P
  obtain ⟨q, t, xs', ys'⟩ := Q
  simp only at hPQ hPp hQp hPb hQb ⊢
  have : Fact p.Prime := ⟨hPp⟩
  have : Fact q.Prime := ⟨hQp⟩
  set fK := toPoly (f)
  set Γ := ptsQ l 1
  have hΓK : ∀ r ∈ Γ, 2 * r.2.1 ≠ 0 ∧ r.2.1 ^ 2 = fK.eval r.1 := by
    intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    obtain ⟨h1, h2, h3⟩ := hon r' hr'
    have hs : ((r'.2.2.sign : ℤ) : NFC.NF M) ^ 2 = 1 := by
      rcases lt_trichotomy r'.2.2 0 with h | h | h
      · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
      · exact absurd h h3
      · rw [Int.sign_eq_one_of_pos h]; norm_num
    refine ⟨mul_ne_zero two_ne_zero (mul_ne_zero (fun h0 ↦ by rw [h0] at hs; norm_num at hs) h2),
      ?_⟩
    simp only
    rw [mul_pow, hs, one_mul, h1]
  have hΓnd : (Γ.map Prod.fst).Nodup := by
    simp only [Γ, ptsQ, List.map_map]; exact hnd
  have hΓesc : ∀ n, ∀ r ∈ escale n Γ, 2 * r.2.1 ≠ 0 ∧ r.2.1 ^ 2 = (toPoly f).eval r.1 := by
    intro n r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    exact hΓK r' hr'
  obtain ⟨φp, Fp, Γp, xp, yp, hmapp, hdegp, hlcp, hFp, hmapΓp, honp, hpwp, hyup, hyfp, hxp, hΓEp,
    hredp⟩ := baseCheckKF_spec hmZ hPb fun r hr ↦ (hΓK r hr).2
  obtain ⟨φq, Fq, Γq, xq, yq, hmapq, hdegq, hlcq, hFq, hmapΓq, honq, hpwq, hyuq, hyfq, hxq, hΓEq,
    hredq⟩ := baseCheckKF_spec hmZ hQb fun r hr ↦ (hΓK r hr).2
  have hp2 : p ≠ 2 := hPb.1
  have hq2 : q ≠ 2 := hQb.1
  unfold torsFromF
  rw [dif_pos ⟨hPp, hQp⟩]
  dsimp only
  split
  · rename_i mp mq hmp hmq
    obtain ⟨hmp1, hmpS, hmpmin⟩ := ordZ_spec hmp
    obtain ⟨hmq1, hmqS, hmqmin⟩ := ordZ_spec hmq
    have hPmp := (residue_iff_principalCF hFp honp hredp mp).mpr hmpS
    have hPmq := (residue_iff_principalCF hFq honq hredq mq).mpr hmqS
    have hminp : ∀ m', 1 ≤ m' → m' < mp → ¬ PrincipalMul
        (Fp.map (IsLocalRing.residue ℤ_[p])) g
        (emap (IsLocalRing.residue ℤ_[p]) Γp) m' := fun m' h1 h2 hP ↦ by
      rw [residue_iff_principalCF hFp honp hredp m', hmpmin m' h1 h2] at hP
      exact Bool.noConfusion hP
    have hminq : ∀ m', 1 ≤ m' → m' < mq → ¬ PrincipalMul
        (Fq.map (IsLocalRing.residue ℤ_[q])) g
        (emap (IsLocalRing.residue ℤ_[q]) Γq) m' := fun m' h1 h2 hP ↦ by
      rw [residue_iff_principalCF hFq honq hredq m', hmqmin m' h1 h2] at hP
      exact Bool.noConfusion hP
    have hK := principalMul_iff_principalC (f) g Γ hΓesc (mp * mq)
    have hiff := torsion_iff_two_primes hp2 hq2 (Nat.ne_of_lt hPQ) φp φq fK hdeg Γ hΓK hΓnd
      _ hdegp hlcp hmapp xp yp hyup hyfp hxp Γp hmapΓp honp hpwp hΓEp mp hmp1 hPmp
      _ hdegq hlcq hmapq xq yq hyuq hyfq hxq Γq hmapΓq honq hpwq hΓEq mq hmq1 hPmq
    have hKl := principalMul_iff_principalC (f) g Γ hΓesc (Nat.lcm mp mq)
    split_ifs with hw hl hc
    · refine ⟨(fun n hn ↦ by cases hn), fun _ ↦ ?_⟩
      exact not_torsion_of_orders hp2 hq2 φp φq fK hdeg Γ hΓK hΓnd
        _ hdegp hlcp hmapp xp yp hyup hyfp hxp Γp hmapΓp honp hpwp hΓEp mp hmp1 hPmp hminp
        _ hdegq hlcq hmapq xq yq hyuq hyfq hxq Γq hmapΓq honq hpwq hΓEq mq hmq1 hPmq hminq
        (findWitness_spec hPp hQp hw)
    · refine ⟨fun n hn ↦ ?_, (fun h ↦ by cases h)⟩
      simp only [Option.some.injEq] at hn
      subst hn
      exact ⟨hl.1, hKl.mpr hl.2⟩
    · refine ⟨fun n hn ↦ ?_, (fun h ↦ by cases h)⟩
      simp only [Option.some.injEq] at hn
      subst hn
      exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hK.mpr hc⟩
    · refine ⟨(fun n hn ↦ by cases hn), fun _ n hn1 hn ↦ hc ?_⟩
      exact hK.mp (hiff.mp ⟨n, hn1, hn⟩)
  · exact ⟨(fun n h ↦ by cases h), (fun h ↦ by cases h)⟩

/-- **`torsNFF` is a correct torsion oracle.** -/
theorem torsNFF_spec {mZ : List ℤ} (hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ))
    {f : CPoly (NFC.NF M)} {g : ℕ} (hdeg : (toPoly (f)).natDegree = 2 * g + 1)
    (B : ℕ) : TorsSpecF f g (torsNFF (M := M) mZ f g B) := by
  intro l hon hnd
  unfold torsNFF
  dsimp only
  split
  · exact ⟨(fun n h ↦ by cases h), (fun h ↦ by cases h)⟩
  rename_i P hP
  split
  · exact ⟨(fun n h ↦ by cases h), (fun h ↦ by cases h)⟩
  rename_i Q hQ
  obtain ⟨-, hPp, hPb⟩ := firstGoodF_spec hP
  obtain ⟨hPQ, hQp, hQb⟩ := firstGoodF_spec hQ
  exact torsFromF_spec hmZ hdeg hon hnd B hPQ hPp hPb hQp hQb

end Jac
