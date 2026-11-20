import RischTragerBronstein.Jacobian.CertCheckK

/-!
# The torsion oracle over a number field

For `K = NF M` and a divisor `Γ = ∑ |zᵢ| (αᵢ, sign zᵢ βᵢ)` (`ptsQ l 1`), `torsNF` searches (below a
bound `B`) two good primes `p < q` (a simple root `s` of `M` modulo `p`, base points `E₀`,
`baseCheckK`), the exact orders `m_p`, `m_q` of `Γ̄` over `𝔽_p`, `𝔽_q` (first `m` with `principalC`
succeeding), and answers:

* `some none` if the orders are incompatible (`not_torsion_of_orders`),
* otherwise `some (some (m_p m_q))` or `some none` according to `principalC` over `K` at `m_p m_q`
  (`torsion_iff_two_primes`),
* `none` if the search fails.

`torsNF_spec`: this is a `TorsSpec` oracle.
-/

open Polynomial CPoly CPoly.Kron EllAlgo

namespace Jac

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

/-- The first `m ∈ [1, B]` with `m Γ̄` principal over `𝔽_p`. -/
def ordZ (p : ℕ) [Fact p.Prime] (fb : CPoly (ZMod p)) (g : ℕ) (Γb : EDiv (ZMod p)) (B : ℕ) :
    Option ℕ :=
  ((List.range B).find? fun i ↦ (principalC fb (escale (i + 1) Γb) (boundA ((i + 1) * edeg Γb))
    (boundB g ((i + 1) * edeg Γb))).isSome).map (· + 1)

/-- `E₀` modulo `p`, away from the reduced abscissae. -/
def findE0K (p : ℕ) (f : List ℤ) (g : ℕ) (xsb : List (ZMod p)) : Option (List ℤ × List ℤ) :=
  let cands := (List.range p).filterMap fun x : ℕ ↦
    if xsb.all (fun a ↦ a - (x : ZMod p) != 0) then
      (sqrtMod p (evalC f (x : ℤ))).map fun y ↦ ((x : ℤ), y)
    else none
  if cands.length < g then none else some ((cands.take g).map (·.1), (cands.take g).map (·.2))

/-- Good-prime data at `p` for the divisor `Γ` over `K`. -/
def goodK (mZ : List ℤ) (f : List ℤ) (g : ℕ) (Γ : EDiv (NFC.NF M)) (p : ℕ) :
    Option (ZMod p × List ℤ × List ℤ) :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    (List.range p).findSome? fun s0 : ℕ ↦
      let s : ZMod p := s0
      match findE0K p f g (Γ.map fun q ↦ redL p s q.1.1) with
      | some (xs, ys) =>
        if baseCheckK p mZ s f g Γ xs ys ∧ squarefreeCheck (castL p f) = true then some (s, xs, ys)
        else none
      | none => none
  else none

/-- Prime data. -/
abbrev PData := Σ p : ℕ, ZMod p × List ℤ × List ℤ

/-- The first good prime above `lo` (below `B`). -/
def firstGood (mZ : List ℤ) (f : List ℤ) (g : ℕ) (Γ : EDiv (NFC.NF M)) (lo B : ℕ) :
    Option PData :=
  (List.range B).findSome? fun p ↦
    if lo < p then (goodK mZ f g Γ p).map fun d ↦ (⟨p, d⟩ : PData) else none

/-- The answer from two good primes. -/
noncomputable def torsFrom (f : List ℤ) (g : ℕ) (Γ : EDiv (NFC.NF M)) (B : ℕ) (P Q : PData) :
    Option (Option ℕ) :=
  if hp : P.1.Prime ∧ Q.1.Prime then
    haveI : Fact P.1.Prime := ⟨hp.1⟩
    haveI : Fact Q.1.Prime := ⟨hp.2⟩
    match ordZ P.1 (castL P.1 f) g (redΓ P.1 P.2.1 Γ) B,
      ordZ Q.1 (castL Q.1 f) g (redΓ Q.1 Q.2.1 Γ) B with
    | some mp, some mq =>
      if (findWitness P.1 Q.1 mp mq).isSome then some none
      else if 1 ≤ Nat.lcm mp mq ∧ (principalC (curveK f) (escale (Nat.lcm mp mq) Γ)
          (boundA (Nat.lcm mp mq * edeg Γ)) (boundB g (Nat.lcm mp mq * edeg Γ))).isSome then
        some (some (Nat.lcm mp mq))
      else if (principalC (curveK f) (escale (mp * mq) Γ) (boundA (mp * mq * edeg Γ))
          (boundB g (mp * mq * edeg Γ))).isSome then some (some (mp * mq))
      else some none
    | _, _ => none
  else none

/-- **The torsion oracle over `NF M`** (search bound `B`). -/
noncomputable def torsNF (mZ : List ℤ) (f : List ℤ) (g : ℕ) (B : ℕ) (l : List (NFC.NF M × NFC.NF M × ℤ)) :
    Option (Option ℕ) :=
  let Γ := ptsQ l 1
  match firstGood mZ f g Γ 0 B with
  | none => none
  | some P =>
    match firstGood mZ f g Γ P.1 B with
    | none => none
    | some Q => torsFrom f g Γ B P Q

/-! ### Specifications -/

lemma ordZ_spec {p : ℕ} [Fact p.Prime] {fb : CPoly (ZMod p)} {g : ℕ} {Γb : EDiv (ZMod p)} {B m : ℕ}
    (h : ordZ p fb g Γb B = some m) :
    1 ≤ m ∧ (principalC fb (escale m Γb) (boundA (m * edeg Γb)) (boundB g (m * edeg Γb))).isSome ∧
      ∀ m', 1 ≤ m' → m' < m → (principalC fb (escale m' Γb) (boundA (m' * edeg Γb))
        (boundB g (m' * edeg Γb))).isSome = false := by
  unfold ordZ at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [List.find?_eq_some_iff_getElem] at hi
  obtain ⟨hp, k, hk, hki, hbefore⟩ := hi
  simp only [List.getElem_range] at hki
  subst hki
  refine ⟨by omega, hp, fun m' h1 h2 ↦ ?_⟩
  have := hbefore (m' - 1) (by omega)
  simp only [List.getElem_range, Nat.sub_add_cancel h1] at this
  simpa using this

lemma goodK_spec {mZ f : List ℤ} {g : ℕ} {Γ : EDiv (NFC.NF M)} {p : ℕ}
    {d : ZMod p × List ℤ × List ℤ} (h : goodK mZ f g Γ p = some d) :
    ∃ hp : p.Prime, @baseCheckK M p ⟨hp⟩ mZ d.1 f g Γ d.2.1 d.2.2 := by
  unfold goodK at h
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

lemma firstGood_spec {mZ f : List ℤ} {g : ℕ} {Γ : EDiv (NFC.NF M)} {lo B : ℕ} {P : PData}
    (h : firstGood mZ f g Γ lo B = some P) :
    lo < P.1 ∧ ∃ hp : P.1.Prime, @baseCheckK M P.1 ⟨hp⟩ mZ P.2.1 f g Γ P.2.2.1 P.2.2.2 := by
  unfold firstGood at h
  obtain ⟨p, -, hp⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at hp with hlo
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact ⟨hlo, goodK_spec hd⟩

/-- `𝔽_p`-principality of the reduction, via `principalC`. -/
lemma residue_iff_principalC {p : ℕ} [Fact p.Prime] {f : List ℤ} {g : ℕ} (B : BaseFacts p f g [])
    {Γp : EDiv ℤ_[p]} (hon : OnCurve ((toPoly f).map (Int.castRingHom ℤ_[p])) Γp)
    {Γb : EDiv (ZMod p)} (hred : emap PadicInt.toZMod Γp = Γb) (m : ℕ) :
    PrincipalMul (((toPoly f).map (Int.castRingHom ℤ_[p])).map (IsLocalRing.residue ℤ_[p])) g
      (emap (IsLocalRing.residue ℤ_[p]) Γp) m ↔
    (principalC (castL p f) (escale m Γb) (boundA (m * edeg Γb))
      (boundB g (m * edeg Γb))).isSome := by
  have honZ := OnCurve.map (φ := PadicInt.toZMod) hon
  rw [B.ef, hred] at honZ
  have hΓ : ∀ n, ∀ q ∈ escale n Γb, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = (toPoly (castL p f)).eval q.1 := by
    intro n q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact ⟨(honZ q' hq').1.ne_zero, (honZ q' hq').2⟩
  rw [← principalMul_iff_principalC (castL p f) g Γb hΓ m]
  constructor
  · intro hP
    have := principal_zmod_of_residue _ _ hP
    rwa [B.ef, hred] at this
  · intro hP
    apply principal_residue_of_zmod
    rwa [B.ef, hred]

set_option maxHeartbeats 1600000 in
/-- **Correctness of the two-prime answer.** -/
theorem torsFrom_spec {mZ : List ℤ} (hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ))
    {f : List ℤ} {g : ℕ} (hdeg : (toPoly (curveK (K := NFC.NF M) f)).natDegree = 2 * g + 1)
    {l : List (NFC.NF M × NFC.NF M × ℤ)}
    (hon : ∀ q ∈ l, (toPoly (curveK (K := NFC.NF M) f)).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0 ∧
      q.2.2 ≠ 0) (hnd : (l.map Prod.fst).Nodup) (B : ℕ) {P Q : PData} (hPQ : P.1 < Q.1)
    (hPp : P.1.Prime) (hPb : @baseCheckK M P.1 ⟨hPp⟩ mZ P.2.1 f g (ptsQ l 1) P.2.2.1 P.2.2.2)
    (hQp : Q.1.Prime) (hQb : @baseCheckK M Q.1 ⟨hQp⟩ mZ Q.2.1 f g (ptsQ l 1) Q.2.2.1 Q.2.2.2) :
    (∀ n, torsFrom f g (ptsQ l 1) B P Q = some (some n) → 1 ≤ n ∧
      PrincipalMul (toPoly (curveK (K := NFC.NF M) f)) g (ptsQ l 1) n) ∧
    (torsFrom f g (ptsQ l 1) B P Q = some none → ∀ n, 1 ≤ n →
      ¬ PrincipalMul (toPoly (curveK (K := NFC.NF M) f)) g (ptsQ l 1) n) := by
  classical
  obtain ⟨p, s, xs, ys⟩ := P
  obtain ⟨q, t, xs', ys'⟩ := Q
  simp only at hPQ hPp hQp hPb hQb ⊢
  have : Fact p.Prime := ⟨hPp⟩
  have : Fact q.Prime := ⟨hQp⟩
  set fK := toPoly (curveK (K := NFC.NF M) f)
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
  have hΓesc : ∀ n, ∀ r ∈ escale n Γ, 2 * r.2.1 ≠ 0 ∧ r.2.1 ^ 2 = (toPoly (curveK f)).eval r.1 := by
    intro n r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    exact hΓK r' hr'
  obtain ⟨φp, Γp, xp, yp, hmapp, hmapΓp, honp, hpwp, hyup, hyfp, hxp, hΓEp, hredp⟩ :=
    baseCheckK_spec hmZ hPb fun r hr ↦ (hΓK r hr).2
  obtain ⟨φq, Γq, xq, yq, hmapq, hmapΓq, honq, hpwq, hyuq, hyfq, hxq, hΓEq, hredq⟩ :=
    baseCheckK_spec hmZ hQb fun r hr ↦ (hΓK r hr).2
  have Bp := baseCheck_spec hPb.1
  have Bq := baseCheck_spec hQb.1
  unfold torsFrom
  rw [dif_pos ⟨hPp, hQp⟩]
  dsimp only
  split
  · rename_i mp mq hmp hmq
    obtain ⟨hmp1, hmpS, hmpmin⟩ := ordZ_spec hmp
    obtain ⟨hmq1, hmqS, hmqmin⟩ := ordZ_spec hmq
    have hPmp := (residue_iff_principalC Bp honp hredp mp).mpr hmpS
    have hPmq := (residue_iff_principalC Bq honq hredq mq).mpr hmqS
    have hminp : ∀ m', 1 ≤ m' → m' < mp → ¬ PrincipalMul
        (((toPoly f).map (Int.castRingHom ℤ_[p])).map (IsLocalRing.residue ℤ_[p])) g
        (emap (IsLocalRing.residue ℤ_[p]) Γp) m' := fun m' h1 h2 hP ↦ by
      rw [residue_iff_principalC Bp honp hredp m', hmpmin m' h1 h2] at hP
      exact Bool.noConfusion hP
    have hminq : ∀ m', 1 ≤ m' → m' < mq → ¬ PrincipalMul
        (((toPoly f).map (Int.castRingHom ℤ_[q])).map (IsLocalRing.residue ℤ_[q])) g
        (emap (IsLocalRing.residue ℤ_[q]) Γq) m' := fun m' h1 h2 hP ↦ by
      rw [residue_iff_principalC Bq honq hredq m', hmqmin m' h1 h2] at hP
      exact Bool.noConfusion hP
    have hK := principalMul_iff_principalC (curveK (K := NFC.NF M) f) g Γ hΓesc (mp * mq)
    have hiff := torsion_iff_two_primes Bp.hp2 Bq.hp2 (Nat.ne_of_lt hPQ) φp φq fK hdeg Γ hΓK hΓnd
      _ Bp.hdeg Bp.hlc hmapp xp yp hyup hyfp hxp Γp hmapΓp honp hpwp hΓEp mp hmp1 hPmp
      _ Bq.hdeg Bq.hlc hmapq xq yq hyuq hyfq hxq Γq hmapΓq honq hpwq hΓEq mq hmq1 hPmq
    have hKl := principalMul_iff_principalC (curveK (K := NFC.NF M) f) g Γ hΓesc (Nat.lcm mp mq)
    split_ifs with hw hl hc
    · refine ⟨(fun n hn ↦ by cases hn), fun _ ↦ ?_⟩
      exact not_torsion_of_orders Bp.hp2 Bq.hp2 φp φq fK hdeg Γ hΓK hΓnd
        _ Bp.hdeg Bp.hlc hmapp xp yp hyup hyfp hxp Γp hmapΓp honp hpwp hΓEp mp hmp1 hPmp hminp
        _ Bq.hdeg Bq.hlc hmapq xq yq hyuq hyfq hxq Γq hmapΓq honq hpwq hΓEq mq hmq1 hPmq hminq
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

/-- **`torsNF` is a correct torsion oracle.** -/
theorem torsNF_spec {mZ : List ℤ} (hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ))
    {f : List ℤ} {g : ℕ} (hdeg : (toPoly (curveK (K := NFC.NF M) f)).natDegree = 2 * g + 1)
    (B : ℕ) : TorsSpec f g (torsNF (M := M) mZ f g B) := by
  intro l hon hnd
  unfold torsNF
  dsimp only
  split
  · exact ⟨(fun n h ↦ by cases h), (fun h ↦ by cases h)⟩
  rename_i P hP
  split
  · exact ⟨(fun n h ↦ by cases h), (fun h ↦ by cases h)⟩
  rename_i Q hQ
  obtain ⟨-, hPp, hPb⟩ := firstGood_spec hP
  obtain ⟨hPQ, hQp, hQb⟩ := firstGood_spec hQ
  exact torsFrom_spec hmZ hdeg hon hnd B hPQ hPp hPb hQp hQb

end Jac
