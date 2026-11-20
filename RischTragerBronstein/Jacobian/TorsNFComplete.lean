import RischTragerBronstein.Jacobian.GoodPrimesK
import RischTragerBronstein.Jacobian.PicFinite

/-!
# The number-field torsion oracle eventually answers

`torsNF_eventually`: when base points `(aᵢ, bᵢ)` with `aᵢ ∈ ℤ` exist (as required by
`exists_goodK`), `torsNF mZ f g B l` is `some _` for every large enough search bound `B`:

* good primes exist above every bound (`exists_goodK`), and the first one found is stable in `B`
  (`firstGood_mono`);
* at a good prime the reduced divisor has finite order, since `Pic⁰` of a curve over a finite
  field is finite (`exists_principalMul`), so `ordZ` succeeds for large `B` (`ordZ_eventually`);
* once both orders are found, `torsFrom` always answers (`torsFrom_isSome`).
-/

open Polynomial CPoly CPoly.Kron EllAlgo

namespace Jac

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

lemma ordZ_isSome {p : ℕ} [Fact p.Prime] {fb : CPoly (ZMod p)} {g : ℕ} {Γb : EDiv (ZMod p)}
    (hΓ : ∀ n, ∀ q ∈ escale n Γb, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = (toPoly fb).eval q.1)
    {h B : ℕ} (h1 : 1 ≤ h) (hB : h ≤ B) (hP : PrincipalMul (toPoly fb) g Γb h) :
    (ordZ p fb g Γb B).isSome := by
  unfold ordZ
  rw [Option.isSome_map, List.find?_isSome]
  refine ⟨h - 1, List.mem_range.mpr (by omega), ?_⟩
  rw [Nat.sub_add_cancel h1]
  simpa using (principalMul_iff_principalC fb g Γb hΓ h).mp hP

omit [Fact (Irreducible (toPoly M))] in
lemma goodK_spec' {mZ f : List ℤ} {g : ℕ} {Γ : EDiv (NFC.NF M)} {p : ℕ}
    {d : ZMod p × List ℤ × List ℤ} (h : goodK mZ f g Γ p = some d) :
    ∃ hp : p.Prime, @baseCheckK M p ⟨hp⟩ mZ d.1 f g Γ d.2.1 d.2.2 ∧
      (haveI : Fact p.Prime := ⟨hp⟩; squarefreeCheck (castL p f) = true) := by
  unfold goodK at h
  split_ifs at h with hp
  refine ⟨hp, ?_⟩
  obtain ⟨s0, -, hs⟩ := List.exists_of_findSome?_eq_some h
  dsimp only at hs
  split at hs
  · split_ifs at hs with hb
    cases hs
    exact hb
  · cases hs

/-- At a good prime, the reduced divisor has finite order, found by `ordZ` for large bounds. -/
lemma ordZ_eventually {p : ℕ} [Fact p.Prime] {mZ : List ℤ}
    (hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ)) {s : ZMod p} {f : List ℤ} {g : ℕ}
    {Γ : EDiv (NFC.NF M)} {xs ys : List ℤ} (hb : baseCheckK p mZ s f g Γ xs ys)
    (hsqf : squarefreeCheck (castL p f) = true)
    (hK : ∀ q ∈ Γ, q.2.1 ^ 2 = (toPoly (curveK (K := NFC.NF M) f)).eval q.1) :
    ∃ B0, ∀ B, B0 ≤ B → (ordZ p (castL p f) g (redΓ p s Γ) B).isSome := by
  obtain ⟨φ, Γp, xp, yp, -, -, honp, hpwp, -, -, -, -, hredp⟩ := baseCheckK_spec hmZ hb hK
  have Bp := baseCheck_spec hb.1
  have honZ := OnCurve.map (φ := PadicInt.toZMod) honp
  rw [Bp.ef, hredp] at honZ
  have hnd : ((redΓ p s Γ).map Prod.fst).Nodup := by
    rw [← hredp, emap, List.map_map]
    refine hpwp.map _ fun r r' hu heq ↦ ?_
    have := hu.map (PadicInt.toZMod (p := p))
    simp only [Function.comp_apply] at heq
    rw [map_sub, heq, sub_self] at this
    exact not_isUnit_zero this
  obtain ⟨h, h1, hP⟩ := exists_principalMul (two_ne_zero_zmod Bp.hp2) Bp.hdegZ
    (squarefreeCheck_sound hsqf) honZ hnd
  have hΓ : ∀ n, ∀ q ∈ escale n (redΓ p s Γ), 2 * q.2.1 ≠ 0 ∧
      q.2.1 ^ 2 = (toPoly (castL p f)).eval q.1 := by
    intro n q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact ⟨(honZ q' hq').1.ne_zero, (honZ q' hq').2⟩
  exact ⟨h, fun B hB ↦ ordZ_isSome hΓ h1 hB hP⟩

omit [Fact (Irreducible (toPoly M))] in
lemma firstGood_mono {mZ f : List ℤ} {g : ℕ} {Γ : EDiv (NFC.NF M)} {lo B B' : ℕ} {P : PData}
    (h : firstGood mZ f g Γ lo B = some P) (hB : B ≤ B') : firstGood mZ f g Γ lo B' = some P := by
  unfold firstGood at *
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hB
  rw [List.range_add, List.findSome?_append, h]
  rfl

omit [Fact (Irreducible (toPoly M))] in
lemma firstGood_isSome {mZ f : List ℤ} {g : ℕ} {Γ : EDiv (NFC.NF M)} {lo p : ℕ} (hlo : lo < p)
    (hg : (goodK mZ f g Γ p).isSome) : (firstGood mZ f g Γ lo (p + 1)).isSome := by
  unfold firstGood
  rw [List.findSome?_isSome_iff]
  refine ⟨p, List.mem_range.mpr (Nat.lt_succ_self p), ?_⟩
  rw [if_pos hlo]
  simpa using hg

omit [Fact (Irreducible (toPoly M))] in
lemma firstGood_spec' {mZ f : List ℤ} {g : ℕ} {Γ : EDiv (NFC.NF M)} {lo B : ℕ} {P : PData}
    (h : firstGood mZ f g Γ lo B = some P) : lo < P.1 ∧ goodK mZ f g Γ P.1 = some P.2 := by
  unfold firstGood at h
  obtain ⟨p, -, hp⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at hp with hlo
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact ⟨hlo, hd⟩

lemma torsFrom_isSome {f : List ℤ} {g : ℕ} {Γ : EDiv (NFC.NF M)} {B : ℕ} {P Q : PData}
    (hp : P.1.Prime) (hq : Q.1.Prime)
    (hP : (@ordZ P.1 ⟨hp⟩ (castL P.1 f) g (redΓ P.1 P.2.1 Γ) B).isSome)
    (hQ : (@ordZ Q.1 ⟨hq⟩ (castL Q.1 f) g (redΓ Q.1 Q.2.1 Γ) B).isSome) :
    (torsFrom f g Γ B P Q).isSome := by
  obtain ⟨mp, hmp⟩ := Option.isSome_iff_exists.mp hP
  obtain ⟨mq, hmq⟩ := Option.isSome_iff_exists.mp hQ
  unfold torsFrom
  rw [dif_pos ⟨hp, hq⟩]
  split
  · split_ifs <;> rfl
  · rename_i hne
    exact absurd hmq (hne mp mq hmp)

/-- **Completeness of the number-field torsion oracle**: for every large search bound it answers. -/
theorem torsNF_eventually (hMZ : ∀ q ∈ M, q.den = 1) {f : List ℤ} {g : ℕ}
    (hlen : f.length = 2 * g + 2) (hlc : f.getD (2 * g + 1) 0 ≠ 0)
    (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ))) (hM1 : 0 < (toPoly M).natDegree)
    (l : List (NFC.NF M × NFC.NF M × ℤ))
    (hon : ∀ q ∈ l, (toPoly (curveK (K := NFC.NF M) f)).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0 ∧
      q.2.2 ≠ 0) (hnd : (l.map Prod.fst).Nodup)
    (as : List ℤ) (bs : List (NFC.NF M)) (hasl : as.length = g) (hbsl : bs.length = g)
    (hab : ∀ i (hi : i < g), bs[i]'(by omega) * bs[i]'(by omega) =
      ((evalC f (as[i]'(by omega)) : ℤ) : NFC.NF M) ∧ bs[i]'(by omega) ≠ 0)
    (hasnd : as.Nodup) (hΓa : ∀ q ∈ l, ∀ a ∈ as, q.1 ≠ (a : NFC.NF M)) :
    ∃ B0, ∀ B, B0 ≤ B → (torsNF (M := M) (M.map Rat.num) f g B l).isSome := by
  classical
  set mZ := M.map Rat.num
  have hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ) := (Kron.polyZ_map M hMZ).symm
  set Γ := ptsQ l 1 with hΓdef
  have hsgn : ∀ z : ℤ, z ≠ 0 → ((z.sign : ℤ) : NFC.NF M) ^ 2 = 1 := by
    intro z hz
    rcases lt_trichotomy z 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
    · exact absurd h hz
    · rw [Int.sign_eq_one_of_pos h]; norm_num
  have hK : ∀ q ∈ Γ, q.2.1 ^ 2 = (toPoly (curveK (K := NFC.NF M) f)).eval q.1 := by
    intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    obtain ⟨h1, -, h3⟩ := hon r' hr'
    simp only
    rw [mul_pow, hsgn _ h3, one_mul, h1]
  have hΓ0 : ∀ q ∈ Γ, q.2.1 ≠ 0 := by
    intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    obtain ⟨-, h2, h3⟩ := hon r' hr'
    have := hsgn _ h3
    exact mul_ne_zero (fun h0 ↦ by rw [h0] at this; norm_num at this) h2
  have hΓd : Γ.Pairwise fun u v ↦ u.1 ≠ v.1 := by
    have : (Γ.map Prod.fst).Nodup := by simp only [Γ, ptsQ, List.map_map]; exact hnd
    exact List.pairwise_map.mp this
  have hΓa' : ∀ q ∈ Γ, ∀ a ∈ as, q.1 ≠ (a : NFC.NF M) := by
    intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    exact hΓa r' hr'
  have hgood := fun N ↦ exists_goodK hMZ hlen hlc hsq hM1 Γ hΓ0 hΓd as bs hasl hbsl hab hasnd hΓa' N
  obtain ⟨p, -, hp⟩ := hgood 0
  have hp0 : 0 < p := by
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hp
    exact (goodK_spec' hd).1.pos
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp (firstGood_isSome hp0 hp)
  obtain ⟨q, hq1, hq⟩ := hgood P.1
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp (firstGood_isSome hq1 hq)
  obtain ⟨-, hPg⟩ := firstGood_spec' hP
  obtain ⟨-, hQg⟩ := firstGood_spec' hQ
  obtain ⟨hPp, hPb, hPs⟩ := goodK_spec' hPg
  obtain ⟨hQp, hQb, hQs⟩ := goodK_spec' hQg
  obtain ⟨BP, hBP⟩ := @ordZ_eventually M _ P.1 ⟨hPp⟩ mZ hmZ _ f g Γ _ _ hPb hPs hK
  obtain ⟨BQ, hBQ⟩ := @ordZ_eventually M _ Q.1 ⟨hQp⟩ mZ hmZ _ f g Γ _ _ hQb hQs hK
  refine ⟨max (max (p + 1) (q + 1)) (max BP BQ), fun B hB ↦ ?_⟩
  unfold torsNF
  dsimp only
  rw [firstGood_mono hP (by omega)]
  dsimp only
  rw [firstGood_mono hQ (by omega)]
  exact torsFrom_isSome hPp hQp (hBP B (by omega)) (hBQ B (by omega))

end Jac
