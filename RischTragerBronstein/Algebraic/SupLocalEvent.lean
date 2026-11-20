import RischTragerBronstein.Algebraic.SupLocalCert
import RischTragerBronstein.Algebraic.SupRedEvent
import RischTragerBronstein.Algebraic.SupRedGEvent

/-!
# The local-certificate torsion oracle eventually answers (square roots)

For any field `K` of characteristic `0` with reductions `Rf p` (induced by embeddings into `ℚ_p`)
at infinitely many primes (`G`), and a query `y² = f(x)`, points `(αq, βq)` whose data are
eventually integral (`EvOk`), the oracle `torsOracleC redAt (localCert f 2)` answers for every
large bound (`torsOracleLocal_eventually`). No global points over `K` are needed: the base points
are found modulo `p` (Stepanov's bound guarantees them).
-/

open Polynomial CPoly CPoly.Kron

set_option linter.unusedSectionVars false

namespace Sup

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

lemma evOk_fintype (G : ℕ → Prop) (Rf : (p : ℕ) → [Fact p.Prime] → RedFns p K) {ι : Type*}
    [Fintype ι] (f : ι → K) (h : ∀ i, EvOk G Rf (f i)) :
    ∃ T : ℕ, ∀ (p : ℕ) [Fact p.Prime], G p → T < p → ∀ i, (Rf p).ok (f i) = true := by
  classical
  obtain ⟨T, hT⟩ := evOk_list G Rf (Finset.univ.toList.map f)
    (fun a ha ↦ by obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha; exact h i)
  exact ⟨T, fun p _ hG hp i ↦ hT p hG hp _ (List.mem_map.mpr ⟨i, by simp, rfl⟩)⟩

lemma natDegree_toPoly_red {p : ℕ} [Fact p.Prime] (R : RedFns p K) (fK : CPoly K)
    (hd : 0 < fK.length - 1) (hl : R.red (fK.getD (fK.length - 1) 0) ≠ 0) :
    (toPoly (fK.map R.red)).natDegree = fK.length - 1 := by
  have hlm : fK.length - 1 < fK.length := by omega
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_toPoly, List.getD_eq_default _ _ (by
      simp only [List.length_map]; have : fK.length - 1 < i := by exact_mod_cast hi
      omega)]
  · rw [coeff_toPoly, List.getD_eq_getElem _ _ (by simpa using hlm), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hlm]
    exact hl

set_option maxHeartbeats 4000000 in
/-- **The local-certificate oracle eventually answers** (square roots). -/
theorem torsOracleLocal_eventually (redAt : (p : ℕ) → Option (RedFns p K)) (G : ℕ → Prop)
    (hGinf : ∀ N, ∃ p, p.Prime ∧ G p ∧ N < p) (Rf : (p : ℕ) → [Fact p.Prime] → RedFns p K)
    (hredAt : ∀ (p : ℕ) [Fact p.Prime], G p → redAt p = some (Rf p))
    (hValid : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p K), redAt p = some R →
      ∃ φ : K →+* ℚ_[p], RedValid p R φ)
    {fK : CPoly K} (hd : 0 < fK.length - 1) (hlc : fK.getD (fK.length - 1) 0 ≠ 0)
    (hcop : Nat.Coprime 2 (fK.length - 1)) {u v : List K}
    (hbez : toPoly u * toPoly fK + toPoly v * derivative (toPoly fK) = 1)
    (l : List (K × K × ℕ))
    (hΓ : ∀ q : Fin l.length, (l.get q).2.1 ≠ 0 ∧ (l.get q).2.1 ^ 2 = evalC fK (l.get q).1)
    (hinj : Function.Injective fun q : Fin l.length ↦ ((l.get q).1, (l.get q).2.1))
    (hevf : ∀ c ∈ fK, EvOk G Rf c) (hevl : EvOk G Rf (fK.getD (fK.length - 1) 0)⁻¹)
    (hevu : ∀ c ∈ u, EvOk G Rf c) (hevv : ∀ c ∈ v, EvOk G Rf c)
    (hevα : ∀ q : Fin l.length, EvOk G Rf (l.get q).1)
    (hevβ : ∀ q : Fin l.length, EvOk G Rf (l.get q).2.1)
    (hevβi : ∀ q : Fin l.length, EvOk G Rf ((l.get q).2.1)⁻¹)
    (hevd : ∀ q q' : Fin l.length, (l.get q).1 ≠ (l.get q').1 →
      EvOk G Rf ((l.get q).1 - (l.get q').1)⁻¹)
    (hevb : ∀ q q' : Fin l.length, q ≠ q' → (l.get q).1 = (l.get q').1 →
      EvOk G Rf ((l.get q).2.1 - (l.get q').2.1)⁻¹) :
    ∃ B0, ∀ B, B0 ≤ B → (torsOracleC redAt (localCert fK 2) (primesBelow B) B fK 2 l).isSome := by
  classical
  set α' : Fin l.length → K := fun q ↦ (l.get q).1 with hα'
  set β' : Fin l.length → K := fun q ↦ (l.get q).2.1 with hβ'
  set mu' : Fin l.length → ℕ := fun q ↦ (l.get q).2.2 with hmu'
  -- uniform bounds for the integrality facts
  obtain ⟨T1, h1⟩ := evOk_list G Rf (fK ++ [(fK.getD (fK.length - 1) 0)⁻¹] ++ u ++ v)
    (fun a ha ↦ by
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ((ha | rfl) | ha) | ha
      · exact hevf a ha
      · exact hevl
      · exact hevu a ha
      · exact hevv a ha)
  obtain ⟨T2, h2⟩ := evOk_fintype G Rf (fun q : Fin l.length ↦ α' q) (fun q ↦ hevα q)
  obtain ⟨T3, h3⟩ := evOk_fintype G Rf (fun q : Fin l.length ↦ β' q) (fun q ↦ hevβ q)
  obtain ⟨T4, h4⟩ := evOk_fintype G Rf (fun q : Fin l.length ↦ (β' q)⁻¹) (fun q ↦ hevβi q)
  obtain ⟨T5, h5⟩ := evOk_fintype G Rf
    (fun qq : {qq : Fin l.length × Fin l.length // α' qq.1 ≠ α' qq.2} ↦ (α' qq.1.1 - α' qq.1.2)⁻¹)
    (fun qq ↦ hevd _ _ qq.2)
  obtain ⟨T6, h6⟩ := evOk_fintype G Rf
    (fun qq : {qq : Fin l.length × Fin l.length // qq.1 ≠ qq.2 ∧ α' qq.1 = α' qq.2} ↦
      (β' qq.1.1 - β' qq.1.2)⁻¹)
    (fun qq ↦ hevb _ _ qq.2.1 qq.2.2)
  set Tb := (16 * (fK.length - 1 + 2) * ((((2 - 1) * (fK.length - 1 - 1) + 1) / 2 +
    (fK.length - 1) + l.length + 1) + (fK.length - 1) + 2)) ^ 2 with hTb
  set T0 := T1 + T2 + T3 + T4 + T5 + T6 + Tb + 3 with hT0
  -- every prime of `G` beyond `T0` is good
  have hgood : ∀ p, p.Prime → G p → T0 < p →
      goodPrime redAt (localCert fK 2) fK 2 α' β' p = true := by
    intro p hpp hGp hpT
    haveI : Fact p.Prime := ⟨hpp⟩
    obtain ⟨φ, hφ⟩ := hValid p (Rf p) (hredAt p hGp)
    set R := Rf p
    have hok1 := h1 p hGp (by omega)
    have hokf : ∀ c ∈ fK, R.ok c = true := fun c hc ↦ hok1 c (by simp [hc])
    have hokl : R.ok (fK.getD (fK.length - 1) 0)⁻¹ = true := hok1 _ (by simp)
    have hoku : ∀ c ∈ u, R.ok c = true := fun c hc ↦ hok1 c (by simp [hc])
    have hokv : ∀ c ∈ v, R.ok c = true := fun c hc ↦ hok1 c (by simp [hc])
    have hlm : fK.length - 1 < fK.length := by omega
    have hlcok : R.ok (fK.getD (fK.length - 1) 0) = true := hokf _ (by
      rw [List.getD_eq_getElem _ _ hlm]; exact List.getElem_mem hlm)
    have hredl := red_ne_zero R φ hφ hlc hlcok hokl
    have hp2 : p ≠ 2 := by omega
    have hnp : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    -- the reduced curve
    have hdegr := natDegree_toPoly_red R fK hd hredl
    have hbr := red_bezout φ R hφ hoku hokv hokf hbez
    have hsq : Squarefree (toPoly (fK.map R.red)) :=
      (show (toPoly (fK.map R.red)).Separable from ⟨_, _, hbr⟩).squarefree
    have hsome := localCert_isSome hp2 R fK α' hcop (by rw [hdegr]; omega) hsq
      (by rw [hdegr]; exact le_of_lt (by omega))
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨cg, cxs, cys, cζ, clam⟩ := c
    have hchk := localCert_check (n := 2) R φ hφ (le_refl 2) hnp hd hokf hlc hokl hoku hokv hbez
      (α := α') (β := β')
      (fun q ↦ ⟨h2 p hGp (by omega) q, h3 p hGp (by omega) q, (hΓ q).1, h4 p hGp (by omega) q,
        (hΓ q).2⟩)
      (fun q q' hne ↦ h5 p hGp (by omega) ⟨(q, q'), hne⟩)
      (fun q q' hqq hα ↦ ⟨fun hb ↦ hqq (hinj (Prod.ext hα hb)),
        h6 p hGp (by omega) ⟨(q, q'), hqq, hα⟩⟩) hc
    unfold goodPrime
    rw [dif_pos hpp]
    simp only [hredAt p hGp]
    rw [show localCert fK 2 p (Rf p) α' = some (cg, cxs, cys, cζ, clam) from hc]
    exact decide_eq_true hchk
  -- two good primes
  obtain ⟨p1, hp1, hG1, hp1T⟩ := hGinf T0
  obtain ⟨p2, hp2, hG2, hp2T⟩ := hGinf p1
  have hg1 := hgood p1 hp1 hG1 hp1T
  have hg2 := hgood p2 hp2 hG2 (by omega)
  set good := goodPrime redAt (localCert fK 2) fK 2 α' β' with hgoodd
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
  obtain ⟨φp, hφp⟩ := hValid p Rp hRp
  obtain ⟨φq, hφq⟩ := hValid q Rq hRq
  obtain ⟨mp, hmp1, hmp⟩ := exists_orderR Rp φp hφp mu' hcp hcop
  obtain ⟨mq', hmq1, hmq⟩ := exists_orderR Rq φq hφq mu' hcq hcop
  refine ⟨max B1 (max mp mq'), fun B hB ↦ ?_⟩
  have hB1 : B1 ≤ B := le_trans (le_max_left _ _) hB
  have hpB := find?_prefix (primesBelow_prefix hB1) hp
  have hqB := find?_prefix ((primesBelow_prefix hB1).filter _) hq
  unfold torsOracleC
  simp only []
  rw [hgoodd] at hpB hqB
  rw [show (fun q ↦ (l.get q).1) = α' from rfl, show (fun q ↦ (l.get q).2.1) = β' from rfl, hpB]
  dsimp only
  rw [hqB]
  dsimp only
  unfold torsWith
  rw [dif_pos hpr, dif_pos hqr]
  simp only [hRp, hRq]
  unfold torsDecideR
  obtain ⟨op, hop⟩ := Option.isSome_iff_exists.mp
    (orderSearchR_isSome Rp fK 2 α' β' mu' hmp1 hmp (bound := B) (by omega))
  obtain ⟨oq, hoq⟩ := Option.isSome_iff_exists.mp
    (orderSearchR_isSome Rq fK 2 α' β' mu' hmq1 hmq (bound := B) (by omega))
  rw [hop, hoq]
  simp only []
  split_ifs <;> rfl

end Sup
