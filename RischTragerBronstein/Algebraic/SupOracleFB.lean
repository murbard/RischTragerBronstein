import RischTragerBronstein.Algebraic.SupCertSearch
import RischTragerBronstein.Algebraic.SupRedGEvent

/-!
# A torsion oracle that always eventually answers

`torsOracleFB` first runs the search oracle `torsOracle` (certificates found modulo `p`) and, if it
does not answer, the oracle with **global** certificates found by `certSearch` among candidate
points of the curve over `K`.

* `torsOracleFB_spec`: it satisfies `TorsSpecN` (every answer is correct).
* `torsOracleFB_eventually`: on every valid query, it answers for all large bounds, provided there
  are enough candidate points (more than `g + d + r` abscissae, `r` the number of query points).
-/

open Polynomial CPoly CPoly.Kron

namespace Sup

section Oracle

variable {K : Type*} [Field K] [DecidableEq K] (redAt : (p : ℕ) → Option (RedFns p K))

/-- The global certificate provider: search a certificate avoiding the query's abscissae. -/
def certProvG (fK : CPoly K) (n : ℕ) (ζ : K) (cands : List (K × K)) : CertProv K :=
  fun p _ R _ α ↦
    match certSearch (fK.length - 1) n ζ cands (List.ofFn α) with
    | some (xs, ys, lam) => globalCert ζ xs ys lam p R α
    | none => none

/-- **The combined oracle.** -/
def torsOracleFB (ps : List ℕ) (bound : ℕ) (fK : CPoly K) (n : ℕ) (ζ : K) (cands : List (K × K))
    (l : List (K × K × ℕ)) : Option (Option ℕ) :=
  match torsOracle redAt ps bound fK n l with
  | some a => some a
  | none => torsOracleC redAt (certProvG fK n ζ cands) ps bound fK n l

theorem torsOracleFB_spec [CharZero K]
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p K), redAt p = some R →
      ∃ φ : K →+* ℚ_[p], RedValid p R φ)
    (ps : List ℕ) (bound : ℕ) {fK : CPoly K} {n : ℕ} (ζ : K) (cands : List (K × K))
    (hsq : Squarefree (CPoly.toPoly fK)) (hcop : Nat.Coprime n (fK.length - 1)) :
    TorsSpecN fK n (torsOracleFB redAt ps bound fK n ζ cands) := by
  intro r α β mq hv hinj
  have h1 := torsOracle_spec redAt hred ps bound hsq hcop r α β mq hv hinj
  have h2 := torsOracleC_spec redAt (certProvG fK n ζ cands) hred ps bound hsq hcop r α β mq hv hinj
  unfold torsOracleFB
  split
  · rename_i a ha
    rw [← ha]; exact h1
  · exact h2

end Oracle

section Congr

variable {K : Type*} [Field K] [DecidableEq K] (redAt : (p : ℕ) → Option (RedFns p K))

/-- `torsOracleC` consults the provider only on the query's abscissae. -/
lemma torsOracleC_congr (cp cp' : CertProv K) (ps : List ℕ) (bound : ℕ) (fK : CPoly K) (n : ℕ)
    (l : List (K × K × ℕ))
    (h : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p K),
      cp p R (fun q : Fin l.length ↦ (l.get q).1) = cp' p R (fun q : Fin l.length ↦ (l.get q).1)) :
    torsOracleC redAt cp ps bound fK n l = torsOracleC redAt cp' ps bound fK n l := by
  have hg : goodPrime redAt cp fK n (fun q : Fin l.length ↦ (l.get q).1)
      (fun q : Fin l.length ↦ (l.get q).2.1) =
      goodPrime redAt cp' fK n (fun q : Fin l.length ↦ (l.get q).1)
      (fun q : Fin l.length ↦ (l.get q).2.1) := by
    funext p
    unfold goodPrime
    split_ifs with hp
    · haveI : Fact p.Prime := ⟨hp⟩
      split
      · rename_i R _
        rw [h p R]
      · rfl
    · rfl
  unfold torsOracleC
  simp only [hg]

end Congr

section Eventually

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

lemma card_filter_avoid {K : Type*} [DecidableEq K] (cands : List (K × K)) (avoid : List K) :
    (cands.map Prod.fst).toFinset.card ≤
      ((cands.filter fun c ↦ c.1 ∉ avoid).map Prod.fst).toFinset.card + avoid.length := by
  classical
  have hsub : (cands.map Prod.fst).toFinset ⊆
      ((cands.filter fun c ↦ c.1 ∉ avoid).map Prod.fst).toFinset ∪ avoid.toFinset := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    by_cases hav : c.1 ∈ avoid
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hav)
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨c, List.mem_filter.mpr ⟨hc, by simpa using hav⟩, rfl⟩))
  calc (cands.map Prod.fst).toFinset.card
      ≤ (((cands.filter fun c ↦ c.1 ∉ avoid).map Prod.fst).toFinset ∪ avoid.toFinset).card :=
        Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (List.toFinset_card_le _) _

set_option maxHeartbeats 3200000 in
/-- **The combined oracle eventually answers** every valid query, given enough candidate points
`(x, y)` (`yⁿ = f(x)`, `y ≠ 0`) of the curve over `K`. -/
theorem torsOracleFB_eventually {mZl : List ℤ}
    (hmZ : toPoly M = (toPoly mZl).map (Int.castRingHom ℚ)) (hM1 : 0 < (toPoly mZl).natDegree)
    {fK : CPoly (NFC.NF M)} {n : ℕ} (hn2 : 2 ≤ n) (hd : 0 < fK.length - 1)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hsq : Squarefree (toPoly fK))
    (hcop : Nat.Coprime n (fK.length - 1)) {ζ : NFC.NF M} (hζ : IsPrimitiveRoot ζ n)
    (cands : List (NFC.NF M × NFC.NF M))
    (hc : ∀ c ∈ cands, c.2 ≠ 0 ∧ c.2 ^ n = evalC fK c.1)
    {r : ℕ} (α β : Fin r → NFC.NF M) (mq : Fin r → ℕ)
    (hΓ : ∀ q, β q ≠ 0 ∧ β q ^ n = evalC fK (α q)) (hinj : Function.Injective fun q ↦ (α q, β q))
    (hcard : ((n - 1) * (fK.length - 1 - 1) + 1) / 2 + (fK.length - 1) + r <
      (cands.map Prod.fst).toFinset.card) :
    ∃ B0, ∀ B, B0 ≤ B → (torsOracleFB (nfRedAt (M := M) mZl) (primesBelow B) B fK n ζ cands
      (gammaL α β mq 1)).isSome := by
  classical
  set d := fK.length - 1 with hd'
  set l := gammaL α β mq 1 with hl
  have hlen : l.length = r := by simp [hl, gammaL]
  set α' : Fin l.length → NFC.NF M := fun q ↦ (l.get q).1 with hα'
  have hα'e : ∀ q, α' q = α (finCongr hlen q) := fun q ↦ by simp [hα', hl, gammaL]; rfl
  have hαmem : ∀ q, α q ∈ List.ofFn α' := fun q ↦ by
    rw [List.mem_ofFn]
    exact ⟨(finCongr hlen).symm q, by rw [hα'e]; simp⟩
  -- a global certificate avoiding the query
  have hX : ((n - 1) * (d - 1) + 1) / 2 + d <
      ((cands.filter fun c ↦ c.1 ∉ List.ofFn α').map Prod.fst).toFinset.card := by
    have := card_filter_avoid cands (List.ofFn α')
    have hlen2 : (List.ofFn α').length = r := by simp [hlen]
    omega
  have hcop' : Nat.Coprime n d := hcop
  obtain ⟨⟨xs, ys, lam⟩, hcs⟩ := Option.ne_none_iff_exists'.mp
    (certSearch_complete hn2 hcop' hζ cands (List.ofFn α') (fun c hc' ↦ (hc c hc').1) hX)
  obtain ⟨hxl, hyl, hnd, hpts, hcert⟩ := certSearch_sound hn2 hcs
  have hζn : ζ ^ n = 1 := hζ.pow_eq_one
  have hζl : ∀ k, 0 < k → k < n → ζ ^ k ≠ 1 := fun k hk hkn ↦ hζ.pow_ne_one_of_pos_of_lt hk.ne' hkn
  have hE : ∀ i < xs.length, ys.getD i 0 ≠ 0 ∧ ys.getD i 0 ^ n = evalC fK (xs.getD i 0) := by
    intro i hi
    obtain ⟨c, hcm, -, hxc, k, -, hyk⟩ := hpts i hi
    obtain ⟨hc0, hcn⟩ := hc c hcm
    rw [hyk, hxc]
    refine ⟨mul_ne_zero (pow_ne_zero _ (hζ.ne_zero (by omega))) hc0, ?_⟩
    rw [mul_pow, ← pow_mul, mul_comm k n, pow_mul, hζn, one_pow, one_mul, hcn]
  have hxd : ∀ i < xs.length, ∀ j < xs.length, i ≠ j → xs.getD i 0 ≠ xs.getD j 0 := by
    intro i hi j hj hij h
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
    exact hij ((List.Nodup.getElem_inj_iff hnd).mp h)
  have hΓ' : ∀ q, β q ≠ 0 ∧ β q ^ n = evalC fK (α q) ∧ ∀ x ∈ xs, α q ≠ x := by
    intro q
    refine ⟨(hΓ q).1, (hΓ q).2, fun x hx h ↦ ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨c, -, hav, hxc, -⟩ := hpts i hi
    rw [List.getD_eq_getElem _ _ hi] at hxc
    apply hav
    rw [← hxc, ← h]
    exact hαmem q
  have hgen : (n - 1) * (fK.length - 1 - 1) ≤ 2 * xs.length := by
    rw [hxl]
    have : (n - 1) * (d - 1) = (n - 1) * (fK.length - 1 - 1) := rfl
    omega
  obtain ⟨B0, hB0⟩ := torsOracleG_eventually hmZ hM1 hn2 hd hlc hsq hcop hζn hζl hgen hyl hE hxd
    (by rw [hxl] at hcert ⊢; exact hcert) α β mq hΓ' hinj
  refine ⟨B0, fun B hB ↦ ?_⟩
  unfold torsOracleFB
  split
  · simp
  · rw [torsOracleC_congr (nfRedAt (M := M) mZl) (certProvG fK n ζ cands) (globalCert ζ xs ys lam)
      _ _ fK n l (fun p _ R ↦ by unfold certProvG; rw [hcs])]
    exact hB0 B hB

end Eventually

end Sup
