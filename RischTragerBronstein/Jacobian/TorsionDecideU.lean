import RischTragerBronstein.Jacobian.GoodPrimes

/-!
# An unconditional torsion decision

`goodData p` searches `E₀` modulo `p` (`findE0`) and checks `goodPrime`. By
`exists_goodPrime` and the completeness of `findE0` (`findE0_good`), the search over `p` terminates,
so `torsionDecideU` (two good primes found by `Nat.find`, then `torsionDecide`) is a total
decision procedure: `torsionDecideU_iff`.
-/

open Polynomial CPoly CPoly.Kron

namespace Jac

lemma sqrtMod_spec {p : ℕ} {c y : ℤ} (h : sqrtMod p c = some y) :
    0 < y ∧ y < p ∧ (p : ℤ) ∣ y ^ 2 - c := by
  unfold sqrtMod at h
  obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.mp h
  have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hy')
  have hp := List.find?_some hy'
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
  refine ⟨by simp only [Int.ofNat_eq_natCast]; omega, by simp only [Int.ofNat_eq_natCast]; omega,
    Int.dvd_of_emod_eq_zero hp.2⟩

lemma sqrtMod_isSome {p : ℕ} {c : ℤ} (hp : 0 < p) {y : ℤ} (hy : ¬ (p : ℤ) ∣ y)
    (hyc : (p : ℤ) ∣ y ^ 2 - c) : (sqrtMod p c).isSome := by
  unfold sqrtMod
  rw [Option.isSome_map, List.find?_isSome]
  refine ⟨(y % p).toNat, List.mem_range.mpr ?_, ?_⟩
  · have := Int.emod_lt_of_pos y (show (0 : ℤ) < p by exact_mod_cast hp); omega
  · have h0 : 0 ≤ y % p := Int.emod_nonneg y (by exact_mod_cast hp.ne')
    have e : (((y % p).toNat : ℕ) : ℤ) = y % p := Int.toNat_of_nonneg h0
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, e]
    refine ⟨fun h ↦ hy ?_, ?_⟩
    · have : y % p = 0 := by omega
      exact Int.dvd_of_emod_eq_zero this
    · have : (y % p) ^ 2 - c ≡ y ^ 2 - c [ZMOD p] :=
        Int.ModEq.sub_right _ (Int.ModEq.pow _ (Int.mod_modEq y p))
      apply Int.emod_eq_zero_of_dvd
      have h2 := dvd_sub hyc this.dvd
      rwa [sub_sub_cancel] at h2

lemma evalC_modEq (f : List ℤ) {a b n : ℤ} (h : a ≡ b [ZMOD n]) :
    evalC f a ≡ evalC f b [ZMOD n] := by
  induction f with
  | nil => exact Int.ModEq.refl _
  | cons c f ih =>
    simp only [evalC, List.foldr_cons] at ih ⊢
    exact Int.ModEq.add_left c (Int.ModEq.mul h ih)

/-- **`findE0` is complete**: if some `E₀` makes `p` good, `findE0` finds one. -/
lemma findE0_good {p : ℕ} [hp : Fact p.Prime] {f : List ℤ} {g : ℕ} {Γ : EDiv ℤ}
    {xs' ys' : List ℤ} (h : goodPrime p f g Γ xs' ys') :
    ∃ xs ys, findE0 p f g Γ = some (xs, ys) ∧ goodPrime p f g Γ xs ys := by
  classical
  obtain ⟨⟨hp2, hlen, hlc, hxl, hyl, hE, hxd, hΓ, hΓd⟩, hsf⟩ := h
  have hp0 : 0 < p := hp.out.pos
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  set F : ℕ → Option (ℤ × ℤ) := fun x : ℕ ↦
    if Γ.all (fun q ↦ (q.1 - (x : ℤ)) % (p : ℤ) != 0) then
      (sqrtMod p (evalC f (x : ℤ))).map fun y ↦ ((x : ℤ), y)
    else none with hF
  set cands := (List.range p).filterMap F with hc
  have hF_spec : ∀ r c, F r = some c → c.1 = r ∧ (∀ q ∈ Γ, ¬ (p : ℤ) ∣ q.1 - r) ∧
      0 < c.2 ∧ c.2 < p ∧ (p : ℤ) ∣ c.2 ^ 2 - evalC f r := by
    intro r c hrc
    simp only [F] at hrc
    split_ifs at hrc with hall
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hrc
    obtain ⟨h1, h2, h3⟩ := sqrtMod_spec hy
    refine ⟨rfl, fun q hq hd ↦ ?_, h1, h2, h3⟩
    have := List.all_eq_true.mp hall q hq
    simp only [bne_iff_ne, ne_eq] at this
    exact this (Int.emod_eq_zero_of_dvd hd)
  have hmem : ∀ c ∈ cands, ∃ r, r < p ∧ F r = some c := by
    intro c hcm
    obtain ⟨r, hr, hrc⟩ := List.mem_filterMap.mp hcm
    exact ⟨r, List.mem_range.mp hr, hrc⟩
  have hcount : g ≤ cands.length := by
    set L := xs'.map fun x : ℤ ↦ (x % (p : ℤ)).toNat
    have hLnd : L.Nodup := by
      simp only [L, List.Nodup]
      rw [List.pairwise_map]
      refine hxd.imp fun {u v} huv he ↦ huv ?_
      have hu0 := Int.emod_nonneg u hpz
      have hv0 := Int.emod_nonneg v hpz
      have e : u % p = v % p := by
        have := congrArg (fun n : ℕ ↦ (n : ℤ)) he
        simpa [Int.toNat_of_nonneg hu0, Int.toNat_of_nonneg hv0] using this
      exact Int.ModEq.dvd (Int.ModEq.symm e)
    have hsub : L ⊆ (List.range p).filter fun r ↦ (F r).isSome := by
      intro r hr
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hx0 := Int.emod_nonneg xs'[i] hpz
      have hxlt := Int.emod_lt_of_pos xs'[i] (show (0 : ℤ) < p by exact_mod_cast hp0)
      have e : (((xs'[i] % p).toNat : ℕ) : ℤ) = xs'[i] % p := Int.toNat_of_nonneg hx0
      have hmod : (((xs'[i] % p).toNat : ℕ) : ℤ) ≡ xs'[i] [ZMOD p] := by
        rw [e]; exact Int.mod_modEq _ _
      rw [List.mem_filter, List.mem_range]
      refine ⟨by omega, ?_⟩
      have hig : i < g := hxl ▸ hi
      obtain ⟨hdv, hnd⟩ := hE i (List.mem_range.mpr hig)
      rw [List.getD_eq_getElem _ _ hi] at hdv
      simp only [F]
      rw [if_pos]
      · rw [Option.isSome_map]
        apply sqrtMod_isSome hp0 hnd
        have h2 := (evalC_modEq f hmod).dvd
        have := dvd_add hdv h2
        rwa [show ys'.getD i 0 ^ 2 - evalC f xs'[i] +
            (evalC f xs'[i] - evalC f (((xs'[i] % p).toNat : ℕ) : ℤ)) =
            ys'.getD i 0 ^ 2 - evalC f (((xs'[i] % p).toNat : ℕ) : ℤ) by ring] at this
      · refine List.all_eq_true.mpr fun q hq ↦ ?_
        simp only [bne_iff_ne, ne_eq]
        intro h0
        apply (hΓ q hq).2.2 xs'[i] (List.getElem_mem hi)
        have h1 := Int.dvd_of_emod_eq_zero h0
        have h2 := hmod.dvd
        have := dvd_sub h1 h2
        rwa [show q.1 - (((xs'[i] % p).toNat : ℕ) : ℤ) -
            (xs'[i] - (((xs'[i] % p).toNat : ℕ) : ℤ)) = q.1 - xs'[i] by ring] at this
    have := (hLnd.subperm hsub).length_le
    rw [List.length_map, hxl, ← List.countP_eq_length_filter,
      ← List.length_filterMap_eq_countP] at this
    exact this
  have hfind : findE0 p f g Γ =
      some ((cands.take g).map (·.1), (cands.take g).map (·.2)) := by
    unfold findE0
    dsimp only
    split_ifs with hlt
    · exact absurd hlt (not_lt.mpr hcount)
    · rfl
  have htl : (cands.take g).length = g := by rw [List.length_take]; omega
  refine ⟨_, _, hfind, ⟨hp2, hlen, hlc, by rw [List.length_map, htl], by rw [List.length_map, htl],
    ?_, ?_, ?_, hΓd⟩, hsf⟩
  · intro i hi
    have hi' : i < (cands.take g).length := by rw [htl]; exact List.mem_range.mp hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getD_eq_getElem _ _ (by simpa using hi')]
    simp only [List.getElem_map]
    obtain ⟨r, -, hrc⟩ := hmem _ (List.mem_of_mem_take (List.getElem_mem hi'))
    obtain ⟨e1, -, h1, h2, h3⟩ := hF_spec r _ hrc
    rw [e1]
    refine ⟨h3, fun hd ↦ ?_⟩
    have := Int.le_of_dvd h1 hd
    omega
  · have hpw : cands.Pairwise fun c c' ↦ c.1 < c'.1 := by
      refine List.Pairwise.filterMap F ?_ List.pairwise_lt_range
      intro a a' haa' b hb b' hb'
      rw [(hF_spec a b hb).1, (hF_spec a' b' hb').1]
      exact_mod_cast haa'
    rw [List.pairwise_map]
    refine (hpw.sublist (List.take_sublist g cands)).imp_of_mem fun {c c'} hc hc' hlt hd ↦ ?_
    obtain ⟨r, hr, hrc⟩ := hmem c (List.mem_of_mem_take hc)
    obtain ⟨r', hr', hrc'⟩ := hmem c' (List.mem_of_mem_take hc')
    rw [(hF_spec r c hrc).1, (hF_spec r' c' hrc').1] at hlt hd
    have := Int.le_of_dvd (by omega) (dvd_sub_comm.mp hd)
    omega
  · intro q hq
    refine ⟨(hΓ q hq).1, (hΓ q hq).2.1, fun x hx ↦ ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨r, -, hrc⟩ := hmem c (List.mem_of_mem_take hc)
    obtain ⟨e1, hΓr, -⟩ := hF_spec r c hrc
    rw [e1]
    exact hΓr q hq

/-- Search for `E₀` modulo `p` and check that `p` is a good prime. -/
def goodData (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (p : ℕ) : Option (List ℤ × List ℤ) :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    match findE0 p f g Γ with
    | some d => if goodPrime p f g Γ d.1 d.2 then some d else none
    | none => none
  else none

variable {f : List ℤ} {g : ℕ} {Γ : EDiv ℤ}

lemma goodData_prime {p : ℕ} {d : List ℤ × List ℤ} (h : goodData f g Γ p = some d) :
    p.Prime := by
  unfold goodData at h
  split_ifs at h with hp
  exact hp

lemma goodData_good {p : ℕ} {d : List ℤ × List ℤ} (h : goodData f g Γ p = some d) :
    @goodPrime p ⟨goodData_prime h⟩ f g Γ d.1 d.2 := by
  have hp := goodData_prime h
  unfold goodData at h
  rw [dif_pos hp] at h
  split at h
  · split_ifs at h with hg
    cases h; exact hg
  · cases h

lemma goodData_isSome {p : ℕ} (hp : p.Prime) {xs ys : List ℤ}
    (h : @goodPrime p ⟨hp⟩ f g Γ xs ys) : (goodData f g Γ p).isSome := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨xs', ys', hfind, hgood⟩ := findE0_good h
  unfold goodData
  rw [dif_pos hp]
  split
  · rename_i d hd
    rw [hfind] at hd
    cases hd
    rw [if_pos hgood]; rfl
  · rename_i hd
    rw [hfind] at hd
    cases hd

/-- The hypotheses of the unconditional decision. -/
structure Hyp (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) : Prop where
  hlen : f.length = 2 * g + 2
  hlc : f.getD (2 * g + 1) 0 ≠ 0
  hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ))
  hΓ : ∀ q ∈ Γ, q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = evalC f q.1
  hΓd : Γ.Pairwise fun u v ↦ u.1 ≠ v.1

lemma exists_goodData (H : Hyp f g Γ) (N : ℕ) : ∃ p, N < p ∧ (goodData f g Γ p).isSome := by
  obtain ⟨p, hp, hNp, xs, ys, hg⟩ := exists_goodPrime H.hlen H.hlc H.hsq H.hΓ H.hΓd N
  exact ⟨p, hNp, goodData_isSome hp hg⟩

/-- The first good prime. -/
def prime1 (H : Hyp f g Γ) : ℕ := Nat.find (exists_goodData H 0)

/-- The next good prime. -/
def prime2 (H : Hyp f g Γ) : ℕ := Nat.find (exists_goodData H (prime1 H))

/-- **The unconditional torsion decision.** -/
def torsionDecideU (H : Hyp f g Γ) : Bool :=
  match hp : goodData f g Γ (prime1 H), hq : goodData f g Γ (prime2 H) with
  | some dp, some dq =>
    haveI : Fact (prime1 H).Prime := ⟨goodData_prime hp⟩
    haveI : Fact (prime2 H).Prime := ⟨goodData_prime hq⟩
    torsionDecide f g Γ (prime1 H) (prime2 H) dp.1 dp.2 dq.1 dq.2 (goodData_good hp)
      (goodData_good hq)
  | _, _ => false

/-- **`torsionDecideU` decides torsion**: it answers `true` iff some positive multiple of `Γ`
is principal over `ℚ`. -/
theorem torsionDecideU_iff (H : Hyp f g Γ) :
    torsionDecideU H = true ↔ ∃ n, 1 ≤ n ∧ PrincipalMul ((toPoly f).map (Int.castRingHom ℚ)) g
      (emap (Int.castRingHom ℚ) Γ) n := by
  have h1 := (Nat.find_spec (exists_goodData H 0)).2
  have h2 := Nat.find_spec (exists_goodData H (prime1 H))
  have hpq : prime1 H ≠ prime2 H := Nat.ne_of_lt h2.1
  obtain ⟨dp, hdp⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨dq, hdq⟩ := Option.isSome_iff_exists.mp h2.2
  unfold torsionDecideU
  split
  · rename_i dp' dq' hp hq
    have : Fact (prime1 H).Prime := ⟨goodData_prime hp⟩
    have : Fact (prime2 H).Prime := ⟨goodData_prime hq⟩
    exact torsionDecide_iff hpq _ _
  · rename_i hne
    exfalso
    exact hne dp dq hdp hdq

end Jac
