import RischTragerBronstein.Jacobian.TorsionDecideK
import RischTragerBronstein.Jacobian.NFReduce
import RischTragerBronstein.Jacobian.TorsionDecideU
import RischTragerBronstein.Algebraic.GoodPrime
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Good primes exist over a number field

* `findE0K_good`: if `g` distinct residues avoid the reduced abscissae and take non-zero square
  values, `findE0K` succeeds, with the base-point conditions of `baseCheck`.
-/

open Polynomial CPoly CPoly.Kron EllAlgo

namespace Jac

lemma findE0K_good {p : ℕ} [hp : Fact p.Prime] {f : List ℤ} {g : ℕ} {xsb : List (ZMod p)}
    (hcand : ∃ L : List ℕ, L.Nodup ∧ g ≤ L.length ∧ ∀ r ∈ L, r < p ∧
      (∀ a ∈ xsb, a - (r : ZMod p) ≠ 0) ∧ (sqrtMod p (evalC f r)).isSome) :
    ∃ xs ys, findE0K p f g xsb = some (xs, ys) ∧ xs.length = g ∧ ys.length = g ∧
      (∀ i ∈ List.range g, (p : ℤ) ∣ ys.getD i 0 ^ 2 - evalC f (xs.getD i 0) ∧
        ¬ (p : ℤ) ∣ ys.getD i 0) ∧
      xs.Pairwise (fun u v ↦ ¬ (p : ℤ) ∣ u - v) ∧
      ∀ x ∈ xs, ∀ a ∈ xsb, a - (x : ZMod p) ≠ 0 := by
  classical
  obtain ⟨L, hLnd, hLlen, hL⟩ := hcand
  have hp0 : 0 < p := hp.out.pos
  set F : ℕ → Option (ℤ × ℤ) := fun x : ℕ ↦
    if xsb.all (fun a ↦ a - (x : ZMod p) != 0) then
      (sqrtMod p (evalC f (x : ℤ))).map fun y ↦ ((x : ℤ), y)
    else none with hF
  set cands := (List.range p).filterMap F with hc
  have hF_spec : ∀ r c, F r = some c → c.1 = r ∧ (∀ a ∈ xsb, a - (r : ZMod p) ≠ 0) ∧
      0 < c.2 ∧ c.2 < p ∧ (p : ℤ) ∣ c.2 ^ 2 - evalC f r := by
    intro r c hrc
    simp only [F] at hrc
    split_ifs at hrc with hall
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hrc
    obtain ⟨h1, h2, h3⟩ := sqrtMod_spec hy
    refine ⟨rfl, fun a ha ↦ ?_, h1, h2, h3⟩
    have := List.all_eq_true.mp hall a ha
    simpa using this
  have hmem : ∀ c ∈ cands, ∃ r, r < p ∧ F r = some c := by
    intro c hcm
    obtain ⟨r, hr, hrc⟩ := List.mem_filterMap.mp hcm
    exact ⟨r, List.mem_range.mp hr, hrc⟩
  have hcount : g ≤ cands.length := by
    have hsub : L ⊆ (List.range p).filter fun r ↦ (F r).isSome := by
      intro r hr
      obtain ⟨h1, h2, h3⟩ := hL r hr
      rw [List.mem_filter, List.mem_range]
      refine ⟨h1, ?_⟩
      simp only [F]
      rw [if_pos (List.all_eq_true.mpr fun a ha ↦ by simpa using h2 a ha), Option.isSome_map]
      exact h3
    have := (hLnd.subperm hsub).length_le
    rw [← List.countP_eq_length_filter, ← List.length_filterMap_eq_countP] at this
    exact le_trans hLlen this
  have hfind : findE0K p f g xsb =
      some ((cands.take g).map (·.1), (cands.take g).map (·.2)) := by
    unfold findE0K
    dsimp only
    split_ifs with hlt
    · exact absurd hlt (not_lt.mpr hcount)
    · rfl
  have htl : (cands.take g).length = g := by rw [List.length_take]; omega
  refine ⟨_, _, hfind, by rw [List.length_map, htl], by rw [List.length_map, htl], ?_, ?_, ?_⟩
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
  · intro x hx a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨r, -, hrc⟩ := hmem c (List.mem_of_mem_take hc)
    obtain ⟨e1, hr, -⟩ := hF_spec r c hrc
    rw [e1, Int.cast_natCast]
    exact hr a ha

lemma pIntL_of_lt {p : ℕ} {l : CPoly ℚ} (h : ∀ c ∈ l, c.den < p) : pIntL p l = true := by
  simp only [pIntL, List.all_eq_true, bne_iff_ne, ne_eq]
  intro c hc h0
  have := h c hc
  rw [Nat.mod_eq_of_lt this] at h0
  exact c.den_nz h0

lemma den_le_sum {l : CPoly ℚ} {c : ℚ} (hc : c ∈ l) : c.den ≤ (l.map (·.den)).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem hc)

section Exist

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

/-- **Good primes exist** for a divisor over `K = NF M`, when base points with `x ∈ ℤ` and
`y ∈ K` are available. -/
theorem exists_goodK (hMZ : ∀ q ∈ M, q.den = 1) {f : List ℤ} {g : ℕ}
    (hlen : f.length = 2 * g + 2) (hlc : f.getD (2 * g + 1) 0 ≠ 0)
    (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ))) (hM1 : 0 < (toPoly M).natDegree)
    (Γ : EDiv (NFC.NF M)) (hΓ : ∀ q ∈ Γ, q.2.1 ≠ 0) (hΓd : Γ.Pairwise fun u v ↦ u.1 ≠ v.1)
    (as : List ℤ) (bs : List (NFC.NF M)) (hasl : as.length = g) (hbsl : bs.length = g)
    (hab : ∀ i (hi : i < g), bs[i]'(by omega) * bs[i]'(by omega) =
      ((evalC f (as[i]'(by omega)) : ℤ) : NFC.NF M) ∧ bs[i]'(by omega) ≠ 0)
    (hasnd : as.Nodup) (hΓa : ∀ q ∈ Γ, ∀ a ∈ as, q.1 ≠ (a : NFC.NF M)) (N : ℕ) :
    ∃ p, N < p ∧ (goodK (M.map Rat.num) f g Γ p).isSome := by
  classical
  set mZ := M.map Rat.num
  have hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ) := (Kron.polyZ_map M hMZ).symm
  set F : ℤ[X] := toPoly mZ
  have hF0 : 0 < F.natDegree := by
    rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)), ← hmZ]
    exact hM1
  -- the elements whose reductions matter
  set Els : List (NFC.NF M) :=
    Γ.flatMap (fun q ↦ [q.1, q.2.1, q.2.1⁻¹]) ++
    Γ.flatMap (fun q ↦ Γ.flatMap fun q' ↦ [q.1 - q'.1, (q.1 - q'.1)⁻¹]) ++
    Γ.flatMap (fun q ↦ as.flatMap fun a : ℤ ↦ [q.1 - (a : NFC.NF M), (q.1 - (a : NFC.NF M))⁻¹,
      (a : NFC.NF M)]) ++
    bs ++ bs.map (·⁻¹) ++ bs.map (fun b ↦ b * b) ++
    as.map (fun a : ℤ ↦ ((evalC f a : ℤ) : NFC.NF M))
  set Td := (Els.map fun x ↦ (x.1.map (·.den)).sum).sum
  obtain ⟨P, Q, d, hd0, hPQ⟩ := exists_bezout_int hsq
  set Ta := (as.map fun a ↦ a.natAbs).sum
  set T := N + 3 + (f.getD (2 * g + 1) 0).natAbs + d.natAbs + Td + 2 * Ta
  obtain ⟨u, v, -, -, huv⟩ := exists_mul_add_mul_eq_C_resultant F (derivative F) le_rfl le_rfl
    (Or.inl hF0.ne')
  set R := resultant F (derivative F)
  have hR0 : R ≠ 0 := by
    intro h0
    have hmap := resultant_map_map F (derivative F) F.natDegree (derivative F).natDegree
      (Int.castRingHom ℚ)
    rw [← show R = resultant F (derivative F) from rfl, h0, map_zero] at hmap
    have hsepM : (toPoly M).Separable := (Irreducible.separable (Fact.out))
    rw [hmZ] at hsepM
    have hne := resultant_ne_zero (F.map (Int.castRingHom ℚ)) _ (hsepM : IsCoprime _ _)
    rw [derivative_map, natDegree_map_eq_of_injective (RingHom.injective_int _),
      natDegree_map_eq_of_injective (RingHom.injective_int _)] at hne
    exact hne hmap
  obtain ⟨p, hp, hpS, n, hn⟩ := Schur.exists_prime_dvd_eval F hF0
    (Finset.range (T + 1) ∪ Nat.primeFactors R.natAbs)
  have hpT : T < p := by
    by_contra h; exact hpS (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega)))
  have hpR : ¬ (p : ℤ) ∣ R := fun h ↦ hpS (Finset.mem_union_right _
    (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hR0⟩))
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p, by omega, ?_⟩
  have hp0 : 0 < p := hp.pos
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hp2 : p ≠ 2 := by omega
  -- the root and its lift
  set s : ZMod p := (n : ZMod p)
  have hs : (F.map (Int.castRingHom (ZMod p))).eval s = 0 := by
    rw [eval_map, eval₂_at_intCast, eq_intCast, Int.cast_id,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hn]
  have hs' : ((derivative F).map (Int.castRingHom (ZMod p))).eval s ≠ 0 := by
    intro h0
    apply hpR
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrArg (fun P : ℤ[X] ↦ (P.map (Int.castRingHom (ZMod p))).eval s) huv
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, map_C, eval_C] at this
    simp only [hs, h0, mul_zero, zero_mul, zero_add, eq_intCast] at this
    exact this.symm
  obtain ⟨z, hz, hzs⟩ := hensel_root_red F s hs hs'
  -- integrality of the relevant elements
  have hpI : ∀ x ∈ Els, pIntL p x.1 = true := fun x hx ↦ pIntL_of_lt fun c hc ↦ by
    have h1 := den_le_sum hc
    have h2 : (x.1.map (·.den)).sum ≤ Td := List.le_sum_of_mem (List.mem_map_of_mem
      (f := fun x : NFC.NF M ↦ (x.1.map (·.den)).sum) hx)
    omega
  have mem1 : ∀ q ∈ Γ, q.1 ∈ Els ∧ q.2.1 ∈ Els ∧ q.2.1⁻¹ ∈ Els := fun q hq ↦ by
    simp only [Els, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map]
    exact ⟨Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨q, hq, by simp⟩))))),
      Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨q, hq, by simp⟩))))),
      Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨q, hq, by simp⟩)))))⟩
  have mem2 : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q'.1 ∈ Els ∧ (q.1 - q'.1)⁻¹ ∈ Els := fun q hq q' hq' ↦ by
    simp only [Els, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map]
    exact ⟨Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, q', hq', by simp⟩))))),
      Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, q', hq', by simp⟩)))))⟩
  have mem3 : ∀ q ∈ Γ, ∀ a ∈ as, q.1 - (a : NFC.NF M) ∈ Els ∧ (q.1 - (a : NFC.NF M))⁻¹ ∈ Els ∧
      (a : NFC.NF M) ∈ Els := fun q hq a ha ↦ by
    simp only [Els, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map]
    exact ⟨Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, a, ha, by simp⟩)))),
      Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, a, ha, by simp⟩)))),
      Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, a, ha, by simp⟩))))⟩
  have mem4 : ∀ b ∈ bs, b ∈ Els ∧ b⁻¹ ∈ Els ∧ b * b ∈ Els := fun b hb ↦ by
    simp only [Els, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map]
    exact ⟨Or.inl (Or.inl (Or.inl (Or.inr hb))), Or.inl (Or.inl (Or.inr ⟨b, hb, rfl⟩)),
      Or.inl (Or.inr ⟨b, hb, rfl⟩)⟩
  have mem5 : ∀ a ∈ as, ((evalC f a : ℤ) : NFC.NF M) ∈ Els := fun a ha ↦ by
    simp only [Els, List.mem_append, List.mem_map]
    exact Or.inr ⟨a, ha, rfl⟩
  -- the reductions (with `s = z mod p`)
  have hzs' : PadicInt.toZMod z = s := hzs
  have R1 : ∀ q ∈ Γ, redL p s q.2.1.1 ≠ 0 := fun q hq ↦ by
    rw [← hzs']
    exact redL_ne_zero F hmZ z hz (hΓ q hq) (hpI _ (mem1 q hq).2.1) (hpI _ (mem1 q hq).2.2)
  have R2 : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 ≠ q'.1 → redL p s q.1.1 ≠ redL p s q'.1.1 := by
    intro q hq q' hq' hne
    rw [← hzs', ← sub_ne_zero, ← redL_sub F hmZ z hz (hpI _ (mem1 q hq).1) (hpI _ (mem1 q' hq').1)
      (hpI _ (mem2 q hq q' hq').1)]
    exact redL_ne_zero F hmZ z hz (sub_ne_zero.mpr hne) (hpI _ (mem2 q hq q' hq').1)
      (hpI _ (mem2 q hq q' hq').2)
  have R3 : ∀ q ∈ Γ, ∀ a ∈ as, redL p s q.1.1 - (a : ZMod p) ≠ 0 := by
    intro q hq a ha
    obtain ⟨h1, h2, h3⟩ := mem3 q hq a ha
    rw [← hzs', ← redL_intCast F hmZ z hz a (hpI _ h3), ← redL_sub F hmZ z hz
      (hpI _ (mem1 q hq).1) (hpI _ h3) (hpI _ h1)]
    exact redL_ne_zero F hmZ z hz (sub_ne_zero.mpr (hΓa q hq a ha)) (hpI _ h1) (hpI _ h2)
  have R4 : ∀ i (hi : i < g), redL p s (bs[i]'(by omega)).1 ≠ 0 ∧
      redL p s (bs[i]'(by omega)).1 ^ 2 = ((evalC f (as[i]'(by omega)) : ℤ) : ZMod p) := by
    intro i hi
    have hb := List.getElem_mem (l := bs) (by omega : i < bs.length)
    have ha := List.getElem_mem (l := as) (by omega : i < as.length)
    obtain ⟨h1, h2, h3⟩ := mem4 _ hb
    refine ⟨by rw [← hzs']; exact redL_ne_zero F hmZ z hz (hab i hi).2 (hpI _ h1) (hpI _ h2), ?_⟩
    rw [← hzs', sq, ← redL_mul F hmZ z hz (hpI _ h1) (hpI _ h1) (hpI _ h3), (hab i hi).1,
      redL_intCast F hmZ z hz _ (by rw [← (hab i hi).1]; exact hpI _ h3)]
  -- the base points `aᵢ mod p`
  have hTa : ∀ a ∈ as, a.natAbs ≤ Ta := fun a ha ↦
    List.le_sum_of_mem (List.mem_map_of_mem (f := fun a : ℤ ↦ a.natAbs) ha)
  have hcast : ∀ a : ℤ, (((a % (p : ℤ)).toNat : ℕ) : ZMod p) = (a : ZMod p) := by
    intro a
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hpz), ZMod.intCast_mod]
  set L := as.map fun a : ℤ ↦ (a % (p : ℤ)).toNat
  have hLnd : L.Nodup := by
    refine hasnd.map_on fun a ha a' ha' he ↦ ?_
    by_contra hne
    have h1 : ((a : ZMod p)) = (a' : ZMod p) := by rw [← hcast, ← hcast, he]
    have h2 : (p : ℤ) ∣ a - a' := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h1, sub_self]
    exact not_dvd_of_natAbs_lt (sub_ne_zero.mpr hne) (by
      have := Int.natAbs_sub_le a a'; have := hTa a ha; have := hTa a' ha'; omega) h2
  have hcand : ∃ L : List ℕ, L.Nodup ∧ g ≤ L.length ∧ ∀ r ∈ L, r < p ∧
      (∀ a ∈ Γ.map (fun q ↦ redL p s q.1.1), a - (r : ZMod p) ≠ 0) ∧
      (sqrtMod p (evalC f r)).isSome := by
    refine ⟨L, hLnd, by simp [L, hasl], fun r hr ↦ ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hig : i < g := by omega
    refine ⟨?_, ?_, ?_⟩
    · have := Int.emod_lt_of_pos as[i] (show (0 : ℤ) < p by exact_mod_cast hp0)
      have h0 := Int.emod_nonneg as[i] hpz
      omega
    · intro c hc
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
      rw [hcast]
      exact R3 q hq _ ha
    · obtain ⟨hb0, hb2⟩ := R4 i hig
      set y : ℤ := ((redL p s (bs[i]'(by omega)).1).val : ℤ)
      have hy : (y : ZMod p) = redL p s (bs[i]'(by omega)).1 := by simp [y]
      apply sqrtMod_isSome hp0 (y := y)
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hy]; exact hb0
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hmod : ((((as[i] % (p : ℤ)).toNat : ℕ) : ℤ)) ≡ as[i] [ZMOD p] := by
          rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hpz)]; exact Int.mod_modEq _ _
        have he := (ZMod.intCast_eq_intCast_iff _ _ p).mpr (evalC_modEq f hmod)
        push_cast
        rw [he, hy, hb2, sub_self]
  obtain ⟨xs, ys, hfind, hxl, hyl, hE, hxd, havoid⟩ := findE0K_good (f := f) (g := g) hcand
  -- the prime is good
  unfold goodK
  rw [dif_pos hp, List.findSome?_isSome_iff]
  refine ⟨s.val, List.mem_range.mpr (ZMod.val_lt s), ?_⟩
  simp only [ZMod.natCast_zmod_val]
  rw [hfind]
  dsimp only
  rw [if_pos]
  · rfl
  refine ⟨⟨⟨hp2, hlen, not_dvd_of_natAbs_lt hlc (by omega), hxl, hyl, hE, hxd, by simp, by simp⟩,
    ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [evalC_eq, castL_eq]; exact hs
  · rw [evalC_eq, toPoly_deriv, castL_eq, derivative_map]; exact hs'
  · intro q hq
    exact ⟨hpI _ (mem1 q hq).1, hpI _ (mem1 q hq).2.1,
      mul_ne_zero (two_ne_zero_zmod hp2) (R1 q hq),
      fun x hx ↦ havoid x hx _ (List.mem_map_of_mem hq)⟩
  · exact hΓd.imp_of_mem fun {u v} hu hv huv ↦ R2 u hu v hv huv
  · apply squarefreeCheck_complete
    rw [castL_eq, derivative_map]
    set φ := Int.castRingHom (ZMod p)
    have hmap := congrArg (Polynomial.map φ) hPQ
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hmap
    have hd : φ d ≠ 0 := by
      rw [eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact not_dvd_of_natAbs_lt hd0 (by omega)
    refine ⟨C (φ d)⁻¹ * P.map φ, C (φ d)⁻¹ * Q.map φ, ?_⟩
    have : C (φ d)⁻¹ * C (φ d) = (1 : (ZMod p)[X]) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hd, C_1]
    linear_combination C (φ d)⁻¹ * hmap + this

end Exist

end Jac
