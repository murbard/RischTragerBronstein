import RischTragerBronstein.Computable.KronCert

/-!
# Completeness of Kronecker's factorisation

* `ptsFor_length`: there are always enough evaluation points;
* `lagr_eval`, `natDegree_lagr_le`: the Lagrange interpolant interpolates, with degree `< n`;
* `noFactor_complete`, `irredQ_complete`: the irreducibility certificate accepts every primitive
  integral irreducible polynomial;
* `findFactor_complete`: the search finds a factor of every reducible primitive integral polynomial
  (Gauss's lemma and uniqueness of interpolation).
-/

open Polynomial

namespace CPoly

namespace Kron

/-! ### Enough points -/

lemma natDegree_lt_length (F : CPoly ℚ) (hF0 : toPoly F ≠ 0) : (toPoly F).natDegree < F.length := by
  by_contra h
  push_neg at h
  apply hF0
  have hc : (toPoly F).coeff (toPoly F).natDegree = 0 := by
    rw [coeff_toPoly]; exact List.getD_eq_default _ _ h
  exact leadingCoeff_eq_zero.mp hc

lemma length_candPts (n : ℕ) : (candPts n).length = n := by simp [candPts]

lemma ptsFor_length (F : CPoly ℚ) (hF0 : toPoly F ≠ 0) (k : ℕ) : (ptsFor F k).length = k := by
  classical
  unfold ptsFor
  rw [List.length_take, min_eq_left]
  set L := candPts (F.length + k)
  have hL := candPts_nodup (F.length + k)
  set P : ℤ → Bool := fun a ↦ decide (evalC F (Int.cast a : ℚ) ≠ 0) with hP
  have hsum := List.length_eq_length_filter_add (l := L) P
  rw [length_candPts] at hsum
  -- the roots among the candidates
  have hroots : (L.filter fun a ↦ !P a).length < F.length := by
    have hsub : ((L.filter fun a ↦ !P a).map (fun a : ℤ ↦ (a : ℚ))).toFinset ⊆
        (toPoly F).roots.toFinset := by
      intro q hq
      simp only [List.mem_toFinset, List.mem_map, List.mem_filter, hP, Bool.not_eq_true',
        decide_eq_false_iff_not, not_not] at hq
      obtain ⟨a, ⟨-, ha⟩, rfl⟩ := hq
      rw [Multiset.mem_toFinset, mem_roots hF0, IsRoot, ← evalC_eq]
      exact ha
    have h1 := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup ((hL.filter _).map Int.cast_injective), List.length_map] at h1
    have h2 := (Multiset.toFinset_card_le (toPoly F).roots).trans (card_roots' (toPoly F))
    have h3 := natDegree_lt_length F hF0
    exact lt_of_le_of_lt (h1.trans h2) h3
  have hgoal : (L.filter fun a : ℤ ↦ evalC F (Int.cast a : ℚ) ≠ 0) = L.filter P := rfl
  rw [hgoal]
  omega

/-! ### Lagrange interpolation -/

lemma trim_length_le_of_natDegree {g : CPoly ℚ} {e : ℕ} (h : (toPoly g).natDegree ≤ e) :
    (trim g).length ≤ e + 1 := by
  by_cases hg : trim g = []
  · rw [hg]; simp
  · rw [length_trim hg]; omega

/-! ### The irreducibility certificate is complete -/

/-- **`noFactor` is complete**: without a factor of degree `e`, the search refutes every
candidate. -/
theorem noFactor_complete (F : CPoly ℚ) (hF0 : toPoly F ≠ 0) (e : ℕ)
    (hno : ∀ g : ℚ[X], g ∣ toPoly F → g.natDegree ≠ e) : noFactor F e = true := by
  classical
  simp only [noFactor, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true']
  set pts := ptsFor F (e + 1) with hpts
  have hlen : pts.length = e + 1 := ptsFor_length F hF0 (e + 1)
  have hndQ : (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)).Nodup :=
    (ptsFor_nodup F (e + 1)).map Int.cast_injective
  refine ⟨hlen, fun ds hds ↦ ?_⟩
  have hdl : ds.length = pts.length := by
    have := (List.mem_sections.mp hds).length_eq
    simp only [List.length_map] at this
    exact this
  set g := lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) (ds.map fun d : ℤ ↦ (Int.cast d : ℚ))
    with hg
  have hgdeg : (toPoly g).natDegree ≤ e := by
    have := natDegree_lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) (ds.map fun d : ℤ ↦ (Int.cast d : ℚ))
    simp only [List.length_map, hlen, Nat.add_sub_cancel] at this
    exact this
  refine Or.inr ⟨⟨fun p hp ↦ ?_, trim_length_le_of_natDegree hgdeg⟩, ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    have hk' : k < pts.length := by simp at hk; omega
    have hkd : k < ds.length := by omega
    simp only [List.getElem_zip, beq_iff_eq]
    rw [evalC_eq]
    have := eval_lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) (ds.map fun d : ℤ ↦ (Int.cast d : ℚ))
      hndQ k (by simpa using hk')
    rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getD_eq_getElem _ _ (by simpa using hkd)]
      at this
    simpa using this
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hl, hz⟩ := hcon
    have htr : trim g ≠ [] := fun h0 ↦ by rw [h0] at hl; simp at hl
    have hdg : (toPoly g).natDegree = e := by rw [length_trim htr] at hl; omega
    have hg0 : toPoly g ≠ 0 := fun h0 ↦ htr ((trim_eq_nil_iff g).mpr h0)
    apply hno (toPoly g) _ hdg
    have hsp := divMod_spec F g
    have hz' : isZero (divMod F g).2 = true := by
      revert hz; cases isZero (divMod F g).2 <;> simp
    have hr : toPoly (divMod F g).2 = 0 := (isZero_iff _).mp hz'
    refine ⟨toPoly (divMod F g).1, ?_⟩
    rw [hsp, hr, add_zero, mul_comm]

lemma degC_eq (F : CPoly ℚ) (hF0 : toPoly F ≠ 0) : degC F = (toPoly F).natDegree := by
  have htr : trim F ≠ [] := fun h0 ↦ hF0 ((trim_eq_nil_iff F).mp h0)
  rw [degC, length_trim htr]; simp

/-- **`irredQ` is complete**: it accepts every primitive integral irreducible polynomial. -/
theorem irredQ_complete (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1)
    (hgcd : gcdL (F.map Rat.num) = 1) (hirr : Irreducible (toPoly F)) : irredQ F = true := by
  classical
  have hF0 : toPoly F ≠ 0 := hirr.ne_zero
  have hpos : 0 < (toPoly F).natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  simp only [irredQ, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
    degC_eq F hF0]
  refine ⟨⟨⟨fun q hq ↦ by simpa using hint q hq, hgcd⟩, hpos⟩, fun e he ↦ ?_⟩
  have he' := List.mem_range.mp he
  refine noFactor_complete F hF0 _ fun g hg hgd ↦ ?_
  obtain ⟨h, hh⟩ := hg
  have hg0 : g ≠ 0 := fun h0 ↦ hF0 (by rw [hh, h0, zero_mul])
  have hh0 : h ≠ 0 := fun h0 ↦ hF0 (by rw [hh, h0, mul_zero])
  have hsum : g.natDegree + h.natDegree = (toPoly F).natDegree := by
    rw [hh, natDegree_mul hg0 hh0]
  rcases hirr.isUnit_or_isUnit hh with hu | hu
  · have := natDegree_eq_zero_of_isUnit hu; omega
  · have := natDegree_eq_zero_of_isUnit hu; omega

lemma polyZ_ne_zero (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1) (hF0 : toPoly F ≠ 0) :
    polyZ F ≠ 0 := fun h0 ↦ hF0 (by rw [← polyZ_map F hint, h0, Polynomial.map_zero])

lemma natDegree_polyZ (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1) :
    (polyZ F).natDegree = (toPoly F).natDegree := by
  rw [← polyZ_map F hint, natDegree_map_eq_of_injective (RingHom.injective_int _)]

lemma polyZ_primitive (F : CPoly ℚ) (hgcd : gcdL (F.map Rat.num) = 1) :
    (polyZ F).IsPrimitive := by
  intro r hr
  have hdvd : r ∣ (gcdL (F.map Rat.num) : ℤ) := dvd_gcdL r _ fun a ha ↦ by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have := (Polynomial.C_dvd_iff_dvd_coeff r (polyZ F)).mp hr i
    rwa [polyZ, coeff_toPoly, List.getD_eq_getElem _ _ hi] at this
  rw [hgcd, Nat.cast_one] at hdvd
  exact isUnit_of_dvd_one hdvd

/-- **`findFactorDeg` is complete**: an integral factor of degree `e` is found. -/
theorem findFactorDeg_complete (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1) (e : ℕ)
    (hF0 : toPoly F ≠ 0) (G : ℤ[X]) (hG : G ∣ polyZ F) (hGd : G.natDegree = e) :
    findFactorDeg F e ≠ none := by
  classical
  unfold findFactorDeg
  intro hnone
  rw [List.findSome?_eq_none_iff] at hnone
  set pts := ptsFor F (e + 1) with hpts
  have hlen : pts.length = e + 1 := ptsFor_length F hF0 (e + 1)
  set GQ := G.map (Int.castRingHom ℚ) with hGQ
  have hFZ0 := polyZ_ne_zero F hint hF0
  have hG0 : G ≠ 0 := fun h0 ↦ hFZ0 (zero_dvd_iff.mp (h0 ▸ hG))
  set ds := pts.map fun a ↦ G.eval a with hds
  have hmem : ds ∈ List.sections (pts.map fun a : ℤ ↦ divsZ (evalC F (Int.cast a : ℚ)).num) := by
    rw [List.mem_sections, hds, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    intro a ha
    rw [num_evalC F hint]
    refine mem_divsZ ?_ (eval_dvd hG)
    have := ptsFor_ne F (e + 1) ha
    rw [evalC_polyZ F hint] at this
    exact_mod_cast this
  have hds_len : ds.length = pts.length := by simp [hds]
  have h1 := hnone ds hmem
  set g := lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) (ds.map fun d : ℤ ↦ (Int.cast d : ℚ))
    with hg
  have hev : ∀ a ∈ pts, (toPoly g).eval (a : ℚ) = GQ.eval (a : ℚ) := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have := eval_lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) (ds.map fun d : ℤ ↦ (Int.cast d : ℚ))
      ((ptsFor_nodup F (e + 1)).map Int.cast_injective) i (by simpa using hi)
    rw [List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa [hds_len] using hi)] at this
    simp only [List.getElem_map, hds] at this
    rw [this, hGQ, eval_map]
    exact (Polynomial.eval₂_hom (Int.castRingHom ℚ) pts[i]).symm
  set sF := (pts.map fun a : ℤ ↦ (a : ℚ)).toFinset with hsF
  have hcard : sF.card = e + 1 := by
    rw [hsF, List.toFinset_card_of_nodup ((ptsFor_nodup F (e + 1)).map Int.cast_injective),
      List.length_map, hlen]
  have hgnd : (toPoly g).natDegree ≤ e := by
    have := natDegree_lagr (pts.map fun a : ℤ ↦ (Int.cast a : ℚ))
      (ds.map fun d : ℤ ↦ (Int.cast d : ℚ))
    simp only [List.length_map, hlen, Nat.add_sub_cancel] at this
    exact this
  have hgdeg : (toPoly g).degree < sF.card := by
    rw [hcard]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hgnd)
  have hGdeg : GQ.degree < sF.card := by
    rw [hcard, hGQ, degree_map_eq_of_injective (RingHom.injective_int _), degree_eq_natDegree hG0,
      hGd]
    exact_mod_cast Nat.lt_succ_self e
  have hgG : toPoly g = GQ := Polynomial.eq_of_degrees_lt_of_eval_finset_eq _ hgdeg hGdeg
    (fun x hx ↦ by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact hev a ha)
  have hGQ0 : GQ ≠ 0 := by
    rw [hGQ]; exact (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hG0
  have hlen' : (trim g).length = e + 1 := by
    have htr : trim g ≠ [] := fun h0 ↦ hGQ0 (by rw [← hgG]; exact (trim_eq_nil_iff g).mp h0)
    rw [length_trim htr, hgG, hGQ, natDegree_map_eq_of_injective (RingHom.injective_int _), hGd]
  have hdvd : toPoly g ∣ toPoly F := by
    rw [hgG, hGQ, ← polyZ_map F hint]
    exact Polynomial.map_dvd _ hG
  have hr0 : toPoly (divMod F g).2 = 0 := by
    have hspec := divMod_spec F g
    refine toPoly_eq_zero_of_dvd_of_degree_lt ?_ (divMod_degree_lt F g (by rw [hgG]; exact hGQ0))
    have : toPoly (divMod F g).2 = toPoly F - toPoly (divMod F g).1 * toPoly g := by
      rw [hspec]; ring
    rw [this]
    exact dvd_sub hdvd (dvd_mul_left _ _)
  have hc : ((trim g).length == e + 1 && intC g && valTest F g && isZero (divMod F g).2) = true := by
    rw [hlen', intC_of_toPoly_eq hgG, valTest_of_toPoly_eq F hint hgG hG, (isZero_iff _).mpr hr0]
    simp
  have hfz : (basisOk (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) &&
      !zFilter F ((lagDen (pts.map fun a : ℤ ↦ (Int.cast a : ℚ)) : ℕ) : ℤ)
        (lagZ (basisZ (pts.map fun a : ℤ ↦ (Int.cast a : ℚ))) ds)) = false := by
    cases hok : basisOk (pts.map fun a : ℤ ↦ (Int.cast a : ℚ))
    · rfl
    · rw [zFilter_of F hint pts ds hds_len G hG hgG hok]; rfl
  simp only [hfz] at h1
  simp [hc] at h1

/-- **`findFactor` is complete**: every reducible primitive integral polynomial of positive
degree has a factor found by the search. -/
theorem findFactor_complete (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1)
    (hgcd : gcdL (F.map Rat.num) = 1) (hpos : 0 < (toPoly F).natDegree)
    (hred : ¬ Irreducible (toPoly F)) : findFactor F ≠ none := by
  classical
  have hF0 : toPoly F ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hpos; omega
  have hprim := polyZ_primitive F hgcd
  have hmap := polyZ_map F hint
  have hnd := natDegree_polyZ F hint
  have hFZ0 := polyZ_ne_zero F hint hF0
  have hredZ : ¬ Irreducible (polyZ F) := fun hirr ↦ hred (by
    have := (hprim.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hirr
    rwa [show (algebraMap ℤ ℚ) = Int.castRingHom ℚ from rfl, hmap] at this)
  have hnu : ¬ IsUnit (polyZ F) := fun hu ↦ by have := natDegree_eq_zero_of_isUnit hu; omega
  rw [irreducible_iff] at hredZ
  push_neg at hredZ
  obtain ⟨a, b, hab, ha, hb⟩ := hredZ hnu
  have ha0 : a ≠ 0 := fun h0 ↦ hFZ0 (by rw [hab, h0, zero_mul])
  have hb0 : b ≠ 0 := fun h0 ↦ hFZ0 (by rw [hab, h0, mul_zero])
  have hsum : a.natDegree + b.natDegree = (polyZ F).natDegree := by rw [hab, natDegree_mul ha0 hb0]
  have hconst : ∀ c : ℤ[X], c ∣ (polyZ F) → c.natDegree = 0 → IsUnit c := fun c hc hc0 ↦ by
    rw [eq_C_of_natDegree_eq_zero hc0] at hc ⊢
    exact isUnit_C.mpr (hprim _ hc)
  have ha' : a.natDegree ≠ 0 := fun h ↦ ha (hconst a ⟨b, hab⟩ h)
  have hb' : b.natDegree ≠ 0 := fun h ↦ hb (hconst b ⟨a, by rw [hab, mul_comm]⟩ h)
  obtain ⟨G, hG, hGd1, hGd2⟩ : ∃ G : ℤ[X], G ∣ (polyZ F) ∧ 1 ≤ G.natDegree ∧
      G.natDegree ≤ (polyZ F).natDegree / 2 := by
    rcases le_total a.natDegree b.natDegree with hle | hle
    · exact ⟨a, ⟨b, hab⟩, by omega, by omega⟩
    · exact ⟨b, ⟨a, by rw [hab, mul_comm]⟩, by omega, by omega⟩
  unfold findFactor
  intro hnone
  rw [List.findSome?_eq_none_iff] at hnone
  refine findFactorDeg_complete F hint (G.natDegree - 1 + 1) hF0 G hG (by omega)
    (hnone _ (List.mem_range.mpr ?_))
  rw [degC_eq F hF0, ← hnd]
  omega

/-! ### The primitive integral associate -/

lemma gcdL_dvd : ∀ l : List ℤ, ∀ a ∈ l, (gcdL l : ℤ) ∣ a
  | [], a, ha => absurd ha List.not_mem_nil
  | b :: l, a, ha => by
    simp only [gcdL, List.foldr_cons] at *
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Int.gcd_dvd_left _ _
    · exact Int.dvd_trans (Int.gcd_dvd_right _ _) (gcdL_dvd l a ha)

lemma gcdL_cons (b : ℤ) (l : List ℤ) : gcdL (b :: l) = Int.gcd b (gcdL l) := rfl

lemma gcdL_map_div (c : ℕ) : ∀ l : List ℤ, (∀ a ∈ l, (c : ℤ) ∣ a) →
    gcdL (l.map (· / (c : ℤ))) = gcdL l / c
  | [], _ => by simp [gcdL]
  | b :: l, h => by
    rw [List.map_cons, gcdL_cons, gcdL_cons,
      gcdL_map_div c l fun a ha ↦ h a (List.mem_cons_of_mem _ ha)]
    have hl : (c : ℤ) ∣ (gcdL l : ℤ) := dvd_gcdL _ _ fun a ha ↦ h a (List.mem_cons_of_mem _ ha)
    have hcast : ((gcdL l / c : ℕ) : ℤ) = (gcdL l : ℤ) / (c : ℤ) := by push_cast; rfl
    rw [hcast, Int.gcd_div (h b List.mem_cons_self) hl, Int.natAbs_natCast]

/-- The lcm of the denominators. -/
def denL (g : CPoly ℚ) : ℕ := g.foldr (fun q acc ↦ Nat.lcm q.den acc) 1

lemma denL_ne_zero : ∀ g : CPoly ℚ, denL g ≠ 0
  | [] => by simp [denL]
  | q :: g => by
    simp only [denL, List.foldr_cons] at *
    exact Nat.lcm_ne_zero q.den_nz (denL_ne_zero g)

lemma den_dvd_denL : ∀ g : CPoly ℚ, ∀ q ∈ g, q.den ∣ denL g
  | [], q, hq => absurd hq List.not_mem_nil
  | r :: g, q, hq => by
    simp only [denL, List.foldr_cons] at *
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Nat.dvd_lcm_left _ _
    · exact (den_dvd_denL g q hq).trans (Nat.dvd_lcm_right _ _)

lemma den_mul_of_dvd (q : ℚ) (d : ℕ) (h : q.den ∣ d) : (q * d).den = 1 := by
  obtain ⟨k, rfl⟩ := h
  have : q * ((q.den * k : ℕ) : ℚ) = ((q.num * k : ℤ) : ℚ) := by
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  rw [this, Rat.den_intCast]

lemma toPoly_map_mul (d : ℚ) : ∀ g : CPoly ℚ, toPoly (g.map (· * d)) = C d * toPoly g
  | [] => by simp
  | a :: g => by
    rw [List.map_cons, toPoly_cons, toPoly_cons, toPoly_map_mul d g, C_mul]; ring

lemma primInt_spec (g : CPoly ℚ) (hg0 : toPoly g ≠ 0) :
    (∀ q ∈ primInt g, q.den = 1) ∧ gcdL ((primInt g).map Rat.num) = 1 ∧
      ∃ k : ℚ, k ≠ 0 ∧ toPoly (primInt g) = C k * toPoly g := by
  classical
  have hd0 : (denL g : ℚ) ≠ 0 := by exact_mod_cast denL_ne_zero g
  set g' := g.map (· * (denL g : ℚ)) with hg'
  have hint' : ∀ x ∈ g', x.den = 1 := fun x hx ↦ by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact den_mul_of_dvd q _ (den_dvd_denL g q hq)
  have hnum' : ∀ x ∈ g', ((x.num : ℤ) : ℚ) = x := fun x hx ↦ by
    have := Rat.num_div_den x
    rwa [hint' x hx, Nat.cast_one, div_one] at this
  set c := gcdL (g'.map Rat.num) with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hg0
    have hz : ∀ x ∈ g', x = 0 := fun x hx ↦ by
      have := gcdL_dvd _ x.num (List.mem_map_of_mem hx)
      rw [← hc, h0, Nat.cast_zero, zero_dvd_iff] at this
      rw [← hnum' x hx, this, Int.cast_zero]
    have htp : toPoly g' = 0 := (isZero_iff _).mp (by simpa [isZero] using hz)
    rw [hg', toPoly_map_mul] at htp
    exact (mul_eq_zero.mp htp).resolve_left (by simpa using hd0)
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
  have hp : primInt g = g'.map (· / (c : ℚ)) := by
    rw [show primInt g = if (c : ℚ) = 0 then g' else g'.map (· / (c : ℚ)) from rfl, if_neg hcQ]
  have hdvd : ∀ x ∈ g', (c : ℤ) ∣ x.num := fun x hx ↦ gcdL_dvd _ _ (List.mem_map_of_mem hx)
  have hp' : primInt g = (g'.map Rat.num).map fun a ↦ ((a / (c : ℤ) : ℤ) : ℚ) := by
    rw [hp]
    conv_rhs => rw [List.map_map]
    refine List.map_congr_left fun x hx ↦ ?_
    simp only [Function.comp_apply]
    rw [Int.cast_div (hdvd x hx) (by exact_mod_cast hc0), hnum' x hx, Int.cast_natCast]
  refine ⟨fun q hq ↦ ?_, ?_, ⟨(c : ℚ)⁻¹ * denL g, mul_ne_zero (inv_ne_zero hcQ) hd0, ?_⟩⟩
  · rw [hp'] at hq
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hq
    exact Rat.den_intCast _
  · rw [hp', List.map_map]
    have : (Rat.num ∘ fun a : ℤ ↦ ((a / (c : ℤ) : ℤ) : ℚ)) = (· / (c : ℤ)) := by
      funext a; simp
    rw [this, gcdL_map_div c _ fun a ha ↦ by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact hdvd x hx, ← hc, Nat.div_self (Nat.pos_of_ne_zero hc0)]
  · rw [hp, show (fun x : ℚ ↦ x / (c : ℚ)) = (· * (c : ℚ)⁻¹) from funext fun x ↦ div_eq_mul_inv _ _,
      toPoly_map_mul, hg', toPoly_map_mul, C_mul, mul_assoc]

/-! ### The factorisation is complete -/

lemma findFactorDeg_spec (F g : CPoly ℚ) (e : ℕ) (h : findFactorDeg F e = some g) :
    (trim g).length = e + 1 ∧ isZero (divMod F g).2 = true := by
  unfold findFactorDeg at h
  obtain ⟨ds, -, hds⟩ := List.exists_of_findSome?_eq_some h
  dsimp only at hds
  split at hds
  · cases hds
  split at hds
  · rename_i hc
    cases hds
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1.1.1, hc.2⟩
  · cases hds

lemma findFactor_spec (F g : CPoly ℚ) (h : findFactor F = some g) :
    ∃ e, e < degC F / 2 ∧ (trim g).length = e + 2 ∧ isZero (divMod F g).2 = true := by
  unfold findFactor at h
  obtain ⟨e, he, hg⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨e, List.mem_range.mp he, findFactorDeg_spec F g (e + 1) hg⟩

lemma rem_zero_spec (F g : CPoly ℚ) (h : isZero (divMod F g).2 = true) :
    toPoly F = toPoly (divMod F g).1 * toPoly g := by
  have hsp := divMod_spec F g
  rw [hsp, (isZero_iff _).mp h, add_zero]

/-- **The factorisation is complete**: with enough fuel, `factorQ` returns certified irreducible
factors whose product is `F` up to a non-zero constant. -/
theorem factorQ_spec : ∀ (n : ℕ) (F : CPoly ℚ), 0 < (toPoly F).natDegree →
    (toPoly F).natDegree ≤ n → (∀ p ∈ factorQ n F, irredQ p = true) ∧
      ∃ k : ℚ, k ≠ 0 ∧ toPoly F = C k * ((factorQ n F).map toPoly).prod
  | 0, F, hpos, hn => by omega
  | n + 1, F, hpos, hn => by
    classical
    have hF0 : toPoly F ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hpos; omega
    obtain ⟨hint, hgcd, k, hk0, hk⟩ := primInt_spec F hF0
    have hdP : (toPoly (primInt F)).natDegree = (toPoly F).natDegree := by
      rw [hk, natDegree_C_mul hk0]
    have hP0 : toPoly (primInt F) ≠ 0 := by
      rw [hk]; exact mul_ne_zero (by simpa using hk0) hF0
    rcases hf : findFactor (primInt F) with _ | g
    · simp only [factorQ, hf]
      have hirr : Irreducible (toPoly (primInt F)) := by
        by_contra hred
        exact findFactor_complete _ hint hgcd (by omega) hred hf
      refine ⟨fun p hp ↦ ?_, k⁻¹, inv_ne_zero hk0, ?_⟩
      · rw [List.mem_singleton.mp hp]
        exact irredQ_complete _ hint hgcd hirr
      · rw [List.map_singleton, List.prod_singleton, hk, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hk0,
          C_1, one_mul]
    · simp only [factorQ, hf]
      obtain ⟨e, he, hgl, hz⟩ := findFactor_spec _ _ hf
      rw [degC_eq _ hP0] at he
      have hgtr : trim g ≠ [] := fun h0 ↦ by rw [h0] at hgl; simp at hgl
      have hg0 : toPoly g ≠ 0 := fun h0 ↦ hgtr ((trim_eq_nil_iff g).mpr h0)
      have hgd : (toPoly g).natDegree = e + 1 := by rw [length_trim hgtr] at hgl; omega
      set q := (divMod (primInt F) g).1 with hq
      have hPq := rem_zero_spec _ _ hz
      rw [← hq] at hPq
      have hq0 : toPoly q ≠ 0 := fun h0 ↦ hP0 (by rw [hPq, h0, zero_mul])
      have hqd : (toPoly q).natDegree + (e + 1) = (toPoly F).natDegree := by
        rw [← hdP, hPq, natDegree_mul hq0 hg0, hgd]
      obtain ⟨h1, k1, hk1, hk1'⟩ := factorQ_spec n g (by omega) (by omega)
      obtain ⟨h2, k2, hk2, hk2'⟩ := factorQ_spec n q (by omega) (by omega)
      refine ⟨fun p hp ↦ ?_, k⁻¹ * (k1 * k2), mul_ne_zero (inv_ne_zero hk0) (mul_ne_zero hk1 hk2),
        ?_⟩
      · rcases List.mem_append.mp hp with hp | hp
        · exact h1 p hp
        · exact h2 p hp
      · have : toPoly F = C k⁻¹ * toPoly (primInt F) := by
          rw [hk, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hk0, C_1, one_mul]
        rw [this, hPq, hk1', hk2', List.map_append, List.prod_append, C_mul, C_mul]
        ring

end Kron

end CPoly
