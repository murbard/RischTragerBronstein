import RischTragerBronstein.Algebraic.SupLocalCert
import RischTragerBronstein.Weil.StepanovN6

/-!
# Local certificates for `n`-th roots

For `n ∣ p − 1`: `𝔽_p` contains a primitive `n`-th root of unity (`exists_primitive_nth`, so
`findZeta` succeeds), an element `a ≠ 0` with `a^{(p−1)/n} = 1` is an `n`-th power
(`exists_nth_root_zmod`, the units being cyclic), and the local certificate exists at every large prime
(`localCert_isSomeN`, from Stepanov's bound for `n`-th powers `many_nth_powers`).
-/

open Polynomial CPoly CPoly.Kron

namespace Sup

variable {p : ℕ} [hp : Fact p.Prime]

lemma card_units_zmod : Nat.card (ZMod p)ˣ = p - 1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units]

lemma exists_generator_zmod : ∃ g : (ZMod p)ˣ, orderOf g = p - 1 ∧ ∀ x : (ZMod p)ˣ,
    x ∈ Subgroup.zpowers g := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine ⟨g, ?_, hg⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_zmod]

/-- A primitive `n`-th root of unity in `𝔽_p` for `n ∣ p − 1`. -/
lemma exists_primitive_nth {n : ℕ} (hn : 1 ≤ n) (hnp : n ∣ p - 1) :
    ∃ ζ : ZMod p, ζ ^ n = 1 ∧ ∀ l, 0 < l → l < n → ζ ^ l ≠ 1 := by
  obtain ⟨g, hgo, -⟩ := exists_generator_zmod (p := p)
  have hp1 := hp.out.one_lt
  obtain ⟨c, hc⟩ := hnp
  have hc0 : c ≠ 0 := by rintro rfl; omega
  have hord : orderOf (g ^ c) = n := by
    rw [orderOf_pow_of_dvd hc0 (by rw [hgo, hc]; exact dvd_mul_left c n), hgo, hc,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hc0)]
  refine ⟨((g ^ c : (ZMod p)ˣ) : ZMod p), ?_, fun l hl hln h1 ↦ ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hord, pow_orderOf_eq_one, Units.val_one]
  · have : (g ^ c) ^ l = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
    have := orderOf_le_of_pow_eq_one hl this
    omega

/-- **Euler's criterion for `n`-th powers.** -/
lemma exists_nth_root_zmod {n : ℕ} (hn : 1 ≤ n) (hnp : n ∣ p - 1) {a : ZMod p} (ha0 : a ≠ 0)
    (ha : a ^ ((p - 1) / n) = 1) : ∃ y : ZMod p, y ^ n = a := by
  obtain ⟨g, hgo, hg⟩ := exists_generator_zmod (p := p)
  set u := Units.mk0 a ha0 with hu
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
  set c := (p - 1) / n with hc
  have hnc : n * c = p - 1 := Nat.mul_div_cancel' hnp
  have hp1 := hp.out.one_lt
  have hc0 : c ≠ 0 := by intro h; rw [h, mul_zero] at hnc; omega
  have huc : u ^ c = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, ha,
    Units.val_one])
  have h1 : g ^ (k * c) = 1 := by rw [zpow_mul, hk]; exact_mod_cast huc
  have h2 : ((p - 1 : ℕ) : ℤ) ∣ k * c := by
    rw [← hgo]; exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [← hnc] at h2
  push_cast at h2
  have h3 : (n : ℤ) ∣ k := by
    obtain ⟨t, ht⟩ := h2
    exact ⟨t, by
      have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast hc0
      apply mul_right_cancel₀ hc'
      linear_combination ht⟩
  obtain ⟨m, rfl⟩ := h3
  refine ⟨((g ^ m : (ZMod p)ˣ) : ZMod p), ?_⟩
  have : (g ^ m) ^ n = u := by rw [← zpow_natCast, ← zpow_mul, mul_comm, hk]
  rw [← Units.val_pow_eq_pow_val, this, hu, Units.val_mk0]

lemma findZeta_isSome {n : ℕ} (hn : 1 ≤ n) (hnp : n ∣ p - 1) : (findZeta (p := p) n).isSome := by
  obtain ⟨ζ, hζn, hζl⟩ := exists_primitive_nth (p := p) hn hnp
  refine List.find?_isSome.mpr ⟨ζ, mem_zmodElems _, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    bne_iff_ne, ne_eq]
  exact ⟨hζn, fun l hl ↦ by
    rcases Nat.eq_zero_or_pos l with h | h
    · exact Or.inl h
    · exact Or.inr (hζl l h hl)⟩


variable {K : Type*} [Field K] [DecidableEq K]

/-- **For `n`-th roots, the local certificate exists at every large prime `p ≡ 1 (mod n)`.** -/
theorem localCert_isSomeN (R : RedFns p K) (fK : CPoly K) {r : ℕ} (α : Fin r → K) {n : ℕ}
    (hn : 2 ≤ n) (hnp : n ∣ p - 1) (hcop : Nat.Coprime n (fK.length - 1))
    (hd : 1 ≤ (toPoly (fK.map R.red)).natDegree) (hsq : Squarefree (toPoly (fK.map R.red)))
    (hpL : (16 * n * n * ((toPoly (fK.map R.red)).natDegree + 2) *
      ((((n - 1) * (fK.length - 1 - 1) + 1) / 2 + (fK.length - 1) + r + 1) +
        (toPoly (fK.map R.red)).natDegree + 2)) ^ 2 ≤ p) :
    (localCert fK n p R α).isSome := by
  classical
  set fr := toPoly (fK.map R.red) with hfr
  set D := fK.length - 1 with hD
  set g := ((n - 1) * (D - 1) + 1) / 2 with hg
  have hz := findZeta_isSome (p := p) (by omega) hnp
  obtain ⟨ζ, hζ⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨hζn, hζl⟩ := findZeta_spec hζ
  have hprim : IsPrimitiveRoot ζ n := IsPrimitiveRoot.mk_of_lt ζ (by omega) hζn
    (fun l hl0 hln ↦ hζl l (List.mem_range.mpr hln) hl0)
  -- a simple irreducible factor
  have hfr0 : fr ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hd; omega
  have hfru : ¬ IsUnit fr := fun h ↦ by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hfr0] at h
    have : fr.natDegree = 0 := by exact_mod_cast h
    omega
  obtain ⟨P, hP, hPf⟩ := WfDvdMonoid.exists_irreducible_factor hfru hfr0
  have hP2 : ¬ P ^ (1 + 1) ∣ fr := fun h ↦ hP.not_isUnit (hsq P (by rwa [← pow_two]))
  have hmany := Stepanov.many_nth_powers n (by omega) hnp fr hd P hP 1 (Nat.coprime_one_left n)
    (by rwa [pow_one]) hP2 (g + D + r + 1) hpL
  set S := Finset.univ.filter fun x : ZMod p ↦ fr.eval x ≠ 0 ∧ fr.eval x ^ ((p - 1) / n) = 1
  set avoid := List.ofFn fun q ↦ R.red (α q) with havoid
  set Xs := (((ptsZ (fK.map R.red) n).filter fun c ↦ c.1 ∉ avoid).map Prod.fst).toFinset
  have hsub : S \ avoid.toFinset ⊆ Xs := by
    intro x hx
    obtain ⟨hxS, hxa⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hx0, hxe⟩ := (Finset.mem_filter.mp hxS).2
    obtain ⟨y, hy⟩ := exists_nth_root_zmod (by omega) hnp hx0 hxe
    have hy0 : y ≠ 0 := fun h ↦ hx0 (by rw [← hy, h, zero_pow (by omega)])
    obtain ⟨y', hy'⟩ := exists_ptsZ (fr := fK.map R.red) (n := n) hy0
      (by rw [evalC_eq, ← hfr, hy])
    refine List.mem_toFinset.mpr (List.mem_map.mpr ⟨(x, y'), List.mem_filter.mpr ⟨hy', ?_⟩, rfl⟩)
    simpa [List.mem_toFinset] using hxa
  have hav : avoid.toFinset.card ≤ r := (List.toFinset_card_le _).trans (by simp [havoid])
  have hcard : g + D < Xs.card := by
    have h1 := Finset.card_le_card hsub
    have h2 : S.card ≤ (S \ avoid.toFinset).card + avoid.toFinset.card := by
      have := Finset.card_sdiff_add_card_inter S avoid.toFinset
      have := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := avoid.toFinset))
      omega
    omega
  have hcs := certSearch_complete hn hcop hprim (ptsZ (fK.map R.red) n) avoid
    (fun c hc ↦ (mem_ptsZ hc).1) (by rw [hg] at hcard; exact hcard)
  unfold localCert
  rw [hζ]
  simp only [Option.isSome_map]
  exact Option.ne_none_iff_isSome.mp hcs

end Sup
