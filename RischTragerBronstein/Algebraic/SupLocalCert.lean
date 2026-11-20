import RischTragerBronstein.Algebraic.SupCertSearch
import RischTragerBronstein.Algebraic.SupRedOracle
import RischTragerBronstein.Weil.Stepanov6
import RischTragerBronstein.Algebraic.SupRedG

/-!
# Local certificates modulo `p`, found among all points of the reduced curve

`localCert fK n`: at a prime `p`, run `certSearch` over `𝔽_p` with **all** the points
`(x, y)`, `y ≠ 0`, of the reduced curve `yⁿ = f̄(x)` as candidates (`ptsZ`), avoiding the
reductions of the query abscissae. Every answer satisfies the local part of `supCheckR`
(`localCert_spec`); for `n = 2` it answers for all large `p` (`localCert_isSome`): Stepanov's bound
(`Stepanov.many_squares`) provides more candidate abscissae than `certSearch_complete` needs.
-/

open Polynomial CPoly CPoly.Kron

namespace Sup

section Defs

variable {p : ℕ} [Fact p.Prime]

/-- The points `(x, y)` (`y ≠ 0`, first `y` found) of `yⁿ = fr(x)` over `𝔽_p`. -/
def ptsZ (fr : CPoly (ZMod p)) (n : ℕ) : List (ZMod p × ZMod p) :=
  (zmodElems p).filterMap fun x ↦
    ((zmodElems p).find? fun y ↦ y != 0 && y ^ n == evalC fr x).map fun y ↦ (x, y)

lemma mem_ptsZ {fr : CPoly (ZMod p)} {n : ℕ} {c : ZMod p × ZMod p} (h : c ∈ ptsZ fr n) :
    c.2 ≠ 0 ∧ c.2 ^ n = evalC fr c.1 := by
  obtain ⟨x, -, hx⟩ := List.mem_filterMap.mp h
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
  have := List.find?_some hy
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
  exact this

lemma mem_zmodElems (x : ZMod p) : x ∈ zmodElems p := by
  rw [zmodElems, List.mem_map]
  refine ⟨x.val, List.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

lemma exists_ptsZ {fr : CPoly (ZMod p)} {n : ℕ} {x y : ZMod p} (hy : y ≠ 0)
    (hxy : y ^ n = evalC fr x) : ∃ y', (x, y') ∈ ptsZ fr n := by
  have hs : ((zmodElems p).find? fun y ↦ y != 0 && y ^ n == evalC fr x).isSome :=
    List.find?_isSome.mpr ⟨y, mem_zmodElems y, by simp [hy, hxy]⟩
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨y', List.mem_filterMap.mpr ⟨x, mem_zmodElems x, by rw [hy']; rfl⟩⟩

lemma findZeta_spec {n : ℕ} {ζ : ZMod p} (h : findZeta (p := p) n = some ζ) :
    ζ ^ n = 1 ∧ ∀ l ∈ List.range n, 0 < l → ζ ^ l ≠ 1 := by
  have := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, bne_iff_ne,
    ne_eq] at this
  refine ⟨this.1, fun l hl hl0 ↦ ?_⟩
  rcases this.2 l hl with h0 | h1
  · exact absurd h0 (by omega)
  · exact h1

end Defs

variable {K : Type*} [Field K] [DecidableEq K]

/-- **The local certificate provider.** -/
def localCert (fK : CPoly K) (n : ℕ) : CertProv K := fun p _ R _ α ↦
  match findZeta (p := p) n with
  | none => none
  | some ζ0 =>
    (certSearch (fK.length - 1) n ζ0 (ptsZ (fK.map R.red) n)
      (List.ofFn fun q ↦ R.red (α q))).map fun c ↦ (c.1.length, c.1, c.2.1, ζ0, c.2.2)

/-- **The local part of the good-reduction check** holds for every answer. -/
theorem localCert_spec {p : ℕ} [Fact p.Prime] (R : RedFns p K) (fK : CPoly K) {n : ℕ} (hn : 2 ≤ n)
    {r : ℕ} (α : Fin r → K) {g : ℕ} {xs ys : List (ZMod p)} {ζ0 : ZMod p}
    {lam : List (List (ZMod p))} (h : localCert fK n p R α = some (g, xs, ys, ζ0, lam)) :
    g = ((n - 1) * (fK.length - 1 - 1) + 1) / 2 ∧ ζ0 ^ n = 1 ∧
    (∀ l ∈ List.range n, 0 < l → ζ0 ^ l ≠ 1) ∧ xs.length = g ∧ ys.length = g ∧
    (∀ i ∈ List.range g, ys.getD i 0 ^ n = evalC (fK.map R.red) (xs.getD i 0) ∧
      ys.getD i 0 ≠ 0) ∧ xs.Pairwise (· ≠ ·) ∧ (∀ q, ∀ x ∈ xs, R.red (α q) ≠ x) ∧
    nsCheckZ p (fK.length - 1) n g xs ys ζ0 lam = true := by
  unfold localCert at h
  split at h
  · exact absurd h (by simp)
  rename_i ζ hζ
  obtain ⟨c, hc, hceq⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at hceq
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hceq
  obtain ⟨hζn, hζl⟩ := findZeta_spec hζ
  obtain ⟨hlen, hylen, hnd, hpts, hcert⟩ := certSearch_sound hn hc
  have hζ0 : ζ ≠ 0 := fun h0 ↦ by rw [h0, zero_pow (by omega)] at hζn; exact zero_ne_one hζn
  refine ⟨hlen, hζn, hζl, rfl, hylen, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨cc, hcc, -, hx, k, -, hy⟩ := hpts i (List.mem_range.mp hi)
    obtain ⟨hc0, hce⟩ := mem_ptsZ hcc
    rw [hy, hx, mul_pow, ← pow_mul, mul_comm k n, pow_mul, hζn, one_pow, one_mul]
    exact ⟨hce, mul_ne_zero (pow_ne_zero _ hζ0) hc0⟩
  · exact List.Nodup.pairwise_of_forall_ne hnd fun _ _ _ _ h ↦ h
  · intro q x hx heq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨cc, -, hav, hx', -⟩ := hpts i hi
    apply hav
    rw [← List.getD_eq_getElem _ 0 hi, hx'.symm.symm] at heq
    rw [← heq]
    exact List.mem_ofFn.mpr ⟨q, rfl⟩
  · simp only [nsCheckZ, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    intro i hi ai hai
    exact hcert i hi ai hai

/-- **For square roots, the local certificate exists at every large prime.** -/
theorem localCert_isSome {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (R : RedFns p K) (fK : CPoly K)
    {r : ℕ} (α : Fin r → K) (hcop : Nat.Coprime 2 (fK.length - 1))
    (hd : 1 ≤ (toPoly (fK.map R.red)).natDegree) (hsq : Squarefree (toPoly (fK.map R.red)))
    (hpL : (16 * ((toPoly (fK.map R.red)).natDegree + 2) *
      ((((2 - 1) * (fK.length - 1 - 1) + 1) / 2 + (fK.length - 1) + r + 1) +
        (toPoly (fK.map R.red)).natDegree + 2)) ^ 2 ≤ p) :
    (localCert fK 2 p R α).isSome := by
  classical
  set fr := toPoly (fK.map R.red) with hfr
  set D := fK.length - 1 with hD
  set g := ((2 - 1) * (D - 1) + 1) / 2 with hg
  -- the root of unity `−1`
  have hz : (findZeta (p := p) 2).isSome := by
    refine List.find?_isSome.mpr ⟨-1, mem_zmodElems _, ?_⟩
    have h1 : (-1 : ZMod p) ≠ 1 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -h
      rw [ZMod.natCast_eq_zero_iff] at this
      have := Nat.le_of_dvd (by norm_num) this
      have := hp.out.two_le
      omega
    simp [h1, List.range_succ]
  obtain ⟨ζ, hζ⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨hζ2, hζl⟩ := findZeta_spec hζ
  have hprim : IsPrimitiveRoot ζ 2 := IsPrimitiveRoot.mk_of_lt ζ (by norm_num) hζ2
    (fun l hl0 hl2 ↦ hζl l (List.mem_range.mpr hl2) hl0)
  -- an odd-multiplicity irreducible factor
  have hfr0 : fr ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hd; omega
  have hfru : ¬ IsUnit fr := fun h ↦ by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hfr0] at h
    have : fr.natDegree = 0 := by exact_mod_cast h
    omega
  obtain ⟨P, hP, hPf⟩ := WfDvdMonoid.exists_irreducible_factor hfru hfr0
  have hP2 : ¬ P ^ (1 + 1) ∣ fr := fun h ↦ hP.not_isUnit (hsq P (by rwa [← pow_two]))
  have hmany := Stepanov.many_squares hp2 fr hd P hP 1 odd_one (by rwa [pow_one]) hP2
    (g + D + r + 1) hpL
  set S := Finset.univ.filter fun x : ZMod p ↦ fr.eval x ≠ 0 ∧ fr.eval x ^ (p / 2) = 1
  set avoid := List.ofFn fun q ↦ R.red (α q) with havoid
  set Xs := (((ptsZ (fK.map R.red) 2).filter fun c ↦ c.1 ∉ avoid).map Prod.fst).toFinset
  have hsub : S \ avoid.toFinset ⊆ Xs := by
    intro x hx
    obtain ⟨hxS, hxa⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hx0, hxe⟩ := (Finset.mem_filter.mp hxS).2
    obtain ⟨y, hy⟩ := (ZMod.euler_criterion p hx0).mpr hxe
    have hy0 : y ≠ 0 := fun h ↦ hx0 (by rw [hy, h, mul_zero])
    obtain ⟨y', hy'⟩ := exists_ptsZ (fr := fK.map R.red) (n := 2) hy0
      (by rw [evalC_eq, ← hfr, hy, sq])
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
  have hcs := certSearch_complete (le_refl 2) hcop hprim (ptsZ (fK.map R.red) 2) avoid
    (fun c hc ↦ (mem_ptsZ hc).1) (by rw [hg] at hcard; exact hcard)
  unfold localCert
  rw [hζ]
  simp only [Option.isSome_map]
  exact Option.ne_none_iff_isSome.mp hcs

/-- **The good-reduction check for a local certificate**, from the integrality of the data over
`K` at `p`. -/
theorem localCert_check {p : ℕ} [Fact p.Prime] [CharZero K] (R : RedFns p K) (φ : K →+* ℚ_[p])
    (hR : RedValid p R φ) {fK : CPoly K} {n : ℕ} (hn2 : 2 ≤ n) (hnp : ((n : ℕ) : ZMod p) ≠ 0)
    (hd : 0 < fK.length - 1) (hokf : ∀ c ∈ fK, R.ok c = true)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hlci : R.ok (fK.getD (fK.length - 1) 0)⁻¹ = true)
    {u v : List K} (hu : ∀ c ∈ u, R.ok c = true) (hv : ∀ c ∈ v, R.ok c = true)
    (hbez : toPoly u * toPoly fK + toPoly v * derivative (toPoly fK) = 1)
    {r : ℕ} {α β : Fin r → K}
    (hΓ : ∀ q, R.ok (α q) = true ∧ R.ok (β q) = true ∧ β q ≠ 0 ∧ R.ok (β q)⁻¹ = true ∧
      β q ^ n = evalC fK (α q))
    (hΓd : ∀ q q', α q ≠ α q' → R.ok (α q - α q')⁻¹ = true)
    (hΓβ : ∀ q q', q ≠ q' → α q = α q' → β q ≠ β q' ∧ R.ok (β q - β q')⁻¹ = true)
    {g : ℕ} {xs ys : List (ZMod p)} {ζ0 : ZMod p} {lam : List (List (ZMod p))}
    (hc : localCert fK n p R α = some (g, xs, ys, ζ0, lam)) :
    supCheckR p R fK n g α β xs ys ζ0 lam := by
  obtain ⟨hg, hζn, hζl, hxl, hyl, hpts, hpw, hav, hns⟩ := localCert_spec R fK hn2 α hc
  refine ⟨hn2, hnp, hd, hokf, red_ne_zero R φ hR hlc (hokf _ ?_) hlci, by omega, ?_, hζn, hζl,
    hxl, hyl, hpts, hpw, fun q ↦ ?_, ?_, ?_, hns⟩
  · have hlm : fK.length - 1 < fK.length := by omega
    rw [List.getD_eq_getElem _ _ hlm]; exact List.getElem_mem hlm
  · exact squarefreeCheck_of_coprime ⟨_, _, red_bezout φ R hR hu hv hokf hbez⟩
  · obtain ⟨ha, hb, hb0, hbi, hbe⟩ := hΓ q
    exact ⟨ha, hb, red_ne_zero R φ hR hb0 hb hbi, hbe, hav q⟩
  · intro q q'
    by_cases h : α q = α q'
    · exact Or.inl h
    · exact Or.inr (red_ne_of_sub R φ hR h (hΓ q).1 (hΓ q').1 (hΓd q q' h))
  · intro q q' hqq hα
    obtain ⟨hne, hok⟩ := hΓβ q q' hqq hα
    exact red_ne_of_sub R φ hR hne (hΓ q).2.1 (hΓ q').2.1 hok

end Sup
