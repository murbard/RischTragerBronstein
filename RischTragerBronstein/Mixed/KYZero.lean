import RischTragerBronstein.Mixed.KRLogs

/-!
# The fibre over `x = 0`: full Galois orbits and killing the orders there

* `galois_full`: if `p(0)` has no `ℓ`-th root in `C` for every prime `ℓ ∣ n` (and `ζ ∈ C`), every
  point `(0, ζᵏβ₀)` is a Galois conjugate of `(0, β₀)`, so every element of `C(x, y)` has the same
  order at all of them;
* `kill_full`: then `w x^{−r}` has order `0` over `x = 0` and the orders of `w` elsewhere;
* `kill_tors`: with witnesses `Z_k` of `N_k (0, ζᵏβ₀)`, a power of `w` times a product of the `Z_k`
  has order `0` over `x = 0` and a multiple of the orders of `w` elsewhere.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)
variable (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)
variable (β₀ : K) (hβ₀ : β₀ ≠ 0) (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)

lemma prod_pow_form (a β : K) : ∀ s : Multiset K, (∀ r ∈ s, ∃ k : ℕ, r = a ^ k * β) →
    ∃ m : ℕ, s.prod = a ^ m * β ^ Multiset.card s := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; exact ⟨0, by simp⟩
  | cons r s ih =>
    intro h
    obtain ⟨m, hm⟩ := ih fun r' hr' ↦ h r' (Multiset.mem_cons_of_mem hr')
    obtain ⟨k, hk⟩ := h r (Multiset.mem_cons_self r s)
    refine ⟨k + m, ?_⟩
    rw [Multiset.prod_cons, hm, hk, Multiset.card_cons, pow_add, pow_succ]
    ring

include hζ hβ₀ hv0 in
/-- **Full Galois orbit over `x = 0`**: all points over `0` have the same orders. -/
theorem galois_full [Algebra.IsAlgebraic C K]
    (hno : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ S.n → ∀ c : C, c ^ ℓ ≠ S.p.eval 0) :
    ∀ (w : C⟮S.x⟯⟮S.y⟯) (k : ℕ), S.rv ζ β₀ w k = S.rv ζ β₀ w 0 := by
  classical
  haveI : IsAlgClosure C K := ⟨inferInstance, inferInstance⟩
  haveI : Normal C K := IsAlgClosure.normal C K
  set m := minpoly C β₀ with hm
  have hint : IsIntegral C β₀ := Algebra.IsIntegral.isIntegral β₀
  have hmon : m.Monic := minpoly.monic hint
  have hp0 : (S.p.map (algebraMap C K)).eval 0 = algebraMap C K (S.p.eval 0) := by
    rw [← map_zero (algebraMap C K), eval_map, eval₂_at_apply]
  have hdvd : m ∣ X ^ S.n - Polynomial.C (S.p.eval 0) := minpoly.dvd C β₀ (by
    rw [map_sub, map_pow, aeval_X, aeval_C, hv0, hp0, sub_self])
  -- the roots of `m` are among the `ζᵏ β₀`
  have hroot : ∀ r ∈ (m.map (algebraMap C K)).roots, ∃ k : ℕ, r = algebraMap C K ζ ^ k * β₀ := by
    intro r hr
    have hr0 : aeval r m = 0 := by
      rw [mem_roots (map_ne_zero (minpoly.ne_zero hint))] at hr
      rwa [IsRoot, eval_map_algebraMap] at hr
    obtain ⟨Q, hQ⟩ := hdvd
    have := congrArg (aeval r) hQ
    rw [map_mul, hr0, zero_mul, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at this
    have hv : r ^ S.n = (S.p.map (algebraMap C K)).eval 0 := by rw [this, hp0]
    obtain ⟨k, -, hk⟩ := S.over_zero_k ζ hζ β₀ hβ₀ hv0 r hv
    exact ⟨k, by rw [hk, bk]⟩
  -- `β₀ᵈ ∈ C`
  have hspl : (m.map (algebraMap C K)).Splits := IsAlgClosed.splits _
  have hcard : Multiset.card (m.map (algebraMap C K)).roots = m.natDegree := by
    rw [← natDegree_map (f := algebraMap C K)]; exact hspl.natDegree_eq_card_roots.symm
  obtain ⟨mm, hmm⟩ := prod_pow_form (algebraMap C K ζ) β₀ _ hroot
  have hc0 := hspl.coeff_zero_eq_prod_roots_of_monic (hmon.map _)
  rw [hmm, hcard, coeff_map, natDegree_map] at hc0
  set d := m.natDegree with hd
  have hζ0 : ζ ≠ 0 := hζ.ne_zero S.hn.ne'
  have hβd : β₀ ^ d = algebraMap C K ((-1) ^ d * m.coeff 0 / ζ ^ mm) := by
    rw [map_div₀, map_mul, map_pow, map_pow, map_neg, map_one, hc0]
    have : (algebraMap C K ζ) ^ mm ≠ 0 := pow_ne_zero _ ((_root_.map_ne_zero _).mpr hζ0)
    field_simp
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  -- `d ∣ n` and `d = n`
  have hdpos : 0 < d := minpoly.natDegree_pos hint
  have hdn : d ≤ S.n := by
    have := natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero S.hn _)
    rwa [natDegree_X_pow_sub_C] at this
  set cd : C := (-1) ^ d * m.coeff 0 / ζ ^ mm with hcd
  have hβn : β₀ ^ S.n = algebraMap C K (S.p.eval 0) := by rw [hv0, hp0]
  -- `β₀ᵍ ∈ C` for `g = gcd(d, n)`
  set g := Nat.gcd d S.n with hg
  have hβ0z : (β₀ : K) ≠ 0 := hβ₀
  have hβg : β₀ ^ g = algebraMap C K (cd ^ (Nat.gcdA d S.n) * S.p.eval 0 ^ (Nat.gcdB d S.n)) := by
    have hbez : (g : ℤ) = d * Nat.gcdA d S.n + S.n * Nat.gcdB d S.n := Nat.gcd_eq_gcd_ab d S.n
    rw [← zpow_natCast, hbez, zpow_add₀ hβ0z, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hβd,
      hβn, map_mul, map_zpow₀, map_zpow₀]
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hdpos
  have hdg : d ≤ g := by
    have := minpoly.min C β₀ (p := X ^ g - Polynomial.C (cd ^ (Nat.gcdA d S.n) * S.p.eval 0 ^
      (Nat.gcdB d S.n))) (monic_X_pow_sub_C _ hgpos.ne') (by
        rw [map_sub, map_pow, aeval_X, aeval_C, hβg, sub_self])
    rw [degree_X_pow_sub_C hgpos, degree_eq_natDegree (minpoly.ne_zero hint)] at this
    exact_mod_cast this
  have hdvdn : d ∣ S.n := by
    have : g = d := le_antisymm (Nat.le_of_dvd hdpos (Nat.gcd_dvd_left _ _)) hdg
    rw [← this]; exact Nat.gcd_dvd_right _ _
  have hdeq : d = S.n := by
    by_contra hne
    obtain ⟨t0, ht0⟩ := hdvdn
    have ht1 : t0 ≠ 1 := fun h ↦ hne (by rw [ht0, h, mul_one])
    obtain ⟨ℓ, hℓ, hℓt⟩ := Nat.exists_prime_and_dvd ht1
    obtain ⟨t, ht⟩ := hℓt
    apply hno ℓ hℓ ⟨d * t, by rw [ht0, ht]; ring⟩ (cd ^ t)
    apply (algebraMap C K).injective
    rw [map_pow, map_pow, ← hβd, ← pow_mul, ← pow_mul, ← hβn, ht0, ht]
    ring_nf
  -- `m = Xⁿ − p(0)`
  have hmeq : X ^ S.n - Polynomial.C (S.p.eval 0) = m :=
    eq_of_monic_of_dvd_of_natDegree_le hmon (monic_X_pow_sub_C _ S.hn.ne') hdvd
      (by rw [natDegree_X_pow_sub_C, ← hd, hdeq])
  intro w k
  have hroot : aeval (bk ζ β₀ k) m = 0 := by
    rw [← hmeq, map_sub, map_pow, aeval_X, aeval_C, S.bk_v ζ hζ β₀ hv0 k, hp0, sub_self]
  obtain ⟨τ, hτ⟩ := minpoly.exists_algEquiv_of_root' (K := C) (Algebra.IsAlgebraic.isAlgebraic β₀) hroot
  have hk : τ (bk ζ β₀ 0) = bk ζ β₀ k := by
    rw [bk, pow_zero, one_mul, hτ]
  rw [rv, rv, ← hk]
  conv_lhs => rw [← map_zero τ]
  rw [S.ordAt_galois τ w 0 _ (S.bk_ne ζ hζ β₀ hβ₀ 0) (S.bk_v ζ hζ β₀ hv0 0)]

include hζ hβ₀ hv0 in
/-- **Killing the orders over `x = 0`** when they are all equal. -/
theorem kill_full (hconst : ∀ (w : C⟮S.x⟯⟮S.y⟯) (k : ℕ), S.rv ζ β₀ w k = S.rv ζ β₀ w 0)
    (V : C⟮S.x⟯⟮S.y⟯) (hV : V ≠ 0) :
    ∃ V' : C⟮S.x⟯⟮S.y⟯, V' ≠ 0 ∧ ∃ M : ℕ, 0 < M ∧
      (∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
        S.ordAt K V' α β' = M * S.ordAt K V α β') ∧
      (∀ β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval 0 → S.ordAt K V' 0 β' = 0) := by
  have hxz : S.xE ^ (-S.rv ζ β₀ V 0) ≠ 0 := zpow_ne_zero _ S.xE_ne
  refine ⟨V * S.xE ^ (-S.rv ζ β₀ V 0), mul_ne_zero hV hxz, 1, one_pos, fun α β' hv hα ↦ ?_,
    fun β' hv ↦ ?_⟩
  · rw [S.ordAt_mul hv hV hxz, S.ordAt_zpow hv, S.ordAt_xE α β' hv, if_neg hα]; simp
  · obtain ⟨k, -, rfl⟩ := S.over_zero_k ζ hζ β₀ hβ₀ hv0 β' hv
    rw [S.ordAt_mul hv hV hxz, S.ordAt_zpow hv, S.ordAt_xE _ _ hv, if_pos rfl,
      if_neg (S.bk_ne ζ hζ β₀ hβ₀ k)]
    have := hconst V k
    simp only [rv] at this ⊢
    rw [this]; ring

include hζ hβ₀ hv0 in
/-- **Killing the orders over `x = 0` with witnesses** `Z_k` of `N_k (0, ζᵏβ₀)`. -/
theorem kill_tors (Z : ℕ → C⟮S.x⟯⟮S.y⟯) (N : ℕ → ℕ) (hZ0 : ∀ k < S.n, Z k ≠ 0)
    (hN : ∀ k < S.n, 0 < N k)
    (hZa : ∀ k < S.n, ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
      S.ordAt K (Z k) α β' = 0)
    (hZz : ∀ k < S.n, ∀ i < S.n, S.ordAt K (Z k) 0 (bk ζ β₀ i) = if i = k then (N k : ℤ) else 0)
    (V : C⟮S.x⟯⟮S.y⟯) (hV : V ≠ 0) :
    ∃ V' : C⟮S.x⟯⟮S.y⟯, V' ≠ 0 ∧ ∃ M : ℕ, 0 < M ∧
      (∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
        S.ordAt K V' α β' = M * S.ordAt K V α β') ∧
      (∀ β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval 0 → S.ordAt K V' 0 β' = 0) := by
  classical
  set Nt : ℕ := ∏ k ∈ Finset.range S.n, N k with hNt
  have hNt0 : 0 < Nt := Finset.prod_pos fun k hk ↦ hN k (Finset.mem_range.mp hk)
  have hNk : ∀ k < S.n, N k ∣ Nt := fun k hk ↦ Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hk)
  set P : C⟮S.x⟯⟮S.y⟯ := ∏ k ∈ Finset.range S.n, Z k ^ (-(((Nt / N k : ℕ) : ℤ) * S.rv ζ β₀ V k))
    with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k hk ↦
    zpow_ne_zero _ (hZ0 k (Finset.mem_range.mp hk))
  have hVN : V ^ (Nt : ℤ) ≠ 0 := zpow_ne_zero _ hV
  refine ⟨V ^ (Nt : ℤ) * P, mul_ne_zero hVN hP0, Nt, hNt0, fun α β' hv hα ↦ ?_, fun β' hv ↦ ?_⟩
  · rw [S.ordAt_mul hv hVN hP0, S.ordAt_zpow hv, hP,
      S.ordAt_prod hv _ _ (fun k hk ↦ zpow_ne_zero _ (hZ0 k (Finset.mem_range.mp hk))),
      Finset.sum_eq_zero fun k hk ↦ by
        rw [S.ordAt_zpow hv, hZa k (Finset.mem_range.mp hk) α β' hv hα, mul_zero]]
    ring
  · obtain ⟨i, hi, rfl⟩ := S.over_zero_k ζ hζ β₀ hβ₀ hv0 β' hv
    rw [S.ordAt_mul hv hVN hP0, S.ordAt_zpow hv, hP,
      S.ordAt_prod hv _ _ (fun k hk ↦ zpow_ne_zero _ (hZ0 k (Finset.mem_range.mp hk)))]
    simp only [S.ordAt_zpow hv]
    rw [Finset.sum_eq_single i (fun k hk hki ↦ by
        rw [hZz k (Finset.mem_range.mp hk) i hi, if_neg (Ne.symm hki), mul_zero])
      (fun h ↦ absurd (Finset.mem_range.mpr hi) h), hZz i hi i hi, if_pos rfl]
    have : ((Nt / N i : ℕ) : ℤ) * (N i : ℤ) = Nt := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (hNk i hi)]
    simp only [rv]
    linear_combination (-(S.ordAt K V 0 (bk ζ β₀ i))) * this

end SuperData

end Differential
