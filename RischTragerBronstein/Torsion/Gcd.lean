import RischTragerBronstein.Torsion.PrincCurve

/-!
# Principal multiples form a subgroup (general curves)

* `divGE_exact`: a witness of `div γ ≥ Γ − c ∞ₓ` (with `deg Γ = c n`) has exactly this divisor;
* `principal_gcd`: if `a Γ − a c ∞ₓ` and `b Γ − b c ∞ₓ` are principal, so is `gcd(a, b)` times it.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Gcd

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]

omit [Algebra C K] [IsAlgClosed K] in
lemma order_zpow' (z : LaurentSeries K) (hz : z ≠ 0) (k : ℤ) : (z ^ k).order = k * z.order := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, HahnSeries.order_pow, nsmul_eq_mul]
  · rw [zpow_neg, zpow_natCast, order_inv' _ (pow_ne_zero _ hz), HahnSeries.order_pow,
      nsmul_eq_mul]
    ring

namespace CurveData

variable (S : CurveData C L)

/-- **Exactness of principal witnesses.** -/
theorem divGE_exact (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K) {J : Type*} [Fintype J] (α : J → C)
    (hα : Function.Injective α) (N : J → ℕ) (hN : ∀ j, 0 < N j) (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (Γ : J → LaurentSeries K → ℕ) (c : ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree)
    (γ : C⟮S.x⟯⟮S.y⟯) (hγ0 : γ ≠ 0) (hγ : S.DivGE α N hN lf hlf Γ c γ) :
    (∀ j r (hr : r ∈ lf j), (Γ j r : ℤ) = (S.embG (branchSub (N j) (algebraMap C K (α j)))
      (branchSub_injective _ (hN j) _) r (S.root_of_mem (hlf j) hr) γ).order) ∧
    (∀ b : K, b ∉ Set.range (fun j ↦ algebraMap C K (α j)) → ∀ (N' : ℕ) (hN' : N' ≠ 0)
      (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N' b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), (S.embG (branchSub N' b)
        (branchSub_injective N' (Nat.pos_of_ne_zero hN') b) r (S.root_of_mem hl hr) γ).order = 0) ∧
    (∀ (N' : ℕ) (hN' : N' ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub N') = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), -((N' * c : ℕ) : ℤ) = (S.embG (infSub N')
        (infSub_injective N' (Nat.pos_of_ne_zero hN')) r (S.root_of_mem hl hr) γ).order) := by
  have key : ∀ (Ni : ℕ) (hNi : 0 < Ni) (li : List (LaurentSeries K))
      (hli : S.F.map (infSub Ni) = (li.map fun r ↦ X - Polynomial.C r).prod), _ := fun Ni hNi li hli ↦
    S.exact_fn hBr γ hγ0 (fun j ↦ algebraMap C K (α j))
      (fun a b h ↦ hα ((algebraMap C K).injective h)) N hN lf hlf (fun j r ↦ (Γ j r : ℤ))
      (fun j r hr ↦ hγ.1 j r hr) (fun b hb N' hN' l hl r hr ↦ hγ.2.1 b hb N' hN' l hl r hr)
      Ni hNi li hli (fun _ ↦ -((Ni * c : ℕ) : ℤ))
      (fun r hr ↦ hγ.2.2 Ni hNi.ne' li hli r hr) (fun j ↦ (dΓ j : ℤ)) (fun j ↦ by
        rw [list_sum_cast, hdΓ j]; push_cast; ring)
      (-((c * S.F.natDegree : ℕ) : ℤ)) (by
        rw [List.map_const', List.sum_replicate, S.length_of_split hli]; push_cast; ring)
      (by rw [← Nat.cast_sum, hsumΓ]; ring)
  obtain ⟨Ni, hNi, li, -, hli⟩ := hBI
  obtain ⟨h1, -, h3⟩ := key Ni (Nat.pos_of_ne_zero hNi) li hli
  exact ⟨h1, h3, fun N' hN' l hl r hr ↦ (key N' (Nat.pos_of_ne_zero hN') l hl).2.1 r hr⟩

/-- **Principal multiples are closed under `gcd`.** -/
theorem principal_gcd (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K) {J : Type*} [Fintype J]
    (α : J → C) (hα : Function.Injective α) (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (Γ : J → LaurentSeries K → ℕ) (c : ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree)
    (a b : ℕ) (γa γb : C⟮S.x⟯⟮S.y⟯) (hγa0 : γa ≠ 0) (hγb0 : γb ≠ 0)
    (hγa : S.DivGE α N hN lf hlf (fun j r ↦ a * Γ j r) (a * c) γa)
    (hγb : S.DivGE α N hN lf hlf (fun j r ↦ b * Γ j r) (b * c) γb) :
    ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
      S.DivGE α N hN lf hlf (fun j r ↦ Nat.gcd a b * Γ j r) (Nat.gcd a b * c) γ := by
  have hscale : ∀ s : ℕ, (∀ j, ((lf j).map fun r ↦ s * Γ j r).sum = N j * (s * dΓ j)) ∧
      ∑ j, s * dΓ j = s * c * S.F.natDegree := fun s ↦
    ⟨fun j ↦ by rw [List.sum_map_mul_left, hdΓ j]; ring, by rw [← Finset.mul_sum, hsumΓ]; ring⟩
  obtain ⟨ea1, ea2, ea3⟩ := S.divGE_exact hBr hBI α hα N hN lf hlf _ _ _ (hscale a).1 (hscale a).2
    γa hγa0 hγa
  obtain ⟨eb1, eb2, eb3⟩ := S.divGE_exact hBr hBI α hα N hN lf hlf _ _ _ (hscale b).1 (hscale b).2
    γb hγb0 hγb
  set x := Nat.gcdA a b
  set y := Nat.gcdB a b
  have hxy : (Nat.gcd a b : ℤ) = a * x + b * y := Nat.gcd_eq_gcd_ab a b
  have hne : γa ^ x * γb ^ y ≠ 0 := mul_ne_zero (zpow_ne_zero _ hγa0) (zpow_ne_zero _ hγb0)
  have hord : ∀ (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (r : LaurentSeries K)
      (hr : (S.F.map g).eval r = 0), (S.embG g hg r hr (γa ^ x * γb ^ y)).order =
        x * (S.embG g hg r hr γa).order + y * (S.embG g hg r hr γb).order := by
    intro g hg r hr
    have h1 : S.embG g hg r hr γa ≠ 0 := (map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hγa0
    have h2 : S.embG g hg r hr γb ≠ 0 := (map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hγb0
    rw [map_mul, map_zpow₀, map_zpow₀, HahnSeries.order_mul (zpow_ne_zero _ h1)
      (zpow_ne_zero _ h2), order_zpow' _ h1, order_zpow' _ h2]
  refine ⟨γa ^ x * γb ^ y, hne, fun j r hr ↦ ?_, fun bb hb N' hN' l hl r hr ↦ ?_,
    fun N' hN' l hl r hr ↦ ?_⟩
  · rw [hord, ← ea1 j r hr, ← eb1 j r hr]
    push_cast
    rw [hxy]; ring_nf; exact le_refl _
  · rw [hord, ea2 bb hb N' hN' l hl r hr, eb2 bb hb N' hN' l hl r hr]; simp
  · rw [hord, ← ea3 N' hN' l hl r hr, ← eb3 N' hN' l hl r hr]
    push_cast
    rw [hxy]; ring_nf; exact le_refl _

/-- **Two primes bound the torsion order**, for any multiplier `mt` divisible by every
`gcd(m_p pᵛ, m_q q^w)` (e.g. `m_p m_q`, or `pairMult`). -/
theorem principal_two_primes_mt (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K) {J : Type*}
    [Fintype J] (α : J → C) (hα : Function.Injective α) (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (Γ : J → LaurentSeries K → ℕ) (c : ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (mp mq : ℕ) (hmp : 0 < mp) (hmq : 0 < mq)
    (hstep_p : ∀ M : ℕ, 0 < M → (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGE α N hN lf hlf (fun j r ↦ M * Γ j r) (M * c) γ) →
      ∃ v : ℕ, ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGE α N hN lf hlf (fun j r ↦ (mp * p ^ v) * Γ j r) ((mp * p ^ v) * c) γ)
    (hstep_q : ∀ M : ℕ, 0 < M → (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGE α N hN lf hlf (fun j r ↦ M * Γ j r) (M * c) γ) →
      ∃ w : ℕ, ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGE α N hN lf hlf (fun j r ↦ (mq * q ^ w) * Γ j r) ((mq * q ^ w) * c) γ)
    (mt : ℕ) (hmt : ∀ v w : ℕ, Nat.gcd (mp * p ^ v) (mq * q ^ w) ∣ mt)
    (M : ℕ) (hM : 0 < M) (htor : ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGE α N hN lf hlf (fun j r ↦ M * Γ j r) (M * c) γ) :
    ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
      S.DivGE α N hN lf hlf (fun j r ↦ mt * Γ j r) (mt * c) γ := by
  obtain ⟨v, γp, hγp0, hγp⟩ := hstep_p M hM htor
  obtain ⟨w, γq, hγq0, hγq⟩ := hstep_q M hM htor
  obtain ⟨γg, hγg0, hγg⟩ := S.principal_gcd hBr hBI α hα N hN lf hlf Γ c dΓ hdΓ hsumΓ _ _ γp γq
    hγp0 hγq0 hγp hγq
  set g := Nat.gcd (mp * p ^ v) (mq * q ^ w) with hg
  have hdvd : g ∣ mt := hmt v w
  obtain ⟨t, ht⟩ := hdvd
  have hpow := hγg.pow hγg0 t
  refine ⟨γg ^ t, pow_ne_zero _ hγg0, ?_⟩
  have e1 : (fun j r ↦ t * (g * Γ j r)) = fun j r ↦ mt * Γ j r := by
    funext j r; rw [ht]; ring
  rw [e1, show t * (g * c) = mt * c by rw [ht]; ring] at hpow
  exact hpow

/-- `gcd(m_p pᵛ, m_q q^w)` divides `m_p m_q` (`p ≠ q` primes). -/
lemma gcd_dvd_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (mp mq v w : ℕ) :
    Nat.gcd (mp * p ^ v) (mq * q ^ w) ∣ mp * mq := by
  have hcop : Nat.Coprime (p ^ v) (q ^ w) :=
    Nat.Coprime.pow v w ((Nat.coprime_primes hp hq).mpr hpq)
  have h1 : Nat.gcd (mp * p ^ v) (mq * q ^ w) ∣ (mp * mq) * p ^ v :=
    (Nat.gcd_dvd_left _ _).trans ⟨mq, by ring⟩
  have h2 : Nat.gcd (mp * p ^ v) (mq * q ^ w) ∣ (mp * mq) * q ^ w :=
    (Nat.gcd_dvd_right _ _).trans ⟨mp, by ring⟩
  have h3 := Nat.dvd_gcd h1 h2
  rwa [Nat.gcd_mul_left, hcop, mul_one] at h3

/-- **Two primes bound the torsion order.** If every principal multiple `N Γ` forces
`(m_p p^v) Γ` and `(m_q q^w) Γ` to be principal for some `v, w` (distinct primes `p, q`), then any
torsion class has `(m_p m_q) Γ` principal. -/
theorem principal_two_primes (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K) {J : Type*}
    [Fintype J] (α : J → C) (hα : Function.Injective α) (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (Γ : J → LaurentSeries K → ℕ) (c : ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (mp mq : ℕ) (hmp : 0 < mp) (hmq : 0 < mq)
    (hstep_p : ∀ M : ℕ, 0 < M → (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGE α N hN lf hlf (fun j r ↦ M * Γ j r) (M * c) γ) →
      ∃ v : ℕ, ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGE α N hN lf hlf (fun j r ↦ (mp * p ^ v) * Γ j r) ((mp * p ^ v) * c) γ)
    (hstep_q : ∀ M : ℕ, 0 < M → (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGE α N hN lf hlf (fun j r ↦ M * Γ j r) (M * c) γ) →
      ∃ w : ℕ, ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGE α N hN lf hlf (fun j r ↦ (mq * q ^ w) * Γ j r) ((mq * q ^ w) * c) γ)
    (M : ℕ) (hM : 0 < M) (htor : ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGE α N hN lf hlf (fun j r ↦ M * Γ j r) (M * c) γ) :
    ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
      S.DivGE α N hN lf hlf (fun j r ↦ (mp * mq) * Γ j r) ((mp * mq) * c) γ := by
  exact S.principal_two_primes_mt hBr hBI α hα N hN lf hlf Γ c dΓ hdΓ hsumΓ p q hp hq hpq mp mq hmp hmq
    hstep_p hstep_q (mp * mq) (gcd_dvd_mul_primes hp hq hpq mp mq) M hM htor

end CurveData

end Gcd

end Curves
