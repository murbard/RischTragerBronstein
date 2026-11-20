import RischTragerBronstein.Mixed.KXExp2

/-!
# The Mordell–Weil exception of `kxDecide`: the non-elementary direction

`kxe_norel`: if a class `k₀` with a non-zero residue satisfies **no relation**
`N · Δ_{k₀} + μ · δ₀ ~ 0` (`N > 0`, `μ ∈ ℤ`; `δ₀ = P₊ − P₋`), then `b y` has no Liouville form.
This replaces the two hypotheses of `kxe_nontors` (`δ₀` killable, `Δ_{k₀}` non-torsion) by the
exact Mordell–Weil condition — a two-point independence statement, certified by the height
pairing (`EllNT`, `EllTwist`) in genus one.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Classical

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

section ExpMain2

variable (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η * X))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (hgood : ∀ α : K, ¬ α = 0 → α′ ≠ ((Polynomial.C η * X).map (algebraMap C K)).eval α)
  (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
  {r nk : ℕ} (c β : Fin r → C) (hc : Function.Injective c) (hc0 : ∀ q, c q ≠ 0)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (cl : Fin r → Fin nk)
  (ρ : Fin nk → C)
  (P : C[X]) (l : ℕ) (b : L) (hb : b ∈ C⟮S.x⟯)
  (D : C[X]) (R : Fin r → C[X]) (hDR : ∀ q, D = (X - Polynomial.C (c q)) * R q)
  (hRne : ∀ q, (R q).eval (c q) ≠ 0)
  (hDoff : ∀ α : K, ¬ α = 0 → (∀ q, α ≠ algebraMap C K (c q)) → (D.map (algebraMap C K)).eval α ≠ 0)
  (hbP : b * aeval S.x (D * S.p ^ l) = aeval S.x P)
  (hres : ∀ q, P.eval (c q) * β q = m q * ρ (cl q) * ((Polynomial.C η * X).eval (c q) - (c q)′) *
    (R q * S.p ^ l).eval (c q))
  (hn2 : S.n = 2) (hcop : Nat.Coprime S.n S.p.natDegree) (β₀ : K) (hβ₀ : β₀ ≠ 0)
  (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)

include hx hK hgood hconstC hc hc0 hβ hb hDR hRne hDoff hbP hres hn2 hβ₀ hv0 in
/-- **No Mordell–Weil relation ⇒ no Liouville form.** -/
theorem kxe_norel (k0 : Fin nk) (hk0 : ∃ q, cl q = k0 ∧ m q ≠ 0)
    (hρ : ∀ e : Fin nk → ℚ, ∑ kk, (e kk : C) * ρ kk = 0 → ∀ kk, e kk = 0)
    (hnorel : ∀ f : C⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
      ¬ ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
        (S.ordAt K f α β' : ℚ) = N * dK c β m cl k0 (α, β') + μ * dZ β₀ (α, β'))
    (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) : False := by
  classical
  obtain ⟨k, d, w, hw, -, -, -, lam, hord, hsum⟩ :=
    S.kxm_core (K := K) (Polynomial.C η * X) hx hK (fun α ↦ α = 0) hgood hconstC c β hc
      (hbadc_of c hc0) hβ m cl ρ P l b hb D R hDR hRne hDoff hbP hres hn2 hbm s cs u hcs hu v hv heq
  set wj : Fin k → C⟮S.x⟯⟮S.y⟯ := fun j ↦ ⟨w j, (hw j j.2).1⟩ with hwj
  have hwj0 : ∀ j, wj j ≠ 0 := fun j h ↦ (hw j j.2).2 (congrArg Subtype.val h)
  -- the normalized, `δ₀`-free logarithms
  have hg : ∀ j : Fin k, ∃ μ : ℤ, ∃ g : C⟮S.x⟯⟮S.y⟯, g ≠ 0 ∧
      S.DivKZ β₀ c β m cl g (fun kk ↦ 2 * lam kk j) μ := fun j ↦ by
    obtain ⟨hz0, hzo⟩ := S.kxe_norm hn2 β₀ hβ₀ hv0 c β hc0 m cl (wj j) (hwj0 j)
      (fun kk ↦ lam kk j) (fun α β' hv hα ↦ hord j j.2 α β' hv hα)
    exact ⟨_, _, hz0, hzo⟩
  choose μj g hg0 hgo using hg
  set M : Fin k → ℕ := fun _ ↦ 1 with hMdef
  have hM : ∀ j, 0 < M j := fun _ ↦ Nat.one_pos
  obtain ⟨φ, hφ⟩ := _root_.exists_sep_functional (ρ := ρ) hρ
  set t : Fin k → ℚ := fun j ↦ φ (d j) k0 with ht
  obtain ⟨Dn, hD0, A, hA⟩ := exists_int_mul (fun j ↦ t j / (2 * M j))
  set z := ∏ j, g j ^ A j with hz
  have hz0 : z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (hg0 j)
  have hcoef : ∀ kk, (∃ q, cl q = kk ∧ m q ≠ 0) →
      ∑ j : Fin k, (A j : ℚ) * (M j * (2 * lam kk j)) = if kk = k0 then (Dn : ℚ) else 0 := by
    intro kk hkk
    have hs := hsum kk hkk
    have hφs := congrArg (fun x ↦ φ x k0) hs
    simp only [map_sum, hφ kk] at hφs
    have e1 : ∑ j ∈ Finset.range k, (φ ((lam kk j : C) * d j)) k0 =
        ∑ j : Fin k, lam kk j * t j := by
      rw [← Fin.sum_univ_eq_sum_range (fun j ↦ (φ ((lam kk j : C) * d j)) k0)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Rat.smul_def, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_apply, e1] at hφs
    simp only [Pi.single_apply] at hφs
    have e2 : ∀ j : Fin k, (A j : ℚ) * (M j * (2 * lam kk j)) = Dn * (lam kk j * t j) := fun j ↦ by
      have hMj : (M j : ℚ) ≠ 0 := by exact_mod_cast (hM j).ne'
      rw [hA j]; field_simp
    rw [Finset.sum_congr rfl fun j _ ↦ e2 j, ← Finset.mul_sum, hφs]
    split_ifs with h1 h2 h2
    · ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring
  have hordz : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K z α β' : ℚ) = Dn * dK c β m cl k0 (α, β') +
        ((∑ j, A j * μj j : ℤ) : ℚ) * dZ β₀ (α, β') := by
    intro α β' hv
    rw [hz, S.ordAt_prod hv _ _ (fun j _ ↦ zpow_ne_zero _ (hg0 j))]
    push_cast
    simp only [S.ordAt_zpow hv, Int.cast_mul]
    have e2 : ∀ j : Fin k, (S.ordAt K (g j) α β' : ℚ) =
        ∑ kk, (M j * (2 * lam kk j)) * dK c β m cl kk (α, β') + μj j * dZ β₀ (α, β') := fun j ↦ by
      rw [hgo j α β' hv]; simp [hMdef]
    simp only [e2, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm, Finset.sum_eq_single k0]
      · have := hcoef k0 hk0
        rw [if_pos rfl] at this
        rw [← this, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      · intro kk _ hkk
        by_cases hkk' : ∃ q, cl q = kk ∧ m q ≠ 0
        · have := hcoef kk hkk'
          rw [if_neg hkk] at this
          rw [show ∑ j : Fin k, (A j : ℚ) * ((M j * (2 * lam kk j)) * dK c β m cl kk (α, β')) =
            (∑ j : Fin k, (A j : ℚ) * (M j * (2 * lam kk j))) * dK c β m cl kk (α, β') by
              rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ ↦ by ring, this, zero_mul]
        · push Not at hkk'
          have hd0 : dK (K := K) c β m cl kk (α, β') = 0 := Finset.sum_eq_zero fun q _ ↦ by
            by_cases hq : cl q = kk
            · simp [mK, hq, hkk' q hq]
            · simp [mK, hq]
          simp [hd0]
      · simp
    · rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ ↦ by ring
  exact hnorel z hz0 Dn hD0 _ hordz

end ExpMain2

end SuperData

end Differential
