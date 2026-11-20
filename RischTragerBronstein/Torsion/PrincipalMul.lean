import RischTragerBronstein.Torsion.Descend

/-!
# Multiples of divisors (general curves)

* `DivGE.pow`: `div γ ≥ Γ − c ∞ₓ` gives `div γˢ ≥ s Γ − s c ∞ₓ`;
* `DivGE.mono`: lower requirements.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Mul

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable {S : CurveData C L}

lemma DivGE.pow {J : Type*} {α : J → C} {N : J → ℕ} {hN : ∀ j, 0 < N j}
    {lf : J → List (LaurentSeries K)}
    {hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod}
    {Γ : J → LaurentSeries K → ℕ} {c : ℕ} {γ : C⟮S.x⟯⟮S.y⟯} (hγ0 : γ ≠ 0)
    (h : S.DivGE α N hN lf hlf Γ c γ) (s : ℕ) :
    S.DivGE α N hN lf hlf (fun j r ↦ s * Γ j r) (s * c) (γ ^ s) := by
  have hne : ∀ (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (r : LaurentSeries K)
      (hr : (S.F.map g).eval r = 0), (S.embG g hg r hr (γ ^ s)).order =
        s * (S.embG g hg r hr γ).order := by
    intro g hg r hr
    rw [map_pow, HahnSeries.order_pow, nsmul_eq_mul]
  refine ⟨fun j r hr ↦ ?_, fun b hb N' hN' l hl r hr ↦ ?_, fun N' hN' l hl r hr ↦ ?_⟩
  · rw [hne]
    have := h.1 j r hr
    push_cast
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · rw [hne]
    exact mul_nonneg (by positivity) (h.2.1 b hb N' hN' l hl r hr)
  · rw [hne]
    have := h.2.2 N' hN' l hl r hr
    push_cast at this ⊢
    nlinarith

end CurveData

end Mul

section Prime

variable {O K₀ : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)] [Field K₀] [Algebra O K₀] [IsFractionRing O K₀]
variable {LK KK Lk kk : Type*} [Field LK] [Algebra K₀ LK] [Field KK] [Algebra K₀ KK] [IsAlgClosed KK]
  [Field Lk] [Algebra (IsLocalRing.ResidueField O) Lk] [Field kk]
  [Algebra (IsLocalRing.ResidueField O) kk] [IsAlgClosed kk]

local notation "𝕜" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "ι" => algebraMap O K₀

set_option maxHeartbeats 1000000 in
/-- **Torsion at a prime**: if `m Γ̄` is principal modulo `ϖ` and `(s ℓ) Γ` over `K₀` (`ℓ` a unit),
then `(m s) Γ` is principal over `K₀`. The place data are given structurally: each root `r` of the
branch systems has a place `π` and a ramification factor `s_r` with orders `s_r` times the place
orders, and `c' N − Γ(r) = s_r m_π`. -/
theorem principal_at_primeG {ϖ : O} (hϖ : Irreducible ϖ) (F : O[X][X]) (hF : F.Monic)
    (SK : CurveData K₀ LK) (hSK : SK.F = F.map (mapRingHom ι)) (hBrK : SK.HasBranches KK)
    (hBIK : SK.HasBranchesInf KK)
    (Sk : CurveData 𝕜 Lk) (hSk : Sk.F = F.map (mapRingHom ρ)) (hBrk : Sk.HasBranches kk)
    (hBIk : Sk.HasBranchesInf kk)
    (hnk : Sk.F.natDegree = SK.F.natDegree) (hn : 0 < SK.F.natDegree)
    -- the integral basis
    (B : Fin SK.F.natDegree → O[X][X]) (D : O[X]) (hDm : D.Monic) (δ : Fin SK.F.natDegree → ℕ)
    (hB0 : B ⟨0, hn⟩ = Polynomial.C D) (hδ0 : δ ⟨0, hn⟩ = 0)
    (hδ : ∀ j : Fin SK.F.natDegree, (j : ℕ) ≠ 0 → 1 ≤ δ j)
    (hBK : SK.IsIntBasis KK (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) δ)
    (hBk : Sk.IsIntBasis kk (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) (D.map ρ)
      (fun j ↦ δ (Fin.cast hnk j)))
    -- the base fibres
    {g : ℕ} (hg : ∑ j, δ j + 1 = g + SK.F.natDegree)
    (x : Fin g → O) (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (y : Fin g → Fin SK.F.natDegree → O)
    (hsplit : ∀ i, F.map (evalRingHom (x i)) = ∏ k, (X - Polynomial.C (y i k)))
    (hFu : ∀ i k, IsUnit (Sup.evalW (derivative F) (x i) (y i k)))
    (hdet : ∀ i, IsUnit (Matrix.det (Matrix.of fun kk j ↦ Sup.evalW (B j) (x i) (y i kk))))
    (hDx : ∀ i, IsUnit (D.eval (x i)))
    (hNS : ∀ q : Fin SK.F.natDegree → 𝕜[X], (∀ j, q j ≠ 0 → (q j).natDegree + δ j ≤ g) →
      (∀ i (k : Fin SK.F.natDegree), (k : ℕ) ≠ 0 →
        Sup.evalW (PsiC (fun j ↦ (B j).map (mapRingHom ρ)) q) (ρ (x i)) (ρ (y i k)) = 0) →
      ∀ i, Sup.evalW (PsiC (fun j ↦ (B j).map (mapRingHom ρ)) q) (ρ (x i)) (ρ (y i ⟨0, hn⟩)) = 0)
    -- the divisor `Γ`
    {J : Type*} [Fintype J] (α : J → O) (hα : ∀ j j', j ≠ j' → IsUnit (α j - α j'))
    (hαx : ∀ j i, IsUnit (α j - x i))
    (NK : J → ℕ) (hNK : ∀ j, 0 < NK j) (lK : J → List (LaurentSeries KK))
    (hlK : ∀ j, SK.F.map (branchSub (NK j) (algebraMap K₀ KK (ι (α j)))) =
      ((lK j).map fun r ↦ X - Polynomial.C r).prod)
    (ΓK : J → LaurentSeries KK → ℕ)
    (Nk : J → ℕ) (hNk : ∀ j, 0 < Nk j) (lk : J → List (LaurentSeries kk))
    (hlk : ∀ j, Sk.F.map (branchSub (Nk j) (algebraMap 𝕜 kk (ρ (α j)))) =
      ((lk j).map fun r ↦ X - Polynomial.C r).prod)
    (Γk : J → LaurentSeries kk → ℕ)
    (cΓ : ℕ) (c' dΓ : J → ℕ) (hdK : ∀ j, ((lK j).map (ΓK j)).sum = NK j * dΓ j)
    (hdk : ∀ j, ((lk j).map (Γk j)).sum = Nk j * dΓ j)
    (hsumΓ : ∑ j, dΓ j = cΓ * SK.F.natDegree) (hle : ∀ j, dΓ j ≤ SK.F.natDegree * c' j)
    -- places over `K₀` and the structure of the branch systems
    {P : Type*} [Fintype P] (pj : P → J) (e : P → ℕ) (he : ∀ π, 0 < e π)
    (mP : P → ℕ) (hmP : ∑ π, mP π = ∑ j, (SK.F.natDegree * c' j - dΓ j))
    (σK : P → Fin SK.F.natDegree → LaurentSeries K₀) (hσ : ∀ π j, LowerBd (σK π j) 0)
    (πK : J → LaurentSeries KK → P) (sK : J → LaurentSeries KK → ℕ)
    (hΓK : ∀ j r, r ∈ lK j → ((c' j * NK j : ℕ) : ℤ) - ΓK j r = sK j r * mP (πK j r))
    (hordK : ∀ (cK : Fin SK.F.natDegree → K₀[X]), cK ≠ 0 → ∀ (j : J) (r : LaurentSeries KK) (hr : r ∈ lK j)
      (u : ℕ), LowerBd (∑ i, branchSub (K := K₀) (e (πK j r)) (ι (α (pj (πK j r)))) (cK i) *
        σK (πK j r) i) u →
      ((sK j r * u : ℕ) : ℤ) ≤ (SK.embG (branchSub (NK j) (algebraMap K₀ KK (ι (α j))))
        (branchSub_injective _ (hNK j) _) r (SK.root_of_mem (hlK j) hr)
        (SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) cK)).order)
    (πk : J → LaurentSeries kk → P) (sk : J → LaurentSeries kk → ℕ)
    (hΓk : ∀ j r, r ∈ lk j → ((c' j * Nk j : ℕ) : ℤ) - Γk j r = sk j r * mP (πk j r))
    (hordk : ∀ (c : Fin SK.F.natDegree → O[X]), (¬ ∀ j, Polynomial.C ϖ ∣ c j) → ∀ (j : J) (r : LaurentSeries kk) (hr : r ∈ lk j)
      (u : ℕ), LowerBd (∑ i, branchSub (K := K₀) (e (πk j r)) (ι (α (pj (πk j r))))
        ((c i).map ι) * σK (πk j r) i) u →
      ((sk j r * u : ℕ) : ℤ) ≤ (Sk.embG (branchSub (Nk j) (algebraMap 𝕜 kk (ρ (α j))))
        (branchSub_injective _ (hNk j) _) r (Sk.root_of_mem (hlk j) hr)
        (Sk.elt (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) (D.map ρ)
          (fun j ↦ (c (Fin.cast hnk j)).map ρ))).order)
    -- the multiples
    (m s ℓ : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hℓ1 : 1 ≤ ℓ) (hℓ : IsUnit (ℓ : O))
    (γk : 𝕜⟮Sk.x⟯⟮Sk.y⟯) (hγk0 : γk ≠ 0)
    (hγk : Sk.DivGE (fun j ↦ ρ (α j)) Nk hNk lk hlk (fun j r ↦ m * Γk j r) (m * cΓ) γk)
    (Ξ : K₀⟮SK.x⟯⟮SK.y⟯) (hΞ0 : Ξ ≠ 0)
    (hΞ : SK.DivGE (fun j ↦ ι (α j)) NK hNK lK hlK (fun j r ↦ (s * ℓ) * ΓK j r) ((s * ℓ) * cΓ) Ξ) :
    ∃ γ : K₀⟮SK.x⟯⟮SK.y⟯, γ ≠ 0 ∧
      SK.DivGE (fun j ↦ ι (α j)) NK hNK lK hlK (fun j r ↦ (m * s) * ΓK j r) ((m * s) * cΓ) γ := by
  classical
  have hγk2 := hγk.pow hγk0 s
  have e1 : (fun j r ↦ s * (m * Γk j r)) = fun j r ↦ (m * s) * Γk j r := by
    funext j r; ring
  rw [e1, show s * (m * cΓ) = (m * s) * cΓ by ring] at hγk2
  have hΞ2 := hΞ.pow hΞ0 m
  have e2 : (fun j r ↦ m * ((s * ℓ) * ΓK j r)) = fun j r ↦ ℓ * ((m * s) * ΓK j r) := by
    funext j r; ring
  rw [e2, show m * ((s * ℓ) * cΓ) = ℓ * ((m * s) * cΓ) by ring] at hΞ2
  refine torsion_descendsG hϖ F hF SK hSK hBrK hBIK Sk hSk hBrk hBIk hnk hn B D hDm δ hB0 hδ0 hδ hBK
    hBk hg x hx y hsplit hFu hdet hDx hNS α hα hαx NK hNK lK hlK (fun j r ↦ (m * s) * ΓK j r)
    Nk hNk lk hlk (fun j r ↦ (m * s) * Γk j r) ((m * s) * cΓ) (fun j ↦ (m * s) * c' j)
    (fun j ↦ (m * s) * dΓ j) (fun j ↦ ?_) (fun j ↦ ?_) ?_ (fun j ↦ ?_) pj e he
    (fun π ↦ (m * s) * mP π) ?_ σK hσ (fun cK hcK hrep j r hr ↦ ?_) (fun c hc hrep j r hr ↦ ?_)
    (γk ^ s) (pow_ne_zero _ hγk0) hγk2 ℓ hℓ1 hℓ (Ξ ^ m) (pow_ne_zero _ hΞ0) hΞ2
  · rw [List.sum_map_mul_left, hdK j]; ring
  · rw [List.sum_map_mul_left, hdk j]; ring
  · rw [← Finset.mul_sum, hsumΓ]; ring
  · have := hle j
    calc (m * s) * dΓ j ≤ (m * s) * (SK.F.natDegree * c' j) := Nat.mul_le_mul_left _ this
      _ = SK.F.natDegree * ((m * s) * c' j) := by ring
  · rw [← Finset.mul_sum, hmP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Nat.mul_sub]; ring_nf
  · have h1 := hordK cK hcK j r hr _ (hrep (πK j r))
    have h2 := hΓK j r hr
    have h3 : (((m * s) * c' j * NK j : ℕ) : ℤ) - (((m * s) * ΓK j r : ℕ) : ℤ) =
        ((sK j r * ((m * s) * mP (πK j r)) : ℕ) : ℤ) := by
      push_cast at h2 ⊢; linear_combination ((m : ℤ) * s) * h2
    linarith
  · have h1 := hordk c hc j r hr _ (hrep (πk j r))
    have h2 := hΓk j r hr
    have h3 : (((m * s) * c' j * Nk j : ℕ) : ℤ) - (((m * s) * Γk j r : ℕ) : ℤ) =
        ((sk j r * ((m * s) * mP (πk j r)) : ℕ) : ℤ) := by
      push_cast at h2 ⊢; linear_combination ((m : ℤ) * s) * h2
    linarith

end Prime

end Curves
