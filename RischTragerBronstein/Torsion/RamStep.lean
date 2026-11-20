import RischTragerBronstein.Torsion.RamPrime
import RischTragerBronstein.Torsion.PrimeStepUnram

/-!
# The prime step over a base field for divisors at places

* `lmap_rot`, `lmap_lsub`: coefficient maps commute with rotations and reparametrizations;
* `princTest_transport_N`: the principality test along branch systems `x = a + Tᴺ` is invariant
  under a field embedding;
* `prime_step_places`: the analogue of `prime_step_unram` for divisors at places with
  representatives.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Nat

variable {C C' : Type*} [Field C] [Field C'] (φ : C →+* C')

lemma lmap_rot (ζ : C) (hζ : ζ ≠ 0) (z : LaurentSeries C) :
    lmap φ (rot ζ hζ z) = rot (φ ζ) ((map_ne_zero_iff φ φ.injective).mpr hζ) (lmap φ z) := by
  ext k
  rw [lmap_coeff, rot_coeff, rot_coeff, lmap_coeff, map_mul, map_zpow₀]

lemma lmap_lsub (s : ℕ) (hs : 0 < s) (z : LaurentSeries C) :
    lmap φ (lsub s hs z) = lsub s hs (lmap φ z) := by
  ext k
  rw [lmap_coeff]
  by_cases hk : (s : ℤ) ∣ k
  · obtain ⟨j, rfl⟩ := hk
    rw [lsub_coeff_mul, lsub_coeff_mul, lmap_coeff]
  · rw [lsub_coeff_not_dvd s hs _ _ hk, lsub_coeff_not_dvd s hs _ _ hk, map_zero]

end Nat

section Transport

variable {C C' L L' : Type*} [Field C] [Field C'] [Field L] [Field L'] [Algebra C L] [Algebra C' L']

/-- **Transport of the test along general branch systems.** -/
theorem princTest_transport_N (S : CurveData C L) (S' : CurveData C' L') (φ : C →+* C')
    (hnK : S'.F.natDegree = S.F.natDegree) (B : Fin S.F.natDegree → C[X][X]) (D : C[X])
    (δ : Fin S.F.natDegree → ℕ) (B' : Fin S'.F.natDegree → C'[X][X]) (D' : C'[X])
    (hB' : ∀ i, B' i = (B (Fin.cast hnK i)).map (mapRingHom φ)) (hD' : D' = D.map φ)
    {J : Type*} (N : J → ℕ) (α : J → C) (α' : J → C') (hα' : ∀ j, α' j = φ (α j))
    (rC : J → Fin S.F.natDegree → LaurentSeries C) (rC' : J → Fin S'.F.natDegree → LaurentSeries C')
    (hr' : ∀ j k, rC' j k = lmap φ (rC j (Fin.cast hnK k)))
    (hσ : ∀ (q : J × Fin S.F.natDegree) i, LowerBd (basisSer B D (N q.1) (α q.1) (rC q.1 q.2) i) 0)
    [Fintype J] (β : J → Fin S.F.natDegree → ℕ) (M : ℕ) :
    princTest δ M (fun q : J × Fin S.F.natDegree ↦ N q.1) (fun q ↦ α q.1)
        (fun q i ↦ basisSer B D (N q.1) (α q.1) (rC q.1 q.2) i) (fun q ↦ β q.1 q.2) ↔
      princTest (fun i ↦ δ (Fin.cast hnK i)) M (fun q : J × Fin S'.F.natDegree ↦ N q.1)
        (fun q ↦ α' q.1) (fun q i ↦ basisSer B' D' (N q.1) (α' q.1) (rC' q.1 q.2) i)
        (fun q ↦ β q.1 (Fin.cast hnK q.2)) := by
  rw [← princTest_map_iff φ δ M _ _ _ _ hσ, ← princTest_cast hnK]
  set eq : J × Fin S'.F.natDegree ≃ J × Fin S.F.natDegree :=
    Equiv.prodCongr (Equiv.refl J) (finCongr hnK) with heq
  rw [← princTest_reindex (fun i ↦ δ (Fin.cast hnK i)) M eq]
  have e1 : (fun q : J × Fin S'.F.natDegree ↦ φ (α (eq q).1)) = fun q ↦ α' q.1 := by
    funext q; rw [hα']; rfl
  have e2 : (fun (q : J × Fin S'.F.natDegree) (i : Fin S'.F.natDegree) ↦
      lmap φ (basisSer B D (N (eq q).1) (α (eq q).1) (rC (eq q).1 (eq q).2) (Fin.cast hnK i))) =
      fun q i ↦ basisSer B' D' (N q.1) (α' q.1) (rC' q.1 q.2) i := by
    funext q i
    have hBf : B' = fun i ↦ (B (Fin.cast hnK i)).map (mapRingHom φ) := funext hB'
    rw [basisSer_map, hr', hα', hD', hBf]
    rfl
  simp only [e1] at *
  rw [show (fun (q : J × Fin S'.F.natDegree) (i : Fin S'.F.natDegree) ↦
      lmap φ (basisSer B D (N (eq q).1) (α (eq q).1) (rC (eq q).1 (eq q).2) (Fin.cast hnK i))) = _ from e2]
  rfl

end Transport

section SerN

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- The basis expansions along a full branch system are integral. -/
lemma basisSer_lowerBd_N {B : Fin S.F.natDegree → C[X][X]} {D : C[X]}
    {δ : Fin S.F.natDegree → ℕ} (hB : S.IsIntBasis K B D δ) (N : ℕ) (hN : 0 < N) (a : C)
    (r : Fin S.F.natDegree → LaurentSeries C)
    (hsp : S.F.map (branchSub (C := C) (K := C) N a) = ∏ k, (X - Polynomial.C (r k)))
    (k i : Fin S.F.natDegree) : LowerBd (basisSer B D N a (r k) i) 0 := by
  have hroot : (S.F.map (branchSub (K := C) N a)).eval (r k) = 0 := by
    rw [hsp, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hl := S.split_lmap (K := K) N a r hsp
  have h1 := hB.reg i (algebraMap C K a) N hN.ne' _ hl _ (List.mem_ofFn.mpr ⟨k, rfl⟩)
  rw [S.embG_lmap_fnWQ N hN a _ hroot] at h1
  exact (lowerBd_lmap_iff _ _ _).mp (lowerBd_of_le_order _ 0 h1)

end CurveData

end SerN

section SplitL

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

/-- Splitting over `C` gives the list splitting over `K` (any index type). -/
lemma split_lmap' (F : C[X][X]) (N : ℕ) (a : C) {m : ℕ} (r : Fin m → LaurentSeries C)
    (hs : F.map (branchSub (C := C) (K := C) N a) = ∏ k, (X - Polynomial.C (r k))) :
    F.map (branchSub N (algebraMap C K a)) =
      ((List.ofFn fun k ↦ lmap (algebraMap C K) (r k)).map fun r ↦ X - Polynomial.C r).prod := by
  have h : branchSub (C := C) (K := K) N (algebraMap C K a) =
      (lmap (algebraMap C K)).comp (branchSub (K := C) N a) :=
    RingHom.ext fun P ↦ (lmap_branchSub N a P).symm
  rw [h, ← Polynomial.map_map, hs, Polynomial.map_prod, List.map_ofFn, List.prod_ofFn]
  exact Finset.prod_congr rfl fun k _ ↦ by simp

lemma extend_ne_zero {α β γ : Type*} [Zero γ] {f : α → β} (hf : Function.Injective f) (g : α → γ)
    (d : β → γ) (hg : ∀ a, g a ≠ 0) (hd : ∀ b, d b ≠ 0) (b : β) : Function.extend f g d b ≠ 0 := by
  classical
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb; rw [hf.extend_apply]; exact hg a
  · rw [Function.extend_apply' _ _ _ hb]; exact hd b

lemma rot_congr' {K : Type*} [Field K] {ζ ζ' : K} (h : ζ = ζ') (hζ : ζ ≠ 0) (hζ' : ζ' ≠ 0)
    (z : LaurentSeries K) : rot ζ hζ z = rot ζ' hζ' z := by subst h; rfl

lemma lsub_congr' {K : Type*} [Field K] {s s' : ℕ} (h : s = s') (hs : 0 < s) (hs' : 0 < s')
    (z : LaurentSeries K) : lsub s hs z = lsub s' hs' z := by subst h; rfl

end SplitL

section StepP

variable {O K₀ : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)] [Field K₀] [Algebra O K₀] [IsFractionRing O K₀]
variable {LK KK Lk kk : Type*} [Field LK] [Algebra K₀ LK] [Field KK] [Algebra K₀ KK] [IsAlgClosed KK]
  [Field Lk] [Algebra (IsLocalRing.ResidueField O) Lk] [Field kk]
  [Algebra (IsLocalRing.ResidueField O) kk] [IsAlgClosed kk]

local notation "𝕜" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "ι" => algebraMap O K₀

set_option maxHeartbeats 8000000 in
/-- **The prime step for divisors at places.** The divisor is given at the roots of full branch
systems `x = α_j + T^{N_j}`: the root `k` above `α_j` is `ζ_{jk}`-rotation of the reparametrized
(`s_{jk}`) representative of the place `π_{jk}`, with multiplicity `s_{jk} Γ_{π_{jk}}`. -/
theorem prime_step_places {ϖ : O} (hϖ : Irreducible ϖ) (F : O[X][X]) (hF : F.Monic)
    (SK : CurveData K₀ LK) (hSK : SK.F = F.map (mapRingHom ι)) (hBrK : SK.HasBranches KK)
    (hBIK : SK.HasBranchesInf KK)
    (Sk : CurveData 𝕜 Lk) (hSk : Sk.F = F.map (mapRingHom ρ)) (hBrk : Sk.HasBranches kk)
    (hBIk : Sk.HasBranchesInf kk)
    (hnk : Sk.F.natDegree = SK.F.natDegree) (hn : 0 < SK.F.natDegree)
    (B : Fin SK.F.natDegree → O[X][X]) (D : O[X]) (hDm : D.Monic) (δ : Fin SK.F.natDegree → ℕ)
    (hB0 : B ⟨0, hn⟩ = Polynomial.C D) (hδ0 : δ ⟨0, hn⟩ = 0)
    (hδ : ∀ j : Fin SK.F.natDegree, (j : ℕ) ≠ 0 → 1 ≤ δ j)
    (hBK : SK.IsIntBasis KK (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) δ)
    (hBk : Sk.IsIntBasis kk (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) (D.map ρ)
      (fun j ↦ δ (Fin.cast hnk j)))
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
    {J : Type*} [Fintype J] (α : J → O) (hα : ∀ j j', j ≠ j' → IsUnit (α j - α j'))
    (hαx : ∀ j i, IsUnit (α j - x i))
    (hDα : ∀ j, ∃ μ : ℕ, ∃ Q : O[X], D.comp (X + Polynomial.C (α j)) = X ^ μ * Q ∧ IsUnit (Q.eval 0))
    (N : J → ℕ) (hN : ∀ j, 0 < N j)
    {P : Type*} [Fintype P] (pj : P → J) (e : P → ℕ) (he : ∀ π, 0 < e π) (ρO : P → PowerSeries O)
    (hρO : ∀ π, (F.map (psSubR (e π) (α (pj π)))).eval (ρO π) = 0)
    -- the roots above `α_j`
    (πr : J → Fin SK.F.natDegree → P) (hπr : ∀ j k, pj (πr j k) = j)
    (hsurj : ∀ π, ∃ j k, πr j k = π)
    (sr : J → Fin SK.F.natDegree → ℕ) (hsr : ∀ j k, 0 < sr j k)
    (hNr : ∀ j k, N j = sr j k * e (πr j k))
    (ζO : J → Fin SK.F.natDegree → O) (hζO : ∀ j k, ζO j k ^ N j = 1)
    (hζK : ∀ j k, ι (ζO j k) ≠ 0) (hζk : ∀ j k, ρ (ζO j k) ≠ 0)
    (hsK : ∀ j, SK.F.map (branchSub (C := K₀) (K := K₀) (N j) (ι (α j))) = ∏ k, (X - Polynomial.C
      (rot (ι (ζO j k)) (hζK j k) (lsub (sr j k) (hsr j k)
        (ofPowerSeries ℤ K₀ (PowerSeries.map ι (ρO (πr j k))))))))
    (hsk : ∀ j, Sk.F.map (branchSub (C := 𝕜) (K := 𝕜) (N j) (ρ (α j))) = ∏ k, (X - Polynomial.C
      (rot (ρ (ζO j k)) (hζk j k) (lsub (sr j k) (hsr j k)
        (ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO (πr j k))))))))
    (hinjK : ∀ j, Function.Injective fun k ↦ rot (ι (ζO j k)) (hζK j k) (lsub (sr j k) (hsr j k)
        (ofPowerSeries ℤ K₀ (PowerSeries.map ι (ρO (πr j k))))))
    (hinjk : ∀ j, Function.Injective fun k ↦ rot (ρ (ζO j k)) (hζk j k) (lsub (sr j k) (hsr j k)
        (ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO (πr j k))))))
    -- the multiplicities
    (ΓP : P → ℕ) (cΓ : ℕ) (c' dΓ : J → ℕ) (hΓle : ∀ π, ΓP π ≤ c' (pj π) * e π)
    (hdK : ∀ j, ∑ k, sr j k * ΓP (πr j k) = N j * dΓ j)
    (hsumΓ : ∑ j, dΓ j = cΓ * SK.F.natDegree) (hle : ∀ j, dΓ j ≤ SK.F.natDegree * c' j)
    (hmP : ∑ π, (c' (pj π) * e π - ΓP π) = ∑ j, (SK.F.natDegree * c' j - dΓ j))
    -- the base field
    {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]
    (S : CurveData C L) (φ : C →+* K₀) (hSKφ : SK.F = S.F.map (mapRingHom φ))
    (hnK : SK.F.natDegree = S.F.natDegree)
    (BC : Fin S.F.natDegree → C[X][X]) (DC : C[X]) (δC : Fin S.F.natDegree → ℕ)
    (hBS : S.IsIntBasis K BC DC δC)
    (hBO : ∀ i, (B i).map (mapRingHom ι) = (BC (Fin.cast hnK i)).map (mapRingHom φ))
    (hDO : D.map ι = DC.map φ) (hδO : ∀ i, δ i = δC (Fin.cast hnK i))
    (αC : J → C) (hαO : ∀ j, ι (α j) = φ (αC j))
    (rC : J → Fin S.F.natDegree → LaurentSeries C)
    (hsC : ∀ j, S.F.map (branchSub (C := C) (K := C) (N j) (αC j)) = ∏ k, (X - Polynomial.C (rC j k)))
    (hrC : ∀ j k, lmap φ (rC j (Fin.cast hnK k)) = rot (ι (ζO j k)) (hζK j k) (lsub (sr j k) (hsr j k)
        (ofPowerSeries ℤ K₀ (PowerSeries.map ι (ρO (πr j k))))))
    (ΓC : J → Fin S.F.natDegree → ℕ) (hΓC : ∀ j k, ΓC j (Fin.cast hnK k) = sr j k * ΓP (πr j k))
    -- the prime
    (p : ℕ) (hp : p.Prime) (hpu : ∀ ℓ : ℕ, Nat.Coprime ℓ p → IsUnit (ℓ : O))
    (mp : ℕ) (hmp : 1 ≤ mp)
    (htestk : princTest (fun i : Fin Sk.F.natDegree ↦ δ (Fin.cast hnk i)) (mp * cΓ)
      (fun q : J × Fin Sk.F.natDegree ↦ N q.1) (fun q ↦ ρ (α q.1))
      (fun q i ↦ basisSer (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) (D.map ρ) (N q.1)
        (ρ (α q.1)) (rot (ρ (ζO q.1 (Fin.cast hnk q.2))) (hζk q.1 _) (lsub (sr q.1 (Fin.cast hnk q.2))
          (hsr q.1 _) (ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO (πr q.1 (Fin.cast hnk q.2))))))) i)
      (fun q ↦ mp * (sr q.1 (Fin.cast hnk q.2) * ΓP (πr q.1 (Fin.cast hnk q.2))))) :
    ∀ M : ℕ, 0 < M →
      princTest δC (M * cΓ) (fun q : J × Fin S.F.natDegree ↦ N q.1) (fun q ↦ αC q.1)
        (fun q i ↦ basisSer BC DC (N q.1) (αC q.1) (rC q.1 q.2) i) (fun q ↦ M * ΓC q.1 q.2) →
      ∃ v : ℕ, princTest δC ((mp * p ^ v) * cΓ) (fun q : J × Fin S.F.natDegree ↦ N q.1)
        (fun q ↦ αC q.1) (fun q i ↦ basisSer BC DC (N q.1) (αC q.1) (rC q.1 q.2) i)
        (fun q ↦ (mp * p ^ v) * ΓC q.1 q.2) := by
  classical
  intro M hM hC
  set ιK := algebraMap K₀ KK with hιK
  set ιk := algebraMap 𝕜 kk with hιk
  set rK : J → Fin SK.F.natDegree → LaurentSeries K₀ := fun j k ↦ rot (ι (ζO j k)) (hζK j k)
    (lsub (sr j k) (hsr j k) (ofPowerSeries ℤ K₀ (PowerSeries.map ι (ρO (πr j k))))) with hrKdef
  set rk : J → Fin Sk.F.natDegree → LaurentSeries 𝕜 := fun j k' ↦
    rot (ρ (ζO j (Fin.cast hnk k'))) (hζk j _) (lsub (sr j (Fin.cast hnk k')) (hsr j _)
      (ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO (πr j (Fin.cast hnk k')))))) with hrkdef
  have hsK' : ∀ j, SK.F.map (branchSub (C := K₀) (K := K₀) (N j) (ι (α j))) =
      ∏ k, (X - Polynomial.C (rK j k)) := hsK
  have hsk' : ∀ j, Sk.F.map (branchSub (C := 𝕜) (K := 𝕜) (N j) (ρ (α j))) =
      ∏ k', (X - Polynomial.C (rk j k')) := fun j ↦ by
    rw [hsk j]
    exact (prod_cast hnk (fun k ↦ X - Polynomial.C (rot (ρ (ζO j k)) (hζk j k)
      (lsub (sr j k) (hsr j k) (ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO (πr j k)))))))).symm
  have hinjK' : ∀ j, Function.Injective fun k ↦ lmap ιK (rK j k) :=
    fun j a b h ↦ hinjK j (lmap_injective ιK h)
  have hinjk' : ∀ j, Function.Injective fun k' ↦ lmap ιk (rk j k') :=
    fun j a b h ↦ Fin.cast_injective hnk (hinjk j (lmap_injective ιk h))
  -- the place data above `α_j` over `K̄₀`
  set πK : J → LaurentSeries KK → P := fun j ↦
    Function.extend (fun k ↦ lmap ιK (rK j k)) (πr j) (fun _ ↦ πr j ⟨0, hn⟩) with hπKdef
  set sK : J → LaurentSeries KK → ℕ := fun j ↦
    Function.extend (fun k ↦ lmap ιK (rK j k)) (sr j) (fun _ ↦ 1) with hsKdef
  set ζKf : J → LaurentSeries KK → KK := fun j ↦
    Function.extend (fun k ↦ lmap ιK (rK j k)) (fun k ↦ ιK (ι (ζO j k))) (fun _ ↦ 1) with hζKdef
  have hsKpos : ∀ j r, 0 < sK j r := fun j r ↦ by
    by_cases hr : ∃ k, lmap ιK (rK j k) = r
    · obtain ⟨k, rfl⟩ := hr; simp only [hsKdef, (hinjK' j).extend_apply]; exact hsr j k
    · simp only [hsKdef, Function.extend_apply' _ _ _ hr]; exact one_pos
  have hζK0' : ∀ j r, ζKf j r ≠ 0 := fun j r ↦ extend_ne_zero (hinjK' j) _ _
    (fun k ↦ (map_ne_zero_iff _ ιK.injective).mpr (hζK j k)) (fun _ ↦ one_ne_zero) r
  have hπK : ∀ j k, πK j (lmap ιK (rK j k)) = πr j k := fun j k ↦ (hinjK' j).extend_apply _ _ k
  have hsKk : ∀ j k, sK j (lmap ιK (rK j k)) = sr j k := fun j k ↦ (hinjK' j).extend_apply _ _ k
  have hζKk : ∀ j k, ζKf j (lmap ιK (rK j k)) = ιK (ι (ζO j k)) :=
    fun j k ↦ (hinjK' j).extend_apply _ _ k
  -- over `k̄`
  set πk : J → LaurentSeries kk → P := fun j ↦
    Function.extend (fun k' ↦ lmap ιk (rk j k')) (fun k' ↦ πr j (Fin.cast hnk k'))
      (fun _ ↦ πr j ⟨0, hn⟩) with hπkdef
  set sk : J → LaurentSeries kk → ℕ := fun j ↦
    Function.extend (fun k' ↦ lmap ιk (rk j k')) (fun k' ↦ sr j (Fin.cast hnk k')) (fun _ ↦ 1)
      with hskdef
  set ζkf : J → LaurentSeries kk → kk := fun j ↦
    Function.extend (fun k' ↦ lmap ιk (rk j k')) (fun k' ↦ ιk (ρ (ζO j (Fin.cast hnk k'))))
      (fun _ ↦ 1) with hζkdef
  have hskpos : ∀ j r, 0 < sk j r := fun j r ↦ by
    by_cases hr : ∃ k', lmap ιk (rk j k') = r
    · obtain ⟨k', rfl⟩ := hr; simp only [hskdef, (hinjk' j).extend_apply]; exact hsr j _
    · simp only [hskdef, Function.extend_apply' _ _ _ hr]; exact one_pos
  have hζk0' : ∀ j r, ζkf j r ≠ 0 := fun j r ↦ extend_ne_zero (hinjk' j) _ _
    (fun k' ↦ (map_ne_zero_iff _ ιk.injective).mpr (hζk j _)) (fun _ ↦ one_ne_zero) r
  have hπk : ∀ j k', πk j (lmap ιk (rk j k')) = πr j (Fin.cast hnk k') :=
    fun j k' ↦ (hinjk' j).extend_apply _ _ k'
  have hskk : ∀ j k', sk j (lmap ιk (rk j k')) = sr j (Fin.cast hnk k') :=
    fun j k' ↦ (hinjk' j).extend_apply _ _ k'
  have hζkk : ∀ j k', ζkf j (lmap ιk (rk j k')) = ιk (ρ (ζO j (Fin.cast hnk k'))) :=
    fun j k' ↦ (hinjk' j).extend_apply _ _ k'
  -- the lists and their structure
  set lK : J → List (LaurentSeries KK) := fun j ↦ List.ofFn fun k ↦ lmap ιK (rK j k) with hlKdef
  have hlK := fun j ↦ SK.split_lmap (K := KK) (N j) (ι (α j)) (rK j) (hsK' j)
  set lk : J → List (LaurentSeries kk) := fun j ↦ List.ofFn fun k' ↦ lmap ιk (rk j k') with hlkdef
  have hlk := fun j ↦ Sk.split_lmap (K := kk) (N j) (ρ (α j)) (rk j) (hsk' j)
  have hπK' : ∀ j r, r ∈ lK j → pj (πK j r) = j := fun j r hr ↦ by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr; rw [hπK]; exact hπr j k
  have hNK : ∀ j r, r ∈ lK j → N j = sK j r * e (πK j r) := fun j r hr ↦ by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr; rw [hsKk, hπK]; exact hNr j k
  have hζKN : ∀ j r, r ∈ lK j → ζKf j r ^ N j = 1 := fun j r hr ↦ by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    rw [hζKk, ← map_pow, ← map_pow, hζO, map_one, map_one]
  have hconjK : ∀ j r, r ∈ lK j → r = rot (ζKf j r) (hζK0' j r) (lsub (sK j r) (hsKpos j r)
      (lmap ιK (ofPowerSeries ℤ K₀ (PowerSeries.map ι (ρO (πK j r)))))) := fun j r hr ↦ by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    rw [rot_congr' (hζKk j k) _ ((map_ne_zero_iff _ ιK.injective).mpr (hζK j k)),
      lsub_congr' (hsKk j k) _ (hsr j k), hπK]
    simp only [hrKdef]
    rw [lmap_rot, lmap_lsub]
  have hπk' : ∀ j r, r ∈ lk j → pj (πk j r) = j := fun j r hr ↦ by
    obtain ⟨k', rfl⟩ := List.mem_ofFn.mp hr; rw [hπk]; exact hπr j _
  have hNk : ∀ j r, r ∈ lk j → N j = sk j r * e (πk j r) := fun j r hr ↦ by
    obtain ⟨k', rfl⟩ := List.mem_ofFn.mp hr; rw [hskk, hπk]; exact hNr j _
  have hζkN : ∀ j r, r ∈ lk j → ζkf j r ^ N j = 1 := fun j r hr ↦ by
    obtain ⟨k', rfl⟩ := List.mem_ofFn.mp hr
    rw [hζkk, ← map_pow, ← map_pow, hζO, map_one, map_one]
  have hconjk : ∀ j r, r ∈ lk j → r = rot (ζkf j r) (hζk0' j r) (lsub (sk j r) (hskpos j r)
      (lmap ιk (ofPowerSeries ℤ 𝕜 (PowerSeries.map ρ (ρO (πk j r)))))) := fun j r hr ↦ by
    obtain ⟨k', rfl⟩ := List.mem_ofFn.mp hr
    rw [rot_congr' (hζkk j k') _ ((map_ne_zero_iff _ ιk.injective).mpr (hζk j _)),
      lsub_congr' (hskk j k') _ (hsr j _), hπk]
    simp only [hrkdef]
    rw [lmap_rot, lmap_lsub]
  have hdK' : ∀ j, ((lK j).map fun r ↦ sK j r * ΓP (πK j r)).sum = N j * dΓ j := fun j ↦ by
    rw [hlKdef, List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply, hsKk, hπK]
    exact hdK j
  have hdk' : ∀ j, ((lk j).map fun r ↦ sk j r * ΓP (πk j r)).sum = N j * dΓ j := fun j ↦ by
    rw [hlkdef, List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply, hskk, hπk]
    rw [sum_cast_eq hnk (fun k ↦ sr j k * ΓP (πr j k))]
    exact hdK j
  -- the transport between `C` and `K₀`
  have hσC : ∀ (q : J × Fin S.F.natDegree) i,
      LowerBd (basisSer BC DC (N q.1) (αC q.1) (rC q.1 q.2) i) 0 :=
    fun q i ↦ S.basisSer_lowerBd_N hBS (N q.1) (hN q.1) (αC q.1) (rC q.1) (hsC q.1) q.2 i
  have hδf : (fun i ↦ δC (Fin.cast hnK i)) = δ := funext fun i ↦ (hδO i).symm
  have htrans : ∀ (β : J → Fin S.F.natDegree → ℕ) (Mc : ℕ),
      princTest δC Mc (fun q : J × Fin S.F.natDegree ↦ N q.1) (fun q ↦ αC q.1)
        (fun q i ↦ basisSer BC DC (N q.1) (αC q.1) (rC q.1 q.2) i) (fun q ↦ β q.1 q.2) ↔
      princTest δ Mc (fun q : J × Fin SK.F.natDegree ↦ N q.1) (fun q ↦ ι (α q.1))
        (fun q i ↦ basisSer (fun i ↦ (B i).map (mapRingHom ι)) (D.map ι) (N q.1) (ι (α q.1))
          (rK q.1 q.2) i) (fun q ↦ β q.1 (Fin.cast hnK q.2)) := by
    intro β Mc
    have := princTest_transport_N S SK φ hnK BC DC δC (fun i ↦ (B i).map (mapRingHom ι)) (D.map ι)
      hBO hDO N αC (fun j ↦ ι (α j)) hαO rC rK (fun j k ↦ (hrC j k).symm) hσC β Mc
    rwa [hδf] at this
  have hΓf : ∀ t : ℕ, (fun (q : J × Fin SK.F.natDegree) ↦ t * ΓC q.1 (Fin.cast hnK q.2)) =
      fun q ↦ t * (sr q.1 q.2 * ΓP (πr q.1 q.2)) := fun t ↦ funext fun q ↦ by rw [hΓC]
  have hprK : ∀ t : ℕ, (∃ Ξ : K₀⟮SK.x⟯⟮SK.y⟯, Ξ ≠ 0 ∧ SK.DivGE (fun j ↦ ι (α j)) N hN lK hlK
      (fun j r ↦ t * (sK j r * ΓP (πK j r))) (t * cΓ) Ξ) ↔
      princTest δ (t * cΓ) (fun q : J × Fin SK.F.natDegree ↦ N q.1) (fun q ↦ ι (α q.1))
        (fun q i ↦ basisSer (fun i ↦ (B i).map (mapRingHom ι)) (D.map ι) (N q.1) (ι (α q.1))
          (rK q.1 q.2) i) (fun q ↦ t * (sr q.1 q.2 * ΓP (πr q.1 q.2))) := fun t ↦
    SK.principal_iff_test hBK (fun j ↦ ι (α j)) N hN rK hsK'
      (fun j k ↦ t * (sr j k * ΓP (πr j k))) (fun j r ↦ t * (sK j r * ΓP (πK j r)))
      (fun j k ↦ by
        show t * (sK j (lmap ιK (rK j k)) * ΓP (πK j (lmap ιK (rK j k)))) = _
        rw [hsKk, hπK]) (t * cΓ)
  -- `M Γ` is principal over `K₀`
  have hKt := (htrans (fun j k ↦ M * ΓC j k) (M * cΓ)).mp hC
  rw [hΓf M] at hKt
  obtain ⟨Ξ, hΞ0, hΞ⟩ := (hprK M).mpr hKt
  -- `M = p^v ℓ`
  set v := M.factorization p with hv
  set ℓ := M / p ^ v with hℓdef
  have hMe : p ^ v * ℓ = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hℓcop : Nat.Coprime ℓ p := (Nat.coprime_ordCompl hp hM.ne').symm
  have hℓ1 : 1 ≤ ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · rw [h, mul_zero] at hMe; omega
    · exact h
  rw [← hMe] at hΞ
  -- the principal witness modulo `p`
  obtain ⟨γk, hγk0, hγk⟩ := (Sk.principal_iff_test hBk (fun j ↦ ρ (α j)) N hN rk hsk'
    (fun j k' ↦ mp * (sr j (Fin.cast hnk k') * ΓP (πr j (Fin.cast hnk k'))))
    (fun j r ↦ mp * (sk j r * ΓP (πk j r))) (fun j k' ↦ by
      show mp * (sk j (lmap ιk (rk j k')) * ΓP (πk j (lmap ιk (rk j k')))) = _
      rw [hskk, hπk])
    (mp * cΓ)).mpr htestk
  obtain ⟨γ', hγ'0, hγ'⟩ := principal_at_prime_places hϖ F hF SK hSK hBrK hBIK Sk hSk hBrk hBIk hnk hn
    B D hDm δ hB0 hδ0 hδ hBK hBk hg x hx y hsplit hFu hdet hDx hNS α hα hαx hDα N hN pj e he ρO hρO
    lK hlK πK hπK' sK hsKpos hNK ζKf hζK0' hζKN hconjK (fun π ↦ by
      obtain ⟨j, k, hk⟩ := hsurj π
      exact ⟨j, lmap ιK (rK j k), List.mem_ofFn.mpr ⟨k, rfl⟩, by rw [hπK]; exact hk⟩)
    lk hlk πk hπk' sk hskpos hNk ζkf hζk0' hζkN
    hconjk ΓP cΓ c' dΓ hΓle hdK' hdk' hsumΓ hle hmP mp (p ^ v) ℓ hmp (Nat.one_le_pow _ _ hp.pos)
    hℓ1 (hpu ℓ hℓcop) γk hγk0 hγk Ξ hΞ0 hΞ
  refine ⟨v, (htrans (fun j k ↦ (mp * p ^ v) * ΓC j k) _).mpr ?_⟩
  rw [hΓf (mp * p ^ v)]
  exact (hprK (mp * p ^ v)).mp ⟨γ', hγ'0, hγ'⟩

end StepP

section TwoP

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L)

/-- **Non-torsion at places from two primes and a failed test.** -/
theorem not_torsion_places_mt (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) {J : Type*} [Fintype J] (α : J → C) (hα : Function.Injective α)
    (N : J → ℕ) (hN : ∀ j, 0 < N j) (rC : J → Fin S.F.natDegree → LaurentSeries C)
    (hsC : ∀ j, S.F.map (branchSub (C := C) (K := C) (N j) (α j)) = ∏ k, (X - Polynomial.C (rC j k)))
    (hinj : ∀ j, Function.Injective fun k ↦ lmap (algebraMap C K) (rC j k))
    (ΓC : J → Fin S.F.natDegree → ℕ) (c : ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ∑ k, ΓC j k = N j * dΓ j) (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (mp mq : ℕ) (hmp : 0 < mp) (hmq : 0 < mq)
    (hstep_p : ∀ M : ℕ, 0 < M →
      princTest δ (M * c) (fun z : J × Fin S.F.natDegree ↦ N z.1) (fun z ↦ α z.1)
        (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i) (fun z ↦ M * ΓC z.1 z.2) →
      ∃ v : ℕ, princTest δ ((mp * p ^ v) * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
        (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
        (fun q ↦ (mp * p ^ v) * ΓC q.1 q.2))
    (hstep_q : ∀ M : ℕ, 0 < M →
      princTest δ (M * c) (fun z : J × Fin S.F.natDegree ↦ N z.1) (fun z ↦ α z.1)
        (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i) (fun z ↦ M * ΓC z.1 z.2) →
      ∃ w : ℕ, princTest δ ((mq * q ^ w) * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
        (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
        (fun z ↦ (mq * q ^ w) * ΓC z.1 z.2))
    (mt : ℕ) (hmt : ∀ v w : ℕ, Nat.gcd (mp * p ^ v) (mq * q ^ w) ∣ mt)
    (htest : ¬ princTest δ (mt * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
        (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
        (fun q ↦ mt * ΓC q.1 q.2)) :
    ∀ M : ℕ, 0 < M → ¬ princTest δ (M * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
      (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
      (fun z ↦ M * ΓC z.1 z.2) := by
  classical
  intro M hM htor
  set Γf : J → LaurentSeries K → ℕ := fun j ↦
    Function.extend (fun k ↦ lmap (algebraMap C K) (rC j k)) (ΓC j) 0 with hΓf
  have hΓk : ∀ j k, Γf j (lmap (algebraMap C K) (rC j k)) = ΓC j k :=
    fun j k ↦ (hinj j).extend_apply _ _ k
  have hiff : ∀ t : ℕ, (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧ S.DivGE α N hN
      (fun j ↦ List.ofFn fun k ↦ lmap (algebraMap C K) (rC j k))
      (fun j ↦ S.split_lmap (N j) (α j) (rC j) (hsC j)) (fun j r ↦ t * Γf j r) (t * c) γ) ↔
      princTest δ (t * c) (fun z : J × Fin S.F.natDegree ↦ N z.1) (fun z ↦ α z.1)
        (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i) (fun z ↦ t * ΓC z.1 z.2) :=
    fun t ↦ S.principal_iff_test hB α N hN rC hsC (fun j k ↦ t * ΓC j k) (fun j r ↦ t * Γf j r)
      (fun j k ↦ by show t * Γf j _ = _; rw [hΓk]) (t * c)
  have hdΓ' : ∀ j, ((List.ofFn fun k ↦ lmap (algebraMap C K) (rC j k)).map (Γf j)).sum =
      N j * dΓ j := fun j ↦ by
    rw [List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply, hΓk]
    exact hdΓ j
  obtain ⟨γ, hγ0, hγ⟩ := S.principal_two_primes_mt hBr hBI α hα N hN _
    (fun j ↦ S.split_lmap (N j) (α j) (rC j) (hsC j)) Γf c dΓ hdΓ' hsumΓ p q hp hq hpq mp mq hmp hmq
    (fun M' hM' h ↦ by
      obtain ⟨v, hv⟩ := hstep_p M' hM' ((hiff M').mp h)
      exact ⟨v, (hiff _).mpr hv⟩)
    (fun M' hM' h ↦ by
      obtain ⟨w, hw⟩ := hstep_q M' hM' ((hiff M').mp h)
      exact ⟨w, (hiff _).mpr hw⟩) mt hmt M hM ((hiff M).mpr htor)
  exact htest ((hiff _).mp ⟨γ, hγ0, hγ⟩)

/-- **Non-torsion at places from two primes and a failed test.** -/
theorem not_torsion_places (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) {J : Type*} [Fintype J] (α : J → C) (hα : Function.Injective α)
    (N : J → ℕ) (hN : ∀ j, 0 < N j) (rC : J → Fin S.F.natDegree → LaurentSeries C)
    (hsC : ∀ j, S.F.map (branchSub (C := C) (K := C) (N j) (α j)) = ∏ k, (X - Polynomial.C (rC j k)))
    (hinj : ∀ j, Function.Injective fun k ↦ lmap (algebraMap C K) (rC j k))
    (ΓC : J → Fin S.F.natDegree → ℕ) (c : ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ∑ k, ΓC j k = N j * dΓ j) (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (mp mq : ℕ) (hmp : 0 < mp) (hmq : 0 < mq)
    (hstep_p : ∀ M : ℕ, 0 < M →
      princTest δ (M * c) (fun z : J × Fin S.F.natDegree ↦ N z.1) (fun z ↦ α z.1)
        (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i) (fun z ↦ M * ΓC z.1 z.2) →
      ∃ v : ℕ, princTest δ ((mp * p ^ v) * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
        (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
        (fun q ↦ (mp * p ^ v) * ΓC q.1 q.2))
    (hstep_q : ∀ M : ℕ, 0 < M →
      princTest δ (M * c) (fun z : J × Fin S.F.natDegree ↦ N z.1) (fun z ↦ α z.1)
        (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i) (fun z ↦ M * ΓC z.1 z.2) →
      ∃ w : ℕ, princTest δ ((mq * q ^ w) * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
        (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
        (fun z ↦ (mq * q ^ w) * ΓC z.1 z.2))
    (htest : ¬ princTest δ ((mp * mq) * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
        (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
        (fun q ↦ (mp * mq) * ΓC q.1 q.2)) :
    ∀ M : ℕ, 0 < M → ¬ princTest δ (M * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
      (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
      (fun z ↦ M * ΓC z.1 z.2) := by
  exact S.not_torsion_places_mt hBr hBI hB α hα N hN rC hsC hinj ΓC c dΓ hdΓ hsumΓ p q hp hq hpq mp mq
    hmp hmq hstep_p hstep_q (mp * mq) (gcd_dvd_mul_primes hp hq hpq mp mq) htest

/-- **The torsion dichotomy at places.** Given the prime steps at `p` and `q`, some multiple of
`Γ − c ∞ₓ` passes the principality test iff the multiple `m_p m_q` does: one linear-algebra
test decides torsion. -/
theorem torsion_iff_test_places (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) {J : Type*} [Fintype J] (α : J → C) (hα : Function.Injective α)
    (N : J → ℕ) (hN : ∀ j, 0 < N j) (rC : J → Fin S.F.natDegree → LaurentSeries C)
    (hsC : ∀ j, S.F.map (branchSub (C := C) (K := C) (N j) (α j)) = ∏ k, (X - Polynomial.C (rC j k)))
    (hinj : ∀ j, Function.Injective fun k ↦ lmap (algebraMap C K) (rC j k))
    (ΓC : J → Fin S.F.natDegree → ℕ) (c : ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ∑ k, ΓC j k = N j * dΓ j) (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (mp mq : ℕ) (hmp : 0 < mp) (hmq : 0 < mq)
    (hstep_p : ∀ M : ℕ, 0 < M →
      princTest δ (M * c) (fun z : J × Fin S.F.natDegree ↦ N z.1) (fun z ↦ α z.1)
        (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i) (fun z ↦ M * ΓC z.1 z.2) →
      ∃ v : ℕ, princTest δ ((mp * p ^ v) * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
        (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
        (fun q ↦ (mp * p ^ v) * ΓC q.1 q.2))
    (hstep_q : ∀ M : ℕ, 0 < M →
      princTest δ (M * c) (fun z : J × Fin S.F.natDegree ↦ N z.1) (fun z ↦ α z.1)
        (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i) (fun z ↦ M * ΓC z.1 z.2) →
      ∃ w : ℕ, princTest δ ((mq * q ^ w) * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
        (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
        (fun z ↦ (mq * q ^ w) * ΓC z.1 z.2)) :
    (∃ M : ℕ, 0 < M ∧ princTest δ (M * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
      (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
      (fun z ↦ M * ΓC z.1 z.2)) ↔
    princTest δ ((mp * mq) * c) (fun z : J × Fin S.F.natDegree ↦ N z.1)
        (fun z ↦ α z.1) (fun z i ↦ basisSer B D (N z.1) (α z.1) (rC z.1 z.2) i)
        (fun z ↦ (mp * mq) * ΓC z.1 z.2) := by
  refine ⟨fun ⟨M, hM, h⟩ ↦ ?_, fun h ↦ ⟨mp * mq, Nat.mul_pos hmp hmq, h⟩⟩
  by_contra htest
  exact S.not_torsion_places hBr hBI hB α hα N hN rC hsC hinj ΓC c dΓ hdΓ hsumΓ p q hp hq hpq mp mq
    hmp hmq hstep_p hstep_q htest M hM h

end CurveData

end TwoP

end Curves
