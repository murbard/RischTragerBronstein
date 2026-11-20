import RischTragerBronstein.Torsion.PrimeStep

/-!
# Divisors supported at unramified points

`DivGEU α y Γ c γ`: `div γ ≥ Γ − c ∞ₓ` for `Γ = ∑ Γ_{j,k} (α_j, y_{j,k})` supported at points of
unramified fibres, stated along every power-series branch through these points (no choice of
branch system). `divGEU_iff`: with the Hensel branch systems, it is `DivGE`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Unram

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- `div γ ≥ Γ − c ∞ₓ`, `Γ` supported at points `(α_j, y_{j,k})` of unramified fibres. -/
def DivGEU {J : Type*} (α : J → C) (y : J → Fin S.F.natDegree → C)
    (Γ : J → Fin S.F.natDegree → ℕ) (c : ℕ) (γ : C⟮S.x⟯⟮S.y⟯) : Prop :=
  (∀ j k (Yp : PowerSeries K)
    (hY : (S.F.map (branchSub 1 (algebraMap C K (α j)))).eval (ofPowerSeries ℤ K Yp) = 0),
    PowerSeries.constantCoeff Yp = algebraMap C K (y j k) →
      (Γ j k : ℤ) ≤ (S.embG (branchSub 1 (algebraMap C K (α j))) (branchSub_injective 1 one_pos _)
        (ofPowerSeries ℤ K Yp) hY γ).order) ∧
  (∀ b : K, b ∉ Set.range (fun j ↦ algebraMap C K (α j)) → ∀ (N' : ℕ) (hN' : N' ≠ 0)
    (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N' b) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l), 0 ≤ (S.embG (branchSub N' b)
      (branchSub_injective N' (Nat.pos_of_ne_zero hN') b) r (S.root_of_mem hl hr) γ).order) ∧
  (∀ (N' : ℕ) (hN' : N' ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N') = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l), -((N' * c : ℕ) : ℤ) ≤ (S.embG (infSub N')
      (infSub_injective N' (Nat.pos_of_ne_zero hN')) r (S.root_of_mem hl hr) γ).order)

lemma list_split (a : K) (Y : Fin S.F.natDegree → PowerSeries K)
    (hs : S.F.map (branchSub 1 a) = ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K (Y k)))) :
    S.F.map (branchSub 1 a) =
      ((List.ofFn fun k ↦ ofPowerSeries ℤ K (Y k)).map fun r ↦ X - Polynomial.C r).prod := by
  rw [hs, List.map_ofFn, List.prod_ofFn]; rfl

/-- The branch through an unramified point is the Hensel lift. -/
lemma unram_root_unique (a : K) (Y : Fin S.F.natDegree → PowerSeries K)
    (hs : S.F.map (branchSub 1 a) = ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K (Y k))))
    (hinj : Function.Injective fun k ↦ PowerSeries.constantCoeff (Y k)) (k0 : Fin S.F.natDegree)
    (Yp : PowerSeries K) (hY : (S.F.map (branchSub 1 a)).eval (ofPowerSeries ℤ K Yp) = 0)
    (hc : PowerSeries.constantCoeff Yp = PowerSeries.constantCoeff (Y k0)) : Yp = Y k0 := by
  rw [hs, eval_prod, Finset.prod_eq_zero_iff] at hY
  obtain ⟨k, -, hk⟩ := hY
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hk
  have hYk : Yp = Y k := HahnSeries.ofPowerSeries_injective hk
  rw [hYk] at hc ⊢
  rw [hinj hc]

/-- **Unramified divisors along Hensel branch systems.** -/
theorem divGEU_iff {J : Type*} (α : J → C) (y : J → Fin S.F.natDegree → C)
    (Y : J → Fin S.F.natDegree → PowerSeries K)
    (hs : ∀ j, S.F.map (branchSub 1 (algebraMap C K (α j))) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K (Y j k))))
    (hYc : ∀ j k, PowerSeries.constantCoeff (Y j k) = algebraMap C K (y j k))
    (hinj : ∀ j, Function.Injective (y j)) (Γ : J → Fin S.F.natDegree → ℕ) (c : ℕ)
    (γ : C⟮S.x⟯⟮S.y⟯) :
    S.DivGEU (K := K) α y Γ c γ ↔ S.DivGE α (fun _ ↦ 1) (fun _ ↦ one_pos)
      (fun j ↦ List.ofFn fun k ↦ ofPowerSeries ℤ K (Y j k)) (fun j ↦ S.list_split _ _ (hs j))
      (fun j ↦ Function.extend (fun k ↦ ofPowerSeries ℤ K (Y j k)) (Γ j) 0) c γ := by
  have hcinj : ∀ j, Function.Injective fun k ↦ PowerSeries.constantCoeff (Y j k) := by
    intro j a b h
    simp only [hYc] at h
    exact hinj j ((algebraMap C K).injective h)
  have hYinj : ∀ j, Function.Injective fun k ↦ ofPowerSeries ℤ K (Y j k) := by
    intro j a b h
    exact hcinj j (by simp only; rw [HahnSeries.ofPowerSeries_injective h])
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j r hr ↦ ?_, h2, h3⟩
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    have e : Function.extend (fun k ↦ ofPowerSeries ℤ K (Y j k)) (Γ j) 0
        (ofPowerSeries ℤ K (Y j k)) = Γ j k := (hYinj j).extend_apply _ _ k
    dsimp only
    rw [e]
    exact h1 j k (Y j k) _ (hYc j k)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j k Yp hY hc ↦ ?_, h2, h3⟩
    have hYp : Yp = Y j k :=
      S.unram_root_unique _ (Y j) (hs j) (hcinj j) k Yp hY (by rw [hc, hYc])
    subst hYp
    have := h1 j (ofPowerSeries ℤ K (Y j k)) (List.mem_ofFn.mpr ⟨k, rfl⟩)
    have e : Function.extend (fun k ↦ ofPowerSeries ℤ K (Y j k)) (Γ j) 0
        (ofPowerSeries ℤ K (Y j k)) = Γ j k := (hYinj j).extend_apply _ _ k
    dsimp only at this
    rwa [e] at this

end CurveData

end Unram

end Curves
