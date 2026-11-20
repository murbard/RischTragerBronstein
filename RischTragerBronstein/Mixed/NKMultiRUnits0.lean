import RischTragerBronstein.Mixed.NKMultiRUnits
import RischTragerBronstein.Mixed.NKUnitsCls0

/-!
# S-units for several slopes at infinity and the roots above `0`

`unitsSpan0_multiR`: `unitsSpan_multiR` with the places above `t = 0` (each root above `0` counted
as a place): `x` and `∑ₖ |Γₖ| + |l₀| − 2` independent S-units span the S-units
(`mem_pow_units_cls0` with the cover of `unitsSpan_multiR` at infinity).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section UnitsMultiR0

variable {C L Kb : Type*} [Field C] [Field L] [Algebra C L] [Field Kb] [Algebra C Kb]
  [IsAlgClosed Kb] [CharZero Kb]

namespace CurveData

variable (S : CurveData C L)

set_option maxHeartbeats 4000000 in
/-- **`x` and `∑ₖ |Γₖ| + |l₀| − 2` independent S-units span the S-units** (places at infinity of
rational slopes `sₖ/eₖ`, and the roots above `0`). -/
theorem unitsSpan0_multiR [CharZero C] (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    {q : ℕ} (e : Fin (q + 1) → ℕ) (he : ∀ k, 0 < e k) (s : Fin (q + 1) → ℤ)
    (hcop : ∀ k, Int.gcd (s k) (e k) = 1)
    (hdec : ∀ k : Fin q, s k.succ * e k.castSucc < s k.castSucc * e k.succ)
    (K0 : Fin (q + 1) → ℤ) (c : Fin (q + 1) → C) (hc : ∀ k, c k ≠ 0) (lo : Fin (q + 1) → ℕ)
    (Γ : Fin (q + 1) → List C) (hΓ : ∀ k, (Γ k).Nodup ∧ (0 : C) ∉ Γ k)
    (hbound : ∀ k, ∀ i ≤ S.F.natDegree, S.F.coeff i ≠ 0 →
      (e k : ℤ) * (S.F.coeff i).natDegree + i * s k ≤ K0 k)
    (hres : ∀ k, ∑ i ∈ Finset.range (S.F.natDegree + 1),
      Polynomial.C (coeffZe (S.F.coeff i) (e k) (K0 k - i * s k)) * X ^ i =
        Polynomial.C (c k) * X ^ (lo k) * ((Γ k).map fun γ ↦ X ^ (e k) - Polynomial.C γ).prod)
    (htop : lo 0 + e 0 * (Γ 0).length = S.F.natDegree)
    (hchain : ∀ k : Fin q, lo k.castSucc = lo k.succ + e k.succ * (Γ k.succ).length)
    (hlast : lo (Fin.last q) = 0)
    (N0 : ℕ) (hN0 : 0 < N0) (l0 : List (LaurentSeries Kb))
    (hlz : S.F.map (branchSub N0 0) = (l0.map fun r ↦ X - Polynomial.C r).prod)
    {mI : ℕ} (hnp : ∑ k, (Γ k).length = mI + 1) {mu : ℕ} (hcount : mI + l0.length = mu + 1)
    (u : Fin mu → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i, u i ≠ 0)
    (hfinu : ∀ i (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u i)).order = 0)
    (hind : ∀ (e0 : ℤ) (a : Fin mu → ℤ),
      (∃ c : C, S.x ^ e0 * ∏ i, (u i : L) ^ a i = algebraMap C L c) → e0 = 0 ∧ a = 0) :
    S.UnitsSpan0 Kb u := by
  classical
  intro w hw hfin
  have hF0 : S.F.coeff 0 ≠ 0 := coeff0_ne_of_resR S.F (e (Fin.last q)) (he _) (s (Fin.last q))
    (K0 (Fin.last q)) (c (Fin.last q)) (hc _) (Γ (Fin.last q)) (hΓ _).2 (by rw [← hlast]; exact hres _)
  -- a branch system above infinity with `eₖ ∣ N`
  obtain ⟨Nb, hNb, lb, -, hlb⟩ := S.hasBranchesInf (K := Kb)
  have hNb' := Nat.pos_of_ne_zero hNb
  set E : ℕ := ∏ k, e k with hE
  have hE0 : 0 < E := Finset.prod_pos fun k _ ↦ he k
  set N : ℕ := Nb * E with hNdef
  have hN : 0 < N := Nat.mul_pos hNb' hE0
  set lr := lb.map (lsub E hE0) with hlr
  have hl : S.F.map (infSub N) = (lr.map fun r ↦ X - Polynomial.C r).prod :=
    branchSys_lsub S.F Nb E hE0 lb hlb
  have hed : ∀ k, e k ∣ N := fun k ↦
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) _
  have hsA := strictAnti_weights N hN e he hed s hdec
  obtain ⟨hord, huniq, hsurj⟩ := multi_hdataR (K := Kb) N hN S.F S.monic hF0 lr hl e he hed s
    hsA K0 c hc lo Γ hΓ hbound hres htop hchain hlast
  have hl0 : ∀ r ∈ lr, r ≠ 0 := by
    intro r hr h0
    subst h0
    have h1 : (S.F.map (infSub (K := Kb) N)).eval 0 = 0 := by
      rw [hl, eval_list_prod]
      exact List.prod_eq_zero (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨0, hr, rfl⟩, by simp⟩)
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at h1
    exact hF0 ((infSub_injective N hN) (by rw [h1, map_zero]))
  have : NeZero ((N : ℕ) : Kb) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Kb N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  -- the places: pairs `(k, γ)`
  have hP : Fintype.card (Σ k : Fin (q + 1), Fin (Γ k).length) = mI + 1 := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact hnp
  set eqv : (Σ k : Fin (q + 1), Fin (Γ k).length) ≃ Fin (mI + 1) :=
    Fintype.equivFinOfCardEq hP with heqv
  set ι := algebraMap C Kb with hι
  -- the place of a root
  have hpl : ∀ p : Fin lr.length, ∃ π : (Σ k : Fin (q + 1), Fin (Γ k).length),
      (lr.get p).order = -(((N / e π.1 : ℕ) : ℤ) * s π.1) ∧
      ((lr.get p).coeff (lr.get p).order) ^ e π.1 = ι ((Γ π.1)[(π.2 : ℕ)]) := by
    intro p
    obtain ⟨k, hk, γ, hγ, hγe⟩ := hord _ (List.get_mem lr p)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hγ
    exact ⟨⟨k, ⟨i, hi⟩⟩, hk, hγe⟩
  choose pl hpl using hpl
  -- a root at each place
  have hrt : ∀ π : (Σ k : Fin (q + 1), Fin (Γ k).length), ∃ p : Fin lr.length,
      (lr.get p).order = -(((N / e π.1 : ℕ) : ℤ) * s π.1) ∧
      ((lr.get p).coeff (lr.get p).order) ^ e π.1 = ι ((Γ π.1)[(π.2 : ℕ)]) := by
    intro π
    obtain ⟨ρ, hρ, hρo, hρe⟩ := hsurj π.1 _ (List.getElem_mem _)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hρ
    exact ⟨⟨i, hi⟩, hρo, hρe⟩
  choose rt hrt using hrt
  -- roots at the same place have expansions with the same orders
  have hsame : ∀ p : Fin lr.length, ∀ f : C⟮S.x⟯⟮S.y⟯,
      (S.embG (infSub N) (infSub_injective N hN) (lr.get p)
        (S.root_of_mem hl (List.get_mem lr p)) f).order =
      (S.embG (infSub N) (infSub_injective N hN) (lr.get (rt (pl p)))
        (S.root_of_mem hl (List.get_mem lr (rt (pl p)))) f).order := by
    intro p f
    set π := pl p with hπ
    obtain ⟨ho, hpw⟩ := hpl p
    obtain ⟨ho', hpw'⟩ := hrt π
    obtain ⟨j, hj⟩ := rot_of_pow_eq S.F N hN hζ lr hl (List.get_mem lr (rt π))
      (List.get_mem lr p) (hl0 _ (List.get_mem lr _)) (e π.1) (he _) (hed _) (s π.1) (hcop _) ho'
      (by rw [ho, ho']) (by rw [hpw, hpw']) huniq
    have hζjN : (ζ ^ j) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hroot := rot_root_inf (ζ ^ j) (pow_ne_zero _ hζ0) N hζjN S.F (lr.get (rt π))
      (S.root_of_mem hl (List.get_mem lr (rt π)))
    have e1 : S.embG (infSub N) (infSub_injective N hN) (lr.get p)
        (S.root_of_mem hl (List.get_mem lr p)) f =
        S.embG (infSub N) (infSub_injective N hN) (rot (ζ ^ j) (pow_ne_zero _ hζ0) (lr.get (rt π)))
          hroot f := by
      revert hroot
      rw [← hj]
      intro hroot
      rfl
    rw [e1, S.embG_rot_inf (ζ ^ j) (pow_ne_zero _ hζ0) N hN hζjN, rot_order]
  -- the cover
  have hcov : ∀ p : Fin lr.length,
      (∃ q', ∀ f : C⟮S.x⟯⟮S.y⟯, (S.embG (infSub N) (infSub_injective N hN) (lr.get p)
          (S.root_of_mem hl (List.get_mem lr p)) f).order =
        (S.embG (infSub N) (infSub_injective N hN) (lr.get (rt (eqv.symm (Fin.castSucc q'))))
          (S.root_of_mem hl (List.get_mem lr (rt (eqv.symm (Fin.castSucc q'))))) f).order) ∨
      ∀ f : C⟮S.x⟯⟮S.y⟯, (S.embG (infSub N) (infSub_injective N hN) (lr.get p)
          (S.root_of_mem hl (List.get_mem lr p)) f).order =
        (S.embG (infSub N) (infSub_injective N hN) (lr.get (rt (eqv.symm (Fin.last mI))))
          (S.root_of_mem hl (List.get_mem lr (rt (eqv.symm (Fin.last mI))))) f).order := by
    intro p
    by_cases hlt : (eqv (pl p) : ℕ) < mI
    · left
      refine ⟨⟨eqv (pl p), hlt⟩, fun f ↦ ?_⟩
      have : eqv.symm (Fin.castSucc ⟨eqv (pl p), hlt⟩) = pl p := by
        rw [Equiv.symm_apply_eq]; ext; rfl
      rw [this]
      exact hsame p f
    · right
      intro f
      have : eqv.symm (Fin.last mI) = pl p := by
        rw [Equiv.symm_apply_eq]
        ext
        simp only [Fin.val_last]
        have := (eqv (pl p)).2
        omega
      rw [this]
      exact hsame p f
  exact S.mem_pow_units_cls0 hgeo N hN lr hl N0 hN0 l0 hlz (fun q' ↦ rt (eqv.symm q'.castSucc))
    (rt (eqv.symm (Fin.last mI))) hcov id (fun p ↦ ⟨p, fun _ ↦ rfl⟩) hcount u hu hfinu hind w hw hfin

end CurveData

end UnitsMultiR0

end Curves
