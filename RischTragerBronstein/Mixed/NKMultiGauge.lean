import RischTragerBronstein.Mixed.NKGalRoots
import RischTragerBronstein.Mixed.NKSplitGauge
import RischTragerBronstein.Mixed.NKRamUnits

/-!
# The gauge at infinity for unramified rational places of any slopes

For a curve whose roots above infinity (a branch system `x = T^{−N}`) have pairwise distinct
`(order, leading coefficient)`, orders divisible by `N` (unramified) and leading coefficients in
`C` — e.g. several Newton slopes, each with distinct rational residual roots — the values at the
places at infinity of a rescaled integral basis normal at infinity form an invertible matrix
`A ∈ GLₙ(C)` with `A′ = Λ A` (`multi_gauge`), exactly as for a single slope (`split_gauge`).

The values lie in `C` by Galois descent (`NKGalRoots`); invertibility is normality at infinity:
a combination with vanishing values has order `≥ 1`, hence `≥ N` along the unramified roots
(they are fixed by the rotation `T ↦ ζT`), hence is `O(1/x)` along every branch system
(`infOrd_of_sys`, by `inf_rel`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Rot

variable {K : Type*} [Field K]

lemma coeff_eq_zero_of_rot_fixed {N : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ N) (hζ0 : ζ ≠ 0)
    (z : LaurentSeries K) (hz : rot ζ hζ0 z = z) (j : ℤ) (hj : ¬ (N : ℤ) ∣ j) : z.coeff j = 0 := by
  have h := congrArg (fun y ↦ y.coeff j) hz
  simp only [rot_coeff] at h
  have hne : ζ ^ j ≠ 1 := fun h1 ↦ hj ((hζ.zpow_eq_one_iff_dvd j).mp h1)
  have : (ζ ^ j - 1) * z.coeff j = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

lemma lowerBd_N_of_rot_fixed {N : ℕ} (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (hζ0 : ζ ≠ 0) (z : LaurentSeries K) (hz : rot ζ hζ0 z = z) (h1 : LowerBd z 1) :
    LowerBd z N := fun j hj ↦ by
  by_cases hj1 : j < 1
  · exact h1 j hj1
  refine coeff_eq_zero_of_rot_fixed hζ hζ0 z hz j fun ⟨c, hc⟩ ↦ ?_
  subst hc
  rcases le_or_gt c 0 with h | h
  · nlinarith
  · nlinarith

lemma rot_order {ζ : K} (hζ0 : ζ ≠ 0) (r : LaurentSeries K) : (rot ζ hζ0 r).order = r.order := by
  by_cases hr : r = 0
  · subst hr; simp
  have hr' : rot ζ hζ0 r ≠ 0 := fun h ↦ hr ((rot_eq_zero_iff ζ hζ0 r).mp h)
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by
      rw [rot_coeff]
      exact mul_ne_zero (zpow_ne_zero _ hζ0) (fun h ↦ hr (HahnSeries.coeff_order_eq_zero.mp h)))
  · exact HahnSeries.order_le_of_coeff_ne_zero (fun h ↦
      hr' (HahnSeries.coeff_order_eq_zero.mp (by rw [rot_coeff, h, mul_zero])))

end Rot

/-- A root of a split polynomial is one of the listed roots. -/
lemma mem_of_eval_prod {K : Type*} [Field K] (l : List (LaurentSeries K)) (Y : LaurentSeries K)
    (hY : (l.map fun r ↦ X - Polynomial.C r).prod.eval Y = 0) : Y ∈ l := by
  rw [eval_list_prod] at hY
  obtain ⟨v, hv, hv0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp hY)
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hv
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hv0
  rw [hv0]; exact hr'

namespace CurveData

section MultiGauge

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

lemma embG_eq_of_eq (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    {Y Y' : LaurentSeries K} (h : Y = Y') (hY : (S.F.map g).eval Y = 0)
    (hY' : (S.F.map g).eval Y' = 0) (z : C⟮S.x⟯⟮S.y⟯) :
    S.embG g hg Y hY z = S.embG g hg Y' hY' z := by
  subst h; rfl

/-- **A root with unique data and order divisible by `N` is fixed by the rotations.** -/
lemma root_rot_fixed (N : ℕ) {ζ : K} (hζ : IsPrimitiveRoot ζ N) (hζ0 : ζ ≠ 0)
    (l : List (LaurentSeries K)) (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    {r : LaurentSeries K} (hr : r ∈ l) (hdvd : (N : ℤ) ∣ r.order)
    (huniq : ∀ r' ∈ l, r'.order = r.order → r'.coeff r'.order = r.coeff r.order → r' = r) :
    rot ζ hζ0 r = r := by
  have hN1 : ζ ^ N = 1 := hζ.pow_eq_one
  have hmem : rot ζ hζ0 r ∈ l := mem_of_eval_prod l _ (by
    rw [← hl]; exact rot_root_inf ζ hζ0 N hN1 S.F r (S.root_of_mem hl hr))
  refine huniq _ hmem (rot_order hζ0 r) ?_
  rw [rot_order, rot_coeff, (hζ.zpow_eq_one_iff_dvd _).mpr hdvd, one_mul]

/-- **An order bound on one branch system above infinity holds on all of them.** -/
lemma infOrd_of_sys (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (z : C⟮S.x⟯⟮S.y⟯) (k : ℤ)
    (h : ∀ r (hr : r ∈ l), LowerBd (S.embG (infSub N) (infSub_injective N hN) r
      (S.root_of_mem hl hr) z) (-(k * N))) : S.InfOrd K z k := by
  intro N' hN' l' hl' r' hr'
  have hN'0 := Nat.pos_of_ne_zero hN'
  have hlen : l.length = S.F.natDegree := S.length_of_split hl
  have hlen' : l'.length = S.F.natDegree := S.length_of_split hl'
  set rv : Fin S.F.natDegree → LaurentSeries K := fun k ↦ l[(k : ℕ)]'(by rw [hlen]; exact k.2)
    with hrv
  set rv' : Fin S.F.natDegree → LaurentSeries K := fun k ↦ l'[(k : ℕ)]'(by rw [hlen']; exact k.2)
    with hrv'
  have hs : S.F.map (infSub N) = ∏ k, (X - Polynomial.C (rv k)) := by
    rw [hl, ← List.prod_ofFn]
    congr 1
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2; simp [hrv]
  have hs' : S.F.map (infSub N') = ∏ k, (X - Polynomial.C (rv' k)) := by
    rw [hl', ← List.prod_ofFn]
    congr 1
    apply List.ext_getElem
    · simp [hlen']
    · intro i h1 h2; simp [hrv']
  obtain ⟨i', hi', hri'⟩ := List.getElem_of_mem hr'
  set k' : Fin S.F.natDegree := ⟨i', by rw [← hlen']; exact hi'⟩ with hk'
  have hrk' : rv' k' = r' := hri'
  obtain ⟨kk, hkk⟩ := S.inf_rel N N' hN hN'0 rv rv' hs hs' k'
  have hkkm : rv kk ∈ l := List.getElem_mem _
  have h1 := h (rv kk) hkkm
  have h2 : LowerBd (lsub N' hN'0 (S.embG (infSub N) (infSub_injective N hN) (rv kk)
      (S.root_of_split _ rv hs kk) z)) (N' * (-(k * N))) :=
    (lowerBd_lsub_iff _ _ _ _).mpr h1
  rw [← hkk z] at h2
  have h3 : LowerBd (S.embG (infSub N') (infSub_injective N' hN'0) (rv' k')
      (S.root_of_split _ rv' hs' k') z) (-(k * N')) := by
    refine (lowerBd_lsub_iff (M := N) (hM := hN) _ _).mp ?_
    convert h2 using 1
    ring
  rw [S.embG_eq_of_eq (infSub N') (infSub_injective N' hN'0) hrk'.symm
    (S.root_of_mem hl' hr') (S.root_of_split _ rv' hs' k') z]
  exact h3

set_option maxHeartbeats 4000000 in
/-- **The gauge at infinity for unramified rational places of any slopes**: if the roots above
infinity have pairwise distinct order and leading coefficient, orders divisible by `N` and leading
coefficients in `C`, the values at the places at infinity of the rescaled basis form an invertible
matrix `A` over `C` with `A′ = Λ A`. -/
theorem multi_gauge [IsGalois C K] (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′) (N : ℕ) (hN : 0 < N)
    (l : List (LaurentSeries K)) (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (hdata : ∀ ρ ∈ l, (N : ℤ) ∣ ρ.order ∧ ρ.coeff ρ.order ∈ Set.range (algebraMap C K) ∧
      ∀ ρ' ∈ l, ρ'.order = ρ.order → ρ'.coeff ρ'.order = ρ.coeff ρ.order → ρ' = ρ)
    (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ)
    (hrw : ∀ j, S.InfOrd K (w j) (r j)) (hred : S.Reduced K w r) (S0 : C[X]) (hS00 : S0 ≠ 0)
    (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C η) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
      S.polyE S0 = ∑ j, S.polyE (P i j) * w j)
    (hdeg : ∀ i j, (pqV η r P S0 i j).natDegree ≤ (X ^ (r i + 1) * S0).natDegree) :
    ∃ A : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C, A.det ≠ 0 ∧
      ∀ i m, (A i m)′ = ∑ j, (pqV η r P S0 i j).coeff (X ^ (r i + 1) * S0).natDegree /
        (X ^ (r i + 1) * S0).leadingCoeff * A j m := by
  classical
  have hlen : l.length = S.F.natDegree := S.length_of_split hl
  set ρ : Fin S.F.natDegree → LaurentSeries K := fun m ↦ l[(m : ℕ)]'(by rw [hlen]; exact m.2)
    with hρdef
  have hρl : ∀ m, ρ m ∈ l := fun m ↦ List.getElem_mem _
  have hρr : ∀ m, (S.F.map (infSub N)).eval (ρ m) = 0 := fun m ↦ S.root_of_mem hl (hρl m)
  set φ : Fin S.F.natDegree → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K) := fun m ↦
    S.embG (infSub N) (infSub_injective N hN) (ρ m) (hρr m) with hφ
  have hfix : ∀ m (σ : K ≃ₐ[C] K), lmap (σ : K →+* K) (ρ m) = ρ m := fun m σ ↦
    root_fixed σ S.F N l hl (hρl m) (hdata _ (hρl m)).2.2 (hdata _ (hρl m)).2.1
  have hmem : ∀ i m, ∃ a : C, algebraMap C K a = (φ m (S.wTil w r i)).coeff 0 := fun i m ↦
    S.embG_coeff_mem N hN (ρ m) (hρr m) (hfix m) _ 0
  choose A0 hA0' using hmem
  set A : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C := Matrix.of fun i m ↦ A0 i m with hA
  have hT0 : ∀ i m, (φ m (S.wTil w r i)).coeff 0 = algebraMap C K (A i m) := fun i m ↦
    (hA0' i m).symm
  have hWLB : ∀ i m, LowerBd (φ m (S.wTil w r i)) 0 := fun i m ↦ by
    have := S.infOrd_wTil w r i (hrw i) N hN.ne' l hl (ρ m) (hρl m)
    simpa using this
  have : NeZero ((N : ℕ) : K) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  have hrotρ : ∀ m, rot ζ hζ0 (ρ m) = ρ m := fun m ↦
    S.root_rot_fixed N hζ hζ0 l hl (hρl m) (hdata _ (hρl m)).1 (hdata _ (hρl m)).2.2
  -- `A` is invertible (normality at infinity)
  have hA0 : A.det ≠ 0 := by
    intro hdet0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet0
    apply hv0
    funext i
    refine hred v ?_ i
    apply S.infOrd_of_sys N hN l hl
    intro ρ' hρ'
    obtain ⟨i', hi', hρi'⟩ := List.getElem_of_mem hρ'
    set m : Fin S.F.natDegree := ⟨i', by rw [← hlen]; exact hi'⟩ with hm
    have hρm : ρ m = ρ' := hρi'
    rw [S.embG_eq_of_eq _ _ hρm.symm _ (hρr m)]
    set z : C⟮S.x⟯⟮S.y⟯ := ∑ j, S.polyE (Polynomial.C (v j)) * ((S.polyE (X ^ r j))⁻¹ * w j)
      with hz
    have hφz : φ m z = ∑ j, HahnSeries.C (algebraMap C K (v j)) * φ m (S.wTil w r j) := by
      rw [hz, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul]
      congr 1
      rw [show S.polyE (Polynomial.C (v j)) = ⟨aeval S.x (Polynomial.C (v j)), S.aeval_mem _⟩ from rfl,
        S.embG_polyX, infSub_C]
    have hLB0 : LowerBd (φ m z) 0 := by
      rw [hφz]
      exact lowerBd_sum _ _ fun j _ ↦ by
        have := (lowerBd_C (algebraMap C K (v j))).mul (hWLB j m)
        rwa [zero_add] at this
    have hc0 : (φ m z).coeff 0 = 0 := by
      rw [hφz, HahnSeries.coeff_sum]
      have h1 : ∀ j, (HahnSeries.C (algebraMap C K (v j)) * φ m (S.wTil w r j)).coeff 0 =
          algebraMap C K (v j * A j m) := fun j ↦ by
        rw [coeff_zero_mul_of_lowerBd (lowerBd_C _) (hWLB j m), hT0, HahnSeries.C_apply,
          HahnSeries.coeff_single_same, map_mul]
      simp only [h1, ← map_sum]
      have := congrFun hv m
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [this, map_zero]
    have hLB1 : LowerBd (φ m z) 1 := fun k hk ↦ by
      rcases lt_or_ge k 0 with h | h
      · exact hLB0 k h
      · rw [show k = 0 by omega]; exact hc0
    have hrot : rot ζ hζ0 (φ m z) = φ m z := by
      rw [hφ]; dsimp only
      rw [← S.embG_rot_inf ζ hζ0 N hN hζ.pow_eq_one (ρ m) (hρr m) z]
      exact S.embG_eq_of_eq _ _ (hrotρ m) _ _ z
    have := lowerBd_N_of_rot_fixed hN hζ hζ0 _ hrot hLB1
    simpa using this
  -- the derivative: `A′ = Λ A`
  refine ⟨A, hA0, fun i m ↦ ?_⟩
  apply (algebraMap C K).injective
  set q : C[X] := X ^ (r i + 1) * S0 with hq
  have hq0 : q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
  have hqK := infSub_ne_zero (K := K) N hN q hq0
  have hmem := S.derivClosedXYW' (Polynomial.C η) hx (S.wTil w r i) (S.wTil w r i).2
  have hdw := S.deriv_wTil η hx w r S0 P hP i
  have hid : (⟨(S.wTil w r i : L)′, hmem⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE q =
      ∑ j, S.polyE (pqV η r P S0 i j) * S.wTil w r j := Subtype.ext (by
    push_cast
    exact hdw)
  have hemb := congrArg (φ m) hid
  rw [map_mul, map_sum] at hemb
  simp only [map_mul] at hemb
  rw [show φ m (S.polyE q) = infSub N q from S.embG_polyX _ _ _ _ _ _] at hemb
  have hpoly : ∀ j, φ m (S.polyE (pqV η r P S0 i j)) = infSub N (pqV η r P S0 i j) := fun j ↦
    S.embG_polyX _ _ _ _ _ _
  simp only [hpoly] at hemb
  have hder : φ m ⟨(S.wTil w r i : L)′, hmem⟩ =
      ∑ j, (infSub (K := K) N (pqV η r P S0 i j) * (infSub (K := K) N q)⁻¹) *
        φ m (S.wTil w r j) := by
    have : φ m ⟨(S.wTil w r i : L)′, hmem⟩ =
        (∑ j, infSub (K := K) N (pqV η r P S0 i j) * φ m (S.wTil w r j)) *
          (infSub (K := K) N q)⁻¹ := by
      rw [← hemb, mul_assoc, mul_inv_cancel₀ hqK, mul_one]
    rw [this, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hL := S.coeff_embG_deriv_inf η hx hK N hN (ρ m) (hρr m) (S.wTil w r i) (hWLB i m) 0
    (by exact_mod_cast hN)
  rw [← hK, ← hT0 i m, ← hL]
  change (φ m ⟨(S.wTil w r i : L)′, hmem⟩).coeff 0 = _
  rw [hder, HahnSeries.coeff_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hlim := lowerBd_infSub_div (K := K) N hN (pqV η r P S0 i j) q hq0 (hdeg i j)
  have hLB : LowerBd (infSub (K := K) N (pqV η r P S0 i j) * (infSub (K := K) N q)⁻¹) 0 := by
    have h2 := (hlim.mono (show (0 : ℤ) ≤ N by positivity)).add
      (lowerBd_C (algebraMap C K ((pqV η r P S0 i j).coeff q.natDegree / q.leadingCoeff)))
    rwa [sub_add_cancel] at h2
  rw [coeff_zero_mul_of_lowerBd hLB (hWLB j m), hT0 j m, RingHom.map_mul (algebraMap C K)]
  congr 1
  have h0 := hlim 0 (by exact_mod_cast hN)
  rw [HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_eq_zero] at h0
  exact h0

end MultiGauge

end CurveData

end Curves
