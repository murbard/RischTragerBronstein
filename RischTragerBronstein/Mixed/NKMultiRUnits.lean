import RischTragerBronstein.Mixed.NKMultiRData
import RischTragerBronstein.Mixed.NKMultiRam
import RischTragerBronstein.Mixed.NKRamUnits

/-!
# Units for several places at infinity of any slopes

The places above infinity of a curve with Newton segments of rational slopes `sₖ/eₖ` and residual
polynomials `c Z^{lo} ∏_{γ ∈ Γₖ} (Z^{eₖ} − γ)` are the pairs `(k, γ)`: the roots with order
`−(N/eₖ) sₖ` and `lcᵉ = γ` are the rotations of one of them (`rot_of_pow_eq`), so their expansions
have the same orders. Hence `∑ₖ |Γₖ| − 1` independent units span the units (`unitsSpan_multiR`,
from `mem_pow_units_cls`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

/-- The weights `(N/eₖ) sₖ` of strictly decreasing slopes `sₖ/eₖ` are strictly decreasing. -/
lemma strictAnti_weights {q : ℕ} (N : ℕ) (hN : 0 < N) (e : Fin (q + 1) → ℕ) (he : ∀ k, 0 < e k)
    (hed : ∀ k, e k ∣ N) (s : Fin (q + 1) → ℤ)
    (hdec : ∀ k : Fin q, s k.succ * e k.castSucc < s k.castSucc * e k.succ) :
    StrictAnti fun k ↦ ((N / e k : ℕ) : ℤ) * s k := by
  have hNe : ∀ k, ((N / e k : ℕ) : ℤ) * e k = N := fun k ↦ by
    exact_mod_cast Nat.div_mul_cancel (hed k)
  rw [Fin.strictAnti_iff_succ_lt]
  intro k
  have h1 := hdec k
  have hp : (0 : ℤ) < e k.castSucc * e k.succ := by
    have := he k.castSucc; have := he k.succ; positivity
  refine lt_of_mul_lt_mul_right ?_ hp.le
  have e1 : ((N / e k.succ : ℕ) : ℤ) * s k.succ * (e k.castSucc * e k.succ) =
      N * (s k.succ * e k.castSucc) := by rw [← hNe k.succ]; ring
  have e2 : ((N / e k.castSucc : ℕ) : ℤ) * s k.castSucc * (e k.castSucc * e k.succ) =
      N * (s k.castSucc * e k.succ) := by rw [← hNe k.castSucc]; ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left h1 (by exact_mod_cast hN)

section RotPow

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- **Roots with the same order and the same `e`-th power of the leading coefficient are rotations
of each other** (`gcd(sp, e) = 1`). -/
lemma rot_of_pow_eq (F : C[X][X]) (N : ℕ) (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (l : List (LaurentSeries K)) (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    {r r' : LaurentSeries K} (hr : r ∈ l) (hr' : r' ∈ l) (hr0 : r ≠ 0) (e : ℕ) (he : 0 < e)
    (hdvd : e ∣ N) (sp : ℤ) (hcop : Int.gcd sp e = 1) (hord : r.order = -((N / e : ℕ) * sp))
    (hord' : r'.order = r.order) (hpow : (r'.coeff r'.order) ^ e = (r.coeff r.order) ^ e)
    (huniq : ∀ r₁ ∈ l, ∀ r₂ ∈ l, r₁.order = r₂.order → r₁.coeff r₁.order = r₂.coeff r₂.order →
      r₁ = r₂) :
    ∃ j : ℕ, r' = rot (ζ ^ j) (pow_ne_zero _ (hζ.ne_zero hN.ne')) r := by
  classical
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  set c := r.coeff r.order with hc
  have hc0 : c ≠ 0 := fun h ↦ hr0 (HahnSeries.coeff_order_eq_zero.mp h)
  set u := r'.coeff r'.order / c with hu
  have hue : u ^ e = 1 := by rw [hu, div_pow, hpow, div_self (pow_ne_zero _ hc0)]
  obtain ⟨d, hd⟩ := hdvd
  have hNe : N / e = d := by rw [hd, Nat.mul_div_cancel_left _ he]
  have hω : IsPrimitiveRoot (ζ ^ d) e := hζ.pow hN (by rw [hd, mul_comm])
  have hωs : IsPrimitiveRoot ((ζ ^ d) ^ (-sp)) e :=
    hω.zpow_of_gcd_eq_one (-sp) (by rw [Int.neg_gcd]; exact hcop)
  haveI : NeZero e := ⟨he.ne'⟩
  obtain ⟨j, -, hj⟩ := hωs.eq_pow_of_pow_eq_one hue
  refine ⟨j, ?_⟩
  have hζj0 : ζ ^ j ≠ 0 := pow_ne_zero _ hζ0
  have hζjN : (ζ ^ j) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hrr : (F.map (infSub N)).eval r = 0 := by
    rw [hl, eval_list_prod]
    exact List.prod_eq_zero (List.mem_map.mpr ⟨X - Polynomial.C r, List.mem_map.mpr ⟨r, hr, rfl⟩,
      by simp⟩)
  have h2 : rot (ζ ^ j) hζj0 r ∈ l :=
    mem_of_eval_prod l _ (by rw [← hl]; exact rot_root_inf _ hζj0 N hζjN F r hrr)
  refine huniq _ hr' _ h2 (by rw [hord', rot_order]) ?_
  rw [rot_lc]
  have hpow' : (ζ ^ j) ^ r.order = ((ζ ^ d) ^ (-sp)) ^ j := by
    rw [hord, hNe, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
      ← zpow_mul]
    congr 1
    ring
  rw [hpow', hj, hu, div_mul_cancel₀ _ hc0]

end RotPow

section UnitsMultiR

variable {C L Kb : Type*} [Field C] [Field L] [Algebra C L] [Field Kb] [Algebra C Kb]
  [IsAlgClosed Kb] [CharZero Kb]

namespace CurveData

variable (S : CurveData C L)

/-- **`∑ₖ |Γₖ| − 1` independent units span the units** for a curve with Newton segments of
rational slopes `sₖ/eₖ` at infinity. -/
theorem unitsSpan_multiR [CharZero C] (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
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
    {mu : ℕ} (hcount : ∑ k, (Γ k).length = mu + 1)
    (u : Fin mu → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i, u i ≠ 0)
    (hfinu : ∀ i (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u i)).order = 0)
    (hind : ∀ a : Fin mu → ℤ, (∃ c : C, ∏ i, (u i : L) ^ a i = algebraMap C L c) → a = 0) :
    S.UnitsSpan Kb u := by
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
  have hP : Fintype.card (Σ k : Fin (q + 1), Fin (Γ k).length) = mu + 1 := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact hcount
  set eqv : (Σ k : Fin (q + 1), Fin (Γ k).length) ≃ Fin (mu + 1) :=
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
  refine S.mem_pow_units_cls hgeo N hN lr hl (fun q' ↦ rt (eqv.symm q'.castSucc))
    (rt (eqv.symm (Fin.last mu))) (fun p ↦ ?_) u hu hfinu hind w hw hfin
  by_cases hlt : (eqv (pl p) : ℕ) < mu
  · left
    refine ⟨⟨eqv (pl p), hlt⟩, fun f ↦ ?_⟩
    have : eqv.symm (Fin.castSucc ⟨eqv (pl p), hlt⟩) = pl p := by
      rw [Equiv.symm_apply_eq]; ext; rfl
    rw [this]
    exact hsame p f
  · right
    intro f
    have : eqv.symm (Fin.last mu) = pl p := by
      rw [Equiv.symm_apply_eq]
      ext
      simp only [Fin.val_last]
      have := (eqv (pl p)).2
      omega
    rw [this]
    exact hsame p f

end CurveData

end UnitsMultiR

end Curves
