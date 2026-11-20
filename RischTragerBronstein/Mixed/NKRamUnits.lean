import RischTragerBronstein.Mixed.NKRamLead
import RischTragerBronstein.Mixed.NKUnitsInf
import RischTragerBronstein.Torsion.Conj

/-!
# Units of a curve with ramified places at infinity

* `rot_infSub`, `embG_rot_inf`: the rotation `T ↦ ζ T` (`ζᴺ = 1`) fixes `x = T^{-N}`, permutes the
  roots of a branch system above infinity, and expansions along a rotated root are the rotated
  expansions — so every function has the same orders along `ρ` and `rot ζ ρ`.
* `coeff_rot_lead`: the leading value `[ρ T^σ]₀` of `rot ζ ρ` is `ζ^{-σ}` times that of `ρ`.
* `rot_class`: if the leading values of the roots are distinct and `ζ^{-σ}` is a primitive `e`-th
  root of unity, roots whose leading values have the same `e`-th power are rotations of each other.
* `mem_pow_units_cls`: as `mem_pow_units_inf`, with the roots covered by one test root per unit and
  one more root up to roots with the same orders — for a single slope `s'/e` at infinity with `r`
  places, `r − 1` independent units suffice.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential GTors CPoly Sup

section RotInf

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

lemma rot_infSub (ζ : K) (hζ : ζ ≠ 0) (N : ℕ) (hN : ζ ^ N = 1) :
    (rot ζ hζ).comp (infSub (C := C) N) = infSub N := by
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · rw [RingHom.comp_apply, is_C, rot_C]
  · rw [RingHom.comp_apply, is_X, rot_single, zpow_neg, zpow_natCast, hN, inv_one, one_mul]

lemma rot_root_inf (ζ : K) (hζ : ζ ≠ 0) (N : ℕ) (hN : ζ ^ N = 1) (F : C[X][X]) (r : LaurentSeries K)
    (hr : (F.map (infSub N)).eval r = 0) : (F.map (infSub N)).eval (rot ζ hζ r) = 0 := by
  rw [← rot_infSub ζ hζ N hN, ← Polynomial.map_map, eval_map, eval₂_at_apply, hr, map_zero]

/-- The leading value of a rotated root. -/
lemma coeff_rot_lead (ζ : K) (hζ : ζ ≠ 0) (r : LaurentSeries K) (σ : ℕ) :
    (rot ζ hζ r * single (σ : ℤ) 1).coeff 0 = ζ ^ (-(σ : ℤ)) * (r * single (σ : ℤ) 1).coeff 0 := by
  have e : ∀ z : LaurentSeries K, (z * single (σ : ℤ) 1).coeff 0 = z.coeff (-(σ : ℤ)) := fun z ↦ by
    have := HahnSeries.coeff_mul_single_add (r := (1 : K)) (x := z) (a := -(σ : ℤ)) (b := (σ : ℤ))
    rw [neg_add_cancel, mul_one] at this
    exact this
  rw [e, e, rot_coeff]

/-- A root of a split polynomial is a member of the list. -/
lemma mem_of_root_split {l : List (LaurentSeries K)} {G : (LaurentSeries K)[X]}
    (hl : G = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K) (hr : G.eval r = 0) :
    r ∈ l := by
  rw [hl, eval_list_prod] at hr
  obtain ⟨v, hv, hv0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp hr)
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hv
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hv0
  rw [hv0]; exact hr'

/-- **Roots with the same `e`-th power of their leading values are rotations of each other.** -/
theorem rot_class (F : C[X][X]) (N σ e : ℕ) (l : List (LaurentSeries K))
    (hl : F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (hnd : (l.map fun r ↦ (r * single (σ : ℤ) 1).coeff 0).Nodup)
    (ζ : K) (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) (hω : IsPrimitiveRoot (ζ ^ σ) e) (he0 : 0 < e)
    (r r' : LaurentSeries K) (hr : r ∈ l) (hr' : r' ∈ l)
    (hc0 : (r * single (σ : ℤ) 1).coeff 0 ≠ 0)
    (he : ((r' * single (σ : ℤ) 1).coeff 0) ^ e = ((r * single (σ : ℤ) 1).coeff 0) ^ e) :
    ∃ j : ℕ, ∃ hj : ζ ^ j ≠ 0, rot (ζ ^ j) hj r = r' := by
  classical
  set c := (r * single (σ : ℤ) 1).coeff 0 with hc
  set c' := (r' * single (σ : ℤ) 1).coeff 0 with hc'
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  -- `c'/c` is an `e`-th root of unity, a power of `(ζ^σ)⁻¹`
  have hpow : (c' / c) ^ e = 1 := by rw [div_pow, he, div_self (pow_ne_zero _ hc0)]
  haveI : NeZero e := ⟨he0.ne'⟩
  have hωi : IsPrimitiveRoot (ζ ^ σ)⁻¹ e := hω.inv
  obtain ⟨j, -, hj⟩ := hωi.eq_pow_of_pow_eq_one hpow
  have hzj : ζ ^ j ≠ 0 := pow_ne_zero _ hζ0
  refine ⟨j, hzj, ?_⟩
  have hNj : (ζ ^ j) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hmem : rot (ζ ^ j) hzj r ∈ l :=
    mem_of_root_split hl _ (rot_root_inf (ζ ^ j) hzj N hNj F r (by
      rw [hl, eval_list_prod]
      exact List.prod_eq_zero (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, by simp⟩)))
  have hlead : (rot (ζ ^ j) hzj r * single (σ : ℤ) 1).coeff 0 = c' := by
    rw [coeff_rot_lead, ← hc]
    have : (ζ ^ j) ^ (-(σ : ℤ)) = ((ζ ^ σ)⁻¹) ^ j := by
      rw [zpow_neg, zpow_natCast, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
    rw [this, hj, div_mul_cancel₀ _ hc0]
  exact List.inj_on_of_nodup_map hnd hmem hr' (by rw [hlead])

end RotInf

section UnitsCls

variable {C L Kb : Type*} [Field C] [Field L] [Algebra C L] [Field Kb] [Algebra C Kb]
  [IsAlgClosed Kb] [CharZero Kb]

namespace CurveData

variable (S : CurveData C L)

/-- **Conjugate roots above infinity**: the expansion along `rot ζ r` is the rotated expansion. -/
lemma embG_rot_inf (ζ : Kb) (hζ : ζ ≠ 0) (N : ℕ) (hN : 0 < N) (hζN : ζ ^ N = 1)
    (r : LaurentSeries Kb) (hr : (S.F.map (infSub N)).eval r = 0) (f : C⟮S.x⟯⟮S.y⟯) :
    S.embG (infSub N) (infSub_injective N hN) (rot ζ hζ r) (rot_root_inf ζ hζ N hζN S.F r hr) f =
      rot ζ hζ (S.embG (infSub N) (infSub_injective N hN) r hr f) := by
  have hc := rot_infSub (C := C) ζ hζ N hζN
  have hinj : Function.Injective ((rot ζ hζ).comp (infSub (C := C) (K := Kb) N)) := by
    rw [hc]; exact infSub_injective N hN
  have h := S.embG_comp (rot ζ hζ) (infSub N) (infSub_injective N hN) hinj r hr
    (by rw [hc]; exact rot_root_inf ζ hζ N hζN S.F r hr)
  have := congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries Kb ↦ φ f) h
  simp only [RingHom.comp_apply] at this
  rw [this]
  exact congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries Kb ↦ φ f) (S.embG_congr' hc.symm _ _ rfl _ _)

/-- Orders along rotated roots agree. -/
lemma order_embG_rot_inf (ζ : Kb) (hζ : ζ ≠ 0) (N : ℕ) (hN : 0 < N) (hζN : ζ ^ N = 1)
    (r r' : LaurentSeries Kb) (hr : (S.F.map (infSub N)).eval r = 0)
    (hr' : (S.F.map (infSub N)).eval r' = 0) (hrr : rot ζ hζ r = r') (f : C⟮S.x⟯⟮S.y⟯) :
    (S.embG (infSub N) (infSub_injective N hN) r' hr' f).order =
      (S.embG (infSub N) (infSub_injective N hN) r hr f).order := by
  subst hrr
  rw [S.embG_rot_inf ζ hζ N hN hζN r hr f, order_rot]


/-- The leading polynomial of weight `N s'` at `x = T^{-N e}` is the intrinsic one. -/
lemma leadPolyR_scale (F : C[X][X]) (N e s' : ℕ) (hN : 0 < N) :
    leadPolyR (N * e) (N * s') F = leadPolyR e s' F := by
  unfold leadPolyR
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h1 : N * s' * (F.natDegree - i) = N * (s' * (F.natDegree - i)) := by ring
  rw [h1]
  simp only [Nat.mul_dvd_mul_iff_left hN, Nat.mul_div_mul_left _ _ hN]

/-- **The classes of the roots above infinity for a single slope `s'/e`** (residual polynomial with
distinct non-zero roots `γ̃ₖ`): test roots for the first `m` classes and a root of the last one
cover all roots up to rotations. -/
theorem cover_ram [CharZero C] (e s' : ℕ) (he : 0 < e) (hcop : Nat.Coprime s' e)
    {m : ℕ} (γ : Fin (m + 1) → C) (hγinj : Function.Injective γ) (hγ0 : ∀ k, γ k ≠ 0)
    (hmon : S.F.Monic)
    (hdeg : ∀ i < S.F.natDegree, e * (S.F.coeff i).natDegree ≤ s' * (S.F.natDegree - i))
    (hlead : leadPolyR e s' S.F = ∏ k, (X ^ e - Polynomial.C (γ k)))
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries Kb))
    (hl : S.F.map (infSub (N * e)) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    ∃ (tq : Fin m → Fin l.length) (p₀ : Fin l.length), ∀ p : Fin l.length,
      (∃ q, ∀ f : C⟮S.x⟯⟮S.y⟯, (S.embG (infSub (N * e)) (infSub_injective (N * e) (by positivity))
          (l.get p) (S.root_of_mem hl (List.get_mem l p)) f).order =
        (S.embG (infSub (N * e)) (infSub_injective (N * e) (by positivity)) (l.get (tq q))
          (S.root_of_mem hl (List.get_mem l (tq q))) f).order) ∨
      ∀ f : C⟮S.x⟯⟮S.y⟯, (S.embG (infSub (N * e)) (infSub_injective (N * e) (by positivity))
          (l.get p) (S.root_of_mem hl (List.get_mem l p)) f).order =
        (S.embG (infSub (N * e)) (infSub_injective (N * e) (by positivity)) (l.get p₀)
          (S.root_of_mem hl (List.get_mem l p₀)) f).order := by
  classical
  have hNe : 0 < N * e := Nat.mul_pos hN he
  set c : LaurentSeries Kb → Kb := fun r ↦ (r * single ((N * s' : ℕ) : ℤ) 1).coeff 0 with hc
  have hdeg' : ∀ i < S.F.natDegree, N * e * (S.F.coeff i).natDegree ≤ N * s' * (S.F.natDegree - i) :=
    fun i hi ↦ by
      have := Nat.mul_le_mul_left N (hdeg i hi)
      calc N * e * (S.F.coeff i).natDegree = N * (e * (S.F.coeff i).natDegree) := by ring
        _ ≤ N * (s' * (S.F.natDegree - i)) := this
        _ = N * s' * (S.F.natDegree - i) := by ring
  obtain ⟨-, hprod⟩ := leadPolyR_eq_prod (K := Kb) (N * e) (N * s') hNe S.F hmon hdeg' l hl
  rw [leadPolyR_scale S.F N e s' hN, hlead, Polynomial.map_prod] at hprod
  set ι := algebraMap C Kb
  have hP : ∀ k, (X ^ e - Polynomial.C (γ k)).map ι = X ^ e - Polynomial.C (ι (γ k)) := fun k ↦ by
    simp
  simp only [hP] at hprod
  -- the leading values are distinct
  have hsep : (∏ k, (X ^ e - Polynomial.C (ι (γ k)))).Separable := by
    refine Polynomial.separable_prod' (fun a _ b _ hab ↦ ?_) (fun a _ ↦ ?_)
    · have hne : ι (γ b) - ι (γ a) ≠ 0 := sub_ne_zero.mpr fun h ↦ hab (hγinj (ι.injective h).symm)
      refine ⟨Polynomial.C (ι (γ b) - ι (γ a))⁻¹, -Polynomial.C (ι (γ b) - ι (γ a))⁻¹, ?_⟩
      rw [neg_mul, ← sub_eq_add_neg, ← mul_sub]
      rw [show (X ^ e - Polynomial.C (ι (γ a))) - (X ^ e - Polynomial.C (ι (γ b))) =
        Polynomial.C (ι (γ b) - ι (γ a)) by rw [map_sub]; ring]
      rw [← C_mul, inv_mul_cancel₀ hne, C_1]
    · exact Polynomial.separable_X_pow_sub_C _ (by exact_mod_cast he.ne')
        ((map_ne_zero_iff _ ι.injective).mpr (hγ0 a))
  have hnd : (l.map c).Nodup := by
    have h1 := Polynomial.nodup_roots hsep
    rw [hprod] at h1
    have e2 : (l.map fun r ↦ X - Polynomial.C (c r)) = ((l.map c).map fun a ↦ X - Polynomial.C a) := by
      rw [List.map_map]; rfl
    rw [e2, ← Multiset.prod_coe, ← Multiset.map_coe, roots_multiset_prod_X_sub_C] at h1
    exact Multiset.coe_nodup.mp h1
  -- every leading value is an `e`-th root of some `γ k`
  have hroot : ∀ r ∈ l, ∃ k, c r ^ e = ι (γ k) := by
    intro r hr
    have h0 : (∏ k, (X ^ e - Polynomial.C (ι (γ k)))).eval (c r) = 0 := by
      rw [hprod, eval_list_prod]
      exact List.prod_eq_zero (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, by
        simp only [eval_sub, eval_X, eval_C]; exact sub_eq_zero.mpr rfl⟩)
    rw [eval_prod] at h0
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h0
    exact ⟨k, by simpa [sub_eq_zero] using hk⟩
  have hc0 : ∀ r ∈ l, c r ≠ 0 := fun r hr h ↦ by
    obtain ⟨k, hk⟩ := hroot r hr
    rw [h, zero_pow he.ne'] at hk
    exact hγ0 k (ι.injective (by rw [← hk, map_zero]))
  -- every class has a root
  have hex : ∀ k, ∃ r ∈ l, c r ^ e = ι (γ k) := by
    intro k
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (ι (γ k)) he
    have h0 : (∏ k, (X ^ e - Polynomial.C (ι (γ k)))).eval a = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [ha])
    rw [hprod, eval_list_prod] at h0
    obtain ⟨v, hv, hv0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hv0
    refine ⟨r, hr, ?_⟩
    have hca : c r = a := hv0.symm
    rw [hca, ha]
  choose ρk hρkl hρk using hex
  have hidx : ∀ k, ∃ i : Fin l.length, l.get i = ρk k := fun k ↦ List.get_of_mem (hρkl k)
  choose ik hik using hidx
  -- the rotations
  have : NeZero (((N * e : ℕ)) : Kb) := ⟨by exact_mod_cast hNe.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Kb (N * e)
  have hζN : IsPrimitiveRoot (ζ ^ N) e := hζ.pow hNe (by ring)
  have hω : IsPrimitiveRoot (ζ ^ (N * s')) e := by
    rw [pow_mul]; exact hζN.pow_of_coprime s' hcop
  have horb : ∀ k (p : Fin l.length), c (l.get p) ^ e = ι (γ k) → ∀ f : C⟮S.x⟯⟮S.y⟯,
      (S.embG (infSub (N * e)) (infSub_injective (N * e) hNe) (l.get p)
        (S.root_of_mem hl (List.get_mem l p)) f).order =
      (S.embG (infSub (N * e)) (infSub_injective (N * e) hNe) (l.get (ik k))
        (S.root_of_mem hl (List.get_mem l (ik k))) f).order := by
    intro k p hp f
    obtain ⟨j, hj, hrot⟩ := rot_class S.F (N * e) (N * s') e l hl hnd ζ hζ hNe hω he (l.get (ik k))
      (l.get p) (List.get_mem l _) (List.get_mem l p) (hc0 _ (List.get_mem l _))
      (by rw [hp, hik, hρk])
    have hjN : (ζ ^ j) ^ (N * e) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    exact S.order_embG_rot_inf (ζ ^ j) hj (N * e) hNe hjN _ _ _ _ hrot f
  refine ⟨fun q ↦ ik q.castSucc, ik (Fin.last m), fun p ↦ ?_⟩
  obtain ⟨k, hk⟩ := hroot (l.get p) (List.get_mem l p)
  refine Fin.lastCases (motive := fun k ↦ c (l.get p) ^ e = ι (γ k) → _) (fun h ↦ Or.inr ?_)
    (fun q h ↦ Or.inl ⟨q, ?_⟩) k hk
  · exact horb (Fin.last m) p h
  · exact horb q.castSucc p h

set_option maxHeartbeats 8000000 in
/-- **Units are power products of given independent units over classes of roots**: the roots of a
branch system above infinity are covered by test roots `tq q` (one per unit) and one more root
`p₀` up to roots along which every function has the same orders (e.g. rotations
`T ↦ ζ T`); then every unit `w` satisfies `w^N = c ∏ uᵢ^{aᵢ}`, `N ≠ 0`. -/
theorem mem_pow_units_cls [CharZero C] (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries Kb))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    {m : ℕ} (tq : Fin m → Fin l.length) (p₀ : Fin l.length)
    (hcover : ∀ p : Fin l.length,
      (∃ q, ∀ f : C⟮S.x⟯⟮S.y⟯, (S.embG (infSub N) (infSub_injective N hN) (l.get p)
          (S.root_of_mem hl (List.get_mem l p)) f).order =
        (S.embG (infSub N) (infSub_injective N hN) (l.get (tq q))
          (S.root_of_mem hl (List.get_mem l (tq q))) f).order) ∨
      ∀ f : C⟮S.x⟯⟮S.y⟯, (S.embG (infSub N) (infSub_injective N hN) (l.get p)
          (S.root_of_mem hl (List.get_mem l p)) f).order =
        (S.embG (infSub N) (infSub_injective N hN) (l.get p₀)
          (S.root_of_mem hl (List.get_mem l p₀)) f).order)
    (u : Fin m → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i, u i ≠ 0)
    (hfinu : ∀ i (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u i)).order = 0)
    (hind : ∀ a : Fin m → ℤ, (∃ c : C, ∏ i, (u i : L) ^ a i = algebraMap C L c) → a = 0)
    (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (hfin : ∀ (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) w).order = 0) :
    ∃ (N' : ℤ) (a : Fin m → ℤ), N' ≠ 0 ∧ ∃ c : C,
      (w : L) ^ N' = algebraMap C L c * ∏ i, (u i : L) ^ a i := by
  classical
  set ρ : Fin l.length → LaurentSeries Kb := fun p ↦ l.get p with hρ
  have hρl : ∀ p, ρ p ∈ l := fun p ↦ List.get_mem _ _
  set φ : Fin l.length → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries Kb) := fun p ↦
    S.embG (infSub N) (infSub_injective N hN) (ρ p) (S.root_of_mem hl (hρl p)) with hφ
  -- orders of power products
  have hordp : ∀ (g : C[X] →+* LaurentSeries Kb) (hg : Function.Injective g) (Y : LaurentSeries Kb)
      (hY : (S.F.map g).eval Y = 0) (e0 : ℤ) (e : Fin m → ℤ),
      (S.embG g hg Y hY (w ^ e0 * ∏ i, u i ^ e i)).order =
        e0 * (S.embG g hg Y hY w).order + ∑ i, e i * (S.embG g hg Y hY (u i)).order := by
    intro g hg Y hY e0 e
    have hw' : S.embG g hg Y hY w ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hw
    obtain ⟨hp0, hpo⟩ := order_prod_zpow_nk Finset.univ (fun i ↦ S.embG g hg Y hY (u i))
      (fun i _ ↦ (map_ne_zero_iff _ (RingHom.injective _)).mpr (hu i)) e
    rw [map_mul, map_zpow₀, map_prod]
    simp only [map_zpow₀]
    rw [HahnSeries.order_mul (zpow_ne_zero _ hw') hp0, order_zpow_ls _ hw', hpo]
  have hprod_ne : ∀ (e0 : ℤ) (e : Fin m → ℤ), w ^ e0 * ∏ i, u i ^ e i ≠ 0 := fun e0 e ↦
    mul_ne_zero (zpow_ne_zero _ hw) (Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hu i))
  -- a power product with vanishing orders at the roots `0, …, m − 1` is a constant
  have hkey : ∀ (e0 : ℤ) (e : Fin m → ℤ),
      (∀ p : Fin m, e0 * (φ (tq p) w).order + ∑ i, e i * (φ (tq p) (u i)).order = 0) →
      ∃ c : C, ((w ^ e0 * ∏ i, u i ^ e i : C⟮S.x⟯⟮S.y⟯) : L) = algebraMap C L c := by
    intro e0 e hzero
    set y := w ^ e0 * ∏ i, u i ^ e i with hy
    have hy1 : ∀ (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
        (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S.embG (branchSub N a)
          (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r (S.root_of_mem hl hr) y).order = 0 :=
      fun a N hN l hl r hr ↦ by
        rw [hy, hordp, hfin a N hN l hl r hr, Finset.sum_eq_zero fun i _ ↦ by
          rw [hfinu i a N hN l hl r hr, mul_zero]]; ring
    have hsum := S.unit_sum_inf y (hprod_ne e0 e) hy1 N hN l hl
    rw [sum_attach_eq_fin l (fun r hr ↦ (S.embG (infSub N) (infSub_injective N hN) r
      (S.root_of_mem hl hr) y).order)] at hsum
    have hall : ∀ p : Fin l.length, (φ p y).order = 0 := by
      have hlow : ∀ p : Fin m, (φ (tq p) y).order = 0 := fun p ↦ by
        rw [hy, hφ]; dsimp only; rw [hordp]; exact hzero p
      set o := (φ p₀ y).order with ho
      have hcl : ∀ p, (φ p y).order = 0 ∨ (φ p y).order = o := fun p ↦ by
        rcases hcover p with ⟨q, hq⟩ | hq
        · left; rw [show (φ p y).order = (φ (tq q) y).order from hq y]; exact hlow q
        · right; exact hq y
      have hsum' : ∑ p : Fin l.length, (φ p y).order = 0 := hsum
      by_cases ho0 : o = 0
      · intro p; rcases hcl p with h | h
        · exact h
        · rw [h, ho0]
      · exfalso
        have hpos : ∀ p, (φ p y).order = if (φ p y).order = 0 then 0 else o := fun p ↦ by
          rcases hcl p with h | h
          · rw [if_pos h, h]
          · rw [if_neg (by rw [h]; exact ho0), h]
        rw [Finset.sum_congr rfl fun p _ ↦ hpos p, Finset.sum_ite, Finset.sum_const_zero,
          zero_add, Finset.sum_const, nsmul_eq_mul] at hsum'
        have hcard : ((Finset.univ.filter fun p ↦ ¬(φ p y).order = 0).card : ℤ) = 0 :=
          (mul_eq_zero.mp hsum').resolve_right ho0
        have hp0 : p₀ ∈ Finset.univ.filter fun p ↦ ¬(φ p y).order = 0 :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho0⟩
        have := Finset.card_pos.mpr ⟨p₀, hp0⟩
        omega
    have hreg : S.RegularFinite Kb y := fun a N hN l hl r hr ↦ (hy1 a N hN l hl r hr).ge
    obtain ⟨M0, hM0, hyM⟩ := S.algebraic_of_regular_l y hreg N hN l hl fun r hr ↦ by
      obtain ⟨⟨p, hp⟩, rfl⟩ := List.get_of_mem hr
      have := hall ⟨p, hp⟩
      exact this.ge
    exact S.mem_const_of_alg_geo hgeo y M0 hM0 hyM
  -- the order matrix of the units at the roots `0, …, m − 1`
  set A : Matrix (Fin m) (Fin m) ℤ := fun i p ↦ (φ (tq p) (u i)).order with hA
  set b : Fin m → ℤ := fun p ↦ (φ (tq p) w).order with hb
  have hcoe : ∀ (e0 : ℤ) (e : Fin m → ℤ), ((w ^ e0 * ∏ i, u i ^ e i : C⟮S.x⟯⟮S.y⟯) : L) =
      (w : L) ^ e0 * ∏ i, (u i : L) ^ e i := fun e0 e ↦ by
    rw [IntermediateField.coe_mul, show ((w ^ e0 : C⟮S.x⟯⟮S.y⟯) : L) = (w : L) ^ e0 from
      map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val w e0, IntermediateField.coe_prod]
    congr 1
  by_cases hdet : A.det = 0
  · -- the units would be dependent
    exfalso
    obtain ⟨a, ha0, hAa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
      (show A.transpose.det = 0 by rw [Matrix.det_transpose]; exact hdet)
    obtain ⟨c, hc⟩ := hkey 0 a fun p ↦ by
      have := congrFun hAa p
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA, Pi.zero_apply] at this
      rw [zero_mul, zero_add]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    apply ha0
    apply hind a
    refine ⟨c, ?_⟩
    rw [← hc, hcoe, zpow_zero, one_mul]
  · -- Cramer: `A.transpose (adj A.transpose b) = det A • b`
    set a : Fin m → ℤ := Matrix.mulVec (A.transpose).adjugate b with ha
    have hAa : Matrix.mulVec A.transpose a = A.det • b := by
      rw [ha, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.det_transpose, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    obtain ⟨c, hc⟩ := hkey A.det (fun i ↦ -a i) fun p ↦ by
      have := congrFun hAa p
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA, Pi.smul_apply,
        smul_eq_mul] at this
      have e : ∑ i, -a i * (φ (tq p) (u i)).order = -(A.det * b p) := by
        rw [← this, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [neg_mul, mul_comm (a i)]; rfl
      rw [e, hb]; ring
    refine ⟨A.det, a, hdet, c, ?_⟩
    rw [hcoe] at hc
    have hprodne : ∏ i, (u i : L) ^ a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦
      zpow_ne_zero _ (fun h ↦ hu i (Subtype.ext h))
    have e2 : ∏ i, (u i : L) ^ (-a i) = (∏ i, (u i : L) ^ a i)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ zpow_neg _ _
    rw [e2] at hc
    rw [← hc, mul_assoc, inv_mul_cancel₀ hprodne, mul_one]


/-- **For a single slope `s'/e` at infinity (`r` places), `r − 1` independent units span the
units.** -/
theorem unitsSpan_ram [CharZero C] (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (e s' : ℕ) (he : 0 < e) (hcop : Nat.Coprime s' e)
    {m : ℕ} (γ : Fin (m + 1) → C) (hγinj : Function.Injective γ) (hγ0 : ∀ k, γ k ≠ 0)
    (hmon : S.F.Monic)
    (hdeg : ∀ i < S.F.natDegree, e * (S.F.coeff i).natDegree ≤ s' * (S.F.natDegree - i))
    (hlead : leadPolyR e s' S.F = ∏ k, (X ^ e - Polynomial.C (γ k)))
    (u : Fin m → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i, u i ≠ 0)
    (hfinu : ∀ i (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u i)).order = 0)
    (hind : ∀ a : Fin m → ℤ, (∃ c : C, ∏ i, (u i : L) ^ a i = algebraMap C L c) → a = 0) :
    S.UnitsSpan Kb u := by
  intro w hw hfin
  obtain ⟨Ni, hNi, li, -, hli⟩ := S.hasBranchesInf (K := Kb)
  have hNi' := Nat.pos_of_ne_zero hNi
  have hli' := branchSys_lsub S.F Ni e he li hli
  obtain ⟨tq, p₀, hcov⟩ := S.cover_ram e s' he hcop γ hγinj hγ0 hmon hdeg hlead Ni hNi'
    (li.map (lsub e he)) hli'
  exact S.mem_pow_units_cls hgeo (Ni * e) (Nat.mul_pos hNi' he) (li.map (lsub e he)) hli' tq p₀ hcov
    u hu hfinu hind w hw hfin

end CurveData

end UnitsCls

end Curves
