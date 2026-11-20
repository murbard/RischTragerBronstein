import RischTragerBronstein.Mixed.NKTorsion

/-!
# Liouville forms with residues at arbitrary places

The place version of `Mixed/NKTorsion`: the degree argument at infinity for orders given along
the roots of `F(αⱼ + T^{Nⱼ}, Y)` (`order_inf_of_places`), simple poles along ramified branches
(`embG_pole_N`), and the effective principal divisor `DivGE` built from a Liouville form
(`divGE_of_liouville`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

section Inf

open Differential

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]
  [IsAlgClosed K] [CharZero K]

namespace CurveData

variable (S : CurveData C L)

/-- **The order at infinity from the finite orders at places** (single place at infinity): if
`z` has orders `o_j(r)` along the roots `r` of `F(α_j + T^{N_j}, Y)` with `∑_r o_j(r) = N_j g_j`,
and order `0` at every other finite branch, then `n · ord_∞ z = −N ∑ g_j` along every branch
`x = T^{−N}`. -/
theorem order_inf_of_places (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d) (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0) {J : Type*} [Fintype J]
    (α : J → K) (hα : Function.Injective α) (Nf : J → ℕ) (hNf : ∀ j, 0 < Nf j)
    (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (Nf j) (α j)) = ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (o : J → LaurentSeries K → ℤ)
    (ho : ∀ j r (hr : r ∈ lf j), (S.embG (branchSub (Nf j) (α j)) (branchSub_injective _ (hNf j) _)
      r (S.root_of_mem (hlf j) hr) z).order = o j r)
    (g : J → ℤ) (hg : ∀ j, ((lf j).map (o j)).sum = Nf j * g j)
    (hother : ∀ b : K, b ∉ Set.range α → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), (S.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S.root_of_mem hl hr) z).order = 0)
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l) :
    (n : ℤ) * (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
      (S.root_of_mem hl hr) z).order = -((N : ℤ) * ∑ j, g j) := by
  classical
  have hF1 : S.F ≠ 1 := fun h ↦ by rw [h, natDegree_one] at hn; omega
  obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt z hF1
  have hxQ : aeval S.x Q ≠ 0 := fun h ↦ hQ ((transcendental_iff.mp S.htr) Q h)
  have hW : S.evXY W ≠ 0 := by
    rw [← hWQ]; exact mul_ne_zero (fun h ↦ hz (Subtype.ext h)) hxQ
  set R := S.normW W S.F.natDegree with hR
  -- the order of `z` along a branch, from `W` and `Q`
  have hrel : ∀ (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (r : LaurentSeries K)
      (hr : (S.F.map g).eval r = 0),
      ((W.map g).eval r).order = (S.embG g hg r hr z).order + (g Q).order := fun g hg r hr ↦ by
    have he := S.eval_W_branch g hg r hr z W Q hWQ
    have h1 : S.embG g hg r hr z ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hz
    have h2 : g Q ≠ 0 := (map_ne_zero_iff _ hg).mpr hQ
    rw [he, HahnSeries.order_mul h1 h2]
  -- the fibre sums
  have hfib : ∀ (b : K) (M : ℕ) (hM : 0 < M) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub M b) = (l.map fun r ↦ X - Polynomial.C r).prod),
      (l.map fun r ↦ ((W.map (branchSub M b)).eval r).order).sum =
        M * ((R.map (algebraMap C K)).rootMultiplicity b : ℤ) := fun b M hM l hl ↦ by
    rw [S.sum_order_eval W hW (by rw [hn] at hWn ⊢; exact hWn) _ (branchSub_injective M hM b) l hl]
    have hR0 := S.normW_ne_zero W S.F.natDegree hWn.le hW _ (branchSub_injective M hM b) l hl
    rw [order_branchSub M hM b R hR0]; push_cast; ring
  have hQo : ∀ (b : K) (M : ℕ) (hM : 0 < M),
      (branchSub M b Q).order = M * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ) :=
    fun b M hM ↦ by rw [order_branchSub M hM b Q hQ]; push_cast; ring
  -- outside the `α_j`: `mult R = n mult Q`
  have hout : ∀ b : K, b ∉ Set.range α → ((R.map (algebraMap C K)).rootMultiplicity b : ℤ) =
      n * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ) := by
    intro b hb
    obtain ⟨M, hM, l0, hl0, hs0⟩ := S.branches_at b
    set l' := l0.map (HahnSeries.ofPowerSeries ℤ K) with hl'
    have hs' : S.F.map (branchSub M b) = (l'.map fun r ↦ X - Polynomial.C r).prod := by
      rw [hs0, hl', List.map_map]; rfl
    have h1 := hfib b M (Nat.pos_of_ne_zero hM) l' hs'
    have hlen : l'.length = n := by rw [hl', List.length_map, hl0, hn]
    rw [list_sum_const l' _ ((M : ℤ) * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ))
      (fun r hr' ↦ by
        rw [hrel _ (branchSub_injective M (Nat.pos_of_ne_zero hM) b) r (S.root_of_mem hs' hr'),
          hother b hb M hM l' hs' r hr', zero_add, hQo b M (Nat.pos_of_ne_zero hM)]), hlen] at h1
    have hMp : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
    have : (M : ℤ) * (n * ((Q.map (algebraMap C K)).rootMultiplicity b : ℤ)) =
        M * ((R.map (algebraMap C K)).rootMultiplicity b : ℤ) := by rw [← h1]; ring
    exact (mul_left_cancel₀ hMp.ne' this).symm
  -- at the `α_j`
  have hat : ∀ j, ((R.map (algebraMap C K)).rootMultiplicity (α j) : ℤ) -
      n * ((Q.map (algebraMap C K)).rootMultiplicity (α j) : ℤ) = g j := by
    intro j
    have h1 := hfib (α j) (Nf j) (hNf j) (lf j) (hlf j)
    have h2 : (lf j).map (fun r ↦ ((W.map (branchSub (Nf j) (α j))).eval r).order) =
        (lf j).map (fun r ↦ o j r + (Nf j : ℤ) * ((Q.map (algebraMap C K)).rootMultiplicity (α j) : ℤ)) :=
      List.map_congr_left fun r hr ↦ by
        rw [hrel _ (branchSub_injective _ (hNf j) _) r (S.root_of_mem (hlf j) hr), ho j r hr,
          hQo (α j) (Nf j) (hNf j)]
    rw [h2, List.sum_map_add, hg j, list_sum_const (lf j) _ _ (fun _ _ ↦ rfl),
      S.length_of_split (hlf j), hn] at h1
    have hNp : (0 : ℤ) < Nf j := by exact_mod_cast hNf j
    have : (Nf j : ℤ) * (((R.map (algebraMap C K)).rootMultiplicity (α j) : ℤ) -
        n * ((Q.map (algebraMap C K)).rootMultiplicity (α j) : ℤ)) = Nf j * g j := by
      linear_combination -h1
    exact mul_left_cancel₀ hNp.ne' this
  -- the degrees
  have hR0 : R ≠ 0 := S.normW_ne_zero W S.F.natDegree hWn.le hW _
    (infSub_injective N (Nat.pos_of_ne_zero hN)) l hl
  set U : Finset K := (R.map (algebraMap C K)).roots.toFinset ∪
    (Q.map (algebraMap C K)).roots.toFinset ∪ Finset.univ.image α with hU
  have hdegR := natDegree_eq_sum_mult R hR0 U (by intro a ha; simp [hU, ha])
  have hdegQ := natDegree_eq_sum_mult Q hQ U (by intro a ha; simp [hU, ha])
  have hdeg : (R.natDegree : ℤ) - n * Q.natDegree = ∑ j, g j := by
    rw [hdegR, hdegQ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := (R.map (algebraMap C K)).roots.toFinset ∪
      (Q.map (algebraMap C K)).roots.toFinset)) (fun a _ ha ↦ by
        rw [hout a (fun ⟨j, hj⟩ ↦ ha (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)), sub_self])]
    rw [Finset.sum_image (fun i _ j _ h ↦ hα h)]
    exact Finset.sum_congr rfl fun j _ ↦ hat j
  -- infinity: all branches have the same order
  have hNp := Nat.pos_of_ne_zero hN
  have hinf := hfib
  have hsumInf : (l.map fun r ↦ ((W.map (infSub N)).eval r).order).sum = -((N : ℤ) * R.natDegree) := by
    rw [S.sum_order_eval W hW (by rw [hn] at hWn ⊢; exact hWn) _ (infSub_injective N hNp) l hl,
      order_infSub N hNp R hR0]
  have hWn' : W.natDegree < n := by rw [← hn]; exact hWn
  have hW0 : W ≠ 0 := fun h ↦ hW (by rw [h]; simp [CurveData.evXY])
  have hconst : ∀ r' ∈ l, ((W.map (infSub N)).eval r').order = ((W.map (infSub N)).eval r).order := by
    intro r' hr'
    have h1 := (eval_order_inf S.F S.monic n d N hn hn0 hNp ha0 hd hw hcop r' (S.root_of_mem hl hr')
      W hW0 hWn').2
    have h2 := (eval_order_inf S.F S.monic n d N hn hn0 hNp ha0 hd hw hcop r (S.root_of_mem hl hr)
      W hW0 hWn').2
    have hnp : (0 : ℤ) < n := by exact_mod_cast hn0
    exact mul_left_cancel₀ hnp.ne' (h1.trans h2.symm)
  rw [list_sum_const l _ _ hconst, S.length_of_split hl, hn] at hsumInf
  have h3 := hrel (infSub N) (infSub_injective N hNp) r (S.root_of_mem hl hr)
  rw [order_infSub N hNp Q hQ] at h3
  rw [← hdeg]
  push_cast at h3 hsumInf ⊢
  linear_combination (n : ℤ) * h3.symm + hsumInf

end CurveData

end Inf

section PoleN

variable {K : Type*} [Field K]

/-- **A pole of order `N`**: `e/(Tᴺ h)` with `h(0) ≠ 0` has no coefficient below `−N`, and
`(e/(Tᴺ h))₋ₙ = e(0)/h(0)`. -/
lemma laurent_pole_N (e h : PowerSeries K) (N : ℕ) (hh : PowerSeries.constantCoeff h ≠ 0) :
    (∀ i : ℤ, i < -(N : ℤ) → (HahnSeries.ofPowerSeries ℤ K e /
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.X ^ N * h)).coeff i = 0) ∧
    (HahnSeries.ofPowerSeries ℤ K e / HahnSeries.ofPowerSeries ℤ K (PowerSeries.X ^ N * h)).coeff
      (-(N : ℤ)) = PowerSeries.constantCoeff e / PowerSeries.constantCoeff h := by
  have hinv : HahnSeries.ofPowerSeries ℤ K h * HahnSeries.ofPowerSeries ℤ K h⁻¹ = 1 := by
    rw [← map_mul, PowerSeries.mul_inv_cancel _ hh, map_one]
  have hq : HahnSeries.ofPowerSeries ℤ K e / HahnSeries.ofPowerSeries ℤ K (PowerSeries.X ^ N * h) =
      HahnSeries.ofPowerSeries ℤ K (e * h⁻¹) * HahnSeries.single (-(N : ℤ)) (1 : K) := by
    rw [map_mul, map_mul, map_pow, HahnSeries.ofPowerSeries_X, div_eq_mul_inv, mul_inv,
      eq_inv_of_mul_eq_one_right hinv]
    have hs : ((HahnSeries.single (1 : ℤ) (1 : K)) ^ N)⁻¹ = HahnSeries.single (-(N : ℤ)) 1 := by
      rw [inv_eq_of_mul_eq_one_right]
      rw [HahnSeries.single_pow, HahnSeries.single_mul_single]; simp
    rw [hs]; ring
  rw [hq]
  have hcoef : ∀ i : ℤ, (HahnSeries.ofPowerSeries ℤ K (e * h⁻¹) *
      HahnSeries.single (-(N : ℤ)) (1 : K)).coeff i =
        (HahnSeries.ofPowerSeries ℤ K (e * h⁻¹)).coeff (i + N) := fun i ↦ by
    have := HahnSeries.coeff_mul_single_add (r := (1 : K))
      (x := HahnSeries.ofPowerSeries ℤ K (e * h⁻¹)) (a := i + N) (b := -(N : ℤ))
    rw [show i + N + -(N : ℤ) = i by ring, mul_one] at this
    exact this
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [hcoef, HahnSeries.ofPowerSeries_apply]
    refine HahnSeries.embDomain_notin_range ?_
    rintro ⟨n, hn⟩
    have : ((n : ℕ) : ℤ) = i + N := hn
    omega
  · rw [hcoef, show -(N : ℤ) + N = ((0 : ℕ) : ℤ) by norm_num, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_inv,
      div_eq_mul_inv]

end PoleN

section PoleNCurve

open Differential

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **The expansion of `B(x, y)/D(x)` at a simple root `α` of `D`** along a branch
`x = α + Tᴺ`, `y = Y(T)`: no term below `T⁻ᴺ`, and `(B/D)₋ₙ = B(α, Y(0))/D′(α)`. -/
lemma embG_pole_N (B : C[X][X]) (D : C[X]) (α : C) (hD0 : D.eval α = 0)
    (hD1 : (derivative D).eval α ≠ 0) (N : ℕ) (hN : 0 < N) (Yp : PowerSeries K)
    (hY : (S.F.map (branchSub N (algebraMap C K α))).eval (HahnSeries.ofPowerSeries ℤ K Yp) = 0)
    (hf : S.evXY B / aeval S.x D ∈ C⟮S.x⟯⟮S.y⟯) :
    (∀ i : ℤ, i < -(N : ℤ) → (S.embG (branchSub N (algebraMap C K α)) (branchSub_injective N hN _)
      _ hY ⟨_, hf⟩).coeff i = 0) ∧
    (S.embG (branchSub N (algebraMap C K α)) (branchSub_injective N hN _) _ hY ⟨_, hf⟩).coeff
      (-(N : ℤ)) = ((B.map (Polynomial.mapRingHom (algebraMap C K))).map
        (Polynomial.evalRingHom (algebraMap C K α))).eval (PowerSeries.constantCoeff Yp) /
          algebraMap C K ((derivative D).eval α) := by
  set a := algebraMap C K α with ha
  set g' : C[X] →+* PowerSeries K := (Polynomial.coeToPowerSeries.ringHom (R := K)).comp
    ((Polynomial.compRingHom (Polynomial.C a + X ^ N)).comp
      (Polynomial.mapRingHom (algebraMap C K))) with hg'
  have hg : branchSub (C := C) (K := K) N a = (HahnSeries.ofPowerSeries ℤ K).comp g' := rfl
  have hfe : (⟨_, hf⟩ : C⟮S.x⟯⟮S.y⟯) = S.evT B / ⟨aeval S.x D, S.aeval_mem D⟩ :=
    Subtype.ext (by rw [IntermediateField.coe_div, S.coe_evT])
  rw [hfe, map_div₀, S.embG_evT, S.embG_polyX, hg, RingHom.comp_apply, eval_map]
  have hE : Polynomial.eval₂ ((HahnSeries.ofPowerSeries ℤ K).comp g')
      (HahnSeries.ofPowerSeries ℤ K Yp) B =
      HahnSeries.ofPowerSeries ℤ K (Polynomial.eval₂ g' Yp B) :=
    (Polynomial.hom_eval₂ B g' (HahnSeries.ofPowerSeries ℤ K) Yp).symm
  erw [hE]
  -- `g′ P = taylor(P)(Tᴺ)`
  have hgD : ∀ P : C[X], g' P = (((Polynomial.taylor a (P.map (algebraMap C K))).comp
      (X ^ N) : K[X]) : PowerSeries K) := fun P ↦ by
    rw [hg', RingHom.comp_apply, RingHom.comp_apply, Polynomial.taylor_apply, Polynomial.comp_assoc,
      Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, add_comm]
    rfl
  -- the denominator `D(a + Tᴺ) = Tᴺ h`
  have hX : X ∣ Polynomial.taylor a (D.map (algebraMap C K)) := by
    rw [Polynomial.X_dvd_iff, Polynomial.taylor_coeff_zero, eval_map, ha, Polynomial.eval₂_at_apply,
      hD0, map_zero]
  obtain ⟨Q, hQ⟩ := hX
  have hgDe : g' D = PowerSeries.X ^ N * ((Q.comp (X ^ N) : K[X]) : PowerSeries K) := by
    rw [hgD, hQ, Polynomial.mul_comp, Polynomial.X_comp, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X]
  have hQ0 : Q.coeff 0 = algebraMap C K ((derivative D).eval α) := by
    have := congrArg (fun p : K[X] ↦ p.coeff 1) hQ
    simp only [Polynomial.taylor_coeff_one, Polynomial.coeff_X_mul] at this
    rw [← this, Polynomial.derivative_map, eval_map, ha, Polynomial.eval₂_at_apply]
  have hh : PowerSeries.constantCoeff ((Q.comp (X ^ N) : K[X]) : PowerSeries K) =
      algebraMap C K ((derivative D).eval α) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, eval_pow, eval_X,
      zero_pow hN.ne', ← Polynomial.coeff_zero_eq_eval_zero, hQ0]
  have hh0 : PowerSeries.constantCoeff ((Q.comp (X ^ N) : K[X]) : PowerSeries K) ≠ 0 := by
    rw [hh]; exact (map_ne_zero_iff _ (algebraMap C K).injective).mpr hD1
  rw [hgDe]
  obtain ⟨hb, hc⟩ := laurent_pole_N (Polynomial.eval₂ g' Yp B) _ N hh0
  refine ⟨hb, ?_⟩
  rw [hc, hh]
  congr 1
  -- the constant term of the numerator
  have hcc : (PowerSeries.constantCoeff (R := K)).comp g' =
      (Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (algebraMap C K)) := by
    refine RingHom.ext fun P ↦ ?_
    rw [RingHom.comp_apply, hgD, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, eval_pow,
      eval_X, zero_pow hN.ne', ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.taylor_coeff_zero]
    rfl
  rw [Polynomial.hom_eval₂, hcc, eval_map, Polynomial.eval₂_map]

end CurveData

end PoleNCurve

end Curves

lemma list_sum_cast_mul {β : Type*} (l : List β) (f : β → ℕ) (M : ℕ) :
    (l.map fun r ↦ ((M * f r : ℕ) : ℤ)).sum = (M : ℤ) * (((l.map f).sum : ℕ) : ℤ) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring

namespace Curves

namespace CurveData

open Differential

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : CurveData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **A Liouville form makes the residue divisor torsion, at any places**: from
`f = v′ + ∑ dⱼ wⱼ′/wⱼ` with residues `ρⱼ(r)` along the roots `r` of `F(αⱼ + T^{Nⱼ}, Y)`,
residue-free elsewhere at finite places, and `Γⱼ(r) = s Λ(ρⱼ(r)) + eⱼ Nⱼ`
(`∑_r Γⱼ(r) = Nⱼ gⱼ`, `∑ gⱼ = c n`), some function `γ ≠ 0` has `div γ ≥ M Γ − M c ∞ₓ`
(`DivGE`, single place at infinity). -/
theorem divGE_of_liouville (hnd : ∀ a : K, a′ ≠ (ω.map (algebraMap C K)).eval a)
    (n dd : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = dd)
    (hw' : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < dd * (n - i))
    (hcop : Nat.Coprime n dd) (k : ℕ) (d : ℕ → C) (w : ℕ → L)
    (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    {J : Type*} [Fintype J] (α : J → C) (hα : Function.Injective α) (Nf : J → ℕ)
    (hNf : ∀ j, 0 < Nf j) (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (Nf j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (ρ : J → LaurentSeries K → C)
    (hbelow : ∀ j r (hr : r ∈ lf j) (i : ℤ), i < -(Nf j : ℤ) →
      (S.embG (branchSub (Nf j) (algebraMap C K (α j))) (branchSub_injective _ (hNf j) _) r
        (S.root_of_mem (hlf j) hr) ⟨f, hf⟩).coeff i = 0)
    (hres : ∀ j r (hr : r ∈ lf j), (S.embG (branchSub (Nf j) (algebraMap C K (α j)))
      (branchSub_injective _ (hNf j) _) r (S.root_of_mem (hlf j) hr) ⟨f, hf⟩).coeff (-(Nf j : ℤ)) =
        (sBranch ω (algebraMap C K (α j)) (Nf j)).coeff (1 - (Nf j : ℤ)) * algebraMap C K (ρ j r))
    (hfree : ∀ b : K, b ∉ Set.range (fun j ↦ algebraMap C K (α j)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l) (i : ℤ), i < 1 - (N : ℤ) →
      (S.embG (branchSub N b) (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r
        (S.root_of_mem hl hr) ⟨f, hf⟩).coeff i = 0)
    (Λ : C →ₗ[ℚ] ℚ) (sc : ℕ) (eS : J → ℤ) (Γ : J → LaurentSeries K → ℕ) (cdeg : ℕ)
    (gdeg : J → ℕ)
    (hΓ : ∀ j r, r ∈ lf j → (Γ j r : ℚ) = sc * Λ (ρ j r) + eS j * Nf j)
    (hgs : ∀ j, ((lf j).map (Γ j)).sum = Nf j * gdeg j)
    (hsum : ∑ j, gdeg j = cdeg * n) :
    ∃ M : ℕ, 0 < M ∧ ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
      S.DivGE (K := K) α Nf hNf lf hlf (fun j r ↦ M * Γ j r) (M * cdeg) γ := by
  classical
  -- the integer exponents
  set M : ℕ := ∏ j ∈ Finset.range k, (Λ (d j)).den with hM
  have hMpos : 0 < M := Finset.prod_pos fun j _ ↦ (Λ (d j)).den_pos
  set e : ℕ → ℤ := fun j ↦ (Λ (d j)).num * ((M / (Λ (d j)).den : ℕ) : ℤ) with he
  have he' : ∀ j < k, (e j : ℚ) = M * Λ (d j) := fun j hj ↦ by
    have hdv : (Λ (d j)).den ∣ M := Finset.dvd_prod_of_mem (fun j ↦ (Λ (d j)).den)
      (Finset.mem_range.mpr hj)
    have := rat_mul_den_int (Λ (d j)) M hdv
    rw [he]; dsimp only
    rw [this, mul_comm]
  -- `γ₀ = ∏ wⱼ^{eⱼ}`
  have hγ0m : (∏ j : Fin k, (w j) ^ (e j)) ∈ C⟮S.x⟯⟮S.y⟯ :=
    prod_mem fun j _ ↦ zpow_mem (hw j j.2).1 _
  have hγ00 : (∏ j : Fin k, (w j) ^ (e j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (hw j j.2).2
  set γ0 : C⟮S.x⟯⟮S.y⟯ := ⟨_, hγ0m⟩ with hγ0
  set γ : C⟮S.x⟯⟮S.y⟯ := γ0 ^ sc * ∏ j, (S.polyF (X - Polynomial.C (α j))) ^ ((M : ℤ) * eS j)
    with hγ
  have hxs0 : ∀ j, S.polyF (X - Polynomial.C (α j)) ≠ 0 := fun j h ↦ by
    have := congrArg Subtype.val h
    rw [S.coe_polyF] at this
    exact (X_sub_C_ne_zero (α j)) ((transcendental_iff.mp S.htr) _ this)
  have hγ0ne : γ0 ≠ 0 := fun h ↦ hγ00 (congrArg Subtype.val h)
  have hγne : γ ≠ 0 := mul_ne_zero (pow_ne_zero _ hγ0ne)
    (Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (hxs0 j))
  -- the order of `γ` along a finite branch
  have hordγ : ∀ (b : K) (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
      (hr : (S.F.map (branchSub N b)).eval r = 0),
      (S.embG (branchSub N b) (branchSub_injective N hN b) r hr γ).order =
        sc * (S.embG (branchSub N b) (branchSub_injective N hN b) r hr γ0).order +
          ∑ j, (M : ℤ) * eS j * (if b = algebraMap C K (α j) then (N : ℤ) else 0) := by
    intro b N hN r hr
    set φ := S.embG (branchSub N b) (branchSub_injective N hN b) r hr
    have h0 : φ γ0 ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr hγ0ne
    have h1 : ∀ j, φ (S.polyF (X - Polynomial.C (α j))) ≠ 0 := fun j ↦
      (map_ne_zero_iff _ φ.injective).mpr (hxs0 j)
    rw [hγ, map_mul, map_pow, map_prod]
    simp only [map_zpow₀]
    rw [HahnSeries.order_mul (pow_ne_zero _ h0) (Finset.prod_ne_zero_iff.mpr fun j _ ↦
      zpow_ne_zero _ (h1 j)), HahnSeries.order_pow, nsmul_eq_mul,
      (order_prod_zpow_nk Finset.univ _ (fun j _ ↦ h1 j) _).2]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [S.order_xsub (α j) b N hN r hr]
  -- the orders of `γ₀`
  have hγ0α : ∀ jj r (hr : r ∈ lf jj), ((S.embG (branchSub (Nf jj) (algebraMap C K (α jj)))
      (branchSub_injective _ (hNf jj) _) r (S.root_of_mem (hlf jj) hr) γ0).order : ℚ) =
        M * Λ (ρ jj r) := fun jj r hr ↦
    S.order_logProd ω hx hK k d w hw v f hv hf heq _ (hnd _) (Nf jj) (hNf jj) r _ (ρ jj r)
      (hbelow jj r hr) (hres jj r hr) Λ M e he' hγ0m
  have hγ0o : ∀ b : K, b ∉ Set.range (fun j ↦ algebraMap C K (α j)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), (S.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S.root_of_mem hl hr) γ0).order = 0 := by
    intro b hb N hN l hl r hr
    have h := S.order_logProd ω hx hK k d w hw v f hv hf heq b (hnd b) N (Nat.pos_of_ne_zero hN) r
      (S.root_of_mem hl hr) 0 (fun i hi ↦ hfree b hb N hN l hl r hr i (by omega))
      (by rw [map_zero, mul_zero]; exact hfree b hb N hN l hl r hr _ (by omega)) Λ M e he' hγ0m
    rw [map_zero, mul_zero] at h
    exact_mod_cast h
  -- the orders of `γ`
  have hαK : Function.Injective (fun j ↦ algebraMap C K (α j)) :=
    fun i j h ↦ hα ((algebraMap C K).injective h)
  have hγα : ∀ j r (hr : r ∈ lf j), (S.embG (branchSub (Nf j) (algebraMap C K (α j)))
      (branchSub_injective _ (hNf j) _) r (S.root_of_mem (hlf j) hr) γ).order = M * Γ j r := by
    intro j r hr
    rw [hordγ _ (Nf j) (hNf j), Finset.sum_eq_single j (fun j' _ hj' ↦ by
      rw [if_neg (fun h ↦ hj' (hαK h.symm)), mul_zero]) (by simp), if_pos rfl]
    have h1 := hγ0α j r hr
    have h2 := hΓ j r hr
    have : ((sc * (S.embG (branchSub (Nf j) (algebraMap C K (α j)))
        (branchSub_injective _ (hNf j) _) r (S.root_of_mem (hlf j) hr) γ0).order +
          (M : ℤ) * eS j * (Nf j : ℤ) : ℤ) : ℚ) = ((M * Γ j r : ℕ) : ℚ) := by
      push_cast
      rw [h1, h2]; ring
    exact_mod_cast this
  have hγo : ∀ b : K, b ∉ Set.range (fun j ↦ algebraMap C K (α j)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), (S.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S.root_of_mem hl hr) γ).order = 0 := by
    intro b hb N hN l hl r hr
    rw [hordγ b N (Nat.pos_of_ne_zero hN), hγ0o b hb N hN l hl r hr, mul_zero, zero_add]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [if_neg (fun h ↦ hb ⟨j, h.symm⟩), mul_zero]
  refine ⟨M, hMpos, γ, hγne, ⟨fun j r hr ↦ ?_, fun b hb N hN l hl r hr ↦ ?_,
    fun N hN l hl r hr ↦ ?_⟩⟩
  · rw [hγα j r hr]; push_cast; exact le_refl _
  · rw [hγo b hb N hN l hl r hr]
  · have h := S.order_inf_of_places n dd hn hn0 ha0 hd hw' hcop γ hγne
      (fun j ↦ algebraMap C K (α j)) hαK Nf hNf lf hlf (fun j r ↦ ((M * Γ j r : ℕ) : ℤ))
      (fun j r hr ↦ hγα j r hr) (fun j ↦ ((M * gdeg j : ℕ) : ℤ)) (fun j ↦ by
        rw [list_sum_cast_mul, hgs j]; push_cast; ring)
      hγo N hN l hl r hr
    have hs : (∑ j, ((M * gdeg j : ℕ) : ℤ)) = M * cdeg * n := by
      push_cast
      rw [← Finset.mul_sum, show (∑ j, (gdeg j : ℤ)) = ((∑ j, gdeg j : ℕ) : ℤ) by push_cast; rfl,
        hsum]
      push_cast; ring
    rw [hs] at h
    have hnp : (0 : ℤ) < n := by exact_mod_cast hn0
    have h2 : (n : ℤ) * (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
        (S.root_of_mem hl hr) γ).order = n * (-((N * (M * cdeg) : ℕ) : ℤ)) := by
      rw [h]; push_cast; ring
    rw [mul_left_cancel₀ hnp.ne' h2]

end CurveData

end Curves
