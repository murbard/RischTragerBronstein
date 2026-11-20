import RischTragerBronstein.Curves.ProcRFSound5

/-!
# The residue-free procedure: the two core implications (over the constants of a Liouville
extension)

On a curve over a field of constants `C` (all constants of `L` in `C`):

* `rows_of_liouville` (**necessity**): if `f = v′ + ∑ dᵢ wᵢ′/wᵢ` with `v, wᵢ` on the curve, then
  `v` lies in the ansatz space (pole bounds from `liouville_local`, `ansatz`), so the linear system
  has a solution over `C`;
* `eq_deriv_of_rows` (**sufficiency**): if the rows are solved by `c` and all computed residues
  vanish, then any such `f` equals `(∑ c_b b)′` (second kind + regularity).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

lemma lowerBd_of_derivation {K : Type*} [Field K] [CharZero K] (z : LaurentSeries K)
    (h : LowerBd (LaurentSeries.derivation z) (-1)) : LowerBd z 0 := by
  intro k hk
  have h1 := h (k - 1) (by omega)
  rw [coeff_derivation, sub_add_cancel] at h1
  have hk0 : ((k : ℤ) : K) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  exact (mul_eq_zero.mp h1).resolve_left hk0

section Core

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- Rewriting a Liouville form with constant coefficients in `C`. -/
lemma liouville_C (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L)) (f v : L)
    {ι : Type*} (sI : Finset ι) (d w : ι → L) (hd : ∀ i ∈ sI, (d i)′ = 0)
    (hw : ∀ i ∈ sI, w i ≠ 0 ∧ w i ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ sI, d i * logDeriv (w i)) :
    ∃ (dc : ι → C) (u : ι → L), (∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) ∧ (∀ i, u i ≠ 0) ∧
      f = v′ + ∑ i ∈ sI, algebraMap C L (dc i) * ((u i)′ / u i) := by
  classical
  have hdC : ∀ i, ∃ c : C, i ∈ sI → d i = algebraMap C L c := fun i ↦ by
    by_cases hi : i ∈ sI
    · obtain ⟨c, hc⟩ := hconst (d i) (hd i hi)
      exact ⟨c, fun _ ↦ hc.symm⟩
    · exact ⟨0, fun h ↦ absurd h hi⟩
  choose dc hdc using hdC
  refine ⟨dc, fun i ↦ if i ∈ sI then w i else 1, fun i ↦ ?_, fun i ↦ ?_, ?_⟩
  · by_cases hi : i ∈ sI
    · simp only [hi, if_true]; exact (hw i hi).2
    · simp only [hi, if_false]; exact one_mem _
  · by_cases hi : i ∈ sI
    · simp only [hi, if_true]; exact (hw i hi).1
    · simp only [hi, if_false]; exact one_ne_zero
  · rw [heq]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [hi, if_true, hdc i hi]
    rfl

variable {K : Type*} [Field K] [CharZero K] [Algebra C K]

lemma hX_fin (N : ℕ) (hN : 0 < N) (a : K) :
    LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K)) ≠ 0 := by
  rw [SuperData.derivation_branchX N hN a]
  exact HahnSeries.single_ne_zero (by exact_mod_cast hN.ne')

lemma hX_inf (N : ℕ) (hN : 0 < N) :
    LaurentSeries.derivation (single (-(N : ℤ)) (1 : K)) ≠ 0 := by
  rw [SuperData.derivation_infX N]
  refine HahnSeries.single_ne_zero ?_
  simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
  exact hN.ne'

variable {P : CurveProb F} {ψ₀ : F →+* C}

omit [Differential C] [Differential L] [DifferentialAlgebra C L] [CharZero K] in
lemma A_bound (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (i : ℕ)
    (hi : ((toB P.A).map (mapRingHom ψ₀)).coeff i ≠ 0) :
    (((toB P.A).map (mapRingHom ψ₀)).coeff i).natDegree + P.k * i ≤ P.DA := by
  rw [coeff_map, coeff_toB] at hi ⊢
  have hl : i < P.A.length := by
    by_contra h
    rw [List.getD_eq_default _ _ (by omega), toPoly_nil] at hi
    exact hi (map_zero _)
  have h1 := hV.okA i hl
  have h2 := natDegree_toPoly_le_length (P.A.getD i [])
  have h3 : 0 < (P.A.getD i []).length :=
    List.length_pos_iff.mpr fun h ↦ hi (by rw [h, toPoly_nil, map_zero])
  rw [coe_mapRingHom, natDegree_map_eq_of_injective ψ₀.injective]
  simp only [zero_add] at h1
  omega

/-- **Necessity**: an elementary integral puts `v` in the ansatz space, so the rows are solvable
over `C`. -/
theorem rows_of_liouville [IsAlgClosed K] (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts)
    (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) {ι : Type*} (sI : Finset ι) (d w : ι → L)
    (hd : ∀ i ∈ sI, (d i)′ = 0) (hw : ∀ i ∈ sI, w i ≠ 0 ∧ w i ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : (S.fE P ψ₀ : L) = v′ + ∑ i ∈ sI, d i * logDeriv (w i)) :
    ∃ cv : ℕ → C, ∀ r ∈ P.allRows,
      ∑ b ∈ Finset.range P.basisIdx.length, cv b * ψ₀ (r.1.getD b 0) = ψ₀ r.2 := by
  obtain ⟨dc, u, hu, hu0, heq'⟩ := S.liouville_C hconst _ v sI d w hd hw heq
  have hf := S.fE_spec P ψ₀ hV
  set D' := (toPoly P.D).map ψ₀ with hD'
  have hD'0 : D' ≠ 0 := by rw [hD', Ne, Polynomial.map_eq_zero_iff ψ₀.injective]; exact hV.D0
  have hdegD : D'.natDegree = degT P.D := by
    rw [hD', natDegree_map_eq_of_injective ψ₀.injective, degT_eq]
  -- the local statements along any branch
  have locF := fun (a : K) (N : ℕ) (hN : 0 < N) (Y : LaurentSeries K)
      (hY : (S.F.map (branchSub N a)).eval Y = 0) ↦
    S.liouville_local _ (hX_fin N hN a) (branchSub N a) (branchSub_injective N hN a)
      (fun P ↦ by rw [SuperData.branchSub_eq_subst]) hC hx Y hY sI dc u hu hu0 v _ hv
      (S.fE P ψ₀).2 heq'
  have locI := fun (N : ℕ) (hN : 0 < N) (Y : LaurentSeries K)
      (hY : (S.F.map (infSub N)).eval Y = 0) ↦
    S.liouville_local _ (hX_inf N hN) (infSub N) (infSub_injective N hN)
      (fun P ↦ by rw [SuperData.infSub_eq_subst]) hC hx Y hY sI dc u hu hu0 v _ hv
      (S.fE P ψ₀).2 heq'
  -- pole bounds for `v`
  have hfin : S.PoleBoundFin K ⟨v, hv⟩ D' := by
    intro a N hN r hsplit k
    have hN' := Nat.pos_of_ne_zero hN
    refine (locF a N hN' (r k) (S.root_of_split _ r hsplit k)).2 _ ?_
    have h1 := (S.lowerBd_fin N hN' a (r k) (S.root_of_split _ r hsplit k) (S.fE P ψ₀) _ D' hD'0
      hf).mul (lowerBd_single ((N : ℤ) - 1) (N : K))
    rw [SuperData.derivation_branchX N hN' a]
    exact h1.mono (by push_cast; omega)
  have hinf : S.PoleBoundInf K ⟨v, hv⟩ P.Binf := by
    intro N hN r hsplit k
    have hN' := Nat.pos_of_ne_zero hN
    refine (locI N hN' (r k) (S.root_of_split _ r hsplit k)).2 _ ?_
    have h1 := (S.lowerBd_inf N hN' P.k (S.coeff_F_le hSF hV) (r k) (S.root_of_split _ r hsplit k)
      (S.fE P ψ₀) _ D' hD'0 hf P.DA (S.A_bound hSF hV)).mul
        (lowerBd_single (-(N : ℤ) - 1) (-(N : K)))
    rw [SuperData.derivation_infX N]
    refine h1.mono ?_
    rw [hdegD]
    have hB : N * (P.DA + 1) ≤ N * P.Binf + N * degT P.D := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by simp only [CurveProb.Binf]; omega)
    have hB' : ((N * (P.DA + 1) : ℕ) : ℤ) ≤ ((N * P.Binf : ℕ) : ℤ) + ((N * degT P.D : ℕ) : ℤ) := by
      exact_mod_cast hB
    push_cast at hB' ⊢
    linarith
  -- the ansatz
  obtain ⟨W, hWn, hWc, hWe⟩ := S.ansatz (K := K) ⟨v, hv⟩ D' hD'0 P.Binf hfin hinf
  rw [S.discR_mul_D hSF hV] at hWe
  have hWc' : ∀ j, (W.coeff j).natDegree ≤ P.E := fun j ↦ by
    refine (hWc j).trans ?_
    rw [hdegD, S.natDegree_F_eq P ψ₀ hSF hV, CurveProb.E]
    have := Nat.mul_le_mul_left ((P.n - 1) * (P.n - 1) + (P.n - 1)) (S.degB_le hSF hV)
    omega
  have hvs := S.eq_lcomb hSF hV ⟨v, hv⟩ W hWn hWc' hWe
  refine ⟨fun b ↦ (W.coeff (P.basisIdx.getD b (0, 0)).1).coeff (P.basisIdx.getD b (0, 0)).2,
    S.rows_of_simple (K := K) P ψ₀ hSF hV (S.fE P ψ₀) hf (S.bE P ψ₀) (S.bE_spec P ψ₀ hV) _
      (fun a N hN Y hY ↦ ?_) (fun N hN Y hY ↦ ?_)⟩
  · rw [← hvs]; exact (locF a N hN Y hY).1
  · rw [← hvs]; exact (locI N hN Y hY).1

/-- **Sufficiency**: solved rows and vanishing residues force `f = (∑ c_b b)′`. -/
theorem eq_deriv_of_rows [IsAlgClosed K] (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cv : ℕ → C)
    (hrows : ∀ r ∈ P.allRows,
      ∑ b ∈ Finset.range P.basisIdx.length, cv b * ψ₀ (r.1.getD b 0) = ψ₀ r.2)
    (hres : ∀ r ∈ P.allRes, r = 0)
    (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) {ι : Type*} (sI : Finset ι) (d w : ι → L)
    (hd : ∀ i ∈ sI, (d i)′ = 0) (hw : ∀ i ∈ sI, w i ≠ 0 ∧ w i ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : (S.fE P ψ₀ : L) = v′ + ∑ i ∈ sI, d i * logDeriv (w i)) :
    (S.fE P ψ₀ : L) = ((∑ b ∈ Finset.range P.basisIdx.length,
      S.cst (cv b) * S.bE P ψ₀ (P.basisIdx.getD b (0, 0)) : C⟮S.x⟯⟮S.y⟯) : L)′ := by
  classical
  have hf := S.fE_spec P ψ₀ hV
  set vv : C⟮S.x⟯⟮S.y⟯ := ∑ b ∈ Finset.range P.basisIdx.length,
      S.cst (cv b) * S.bE P ψ₀ (P.basisIdx.getD b (0, 0)) with hvv
  -- second kind: `f = v′`
  have hfv : (S.fE P ψ₀ : L) = v′ :=
    S.curve_second_kind (K := K) hC hx hconst _ v (S.fE P ψ₀).2 hv sI d w hd hw heq
      (fun a N hN l hl r hr ↦ S.resFin_all P ψ₀ hSF hV (S.fE P ψ₀) hf hres a N hN l hl r hr)
      (fun N hN l hl r hr ↦ S.resInf_all P ψ₀ hSF hV (S.fE P ψ₀) hf hres N hN l hl r hr)
  have heq0 : (S.fE P ψ₀ : L) = v′ + ∑ i ∈ (∅ : Finset Unit),
      algebraMap C L ((fun _ ↦ 0) i) * (((fun _ ↦ (1 : L)) i)′ / (fun _ ↦ (1 : L)) i) := by
    rw [Finset.sum_empty, add_zero]; exact hfv
  -- `v − vv` has no poles
  have hreg : ∀ (Xh : LaurentSeries K) (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
      (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0),
      LaurentSeries.derivation Xh ≠ 0 → (∀ Q, g Q = substHom Xh Q) →
      LowerBd (S.embG g hg Y hY (S.fE P ψ₀) * LaurentSeries.derivation Xh -
        LaurentSeries.derivation (S.embG g hg Y hY vv)) (-1) →
      0 ≤ (S.embG g hg Y hY (⟨v, hv⟩ - vv)).order := by
    intro Xh g hg Y hY hX hgX hlb
    have hexp := S.expand_liouville Xh hX g hg hgX hC hx Y hY ∅ (fun _ ↦ 0) (fun _ ↦ (1 : L))
      (fun _ ↦ one_mem _) (fun _ ↦ one_ne_zero) v _ hv (S.fE P ψ₀).2 heq0
    rw [Finset.sum_empty, add_zero] at hexp
    refine order_nonneg_of_lowerBd _ (lowerBd_of_derivation _ ?_)
    rw [map_sub, map_sub]
    convert hlb using 2
    exact hexp.symm
  have hfin : S.RegularFinite K (⟨v, hv⟩ - vv) := by
    intro a N hN l hl r hr
    exact hreg _ _ _ _ _ (hX_fin N (Nat.pos_of_ne_zero hN) a)
      (fun Q ↦ by rw [SuperData.branchSub_eq_subst])
      (S.simpleFin_all P ψ₀ hSF hV (S.fE P ψ₀) hf (S.bE P ψ₀) (S.bE_spec P ψ₀ hV) cv hrows
        a N hN l hl r hr)
  have hinf : S.RegularInf K (⟨v, hv⟩ - vv) := by
    intro N hN l hl r hr
    exact hreg _ _ _ _ _ (hX_inf N (Nat.pos_of_ne_zero hN))
      (fun Q ↦ by rw [SuperData.infSub_eq_subst])
      (S.simpleInf_all P ψ₀ hSF hV (S.fE P ψ₀) hf (S.bE P ψ₀) (S.bE_spec P ψ₀ hV) cv hrows
        N hN l hl r hr)
  have h0 := S.deriv_eq_zero_of_regular (K := K) hC _ hfin hinf
  rw [AddSubgroupClass.coe_sub, map_sub, sub_eq_zero] at h0
  rw [hfv, h0]

end CurveData

end Core

end Curves
