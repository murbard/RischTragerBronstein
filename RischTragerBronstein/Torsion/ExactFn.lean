import RischTragerBronstein.Torsion.Conj

/-!
# Exact divisors of functions (any characteristic)

`exact_fn`: let `u ≠ 0` be a function with lower bounds `z` along complete branch systems above
finitely many points `ptᵢ`, regular above every other finite point, with lower bound `zᵢ` above
infinity. If the normalized bounds are integers adding up to `0`, then all bounds are attained and
`u` has order `0` along every branch above every other finite point.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section ExactFn

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma order_W_eq (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0) (W : C[X][X]) (Q : C[X])
    (hQ : Q ≠ 0) (hWQ : (u : L) * aeval S.x Q = S.evXY W) :
    ((W.map g).eval Y).order = (S.embG g hg Y hY u).order + (g Q).order := by
  rw [S.eval_W_branch g hg Y hY u W Q hWQ, HahnSeries.order_mul
    ((map_ne_zero_iff _ (S.embG g hg Y hY).injective).mpr hu) ((map_ne_zero_iff _ hg).mpr hQ)]

lemma embG_order_congrN {N N' : ℕ} (h : N = N') (hN : 0 < N) (hN' : 0 < N') (b : K)
    (r : LaurentSeries K) (hr : (S.F.map (branchSub N b)).eval r = 0)
    (hr' : (S.F.map (branchSub N' b)).eval r = 0) (u : C⟮S.x⟯⟮S.y⟯) :
    (S.embG (branchSub N b) (branchSub_injective N hN b) r hr u).order =
      (S.embG (branchSub N' b) (branchSub_injective N' hN' b) r hr' u).order := by
  subst h; rfl

variable [IsAlgClosed K]

/-- **Exact divisors of functions.** -/
theorem exact_fn (hBr : S.HasBranches K) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0)
    {I : Type*} [Fintype I] (pt : I → K) (hpt : Function.Injective pt)
    (Nf : I → ℕ) (hNf : ∀ i, 0 < Nf i) (lf : I → List (LaurentSeries K))
    (hlf : ∀ i, S.F.map (branchSub (Nf i) (pt i)) = ((lf i).map fun r ↦ X - Polynomial.C r).prod)
    (z : I → LaurentSeries K → ℤ)
    (hz : ∀ i r (hr : r ∈ lf i), z i r ≤ (S.embG (branchSub (Nf i) (pt i))
      (branchSub_injective _ (hNf i) _) r (S.root_of_mem (hlf i) hr) u).order)
    (hreg : ∀ b, b ∉ Set.range pt → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), 0 ≤ (S.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S.root_of_mem hl hr) u).order)
    (Ni : ℕ) (hNi : 0 < Ni) (li : List (LaurentSeries K))
    (hli : S.F.map (infSub Ni) = (li.map fun r ↦ X - Polynomial.C r).prod)
    (zi : LaurentSeries K → ℤ)
    (hzi : ∀ r (hr : r ∈ li), zi r ≤ (S.embG (infSub Ni) (infSub_injective Ni hNi) r
      (S.root_of_mem hli hr) u).order)
    (d : I → ℤ) (hd : ∀ i, ((lf i).map (z i)).sum = Nf i * d i) (di : ℤ)
    (hdi : (li.map zi).sum = Ni * di) (hsum : ∑ i, d i + di = 0) :
    (∀ i r (hr : r ∈ lf i), z i r = (S.embG (branchSub (Nf i) (pt i))
      (branchSub_injective _ (hNf i) _) r (S.root_of_mem (hlf i) hr) u).order) ∧
    (∀ r (hr : r ∈ li), zi r = (S.embG (infSub Ni) (infSub_injective Ni hNi) r
      (S.root_of_mem hli hr) u).order) ∧
    (∀ b, b ∉ Set.range pt → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l), (S.embG (branchSub N b)
        (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r (S.root_of_mem hl hr) u).order = 0) := by
  classical
  set ι := algebraMap C K with hι
  obtain ⟨W, Q, hQ, hWQ⟩ := S.exists_repr u
  have hxQ : aeval S.x Q ≠ 0 := fun h ↦ hQ (transcendental_iff.mp S.htr Q h)
  have hW : S.evXY W ≠ 0 := by
    rw [← hWQ]
    exact mul_ne_zero (fun h ↦ hu (Subtype.ext h)) hxQ
  set m := W.natDegree with hm
  set QK := Q.map ι with hQK
  have hQK0 : QK ≠ 0 := by rw [hQK, Ne, Polynomial.map_eq_zero_iff ι.injective]; exact hQ
  -- branch systems above the other points
  have hBr' : ∀ b : K, ∃ N, N ≠ 0 ∧ ∃ l : List (LaurentSeries K),
      S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod := fun b ↦ by
    obtain ⟨N, hN, l, -, hl⟩ := hBr b
    exact ⟨N, hN, l.map (ofPowerSeries ℤ K), by rw [hl, List.map_map]; rfl⟩
  choose NB hNB lB hlB using hBr'
  -- orders of `W` versus orders of `u`
  have hordW : ∀ (N : ℕ) (hN : 0 < N) (b : K) (r : LaurentSeries K)
      (hr : (S.F.map (branchSub N b)).eval r = 0),
      ((W.map (branchSub (C := C) N b)).eval r).order - N * (QK.rootMultiplicity b : ℤ) =
        (S.embG (branchSub N b) (branchSub_injective N hN b) r hr u).order := by
    intro N hN b r hr
    rw [S.order_W_eq _ (branchSub_injective N hN b) r hr u hu W Q hQ hWQ,
      order_branchSub N hN b Q hQ]
    push_cast; ring
  have hordWi : ∀ (r : LaurentSeries K) (hr : (S.F.map (infSub Ni)).eval r = 0),
      ((W.map (infSub (C := C) Ni)).eval r).order + Ni * (Q.natDegree : ℤ) =
        (S.embG (infSub Ni) (infSub_injective Ni hNi) r hr u).order := by
    intro r hr
    rw [S.order_W_eq _ (infSub_injective Ni hNi) r hr u hu W Q hQ hWQ, order_infSub Ni hNi Q hQ]
    ring
  -- the data on `K`
  set R := QK.roots.toFinset.filter (· ∉ Set.range pt) with hR
  set T := Finset.univ.image pt ∪ R with hT
  set Nf' : K → ℕ := Function.extend pt Nf NB with hNf'
  set lf' : K → List (LaurentSeries K) := Function.extend pt lf lB with hlf'
  set z' : K → LaurentSeries K → ℤ := Function.extend pt z (fun _ _ ↦ 0) with hz'
  set d' : K → ℤ := Function.extend pt d (fun _ ↦ 0) with hd'
  have hnot : ∀ b, b ∉ Set.range pt → ¬∃ a, pt a = b := fun b hb ⟨a, ha⟩ ↦ hb ⟨a, ha⟩
  have hNf'pos : ∀ b, 0 < Nf' b := by
    intro b
    by_cases hb : b ∈ Set.range pt
    · obtain ⟨i, rfl⟩ := hb; rw [hNf', hpt.extend_apply]; exact hNf i
    · rw [hNf', Function.extend_apply' _ _ _ (hnot _ hb)]; exact Nat.pos_of_ne_zero (hNB b)
  have hsplit' : ∀ b, S.F.map (branchSub (Nf' b) b) =
      ((lf' b).map fun r ↦ X - Polynomial.C r).prod := by
    intro b
    by_cases hb : b ∈ Set.range pt
    · obtain ⟨i, rfl⟩ := hb; rw [hNf', hlf', hpt.extend_apply, hpt.extend_apply]; exact hlf i
    · rw [hNf', hlf', Function.extend_apply' _ _ _ (hnot _ hb), Function.extend_apply' _ _ _ (hnot _ hb)]; exact hlB b
  have hQT : ∀ b, QK.IsRoot b → b ∈ T := by
    intro b hb
    by_cases hr : b ∈ Set.range pt
    · obtain ⟨i, rfl⟩ := hr
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((mem_roots hQK0).mpr hb), hr⟩)
  have hz'b : ∀ b ∈ T, ∀ r ∈ lf' b, z' b r ≤ ((W.map (branchSub (C := C) (Nf' b) b)).eval r).order -
      Nf' b * (QK.rootMultiplicity b : ℤ) := by
    intro b _ r hr
    rw [hordW _ (hNf'pos b) b r (S.root_of_mem (hsplit' b) hr)]
    by_cases hb : b ∈ Set.range pt
    · obtain ⟨i, rfl⟩ := hb
      have hr' : r ∈ lf i := by rw [hlf', hpt.extend_apply] at hr; exact hr
      have e1 : z' (pt i) r = z i r := by rw [hz', hpt.extend_apply]
      rw [e1]
      have hNe : Nf' (pt i) = Nf i := by rw [hNf', hpt.extend_apply]
      exact (hz i r hr').trans (le_of_eq (S.embG_order_congrN hNe.symm (hNf i) (hNf'pos _) _ _ _ _ _))
    · have e1 : z' b r = 0 := by rw [hz', Function.extend_apply' _ _ _ (hnot _ hb)]
      rw [e1]
      have hr' : r ∈ lB b := by rw [hlf', Function.extend_apply' _ _ _ (hnot _ hb)] at hr; exact hr
      have hNe : Nf' b = NB b := by rw [hNf', Function.extend_apply' _ _ _ (hnot _ hb)]
      exact (hreg b hb (NB b) (hNB b) (lB b) (hlB b) r hr').trans
        (le_of_eq (S.embG_order_congrN hNe.symm (Nat.pos_of_ne_zero (hNB b)) (hNf'pos _) _ _ _ _ _))
  have hd'b : ∀ b ∈ T, ((lf' b).map (z' b)).sum = Nf' b * d' b := by
    intro b _
    by_cases hb : b ∈ Set.range pt
    · obtain ⟨i, rfl⟩ := hb
      rw [hlf', hz', hNf', hd', hpt.extend_apply, hpt.extend_apply, hpt.extend_apply, hpt.extend_apply]; exact hd i
    · rw [hlf', hz', hNf', hd', Function.extend_apply' _ _ _ (hnot _ hb), Function.extend_apply' _ _ _ (hnot _ hb), Function.extend_apply' _ _ _ (hnot _ hb),
        Function.extend_apply' _ _ _ (hnot _ hb)]
      simp
  have hdisj : Disjoint (Finset.univ.image pt) R := by
    rw [Finset.disjoint_left]
    intro b hb hbR
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp hbR).2 ⟨i, rfl⟩
  have hsum' : ∑ b ∈ T, d' b + di = 0 := by
    rw [hT, Finset.sum_union hdisj, Finset.sum_image fun i _ j _ h ↦ hpt h]
    have h1 : ∑ b ∈ R, d' b = 0 := Finset.sum_eq_zero fun b hb ↦ by
      rw [hd', Function.extend_apply' _ _ _ (hnot _ (Finset.mem_filter.mp hb).2)]
    rw [h1, add_zero]
    simp only [hd', hpt.extend_apply]
    exact hsum
  have hzi' : ∀ r ∈ li, zi r ≤ ((W.map (infSub (C := C) Ni)).eval r).order + Ni * (Q.natDegree : ℤ) := by
    intro r hr
    rw [hordWi r (S.root_of_mem hli hr)]; exact hzi r hr
  obtain ⟨hE1, hE2, hE3⟩ := S.exact_divisor W m le_rfl hW Q hQ T hQT Nf' hNf'pos lf'
    (fun b _ ↦ hsplit' b) z' hz'b Ni hNi li hli zi hzi' d' hd'b di hdi hsum'
  refine ⟨fun i r hr ↦ ?_, fun r hr ↦ ?_, fun b hb N hN l hl r hr ↦ ?_⟩
  · have hmem : pt i ∈ T := Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hr' : r ∈ lf' (pt i) := by rw [hlf', hpt.extend_apply]; exact hr
    have := hE1 (pt i) hmem r hr'
    rw [hordW _ (hNf'pos _) _ r (S.root_of_mem (hsplit' _) hr')] at this
    rw [hz', hpt.extend_apply] at this
    have hNe : Nf' (pt i) = Nf i := by rw [hNf', hpt.extend_apply]
    exact this.trans (S.embG_order_congrN hNe (hNf'pos _) (hNf i) _ _ _ _ _)
  · have := hE2 r hr
    rw [hordWi r (S.root_of_mem hli hr)] at this
    exact this
  · -- above a point off the `ptᵢ`
    have hN0 : 0 < N := Nat.pos_of_ne_zero hN
    have hge : ∀ r' (hr' : r' ∈ l), 0 ≤ (S.embG (branchSub N b) (branchSub_injective N hN0 b) r'
        (S.root_of_mem hl hr') u).order := fun r' hr' ↦ hreg b hb N hN l hl r' hr'
    -- the multiplicity of `b` in the norm
    have hmult : (((S.normW W m).map ι).rootMultiplicity b : ℤ) = S.F.natDegree *
        (QK.rootMultiplicity b : ℤ) := by
      by_cases hbT : b ∈ T
      · have hbR : b ∈ R := by
          rcases Finset.mem_union.mp hbT with h | h
          · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h; exact absurd ⟨i, rfl⟩ hb
          · exact h
        have hs := S.sum_order_fin W m le_rfl hW (Nf' b) (hNf'pos b) b (lf' b) (hsplit' b)
        have hlen := S.length_of_split (hsplit' b)
        have hz0 : ∀ r' ∈ lf' b, ((W.map (branchSub (C := C) (Nf' b) b)).eval r').order =
            Nf' b * (QK.rootMultiplicity b : ℤ) := by
          intro r' hr'
          have := hE1 b hbT r' hr'
          rw [hz', Function.extend_apply' _ _ _ (hnot _ hb)] at this
          linarith
        rw [List.map_congr_left hz0, List.map_const', List.sum_replicate, hlen, nsmul_eq_mul] at hs
        have hN' : (0 : ℤ) < Nf' b := by exact_mod_cast hNf'pos b
        have : (Nf' b : ℤ) * ((((S.normW W m).map ι).rootMultiplicity b : ℤ) -
            S.F.natDegree * (QK.rootMultiplicity b : ℤ)) = 0 := by
          push_cast at hs; linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hN'.ne'
        · linarith
      · have hQb : QK.rootMultiplicity b = 0 := by
          by_contra h0
          exact hbT (hQT b ((rootMultiplicity_pos hQK0).mp (Nat.pos_of_ne_zero h0)))
        rw [hE3 b hbT, hQb]; simp
    have hs := S.sum_order_fin W m le_rfl hW N hN0 b l hl
    have hlen := S.length_of_split hl
    have hf0 : ∀ r' ∈ l, (fun _ ↦ (0 : ℤ)) r' ≤ (fun r' ↦ ((W.map (branchSub (C := C) N b)).eval r').order -
        N * (QK.rootMultiplicity b : ℤ)) r' := by
      intro r' hr'
      simp only
      rw [hordW N hN0 b r' (S.root_of_mem hl hr')]
      exact hge r' hr'
    have hsum0 : (l.map fun _ ↦ (0 : ℤ)).sum = (l.map fun r' ↦ ((W.map (branchSub (C := C) N b)).eval r').order -
        N * (QK.rootMultiplicity b : ℤ)).sum := by
      rw [list_sum_map_sub', hs, hlen, hmult]
      simp only [List.map_const', List.sum_replicate, smul_zero]
      ring
    have := list_eq_of_sum_eq l _ _ hf0 hsum0 r hr
    rw [← hordW N hN0 b r (S.root_of_mem hl hr)]
    linarith

end CurveData

end ExactFn

end Curves
