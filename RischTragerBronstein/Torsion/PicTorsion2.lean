import RischTragerBronstein.Torsion.PicTorsion
import RischTragerBronstein.Torsion.Degree
import RischTragerBronstein.Torsion.Exact
import RischTragerBronstein.Torsion.PrincipalG
import RischTragerBronstein.Torsion.CertBasis3

/-!
# Orders of a function fibre by fibre

For `u = W(x, y)/Q(x) ≠ 0`, along any complete branch system above `x = b` (`x = b + Tᴺ`) the
orders of `u` add up to `N · μ(b)` with `μ(b) = mult_b N(W) − n · mult_b Q` (`fibre_sum`), and
above infinity to `−N · (deg N(W) − n deg Q)` (`inf_sum`); `∑_b μ(b) = deg N(W) − n deg Q`
(`sum_mu`). These are the bookkeeping identities of the degree theorem, used for the finiteness
of `Pic⁰` over finite fields.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

lemma sum_attach_eq_fin {α : Type*} : ∀ (l : List α) (G : (r : α) → r ∈ l → ℤ),
    (l.attach.map fun r ↦ G r.1 r.2).sum = ∑ i : Fin l.length, G (l.get i) (List.get_mem l i)
  | [], G => by simp
  | a :: l, G => by
    have ih := sum_attach_eq_fin l fun r h ↦ G r (List.mem_cons_of_mem a h)
    rw [List.attach_cons, List.map_cons, List.sum_cons, List.map_map]
    change _ = ∑ i : Fin (l.length + 1), G ((a :: l).get i) (List.get_mem (a :: l) i)
    rw [Fin.sum_univ_succ]
    congr 1

section Fibre

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- `μ(b) = mult_b N(W) − n · mult_b Q`. -/
noncomputable def muW (W : C[X][X]) (m : ℕ) (Q : C[X]) (b : K) : ℤ :=
  ((S.normW W m).map (algebraMap C K)).rootMultiplicity b -
    S.F.natDegree * (Q.map (algebraMap C K)).rootMultiplicity b

lemma order_div_of (z w : LaurentSeries K) (hz : z ≠ 0) (hw : w ≠ 0) :
    (z / w).order = z.order - w.order := by
  have h : z = z / w * w := by rw [div_mul_cancel₀ z hw]
  have hzw : z / w ≠ 0 := div_ne_zero hz hw
  have := congrArg HahnSeries.order h
  rw [HahnSeries.order_mul hzw hw] at this
  omega

/-- **The orders above a finite point.** -/
lemma fibre_sum (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0) (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0)
    (hWQ : (u : L) * aeval S.x Q = S.evXY W) (m : ℕ) (hWm : W.natDegree ≤ m)
    (N : ℕ) (hN : 0 < N) (b : K) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    (l.attach.map fun r ↦ (S.embG (branchSub N b) (branchSub_injective N hN b) r.1
      (S.root_of_mem hl r.2) u).order).sum = N * S.muW W m Q b := by
  classical
  have hW : S.evXY W ≠ 0 := by
    rw [← hWQ]
    exact mul_ne_zero (fun h ↦ hu (Subtype.ext h)) (fun h ↦ S.htr ⟨Q, hQ, h⟩)
  have hQb : branchSub N b Q ≠ 0 :=
    (map_ne_zero_iff _ (branchSub_injective N hN b)).mpr hQ
  have hsum := S.sum_order_fin W m hWm hW N hN b l hl
  have hlen := S.length_of_split hl
  -- each order of `W` is the order of `u` plus the order of `Q`
  have hrel : ∀ (r : LaurentSeries K) (hr : r ∈ l),
      ((W.map (branchSub N b)).eval r).order =
        (S.embG (branchSub N b) (branchSub_injective N hN b) r (S.root_of_mem hl hr) u).order +
          N * (Q.map (algebraMap C K)).rootMultiplicity b := by
    intro r hr
    have e := S.eval_W_branch (branchSub N b) (branchSub_injective N hN b) r
      (S.root_of_mem hl hr) u W Q hWQ
    have hu' : S.embG (branchSub N b) (branchSub_injective N hN b) r (S.root_of_mem hl hr) u ≠ 0 :=
      (map_ne_zero_iff _ (S.embG _ _ r _).injective).mpr hu
    rw [e, HahnSeries.order_mul hu' hQb, order_branchSub N hN b Q hQ]
    push_cast; ring
  have e2 : (l.map fun r ↦ ((W.map (branchSub N b)).eval r).order) =
      l.attach.map fun r ↦ (S.embG (branchSub N b) (branchSub_injective N hN b) r.1
        (S.root_of_mem hl r.2) u).order + N * (Q.map (algebraMap C K)).rootMultiplicity b := by
    conv_lhs => rw [← List.attach_map_subtype_val l, List.map_map]
    exact List.map_congr_left fun r _ ↦ hrel r.1 r.2
  rw [e2, List.sum_map_add, List.map_const', List.sum_replicate, List.length_attach, hlen] at hsum
  rw [muW]
  simp only [nsmul_eq_mul] at hsum
  push_cast
  linarith

/-- **The orders above infinity.** -/
lemma inf_sum (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0) (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0)
    (hWQ : (u : L) * aeval S.x Q = S.evXY W) (m : ℕ) (hWm : W.natDegree ≤ m)
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    (l.attach.map fun r ↦ (S.embG (infSub N) (infSub_injective N hN) r.1
      (S.root_of_mem hl r.2) u).order).sum =
      -(N * ((S.normW W m).natDegree - S.F.natDegree * Q.natDegree : ℤ)) := by
  classical
  have hW : S.evXY W ≠ 0 := by
    rw [← hWQ]
    exact mul_ne_zero (fun h ↦ hu (Subtype.ext h)) (fun h ↦ S.htr ⟨Q, hQ, h⟩)
  have hQb : infSub (K := K) N Q ≠ 0 := (map_ne_zero_iff _ (infSub_injective N hN)).mpr hQ
  have hsum := S.sum_order_inf W m hWm hW N hN l hl
  have hlen := S.length_of_split hl
  have hrel : ∀ (r : LaurentSeries K) (hr : r ∈ l),
      ((W.map (infSub N)).eval r).order =
        (S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr) u).order +
          -(N * Q.natDegree : ℤ) := by
    intro r hr
    have e := S.eval_W_branch (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr) u W Q hWQ
    have hu' : S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr) u ≠ 0 :=
      (map_ne_zero_iff _ (S.embG _ _ r _).injective).mpr hu
    rw [e, HahnSeries.order_mul hu' hQb, order_infSub N hN Q hQ]
  have e2 : (l.map fun r ↦ ((W.map (infSub N)).eval r).order) =
      l.attach.map fun r ↦ (S.embG (infSub N) (infSub_injective N hN) r.1
        (S.root_of_mem hl r.2) u).order + -(N * Q.natDegree : ℤ) := by
    conv_lhs => rw [← List.attach_map_subtype_val l, List.map_map]
    exact List.map_congr_left fun r _ ↦ hrel r.1 r.2
  rw [e2, List.sum_map_add, List.map_const', List.sum_replicate, List.length_attach, hlen] at hsum
  simp only [nsmul_eq_mul] at hsum
  linarith

variable [IsAlgClosed K]

/-- **The total of `μ`**: over any finite set containing the roots. -/
lemma sum_mu (W : C[X][X]) (m : ℕ) (Q : C[X]) (hN0 : S.normW W m ≠ 0) (hQ : Q ≠ 0)
    (T : Finset K)
    (hT : ∀ b, ((S.normW W m * Q).map (algebraMap C K)).IsRoot b → b ∈ T) :
    ∑ b ∈ T, S.muW W m Q b = (S.normW W m).natDegree - S.F.natDegree * Q.natDegree := by
  classical
  have hN' : (S.normW W m).map (algebraMap C K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hN0
  have hQ' : Q.map (algebraMap C K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hQ
  have h1 := sum_rootMultiplicity_eq ((S.normW W m).map (algebraMap C K)) hN' T fun b hb ↦ hT b (by
    rw [Polynomial.map_mul, IsRoot, eval_mul]; rw [IsRoot] at hb; rw [hb, zero_mul])
  have h2 := sum_rootMultiplicity_eq (Q.map (algebraMap C K)) hQ' T fun b hb ↦ hT b (by
    rw [Polynomial.map_mul, IsRoot, eval_mul]; rw [IsRoot] at hb; rw [hb, mul_zero])
  rw [natDegree_map] at h1 h2
  simp only [muW, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2]

/-- A branch system above `b` as a list of Laurent series. -/
lemma hasBranches_list (hBr : S.HasBranches K) (b : K) :
    ∃ N, 0 < N ∧ ∃ l : List (LaurentSeries K),
      S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod := by
  obtain ⟨N, hN, l, -, hl⟩ := hBr b
  exact ⟨N, Nat.pos_of_ne_zero hN, l.map (ofPowerSeries ℤ K), by rw [hl, List.map_map]; rfl⟩

section Surplus

variable {J : Type*} [Fintype J] (α : J → C) (N : J → ℕ) (hN : ∀ j, 0 < N j)
  (lf : J → List (LaurentSeries K))
  (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
    ((lf j).map fun r ↦ X - Polynomial.C r).prod)

omit [IsAlgClosed K] in
lemma sum_nonneg_attach {l : List (LaurentSeries K)} (g : {r // r ∈ l} → ℤ) (h : ∀ r, 0 ≤ g r) :
    0 ≤ (l.attach.map g).sum :=
  List.sum_nonneg fun z hz ↦ by obtain ⟨r, -, rfl⟩ := List.mem_map.mp hz; exact h r

/-- Off the points of `Γ`, `μ ≥ 0`, and `μ > 0` as soon as one order is positive. -/
lemma mu_off (hBr : S.HasBranches K) (Γ : J → LaurentSeries K → ℕ) (c : ℕ) (u : C⟮S.x⟯⟮S.y⟯)
    (hu : u ≠ 0) (hdiv : S.DivGE α N hN lf hlf Γ c u) (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0)
    (hWQ : (u : L) * aeval S.x Q = S.evXY W) (m : ℕ) (hWm : W.natDegree ≤ m) (b : K)
    (hb : b ∉ Set.range fun j ↦ algebraMap C K (α j)) :
    0 ≤ S.muW W m Q b ∧ ∀ (N' : ℕ) (hN' : 0 < N') (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N' b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      0 < (S.embG (branchSub N' b) (branchSub_injective N' hN' b) r (S.root_of_mem hl hr) u).order →
        0 < S.muW W m Q b := by
  classical
  have key : ∀ (N' : ℕ) (hN' : 0 < N') (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N' b) = (l.map fun r ↦ X - Polynomial.C r).prod),
      (N' : ℤ) * S.muW W m Q b = (l.attach.map fun r ↦ (S.embG (branchSub N' b)
        (branchSub_injective N' hN' b) r.1 (S.root_of_mem hl r.2) u).order).sum ∧
      ∀ r (hr : r ∈ l), 0 ≤ (S.embG (branchSub N' b) (branchSub_injective N' hN' b) r
        (S.root_of_mem hl hr) u).order := fun N' hN' l hl ↦
    ⟨(S.fibre_sum u hu W Q hQ hWQ m hWm N' hN' b l hl).symm,
      fun r hr ↦ hdiv.2.1 b hb N' hN'.ne' l hl r hr⟩
  obtain ⟨N0, hN0, l0, hl0⟩ := S.hasBranches_list hBr b
  refine ⟨?_, fun N' hN' l hl r hr hpos ↦ ?_⟩
  · obtain ⟨e, hnn⟩ := key N0 hN0 l0 hl0
    have := sum_nonneg_attach _ fun r ↦ hnn r.1 r.2
    rw [← e] at this
    by_contra h
    push_neg at h
    have : (N0 : ℤ) * S.muW W m Q b < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hN0) h
    linarith
  · obtain ⟨e, hnn⟩ := key N' hN' l hl
    have hsum : 0 < (l.attach.map fun r ↦ (S.embG (branchSub N' b)
        (branchSub_injective N' hN' b) r.1 (S.root_of_mem hl r.2) u).order).sum := by
      refine lt_of_lt_of_le hpos (List.single_le_sum ?_ _ ?_)
      · intro z hz; obtain ⟨r, -, rfl⟩ := List.mem_map.mp hz; exact hnn r.1 r.2
      · exact List.mem_map.mpr ⟨⟨r, hr⟩, List.mem_attach _ _, rfl⟩
    rw [← e] at hsum
    exact pos_of_mul_pos_right hsum (by positivity)

/-- At the points of `Γ`: `μ(α_j) ≥ M d_j`. -/
lemma mu_alpha (Γ : J → LaurentSeries K → ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (M c : ℕ) (u : C⟮S.x⟯⟮S.y⟯)
    (hu : u ≠ 0) (hdiv : S.DivGE α N hN lf hlf (fun j r ↦ M * Γ j r) c u) (W : C[X][X])
    (Q : C[X]) (hQ : Q ≠ 0) (hWQ : (u : L) * aeval S.x Q = S.evXY W) (m : ℕ)
    (hWm : W.natDegree ≤ m) (j : J) : (M * dΓ j : ℤ) ≤ S.muW W m Q (algebraMap C K (α j)) := by
  classical
  have e := S.fibre_sum u hu W Q hQ hWQ m hWm (N j) (hN j) _ (lf j) (hlf j)
  have hle : ((lf j).attach.map fun r ↦ ((M * Γ j r.1 : ℕ) : ℤ)).sum ≤
      ((lf j).attach.map fun r ↦ (S.embG (branchSub (N j) (algebraMap C K (α j)))
        (branchSub_injective (N j) (hN j) _) r.1 (S.root_of_mem (hlf j) r.2) u).order).sum :=
    List.sum_le_sum fun r _ ↦ hdiv.1 j r.1 r.2
  have hΓs : ((lf j).attach.map fun r ↦ ((M * Γ j r.1 : ℕ) : ℤ)).sum = M * N j * dΓ j := by
    have hnat : ((lf j).attach.map fun r ↦ M * Γ j r.1).sum = M * (N j * dΓ j) := by
      rw [show ((lf j).attach.map fun r ↦ M * Γ j r.1) =
          ((lf j).attach.map Subtype.val).map (fun r ↦ M * Γ j r) by rw [List.map_map]; rfl,
        List.attach_map_subtype_val, List.sum_map_mul_left, hdΓ j]
    have := congrArg (Nat.cast : ℕ → ℤ) hnat
    rw [Nat.cast_list_sum, List.map_map] at this
    rw [show (fun r : {r // r ∈ lf j} ↦ ((M * Γ j r.1 : ℕ) : ℤ)) =
      (Nat.cast : ℕ → ℤ) ∘ (fun r ↦ M * Γ j r.1) from rfl, this]
    push_cast; ring
  rw [hΓs, e] at hle
  have hN0 : (0 : ℤ) < N j := by exact_mod_cast hN j
  nlinarith

/-- Above infinity: `deg N(W) − n deg Q ≤ n c`. -/
lemma nu_inf (hBI : S.HasBranchesInf K) (Γ : J → LaurentSeries K → ℕ) (c : ℕ)
    (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0) (hdiv : S.DivGE α N hN lf hlf Γ c u) (W : C[X][X])
    (Q : C[X]) (hQ : Q ≠ 0) (hWQ : (u : L) * aeval S.x Q = S.evXY W) (m : ℕ)
    (hWm : W.natDegree ≤ m) :
    ((S.normW W m).natDegree - S.F.natDegree * Q.natDegree : ℤ) ≤ S.F.natDegree * c := by
  classical
  obtain ⟨N0, hN0, l, hlen, hl⟩ := hBI
  have hN0' : 0 < N0 := Nat.pos_of_ne_zero hN0
  have e := S.inf_sum u hu W Q hQ hWQ m hWm N0 hN0' l hl
  have hle : ((l.attach.map fun _ ↦ (-((N0 * c : ℕ) : ℤ)))).sum ≤
      (l.attach.map fun r ↦ (S.embG (infSub N0) (infSub_injective N0 hN0') r.1
        (S.root_of_mem hl r.2) u).order).sum :=
    List.sum_le_sum fun r _ ↦ hdiv.2.2 N0 hN0 l hl r.1 r.2
  rw [e, List.map_const', List.sum_replicate, List.length_attach, hlen, nsmul_eq_mul] at hle
  push_cast at hle
  have hN0'' : (0 : ℤ) < N0 := by exact_mod_cast hN0'
  nlinarith

/-- The norm of a non-zero function is non-zero. -/
lemma normW_ne_zero' (hBr : S.HasBranches K) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0) (W : C[X][X])
    (Q : C[X]) (hQ : Q ≠ 0) (hWQ : (u : L) * aeval S.x Q = S.evXY W) (m : ℕ)
    (hWm : W.natDegree ≤ m) : S.normW W m ≠ 0 := by
  obtain ⟨N0, hN0, l, hl⟩ := S.hasBranches_list hBr 0
  have hW : S.evXY W ≠ 0 := by
    rw [← hWQ]; exact mul_ne_zero (fun h ↦ hu (Subtype.ext h)) (fun h ↦ S.htr ⟨Q, hQ, h⟩)
  exact S.normW_ne_zero W m hWm hW _ (branchSub_injective N0 hN0 0) l hl

/-- **The surplus off `Γ` is at most `n s`.** -/
lemma surplus_bound (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    (hα : Function.Injective α) (Γ : J → LaurentSeries K → ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (c : ℕ)
    (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree) (M s : ℕ) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0)
    (hdiv : S.DivGE α N hN lf hlf (fun j r ↦ M * Γ j r) (M * c + s) u) (W : C[X][X])
    (Q : C[X]) (hQ : Q ≠ 0) (hWQ : (u : L) * aeval S.x Q = S.evXY W) (m : ℕ)
    (hWm : W.natDegree ≤ m) (T : Finset K)
    (hT : ∀ b ∈ T, b ∉ Set.range fun j ↦ algebraMap C K (α j)) :
    ∑ b ∈ T, S.muW W m Q b ≤ S.F.natDegree * s := by
  classical
  have hN0 := S.normW_ne_zero' hBr u hu W Q hQ hWQ m hWm
  set A : Finset K := Finset.univ.image fun j ↦ algebraMap C K (α j) with hA
  set R : Finset K := ((S.normW W m * Q).map (algebraMap C K)).roots.toFinset with hR
  set T' := R ∪ T ∪ A with hT'
  have hsum := S.sum_mu W m Q hN0 hQ T' fun b hb ↦ by
    have h0 : (S.normW W m * Q).map (algebraMap C K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr (mul_ne_zero hN0 hQ)
    simp only [hT', Finset.mem_union]
    exact Or.inl (Or.inl (Multiset.mem_toFinset.mpr ((mem_roots h0).mpr hb)))
  have hsplit := Finset.sum_sdiff (s₁ := A) (s₂ := T') (f := S.muW W m Q)
    (Finset.subset_union_right)
  -- the points of `Γ`
  have hAsum : ∑ b ∈ A, S.muW W m Q b = ∑ j, S.muW W m Q (algebraMap C K (α j)) := by
    rw [hA, Finset.sum_image fun j _ j' _ h ↦ hα ((algebraMap C K).injective h)]
  have hAge : (M * (c * S.F.natDegree) : ℤ) ≤ ∑ j, S.muW W m Q (algebraMap C K (α j)) := by
    have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦
      S.mu_alpha α N hN lf hlf Γ dΓ hdΓ M (M * c + s) u hu hdiv W Q hQ hWQ m hWm j
    rw [← Finset.mul_sum] at h
    have : ((∑ j, dΓ j : ℕ) : ℤ) = c * S.F.natDegree := by exact_mod_cast hsumΓ
    push_cast at this
    rw [this] at h
    exact h
  -- off `Γ`: non-negative, and `T` is part of it
  have hoff : ∑ b ∈ T, S.muW W m Q b ≤ ∑ b ∈ T' \ A, S.muW W m Q b := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb ↦ ?_) (fun b hb _ ↦ ?_)
    · rw [Finset.mem_sdiff]
      refine ⟨by simp [hT', hb], fun hbA ↦ hT b hb ?_⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hbA
      exact ⟨j, rfl⟩
    · rw [Finset.mem_sdiff] at hb
      refine (S.mu_off α N hN lf hlf hBr _ _ u hu hdiv W Q hQ hWQ m hWm b fun ⟨j, hj⟩ ↦ hb.2 ?_).1
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  have hinf := S.nu_inf α N hN lf hlf hBI _ _ u hu hdiv W Q hQ hWQ m hWm
  rw [hsum] at hsplit
  push_cast at hinf
  nlinarith

open Classical in
/-- **The surplus identity**: with `R` the roots of `N(W) Q` off `Γ`,
`∑_R μ + ∑_j (μ(α_j) − M d_j) + (n (M c + s) − (deg N(W) − n deg Q)) = n s`. -/
lemma surplus_total (hBr : S.HasBranches K) (hα : Function.Injective α)
    (Γ : J → LaurentSeries K → ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (c : ℕ)
    (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree) (M s : ℕ) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0)
    (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0) (hWQ : (u : L) * aeval S.x Q = S.evXY W) (m : ℕ)
    (hWm : W.natDegree ≤ m) :
    ∑ b ∈ (((S.normW W m * Q).map (algebraMap C K)).roots.toFinset \
        Finset.univ.image fun j ↦ algebraMap C K (α j)), S.muW W m Q b +
      ∑ j, (S.muW W m Q (algebraMap C K (α j)) - M * dΓ j) +
      (S.F.natDegree * (M * c + s) - ((S.normW W m).natDegree - S.F.natDegree * Q.natDegree)) =
    S.F.natDegree * s := by
  have hN0 := S.normW_ne_zero' hBr u hu W Q hQ hWQ m hWm
  set A : Finset K := Finset.univ.image fun j ↦ algebraMap C K (α j) with hA
  set R : Finset K := ((S.normW W m * Q).map (algebraMap C K)).roots.toFinset with hR
  have hsum := S.sum_mu W m Q hN0 hQ (R ∪ A) fun b hb ↦ by
    have h0 : (S.normW W m * Q).map (algebraMap C K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr (mul_ne_zero hN0 hQ)
    exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr ((mem_roots h0).mpr hb))
  have hsplit := Finset.sum_sdiff (s₁ := A) (s₂ := R ∪ A) (f := S.muW W m Q)
    Finset.subset_union_right
  rw [Finset.union_sdiff_right] at hsplit
  have hAsum : ∑ b ∈ A, S.muW W m Q b = ∑ j, S.muW W m Q (algebraMap C K (α j)) := by
    rw [hA, Finset.sum_image fun j _ j' _ h ↦ hα ((algebraMap C K).injective h)]
  have hd : ∑ j, ((M * dΓ j : ℕ) : ℤ) = M * c * S.F.natDegree := by
    rw [← Nat.cast_sum, ← Finset.mul_sum, hsumΓ]; push_cast; ring
  rw [Finset.sum_sub_distrib]
  push_cast at hd ⊢
  rw [hd]
  linarith

end Surplus

section Frob

variable [Fintype C] {J : Type*} [Fintype J] (α : J → C) (N : J → ℕ) (hN : ∀ j, 0 < N j)
  (lf : J → List (LaurentSeries K))
  (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
    ((lf j).map fun r ↦ X - Polynomial.C r).prod)
  {φ : K →+* K} (hφ : ∀ x, φ x = x ^ Fintype.card C)
include hφ

/-- `μ` is invariant under the Frobenius. -/
lemma muW_frob (W : C[X][X]) (m : ℕ) (Q : C[X]) (hN0 : S.normW W m ≠ 0) (hQ : Q ≠ 0) (b : K) :
    S.muW W m Q (φ b) = S.muW W m Q b := by
  simp only [muW, rootMult_frob hφ _ hN0, rootMult_frob hφ _ hQ]

/-- **Support**: off `Γ`, a point with `μ > 0` is fixed by `φ^{(n s)!}`. -/
lemma support_fixed (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    (hα : Function.Injective α) (Γ : J → LaurentSeries K → ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (c : ℕ)
    (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree) (M s : ℕ) (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0)
    (hdiv : S.DivGE α N hN lf hlf (fun j r ↦ M * Γ j r) (M * c + s) u) (W : C[X][X])
    (Q : C[X]) (hQ : Q ≠ 0) (hWQ : (u : L) * aeval S.x Q = S.evXY W) (m : ℕ)
    (hWm : W.natDegree ≤ m) (b : K) (hb : b ∉ Set.range fun j ↦ algebraMap C K (α j))
    (hμ : 0 < S.muW W m Q b) : φ^[(S.F.natDegree * s).factorial] b = b := by
  classical
  have hN0 := S.normW_ne_zero' hBr u hu W Q hQ hWQ m hWm
  have hP0 : (S.normW W m * Q).map (algebraMap C K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr (mul_ne_zero hN0 hQ)
  set R : Finset K := (((S.normW W m * Q).map (algebraMap C K)).roots.toFinset).filter
    fun z ↦ z ∉ Set.range (fun j ↦ algebraMap C K (α j)) ∧ 0 < S.muW W m Q z with hR
  have hroot : ∀ z, 0 < S.muW W m Q z → z ∈ ((S.normW W m * Q).map (algebraMap C K)).roots := by
    intro z hz
    rw [mem_roots hP0, ← rootMultiplicity_pos hP0, Polynomial.map_mul,
      rootMultiplicity_mul (by rwa [← Polynomial.map_mul])]
    have : 0 < ((S.normW W m).map (algebraMap C K)).rootMultiplicity z := by
      unfold muW at hz
      have : (0 : ℤ) ≤ S.F.natDegree * ((Q.map (algebraMap C K)).rootMultiplicity z : ℤ) := by
        positivity
      omega
    omega
  have hbR : b ∈ R := by
    rw [hR, Finset.mem_filter, Multiset.mem_toFinset]; exact ⟨hroot b hμ, hb, hμ⟩
  have hmaps : ∀ z ∈ R, φ z ∈ R := by
    intro z hz
    rw [hR, Finset.mem_filter] at hz ⊢
    have hμz : S.muW W m Q (φ z) = S.muW W m Q z := S.muW_frob hφ W m Q hN0 hQ z
    refine ⟨Multiset.mem_toFinset.mpr (hroot _ (by rw [hμz]; exact hz.2.2)), fun ⟨j, hj⟩ ↦ ?_,
      by rw [hμz]; exact hz.2.2⟩
    apply hz.2.1
    refine ⟨j, φ.injective ?_⟩
    rw [frob_fix hφ]
    exact hj
  have hcard : R.card ≤ S.F.natDegree * s := by
    have h1 : (R.card : ℤ) ≤ ∑ z ∈ R, S.muW W m Q z := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum fun z hz ↦ ?_
      rw [hR, Finset.mem_filter] at hz
      push_cast; omega
    have h2 := S.surplus_bound α N hN lf hlf hBr hBI hα Γ dΓ hdΓ c hsumΓ M s u hu hdiv W Q hQ hWQ m
      hWm R fun z hz ↦ by rw [hR, Finset.mem_filter] at hz; exact hz.2.1
    exact_mod_cast h1.trans h2
  have hfix := iterate_fix_of_mapsTo φ.injective R hmaps b hbR
  obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial hcard
  rw [ht, Function.iterate_mul]
  exact Function.iterate_fixed hfix t

end Frob

section Main

variable [Fintype C] {J : Type*} [Fintype J] (α : J → C) (N : J → ℕ) (hN : ∀ j, 0 < N j)
  (lf : J → List (LaurentSeries K))
  (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
    ((lf j).map fun r ↦ X - Polynomial.C r).prod)

omit [IsAlgClosed K] [Fintype C] [Fintype J] in
lemma order_quot (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (r : LaurentSeries K)
    (hr : (S.F.map g).eval r = 0) (u v : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0) (hv : v ≠ 0) :
    (S.embG g hg r hr (u / v)).order = (S.embG g hg r hr u).order - (S.embG g hg r hr v).order := by
  rw [map_div₀]
  exact order_div_of _ _ ((map_ne_zero_iff _ (S.embG g hg r hr).injective).mpr hu)
    ((map_ne_zero_iff _ (S.embG g hg r hr).injective).mpr hv)

/-- **Every divisor class of degree `0` over a finite field has finite order** (in the explicit
model): if for every `M` some `u_M ≠ 0` has `div u_M ≥ M Γ − (M c + s) ∞ₓ` (Riemann's inequality),
then some positive multiple `m (Γ − c ∞ₓ)` is principal. The surpluses of the `u_M` have total
`n s` and lie above finitely many points (`support_fixed`), so two of them coincide
(pigeonhole), and the quotient has divisor exactly `(M₂ − M₁)(Γ − c ∞ₓ)`. -/
theorem exists_principal_mul (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    (hα : Function.Injective α) (Γ : J → LaurentSeries K → ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (c : ℕ)
    (hsumΓ : ∑ j, dΓ j = c * S.F.natDegree) (s : ℕ)
    (hR : ∀ M : ℕ, ∃ u : C⟮S.x⟯⟮S.y⟯, u ≠ 0 ∧
      S.DivGE α N hN lf hlf (fun j r ↦ M * Γ j r) (M * c + s) u) :
    ∃ m, 0 < m ∧ ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
      S.DivGE α N hN lf hlf (fun j r ↦ m * Γ j r) (m * c) γ := by
  classical
  obtain ⟨φ, hφ⟩ := exists_frob (C := C) (K := K)
  choose u hu0 hdiv using hR
  choose W Q hQ hWQ using fun M ↦ S.exists_repr (u M)
  set n := S.F.natDegree with hn
  set k := (n * s).factorial with hk
  have hk0 : 0 < k := Nat.factorial_pos _
  set A : Finset K := Finset.univ.image fun j ↦ algebraMap C K (α j) with hA
  have hAr : ∀ b, b ∈ A ↔ b ∈ Set.range fun j ↦ algebraMap C K (α j) := fun b ↦ by
    simp [hA]
  set Z0 : Finset K := (finite_frob_fixed hφ k hk0).toFinset \ A with hZ0
  -- branch systems above the points of `Z0` and above infinity
  choose Nb hNb lb hlb using fun b ↦ S.hasBranches_list hBr b
  obtain ⟨Ni, hNi, li, hlen, hli⟩ := hBI
  have hNi' : 0 < Ni := Nat.pos_of_ne_zero hNi
  -- the orders
  let oα : ℕ → (j : J) → Fin (lf j).length → ℤ := fun M j i ↦
    (S.embG (branchSub (N j) (algebraMap C K (α j))) (branchSub_injective _ (hN j) _)
      ((lf j).get i) (S.root_of_mem (hlf j) (List.get_mem _ _)) (u M)).order
  let ob : ℕ → (b : Z0) → Fin (lb (b : K)).length → ℤ := fun M b i ↦
    (S.embG (branchSub (Nb (b : K)) (b : K)) (branchSub_injective _ (hNb (b : K)) _)
      ((lb (b : K)).get i) (S.root_of_mem (hlb (b : K)) (List.get_mem _ _)) (u M)).order
  let oi : ℕ → Fin li.length → ℤ := fun M i ↦
    (S.embG (infSub Ni) (infSub_injective _ hNi') (li.get i)
      (S.root_of_mem hli (List.get_mem _ _)) (u M)).order
  -- the surpluses and their bound
  set B : ℕ := n * s * (∑ j, N j + ∑ b ∈ Z0, Nb b + Ni) with hB
  let Eα : ℕ → (j : J) → Fin (lf j).length → ℤ := fun M j i ↦ oα M j i - M * Γ j ((lf j).get i)
  let Eb : ℕ → (b : Z0) → Fin (lb (b : K)).length → ℤ := ob
  let Ei : ℕ → Fin li.length → ℤ := fun M i ↦ oi M i + Ni * (M * c + s)
  have hbounds : ∀ M, (∀ j i, 0 ≤ Eα M j i ∧ Eα M j i ≤ B) ∧ (∀ b i, 0 ≤ Eb M b i ∧ Eb M b i ≤ B) ∧
      (∀ i, 0 ≤ Ei M i ∧ Ei M i ≤ B) := by
    intro M
    set mW := (W M).natDegree
    have hT := S.surplus_total α N lf hBr hα Γ dΓ hdΓ c hsumΓ M s (u M) (hu0 M) (W M)
      (Q M) (hQ M) (hWQ M) mW le_rfl
    set R := ((S.normW (W M) mW * Q M).map (algebraMap C K)).roots.toFinset \ A with hR
    -- the three parts are non-negative
    have hX1 : ∀ b ∈ R, 0 ≤ S.muW (W M) mW (Q M) b := fun b hb ↦
      (S.mu_off α N hN lf hlf hBr _ _ (u M) (hu0 M) (hdiv M) (W M) (Q M) (hQ M) (hWQ M) mW le_rfl b
        fun h ↦ (Finset.mem_sdiff.mp hb).2 ((hAr b).mpr h)).1
    have hX2 : ∀ j, 0 ≤ S.muW (W M) mW (Q M) (algebraMap C K (α j)) - M * dΓ j := fun j ↦ by
      have := S.mu_alpha α N hN lf hlf Γ dΓ hdΓ M _ (u M) (hu0 M) (hdiv M) (W M) (Q M) (hQ M)
        (hWQ M) mW le_rfl j
      push_cast at this; linarith
    have hX3 := S.nu_inf α N hN lf hlf ⟨Ni, hNi, li, hlen, hli⟩ _ _ (u M) (hu0 M) (hdiv M) (W M)
      (Q M) (hQ M) (hWQ M) mW le_rfl
    have hS1 : 0 ≤ ∑ b ∈ R, S.muW (W M) mW (Q M) b := Finset.sum_nonneg hX1
    have hS2 : 0 ≤ ∑ j, (S.muW (W M) mW (Q M) (algebraMap C K (α j)) - M * dΓ j) :=
      Finset.sum_nonneg fun j _ ↦ hX2 j
    have hBn : (0 : ℤ) ≤ n * s := by positivity
    push_cast at hT hX3
    refine ⟨fun j i ↦ ?_, fun b i ↦ ?_, fun i ↦ ?_⟩
    · -- at the points of `Γ`
      have hge : ∀ i', 0 ≤ Eα M j i' := fun i' ↦ by
        have := (hdiv M).1 j ((lf j).get i') (List.get_mem _ _)
        simp only [Eα, oα]; push_cast at this; linarith
      have hsumE : ∑ i', Eα M j i' = N j * (S.muW (W M) mW (Q M) (algebraMap C K (α j)) -
          M * dΓ j) := by
        have e1 := S.fibre_sum (u M) (hu0 M) (W M) (Q M) (hQ M) (hWQ M) mW le_rfl (N j) (hN j) _
          (lf j) (hlf j)
        rw [sum_attach_eq_fin (lf j) fun r hr ↦ (S.embG (branchSub (N j) (algebraMap C K (α j)))
          (branchSub_injective _ (hN j) _) r (S.root_of_mem (hlf j) hr) (u M)).order] at e1
        have e2 : ∑ i' : Fin (lf j).length, ((M * Γ j ((lf j).get i') : ℕ) : ℤ) =
            M * (N j * dΓ j) := by
          have := sum_attach_eq_fin (lf j) fun r _ ↦ ((M * Γ j r : ℕ) : ℤ)
          rw [← this, show ((lf j).attach.map fun r ↦ ((M * Γ j r.1 : ℕ) : ℤ)) =
            ((lf j).attach.map Subtype.val).map (fun r ↦ ((M * Γ j r : ℕ) : ℤ)) by
              rw [List.map_map]; rfl, List.attach_map_subtype_val]
          have h4 : ((lf j).map fun r ↦ ((M * Γ j r : ℕ) : ℤ)).sum =
              ((M * ((lf j).map (Γ j)).sum : ℕ) : ℤ) := by
            rw [← List.sum_map_mul_left, Nat.cast_list_sum, List.map_map]; rfl
          rw [h4, hdΓ j]; push_cast; ring
        simp only [Eα, oα, Finset.sum_sub_distrib]
        rw [e1]
        push_cast at e2 ⊢
        rw [e2]; ring
      have hle : Eα M j i ≤ ∑ i', Eα M j i' :=
        Finset.single_le_sum (fun i' _ ↦ hge i') (Finset.mem_univ i)
      have hj : S.muW (W M) mW (Q M) (algebraMap C K (α j)) - M * dΓ j ≤ n * s := by
        have := Finset.single_le_sum (fun j' (_ : j' ∈ Finset.univ) ↦ hX2 j') (Finset.mem_univ j)
        linarith
      refine ⟨hge i, hle.trans ?_⟩
      rw [hsumE]
      have hNB : (N j : ℤ) ≤ ∑ j', N j' + ∑ b ∈ Z0, Nb b + Ni := by
        have := Finset.single_le_sum (fun j' (_ : j' ∈ Finset.univ) ↦ Nat.zero_le (N j'))
          (Finset.mem_univ j)
        push_cast; linarith [(Finset.sum_nonneg fun b (_ : b ∈ Z0) ↦ (Nat.cast_nonneg (Nb b) : (0:ℤ) ≤ Nb b))]
      calc (N j : ℤ) * (S.muW (W M) mW (Q M) (algebraMap C K (α j)) - M * dΓ j)
          ≤ N j * (n * s) := mul_le_mul_of_nonneg_left hj (by positivity)
        _ ≤ (∑ j', N j' + ∑ b ∈ Z0, Nb b + Ni) * (n * s) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hNB) hBn
        _ = B := by rw [hB]; push_cast; ring
    · -- at the other points of `Z0`
      have hbA : (b : K) ∉ Set.range fun j ↦ algebraMap C K (α j) := fun h ↦
        (Finset.mem_sdiff.mp b.2).2 ((hAr b).mpr h)
      have hge : ∀ i', 0 ≤ Eb M b i' := fun i' ↦
        (hdiv M).2.1 b hbA (Nb (b : K)) (hNb (b : K)).ne' (lb (b : K)) (hlb (b : K)) _ (List.get_mem _ _)
      have hsumE : ∑ i', Eb M b i' = Nb (b : K) * S.muW (W M) mW (Q M) (b : K) := by
        have e1 := S.fibre_sum (u M) (hu0 M) (W M) (Q M) (hQ M) (hWQ M) mW le_rfl (Nb (b : K)) (hNb (b : K)) _
          (lb (b : K)) (hlb (b : K))
        rw [sum_attach_eq_fin (lb (b : K)) fun r hr ↦ (S.embG (branchSub (Nb (b : K)) (b : K))
          (branchSub_injective _ (hNb (b : K)) _) r (S.root_of_mem (hlb (b : K)) hr) (u M)).order] at e1
        exact e1
      have hμ : S.muW (W M) mW (Q M) (b : K) ≤ n * s := by
        by_cases hpos : 0 < S.muW (W M) mW (Q M) (b : K)
        · have hN0 := S.normW_ne_zero' hBr (u M) (hu0 M) (W M) (Q M) (hQ M) (hWQ M) mW le_rfl
          have hP0 : (S.normW (W M) mW * Q M).map (algebraMap C K) ≠ 0 :=
            (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr (mul_ne_zero hN0 (hQ M))
          have hbR : (b : K) ∈ R := by
            rw [hR, Finset.mem_sdiff, Multiset.mem_toFinset]
            refine ⟨?_, fun h ↦ hbA ((hAr b).mp h)⟩
            rw [mem_roots hP0, ← rootMultiplicity_pos hP0, Polynomial.map_mul,
              rootMultiplicity_mul (by rwa [← Polynomial.map_mul])]
            have : 0 < ((S.normW (W M) mW).map (algebraMap C K)).rootMultiplicity (b : K) := by
              unfold muW at hpos
              have : (0 : ℤ) ≤ S.F.natDegree *
                  (((Q M).map (algebraMap C K)).rootMultiplicity (b : K) : ℤ) := by
                positivity
              omega
            omega
          have := Finset.single_le_sum hX1 hbR
          linarith
        · linarith
      refine ⟨hge i, (Finset.single_le_sum (fun i' _ ↦ hge i') (Finset.mem_univ i)).trans ?_⟩
      rw [hsumE]
      have hNB : (Nb (b : K) : ℤ) ≤ ∑ j', N j' + ∑ b' ∈ Z0, Nb b' + Ni := by
        have := Finset.single_le_sum (fun b' (_ : b' ∈ Z0) ↦ Nat.zero_le (Nb b')) b.2
        push_cast; linarith [(Finset.sum_nonneg fun j' (_ : j' ∈ Finset.univ) ↦
          (Nat.cast_nonneg (N j') : (0:ℤ) ≤ N j'))]
      have hμ0 : 0 ≤ S.muW (W M) mW (Q M) (b : K) :=
        (S.mu_off α N hN lf hlf hBr _ _ (u M) (hu0 M) (hdiv M) (W M) (Q M) (hQ M) (hWQ M) mW le_rfl
          (b : K) hbA).1
      calc (Nb (b : K) : ℤ) * S.muW (W M) mW (Q M) (b : K) ≤ Nb (b : K) * (n * s) :=
            mul_le_mul_of_nonneg_left hμ (by positivity)
        _ ≤ (∑ j', N j' + ∑ b' ∈ Z0, Nb b' + Ni) * (n * s) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hNB) hBn
        _ = B := by rw [hB]; push_cast; ring
    · -- above infinity
      have hge : ∀ i', 0 ≤ Ei M i' := fun i' ↦ by
        have := (hdiv M).2.2 Ni hNi li hli _ (List.get_mem _ i')
        simp only [Ei, oi]; push_cast at this; linarith
      have hsumE : ∑ i', Ei M i' = Ni * (n * (M * c + s) - ((S.normW (W M) mW).natDegree -
          n * (Q M).natDegree)) := by
        have e1 := S.inf_sum (u M) (hu0 M) (W M) (Q M) (hQ M) (hWQ M) mW le_rfl Ni hNi' li hli
        rw [sum_attach_eq_fin li fun r hr ↦ (S.embG (infSub Ni) (infSub_injective _ hNi') r
          (S.root_of_mem hli hr) (u M)).order] at e1
        simp only [Ei, oi, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, hlen, nsmul_eq_mul]
        rw [e1]; ring
      refine ⟨hge i, (Finset.single_le_sum (fun i' _ ↦ hge i') (Finset.mem_univ i)).trans ?_⟩
      rw [hsumE]
      have hX3' : (n : ℤ) * (M * c + s) - ((S.normW (W M) mW).natDegree - n * (Q M).natDegree) ≤
          n * s := by linarith
      have hNB : (Ni : ℤ) ≤ ∑ j', N j' + ∑ b' ∈ Z0, Nb b' + Ni := by
        push_cast
        linarith [(Finset.sum_nonneg fun j' (_ : j' ∈ Finset.univ) ↦
          (Nat.cast_nonneg (N j') : (0:ℤ) ≤ N j')), (Finset.sum_nonneg fun b' (_ : b' ∈ Z0) ↦
          (Nat.cast_nonneg (Nb b') : (0:ℤ) ≤ Nb b'))]
      calc (Ni : ℤ) * (n * (M * c + s) - ((S.normW (W M) mW).natDegree - n * (Q M).natDegree))
          ≤ Ni * (n * s) := mul_le_mul_of_nonneg_left hX3' (by positivity)
        _ ≤ (∑ j', N j' + ∑ b' ∈ Z0, Nb b' + Ni) * (n * s) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hNB) hBn
        _ = B := by rw [hB]; push_cast; ring
  -- the pigeonhole
  let f : ℕ → ((j : J) → Fin (lf j).length → Fin (B + 1)) × ((b : Z0) → Fin (lb (b : K)).length →
      Fin (B + 1)) × (Fin li.length → Fin (B + 1)) := fun M ↦
    (fun j i ↦ ⟨min (Eα M j i).toNat B, by omega⟩, fun b i ↦ ⟨min (Eb M b i).toNat B, by omega⟩,
      fun i ↦ ⟨min (Ei M i).toNat B, by omega⟩)
  obtain ⟨M1, M2, hne, hfeq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hclamp : ∀ {x y : ℤ}, 0 ≤ x ∧ x ≤ B → 0 ≤ y ∧ y ≤ B → min x.toNat B = min y.toNat B →
      x = y := fun hx hy h ↦ by omega
  -- equal surpluses
  have hEq : ∀ {M1 M2}, f M1 = f M2 → (∀ j i, Eα M1 j i = Eα M2 j i) ∧
      (∀ b i, Eb M1 b i = Eb M2 b i) ∧ ∀ i, Ei M1 i = Ei M2 i := by
    intro M1 M2 h
    refine ⟨fun j i ↦ ?_, fun b i ↦ ?_, fun i ↦ ?_⟩
    · have := congrArg Fin.val (congrFun (congrFun (congrArg Prod.fst h) j) i)
      exact hclamp ((hbounds M1).1 j i) ((hbounds M2).1 j i) this
    · have := congrArg Fin.val (congrFun (congrFun (congrArg (fun z ↦ z.2.1) h) b) i)
      exact hclamp ((hbounds M1).2.1 b i) ((hbounds M2).2.1 b i) this
    · have := congrArg Fin.val (congrFun (congrArg (fun z ↦ z.2.2) h) i)
      exact hclamp ((hbounds M1).2.2 i) ((hbounds M2).2.2 i) this
  -- off `Γ` and off `Z0`, all the orders vanish
  have hzero : ∀ M (b : K), b ∉ Set.range (fun j ↦ algebraMap C K (α j)) → b ∉ Z0 →
      ∀ (N' : ℕ) (hN' : 0 < N') (l : List (LaurentSeries K))
        (hl : S.F.map (branchSub N' b) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries K) (hr : r ∈ l),
        (S.embG (branchSub N' b) (branchSub_injective N' hN' b) r (S.root_of_mem hl hr)
          (u M)).order = 0 := by
    intro M b hb hbZ N' hN' l hl r hr
    have h0 := (hdiv M).2.1 b hb N' hN'.ne' l hl r hr
    by_contra hne0
    have hpos := (S.mu_off α N hN lf hlf hBr _ _ (u M) (hu0 M) (hdiv M) (W M) (Q M) (hQ M)
      (hWQ M) _ le_rfl b hb).2 N' hN' l hl r hr (lt_of_le_of_ne h0 (Ne.symm hne0))
    have hfix := S.support_fixed α N hN lf hlf hφ hBr ⟨Ni, hNi, li, hlen, hli⟩ hα Γ dΓ hdΓ c hsumΓ
      M s (u M) (hu0 M) (hdiv M) (W M) (Q M) (hQ M) (hWQ M) _ le_rfl b hb hpos
    apply hbZ
    rw [hZ0, Finset.mem_sdiff, Set.Finite.mem_toFinset]
    exact ⟨hfix, fun h ↦ hb ((hAr b).mp h)⟩
  -- the conclusion from `M1 < M2`
  have key : ∀ M1 M2, M1 < M2 → f M1 = f M2 → ∃ m, 0 < m ∧ ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
      S.DivGE α N hN lf hlf (fun j r ↦ m * Γ j r) (m * c) γ := by
    intro M1 M2 hlt h
    obtain ⟨h1, h2, h3⟩ := hEq h
    refine ⟨M2 - M1, by omega, u M2 / u M1, div_ne_zero (hu0 M2) (hu0 M1), ?_, ?_, ?_⟩
    · -- at the points of `Γ`
      intro j r hr
      obtain ⟨i, rfl⟩ := List.get_of_mem hr
      rw [S.order_quot _ _ _ _ _ _ (hu0 M2) (hu0 M1)]
      have := h1 j i
      simp only [Eα, oα] at this
      push_cast [Nat.cast_sub hlt.le]
      linarith
    · -- off `Γ`
      intro b hb N' hN' l hl r hr
      rw [S.order_quot _ _ _ _ _ _ (hu0 M2) (hu0 M1)]
      by_cases hbZ : b ∈ Z0
      · obtain ⟨r0, hr0, htr⟩ := S.order_transfer b (Nb b) N' (hNb b) (Nat.pos_of_ne_zero hN')
          (lb b) l (hlb b) hl r hr
        obtain ⟨i, rfl⟩ := List.get_of_mem hr0
        have e2 := htr (u M2)
        have e1 := htr (u M1)
        have := h2 ⟨b, hbZ⟩ i
        simp only [Eb, ob] at this
        have hNb0 : (0 : ℤ) < Nb b := by exact_mod_cast hNb b
        have : (Nb b : ℤ) * ((S.embG (branchSub N' b) (branchSub_injective N' (Nat.pos_of_ne_zero hN') b) r
            (S.root_of_mem hl hr) (u M2)).order - (S.embG (branchSub N' b)
            (branchSub_injective N' (Nat.pos_of_ne_zero hN') b) r (S.root_of_mem hl hr) (u M1)).order) = 0 := by
          rw [mul_sub, e2, e1, ← mul_sub]
          rw [show (S.embG (branchSub (Nb b) b) (branchSub_injective (Nb b) (hNb b) b)
              ((lb b).get i) (S.root_of_mem (hlb b) (List.get_mem _ _)) (u M2)).order -
            (S.embG (branchSub (Nb b) b) (branchSub_injective (Nb b) (hNb b) b)
              ((lb b).get i) (S.root_of_mem (hlb b) (List.get_mem _ _)) (u M1)).order = 0 by
            linarith]
          ring
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hNb0.ne'
        · linarith
      · rw [hzero M2 b hb hbZ N' (Nat.pos_of_ne_zero hN') l hl r hr,
          hzero M1 b hb hbZ N' (Nat.pos_of_ne_zero hN') l hl r hr, sub_self]
    · -- above infinity
      intro N' hN' l hl r hr
      rw [S.order_quot _ _ _ _ _ _ (hu0 M2) (hu0 M1)]
      obtain ⟨r0, hr0, htr⟩ := S.order_transfer_inf Ni N' hNi' (Nat.pos_of_ne_zero hN') li l hli hl
        r hr
      obtain ⟨i, rfl⟩ := List.get_of_mem hr0
      have e2 := htr (u M2)
      have e1 := htr (u M1)
      have := h3 i
      simp only [Ei, oi] at this
      have hNi0 : (0 : ℤ) < Ni := by exact_mod_cast hNi'
      have hd : (Ni : ℤ) * ((S.embG (infSub N') (infSub_injective N' (Nat.pos_of_ne_zero hN')) r (S.root_of_mem hl hr)
          (u M2)).order - (S.embG (infSub N') (infSub_injective N' (Nat.pos_of_ne_zero hN')) r (S.root_of_mem hl hr)
          (u M1)).order) = Ni * (-(N' * ((M2 - M1 : ℕ) * c : ℕ) : ℤ)) := by
        rw [mul_sub, e2, e1]
        push_cast [Nat.cast_sub hlt.le]
        linear_combination (-(N' : ℤ)) * this
      have := mul_left_cancel₀ hNi0.ne' hd
      rw [this]
      push_cast
      exact le_refl _
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key M1 M2 hlt hfeq
  · exact key M2 M1 hlt hfeq.symm

end Main

end CurveData

end Fibre

end Curves
