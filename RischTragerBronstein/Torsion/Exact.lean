import RischTragerBronstein.Torsion.Degree

/-!
# Exact divisors from lower bounds (any characteristic)

For `u = W(x, y)/Q(x)` on a curve over an algebraically closed `K`: if the orders of `u` along
complete branch systems above the points of a finite set `T` (containing the roots of `Q`) and above
infinity are bounded below by `z`, the normalized bounds are integers, and they add up to `0`, then
all the bounds are attained and `W(x, y)` has no zeros outside `T` (`exact_divisor`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Exact

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]

lemma sum_rootMultiplicity_le (P : K[X]) (T : Finset K) :
    ∑ a ∈ T, (P.rootMultiplicity a : ℤ) ≤ P.natDegree := by
  classical
  by_cases hP : P = 0
  · simp [hP]
  have h1 : ∑ a ∈ T, P.rootMultiplicity a = (P.roots.filter (· ∈ T)).card := by
    rw [← Multiset.sum_count_eq_card (s := T) (m := P.roots.filter (· ∈ T))
      (fun a ha ↦ (Multiset.mem_filter.mp ha).2)]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [Multiset.count_filter_of_pos ha, count_roots]
  have h2 : (P.roots.filter (· ∈ T)).card ≤ P.natDegree :=
    (Multiset.card_le_card (Multiset.filter_le _ _)).trans (card_roots' P)
  exact_mod_cast (h1 ▸ h2 : ∑ a ∈ T, P.rootMultiplicity a ≤ P.natDegree)

lemma sum_rootMultiplicity_eq (P : K[X]) (hP : P ≠ 0) (T : Finset K)
    (hT : ∀ a, P.IsRoot a → a ∈ T) :
    ∑ a ∈ T, (P.rootMultiplicity a : ℤ) = P.natDegree := by
  classical
  have h1 : ∑ a ∈ T, P.rootMultiplicity a = P.roots.card := by
    rw [← Multiset.sum_count_eq_card (s := T) (m := P.roots)
      (fun a ha ↦ hT a ((mem_roots hP).mp ha))]
    exact Finset.sum_congr rfl fun a _ ↦ (count_roots P).symm
  rw [← IsAlgClosed.card_roots_eq_natDegree (k := K)]
  exact_mod_cast h1

lemma rootMultiplicity_zero_of_sum (P : K[X]) (hP : P ≠ 0) (T : Finset K)
    (h : ∑ a ∈ T, (P.rootMultiplicity a : ℤ) = P.natDegree) (a : K) (ha : a ∉ T) :
    P.rootMultiplicity a = 0 := by
  classical
  by_contra h0
  have h1 : ∑ b ∈ insert a T, (P.rootMultiplicity b : ℤ) ≤ P.natDegree :=
    sum_rootMultiplicity_le P (insert a T)
  rw [Finset.sum_insert ha, h] at h1
  have : (0 : ℤ) < P.rootMultiplicity a := by exact_mod_cast Nat.pos_of_ne_zero h0
  omega

lemma list_sum_map_sub' {α : Type*} (l : List α) (f : α → ℤ) (c : ℤ) :
    (l.map fun r ↦ f r - c).sum = (l.map f).sum - l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

lemma list_sum_map_add' {α : Type*} (l : List α) (f : α → ℤ) (c : ℤ) :
    (l.map fun r ↦ f r + c).sum = (l.map f).sum + l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

lemma list_eq_of_sum_eq {α : Type*} (l : List α) (f g : α → ℤ) (h : ∀ r ∈ l, f r ≤ g r)
    (hs : (l.map f).sum = (l.map g).sum) : ∀ r ∈ l, f r = g r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons] at hs
    have ha := h a List.mem_cons_self
    have hl : (l.map f).sum ≤ (l.map g).sum :=
      List.sum_le_sum fun r hr ↦ h r (List.mem_cons_of_mem _ hr)
    have e1 : f a = g a := by omega
    have e2 : (l.map f).sum = (l.map g).sum := by omega
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact e1
    · exact ih (fun r hr ↦ h r (List.mem_cons_of_mem _ hr)) e2 r hr

namespace CurveData

variable (S : CurveData C L)

/-- **Exact divisors**: lower bounds of total degree `0` are attained. -/
theorem exact_divisor (W : C[X][X]) (m : ℕ) (hWm : W.natDegree ≤ m) (hW : S.evXY W ≠ 0)
    (Q : C[X]) (hQ : Q ≠ 0) (T : Finset K)
    (hQT : ∀ a, (Q.map (algebraMap C K)).IsRoot a → a ∈ T)
    (Nf : K → ℕ) (hNf : ∀ a, 0 < Nf a) (lf : K → List (LaurentSeries K))
    (hlf : ∀ a ∈ T, S.F.map (branchSub (Nf a) a) = ((lf a).map fun r ↦ X - Polynomial.C r).prod)
    (z : K → LaurentSeries K → ℤ)
    (hz : ∀ a ∈ T, ∀ r ∈ lf a, z a r ≤ ((W.map (branchSub (Nf a) a)).eval r).order -
      Nf a * ((Q.map (algebraMap C K)).rootMultiplicity a : ℤ))
    (Ni : ℕ) (hNi : 0 < Ni) (li : List (LaurentSeries K))
    (hli : S.F.map (infSub Ni) = (li.map fun r ↦ X - Polynomial.C r).prod)
    (zi : LaurentSeries K → ℤ)
    (hzi : ∀ r ∈ li, zi r ≤ ((W.map (infSub Ni)).eval r).order + Ni * (Q.natDegree : ℤ))
    (d : K → ℤ) (hd : ∀ a ∈ T, ((lf a).map (z a)).sum = Nf a * d a) (di : ℤ)
    (hdi : (li.map zi).sum = Ni * di) (hsum : ∑ a ∈ T, d a + di = 0) :
    (∀ a ∈ T, ∀ r ∈ lf a, z a r = ((W.map (branchSub (Nf a) a)).eval r).order -
      Nf a * ((Q.map (algebraMap C K)).rootMultiplicity a : ℤ)) ∧
    (∀ r ∈ li, zi r = ((W.map (infSub Ni)).eval r).order + Ni * (Q.natDegree : ℤ)) ∧
    (∀ a ∉ T, ((S.normW W m).map (algebraMap C K)).rootMultiplicity a = 0) := by
  classical
  set n := S.F.natDegree with hn
  set P := (S.normW W m).map (algebraMap C K) with hP
  have hPne : P ≠ 0 := by
    have := S.normW_ne_zero (K := K) W m hWm hW _ (infSub_injective Ni hNi) li hli
    rw [hP, Ne, Polynomial.map_eq_zero_iff (algebraMap C K).injective]; exact this
  have hPdeg : P.natDegree = (S.normW W m).natDegree :=
    natDegree_map_eq_of_injective (algebraMap C K).injective _
  set QK := Q.map (algebraMap C K) with hQK
  have hQK0 : QK ≠ 0 := by rw [hQK, Ne, Polynomial.map_eq_zero_iff (algebraMap C K).injective]; exact hQ
  have hQdeg : QK.natDegree = Q.natDegree := natDegree_map_eq_of_injective (algebraMap C K).injective _
  -- the actual normalized orders
  set du : K → ℤ := fun a ↦ (P.rootMultiplicity a : ℤ) - n * (QK.rootMultiplicity a : ℤ) with hdu
  have hsumfin : ∀ a ∈ T, ((lf a).map fun r ↦ ((W.map (branchSub (Nf a) a)).eval r).order -
      Nf a * (QK.rootMultiplicity a : ℤ)).sum = Nf a * du a := by
    intro a ha
    have h1 := S.sum_order_fin W m hWm hW (Nf a) (hNf a) a (lf a) (hlf a ha)
    have hlen := S.length_of_split (hlf a ha)
    rw [list_sum_map_sub', h1, hlen]
    simp only [hdu, hP, hQK, hn]; ring
  have hsuminf : (li.map fun r ↦ ((W.map (infSub Ni)).eval r).order + Ni * (Q.natDegree : ℤ)).sum =
      Ni * (-(P.natDegree : ℤ) + n * Q.natDegree) := by
    have h1 := S.sum_order_inf W m hWm hW Ni hNi li hli
    have hlen := S.length_of_split hli
    rw [list_sum_map_add', h1, hlen, hPdeg]; ring
  have hle : ∀ a ∈ T, d a ≤ du a := by
    intro a ha
    have h1 : ((lf a).map (z a)).sum ≤ ((lf a).map fun r ↦ ((W.map (branchSub (Nf a) a)).eval r).order -
        Nf a * (QK.rootMultiplicity a : ℤ)).sum := List.sum_le_sum fun r hr ↦ hz a ha r hr
    rw [hd a ha, hsumfin a ha] at h1
    have hN : (0 : ℤ) < Nf a := by exact_mod_cast hNf a
    exact le_of_mul_le_mul_left h1 hN
  have hlei : di ≤ -(P.natDegree : ℤ) + n * Q.natDegree := by
    have h1 : (li.map zi).sum ≤ (li.map fun r ↦ ((W.map (infSub Ni)).eval r).order +
        Ni * (Q.natDegree : ℤ)).sum := List.sum_le_sum fun r hr ↦ hzi r hr
    rw [hdi, hsuminf] at h1
    have hN : (0 : ℤ) < Ni := by exact_mod_cast hNi
    exact le_of_mul_le_mul_left h1 hN
  have hQsum := sum_rootMultiplicity_eq QK hQK0 T hQT
  have hPsum := sum_rootMultiplicity_le P T
  have htot : ∑ a ∈ T, du a + (-(P.natDegree : ℤ) + n * Q.natDegree) =
      ∑ a ∈ T, (P.rootMultiplicity a : ℤ) - P.natDegree := by
    simp only [hdu, Finset.sum_sub_distrib, ← Finset.mul_sum, hQsum, hQdeg]; ring
  have hsumle : ∑ a ∈ T, d a ≤ ∑ a ∈ T, du a := Finset.sum_le_sum hle
  have hPeq : ∑ a ∈ T, (P.rootMultiplicity a : ℤ) = P.natDegree := by linarith
  have hTeq : ∑ a ∈ T, d a = ∑ a ∈ T, du a := by linarith
  have hdeq : ∀ a ∈ T, d a = du a := by
    intro a ha
    by_contra hne
    have hlt : d a < du a := lt_of_le_of_ne (hle a ha) hne
    have := Finset.sum_lt_sum hle ⟨a, ha, hlt⟩
    linarith
  have hdieq : di = -(P.natDegree : ℤ) + n * Q.natDegree := by linarith
  refine ⟨fun a ha ↦ list_eq_of_sum_eq _ _ _ (hz a ha) (by rw [hd a ha, hsumfin a ha, hdeq a ha]),
    list_eq_of_sum_eq _ _ _ hzi (by rw [hdi, hsuminf, hdieq]), fun a ha ↦ ?_⟩
  exact rootMultiplicity_zero_of_sum P hPne T hPeq a ha

end CurveData

end Exact

end Curves
