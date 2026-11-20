import RischTragerBronstein.Mixed.NKMultiData
import RischTragerBronstein.Mixed.NKSplitShape
import RischTragerBronstein.Mixed.KXSem

/-!
# Several slopes at infinity: the code check

`multiShapeC Pp segs`: for `θⁿ + ∑ aᵢ θⁱ = 0` and segments `(sₖ, K₀ₖ, cₖ, Γₖ)` with strictly
decreasing integer slopes, `deg aᵢ + i sₖ ≤ K₀ₖ`, the residual polynomial
`∑ᵢ [aᵢ]_{K₀ₖ − i sₖ} Zⁱ = cₖ Z^{loₖ} ∏_{γ ∈ Γₖ} (Z − γ)` (`loₖ` the number of roots of the later
segments), `cₖ ≠ 0`, the codes of `Γₖ` with distinct non-zero values and `∑ₖ |Γₖ| = n`
(`multiShape_spec`): the data of `multi_hdata`, hence of `multi_gauge`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}

section Codes

variable (Fc ks)

/-- The integer-indexed coefficient of a polynomial code. -/
def coeffZC (m : ℕ) (p : GPoly (LC m)) (j : ℤ) : LC m :=
  if 0 ≤ j then p.getD j.toNat (MO Fc ks m).zero else (MO Fc ks m).zero

/-- The coefficient `aᵢ` (with `aₙ = 1`). -/
def coefC (m : ℕ) (Pp : List (GPoly (LC m))) (i : ℕ) : GPoly (LC m) :=
  if i < Pp.length then Pp.getD i [] else [(MO Fc ks m).one]

/-- The residual polynomial `∑ᵢ [aᵢ]_{K₀ − i s} Zⁱ` on codes. -/
def residC (m : ℕ) (Pp : List (GPoly (LC m))) (s K0 : ℤ) : GPoly (LC m) :=
  (List.range (Pp.length + 1)).map fun i ↦ coeffZC Fc ks m (coefC Fc ks m Pp i) (K0 - i * s)

/-- `c Z^{lo} ∏ (Z − γ)` on codes. -/
def targetC (m : ℕ) (lo : ℕ) (c : LC m) (γs : List (LC m)) : GPoly (LC m) :=
  GPoly.mul (MO Fc ks m) [c] (GPoly.mul (MO Fc ks m) (monoG Fc ks m lo) (prodXG Fc ks m γs))

/-- A segment: slope, `K₀`, leading constant, residual roots. -/
abbrev SegC (m : ℕ) := ℤ × ℤ × LC m × List (LC m)

/-- The default segment. -/
def segD (m : ℕ) : SegC m := (0, 0, (MO Fc ks m).zero, [])

/-- The number of roots of the segments after `k`. -/
def loC {m : ℕ} (segs : List (SegC m)) (k : ℕ) : ℕ :=
  ((segs.drop (k + 1)).map fun sg ↦ sg.2.2.2.length).sum

/-- **The shape check for several slopes at infinity.** -/
def multiShapeC (m : ℕ) (Pp : List (GPoly (LC m))) (segs : List (SegC m)) : Bool :=
  let O := MO Fc ks m
  let n := Pp.length
  decide (0 < n) && decide (0 < segs.length) &&
  decide ((segs.map fun sg ↦ sg.2.2.2.length).sum = n) &&
  (List.range (segs.length - 1)).all (fun k ↦
    decide ((segs.getD (k + 1) (segD Fc ks m)).1 < (segs.getD k (segD Fc ks m)).1)) &&
  (List.range segs.length).all fun k ↦
    let sg := segs.getD k (segD Fc ks m)
    ((List.range n).all fun i ↦ (List.range (Pp.getD i []).length).all fun j ↦
      decide ((j : ℤ) + i * sg.1 ≤ sg.2.1) || O.isZero ((Pp.getD i []).getD j O.zero)) &&
    decide ((n : ℤ) * sg.1 ≤ sg.2.1) &&
    GPoly.isZero O (GPoly.sub O (residC Fc ks m Pp sg.1 sg.2.1)
      (targetC Fc ks m (loC segs k) sg.2.2.1 sg.2.2.2)) &&
    !O.isZero sg.2.2.1 &&
    (List.range sg.2.2.2.length).all fun a ↦ !O.isZero (sg.2.2.2.getD a O.zero) &&
      (List.range sg.2.2.2.length).all fun b ↦
        decide (a = b) || !O.isZero (O.add (sg.2.2.2.getD a O.zero) (O.neg (sg.2.2.2.getD b O.zero)))

end Codes

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

section Sem

variable (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m)))

lemma sem_coeffZC (p : GPoly (LC m)) (j : ℤ) :
    (T.MP m h).sem (coeffZC Fc ks m p j) = coeffZ (GPoly.toPoly (T.MP m h) p) j := by
  unfold coeffZC coeffZ
  split_ifs
  · rw [coeff_toPoly_sem]
  · exact (T.MP m h).sem_zero

lemma nkF_coeff_coefC (i : ℕ) (hi : i ≤ Pp.length) :
    (T.nkF m h Pp).coeff i = GPoly.toPoly (T.MP m h) (coefC Fc ks m Pp i) := by
  unfold coefC
  split_ifs with hlt
  · rw [nkF, polyF_coeff _ _ _ hlt]
  · have hin : i = Pp.length := by omega
    subst hin
    have hmon := polyF_monic (fun i ↦ GPoly.toPoly (T.MP m h) (Pp.getD i [])) Pp.length
    have hdeg := polyF_natDegree (fun i ↦ GPoly.toPoly (T.MP m h) (Pp.getD i [])) Pp.length
    rw [show (T.nkF m h Pp).coeff Pp.length = 1 by
      rw [← hdeg]; exact hmon.coeff_natDegree]
    simp [GPoly.toPoly, (T.MP m h).sem_one]

lemma toPoly_residC (s K0 : ℤ) :
    GPoly.toPoly (T.MP m h) (residC Fc ks m Pp s K0) =
      ∑ i ∈ Finset.range ((T.nkF m h Pp).natDegree + 1),
        Polynomial.C (coeffZ ((T.nkF m h Pp).coeff i) (K0 - i * s)) * X ^ i := by
  have hFn : (T.nkF m h Pp).natDegree = Pp.length := polyF_natDegree _ _
  ext j
  rw [coeff_toPoly_sem, finsetSum_coeff, hFn]
  simp only [coeff_C_mul_X_pow]
  by_cases hj : j < Pp.length + 1
  · rw [Finset.sum_eq_single j (fun b _ hb ↦ by rw [if_neg (Ne.symm hb)])
      (fun h' ↦ absurd (Finset.mem_range.mpr hj) h'), if_pos rfl, residC,
      List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range,
      T.sem_coeffZC m h, T.nkF_coeff_coefC m h Pp j (by omega)]
  · rw [Finset.sum_eq_zero fun b hb ↦ by
      rw [if_neg (by have := Finset.mem_range.mp hb; omega)], residC,
      List.getD_eq_default _ _ (by simp; omega), (T.MP m h).sem_zero]

lemma toPoly_targetC (lo : ℕ) (c : LC m) (γs : List (LC m)) :
    GPoly.toPoly (T.MP m h) (targetC Fc ks m lo c γs) =
      Polynomial.C ((T.MP m h).sem c) * X ^ lo *
        (γs.map fun g ↦ X - Polynomial.C ((T.MP m h).sem g)).prod := by
  rw [targetC, GPoly.toPoly_mul, GPoly.toPoly_mul, T.toPoly_monoG m h, T.toPoly_prodXG m h]
  simp [GPoly.toPoly, mul_assoc]

end Sem

lemma loC_last {m : ℕ} (segs : List (SegC m)) (q : ℕ) (hq : segs.length = q + 1) : loC segs q = 0 := by
  rw [loC, List.drop_eq_nil_of_le (by omega)]
  rfl

lemma loC_succ {m : ℕ} (segs : List (SegC m)) (k : ℕ) (hk : k + 1 < segs.length) (d : SegC m) :
    loC segs k = loC segs (k + 1) + (segs.getD (k + 1) d).2.2.2.length := by
  rw [loC, loC, List.drop_eq_getElem_cons hk, List.map_cons, List.sum_cons,
    List.getD_eq_getElem _ _ hk]
  ring

lemma loC_zero {m : ℕ} (segs : List (SegC m)) (h0 : 0 < segs.length) (d : SegC m) :
    loC segs 0 + (segs.getD 0 d).2.2.2.length = (segs.map fun sg ↦ sg.2.2.2.length).sum := by
  obtain ⟨sg, rest, rfl⟩ : ∃ sg rest, segs = sg :: rest := by
    cases segs with
    | nil => simp at h0
    | cons a l => exact ⟨a, l, rfl⟩
  simp [loC]
  ring

/-- **The meaning of the shape check for several slopes.** -/
lemma multiShape_spec (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m))) (segs : List (SegC m))
    (hms : multiShapeC Fc ks m Pp segs = true) :
    ∃ q, segs.length = q + 1 ∧ 0 < Pp.length ∧
      StrictAnti (fun k : Fin (q + 1) ↦ (segs.getD k (segD Fc ks m)).1) ∧
      (∀ k : Fin (q + 1), (T.MP m h).sem (segs.getD k (segD Fc ks m)).2.2.1 ≠ 0) ∧
      (∀ k : Fin (q + 1), (((segs.getD k (segD Fc ks m)).2.2.2).map (T.MP m h).sem).Nodup ∧
        (0 : T.F m) ∉ ((segs.getD k (segD Fc ks m)).2.2.2).map (T.MP m h).sem) ∧
      (∀ k : Fin (q + 1), ∀ i ≤ (T.nkF m h Pp).natDegree, (T.nkF m h Pp).coeff i ≠ 0 →
        (((T.nkF m h Pp).coeff i).natDegree : ℤ) + i * (segs.getD k (segD Fc ks m)).1 ≤
          (segs.getD k (segD Fc ks m)).2.1) ∧
      (∀ k : Fin (q + 1), ∑ i ∈ Finset.range ((T.nkF m h Pp).natDegree + 1),
        Polynomial.C (coeffZ ((T.nkF m h Pp).coeff i)
          ((segs.getD k (segD Fc ks m)).2.1 - i * (segs.getD k (segD Fc ks m)).1)) * X ^ i =
        Polynomial.C ((T.MP m h).sem (segs.getD k (segD Fc ks m)).2.2.1) * X ^ (loC segs k) *
          (((segs.getD k (segD Fc ks m)).2.2.2.map (T.MP m h).sem).map
            fun γ ↦ X - Polynomial.C γ).prod) ∧
      loC segs 0 + ((segs.getD 0 (segD Fc ks m)).2.2.2.map (T.MP m h).sem).length =
        (T.nkF m h Pp).natDegree ∧
      (∀ k : Fin q, loC segs k.castSucc = loC segs k.succ +
        ((segs.getD k.succ (segD Fc ks m)).2.2.2.map (T.MP m h).sem).length) ∧
      loC segs (Fin.last q) = 0 := by
  classical
  have hFn : (T.nkF m h Pp).natDegree = Pp.length := polyF_natDegree _ _
  unfold multiShapeC at hms
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hms
  obtain ⟨⟨⟨⟨hn0, hs0⟩, hsum⟩, hdec⟩, hseg⟩ := hms
  obtain ⟨q, hq⟩ : ∃ q, segs.length = q + 1 := ⟨segs.length - 1, by omega⟩
  refine ⟨q, hq, hn0, ?_, fun k ↦ ?_, fun k ↦ ?_, fun k i hi hai ↦ ?_, fun k ↦ ?_, ?_, fun k ↦ ?_,
    loC_last segs q hq⟩
  · -- strictly decreasing slopes
    rw [Fin.strictAnti_iff_succ_lt]
    intro k
    have := hdec k (by have := k.2; omega)
    simpa using this
  · -- `c ≠ 0`
    obtain ⟨⟨⟨⟨-, -⟩, -⟩, hc⟩, -⟩ := hseg k (by omega)
    intro h0
    have : (MO Fc ks m).isZero (segs.getD k (segD Fc ks m)).2.2.1 = true :=
      ((T.MP m h).isZero_iff _).mpr h0
    rw [this] at hc
    exact Bool.noConfusion hc
  · -- the residual roots
    obtain ⟨-, hγ⟩ := hseg k (by omega)
    set γs := (segs.getD k (segD Fc ks m)).2.2.2 with hγs
    have hne : ∀ a < γs.length, (T.MP m h).sem (γs.getD a (MO Fc ks m).zero) ≠ 0 := by
      intro a ha h0
      have h1 := (hγ a ha).1
      rw [((T.MP m h).isZero_iff _).mpr h0] at h1
      exact Bool.noConfusion h1
    have hdist : ∀ a < γs.length, ∀ b < γs.length, (T.MP m h).sem (γs.getD a (MO Fc ks m).zero) =
        (T.MP m h).sem (γs.getD b (MO Fc ks m).zero) → a = b := by
      intro a ha b hb hab
      rcases Bool.or_eq_true_iff.mp ((hγ a ha).2 b hb) with h1 | h1
      · exact of_decide_eq_true h1
      · have h2 : (MO Fc ks m).isZero ((MO Fc ks m).add (γs.getD a (MO Fc ks m).zero)
            ((MO Fc ks m).neg (γs.getD b (MO Fc ks m).zero))) = true := by
          rw [(T.MP m h).isZero_iff, (T.MP m h).sem_add, (T.MP m h).sem_neg, hab, add_neg_cancel]
        rw [h2] at h1
        exact Bool.noConfusion h1
    refine ⟨?_, fun h0 ↦ ?_⟩
    · rw [List.nodup_iff_injective_get]
      intro a b hab
      simp only [List.get_eq_getElem, List.getElem_map] at hab
      have ha : (a : ℕ) < γs.length := by simpa using a.2
      have hb : (b : ℕ) < γs.length := by simpa using b.2
      rw [← List.getD_eq_getElem _ (MO Fc ks m).zero ha,
        ← List.getD_eq_getElem _ (MO Fc ks m).zero hb] at hab
      exact Fin.ext (hdist _ ha _ hb hab)
    · obtain ⟨g, hg, hg0⟩ := List.mem_map.mp h0
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hg
      exact hne a ha (by rw [List.getD_eq_getElem _ _ ha]; exact hg0)
  · -- the bound
    obtain ⟨⟨⟨⟨hbd, hnK⟩, -⟩, -⟩, -⟩ := hseg k (by omega)
    rw [hFn] at hi
    rcases lt_or_eq_of_le hi with hi | hi
    · have hcoef : (T.nkF m h Pp).coeff i = GPoly.toPoly (T.MP m h) (Pp.getD i []) := by
        rw [nkF, polyF_coeff _ _ _ hi]
      rw [hcoef] at hai ⊢
      set d := (GPoly.toPoly (T.MP m h) (Pp.getD i [])).natDegree with hd
      have hcd : (GPoly.toPoly (T.MP m h) (Pp.getD i [])).coeff d ≠ 0 :=
        leadingCoeff_ne_zero.mpr hai
      rw [coeff_toPoly_sem] at hcd
      have hdl : d < (Pp.getD i []).length := by
        by_contra hdl
        push Not at hdl
        exact hcd (by rw [List.getD_eq_default _ _ hdl, (T.MP m h).sem_zero])
      rcases Bool.or_eq_true_iff.mp (hbd i hi d hdl) with h1 | h1
      · exact of_decide_eq_true h1
      · exact absurd (((T.MP m h).isZero_iff _).mp h1) hcd
    · subst hi
      have hmon := polyF_monic (fun i ↦ GPoly.toPoly (T.MP m h) (Pp.getD i [])) Pp.length
      have h1 : (T.nkF m h Pp).coeff Pp.length = 1 := by
        rw [← hFn]; exact hmon.coeff_natDegree
      rw [h1, natDegree_one]
      push_cast
      linarith
  · -- the residual identity
    obtain ⟨⟨⟨-, hres⟩, -⟩, -⟩ := hseg k (by omega)
    have h1 := (GPoly.isZero_iff (T.MP m h) _).mp hres
    rw [GPoly.toPoly_sub, sub_eq_zero, T.toPoly_residC m h Pp, T.toPoly_targetC m h] at h1
    rw [h1, List.map_map]
    rfl
  · -- the top
    rw [List.length_map, loC_zero segs hs0 (segD Fc ks m), hsum, hFn]
  · -- the chain
    rw [List.length_map]
    exact loC_succ segs k (by have := k.2; simp; omega) (segD Fc ks m)


end MTower

end Curves.MT
