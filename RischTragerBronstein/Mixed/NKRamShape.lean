import RischTragerBronstein.Mixed.NKSplitShape
import RischTragerBronstein.Mixed.NKRamUnits

/-!
# Ramified places at infinity: the code check

`ramShapeC Pp e s' γs`: a single slope `s'/e` at infinity (`gcd(s', e) = 1`, `e ∣ n`): the
coefficients `aᵢ` of `θⁿ + ∑ aᵢ θⁱ` have `e deg aᵢ ≤ (n − i) s'`, the leading polynomial of weight
`s'/e` is `∏ₖ (Zᵉ − γₖ)` and the codes `γₖ` (`k < n/e`) have distinct non-zero values
(`ramShape_spec`). The curve then has `n/e` places at infinity, each of ramification `e`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}

section Codes

variable (Fc ks)

/-- The leading polynomial of weight `s'/e` on codes. -/
def leadPolyRC (m : ℕ) (Pp : List (GPoly (LC m))) (e s' : ℕ) : GPoly (LC m) :=
  ((List.range Pp.length).map fun i ↦
    if e ∣ s' * (Pp.length - i) then (Pp.getD i []).getD (s' * (Pp.length - i) / e) (MO Fc ks m).zero
    else (MO Fc ks m).zero) ++ [(MO Fc ks m).one]

/-- `Zᵉ − γ` on codes. -/
def powSubG (m e : ℕ) (g : LC m) : GPoly (LC m) :=
  (MO Fc ks m).neg g :: (List.replicate (e - 1) (MO Fc ks m).zero ++ [(MO Fc ks m).one])

/-- `∏ₖ (Zᵉ − γₖ)` on codes. -/
def prodPowXG (m e : ℕ) (γs : List (LC m)) : GPoly (LC m) :=
  γs.foldr (fun g acc ↦ GPoly.mul (MO Fc ks m) (powSubG Fc ks m e g) acc) [(MO Fc ks m).one]

/-- **The ramified shape check.** -/
def ramShapeC (m : ℕ) (Pp : List (GPoly (LC m))) (e s' : ℕ) (γs : List (LC m)) : Bool :=
  let O := MO Fc ks m
  let n := Pp.length
  decide (0 < n) && decide (0 < e) && decide (n % e = 0) && Nat.gcd s' e == 1 &&
  decide (γs.length = n / e) &&
  ((List.range n).all fun i ↦ (List.range (Pp.getD i []).length).all fun k ↦
    decide (e * k ≤ s' * (n - i)) || O.isZero ((Pp.getD i []).getD k O.zero)) &&
  GPoly.isZero O (GPoly.sub O (leadPolyRC Fc ks m Pp e s') (prodPowXG Fc ks m e γs)) &&
  ((List.range (n / e)).all fun k ↦ !O.isZero (γs.getD k O.zero) &&
    (List.range (n / e)).all fun l ↦
      decide (k = l) || !O.isZero (O.add (γs.getD k O.zero) (O.neg (γs.getD l O.zero))))

end Codes

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma toPoly_powSubG (m : ℕ) (h : T.Tr m) (e : ℕ) (he : 0 < e) (g : LC m) :
    GPoly.toPoly (T.MP m h) (powSubG Fc ks m e g) = X ^ e - Polynomial.C ((T.MP m h).sem g) := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_lt he
  simp only [zero_add, powSubG, Nat.add_sub_cancel, GPoly.toPoly_cons, (T.MP m h).sem_neg, C_neg]
  have : ∀ k : ℕ, GPoly.toPoly (T.MP m h) (List.replicate k (MO Fc ks m).zero ++ [(MO Fc ks m).one]) =
      X ^ k := by
    intro k
    induction k with
    | zero => simp [GPoly.toPoly, (T.MP m h).sem_one]
    | succ k ih =>
      rw [List.replicate_succ, List.cons_append, GPoly.toPoly_cons, ih, (T.MP m h).sem_zero, C_0,
        zero_add, pow_succ, mul_comm]
  rw [this, pow_succ, mul_comm X]
  ring

lemma toPoly_prodPowXG (m : ℕ) (h : T.Tr m) (e : ℕ) (he : 0 < e) (γs : List (LC m)) :
    GPoly.toPoly (T.MP m h) (prodPowXG Fc ks m e γs) =
      (γs.map fun g ↦ X ^ e - Polynomial.C ((T.MP m h).sem g)).prod := by
  induction γs with
  | nil => simp [prodPowXG, GPoly.toPoly, (T.MP m h).sem_one]
  | cons g γs ih =>
    rw [prodPowXG, List.foldr_cons, GPoly.toPoly_mul, ← prodPowXG, ih, List.map_cons,
      List.prod_cons, T.toPoly_powSubG m h e he]

/-- **The meaning of the ramified shape check.** -/
lemma ramShape_spec (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m))) (e s' : ℕ) (γs : List (LC m))
    (hsh : ramShapeC Fc ks m Pp e s' γs = true) :
    0 < Pp.length ∧ 0 < e ∧ e ∣ Pp.length ∧ Nat.Coprime s' e ∧ γs.length = Pp.length / e ∧
    (∀ i < (T.nkF m h Pp).natDegree, e * ((T.nkF m h Pp).coeff i).natDegree ≤
      s' * ((T.nkF m h Pp).natDegree - i)) ∧
    leadPolyR e s' (T.nkF m h Pp) =
      ∏ k : Fin (Pp.length / e), (X ^ e - Polynomial.C ((T.MP m h).sem (γs.getD k (MO Fc ks m).zero))) ∧
    Function.Injective (fun k : Fin (Pp.length / e) ↦ (T.MP m h).sem (γs.getD k (MO Fc ks m).zero)) ∧
    ∀ k : Fin (Pp.length / e), (T.MP m h).sem (γs.getD k (MO Fc ks m).zero) ≠ 0 := by
  classical
  unfold ramShapeC at hsh
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hsh
  obtain ⟨⟨⟨⟨⟨⟨⟨hn0, he0⟩, hdvd⟩, hcop⟩, hlen⟩, hdeg⟩, hlead⟩, hdist⟩ := hsh
  have hFn : (T.nkF m h Pp).natDegree = Pp.length := polyF_natDegree _ _
  refine ⟨hn0, he0, Nat.dvd_of_mod_eq_zero hdvd, hcop, hlen, fun i hi ↦ ?_, ?_, ?_, fun k ↦ ?_⟩
  · rw [hFn] at hi ⊢
    rw [nkF, polyF_coeff _ _ _ hi]
    by_cases hz : GPoly.toPoly (T.MP m h) (Pp.getD i []) = 0
    · rw [hz, natDegree_zero, mul_zero]; exact Nat.zero_le _
    · set d := (GPoly.toPoly (T.MP m h) (Pp.getD i [])).natDegree with hd
      have hcd : (GPoly.toPoly (T.MP m h) (Pp.getD i [])).coeff d ≠ 0 :=
        leadingCoeff_ne_zero.mpr hz
      rw [coeff_toPoly_sem] at hcd
      rcases hdeg i hi d (by
        by_contra hge
        rw [List.getD_eq_default _ _ (by omega), (T.MP m h).sem_zero] at hcd
        exact hcd rfl) with h1 | h1
      · exact h1
      · exact absurd (((T.MP m h).isZero_iff _).mp h1) hcd
  · have h1 := (GPoly.isZero_iff (T.MP m h) _).mp hlead
    rw [GPoly.toPoly_sub, sub_eq_zero, T.toPoly_prodPowXG m h e he0] at h1
    have hprod : (γs.map fun g ↦ X ^ e - Polynomial.C ((T.MP m h).sem g)).prod =
        ∏ k : Fin (Pp.length / e),
          (X ^ e - Polynomial.C ((T.MP m h).sem (γs.getD k (MO Fc ks m).zero))) := by
      rw [← List.prod_ofFn]
      congr 1
      apply List.ext_getElem (by simp [hlen])
      intro k h1 h2
      have hk : k < γs.length := by simp at h1 h2; omega
      rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem _ _ hk]
    rw [← hprod, ← h1]
    ext k
    rw [leadPolyR, finsetSum_coeff, coeff_toPoly_sem, hFn]
    simp only [coeff_C_mul_X_pow]
    by_cases hk : k ≤ Pp.length
    · rw [Finset.sum_eq_single k (fun j _ hjk ↦ by rw [if_neg (Ne.symm hjk)])
        (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h), if_pos rfl]
      rcases lt_or_eq_of_le hk with hk | hk
      · rw [leadPolyRC, List.getD_append _ _ _ _ (by simpa using hk),
          List.getD_eq_getElem (l := (List.range Pp.length).map fun i ↦
            if e ∣ s' * (Pp.length - i) then
              (Pp.getD i []).getD (s' * (Pp.length - i) / e) (MO Fc ks m).zero
            else (MO Fc ks m).zero) _ (by simpa using hk),
          List.getElem_map, List.getElem_range]
        split_ifs
        · rw [nkF, polyF_coeff _ _ _ hk, coeff_toPoly_sem]
        · simp [(T.MP m h).sem_zero]
      · subst hk
        have hmon := (polyF_monic (fun i ↦ GPoly.toPoly (T.MP m h) (Pp.getD i [])) Pp.length)
        have h1 : (T.nkF m h Pp).coeff Pp.length = 1 := by
          rw [← hFn]; exact hmon.coeff_natDegree
        rw [Nat.sub_self, mul_zero, if_pos (dvd_zero e), Nat.zero_div, h1, coeff_one_zero, leadPolyRC,
          List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range,
          Nat.sub_self, List.getD_cons_zero, (T.MP m h).sem_one]
    · rw [Finset.sum_eq_zero fun j hj ↦ by
        rw [if_neg (by have := Finset.mem_range.mp hj; omega)], leadPolyRC,
        List.getD_eq_default _ _ (by simp; omega), (T.MP m h).sem_zero]
  · intro k l hkl
    by_contra hne
    rcases (hdist k k.2).2 l l.2 with h2 | h2
    · exact hne (Fin.ext h2)
    · have h3 : (MO Fc ks m).isZero ((MO Fc ks m).add (γs.getD k (MO Fc ks m).zero)
          ((MO Fc ks m).neg (γs.getD l (MO Fc ks m).zero))) = true := by
        rw [(T.MP m h).isZero_iff, (T.MP m h).sem_add, (T.MP m h).sem_neg, ← sub_eq_add_neg]
        exact sub_eq_zero.mpr hkl
      rw [h3] at h2
      exact Bool.noConfusion h2
  · intro h0
    have := (hdist k k.2).1
    rw [((T.MP m h).isZero_iff _).mpr h0] at this
    exact Bool.noConfusion this

end MTower

end Curves.MT
