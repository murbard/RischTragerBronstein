import RischTragerBronstein.Algebraic.NumField
import RischTragerBronstein.Computable.ResultantC

/-!
# The norm of a polynomial over a number field (Trager)

For `K = ℚ[θ]/(f)` and `g ∈ K[x]`, the norm `N_s(x) = Res_y(f(y), g(x − s y, y))` (`g(·, y)` the
polynomial whose coefficients are the representatives of those of `g`) is computed by
interpolating the computable resultants `Res_y(f(y), g(k − s y, y))`, `k = 0, …, n·m`
(`normPoly`). `normPoly_map`: over any field `L` in which `f` splits,
`N_s = lc(f)^e ∏_{f(θ) = 0} g_θ(x − s θ)`, where `g_θ` is `g` with `θ` substituted.
-/

open Polynomial CPoly

namespace NFC

variable (f : CPoly ℚ) [hf : Fact (Irreducible (toPoly f))]

/-- `y ↦ g(k − s y, y)`: Horner in `k − s y`. -/
def hEval (g : CPoly (NF f)) (k s : ℚ) : CPoly ℚ :=
  g.foldr (fun c acc ↦ add c.1 (mul [k, -s] acc)) []

/-- The formal degree `e = (n − 1) + m` (`n = deg f`, `m + 1` = length of `g`). -/
def eDeg (g : CPoly (NF f)) : ℕ := (degT f - 1) + (g.length - 1)

/-- The value `N_s(k)`: `lc(f)^{e − deg h} Res(f, h)`, `h = g(k − s y, y)`. -/
def normVal (g : CPoly (NF f)) (s k : ℚ) : ℚ :=
  lcT f ^ (eDeg f g - degT (hEval f g k s)) * resC f (hEval f g k s)

/-- The interpolation nodes `0, 1, …, n·m`. -/
def nodes (g : CPoly (NF f)) : List ℚ :=
  List.map (fun i : ℕ ↦ (i : ℚ)) (List.range (degT f * (g.length - 1) + 1))

/-- **The norm** `N_s(x)`. -/
def normPoly (g : CPoly (NF f)) (s : ℚ) : CPoly ℚ :=
  Kron.lagr (nodes f g) ((nodes f g).map (normVal f g s))

/-- Substituting a root `θ` into an element of `K`. -/
noncomputable def evAt {L : Type*} [Field L] [Algebra ℚ L] (θ : L) (c : NF f) : L :=
  aeval θ (toPoly c.1)

lemma aeval_lin {L : Type*} [Field L] [Algebra ℚ L] (θ : L) (k s : ℚ) :
    aeval θ (toPoly ([k, -s] : CPoly ℚ)) = algebraMap ℚ L k - algebraMap ℚ L s * θ := by
  simp [CPoly.toPoly]; ring

lemma aeval_hEval {L : Type*} [Field L] [Algebra ℚ L] (θ : L) (k s : ℚ) :
    ∀ g : CPoly (NF f), aeval θ (toPoly (hEval f g k s)) =
      (toPoly (g.map (evAt f θ))).eval (algebraMap ℚ L k - algebraMap ℚ L s * θ)
  | [] => by simp [hEval, CPoly.toPoly]
  | c :: t => by
    show aeval θ (toPoly (add c.1 (mul [k, -s] (hEval f t k s)))) = _
    rw [toPoly_add, toPoly_mul, map_add, map_mul, aeval_hEval θ k s t, aeval_lin,
      List.map_cons, toPoly_cons, eval_add, eval_mul, eval_C, eval_X]
    simp only [evAt]

lemma natDegree_elem (c : NF f) : (toPoly c.1).natDegree ≤ degT f - 1 := by
  have h := degree_val f c
  rw [degT_eq]
  by_cases h0 : toPoly c.1 = 0
  · rw [h0]; simp
  · have := natDegree_lt_natDegree h0 h; omega

lemma natDegree_hEval (k s : ℚ) : ∀ g : CPoly (NF f),
    (toPoly (hEval f g k s)).natDegree ≤ (degT f - 1) + (g.length - 1)
  | [] => by simp [hEval, CPoly.toPoly]
  | c :: t => by
    show (toPoly (add c.1 (mul [k, -s] (hEval f t k s)))).natDegree ≤ _
    rw [toPoly_add, toPoly_mul]
    have h1 := natDegree_elem f c
    have h2 := natDegree_hEval k s t
    have hl : (toPoly ([k, -s] : CPoly ℚ)).natDegree ≤ 1 := natDegree_toPoly_le_length _
    rw [List.length_cons]
    refine (natDegree_add_le _ _).trans (max_le (by omega) ?_)
    rcases t with _ | ⟨c', t'⟩
    · simp [hEval, CPoly.toPoly]
    · refine (natDegree_mul_le).trans ?_
      simp only [List.length_cons] at h2 ⊢
      omega


lemma nodes_nodup (g : CPoly (NF f)) : (nodes f g).Nodup :=
  List.Nodup.map (fun a b h ↦ by exact_mod_cast h) List.nodup_range

lemma nodes_getD (g : CPoly (NF f)) (i : ℕ) (hi : i < (nodes f g).length) :
    (nodes f g).getD i 0 = i := by
  simp only [nodes, List.length_map, List.length_range] at hi
  simp [nodes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

set_option maxHeartbeats 1600000 in
/-- **The product formula for the norm.** -/
theorem normPoly_map {L : Type*} [Field L] [CharZero L]
    (hspl : ((toPoly f).map (algebraMap ℚ L)).Splits) (g : CPoly (NF f)) (s : ℚ) :
    (toPoly (normPoly f g s)).map (algebraMap ℚ L) =
      C (algebraMap ℚ L (lcT f) ^ eDeg f g) *
        ((((toPoly f).map (algebraMap ℚ L)).roots).map fun θ ↦
          (toPoly (g.map (evAt f θ))).comp (X - C (algebraMap ℚ L s * θ))).prod := by
  set fL := (toPoly f).map (algebraMap ℚ L) with hfL
  have hf0 : toPoly f ≠ 0 := f_ne_zero f
  have hfLdeg : fL.natDegree = (toPoly f).natDegree :=
    natDegree_map_eq_of_injective (algebraMap ℚ L).injective _
  set n := (toPoly f).natDegree
  set m := g.length - 1
  have hn : degT f = n := degT_eq f
  have hlen : (nodes f g).length = n * m + 1 := by simp [nodes, hn, m]
  classical
  set S : Finset L := (Finset.range (n * m + 1)).image fun i : ℕ ↦ (i : L)
  have hS : S.card = n * m + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (s := S)
  · rw [hS]
    refine (degree_map_le).trans_lt ?_
    refine (degree_le_natDegree).trans_lt ?_
    have := Kron.natDegree_lagr (nodes f g) ((nodes f g).map (normVal f g s))
    rw [hlen] at this
    exact_mod_cast (show (toPoly (normPoly f g s)).natDegree < n * m + 1 by
      simp only [normPoly]; omega)
  · rw [hS]
    refine (degree_le_natDegree).trans_lt ?_
    have hfac : ∀ θ ∈ fL.roots, ((toPoly (g.map (evAt f θ))).comp
        (X - C (algebraMap ℚ L s * θ))).natDegree ≤ m := by
      intro θ _
      refine (natDegree_comp_le).trans ?_
      have h1 := natDegree_toPoly_le_length (g.map (evAt f θ))
      rw [List.length_map] at h1
      have h2 : (X - C (algebraMap ℚ L s * θ)).natDegree ≤ 1 := natDegree_X_sub_C_le _
      calc _ ≤ (g.length - 1) * 1 := Nat.mul_le_mul h1 h2
        _ = m := by simp [m]
    have hprod := natDegree_multiset_prod_le (fL.roots.map fun θ ↦
      (toPoly (g.map (evAt f θ))).comp (X - C (algebraMap ℚ L s * θ)))
    have hsum : ((fL.roots.map fun θ ↦ (toPoly (g.map (evAt f θ))).comp
        (X - C (algebraMap ℚ L s * θ))).map natDegree).sum ≤ n * m := by
      rw [Multiset.map_map]
      refine (Multiset.sum_le_card_nsmul _ m fun x hx ↦ ?_).trans ?_
      · obtain ⟨θ, hθ, rfl⟩ := Multiset.mem_map.mp hx; exact hfac θ hθ
      · rw [Multiset.card_map, ← hspl.natDegree_eq_card_roots, hfLdeg, smul_eq_mul]
    have := (natDegree_C_mul_le (algebraMap ℚ L (lcT f) ^ eDeg f g) _).trans (hprod.trans hsum)
    exact_mod_cast Nat.lt_succ_of_le this
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range] at hi
    -- the left side
    rw [eval_map_algebraMap, show ((i : ℕ) : L) = algebraMap ℚ L (i : ℚ) by simp,
      aeval_algebraMap_apply, coe_aeval_eq_eval]
    have hval := Kron.eval_lagr (nodes f g) ((nodes f g).map (normVal f g s)) (nodes_nodup f g) i
      (by rw [hlen]; exact hi)
    rw [nodes_getD f g i (by rw [hlen]; exact hi)] at hval
    have hi' : i < degT f * (g.length - 1) + 1 := by rw [hn]; exact hi
    have hv' : ((nodes f g).map (normVal f g s)).getD i 0 = normVal f g s (i : ℚ) := by
      simp [nodes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi']
    rw [show normPoly f g s = Kron.lagr (nodes f g) ((nodes f g).map (normVal f g s)) from rfl, hval,
      hv']
    -- the value through the resultant
    set h := hEval f g (i : ℚ) s
    have hd := natDegree_hEval f (i : ℚ) s g
    rw [normVal, resC_eq, map_mul, map_pow, lcT_eq, degT_eq, ← resultant_map_map]
    have hdL : ((toPoly h).map (algebraMap ℚ L)).natDegree = (toPoly h).natDegree :=
      natDegree_map_eq_of_injective (algebraMap ℚ L).injective _
    have hde : (toPoly h).natDegree ≤ eDeg f g := by unfold eDeg; exact hd
    have key := resultant_add_right_deg ((toPoly f).map (algebraMap ℚ L))
      ((toPoly h).map (algebraMap ℚ L)) (toPoly f).natDegree (toPoly h).natDegree
      (eDeg f g - (toPoly h).natDegree) (le_of_eq hdL)
    rw [show (toPoly h).natDegree + (eDeg f g - (toPoly h).natDegree) = eDeg f g by omega] at key
    have hcoef : ((toPoly f).map (algebraMap ℚ L)).coeff (toPoly f).natDegree =
        algebraMap ℚ L (toPoly f).leadingCoeff := by rw [coeff_map]; rfl
    rw [hcoef] at key
    rw [← key]
    have key2 := resultant_eq_prod_eval ((toPoly f).map (algebraMap ℚ L))
      ((toPoly h).map (algebraMap ℚ L)) (eDeg f g) (by rw [hdL]; exact hde) hspl
    rw [hfLdeg] at key2
    rw [key2]
    -- the right side
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, leadingCoeff_map_of_injective
      (algebraMap ℚ L).injective]
    congr 2
    refine Multiset.map_congr rfl fun θ _ ↦ ?_
    simp only [Function.comp_apply, eval_comp, eval_sub, eval_X, eval_C, eval_map_algebraMap]
    rw [aeval_hEval]

end NFC
