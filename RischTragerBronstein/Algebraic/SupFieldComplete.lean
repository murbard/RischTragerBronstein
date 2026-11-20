import RischTragerBronstein.Algebraic.SupDecideQ
import RischTragerBronstein.Jacobian.NFTower
import RischTragerBronstein.Algebraic.SupFrontComplete

/-!
# The field loops of `superDecideQ` always succeed

* `nthLoop_spec`: with enough fuel, `nthLoop f S n` returns a field in which every root `α` of `S`
  has an `n`-th root of `f(α)` found by `rootsIn` (`NthDone`), provided `S` is squarefree and
  coprime to `f`. Each step adds one root with an `n`-th root (`GoodRoots`), and there are at most
  `deg S` roots.
* `buildField_spec`: `buildField f S n fuel` succeeds for `fuel > max(n, deg S)`; the field
  contains all `n`-th roots of unity and satisfies `NthDone`.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac NFC

namespace Sup

section Xn

variable {K : Type*} [Field K]

lemma toPoly_replicate_one : ∀ k : ℕ, toPoly (List.replicate k (0 : K) ++ [1]) = X ^ k
  | 0 => by simp [CPoly.toPoly]
  | k + 1 => by
    rw [List.replicate_succ, List.cons_append, toPoly_cons, toPoly_replicate_one k]
    simp; ring

lemma toPoly_xnMinus {n : ℕ} (hn : 0 < n) (c : K) : toPoly (xnMinus n c) = X ^ n - C c := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [xnMinus, toPoly_cons, Nat.succ_sub_one, toPoly_replicate_one]
  simp; ring

lemma sqf_xnMinus [CharZero K] {n : ℕ} (hn : 0 < n) {c : K} (hc : c ≠ 0) :
    Squarefree (toPoly (xnMinus n c)) := by
  rw [toPoly_xnMinus hn]
  exact (separable_X_pow_sub_C c (by exact_mod_cast hn.ne') hc).squarefree

lemma natDegree_xnMinus {n : ℕ} (hn : 0 < n) (c : K) : (toPoly (xnMinus n c)).natDegree = n := by
  rw [toPoly_xnMinus hn, natDegree_X_pow_sub_C]

end Xn

variable (f S : CPoly ℚ) (n : ℕ)

/-- `k` distinct roots of `S` in `NF M`, each with an `n`-th root of `f` there. -/
def GoodRoots (M : CPoly ℚ) (hM : Kron.irredQ M = true) (k : ℕ) : Prop :=
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  ∃ l : List (NF M), l.Nodup ∧ k ≤ l.length ∧
    ∀ a ∈ l, aeval a (toPoly S) = 0 ∧ ∃ b : NF M, b ^ n = aeval a (toPoly f)

/-- The exit condition of `nthLoop`. -/
def NthDone (M : CPoly ℚ) (hM : Kron.irredQ M = true) : Prop :=
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  ∃ rs, rootsIn M (liftK (K := NF M) S) = some rs ∧ ∀ α ∈ rs.dedup,
    ((rootsIn M (xnMinus n (evalC (liftK (K := NF M) f) α))).bind List.head?).isSome

set_option maxHeartbeats 3200000 in
/-- **`nthLoop` succeeds** with enough fuel. -/
theorem nthLoop_spec (hn : 0 < n) (hSsq : Squarefree (toPoly S))
    (hcop : IsCoprime (toPoly S) (toPoly f)) :
    ∀ (fuel : ℕ) (M : CPoly ℚ) (hM : Kron.irredQ M = true) (k : ℕ), GoodRoots f S n M hM k →
      (toPoly S).natDegree < fuel + k →
      ∃ M' hM', nthLoop f S n fuel M hM = some ⟨M', hM'⟩ ∧ NthDone f S n M' hM' ∧
        (letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
         letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
         Nonempty (NF M →+* NF M'))
  | 0, M, hM, k, hk, hlt => by
    exfalso
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    obtain ⟨l, hl, hlen, hr⟩ := hk
    have := length_le_natDegree ((Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective).mpr
      hSsq.ne_zero) hl (fun a ha ↦ by rw [eval_map_algebraMap]; exact (hr a ha).1)
    rw [natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective] at this
    omega
  | fuel + 1, M, hM, k, hk, hlt => by
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    have hgL : toPoly (liftK (K := NF M) S) = (toPoly S).map (algebraMap ℚ (NF M)) :=
      toPoly_liftK S
    have hgsq : Squarefree (toPoly (liftK (K := NF M) S)) := by
      rw [hgL]; exact ((PerfectField.separable_iff_squarefree).mpr hSsq).map.squarefree
    obtain ⟨rs, hrs, -⟩ := rootsIn_complete M _ hgsq
    have hsound := rootsIn_sound M _ hrs
    have hevf : ∀ α : NF M, evalC (liftK (K := NF M) f) α = aeval α (toPoly f) := fun α ↦ by
      rw [evalC_eq, toPoly_liftK, eval_map_algebraMap]
    have hfK : ∀ α : NF M, aeval α (toPoly S) = 0 → evalC (liftK (K := NF M) f) α ≠ 0 := by
      intro α hα h0
      obtain ⟨u, v, huv⟩ := hcop
      have := congrArg (aeval α) huv
      rw [map_add, map_mul, map_mul, hα, map_one, ← hevf, h0] at this
      simp at this
    have hrootS : ∀ α ∈ rs, aeval α (toPoly S) = 0 := fun α hα ↦ by
      have := hsound α hα; rwa [hgL, eval_map_algebraMap] at this
    simp only [nthLoop, hrs]
    split
    · rename_i hfind
      refine ⟨M, hM, rfl, ⟨rs, hrs, fun α hα ↦ ?_⟩, ⟨RingHom.id _⟩⟩
      have := List.find?_eq_none.mp hfind α hα
      revert this
      cases (rootsIn M (xnMinus n (evalC (liftK (K := NF M) f) α))).bind List.head? <;> simp
    · rename_i α0 hfind
      have hα0mem : α0 ∈ rs.dedup := List.mem_of_find?_eq_some hfind
      have hα0bad := List.find?_some hfind
      have hc0 : evalC (liftK (K := NF M) f) α0 ≠ 0 :=
        hfK α0 (hrootS α0 (List.mem_dedup.mp hα0mem))
      have hxsq := sqf_xnMinus (K := NF M) hn hc0
      have hxdeg : 0 < (toPoly (xnMinus n (evalC (liftK (K := NF M) f) α0))).natDegree := by
        rw [natDegree_xnMinus hn]; exact hn
      obtain ⟨M1, hM1, hext, hprop⟩ := extStep_spec M _ hxsq hxdeg
      letI : Fact (Irreducible (toPoly M1)) := ⟨Kron.irredQ_sound M1 hM1⟩
      obtain ⟨θ', hθ', α', hα'⟩ := hprop
      -- no `n`-th root of `f(α₀)` in `NF M`
      have hno : ∀ b : NF M, b ^ n ≠ evalC (liftK (K := NF M) f) α0 := by
        intro b hb
        obtain ⟨rs0, hrs0, hall0⟩ := rootsIn_complete M _ hxsq
        have hbm : b ∈ rs0 := hall0 b (by rw [toPoly_xnMinus hn]; simp [hb])
        rw [hrs0] at hα0bad
        cases rs0 with
        | nil => simp at hbm
        | cons r rs' => simp at hα0bad
      rw [hext]
      simp only
      set φ := emb M M1 hθ'
      have hgood : GoodRoots f S n M1 hM1 (k + 1) := by
        obtain ⟨l, hl, hlen, hr⟩ := hk
        have hα0l : α0 ∉ l := fun h ↦ by
          obtain ⟨b, hb⟩ := (hr α0 h).2
          exact hno b (by rw [hb, ← hevf])
        refine ⟨φ α0 :: l.map φ, ?_, by simp; omega, ?_⟩
        · refine List.nodup_cons.mpr ⟨fun h ↦ ?_, hl.map φ.injective⟩
          obtain ⟨a, ha, hφa⟩ := List.mem_map.mp h
          exact hα0l (φ.injective hφa ▸ ha)
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · refine ⟨by rw [← aeval_ringHom_rat φ, hrootS α0 (List.mem_dedup.mp hα0mem),
              map_zero], α', ?_⟩
            rw [toPoly_xnMinus hn, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
              Polynomial.map_C, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hα'
            rw [hα', hevf, aeval_ringHom_rat]
          · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
            obtain ⟨h1, c, hc⟩ := hr b hb
            exact ⟨by rw [← aeval_ringHom_rat φ, h1, map_zero], φ c,
              by rw [← map_pow, hc, aeval_ringHom_rat]⟩
      obtain ⟨M', hM', h', hdone, ⟨ψ⟩⟩ :=
        nthLoop_spec hn hSsq hcop fuel M1 hM1 (k + 1) hgood (by omega)
      exact ⟨M', hM', h', hdone, ⟨ψ.comp φ⟩⟩

/-- Roots transport along an embedding of number fields. -/
lemma HasRoots.mapEmb {M M' : CPoly ℚ} {hM : Kron.irredQ M = true} {hM' : Kron.irredQ M' = true}
    {D : CPoly ℚ} {k : ℕ} (h : HasRoots M hM D k)
    (φ : (letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
          letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
          NF M →+* NF M')) : HasRoots M' hM' D k := by
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
  obtain ⟨l, hl, hlen, hr⟩ := h
  obtain ⟨hl', hr'⟩ := roots_map φ hl hr
  exact ⟨l.map φ, hl', by simpa using hlen, hr'⟩

lemma hasRoots_zero (M : CPoly ℚ) (hM : Kron.irredQ M = true) (D : CPoly ℚ) : HasRoots M hM D 0 :=
  ⟨[], List.nodup_nil, le_refl _, by simp⟩

lemma goodRoots_zero (M : CPoly ℚ) (hM : Kron.irredQ M = true) : GoodRoots f S n M hM 0 :=
  ⟨[], List.nodup_nil, le_refl _, by simp⟩

/-- **`buildField` succeeds** once `fuel > max(n, deg S)`: the field contains `n` distinct
`n`-th roots of unity and all roots of `S`, and `nthLoop`'s exit condition holds there. -/
theorem buildField_spec (hn : 0 < n) (hSsq : Squarefree (toPoly S))
    (hcop : IsCoprime (toPoly S) (toPoly f)) (fuel : ℕ) (hfn : n < fuel)
    (hfS : (toPoly S).natDegree < fuel) :
    ∃ M hM, buildField f S n fuel = some ⟨M, hM⟩ ∧ NthDone f S n M hM ∧
      HasRoots M hM (xnMinus n 1) n ∧ HasRoots M hM S (toPoly S).natDegree := by
  have hX : Squarefree (toPoly (xnMinus n (1 : ℚ))) := sqf_xnMinus hn one_ne_zero
  have hXd : (toPoly (xnMinus n (1 : ℚ))).natDegree = n := natDegree_xnMinus hn 1
  obtain ⟨M1, hM1, h1, hr1⟩ := splitLoop_spec (xnMinus n 1) hX fuel [0, 1] irredQ_X 0
    (hasRoots_zero _ _ _) (by omega)
  obtain ⟨M2, hM2, h2, hr2⟩ := splitLoop_spec S hSsq fuel M1 hM1 0 (hasRoots_zero _ _ _)
    (by omega)
  obtain ⟨φ12⟩ := splitLoop_emb S hSsq fuel M1 hM1 M2 hM2 h2
  obtain ⟨M3, hM3, h3, hdone, ⟨φ23⟩⟩ := nthLoop_spec f S n hn hSsq hcop fuel M2 hM2 0
    (goodRoots_zero f S n _ _) (by omega)
  refine ⟨M3, hM3, ?_, hdone, ?_, ?_⟩
  · simp only [buildField, h1, h2, h3]
  · rw [hXd] at hr1
    exact HasRoots.mapEmb (hM' := hM3) (HasRoots.mapEmb (hM' := hM2) hr1 φ12) φ23
  · exact HasRoots.mapEmb (hM' := hM3) hr2 φ23

section Split

/-- `n` distinct `n`-th roots of unity give a primitive one. -/
lemma exists_primRoot_of_roots {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) {l : List K}
    (hl : l.Nodup) (hlen : n ≤ l.length) (hr : ∀ a ∈ l, a ^ n = 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hne : ∀ a ∈ l, a ≠ 0 := fun a ha h0 ↦ by
    have := hr a ha; rw [h0, zero_pow hn.ne'] at this; exact zero_ne_one this
  let g : Fin l.length → rootsOfUnity n K := fun i ↦
    ⟨Units.mk0 (l.get i) (hne _ (List.get_mem l i)), by
      rw [mem_rootsOfUnity]; ext; simpa using hr _ (List.getElem_mem i.2)⟩
  have hg : Function.Injective g := by
    intro i j hij
    have h1 : l.get i = l.get j := by
      have := congrArg (fun u : rootsOfUnity n K ↦ ((u : Kˣ) : K)) hij
      simpa [g] using this
    exact (List.Nodup.get_inj_iff hl).mp h1
  have hcard : n ≤ Nat.card (rootsOfUnity n K) := by
    have := Nat.card_le_card_of_injective g hg
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  exact card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp
    (le_antisymm (card_rootsOfUnity K n) hcard)

/-- **The non-branch part splits** over a field containing the roots of its rational version. -/
lemma nbPart_split {K : Type*} [Field K] [CharZero K] [DecidableEq K] (f D : CPoly ℚ)
    (hD : toPoly D ≠ 0) (as : List K) (hnd : as.Nodup)
    (hmem : ∀ α ∈ as, aeval α (toPoly (nbPartK f D)) = 0)
    (hcount : (toPoly (nbPartK f D)).natDegree ≤ as.length) :
    ∃ lc : K, lc ≠ 0 ∧ toPoly (nbPartK (liftK (K := K) f) (liftK (K := K) D)) =
      C lc * ∏ i : Fin as.length, (X - C (as.get i)) := by
  classical
  set fK := liftK (K := K) f with hfKdef
  set DK := liftK (K := K) D with hDKdef
  have hfK : toPoly fK = (toPoly f).map (algebraMap ℚ K) := toPoly_liftK f
  have hDK : toPoly DK = (toPoly D).map (algebraMap ℚ K) := toPoly_liftK D
  have hDK0 : toPoly DK ≠ 0 := by
    rw [hDK]; exact (Polynomial.map_ne_zero_iff (algebraMap ℚ K).injective).mpr hD
  set P := toPoly (nbPartK fK DK) with hP
  have hP0 : P ≠ 0 := nbPartK_ne_zero fK DK hDK0
  have hPsq : Squarefree P := squarefree_nbPartK fK DK hDK0
  have hPcop : IsCoprime P (toPoly fK) := isCoprime_nbPartK fK DK hDK0
  have hPD : P ∣ toPoly DK := by
    obtain ⟨-, -, -, he⟩ := nbPartK_facts fK DK hDK0
    rw [sqfreePart_mul DK hDK0, he, mul_assoc]; exact dvd_mul_right _ _
  have hSf : IsCoprime (toPoly (nbPartK f D)) (toPoly f) := isCoprime_nbPartK f D hD
  have hSD : toPoly (nbPartK f D) ∣ toPoly D := by
    obtain ⟨-, -, -, he⟩ := nbPartK_facts f D hD
    rw [sqfreePart_mul D hD, he, mul_assoc]; exact dvd_mul_right _ _
  -- every element of `as` is a root of `P`
  have has : ∀ a ∈ as, P.IsRoot a := by
    intro a ha
    have hSa := hmem a ha
    have h1 : ((toPoly DK).map (RingHom.id K)).IsRoot a := by
      rw [Polynomial.map_id, hDK, IsRoot, eval_map_algebraMap]
      obtain ⟨q, hq⟩ := hSD; rw [hq, map_mul, hSa, zero_mul]
    have h2 : ¬((toPoly fK).map (RingHom.id K)).IsRoot a := by
      rw [Polynomial.map_id, hfK, IsRoot, eval_map_algebraMap]
      intro h0
      obtain ⟨u, v, huv⟩ := hSf
      have := congrArg (aeval a) huv
      rw [map_add, map_mul, map_mul, hSa, h0, map_one] at this; simp at this
    simpa using isRoot_nbPartK fK DK hDK0 (RingHom.id K) a h1 h2
  -- counting in the algebraic closure
  let φ := algebraMap K (AlgebraicClosure K)
  have hφℚ : φ.comp (algebraMap ℚ K) = algebraMap ℚ (AlgebraicClosure K) := RingHom.ext_rat _ _
  have hPL0 : P.map φ ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).mpr hP0
  have hsplitL : Splits (P.map φ) := IsAlgClosed.splits _
  have hsepL : (P.map φ).Separable := ((PerfectField.separable_iff_squarefree).mpr hPsq).map
  have hnodupL := nodup_roots hsepL
  have hsubL : ∀ β ∈ (P.map φ).roots, β ∈ as.map φ := by
    intro β hβ
    have hβr : (P.map φ).eval β = 0 := (mem_roots hPL0).mp hβ
    have hβD : ((toPoly D).map (algebraMap ℚ (AlgebraicClosure K))).IsRoot β := by
      obtain ⟨q, hq⟩ := hPD
      have := congrArg (fun r ↦ (r.map φ).eval β) hq
      simp only [Polynomial.map_mul, eval_mul, hβr, zero_mul, hDK, Polynomial.map_map, hφℚ] at this
      exact this
    have hβf : ¬((toPoly f).map (algebraMap ℚ (AlgebraicClosure K))).IsRoot β := by
      intro h0
      obtain ⟨u, v, huv⟩ := hPcop
      have := congrArg (fun r ↦ (r.map φ).eval β) huv
      simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hβr, mul_zero,
        zero_add, hfK, Polynomial.map_map, hφℚ, Polynomial.map_one, eval_one] at this
      rw [IsRoot.def] at h0
      rw [h0, mul_zero] at this
      exact zero_ne_one this
    have hβS := isRoot_nbPartK f D hD (algebraMap ℚ (AlgebraicClosure K)) β hβD hβf
    rw [IsRoot.def, eval_map_algebraMap] at hβS
    exact root_mem_map φ (nbPartK_ne_zero f D hD) hnd hcount hmem hβS
  have hcardL : P.natDegree ≤ as.length := by
    rw [← natDegree_map_eq_of_injective φ.injective, hsplitL.natDegree_eq_card_roots]
    have hle : (P.map φ).roots ≤ ((as.map φ : List _) : Multiset _) :=
      (Multiset.le_iff_subset hnodupL).mpr fun β hβ ↦ by simpa using hsubL β hβ
    simpa using Multiset.card_le_card hle
  have hasle : (as : Multiset K) ≤ P.roots :=
    (Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnd)).mpr fun a ha ↦
      (mem_roots hP0).mpr (has a ha)
  have hrootsEq : P.roots = (as : Multiset K) := by
    refine (Multiset.eq_of_le_of_card_le hasle ?_).symm
    simp only [Multiset.coe_card]; exact (card_roots' P).trans hcardL
  have hsplit : Splits P := by
    rw [splits_iff_card_roots, hrootsEq, Multiset.coe_card]
    have := card_roots' P
    rw [hrootsEq, Multiset.coe_card] at this
    omega
  refine ⟨P.leadingCoeff, leadingCoeff_ne_zero.mpr hP0, ?_⟩
  conv_lhs => rw [hsplit.eq_prod_roots, hrootsEq]
  rw [Multiset.map_coe, Multiset.prod_coe]
  congr 1
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

end Split

section Answer

/-- **`superDecideM` answers** over a field satisfying the exit conditions of the field loops,
whenever the torsion oracle answers. -/
theorem superDecideM_ne_none (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]
    (hM : Kron.irredQ M = true) {n : ℕ} (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hdeg : (toPoly f).natDegree = f.length - 1) (hpd : 0 < f.length - 1)
    (hcop : Nat.Coprime n (f.length - 1)) (A : List (CPoly ℚ)) (D : CPoly ℚ) (hD : toPoly D ≠ 0)
    (B : ℕ) (hdone : NthDone f (nbPartK f D) n M hM)
    (hunity : HasRoots M hM (xnMinus n 1) n)
    (hSr : HasRoots M hM (nbPartK f D) (toPoly (nbPartK f D)).natDegree)
    (hans : TorsAnswers (liftK (K := NF M) f) n
      (torsOracle (nfRedAt (M := M) (M.map Rat.num)) (primesBelow B) B (liftK f) n)) :
    superDecideM M f n A D B ≠ none := by
  classical
  set S := nbPartK f D with hSdef
  have hX : Squarefree (toPoly (liftK (K := NF M) (xnMinus n (1 : ℚ)))) := by
    rw [toPoly_liftK]
    exact ((PerfectField.separable_iff_squarefree).mpr (sqf_xnMinus hn one_ne_zero)).map.squarefree
  obtain ⟨rz, hrz, hallz⟩ := rootsIn_complete M _ hX
  obtain ⟨rs, hrs, hnth⟩ := hdone
  have hSsqK : Squarefree (toPoly (liftK (K := NF M) S)) := by
    rw [toPoly_liftK]
    exact ((PerfectField.separable_iff_squarefree).mpr (squarefree_nbPartK f D hD)).map.squarefree
  obtain ⟨rs', hrs', hallS⟩ := rootsIn_complete M _ hSsqK
  rw [hrs] at hrs'
  cases hrs'
  -- a primitive root of unity is found
  obtain ⟨ζ0, hζ0⟩ : ∃ ζ : NF M, IsPrimitiveRoot ζ n := by
    obtain ⟨l, hl, hlen, hr⟩ := hunity
    refine exists_primRoot_of_roots hn hl hlen fun a ha ↦ ?_
    have := hr a ha
    rw [toPoly_xnMinus hn] at this
    simpa [sub_eq_zero] using this
  have hζ0mem : ζ0 ∈ rz := hallz ζ0 (by
    rw [toPoly_liftK, eval_map_algebraMap, toPoly_xnMinus hn]; simp [hζ0.pow_eq_one])
  have hprim : isPrimRoot M n ζ0 = true := by
    simp only [isPrimRoot, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, beq_iff_eq]
    exact ⟨hζ0.pow_eq_one, fun l hl ↦ by
      rcases Nat.eq_zero_or_pos l with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr (by simpa using hζ0.pow_ne_one_of_pos_of_lt hpos.ne' hl)⟩
  obtain ⟨ζ, hfind⟩ : ∃ ζ, rz.find? (isPrimRoot M n) = some ζ :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨ζ0, hζ0mem, hprim⟩)
  have hζp : isPrimRoot M n ζ = true := List.find?_some hfind
  have hζ : IsPrimitiveRoot ζ n := isPrimRoot_spec hn hζp
  -- roots of `S`, and the `n`-th roots
  have hevf : ∀ α : NF M, evalC (liftK (K := NF M) f) α = aeval α (toPoly f) := fun α ↦ by
    rw [evalC_eq, toPoly_liftK, eval_map_algebraMap]
  have hrootS : ∀ α ∈ rs, aeval α (toPoly S) = 0 := fun α hα ↦ by
    have := rootsIn_sound M _ hrs α hα; rwa [toPoly_liftK, eval_map_algebraMap] at this
  have hfne : ∀ α ∈ rs, evalC (liftK (K := NF M) f) α ≠ 0 := by
    intro α hα h0
    obtain ⟨u, v, huv⟩ := isCoprime_nbPartK f D hD
    have := congrArg (aeval α) huv
    rw [map_add, map_mul, map_mul, ← hSdef, hrootS α hα, map_one, ← hevf, h0] at this
    simp at this
  set g : NF M → NF M := fun α ↦
    ((rootsIn M (xnMinus n (evalC (liftK (K := NF M) f) α))).bind List.head?).getD 0 with hg
  have hgb : ∀ α ∈ rs.dedup, g α ≠ 0 ∧ g α ^ n = evalC (liftK (K := NF M) f) α := by
    intro α hα
    have hαrs := List.mem_dedup.mp hα
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hnth α hα)
    have hgr : g α = r := by rw [hg]; simp only; rw [hr]; rfl
    cases hl0 : rootsIn M (xnMinus n (evalC (liftK (K := NF M) f) α)) with
    | none => rw [hl0] at hr; simp at hr
    | some l0 =>
      rw [hl0] at hr
      have hrl : r ∈ l0 := List.mem_of_mem_head? hr
      have hroot := rootsIn_sound M _ hl0 r hrl
      rw [toPoly_xnMinus hn] at hroot
      simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hroot
      rw [hgr]
      refine ⟨fun h0 ↦ hfne α hαrs ?_, hroot⟩
      rw [← hroot, h0, zero_pow hn.ne']
  -- the data checks pass and `superFront` answers
  unfold superDecideM fieldData
  simp only [← hSdef]
  simp only [hrz, hrs, hfind]
  set as := rs.dedup with has
  have hnd : as.Nodup := List.nodup_dedup rs
  have hbget : ∀ i : Fin as.length, (as.map g).getD i 0 = g (as.get i) := fun i ↦ by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]; rfl
  have hcond : (isPrimRoot M n ζ && decide as.Nodup && (List.finRange as.length).all fun i ↦
      decide ((as.map g).getD i 0 ≠ 0 ∧
        (as.map g).getD i 0 ^ n = evalC (liftK (K := NF M) f) (as.get i))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
      true_implies]
    exact ⟨⟨hζp, hnd⟩, fun i ↦ by rw [hbget]; exact hgb _ (List.get_mem _ _)⟩
  rw [if_pos (by simpa [hg] using hcond)]
  have hmZ : toPoly M = (toPoly (M.map Rat.num)).map (Int.castRingHom ℚ) :=
    (Kron.polyZ_map M (int_of_irredQ hM)).symm
  have hsqK : Squarefree (toPoly (liftK (K := NF M) f)) := by
    rw [toPoly_liftK]; exact ((PerfectField.separable_iff_squarefree).mpr hsq).map.squarefree
  have hlen : (liftK (K := NF M) f).length = f.length := by simp [liftK]
  have hp1 : 1 ≤ (toPoly (liftK (K := NF M) f)).natDegree := by
    rw [toPoly_liftK, natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective, hdeg]; omega
  have hDK : toPoly (liftK (K := NF M) D) ≠ 0 := by
    rw [toPoly_liftK]; exact (Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective).mpr hD
  have hcount : (toPoly S).natDegree ≤ as.length := by
    obtain ⟨l, hl, hlen', hr⟩ := hSr
    have hsub : l ⊆ as := fun a ha ↦ List.mem_dedup.mpr (hallS a (by
      rw [toPoly_liftK, eval_map_algebraMap]; exact hr a ha))
    exact hlen'.trans (hl.subperm hsub).length_le
  obtain ⟨lc, hlc, hS⟩ := nbPart_split f D hD as hnd
    (fun α hα ↦ hrootS α (List.mem_dedup.mp hα)) hcount
  have hinj : Function.Injective fun i : Fin as.length ↦ as.get i :=
    fun i j hij ↦ (List.Nodup.get_inj_iff hnd).mp hij
  refine superFront_ne_none (liftK f) hn hsqK hp1 hζ _
    (torsOracle_spec (nfRedAt (M := M) (M.map Rat.num))
      (fun p _ R hR ↦ nfRedAt_valid _ hmZ p R hR) (primesBelow B) B hsqK (by rw [hlen]; exact hcop))
    hans (A.map (liftK (K := NF M))) (liftK (K := NF M) D) hDK (fun i ↦ as.get i)
    (fun i ↦ (as.map g).getD i 0) hinj (fun i ↦ by rw [hbget]; exact (hgb _ (List.get_mem _ _)).1)
    (fun i ↦ by rw [hbget, ← evalC_eq]; exact (hgb _ (List.get_mem _ _)).2) lc hlc hS

/-- **`superDecideQ` answers** for large fuel, whenever the torsion oracle answers over the
field it builds. -/
theorem superDecideQ_ne_none_of {n : ℕ} (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hdeg : (toPoly f).natDegree = f.length - 1) (hpd : 0 < f.length - 1)
    (hcop : Nat.Coprime n (f.length - 1)) (A : List (CPoly ℚ)) (D : CPoly ℚ) (hD : toPoly D ≠ 0)
    (B fuel : ℕ) (hfn : n < fuel) (hfS : (toPoly (nbPartK f D)).natDegree < fuel)
    (hans : ∀ (M : CPoly ℚ) [Fact (Irreducible (toPoly M))], TorsAnswers (liftK (K := NF M) f) n
      (torsOracle (nfRedAt (M := M) (M.map Rat.num)) (primesBelow B) B (liftK f) n)) :
    superDecideQ f n A D B fuel ≠ none := by
  obtain ⟨M, hM, hbuild, hdone, hunity, hSr⟩ := buildField_spec f (nbPartK f D) n hn
    (squarefree_nbPartK f D hD) (isCoprime_nbPartK f D hD) fuel hfn hfS
  unfold superDecideQ
  rw [hbuild]
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  exact superDecideM_ne_none f M hM hn hsq hdeg hpd hcop A D hD B hdone hunity hSr (hans M)

end Answer

end Sup
