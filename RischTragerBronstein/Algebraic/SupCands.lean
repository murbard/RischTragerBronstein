import RischTragerBronstein.Algebraic.SupMobComplete
import RischTragerBronstein.Algebraic.SupOracleFB

/-!
# Candidate points for global certificates

`candQ f N`: the first `N` natural numbers `c` with `f(c) ≠ 0`. `candPoly` is `∏ (X − c)`; it is
squarefree and coprime to `f`, so `nthLoop f (candPoly …)` adjoins `n`-th roots of `f(c)`.
`buildFieldAll` is `buildFieldMob` followed by that loop; `buildFieldAll_spec`: it succeeds for
large fuel, with all the facts `MobField` and `n`-th roots of `f` at every candidate.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac NFC

namespace Sup

/-- The first `N` natural numbers that are not roots of `f`. -/
def candQ (f : CPoly ℚ) (N : ℕ) : List ℚ :=
  (((List.range (N + f.length)).map fun i : ℕ ↦ (i : ℚ)).filter fun c ↦ decide (evalC f c ≠ 0)).take N

/-- `∏ (X − c)`. -/
def candPoly (cs : List ℚ) : CPoly ℚ := cs.foldr (fun c acc ↦ mul [-c, 1] acc) [1]

lemma toPoly_candPoly : ∀ cs : List ℚ, toPoly (candPoly cs) = (cs.map fun c ↦ X - C c).prod
  | [] => by simp [candPoly, CPoly.toPoly]
  | c :: cs => by
    have ih := toPoly_candPoly cs
    show toPoly (mul [-c, 1] (candPoly cs)) = _
    rw [toPoly_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    simp [CPoly.toPoly]; ring

lemma candQ_nodup (f : CPoly ℚ) (N : ℕ) : (candQ f N).Nodup :=
  ((List.nodup_range.map fun i j h ↦ by exact_mod_cast h).filter _).sublist
    (List.take_sublist _ _)

lemma candQ_ne (f : CPoly ℚ) (N : ℕ) : ∀ c ∈ candQ f N, (toPoly f).eval c ≠ 0 := by
  intro c hc
  have := (List.mem_filter.mp ((List.take_sublist _ _).subset hc)).2
  rw [← evalC_eq]; simpa using this

lemma candQ_length (f : CPoly ℚ) (hf0 : toPoly f ≠ 0) (N : ℕ) : (candQ f N).length = N := by
  unfold candQ
  rw [List.length_take]
  apply min_eq_left
  -- at most `deg f < f.length` of the `N + f.length` candidates are roots
  set L := (List.range (N + f.length)).map fun i : ℕ ↦ (i : ℚ)
  have hnd : L.Nodup := List.nodup_range.map fun i j h ↦ by exact_mod_cast h
  have hroots : (L.filter fun c ↦ !decide (evalC f c ≠ 0)).length ≤ f.length := by
    have hnd' := hnd.filter (fun c ↦ !decide (evalC f c ≠ 0))
    have := length_le_natDegree hf0 hnd' (fun a ha ↦ by
      have := (List.mem_filter.mp ha).2
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_not] at this
      rw [← evalC_eq]; exact this)
    have h2 := natDegree_toPoly_le' f
    omega
  have htot := List.length_eq_length_filter_add (l := L) (fun c ↦ decide (evalC f c ≠ 0))
  have hL : L.length = N + f.length := by simp [L]
  omega

lemma candPoly_squarefree (cs : List ℚ) (hnd : cs.Nodup) : Squarefree (toPoly (candPoly cs)) := by
  rw [toPoly_candPoly, ← List.prod_toFinset _ hnd]
  exact (separable_prod_X_sub_C_iff' (f := id)).mpr (fun x _ y _ h ↦ h) |>.squarefree

lemma candPoly_coprime (f : CPoly ℚ) (cs : List ℚ) (hne : ∀ c ∈ cs, (toPoly f).eval c ≠ 0) :
    IsCoprime (toPoly (candPoly cs)) (toPoly f) := by
  rw [toPoly_candPoly]
  induction cs with
  | nil => simp [isCoprime_one_left]
  | cons c cs ih =>
    rw [List.map_cons, List.prod_cons]
    refine IsCoprime.mul_left ?_ (ih fun c' hc' ↦ hne c' (List.mem_cons_of_mem _ hc'))
    refine (irreducible_X_sub_C c).coprime_iff_not_dvd.mpr fun h ↦ hne c List.mem_cons_self ?_
    exact (dvd_iff_isRoot.mp h)

lemma candPoly_root {K : Type*} [Field K] [CharZero K] (cs : List ℚ) (c : ℚ) (hc : c ∈ cs) :
    aeval (c : K) (toPoly (candPoly cs)) = 0 := by
  rw [toPoly_candPoly, map_list_prod, List.map_map]
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨c, hc, by simp⟩

lemma natDegree_candPoly (cs : List ℚ) : (toPoly (candPoly cs)).natDegree = cs.length := by
  rw [toPoly_candPoly]
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hne : (cs.map fun c ↦ X - C c).prod ≠ 0 :=
      List.prod_ne_zero (by simp [X_sub_C_ne_zero])
    rw [List.map_cons, List.prod_cons, natDegree_mul (X_sub_C_ne_zero c) hne, natDegree_X_sub_C,
      ih, List.length_cons]
    ring

/-- The field for the complete procedures: `buildFieldMob`, then `n`-th roots of `f` at the
candidates. -/
noncomputable def buildFieldAll (f S : CPoly ℚ) (n fuel : ℕ) (cs : List ℚ) :
    Option (Σ' M : CPoly ℚ, Kron.irredQ M = true) :=
  match buildFieldMob f S n fuel with
  | some ⟨M, h⟩ => nthLoop f (candPoly cs) n fuel M h
  | none => none

/-- `MobField` transports along embeddings. -/
lemma MobField.mapEmb {f S : CPoly ℚ} {n : ℕ} {M M' : CPoly ℚ} {hM : Kron.irredQ M = true}
    {hM' : Kron.irredQ M' = true} (hS0 : toPoly S ≠ 0) (h : MobField f S n M hM)
    (φ : (letI : Fact (Irreducible (toPoly M))  := ⟨Kron.irredQ_sound M hM⟩
          letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
          NF M →+* NF M')) : MobField f S n M' hM' := by
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
  obtain ⟨hU, hF, hSr, hSn, c, hc⟩ := h
  refine ⟨HasRoots.mapEmb (hM' := hM') hU φ, HasRoots.mapEmb (hM' := hM') hF φ,
    HasRoots.mapEmb (hM' := hM') hSr φ, nth_map (hM' := hM') hS0 hSr hSn φ, φ c, ?_⟩
  rw [← map_pow, hc]
  exact RingHom.congr_fun (RingHom.ext_rat (φ.comp (algebraMap ℚ _)) (algebraMap ℚ _)) _

/-- **`buildFieldAll` succeeds** for large fuel: `MobField` and `n`-th roots of `f` at every
candidate. -/
theorem buildFieldAll_spec (f S : CPoly ℚ) {n : ℕ} (hn : 0 < n) (hfsq : Squarefree (toPoly f))
    (hfd : (toPoly f).natDegree = f.length - 1) (hd : 1 ≤ (toPoly f).natDegree)
    (hSsq : Squarefree (toPoly S)) (hcop : IsCoprime (toPoly S) (toPoly f)) (cs : List ℚ)
    (hcs : cs.Nodup) (hcf : ∀ c ∈ cs, (toPoly f).eval c ≠ 0) (fuel : ℕ) (hfn : n < fuel)
    (hff : (toPoly f).natDegree < fuel) (hfS : (toPoly S).natDegree < fuel)
    (hfc : cs.length < fuel) :
    ∃ M hM, buildFieldAll f S n fuel cs = some ⟨M, hM⟩ ∧ MobField f S n M hM ∧
      (letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
       ∀ c ∈ cs, ∃ y : NF M, y ^ n = aeval (c : NF M) (toPoly f)) := by
  obtain ⟨M0, hM0, h0, hMF⟩ := buildFieldMob_spec f S hn hfsq hfd hd hSsq hcop fuel hfn hff hfS
  have hcsq := candPoly_squarefree cs hcs
  have hccop := candPoly_coprime f cs hcf
  obtain ⟨M, hM, h1, hdone, ⟨φ⟩⟩ := nthLoop_spec f (candPoly cs) n hn hcsq hccop fuel M0 hM0 0
    (goodRoots_zero _ _ n _ _) (by rw [natDegree_candPoly]; omega)
  refine ⟨M, hM, by simp only [buildFieldAll, h0, h1], MobField.mapEmb (hM' := hM)
    hSsq.ne_zero hMF φ, ?_⟩
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  intro c hc
  exact nth_of_done hn hcsq hdone (c : NF M) (candPoly_root cs c hc)

end Sup
