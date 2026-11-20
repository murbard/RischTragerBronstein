import RischTragerBronstein.Jacobian.HypDecideEvenKComplete
import RischTragerBronstein.Jacobian.NFTower

/-!
# Even degree over `ℚ`, without a rational root

For `y² = q(x)`, `q ∈ ℚ[x]` squarefree of degree `2g + 2`, and any `A, D ∈ ℚ[x]`:

1. `towerEven`: a number field `K` in which the non-branch part `S₁` of `D` and `g` base
   abscissae split (`baseS`), `q` is a non-zero square at their roots, `lc(q)` is a square, and
   `q` splits (chained `splitLoop`/`sqLoopG`, with the embeddings of `NFTower`);
2. a root `e ∈ K` of `q` (`rootsIn`), and `hypDecideEvenK` over `K`.

`hypDecideEvenQ_spec`: every answer is correct. `hypDecideEvenQ_decides`: for all large bounds
there is an answer.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad NFC

namespace Jac

/-- The field for the even-degree procedure. -/
noncomputable def towerEven (q S2 : CPoly ℚ) (lc : ℚ) :
    Option (Σ' M : CPoly ℚ, Kron.irredQ M = true) :=
  match splitLoop S2 (Kron.degC S2 + 1) [0, 1] irredQ_X with
  | some ⟨M1, h1⟩ =>
    match sqLoopG q S2 (Kron.degC S2 + 1) M1 h1 with
    | some ⟨M2, h2⟩ =>
      match sqLoopG [lc] [0, 1] 2 M2 h2 with
      | some ⟨M3, h3⟩ => splitLoop q (Kron.degC q + 1) M3 h3
      | none => none
    | none => none
  | none => none

set_option maxHeartbeats 3200000 in
theorem towerEven_spec (q S2 : CPoly ℚ) (lc : ℚ) (hqsq : Squarefree (toPoly q))
    (hS2 : Squarefree (toPoly S2)) (hcop : IsCoprime (toPoly S2) (toPoly q)) (hlc : lc ≠ 0) :
    ∃ M hM, towerEven q S2 lc = some ⟨M, hM⟩ ∧
      (letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      HasRoots M hM S2 (toPoly S2).natDegree ∧
      (∀ α : NF M, aeval α (toPoly S2) = 0 → ∃ β : NF M, β ≠ 0 ∧ β * β = pValG q α) ∧
      (∃ γ : NF M, γ ≠ 0 ∧ γ * γ = (lc : NF M)) ∧
      HasRoots M hM q (toPoly q).natDegree) := by
  have hdS2 : Kron.degC S2 = (toPoly S2).natDegree := Kron.degC_eq S2 hS2.ne_zero
  have hdq : Kron.degC q = (toPoly q).natDegree := Kron.degC_eq q hqsq.ne_zero
  obtain ⟨M1, h1, hl1, hr1⟩ := splitLoop_spec S2 hS2 (Kron.degC S2 + 1) [0, 1] irredQ_X 0
    ⟨[], List.nodup_nil, le_rfl, by simp⟩ (by rw [hdS2]; omega)
  obtain ⟨M2, h2, hl2, hr2, hsq2⟩ := sqLoopG_spec q S2 hS2 hcop (Kron.degC S2 + 1) M1 h1 0 hr1
    ⟨[], List.nodup_nil, le_rfl, by simp⟩ (by rw [hdS2]; omega)
  letI : Fact (Irreducible (toPoly M2)) := ⟨Kron.irredQ_sound M2 h2⟩
  have hX : toPoly ([0, 1] : CPoly ℚ) = X := by simp [CPoly.toPoly]
  have hXsq : Squarefree (toPoly ([0, 1] : CPoly ℚ)) := by rw [hX]; exact irreducible_X.squarefree
  have hXcop : IsCoprime (toPoly ([0, 1] : CPoly ℚ)) (toPoly [lc]) := by
    refine ⟨0, C lc⁻¹, ?_⟩
    simp [CPoly.toPoly, ← C_mul, inv_mul_cancel₀ hlc]
  obtain ⟨M3, h3, hl3, -, hsq3⟩ := sqLoopG_spec [lc] [0, 1] hXsq hXcop 2 M2 h2 0
    ⟨[0], List.nodup_singleton _, by rw [hX]; simp, by simp [hX]⟩
    ⟨[], List.nodup_nil, le_rfl, by simp⟩ (by rw [hX]; simp)
  letI : Fact (Irreducible (toPoly M3)) := ⟨Kron.irredQ_sound M3 h3⟩
  obtain ⟨M4, h4, hl4, hr4⟩ := splitLoop_spec q hqsq (Kron.degC q + 1) M3 h3 0
    ⟨[], List.nodup_nil, le_rfl, by simp⟩ (by rw [hdq]; omega)
  letI : Fact (Irreducible (toPoly M4)) := ⟨Kron.irredQ_sound M4 h4⟩
  obtain ⟨φ23⟩ := sqLoopG_emb [lc] [0, 1] hXcop hXsq 2 M2 h2 M3 h3 hl3
  obtain ⟨φ34⟩ := splitLoop_emb q hqsq _ M3 h3 M4 h4 hl4
  set φ := φ34.comp φ23
  refine ⟨M4, h4, ?_, ?_, ?_, ?_, hr4⟩
  · unfold towerEven
    rw [hl1]; simp only; rw [hl2]; simp only; rw [hl3]; simp only; exact hl4
  · obtain ⟨l, hl, hlen, hr⟩ := hr2
    obtain ⟨hl', hr'⟩ := roots_map φ hl hr
    exact ⟨l.map φ, hl', by simpa using hlen, hr'⟩
  · obtain ⟨l, hl, hlen, hr⟩ := hr2
    exact sqFacts_map φ q hS2.ne_zero hl hlen hr hsq2
  · obtain ⟨γ, hγ0, hγ⟩ := hsq3 0 (by simp [hX])
    refine ⟨φ34 γ, (map_ne_zero_iff _ φ34.injective).mpr hγ0, ?_⟩
    rw [← map_mul, hγ]
    simp [pValG, CPoly.toPoly, map_ratCast]

/-- **Even degree over `ℚ`.** -/
noncomputable def hypDecideEvenQ (q A D : CPoly ℚ) (B : ℕ) : Option Bool :=
  if trim A = [] then some true
  else if isZero D then none
  else
    match towerEven q (baseS q (nbPart q D) ((q.length - 3) / 2)) (lead (trim q)) with
    | none => none
    | some ⟨M, hM⟩ =>
      letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      match rootsIn M (liftK q) with
      | some (e :: _) => hypDecideEvenK M (liftK q) e (liftK A) (liftK D) B
      | _ => none

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Correctness of `hypDecideEvenQ`.** -/
theorem hypDecideEvenQ_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly ℚ) (hy : y ^ 2 = aeval x (toPoly q)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (B : ℕ) (ans : Bool) (h : hypDecideEvenQ q A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold hypDecideEvenQ at h
  split_ifs at h with hA0 hDz
  · cases h
    have : toPoly A = 0 := (trim_eq_nil_iff A).mp hA0
    simp only [this, map_zero, zero_div, true_iff]
    simpa using hasElementaryIntegral_of_deriv (0 : E)
  split at h
  · cases h
  rename_i M hM _
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  split at h
  swap
  · cases h
  rename_i e tl _
  let ι : NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NF M) (M := Kc)).toRingHom
  have hy' : y ^ 2 = evF ι x (liftK q) := by rw [evF_liftK]; exact hy
  have := hypDecideEvenK_spec M (int_of_irredQ hM) hC hCall x y hx (liftK q) e ι hy' hgen
    (liftK A) (liftK D) B ans h
  rwa [evF_liftK, evF_liftK] at this

end Spec

set_option maxHeartbeats 6400000 in
/-- **`hypDecideEvenQ` answers for all large bounds.** -/
theorem hypDecideEvenQ_eventually (q : CPoly ℚ) {g : ℕ} (hlen : q.length = 2 * g + 3)
    (hlcq : q.getD (2 * g + 2) 0 ≠ 0) (hqsq : Squarefree (toPoly q)) (A D : CPoly ℚ)
    (hD : toPoly D ≠ 0) : ∃ B0, ∀ B, B0 ≤ B → hypDecideEvenQ q A D B ≠ none := by
  classical
  by_cases hA0 : trim A = []
  · exact ⟨0, fun B _ ↦ by simp [hypDecideEvenQ, hA0]⟩
  have hDz : isZero D = false := by
    rcases h : isZero D with _ | _
    · rfl
    · exact absurd ((isZero_iff _).mp h) hD
  have hq2 : (toPoly q).natDegree = 2 * g + 2 := by
    have hcoef : ∀ n, (toPoly q).coeff n = q.getD n 0 := coeff_toPoly q
    refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hcoef]; exact hlcq))
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [hcoef, List.getD_eq_default _ _ (by rw [hlen]; exact_mod_cast hn)]
  have hq0 : toPoly q ≠ 0 := hqsq.ne_zero
  set S1 := nbPart q D
  have hS10 := nbPart_ne_zero q D hD
  have hS1sq := squarefree_nbPart q D hD
  have hS1cop := isCoprime_nbPart q D hD
  set as := baseAs q S1 g
  have hasnd : as.Nodup := (baseAs_spec q S1 g).1
  have hasg : ∀ a ∈ as, (toPoly S1).eval (a : ℚ) ≠ 0 ∧ (toPoly q).eval (a : ℚ) ≠ 0 :=
    (baseAs_spec q S1 g).2
  have hasl : as.length = g := baseAs_length q S1 g hS10 hq0
  set asQ : List ℚ := as.map fun a : ℕ ↦ (a : ℚ)
  have hasQnd : asQ.Nodup := hasnd.map Nat.cast_injective
  have hS2 : toPoly (baseS q S1 g) = toPoly S1 * (asQ.map fun r ↦ X - C r).prod := by
    rw [baseS, toPoly_mul, toPoly_prodLin]
  set S2 := baseS q S1 g with hS2def
  have hPS : IsCoprime (asQ.map fun r ↦ X - C r).prod (toPoly S1) :=
    isCoprime_prodX _ _ fun a ha ↦ by
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha; exact (hasg n hn).1
  have hPq : IsCoprime (asQ.map fun r ↦ X - C r).prod (toPoly q) :=
    isCoprime_prodX _ _ fun a ha ↦ by
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha; exact (hasg n hn).2
  have hS2sq : Squarefree (toPoly S2) := by
    rw [hS2, squarefree_mul_iff]
    exact ⟨hPS.symm.isRelPrime, hS1sq, squarefree_prodX _ hasQnd⟩
  have hS2cop : IsCoprime (toPoly S2) (toPoly q) := by rw [hS2]; exact hS1cop.mul_left hPq
  have hlc0 : lead (trim q) ≠ 0 := by
    rw [show lead (trim q) = lcT q from rfl, lcT_eq]; exact leadingCoeff_ne_zero.mpr hq0
  obtain ⟨M, hM, htower, hrS2, hsqS2, ⟨γ, hγ0, hγ⟩, hrq⟩ :=
    towerEven_spec q S2 (lead (trim q)) hqsq hS2sq hS2cop hlc0
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  have hMZ := int_of_irredQ hM
  have hL : ∀ P : CPoly ℚ, toPoly (liftK (K := NF M) P) = (toPoly P).map (algebraMap ℚ (NF M)) :=
    fun P ↦ toPoly_liftK P
  -- a root of `q`
  have hqLsq : Squarefree (toPoly (liftK (K := NF M) q)) := by
    rw [hL]; exact ((PerfectField.separable_iff_squarefree).mpr hqsq).map.squarefree
  obtain ⟨rs, hrs, hall⟩ := rootsIn_complete M _ hqLsq
  have hsound := rootsIn_sound M _ hrs
  obtain ⟨lq, hlq, hlenq, hrq'⟩ := hrq
  obtain ⟨e, tl, hrse⟩ : ∃ e tl, rs = e :: tl := by
    cases lq with
    | nil => simp at hlenq; omega
    | cons a lq' =>
      have ha := hrq' a List.mem_cons_self
      have := hall a (by rw [hL, eval_map_algebraMap]; exact ha)
      cases rs with
      | nil => simp at this
      | cons e tl => exact ⟨e, tl, rfl⟩
  have he : (toPoly (liftK (K := NF M) q)).eval e = 0 := hsound e (by rw [hrse]; simp)
  -- the facts for `hypDecideEvenK_eventually`
  set Kb := AlgebraicClosure (NF M)
  set j := algebraMap (NF M) Kb
  have hmapKb : ∀ P : CPoly ℚ, (toPoly (liftK (K := NF M) P)).map j =
      (toPoly P).map (algebraMap ℚ Kb) := fun P ↦ by
    rw [hL, Polynomial.map_map]; congr 1
  have hS1S2 : ∀ {L : Type} [Field L] [CharZero L] (α : L),
      ((toPoly S1).map (algebraMap ℚ L)).IsRoot α → aeval α (toPoly S2) = 0 := by
    intro L _ _ α hα
    rw [hS2, map_mul]
    have : aeval α (toPoly S1) = 0 := by rw [← eval_map_algebraMap]; exact hα
    rw [this, zero_mul]
  obtain ⟨l2, hl2, hlen2, hr2⟩ := hrS2
  have hroots : ∀ α : Kb, ((toPoly (liftK (K := NF M) D)).map j).eval α = 0 →
      ((toPoly (liftK (K := NF M) q)).map j).eval α ≠ 0 → α ∈ Set.range j := by
    intro α hDα hqα
    rw [hmapKb] at hDα hqα
    have hS1α := isRoot_nbPart q D hD (algebraMap ℚ Kb) α hDα hqα
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp (root_mem_map j hS2sq.ne_zero hl2 hlen2 hr2
      (hS1S2 α hS1α))
    exact ⟨a, rfl⟩
  have hsqD : ∀ α : NF M, (toPoly (liftK (K := NF M) D)).eval α = 0 →
      (toPoly (liftK (K := NF M) q)).eval α ≠ 0 →
      ∃ β : NF M, β ≠ 0 ∧ β * β = (toPoly (liftK (K := NF M) q)).eval α := by
    intro α hDα hqα
    rw [hL] at hDα hqα
    have hS1α := isRoot_nbPart q D hD (algebraMap ℚ (NF M)) α hDα hqα
    obtain ⟨β, hβ0, hβ⟩ := hsqS2 α (hS1S2 α hS1α)
    refine ⟨β, hβ0, ?_⟩
    rw [hβ, pValG, hL, eval_map_algebraMap]
  have hlcK : ∃ γ : NF M, γ ≠ 0 ∧ γ * γ = (toPoly (liftK (K := NF M) q)).leadingCoeff := by
    refine ⟨γ, hγ0, ?_⟩
    rw [hγ, hL, leadingCoeff_map_of_injective (algebraMap ℚ (NF M)).injective,
      show lead (trim q) = lcT q from rfl, lcT_eq]
    rfl
  set bsK : List (NF M) := as.map fun a : ℕ ↦ (a : NF M)
  have hbase : ∀ b ∈ bsK, ∃ a ∈ as, b = (a : NF M) := fun b hb ↦ by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb; exact ⟨a, ha, rfl⟩
  have hcastK : ∀ a : ℕ, ((a : ℚ) : NF M) = (a : NF M) := fun a ↦ by simp
  have hbroot : ∀ a ∈ as, aeval ((a : ℚ) : NF M) (toPoly S2) = 0 := by
    intro a ha
    rw [hS2, map_mul, map_list_prod]
    refine mul_eq_zero_of_right _ (List.prod_eq_zero_iff.mpr (List.mem_map.mpr
      ⟨X - C (a : ℚ), List.mem_map_of_mem (List.mem_map_of_mem ha), by simp⟩))
  obtain ⟨B0, hB0⟩ := hypDecideEvenK_eventually M hMZ (liftK q) (g := g)
    (by rw [hL, natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective, hq2]) hqLsq e he
    (liftK A) (liftK D) (by rw [hL]; exact (Polynomial.map_ne_zero_iff
      (algebraMap ℚ (NF M)).injective).mpr hD)
    hroots hsqD hlcK bsK (by simp [bsK, hasl]) (hasnd.map Nat.cast_injective)
    (fun b hb hDb ↦ by
      obtain ⟨a, ha, rfl⟩ := hbase b hb
      have e1 : ((toPoly D).map (algebraMap ℚ (NF M))).eval (a : NF M) =
          algebraMap ℚ (NF M) ((toPoly D).eval (a : ℚ)) := by
        rw [show (a : NF M) = algebraMap ℚ (NF M) (a : ℚ) by simp, eval_map, eval₂_hom]
      rw [hL, e1] at hDb
      have hDa : (toPoly D).eval (a : ℚ) = 0 := (algebraMap ℚ (NF M)).injective (by
        rw [hDb, map_zero])
      by_cases hqa : (toPoly q).eval (a : ℚ) = 0
      · exact (hasg a ha).2 hqa
      · have := isRoot_nbPart q D hD (RingHom.id ℚ) (a : ℚ) (by simpa using hDa)
          (by simpa using hqa)
        exact (hasg a ha).1 (by simpa using this))
    (fun b hb ↦ by
      obtain ⟨a, ha, rfl⟩ := hbase b hb
      obtain ⟨β, hβ0, hβ⟩ := hsqS2 _ (hbroot a ha)
      refine ⟨β, hβ0, ?_⟩
      rw [hβ, pValG, hL, eval_map_algebraMap, hcastK])
  refine ⟨B0, fun B hB ↦ ?_⟩
  have hgq : (q.length - 3) / 2 = g := by omega
  unfold hypDecideEvenQ
  rw [if_neg hA0, if_neg (by rw [hDz]; exact Bool.false_ne_true), hgq]
  rw [htower]
  simp only
  rw [hrs, hrse]
  exact hB0 B hB

section Decides

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The even-degree decision over `ℚ`**: for `q ∈ ℚ[x]` squarefree of degree `2g + 2` (given
without trailing zeros) and any `A, D` with `D ≠ 0`, `hypDecideEvenQ` answers for all large
bounds, and the answer is `true` exactly when `∫ A/(D √q) dx` is elementary. -/
theorem hypDecideEvenQ_decides [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (q : CPoly ℚ) {g : ℕ} (hlen : q.length = 2 * g + 3) (hlcq : q.getD (2 * g + 2) 0 ≠ 0)
    (hqsq : Squarefree (toPoly q)) (hy : y ^ 2 = aeval x (toPoly q))
    (hgen : ∀ z : E, InHyp Kc x y z) (A D : CPoly ℚ) (hD : toPoly D ≠ 0) :
    ∃ B0, ∀ B, B0 ≤ B → ∃ ans, hypDecideEvenQ q A D B = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨B0, hB0⟩ := hypDecideEvenQ_eventually q hlen hlcq hqsq A D hD
  refine ⟨B0, fun B hB ↦ ?_⟩
  obtain ⟨ans, h⟩ := Option.ne_none_iff_exists'.mp (hB0 B hB)
  exact ⟨ans, h, hypDecideEvenQ_spec hC hCall x y hx q hy hgen A D B ans h⟩

end Decides

end Jac
