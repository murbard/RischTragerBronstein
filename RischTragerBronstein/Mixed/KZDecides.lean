import RischTragerBronstein.Mixed.KZMain
import RischTragerBronstein.Mixed.KYDecides

/-!
# Radicals with poles in `Kₘ ⊗ N`: the decision answers

`kzDecideL` (local torsion certificates over `Kₘ ⊗ N`) answers for every large bound at suitable
residues, unless a component is certified non-torsion while the orders over `t = 0` cannot be
killed (the Mordell–Weil case, `kzDecideL_decides`).

The decision is about codes only, so its facts may be read in any realization of the tower. We
use one over a splitting extension containing a constant root `ρ` of `M` (`exists_root_tower`,
needing no integrability hypothesis). There the points over the poles are valid points of
`yⁿ = A` over `Kₘ ⊗ N` (`kz_ptsM`, from `kz_points` through the injective `ψ_ρ`). The rest is
`kyDecideL_decides`'. With `kzDecide_correct`: `kz_decided`.
-/

open Polynomial Differential IntermediateField CPoly CPoly.Kron Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **A realization of the tower with a constant root of `P`** (over a splitting extension). -/
theorem exists_root_tower (P : ℚ[X]) (hP : 0 < P.natDegree) :
    ∃ (E : Type u) (_ : Field E) (_ : Differential E) (_ : CharZero E)
      (TE : MTower Fc ks (constants E) E) (ρ : E), TE.n = T.n ∧ aeval ρ P = 0 ∧ ρ′ = 0 := by
  have hP0 : P ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hP; omega
  obtain ⟨E₂, _, _, _, _, _, -, -, -, hspl⟩ := split_ext L 1 one_pos 1 one_ne_zero P hP0
  obtain ⟨TE, hTEn, -, -, -⟩ := T.exists_lift E₂
  obtain ⟨ρ, hρ⟩ := hspl.exists_eval_eq_zero (by
    rw [degree_map]; exact fun h ↦ by rw [degree_eq_natDegree hP0] at h; norm_cast at h; omega)
  have hρP : aeval ρ P = 0 := by rwa [eval_map, ← aeval_def] at hρ
  exact ⟨E₂, inferInstance, inferInstance, inferInstance, TE, ρ, hTEn, hρP,
    deriv_eq_zero_of_isAlgebraic ρ ⟨P, hP0, hρP⟩⟩

set_option maxHeartbeats 1600000 in
/-- **The points over the poles** are points of `yⁿ = A` over `Kₘ ⊗ N`, pairwise distinct. -/
theorem kz_ptsM (m : ℕ) (hM : T.MixHyp (m + 1)) {g : LC m} (hk : ks m = .exp g) (n j : ℕ)
    (hn : 0 < n) (hjc : Nat.Coprime j n) (A B : GPoly (LC m)) (kt l : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hok : kzOK Fc ks m M A B kt l cs dC = true)
    (hc : kzConst Fc ks m n j M g A B kt l cs = true)
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true) :
    IsPrimitiveRoot (ofQ Fc m M zN) n ∧
    (∀ i, kzBe Fc ks m n j M g A B kt l cs zN gs i ≠ 0 ∧
      kzBe Fc ks m n j M g A B kt l cs zN gs i ^ n =
        (toPoly (kyFA Fc m M A)).eval (kzAl Fc m n M cs i)) ∧
    Function.Injective fun i ↦ (kzAl Fc m n M cs i, kzBe Fc ks m n j M g A B kt l cs zN gs i) := by
  have hm : T.Tr m := hM.tr.of_succ
  obtain ⟨htrim, hlen, hz1, hz2, -, -⟩ := kzFieldOK_spec hF
  have hM0 : toPoly M ≠ 0 := by
    intro h0
    have := (trim_eq_nil_iff M).mpr h0
    rw [htrim] at this; rw [this] at hlen; simp at hlen
  have hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0 :=
    hmin_of_irr M ρ hρ (K := KF Fc m) (by rw [← toPoly_liftQ]; exact Fact.out)
  have hζ := zetaM_prim Fc m M htrim hlen n hn zN hz1 hz2
  have hok' := T.kzOK_spec m hm M ρ hρ A B kt l cs dC hok
  have hD0 : ∀ q < cs.length, T.psiNFM m hm M ρ hρ (kzD Fc ks m M g cs q) ≠ 0 :=
    fun q hq ↦ T.kzD_ne m hM hk M ρ hρ hM0 cs q (hok'.2.2 q hq).1
  obtain ⟨-, hβf, -⟩ := T.kz_points m hm n j hn hjc g A B kt l M cs dC ρ hρ zN gs hok hc hF hmin
    hD0
  have hcinj := T.kz_cinj m hm M ρ hρ A B kt l cs dC hok
  have hpf : (toPoly (kyFA Fc m M A)).map (T.psiNFM m hm M ρ hρ) = GPoly.toPoly (T.MP m hm) A :=
    T.kyFA_map m hm M ρ hρ A
  have hin : ∀ i : Fin (cs.length * n), (i : ℕ) / n < cs.length :=
    fun i ↦ (Nat.div_lt_iff_lt_mul hn).mpr i.2
  have hβ0 : ∀ q < cs.length, kzBeta Fc ks m n j M g A B kt l cs gs q ≠ 0 := fun q hq h0 ↦
    (hβf q hq).1 (by
      change T.psiNFM m hm M ρ hρ (kzBeta Fc ks m n j M g A B kt l cs gs q) = 0
      rw [h0, map_zero])
  refine ⟨hζ, fun i ↦ ⟨?_, ?_⟩, fun i i' h ↦ ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) (hβ0 _ (hin i))
  · have hβn : T.psiNFM m hm M ρ hρ (kzBeta Fc ks m n j M g A B kt l cs gs (i / n)) ^ n =
        (GPoly.toPoly (T.MP m hm) A).eval (T.psiNFM m hm M ρ hρ (kzC Fc m M cs (i / n))) :=
      (hβf _ (hin i)).2
    apply (T.psiNFM m hm M ρ hρ).injective
    rw [kzBe, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul, map_pow,
      hβn, ← hpf, eval_map, eval₂_at_apply]
    rfl
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : (i : ℕ) / n = i' / n := by
      have : T.psiNFM m hm M ρ hρ (kzC Fc m M cs (i / n)) =
          T.psiNFM m hm M ρ hρ (kzC Fc m M cs (i' / n)) := congrArg _ h1
      exact congrArg Fin.val (hcinj (a₁ := ⟨_, hin i⟩) (a₂ := ⟨_, hin i'⟩) this)
    simp only [kzBe, h1'] at h2
    have h3 := mul_right_cancel₀ (hβ0 _ (hin i')) h2
    have h4 := hζ.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h3
    apply Fin.ext
    rw [← Nat.div_add_mod i n, ← Nat.div_add_mod i' n, h1', h4]

section Solve

variable (m : ℕ) (hm : T.Tr m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]

include T hm in
set_option maxHeartbeats 1600000 in
open Classical in
/-- `kzSolveC` answers when every component is torsion. -/
lemma kzSolveC_isSome (n j : ℕ) (hn1 : 1 < n) (g : LC m)
    (htrim : CPoly.trim M = M) (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A B : GPoly (LC m))
    (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (hvK : ∀ i, kzBe Fc ks m n j M g A B kt l cs zN gs i ≠ 0 ∧
      kzBe Fc ks m n j M g A B kt l cs zN gs i ^ n =
        (toPoly (kyFA Fc m M A)).eval (kzAl Fc m n M cs i))
    (hinjK : Function.Injective fun i ↦
      (kzAl Fc m n M cs i, kzBe Fc ks m n j M g A B kt l cs zN gs i))
    (hsqK : Squarefree (toPoly (kyFA Fc m M A)))
    (hcop2 : Nat.Coprime n ((kyFA Fc m M A).length - 1))
    (hP0sq : Squarefree ((toPoly (A.map (trC Fc m))).map (eM Fc m M)))
    (hP0deg : 0 < ((toPoly (A.map (trC Fc m))).map (eM Fc m M)).natDegree)
    (rs : ℕ → ℕ) (Bd : ℕ) (extra : List (LC (m + 1)))
    (hall : ∀ f ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length), ∃ N,
      kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs f =
        some (some N)) :
    (kzSolveC Fc ks lv m n j g M zN gs A B kt l cs dC (fun fK ↦ localCert fK n) (primesBelow Bd) Bd
      rs extra).isSome := by
  have hn0 : 0 < n := by omega
  have hspec := torsOracleC_spec (redAtNFM Fc m M rs) (localCert (kyFA Fc m M A) n)
    (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) (primesBelow Bd) Bd hsqK hcop2
  have hΓ : ∀ i, ((n : ℕ) : NFM Fc m M) * kzBe Fc ks m n j M g A B kt l cs zN gs i ^ (n - 1) ≠ 0 ∧
      kzBe Fc ks m n j M g A B kt l cs zN gs i ^ n =
        (toPoly (kyFA Fc m M A)).eval (kzAl Fc m n M cs i) :=
    fun i ↦ ⟨mul_ne_zero (by exact_mod_cast hn0.ne') (pow_ne_zero _ (hvK i).1), (hvK i).2⟩
  unfold kzSolveC
  dsimp only
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length) with hcomps
  set tors := comps.map (kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n)
    (primesBelow Bd) Bd rs) with htorsdef
  have hwit : ∀ f N, kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n)
      (primesBelow Bd) Bd rs f = some (some N) →
      kzWit Fc ks m n j M g A B kt l cs zN gs f N ≠ none := by
    intro f N hN
    have hP := ((hspec _ _ _ (kyMult n j M zN gs cs.length f) hvK hinjK).1 N hN).2
    exact witW_ne_none _ n hn0 _ _ _ _ N hΓ hP
  have hws : ∀ p ∈ List.zip comps tors,
      kzWit Fc ks m n j M g A B kt l cs zN gs p.1 ((p.2.getD none).getD 0) ≠ none := by
    intro p hp
    have hp1 : p.1 ∈ comps := (List.of_mem_zip hp).1
    have hp2 : p.2 = kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n)
        (primesBelow Bd) Bd rs p.1 := by
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
      rw [← hpi]
      simp [htorsdef]
    obtain ⟨N, hN⟩ := hall p.1 hp1
    rw [hp2, hN]
    exact hwit p.1 N hN
  rcases hW : ((List.zip comps tors).map fun p ↦
      kzWit Fc ks m n j M g A B kt l cs zN gs p.1 ((p.2.getD none).getD 0)).allSome with _ | Wbs
  · exfalso
    refine allSome_ne_none _ (fun y hy h0 ↦ ?_) hW
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    exact hws p hp h0
  · rcases hC : (Wbs.map (kyColM Fc ks m n M A (MO Fc ks m).one j)).allSome with _ | colss
    · exfalso
      refine allSome_ne_none _ (fun y hy h0 ↦ ?_) hC
      obtain ⟨Wb, hWb, rfl⟩ := List.mem_map.mp hy
      obtain ⟨p, -, hpw⟩ := List.mem_map.mp (mem_of_allSome hW hWb)
      obtain ⟨hWb0, hWbd, -⟩ := witW_spec (kyFA Fc m M A) n hn0 _ _ _ _ _ hΓ hpw
      have := T.kyColM_isSome m M n hn1 hm htrim Wb hWb0
        (natDegree_lt_of_witW hWb0 fun i a h ↦ (hWbd i a h).1) A hP0sq hP0deg (MO Fc ks m).one j
      rw [h0] at this; exact absurd this (by simp)
    · simp only [hW, hC, Option.isSome_some]

end Solve

set_option maxHeartbeats 8000000 in
open Classical in
/-- **`kzDecideL` answers** for every large bound, at suitable residues (accepted data), unless a
component is certified non-torsion while the orders over `t = 0` cannot be killed: either some
`ℓ`-th root (`ℓ ∣ n` prime) of `A(0)` exists while no `n`-th root does, or some point `(0, ζᵏ)` of
the twist is certified non-torsion (the Mordell–Weil case). -/
theorem kzDecideL_decides (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime n (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (hn1 : 1 < n) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n) (hr0 : cs.length ≠ 0)
    (hok : kzOK Fc ks m M A B kt l cs dC = true)
    (hF : kzConst Fc ks m n j M g A B kt l cs = true →
      kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (kzDecideL Fc ks lv m n j g M zN gs A B kt l cs dC (primesBelow Bd) Bd rs).isSome ∨
      ((((List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)).map
          (kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bd) Bd
            rs)).any (· == some none) = true ∧
        ((krZ Fc ks lv m n A = none ∧ ∃ ℓ, ℓ.Prime ∧ ℓ ∣ n ∧ (krZ Fc ks lv m ℓ A).isSome) ∨
          ∃ z, krZ Fc ks lv m n A = some z ∧ ∃ k < n,
            kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
              (primesBelow Bd) Bd rs k = some none)) := by
  have hn0 : 0 < n := by omega
  have hacc : (!(decide (1 < n) && decide (0 < j) && decide (j < n) &&
      decide (Nat.Coprime j n))) = false := by
    simp only [decide_eq_true hn1, decide_eq_true hj0, decide_eq_true hjn, decide_eq_true hjc]
    rfl
  by_cases hcst : kzConst Fc ks m n j M g A B kt l cs = true
  swap
  · refine ⟨fun _ ↦ 0, 0, fun _ _ ↦ Or.inl ?_⟩
    unfold kzDecideL kzDecideC
    dsimp only
    rw [if_neg (by rw [hacc]; decide), if_neg hr0, if_neg (by simp [hok]),
      if_pos (by simpa using hcst)]
    rfl
  have hFt := hF hcst
  obtain ⟨htrim, hlen, -, -, -, -⟩ := kzFieldOK_spec hFt
  have hMdeg : 0 < (toPoly M).natDegree := by
    have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
    have := CPoly.length_trim (p := M) (by rw [htrim]; exact hMne)
    rw [htrim] at this; omega
  -- a tower with a constant root of `M`
  obtain ⟨E, _, _, _, TE, ρE, hTEn, hρE, hρd⟩ := T.exists_root_tower (toPoly M) hMdeg
  have hTEn' : TE.n = m + 1 := by rw [hTEn, hn]
  have MS := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : TE.Tr (m + 1) := MS.hyp.tr
  have hTm : TE.Tr m := hTr.of_succ
  obtain ⟨ρ, hρ, -⟩ := TE.kz_rootF m hTm n j hn0 g A B kt l M cs zN gs hFt ρE hρE hρd
  have hsq := GPoly.squarefreeCheck_sound (TE.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (TE.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (TE.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (TE.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime n (GPoly.toPoly (TE.MP m hTm) A).natDegree := by
    rw [hdeg1]; exact hcop
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((TE.MP m hTm).isZero_iff _).mp h)
        (TE.kzOK_spec m hTm M ρ hρ A B kt l cs dC hok).1
  obtain ⟨hζ, hvK, hinjK⟩ := TE.kz_ptsM m MS.hyp hk n j hn0 hjc A B kt l M cs dC ρ hρ zN gs hok
    hcst hFt
  obtain ⟨hd, hlc, hsqK, hcop2, hP0sq, hP0deg⟩ := TE.kyFA_facts m hTm M A A 1 one_ne_zero
    (by rw [map_one, one_mul]; exact TE.toPoly_trC_map m hTm A) hsq n hcopA hdegA
  obtain ⟨D, hD, mZ, hmZ, hsepM, hdegM⟩ := M_clear Fc m M htrim hlen
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length) with hcomps
  -- the twist, for an `n`-th root `z` of `A(0)`
  have hPsi : ∀ z, krZ Fc ks lv m n A = some z →
      kyKap Fc ks m n A z ≠ 0 ∧
      let fK := kyFA Fc m M (krAh Fc ks m n A z (kyKap Fc ks m n A z))
      let P0 := (toPoly ((krAh Fc ks m n A z (kyKap Fc ks m n A z)).map (trC Fc m))).map
        (eM Fc m M)
      0 < fK.length - 1 ∧ fK.getD (fK.length - 1) 0 ≠ 0 ∧ Squarefree (toPoly fK) ∧
        Nat.Coprime n (fK.length - 1) ∧ Squarefree P0 ∧ 0 < P0.natDegree ∧
        (toPoly fK).eval 0 = 1 := by
    intro z hz
    obtain ⟨-, -, hκ0⟩ := TE.kr_z_facts hmon hdeg m n hn0 hTEn' hc A ha0 z hz
    obtain ⟨hz0, hzκ⟩ := TE.kr_zsem hmon hdeg m n hn0 hTEn' hc hTm A ha0 z hz
    exact ⟨hκ0, TE.kyPsi_facts m hTm M n A hsq hcopA hdegA z _ hκ0 hz0 hzκ⟩
  have hζk : ∀ k : ℕ, ofQ Fc m M zN ^ k ≠ 0 := fun k ↦ pow_ne_zero _ (hζ.ne_zero hn0.ne')
  have hζn : ∀ k : ℕ, (ofQ Fc m M zN ^ k) ^ n = 1 := fun k ↦ by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  -- the queries
  set Q : (ℕ ⊕ Option ℕ) → (ℕ → ℕ) → Prop := fun o rs ↦ match o with
    | Sum.inl f => ∃ B0, ∀ Bb, B0 ≤ Bb →
        (kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bb) Bb
          rs f).isSome
    | Sum.inr none => ∀ z, krZ Fc ks lv m n A = some z → ∃ B0, ∀ Bb, B0 ≤ Bb →
        (kyTorsPsiC Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
          (primesBelow Bb) Bb rs).isSome
    | Sum.inr (some k) => ∀ z, krZ Fc ks lv m n A = some z → ∃ B0, ∀ Bb, B0 ≤ Bb →
        (kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
          (primesBelow Bb) Bb rs k).isSome with hQdef
  obtain ⟨rs, hrs⟩ := exists_rs_many Fc m
    (comps.map Sum.inl ++ (Sum.inr none :: (List.range n).map (Sum.inr ∘ some))) Q
    (fun o _ ↦ by
      rcases o with f | _ | k
      · exact kfm_query_els Fc m M n (by omega) _ hζ D hD mZ hmZ hsepM hdegM hd hlc hsqK hcop2
          _ _ (kyMult n j M zN gs cs.length f) hvK hinjK
      · rcases hz : krZ Fc ks lv m n A with _ | z
        · exact ⟨[], fun rs _ _ z' hz' ↦ absurd (hz.symm.trans hz') (by simp)⟩
        · obtain ⟨-, hd', hlc', hsq', hcop', -, -, hf0⟩ := hPsi z hz
          obtain ⟨Els, hEls⟩ := kfm_query_els Fc m M n (by omega) _ hζ D hD mZ hmZ hsepM hdegM
            hd' hlc' hsq' hcop' (fun _ : Fin n ↦ (0 : NFM Fc m M))
            (fun k ↦ ofQ Fc m M zN ^ (k : ℕ)) (ramMult n)
            (fun k ↦ ⟨hζk k, by rw [hζn, hf0]⟩)
            (fun k k' h ↦ Fin.ext (hζ.pow_inj k.2 k'.2 (congrArg Prod.snd h)))
          refine ⟨Els, fun rs h0 hE z' hz' ↦ ?_⟩
          obtain rfl := Option.some.inj (hz.symm.trans hz')
          exact hEls rs h0 hE
      · rcases hz : krZ Fc ks lv m n A with _ | z
        · exact ⟨[], fun rs _ _ z' hz' ↦ absurd (hz.symm.trans hz') (by simp)⟩
        · obtain ⟨-, hd', hlc', hsq', hcop', -, -, hf0⟩ := hPsi z hz
          obtain ⟨Els, hEls⟩ := kfm_query_els Fc m M n (by omega) _ hζ D hD mZ hmZ hsepM hdegM
            hd' hlc' hsq' hcop' ![(0 : NFM Fc m M)] ![ofQ Fc m M zN ^ k] ![1]
            (fun i ↦ by fin_cases i; exact ⟨hζk k, by simp only [Matrix.cons_val_fin_one]; rw [hζn, hf0]⟩)
            (fun a b _ ↦ Subsingleton.elim a b)
          refine ⟨Els, fun rs h0 hE z' hz' ↦ ?_⟩
          obtain rfl := Option.some.inj (hz.symm.trans hz')
          exact hEls rs h0 hE)
  -- uniform bounds
  obtain ⟨B1, hB1⟩ := eventually_list comps (fun f Bb ↦
    (kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bb) Bb
      rs f).isSome) fun f hf ↦ hrs (Sum.inl f) (by simp [hf])
  obtain ⟨B2, hB2⟩ : ∃ B2, ∀ Bb, B2 ≤ Bb → ∀ z, krZ Fc ks lv m n A = some z →
      (kyTorsPsiC Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bb) Bb rs).isSome := by
    rcases hz : krZ Fc ks lv m n A with _ | z
    · exact ⟨0, fun _ _ z' hz' ↦ absurd hz' (by simp)⟩
    · obtain ⟨B2, h2⟩ := hrs (Sum.inr none) (by simp) z hz
      exact ⟨B2, fun Bb hBb z' hz' ↦ by obtain rfl := Option.some.inj hz'; exact h2 Bb hBb⟩
  obtain ⟨B3, hB3⟩ : ∃ B3, ∀ Bb, B3 ≤ Bb → ∀ z, krZ Fc ks lv m n A = some z → ∀ k < n,
      (kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bb) Bb rs k).isSome := by
    rcases hz : krZ Fc ks lv m n A with _ | z
    · exact ⟨0, fun _ _ z' hz' ↦ absurd hz' (by simp)⟩
    · obtain ⟨B3, h3⟩ := eventually_list (List.range n) (fun k Bb ↦
        (kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
          (primesBelow Bb) Bb rs k).isSome)
        fun k hk ↦ hrs (Sum.inr (some k)) (by simp [List.mem_range.mp hk]) z hz
      exact ⟨B3, fun Bb hBb z' hz' k hk ↦ by
        obtain rfl := Option.some.inj hz'; exact h3 Bb hBb k (List.mem_range.mpr hk)⟩
  refine ⟨rs, max B1 (max B2 B3), fun Bd hBd ↦ ?_⟩
  have hB1' := hB1 Bd (le_of_max_le_left hBd)
  have hB2' := hB2 Bd (le_of_max_le_left (le_of_max_le_right hBd))
  have hB3' := hB3 Bd (le_of_max_le_right (le_of_max_le_right hBd))
  set tors := comps.map (kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n)
    (primesBelow Bd) Bd rs) with htorsdef
  have hnone : ¬ tors.any (· == none) = true := by
    intro h
    obtain ⟨x, hx, hx0⟩ := List.any_eq_true.mp h
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    have := hB1' f hf
    simp only [beq_iff_eq] at hx0
    rw [hx0] at this; exact absurd this (by simp)
  have hallT : ¬ tors.any (· == some none) = true → ∀ f ∈ comps, ∃ N,
      kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs f =
        some (some N) := by
    intro hsn f hf
    rcases h : kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bd)
      Bd rs f with _ | _ | N
    · have := hB1' f hf; rw [h] at this; exact absurd this (by simp)
    · exfalso; apply hsn
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, hf, h⟩, by simp⟩
    · exact ⟨N, rfl⟩
  have hsolve := fun extra hsn ↦ TE.kzSolveC_isSome (lv := lv) m hTm M n j hn1 g htrim zN gs A
    B kt l cs dC hvK hinjK hsqK hcop2 hP0sq hP0deg rs Bd extra (hallT hsn)
  -- the zero queries
  have hzero : ∀ z, krZ Fc ks lv m n A = some z →
      ¬ kyZeroTorsC Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bd) Bd rs = true →
      ∃ k < n, kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bd) Bd rs k = some none := by
    intro z hz hzt
    by_contra hcon
    push Not at hcon
    apply hzt
    refine List.all_eq_true.mpr fun k hk ↦ ?_
    have hk' := List.mem_range.mp hk
    have hs := hB3' z hz k hk'
    rcases hq : kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
      (primesBelow Bd) Bd rs k with _ | _ | N
    · rw [hq] at hs; exact absurd hs (by simp)
    · exact absurd hq (hcon k hk')
    · change (match kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bd) Bd rs k with
        | some (some _) => true
        | _ => false) = true
      rw [hq]
  unfold kzDecideL kzDecideC
  dsimp only
  rw [if_neg (by rw [hacc]; decide), if_neg hr0, if_neg (by simp [hok]), if_neg (by simp [hcst]),
    if_neg (by simp [hFt])]
  rw [← hcomps, ← htorsdef, if_neg hnone]
  rcases hz : krZ Fc ks lv m n A with _ | z
  · by_cases hsn : tors.any (· == some none) = true
    · by_cases hpr : (List.range (n + 1)).all (fun ℓ ↦ !(decide (Nat.Prime ℓ ∧ ℓ ∣ n)) ||
          (krZ Fc ks lv m ℓ A).isNone) = true
      · left; rw [if_neg (by simp [hsn]), if_pos hpr]; rfl
      · right
        refine ⟨hsn, Or.inl ⟨rfl, ?_⟩⟩
        by_contra hcon
        push Not at hcon
        apply hpr
        refine List.all_eq_true.mpr fun ℓ _ ↦ ?_
        by_cases hℓ : Nat.Prime ℓ ∧ ℓ ∣ n
        · have := hcon ℓ hℓ.1 hℓ.2
          simp only [Bool.not_eq_true, Option.isSome_eq_false_iff] at this
          simp [this]
        · simp [hℓ]
    · left; rw [if_pos (by simp [hsn])]; exact hsolve [] hsn
  · obtain ⟨hκ0, -, -, -, -, hP0sq, hP0deg, hf0⟩ := hPsi z hz
    have hkap : (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
        (A.getD 0 (MO Fc ks m).zero))).getD 0 = kyKap Fc ks m n A z := rfl
    dsimp only
    rw [hkap, if_neg hκ0]
    have hPsiq : (kyTorsPsiC Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bd) Bd rs).isSome := hB2' z hz
    rcases ht : kyTorsPsiC Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
      (primesBelow Bd) Bd rs with _ | _ | N0
    · rw [ht] at hPsiq; exact absurd hPsiq (by simp)
    · dsimp only
      by_cases hsn : tors.any (· == some none) = true
      · by_cases hzt : kyZeroTorsC Fc ks m n M A zN z (kyKap Fc ks m n A z)
            (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs = true
        · left; rw [if_neg (by simp [hsn]), if_pos hzt]; rfl
        · right; exact ⟨hsn, Or.inr ⟨z, rfl, hzero z hz hzt⟩⟩
      · left; rw [if_pos (by simp [hsn])]; exact hsolve [] hsn
    · dsimp only
      by_cases hsn : tors.any (· == some none) = true
      · by_cases hzt : kyZeroTorsC Fc ks m n M A zN z (kyKap Fc ks m n A z)
            (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs = true
        · left; rw [if_neg (by simp [hsn]), if_pos hzt]; rfl
        · right; exact ⟨hsn, Or.inr ⟨z, rfl, hzero z hz hzt⟩⟩
      · left
        rw [if_pos (by simp [hsn])]
        obtain ⟨-, hd', hlc', hsq', hcop', -, -, -⟩ := hPsi z hz
        have hspec := torsOracleC_spec (redAtNFM Fc m M rs)
          (localCert (kyFA Fc m M (krAh Fc ks m n A z (kyKap Fc ks m n A z))) n)
          (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) (primesBelow Bd) Bd hsq' hcop'
        have hv : ∀ k : Fin n, ofQ Fc m M zN ^ (k : ℕ) ≠ 0 ∧
            (ofQ Fc m M zN ^ (k : ℕ)) ^ n = (toPoly (kyFA Fc m M (krAh Fc ks m n A z
              (kyKap Fc ks m n A z)))).eval ((fun _ : Fin n ↦ (0 : NFM Fc m M)) k) :=
          fun k ↦ ⟨hζk k, by rw [hζn, hf0]⟩
        have hinj : Function.Injective fun k : Fin n ↦
            ((fun _ : Fin n ↦ (0 : NFM Fc m M)) k, ofQ Fc m M zN ^ (k : ℕ)) :=
          fun k k' h ↦ Fin.ext (hζ.pow_inj k.2 k'.2 (congrArg Prod.snd h))
        have hP := ((hspec n _ _ (ramMult n) hv hinj).1 N0 ht).2
        have hΓ : ∀ k : Fin n, ((n : ℕ) : NFM Fc m M) * (ofQ Fc m M zN ^ (k : ℕ)) ^ (n - 1) ≠ 0 ∧
            (ofQ Fc m M zN ^ (k : ℕ)) ^ n = (toPoly (kyFA Fc m M (krAh Fc ks m n A z
              (kyKap Fc ks m n A z)))).eval ((fun _ : Fin n ↦ (0 : NFM Fc m M)) k) :=
          fun k ↦ ⟨mul_ne_zero (by exact_mod_cast hn0.ne') (pow_ne_zero _ (hv k).1), (hv k).2⟩
        have hw := witW_ne_none _ n hn0 _ _ _ (ramMult n) N0 hΓ hP
        rcases hwit : kyWitPsi Fc ks m n M A zN z (kyKap Fc ks m n A z) N0 with _ | W0b
        · exact absurd hwit hw
        obtain ⟨hWb0, hWbd, -⟩ := witW_spec _ n hn0 _ _ _ (ramMult n) N0 hΓ hwit
        have hcol := TE.kyColM_isSome m M n hn1 hTm htrim W0b hWb0
          (natDegree_lt_of_witW hWb0 fun i a h ↦ (hWbd i a h).1) _ hP0sq hP0deg z j
        obtain ⟨cols0, hcols0⟩ := Option.isSome_iff_exists.mp hcol
        dsimp only
        rw [hcols0]
        exact hsolve cols0 hsn

open Classical in
/-- **Radicals with poles in `Kₘ ⊗ N` are decided** (accepted data), outside the Mordell–Weil case:
at suitable residues, for every large bound, either `kzDecideL` answers correctly, or some component
is certified non-torsion while the orders over `t = 0` cannot be killed. -/
theorem kz_decided (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime n (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ n = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (hn1 : 1 < n) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n) (hr0 : cs.length ≠ 0)
    (hok : kzOK Fc ks m M A B kt l cs dC = true)
    (hF : kzConst Fc ks m n j M g A B kt l cs = true →
      kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (∃ b, kzDecideL Fc ks lv m n j g M zN gs A B kt l cs dC (primesBelow Bd) Bd rs = some b ∧
        (HasElementaryIntegral (T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) * θ ^ j) ↔
          b = true)) ∨
      ((((List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)).map
          (kzTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bd) Bd
            rs)).any (· == some none) = true ∧
        ((krZ Fc ks lv m n A = none ∧ ∃ ℓ, ℓ.Prime ∧ ℓ ∣ n ∧ (krZ Fc ks lv m ℓ A).isSome) ∨
          ∃ z, krZ Fc ks lv m n A = some z ∧ ∃ k < n,
            kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
              (primesBelow Bd) Bd rs k = some none)) := by
  obtain ⟨rs, B0, h⟩ := T.kzDecideL_decides hmon hdeg m hn hc hk n j M zN gs A hsqc hdegpos hcop
    B kt l cs dC hn1 hj0 hjn hjc hr0 hok hF
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  rcases h Bd hBd with h1 | h1
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    exact Or.inl ⟨b, hb, T.kzDecide_correct hmon hdeg m hn hc hk n j M zN gs A hsqc hdegpos hcop θ
      hθ hgen B kt l cs dC _ _ rs b hb⟩
  · exact Or.inr h1

end MTower

end Curves.MT
