import RischTragerBronstein.Mixed.NKSearchTR

/-!
# Constant curves over a logarithm: the exact part is decided

**`nk_decidesTR`**: for `θⁿ + ∑ aᵢ(t) θⁱ = 0` over a logarithmic level `t′ = η` with a single
place at infinity and **constant coefficients** (`aᵢ ∈ ℚ[t]`), and `f = ∑ bⱼ(t) θʲ`: for every large
bound `N`, `elM` decides `τ(f)/n` and `searchTR` decides the exact part, and together they decide
whether `f` has an elementary integral — no basis, shift or certificate has to be supplied (the
search is complete by `exactTR_exists`: integral bases normal at infinity with logarithmic
derivation matrices exist, `exists_logBasis`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- At a primitive level, `η` is not a derivative. -/
lemma eta_not_deriv_M (m : ℕ) (h0 : T.Tr m) (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m)) : ∀ y : T.F m, y′ ≠ (T.MP m h0).sem η := by
  intro y hy
  have hc : (T.ts m - (y : L))′ = 0 := by
    rw [Derivation.map_sub, T.deriv_ts_L m h0 hm hk, ← hy]
    exact sub_self _
  obtain ⟨κ, hκ⟩ := T.hconst _ hc
  apply htr
  have hmem : T.ts m ∈ T.F m := by
    have : T.ts m = algebraMap Cc L κ + (y : L) := by rw [hκ]; ring
    rw [this]
    exact add_mem (T.const_mem m κ) y.2
  exact isAlgebraic_algebraMap (R := T.F m) (⟨T.ts m, hmem⟩ : T.F m)

/-- The coefficients of `nkPC` for a constant curve. -/
lemma nkPC_sem_const (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m))) (F0 : ℚ[X][X])
    (hF0 : F0.Monic) (hlen : Pp.length = F0.natDegree)
    (hcoef : ∀ i < Pp.length, T.evP m (Pp.getD i []) = aeval (T.ts m) (F0.coeff i)) (i : ℕ) :
    (T.MPr (m + 1) h1).sem ((nkPC Fc ks m Pp).getD i (MOr Fc ks (m + 1)).zero) =
      T.phi m ((F0.coeff i).map (algebraMap ℚ (T.F m))) := by
  have hc := coeff_toPoly_sem (T.MPr (m + 1) h1) (nkPC Fc ks m Pp) i
  rw [T.toPoly_nkPC m h1 Pp] at hc
  rw [← hc]
  apply Subtype.ext
  rw [coe_phi, aeval_map_algebraMap]
  rcases lt_trichotomy i Pp.length with hi | hi | hi
  · rw [polyF_coeff _ _ _ hi, ← hcoef i hi]
    exact T.sem_poly_code m h1 _
  · subst hi
    have hm1 := (polyF_monic (fun i ↦ (T.MPr (m + 1) h1).sem (polyCode Fc ks m (Pp.getD i [])))
      Pp.length).coeff_natDegree
    rw [polyF_natDegree] at hm1
    rw [hm1, hlen, hF0.coeff_natDegree, map_one, OneMemClass.coe_one]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [polyF_natDegree]; exact hi),
      coeff_eq_zero_of_natDegree_lt (by omega), map_zero, ZeroMemClass.coe_zero]

set_option maxHeartbeats 4000000 in
/-- **The decision for constant curves over a logarithm**: for every large bound, `elM` decides
`τ(f)/n`, `searchTR` decides the exact part, and together they decide `f`. -/
theorem nk_decidesTR (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m)))
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (hlen : Pp.length = F0.natDegree)
    (hcoef : ∀ i < Pp.length, T.evP m (Pp.getD i []) = aeval (T.ts m) (F0.coeff i)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchTR Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  set q := nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s
  obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m + 1) (by omega)
  obtain ⟨N₀, hN₀⟩ := elM_decides_any hmon hdeg hshF T' (m + 1) hT'n hc hT'gen q
  -- `L` is algebraic over `F (m + 1)`
  have hmem : ∀ i, T.evP m (Pp.getD i []) ∈ T.F (m + 1) := fun i ↦ T.evP_mem m (T.ev_mem m) _
  have hθi : IsIntegral (T.F (m + 1)) θ := by
    refine ⟨polyF (fun i ↦ (⟨T.evP m (Pp.getD i []), hmem i⟩ : T.F (m + 1))) Pp.length,
      polyF_monic _ _, ?_⟩
    rw [← eval_map, polyF_eval_map]
    exact hθ
  have halg : Algebra.IsAlgebraic (T.F (m + 1)) L := ⟨fun z ↦ by
    have := IntermediateField.isAlgebraic_adjoin_simple hθi
    exact (IntermediateField.isAlgebraic_iff (x := (⟨z, hgen z⟩ :
      IntermediateField.adjoin (T.F (m + 1)) {θ}))).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have h0 : HasElementaryIntegral (T.ev (m + 1) q) ↔ HasElementaryIntegral (T'.ev (m + 1) q) := by
    rw [← hasElementaryIntegral_isAlgebraic_iff halg]
    rw [show algebraMap (T.F (m + 1)) L (T'.ev (m + 1) q) = T.ev (m + 1) q from
      hT'ev (m + 1) le_rfl q]
  -- the search answers for large bounds
  have hn0 := (T.nkShape_spec m hTr.of_succ Pp hsh).1
  have hPlen : (nkPC Fc ks m Pp).length = F0.natDegree + 1 := by
    have := length_nkPC (Fc := Fc) (ks := ks) m Pp; omega
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 →
      ∀ j < F0.natDegree, a j = 0 := by
    rw [← hlen]; exact T.nkCurve_ind m hTr Pp hsh θ hθ
  obtain ⟨A, B, Ai, Bi, r, hex⟩ := T.exactTR_exists m hTr (by omega) hk (hTr m (by omega))
    (paramLimC Fc ks lv m) MSm.lim
    (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega)))
    F0 hF0 (by omega) (nkPC Fc ks m Pp) hPlen (T.nkPC_sem_const m hTr Pp F0 hF0 hlen hcoef) θ hP hind
    (nkRest Fc ks m (nkFl Fc ks m fp) q)
  obtain ⟨B0, hB0⟩ := searchTR_complete Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
    (nkRest Fc ks m (nkFl Fc ks m fp) q) F0.natDegree (by omega) A B Ai Bi r hex
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (hB0 N (le_of_max_le_right hN))
  obtain ⟨r', Tc, Ti, hex'⟩ := searchTR_sound Fc ks m η _ _ _ N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffTR hmon hdeg m hn hc hk Pp hsh θ hθ hgen s hs fp r' Tc Ti res hex', h0, hiff]

set_option maxHeartbeats 4000000 in
/-- **The decision with precomputed basis candidates** (`searchTRP`, tried before the enumeration). -/
theorem nk_decidesTRP (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m)))
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (hlen : Pp.length = F0.natDegree)
    (hcoef : ∀ i < Pp.length, T.evP m (Pp.getD i []) = aeval (T.ts m) (F0.coeff i))
    (pre : List (List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ))) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchTRP Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  set q := nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s
  obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m + 1) (by omega)
  obtain ⟨N₀, hN₀⟩ := elM_decides_any hmon hdeg hshF T' (m + 1) hT'n hc hT'gen q
  -- `L` is algebraic over `F (m + 1)`
  have hmem : ∀ i, T.evP m (Pp.getD i []) ∈ T.F (m + 1) := fun i ↦ T.evP_mem m (T.ev_mem m) _
  have hθi : IsIntegral (T.F (m + 1)) θ := by
    refine ⟨polyF (fun i ↦ (⟨T.evP m (Pp.getD i []), hmem i⟩ : T.F (m + 1))) Pp.length,
      polyF_monic _ _, ?_⟩
    rw [← eval_map, polyF_eval_map]
    exact hθ
  have halg : Algebra.IsAlgebraic (T.F (m + 1)) L := ⟨fun z ↦ by
    have := IntermediateField.isAlgebraic_adjoin_simple hθi
    exact (IntermediateField.isAlgebraic_iff (x := (⟨z, hgen z⟩ :
      IntermediateField.adjoin (T.F (m + 1)) {θ}))).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have h0 : HasElementaryIntegral (T.ev (m + 1) q) ↔ HasElementaryIntegral (T'.ev (m + 1) q) := by
    rw [← hasElementaryIntegral_isAlgebraic_iff halg]
    rw [show algebraMap (T.F (m + 1)) L (T'.ev (m + 1) q) = T.ev (m + 1) q from
      hT'ev (m + 1) le_rfl q]
  -- the search answers for large bounds
  have hn0 := (T.nkShape_spec m hTr.of_succ Pp hsh).1
  have hPlen : (nkPC Fc ks m Pp).length = F0.natDegree + 1 := by
    have := length_nkPC (Fc := Fc) (ks := ks) m Pp; omega
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range F0.natDegree, (a j : L) * θ ^ j = 0 →
      ∀ j < F0.natDegree, a j = 0 := by
    rw [← hlen]; exact T.nkCurve_ind m hTr Pp hsh θ hθ
  obtain ⟨A, B, Ai, Bi, r, hex⟩ := T.exactTR_exists m hTr (by omega) hk (hTr m (by omega))
    (paramLimC Fc ks lv m) MSm.lim
    (T.eta_not_deriv_M m hTr.of_succ (by omega) hk (hTr m (by omega)))
    F0 hF0 (by omega) (nkPC Fc ks m Pp) hPlen (T.nkPC_sem_const m hTr Pp F0 hF0 hlen hcoef) θ hP hind
    (nkRest Fc ks m (nkFl Fc ks m fp) q)
  obtain ⟨B0, hB0⟩ := searchTRP_complete Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
    (nkRest Fc ks m (nkFl Fc ks m fp) q) pre
    (searchTR_complete Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) q) F0.natDegree (by omega) A B Ai Bi r hex)
  refine ⟨max N₀ B0, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (hB0 N (le_of_max_le_right hN))
  obtain ⟨r', Tc, Ti, hex'⟩ := searchTRP_sound Fc ks m η _ _ _ pre N res hres
  refine ⟨b, res, hb, hres, ?_⟩
  rw [T.nk_iffTR hmon hdeg m hn hc hk Pp hsh θ hθ hgen s hs fp r' Tc Ti res hex', h0, hiff]

end MTower

end Curves.MT
