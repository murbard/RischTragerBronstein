import RischTragerBronstein.Mixed.NKExpLog
import RischTragerBronstein.Mixed.NKExactG
import RischTragerBronstein.Mixed.KETower
import RischTragerBronstein.Mixed.NKExactT2

/-!
# The logarithmic part over a non-Kummer extension of an exponential level

`θⁿ + ∑ aᵢ(t) θⁱ = 0` over `t = exp(a)` (`t′ = a′ t`), with a single place above `t = ∞`
(`nkShape`) and a single place above `t = 0` (`nkShape0`: `ord₀ a₀ = d₀`, `gcd(n, d₀) = 1`,
`n ord₀ aᵢ > d₀ (n − i)`). For `f = ∑ bⱼ(t) θʲ` (no finite poles), every unit of a Liouville form is
`c tᵏ` up to an `n`-th power (`unit_pow_exp`), so its logarithmic part lies in `Fₘ`
(`nk_liouvilleE`), and **`f` has an elementary integral iff `f − τ(f)/n` is exact and `τ(f)/n`
has one** (`nk_iffE`, `nk_decidesE`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential

section Codes

variable {α : Type} (O : COps α)

/-- The order of vanishing at `0` of a code polynomial (`0` for the zero polynomial). -/
def trailG : GPoly α → ℕ
  | [] => 0
  | a :: p => if O.isZero a then trailG p + 1 else 0

lemma trailG_eq {K : Type*} [Field K] [Differential K] (M : CField α K O) :
    ∀ p : GPoly α, GPoly.toPoly M p ≠ 0 → trailG O p = (GPoly.toPoly M p).natTrailingDegree
  | [], h => absurd rfl h
  | a :: p, h => by
    rw [GPoly.toPoly_cons] at h
    rw [trailG, GPoly.toPoly_cons]
    split_ifs with ha
    · have ha' : M.sem a = 0 := (M.isZero_iff a).mp ha
      rw [ha', map_zero, zero_add] at h ⊢
      have hp : GPoly.toPoly M p ≠ 0 := fun h0 ↦ h (by rw [h0, mul_zero])
      rw [trailG_eq M p hp, mul_comm, ← pow_one X, natTrailingDegree_mul_X_pow hp]
    · have ha' : M.sem a ≠ 0 := fun h0 ↦ ha ((M.isZero_iff a).mpr h0)
      symm
      refine Nat.eq_zero_of_le_zero (natTrailingDegree_le_of_ne_zero ?_)
      simp [ha']

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The shape of a single place above `t = 0`**: `ord₀ a₀ = d₀`, `gcd(n, d₀) = 1`,
`n ord₀ aᵢ > d₀ (n − i)` for the non-zero `aᵢ`. -/
def nkShape0 (m : ℕ) (Pp : List (GPoly (LC m))) : Bool :=
  let O := MO Fc ks m
  let n := Pp.length
  let d := trailG O (Pp.getD 0 [])
  !GPoly.isZero O (Pp.getD 0 []) && Nat.gcd n d == 1 &&
    (List.range n).all fun i ↦ i == 0 || GPoly.isZero O (Pp.getD i []) ||
      decide (d * (n - i) < n * trailG O (Pp.getD i []))

/-- The Risch-equation solver of level `m` for the exponential solver. -/
def rdeE (lv : (m : ℕ) → LC m) (m : ℕ) : LC m → List (LC m) → List (List ℚ × LC m) :=
  fun c ws ↦ prdeC Fc ks lv m ⟨c, []⟩ ws


/-- The order of the powers `θⁱ` by the fractional part of their weight `i d/n` at infinity. -/
def nkOrd (n d : ℕ) : List ℕ := (List.range n).insertionSort fun i j ↦ i * d % n ≤ j * d % n

/-- `tᵏ` and `t⁻ᵏ` at level `m + 1`. -/
def tPowC (m k : ℕ) : LC (m + 1) :=
  (List.replicate k (MO Fc ks m).zero ++ [(MO Fc ks m).one], [(MO Fc ks m).one])
def tInvPowC (m k : ℕ) : LC (m + 1) :=
  ([(MO Fc ks m).one], List.replicate k (MO Fc ks m).zero ++ [(MO Fc ks m).one])

/-- **The basis normal at infinity** `wᵣ = θ^{π r}/t^{⌊π(r) d/n⌋}` of a curve with a single place
at infinity (`d = deg a₀`), as the matrix `Tc` (`w = Tc θ`), and its inverse `Ti`. -/
def nkTc (m : ℕ) (Pp : List (GPoly (LC m))) : List (List (LC (m + 1))) :=
  let n := Pp.length
  let d := degG (MO Fc ks m) (Pp.getD 0 [])
  let π := nkOrd n d
  (List.range n).map fun r ↦ (List.range n).map fun c ↦
    if c = π.getD r 0 then tInvPowC Fc ks m (π.getD r 0 * d / n) else (MOr Fc ks (m + 1)).zero
def nkTi (m : ℕ) (Pp : List (GPoly (LC m))) : List (List (LC (m + 1))) :=
  let n := Pp.length
  let d := degG (MO Fc ks m) (Pp.getD 0 [])
  let π := nkOrd n d
  (List.range n).map fun i ↦ (List.range n).map fun c ↦
    if π.getD c 0 = i then tPowC Fc ks m (i * d / n) else (MOr Fc ks (m + 1)).zero

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The shape facts above `0`**. -/
lemma nkShape0_spec (m : ℕ) (h0 : T.Tr m) (Pp : List (GPoly (LC m)))
    (hsh : nkShape0 Fc ks m Pp = true) :
    let F := polyF (fun i ↦ GPoly.toPoly (T.MP m h0) (Pp.getD i [])) Pp.length
    let d := trailG (MO Fc ks m) (Pp.getD 0 [])
    (F.coeff 0).natTrailingDegree = d ∧
      (∀ i, 0 < i → i < Pp.length → F.coeff i = 0 ∨
        d * (Pp.length - i) < Pp.length * (F.coeff i).natTrailingDegree) ∧
      Nat.Coprime Pp.length d := by
  intro F d
  unfold nkShape0 at hsh
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at hsh
  obtain ⟨⟨hz0, hcop⟩, hw⟩ := hsh
  have hnz : ∀ i, GPoly.isZero (MO Fc ks m) (Pp.getD i []) = false →
      GPoly.toPoly (T.MP m h0) (Pp.getD i []) ≠ 0 := fun i hi h ↦ by
    rw [← GPoly.isZero_iff (T.MP m h0)] at h; rw [h] at hi; exact absurd hi (by simp)
  by_cases hn0 : 0 < Pp.length
  · have hc0 : F.coeff 0 = GPoly.toPoly (T.MP m h0) (Pp.getD 0 []) := polyF_coeff _ _ _ hn0
    refine ⟨?_, fun i hi hin ↦ ?_, hcop⟩
    · rw [hc0, ← trailG_eq _ (T.MP m h0) _ (hnz 0 hz0)]
    · rw [polyF_coeff _ _ _ hin]
      rcases hw i hin with (h | h) | h
      · omega
      · left; exact (GPoly.isZero_iff (T.MP m h0) _).mp h
      · by_cases hz : GPoly.isZero (MO Fc ks m) (Pp.getD i []) = true
        · left; exact (GPoly.isZero_iff (T.MP m h0) _).mp hz
        · right
          rw [← trailG_eq _ (T.MP m h0) _ (hnz i (by simpa using hz))]
          exact h
  · refine ⟨?_, fun i hi hin ↦ absurd hin (by omega), hcop⟩
    have hF : F = 1 := by simp [F, polyF, show Pp.length = 0 by omega]
    rw [hF]; simp [d, show Pp = [] from List.eq_nil_of_length_eq_zero (by omega), trailG]

set_option maxHeartbeats 4000000 in
/-- The exponential solver meets its specification at a certified exponential level. -/
theorem expSpecE (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a) :
    T.SolverSpec m ((T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr.of_succ) 0
      ((T.MP m (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr.of_succ).sem
        ((MO Fc ks m).deriv a)) (expSysT Fc ks m a (rdeE Fc ks lv m)) := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  refine T.expTSpec (by omega) hTr.of_succ (hTr m (by omega)) hk (rdeE Fc ks lv m)
    (fun c ↦ T.rde_deriv_of MSm.hyp.tr (prdeC Fc ks lv m) MSm.rde c) (fun z hz j hj ↦ ?_)
  rw [(T.MP m _).sem_deriv, T.sem_MP_F]
  exact MS.hyp.hom m (by omega) a hk j hj z hz

set_option maxHeartbeats 4000000 in
/-- **`⇐`**: an exact `f − τ(f)/n` and an elementary `τ(f)/n` give an elementary `f`. -/
theorem nk_sufficientE (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactG Fc ks m (expSysT Fc ks m a (rdeE Fc ks lv m)) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res)
    (hr : res = true)
    (hq : HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hn0 := (T.nkShape_spec m hTr.of_succ Pp hsh).1
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact T.nkCurve_ind m hTr Pp hsh θ hθ
  have hiff := T.exactG_correct m hTr (hTr m (by omega)) _ _ _
    (T.expSpecE hmon hdeg m hn hc hk) (nkPC Fc ks m Pp) _ θ hP hind res hres
  obtain ⟨Y, hY⟩ := hiff.mp hr
  rw [hlen, T.sum_nkRest m hTr Pp.length hn0] at hY
  rw [show ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
      T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
        (∑ i ∈ Finset.range Pp.length, (Y i : L) * θ ^ i)′ by rw [hY]; ring]
  exact hq.add_in (hasElementaryIntegralIn_deriv _)

set_option maxHeartbeats 16000000 in
/-- **`⇒`**: an elementary `f` has an exact `f − τ(f)/n` and an elementary `τ(f)/n` (the
logarithmic part of a Liouville form lies in `Fₘ`, and `τ` is `n` on `Fₘ`). -/
theorem nk_necessaryE (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactG Fc ks m (expSysT Fc ks m a (rdeE Fc ks lv m)) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res)
    (hf : HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j)) :
    res = true ∧
      HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  classical
  set n := Pp.length with hnn
  set f := ∑ j ∈ Finset.range n, T.evP m (fp.getD j []) * θ ^ j with hfdef
  set q := nkTau Fc ks m n (nkFl Fc ks m fp) s with hq
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨ι, s', c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₁ _ g hg
  -- the tower in `E₁`
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₁
  set ψ := algebraMap L E₁ with hψ
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTE : TE.Tr (m + 1) := MSE.hyp.tr
  have hTEm : TE.Tr m := hTE.of_succ
  have MSEm := TE.mspecs hmon hdeg lv m (by omega) hcm
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    rw [← TE.sem_poly_code m hTE, ← T.sem_poly_code m hTr]
    exact (TE.sem_MP (m + 1) hTE _).trans ((hTEev (m + 1) _).trans
      (congrArg ψ (T.sem_MP (m + 1) hTr _).symm))
  have hθE : (ψ θ) ^ n + ∑ i ∈ Finset.range n, TE.evP m (Pp.getD i []) * (ψ θ) ^ i = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ, map_zero]
  -- the curve over `C₁ = Fₘ` of the lifted tower
  set S₁ := TE.nkCurve m hTE Pp hsh (ψ θ) hθE with hS₁
  have hsp := TE.nkShape_spec m hTEm Pp hsh
  have hS₁F : S₁.F.natDegree = n := polyF_natDegree _ _
  set η₁ : TE.F m := (TE.val m a)′ with hη₁
  have hx : S₁.x′ = aeval S₁.x (Polynomial.C η₁ * X) := by
    rw [map_mul, aeval_C, aeval_X]
    change (TE.ts m)′ = _
    rw [TE.ht m (by omega), hk]
    rfl
  have hnd : ∀ α : AlgebraicClosure (TE.F m), α ≠ 0 →
      α′ ≠ ((Polynomial.C η₁ * X).map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).eval α :=
    fun α hα ↦ by
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_X]
      refine not_exp_of_integral η₁ (fun dd hdd z hz h ↦ ?_) α (Algebra.IsIntegral.isIntegral α) hα
      have := MSE.hyp.hom m (by omega) a hk (-(dd : ℤ)) (by omega) z hz
      apply this
      rw [h, show TE.val m a = TE.val m a from rfl]
      push_cast
      ring
  have hK : ∀ c : TE.F m, (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c)′ =
      algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c′ := fun c ↦ deriv_algebraMap c
  have hconstC : ∀ z : E₁, z′ = 0 → z ∈ Set.range (algebraMap (TE.F m) E₁) := fun z hz ↦ by
    obtain ⟨c0, hc0⟩ := TE.hconst z hz
    exact ⟨⟨z, hc0 ▸ TE.const_mem m c0⟩, rfl⟩
  set T₁ := (TE.F m)⟮S₁.x⟯⟮S₁.y⟯ with hT₁
  have hxT : ∀ w ∈ TE.F (m + 1), w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (TE.mem_F_succ).mp hw⟩ : (TE.F m)⟮S₁.x⟯)
  have hLT : ∀ z : L, ψ z ∈ T₁ := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hxT _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₁, w ∈ T₁ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := hconstC w hw
      rw [← hc0]
      exact S₁.const_mem c0
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  -- the integrand is a polynomial in `x, y`
  have hψf : ψ f = ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j := by
    simp only [hfdef, map_sum, map_mul, map_pow, hPE]
  set Q : (TE.F m)[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (fp.getD j [])) * X ^ j with hQ
  have hQv : S₁.evXY Q = ψ f := by
    rw [hψf, CurveData.evXY, hQ, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul, eval_C,
      eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  have hfT : ψ f ∈ T₁ := hLT f
  have hfQ : (⟨ψ f, hfT⟩ : T₁) = S₁.evT Q := Subtype.ext (by rw [S₁.coe_evT, hQv])
  have hreg : S₁.RegularFinite (AlgebraicClosure (TE.F m)) ⟨ψ f, hfT⟩ := by
    rw [hfQ]; exact S₁.regularFinite_evT Q
  have hresF : ∀ (b : AlgebraicClosure (TE.F m)), b ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries (AlgebraicClosure (TE.F m))))
      (hl : S₁.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries (AlgebraicClosure (TE.F m))) (hr : r ∈ l) (k : ℤ), k < 1 - (N : ℤ) →
      (S₁.embG (branchSub N b) (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r
        (S₁.root_of_mem hl hr) ⟨ψ f, hfT⟩).coeff k = 0 := by
    intro b _ N hN l hl r hr k hk
    apply HahnSeries.coeff_eq_zero_of_lt_order
    have := hreg b N hN l hl r hr
    have : (1 : ℤ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero hN
    omega
  have hsp0 := TE.nkShape0_spec m hTEm Pp hsh0
  -- the logarithmic part lies in `Fₘ`
  have heq₁ : ψ f = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [heqL, add_comm]
  obtain ⟨ℓ₀, hℓ₀⟩ := S₁.nk_liouvilleE (K := AlgebraicClosure (TE.F m)) (Polynomial.C η₁ * X) hx hK
    η₁ rfl hnd n _ _ hS₁F hsp.1 hsp.2.1 hsp.2.2.1 hsp.2.2.2.1 hsp.2.2.2.2 hsp0.1 hsp0.2.1 hsp0.2.2
    hconstC (ψ f) hfT hresF s' c u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩) v
    (hCT v hv) heq₁
  -- the trace
  have hPθE : TE.evθ m hTE (ψ θ) (nkPC Fc ks m Pp) = 0 := by rw [TE.evθ_nkPC]; exact hθE
  obtain ⟨hs0, hτ⟩ := TE.traceC_sound m hTE Pp (ψ θ) hPθE s hs
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  have hdx : ∀ z ∈ (TE.F m)⟮S₁.x⟯, z′ ∈ (TE.F m)⟮S₁.x⟯ := fun z hz ↦ by
    have := ((⟨z, (TE.mem_F_succ).mpr hz⟩ : TE.F (m + 1))′ : TE.F (m + 1)).2
    rw [MTower.coe_deriv] at this
    exact (TE.mem_F_succ).mp this
  obtain ⟨w, hw, hwe⟩ := S₁.trace_split (fun j ↦ ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁))
    (fun j ↦ (TE.mem_F_succ).mp (M1.sem (s.getD j O1.zero)).2)
    (by rw [hS₁F, hs0]; push_cast; rfl)
    (fun i hi ↦ by
      rw [hS₁F] at hi ⊢
      obtain ⟨c', hc'd, hc's⟩ := hτ i hi
      refine ⟨fun j ↦ (c' j : E₁), fun j ↦ (TE.mem_F_succ).mp (c' j).2, hc'd, ?_⟩
      have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) hc's
      simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
        MTower.coe_deriv] at this
      exact this)
    hdx (fun j ↦ TE.evP m (fp.getD j [])) (fun j ↦ (TE.mem_F_succ).mp (TE.evP_mem m (TE.ev_mem m) _))
    v (hCT v hv) (algebraMap (TE.F m) E₁ ℓ₀) (IntermediateField.algebraMap_mem _ ℓ₀)
    (by
      rw [hS₁F]
      change ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j = _
      rw [← hψf]; exact hℓ₀)
  rw [hS₁F] at hwe
  -- `ψ (τ(f)/n)`
  have hqv : ψ (T.ev (m + 1) q) = (∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁)) / n := by
    rw [← hTEev (m + 1) q, ← TE.coe_sem_MPr (m + 1) hTE q, hq, TE.sem_nkTau m n hTE]
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [TE.sem_nkFl m hTE fp j]
  have hlog : algebraMap (TE.F m) E₁ ℓ₀ = ∑ i ∈ s', c i * logDeriv (u i) := by
    have := hℓ₀.symm.trans heq₁
    exact add_left_cancel this
  refine ⟨?_, ?_⟩
  · ----------------------------------------------------------------------------------------------
    -- the exact part in the lifted tower
    have hvw : v - w ∈ T₁ := sub_mem (hCT v hv) (IntermediateField.algebraMap_mem T₁
      (⟨w, hw⟩ : (TE.F m)⟮S₁.x⟯))
    obtain ⟨Y', hY'm, hY'⟩ := S₁.exists_coords (v - w) hvw
    rw [hS₁F] at hY'
    have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
    have hind : ∀ a : ℕ → TE.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
        (a j : E₁) * (ψ θ) ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
      rw [hlen]; exact TE.nkCurve_ind m hTE Pp hsh (ψ θ) hθE
    have hiff := TE.exactG_correct m hTE (hTE m (by omega)) _ _ _
      (TE.expSpecE hmon hdeg m (by rw [hTEn]; exact hn) hc hk) (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind
      res hres
    refine hiff.mpr ⟨fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen, TE.sum_nkRest m hTE n hsp.1, hTEev (m + 1) q]
    change (∑ i ∈ Finset.range n, Y' i * S₁.y ^ i)′ = _
    rw [← hY', ← hψf, hqv, hwe, map_sub, hℓ₀]
    ring
  · ----------------------------------------------------------------------------------------------
    -- `τ(f)/n` has a Liouville form in `E₁`
    set l : List (E₁ × E₁) := s'.toList.map fun i ↦ (c i, u i) with hl0
    have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      rw [Finset.mem_toList] at hi
      exact ⟨(hdata i hi).1, (hdata i hi).2.2⟩
    have hform := hasElementaryIntegral_of_liouville_form w l hl
    have hsumeq : w′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum = ψ (T.ev (m + 1) q) := by
      rw [hqv, hwe, hlog, hl0, List.map_map, Finset.sum_map_toList]
      rfl
    rw [hsumeq] at hform
    exact HasElementaryIntegral.of_extension hE₁ hform

/-- **The logarithmic part over a non-Kummer extension of an exponential level**: for
`θⁿ + ∑ aᵢ(t) θⁱ = 0` with single places above `t = 0` and `t = ∞` and `f = ∑ bⱼ(t) θʲ`, `f` has
an elementary integral iff `f − τ(f)/n` is exact (`exactG` with the exponential solver) and
`τ(f)/n ∈ Fₘ₊₁` has one. -/
theorem nk_iffE (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactG Fc ks m (expSysT Fc ks m a (rdeE Fc ks lv m)) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) :=
  ⟨T.nk_necessaryE hmon hdeg m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp res hres,
    fun h ↦ T.nk_sufficientE hmon hdeg m hn hc hk Pp hsh hsh0 θ hθ s fp res hres h.1 h.2⟩

set_option maxHeartbeats 4000000 in
/-- **The decision**: `elM` decides `τ(f)/n` (at every large search bound), `exactG` the rest. -/
theorem nk_decidesE (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactG Fc ks m (expSysT Fc ks m a (rdeE Fc ks lv m)) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
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
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N hN
  refine ⟨b, hb, ?_⟩
  rw [T.nk_iffE hmon hdeg m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp res hres, h0, hiff]

set_option maxHeartbeats 4000000 in
/-- **`⇐`** (any basis `w = Tc θ`, `exactT`): an exact `f − τ(f)/n` and an elementary `τ(f)/n` give an elementary `f`. -/
theorem nk_sufficientET (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactT Fc ks m (expSysT Fc ks m a (rdeE Fc ks lv m)) (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res)
    (hr : res = true)
    (hq : HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hn0 := (T.nkShape_spec m hTr.of_succ Pp hsh).1
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact T.nkCurve_ind m hTr Pp hsh θ hθ
  have hiff := T.exactT_correct m hTr (hTr m (by omega)) _ _ _
    (T.expSpecE hmon hdeg m hn hc hk) (nkPC Fc ks m Pp) _ θ hP hind Tc Ti res hres
  obtain ⟨Y, hY⟩ := hiff.mp hr
  rw [hlen, T.sum_nkRest m hTr Pp.length hn0] at hY
  rw [show ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
      T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
        (∑ i ∈ Finset.range Pp.length, (Y i : L) * θ ^ i)′ by rw [hY]; ring]
  exact hq.add_in (hasElementaryIntegralIn_deriv _)

set_option maxHeartbeats 16000000 in
/-- **`⇒`**: an elementary `f` has an exact `f − τ(f)/n` and an elementary `τ(f)/n` (the
logarithmic part of a Liouville form lies in `Fₘ`, and `τ` is `n` on `Fₘ`). -/
theorem nk_necessaryET (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactT Fc ks m (expSysT Fc ks m a (rdeE Fc ks lv m)) (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res)
    (hf : HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j)) :
    res = true ∧
      HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  classical
  set n := Pp.length with hnn
  set f := ∑ j ∈ Finset.range n, T.evP m (fp.getD j []) * θ ^ j with hfdef
  set q := nkTau Fc ks m n (nkFl Fc ks m fp) s with hq
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨ι, s', c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₁ _ g hg
  -- the tower in `E₁`
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₁
  set ψ := algebraMap L E₁ with hψ
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTE : TE.Tr (m + 1) := MSE.hyp.tr
  have hTEm : TE.Tr m := hTE.of_succ
  have MSEm := TE.mspecs hmon hdeg lv m (by omega) hcm
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    rw [← TE.sem_poly_code m hTE, ← T.sem_poly_code m hTr]
    exact (TE.sem_MP (m + 1) hTE _).trans ((hTEev (m + 1) _).trans
      (congrArg ψ (T.sem_MP (m + 1) hTr _).symm))
  have hθE : (ψ θ) ^ n + ∑ i ∈ Finset.range n, TE.evP m (Pp.getD i []) * (ψ θ) ^ i = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ, map_zero]
  -- the curve over `C₁ = Fₘ` of the lifted tower
  set S₁ := TE.nkCurve m hTE Pp hsh (ψ θ) hθE with hS₁
  have hsp := TE.nkShape_spec m hTEm Pp hsh
  have hS₁F : S₁.F.natDegree = n := polyF_natDegree _ _
  set η₁ : TE.F m := (TE.val m a)′ with hη₁
  have hx : S₁.x′ = aeval S₁.x (Polynomial.C η₁ * X) := by
    rw [map_mul, aeval_C, aeval_X]
    change (TE.ts m)′ = _
    rw [TE.ht m (by omega), hk]
    rfl
  have hnd : ∀ α : AlgebraicClosure (TE.F m), α ≠ 0 →
      α′ ≠ ((Polynomial.C η₁ * X).map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).eval α :=
    fun α hα ↦ by
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_X]
      refine not_exp_of_integral η₁ (fun dd hdd z hz h ↦ ?_) α (Algebra.IsIntegral.isIntegral α) hα
      have := MSE.hyp.hom m (by omega) a hk (-(dd : ℤ)) (by omega) z hz
      apply this
      rw [h, show TE.val m a = TE.val m a from rfl]
      push_cast
      ring
  have hK : ∀ c : TE.F m, (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c)′ =
      algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c′ := fun c ↦ deriv_algebraMap c
  have hconstC : ∀ z : E₁, z′ = 0 → z ∈ Set.range (algebraMap (TE.F m) E₁) := fun z hz ↦ by
    obtain ⟨c0, hc0⟩ := TE.hconst z hz
    exact ⟨⟨z, hc0 ▸ TE.const_mem m c0⟩, rfl⟩
  set T₁ := (TE.F m)⟮S₁.x⟯⟮S₁.y⟯ with hT₁
  have hxT : ∀ w ∈ TE.F (m + 1), w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (TE.mem_F_succ).mp hw⟩ : (TE.F m)⟮S₁.x⟯)
  have hLT : ∀ z : L, ψ z ∈ T₁ := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hxT _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₁, w ∈ T₁ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := hconstC w hw
      rw [← hc0]
      exact S₁.const_mem c0
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  -- the integrand is a polynomial in `x, y`
  have hψf : ψ f = ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j := by
    simp only [hfdef, map_sum, map_mul, map_pow, hPE]
  set Q : (TE.F m)[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (fp.getD j [])) * X ^ j with hQ
  have hQv : S₁.evXY Q = ψ f := by
    rw [hψf, CurveData.evXY, hQ, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul, eval_C,
      eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  have hfT : ψ f ∈ T₁ := hLT f
  have hfQ : (⟨ψ f, hfT⟩ : T₁) = S₁.evT Q := Subtype.ext (by rw [S₁.coe_evT, hQv])
  have hreg : S₁.RegularFinite (AlgebraicClosure (TE.F m)) ⟨ψ f, hfT⟩ := by
    rw [hfQ]; exact S₁.regularFinite_evT Q
  have hresF : ∀ (b : AlgebraicClosure (TE.F m)), b ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries (AlgebraicClosure (TE.F m))))
      (hl : S₁.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries (AlgebraicClosure (TE.F m))) (hr : r ∈ l) (k : ℤ), k < 1 - (N : ℤ) →
      (S₁.embG (branchSub N b) (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r
        (S₁.root_of_mem hl hr) ⟨ψ f, hfT⟩).coeff k = 0 := by
    intro b _ N hN l hl r hr k hk
    apply HahnSeries.coeff_eq_zero_of_lt_order
    have := hreg b N hN l hl r hr
    have : (1 : ℤ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero hN
    omega
  have hsp0 := TE.nkShape0_spec m hTEm Pp hsh0
  -- the logarithmic part lies in `Fₘ`
  have heq₁ : ψ f = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [heqL, add_comm]
  obtain ⟨ℓ₀, hℓ₀⟩ := S₁.nk_liouvilleE (K := AlgebraicClosure (TE.F m)) (Polynomial.C η₁ * X) hx hK
    η₁ rfl hnd n _ _ hS₁F hsp.1 hsp.2.1 hsp.2.2.1 hsp.2.2.2.1 hsp.2.2.2.2 hsp0.1 hsp0.2.1 hsp0.2.2
    hconstC (ψ f) hfT hresF s' c u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩) v
    (hCT v hv) heq₁
  -- the trace
  have hPθE : TE.evθ m hTE (ψ θ) (nkPC Fc ks m Pp) = 0 := by rw [TE.evθ_nkPC]; exact hθE
  obtain ⟨hs0, hτ⟩ := TE.traceC_sound m hTE Pp (ψ θ) hPθE s hs
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  have hdx : ∀ z ∈ (TE.F m)⟮S₁.x⟯, z′ ∈ (TE.F m)⟮S₁.x⟯ := fun z hz ↦ by
    have := ((⟨z, (TE.mem_F_succ).mpr hz⟩ : TE.F (m + 1))′ : TE.F (m + 1)).2
    rw [MTower.coe_deriv] at this
    exact (TE.mem_F_succ).mp this
  obtain ⟨w, hw, hwe⟩ := S₁.trace_split (fun j ↦ ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁))
    (fun j ↦ (TE.mem_F_succ).mp (M1.sem (s.getD j O1.zero)).2)
    (by rw [hS₁F, hs0]; push_cast; rfl)
    (fun i hi ↦ by
      rw [hS₁F] at hi ⊢
      obtain ⟨c', hc'd, hc's⟩ := hτ i hi
      refine ⟨fun j ↦ (c' j : E₁), fun j ↦ (TE.mem_F_succ).mp (c' j).2, hc'd, ?_⟩
      have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) hc's
      simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
        MTower.coe_deriv] at this
      exact this)
    hdx (fun j ↦ TE.evP m (fp.getD j [])) (fun j ↦ (TE.mem_F_succ).mp (TE.evP_mem m (TE.ev_mem m) _))
    v (hCT v hv) (algebraMap (TE.F m) E₁ ℓ₀) (IntermediateField.algebraMap_mem _ ℓ₀)
    (by
      rw [hS₁F]
      change ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j = _
      rw [← hψf]; exact hℓ₀)
  rw [hS₁F] at hwe
  -- `ψ (τ(f)/n)`
  have hqv : ψ (T.ev (m + 1) q) = (∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁)) / n := by
    rw [← hTEev (m + 1) q, ← TE.coe_sem_MPr (m + 1) hTE q, hq, TE.sem_nkTau m n hTE]
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [TE.sem_nkFl m hTE fp j]
  have hlog : algebraMap (TE.F m) E₁ ℓ₀ = ∑ i ∈ s', c i * logDeriv (u i) := by
    have := hℓ₀.symm.trans heq₁
    exact add_left_cancel this
  refine ⟨?_, ?_⟩
  · ----------------------------------------------------------------------------------------------
    -- the exact part in the lifted tower
    have hvw : v - w ∈ T₁ := sub_mem (hCT v hv) (IntermediateField.algebraMap_mem T₁
      (⟨w, hw⟩ : (TE.F m)⟮S₁.x⟯))
    obtain ⟨Y', hY'm, hY'⟩ := S₁.exists_coords (v - w) hvw
    rw [hS₁F] at hY'
    have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
    have hind : ∀ a : ℕ → TE.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
        (a j : E₁) * (ψ θ) ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
      rw [hlen]; exact TE.nkCurve_ind m hTE Pp hsh (ψ θ) hθE
    have hiff := TE.exactT_correct m hTE (hTE m (by omega)) _ _ _
      (TE.expSpecE hmon hdeg m (by rw [hTEn]; exact hn) hc hk) (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind
      Tc Ti res hres
    refine hiff.mpr ⟨fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen, TE.sum_nkRest m hTE n hsp.1, hTEev (m + 1) q]
    change (∑ i ∈ Finset.range n, Y' i * S₁.y ^ i)′ = _
    rw [← hY', ← hψf, hqv, hwe, map_sub, hℓ₀]
    ring
  · ----------------------------------------------------------------------------------------------
    -- `τ(f)/n` has a Liouville form in `E₁`
    set l : List (E₁ × E₁) := s'.toList.map fun i ↦ (c i, u i) with hl0
    have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      rw [Finset.mem_toList] at hi
      exact ⟨(hdata i hi).1, (hdata i hi).2.2⟩
    have hform := hasElementaryIntegral_of_liouville_form w l hl
    have hsumeq : w′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum = ψ (T.ev (m + 1) q) := by
      rw [hqv, hwe, hlog, hl0, List.map_map, Finset.sum_map_toList]
      rfl
    rw [hsumeq] at hform
    exact HasElementaryIntegral.of_extension hE₁ hform

/-- **The logarithmic part over a non-Kummer extension of an exponential level**: for
`θⁿ + ∑ aᵢ(t) θⁱ = 0` with single places above `t = 0` and `t = ∞` and `f = ∑ bⱼ(t) θʲ`, `f` has
an elementary integral iff `f − τ(f)/n` is exact (`exactG` with the exponential solver) and
`τ(f)/n ∈ Fₘ₊₁` has one. -/
theorem nk_iffET (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactT Fc ks m (expSysT Fc ks m a (rdeE Fc ks lv m)) (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) :=
  ⟨T.nk_necessaryET hmon hdeg m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp Tc Ti res hres,
    fun h ↦ T.nk_sufficientET hmon hdeg m hn hc hk Pp hsh hsh0 θ hθ s fp Tc Ti res hres h.1 h.2⟩

set_option maxHeartbeats 4000000 in
/-- **The decision**: `elM` decides `τ(f)/n` (at every large search bound), `exactG` the rest. -/
theorem nk_decidesET (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactT Fc ks m (expSysT Fc ks m a (rdeE Fc ks lv m)) (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
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
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N hN
  refine ⟨b, hb, ?_⟩
  rw [T.nk_iffET hmon hdeg m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp Tc Ti res hres, h0, hiff]

end MTower

end Curves.MT
