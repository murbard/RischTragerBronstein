import RischTragerBronstein.Mixed.MTWitChain
import RischTragerBronstein.Mixed.MTElemTower
import RischTragerBronstein.Mixed.MTStepE
import RischTragerBronstein.Liouville.RootSumExplicit

/-!
# The antiderivative returned by `elMW` is correct

`MTower.LevelOK m w q c0`: at the level `m + 1` (`t = tₘ`, `t′ = η + e t`), the integrand `q` is

  `q = (gn/gd + pc/t^kk)′ + b/s + c0`

with `s` separable, `deg b < deg s`, `r` the residue polynomial of `b / s` and the residue test
passed — so that `∫ b/s = ∑_{s(α)=0} r(α) log (t − α) − (∑ r(α)) log θ` with constant `r(α)`
(`Differential.rootSum_explicit`). `ValidW m q w` chains these down to the curve, where the
remaining integrand has an elementary integral.

`elMW_valid`: every antiderivative returned by `elMW` is valid.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- `(η, e)` with `tₘ′ = η + e tₘ`. -/
noncomputable def ηeK (m : ℕ) (h : T.Tr m) : KindC m → T.F m × T.F m
  | .prim η => ((T.MP m h).sem η, 0)
  | .exp a => (0, ((T.MP m h).sem a)′)

/-- **One level of the antiderivative is correct.** -/
def LevelOK (m : ℕ) (w : LevelW m) (q : LC (m + 1)) (c0 : LC m) : Prop :=
  ∀ hm : T.Tr m,
    T.ev (m + 1) q = (aeval (T.ts m) (GPoly.toPoly (T.MP m hm) w.gn) /
        aeval (T.ts m) (GPoly.toPoly (T.MP m hm) w.gd) +
        aeval (T.ts m) (GPoly.toPoly (T.MP m hm) w.pc) / T.ts m ^ w.kk)′ +
      aeval (T.ts m) (GPoly.toPoly (T.MP m hm) w.b) /
        aeval (T.ts m) (GPoly.toPoly (T.MP m hm) w.s) + T.ev m c0 ∧
    (T.ts m)′ = algebraMap (T.F m) L (T.ηeK m hm (ks m)).1 +
      algebraMap (T.F m) L (T.ηeK m hm (ks m)).2 * T.ts m ∧
    (GPoly.toPoly (T.MP m hm) w.s).Separable ∧
    aeval (T.ts m) (GPoly.toPoly (T.MP m hm) w.s) ≠ 0 ∧
    (GPoly.toPoly (T.MP m hm) w.b).degree < (GPoly.toPoly (T.MP m hm) w.s).degree ∧
    GPoly.toPoly (T.MP m hm) w.s ∣ GPoly.toPoly (T.MP m hm) w.r *
        (mapCoeffs (GPoly.toPoly (T.MP m hm) w.s) +
          (C (T.ηeK m hm (ks m)).1 + C (T.ηeK m hm (ks m)).2 * X) *
            derivative (GPoly.toPoly (T.MP m hm) w.s)) - GPoly.toPoly (T.MP m hm) w.b ∧
    GPoly.toPoly (T.MP m hm) w.s ∣
      residueTest (GPoly.toPoly (T.MP m hm) w.r) (GPoly.toPoly (T.MP m hm) w.s)

/-- **A valid antiderivative witness** for the level-`m` integrand `q`. -/
def ValidW : (m : ℕ) → LC m → ADW m → Prop
  | 0, q, w => T.ev 0 q = T.ev 0 (w : LC 0) ∧ HasElementaryIntegralIn (T.ev 0 (w : LC 0))
  | m + 1, q, w => ∃ c0 : LC m, T.LevelOK m (w : LevelW m × ADW m).1 q c0 ∧
      ValidW m c0 (w : LevelW m × ADW m).2

lemma certC_le {n : ℕ} (hc : certC Fc ks lv n = true) : ∀ m, m ≤ n → certC Fc ks lv m = true := by
  intro m hm
  induction n with
  | zero => obtain rfl : m = 0 := by omega
            exact hc
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · rw [certX_succ, Bool.and_eq_true] at hc
      exact ih hc.1 (by omega)
    · obtain rfl : m = n + 1 := by omega
      exact hc

/-- `tₘ′ = η + e tₘ`. -/
lemma ts_deriv_ηe (m : ℕ) (hm : T.Tr m) (hmn : m < T.n) :
    (T.ts m)′ = algebraMap (T.F m) L (T.ηeK m hm (ks m)).1 +
      algebraMap (T.F m) L (T.ηeK m hm (ks m)).2 * T.ts m := by
  rw [T.ht m hmn]
  cases hk : ks m with
  | prim η =>
    simp only [ηeK, map_zero, zero_mul, add_zero]
    exact (T.sem_MP m hm η).symm
  | exp a =>
    simp only [ηeK, map_zero, zero_add]
    change (T.ev m a)′ * T.ts m = _
    rw [← T.sem_MP m hm a]
    rfl

/-- **The zero witness is valid** for an integrand of value `0`. -/
lemma validW_zero : ∀ m, m ≤ T.n → T.Tr m → ∀ q : LC m, T.ev m q = 0 →
    T.ValidW m q (zeroW Fc ks m)
  | 0, _, _, q, hq => by
    refine ⟨?_, ?_⟩
    · rw [hq]
      change (0 : L) = T.ev 0 (MO Fc ks 0).zero
      rw [← T.sem_MP 0 (fun i hi ↦ absurd hi (Nat.not_lt_zero _)), CField.sem_zero]
      rfl
    · change HasElementaryIntegralIn (T.ev 0 (MO Fc ks 0).zero)
      rw [← T.sem_MP 0 (fun i hi ↦ absurd hi (Nat.not_lt_zero _)), CField.sem_zero]
      simpa using hasElementaryIntegralIn_deriv (0 : L)
  | m + 1, hmn, htr, q, hq => by
    have hz : ∀ hm : T.Tr m, T.ev m (MO Fc ks m).zero = 0 := fun hm ↦ by
      rw [← T.sem_MP m hm, CField.sem_zero]; rfl
    refine ⟨(MO Fc ks m).zero, fun hm ↦ ?_, validW_zero m (by omega) htr.of_succ _ ?_⟩
    · simp only [zeroW, GPoly.toPoly_nil, GPoly.toPoly_cons, CField.sem_one, map_zero, map_one,
        mul_zero, add_zero, div_one, pow_zero, hz hm, hq]
      refine ⟨trivial, T.ts_deriv_ηe m hm (by omega), separable_one, one_ne_zero, ?_, one_dvd _,
        one_dvd _⟩
      simp
    · exact hz htr.of_succ

/-- **The base case**: the remaining integrand on the curve has an elementary integral. -/
lemma validW_base (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hsh : curveShape Fc = true) (n : ℕ) (hn : T.n = n) (hc : certC Fc ks lv n = true)
    (hE : IsElementaryExtension (T.F 0) L) (q : LC 0) (N : ℕ) (w : ADW 0)
    (h : elMW Fc ks lv 0 q N = some (some w)) : T.ValidW 0 q w := by
  have helM : elM Fc ks lv 0 q N = some true := by rw [← elMW_isSome, h]; rfl
  have hw : (w : LC 0) = q := by
    simp only [elMW] at h
    obtain ⟨b, -, hb⟩ := Option.map_eq_some_iff.mp h
    cases b
    · simp at hb
    · simp only [if_true] at hb
      exact (Option.some.inj hb).symm
  obtain ⟨T0, hT0n, hT0ev, hT0gen, -⟩ := T.exists_sub 0 (Nat.zero_le _)
  have hIn := (elM_sound hmon hdeg hsh T0 0 hT0n (certC_le hc 0 (Nat.zero_le _)) hT0gen q N true
    helM).2 rfl
  have hval : T.ev 0 q = algebraMap (T.F 0) L (T0.ev 0 q) := (hT0ev 0 le_rfl q).symm
  refine ⟨by rw [hw], ?_⟩
  rw [hw, hval]
  exact HasElementaryIntegralIn.of_base hE hIn

set_option maxHeartbeats 4000000 in
/-- **The level step below a logarithm.** -/
lemma levelOK_prim (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hmn : m < T.n) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hkη : ks m = .prim η)
    (qq : LC (m + 1)) (hz : ¬GPoly.isZero (MO Fc ks m) (qq : GFrac (LC m)).2 = true)
    (hh : GPoly.HermiteResult (LC m))
    (hhe : hh = GPoly.hermite (MO Fc ks m) (wKC (MO Fc ks m) (.prim η)) (qq : GFrac (LC m)).1
      (qq : GFrac (LC m)).2)
    (hres : GPoly.residueCheck (MO Fc ks m) (wKC (MO Fc ks m) (.prim η))
      (GPoly.divMod (MO Fc ks m) hh.b hh.s).2 hh.s = true)
    (Q1 : LC m) (P : GPoly (LC m))
    (hch : mchainW Fc ks lv m η (GPoly.divMod (MO Fc ks m) hh.b hh.s).1
      (GPoly.divMod (MO Fc ks m) hh.b hh.s).1.length (MO Fc ks m).zero = some (Q1, P)) :
    T.LevelOK m ⟨hh.gn, hh.gd, P, 0, (GPoly.divMod (MO Fc ks m) hh.b hh.s).2, hh.s,
      GPoly.residuePoly (MO Fc ks m) (wKC (MO Fc ks m) (.prim η))
        (GPoly.divMod (MO Fc ks m) hh.b hh.s).2 hh.s⟩ qq
      (mconst Fc ks m η (GPoly.divMod (MO Fc ks m) hh.b hh.s).1 Q1) := by
  classical
  intro hk
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have MSk := T.mspecs hmon hdeg lv m (by omega) (certC_le hc m (by omega))
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have htr : Transcendental (T.F m) (T.ts m) := hTr m (by omega)
  have hsemM : ∀ a, (((T.MP m hk).sem a : T.F m) : L) = T.ev m a := T.sem_MP m hk
  have haev : ∀ p, aeval (T.ts m) (GPoly.toPoly (T.MP m hk) p) = T.evP m p :=
    T.aeval_toPoly (T.MP m hk) hsemM
  have hvalq : T.ev (m + 1) qq = aeval (T.ts m) (GPoly.toPoly (T.MP m hk) (qq : GFrac (LC m)).1) /
      aeval (T.ts m) (GPoly.toPoly (T.MP m hk) (qq : GFrac (LC m)).2) := by
    rw [haev, haev]; rfl
  set O := MO Fc ks m with hO
  set M := T.MP m hk with hMdef
  set t := T.ts m with htdef
  set ηv := M.sem η with hηv
  set A := (qq : GFrac (LC m)).1 with hAdef
  set D := (qq : GFrac (LC m)).2 with hDdef
  set w : GPoly (LC m) := wKC O (.prim η) with hwdef
  have ht' : t′ = algebraMap (T.F m) L ηv := by
    rw [htdef, T.ht m hmn, hkη]
    exact (hsemM η).symm
  have hD0 : GPoly.toPoly M D ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  have hWp : GPoly.toPoly M w = C ηv := by
    simp [hwdef, wKC, hηv]
  have hw : t′ = aeval t (C ηv) := by rw [aeval_C, ht']
  letI := algebraAdjoinSimple (F := T.F m) t
  letI dP : Differential (T.F m)[X] := polynomialOfDeriv (C ηv)
  letI : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  haveI hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple t htr
  haveI hDAL : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  have hD : ∀ P : (T.F m)[X], P′ = implicitDeriv (GPoly.toPoly M w) P := fun P ↦ by
    rw [hWp]; rfl
  have hφ : ∀ P : (T.F m)[X], (((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P) : (T.F m)⟮t⟯) : L) =
      aeval t P := fun P ↦ algebraMap_adjoinSimple t P
  have hinjt : ∀ P : (T.F m)[X], aeval t P = 0 → P = 0 := fun P h ↦
    transcendental_iff.mp htr P h
  have hnormAll : ∀ p : (T.F m)[X], Irreducible p → ¬p ∣ p′ := fun p hp h ↦
    T.normal_prim m htr hkη p hp (by
      rw [T.wPoly_prim hmn hkη, ← T.sem_MP_F]
      exact h)
  have hnormal : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly M D →
      ¬p ∣ implicitDeriv (GPoly.toPoly M w) p := fun p hp _ h ↦
    hnormAll p hp (by rwa [hD p])
  -- (1) Hermite reduction
  have hchk := GPoly.hermiteCheck_hermite M w A D hnormal hD0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := (T.F m)⟮t⟯) M w A D _ hD hchk
  rw [← hhe] at hid hsq
  set Sd := GPoly.toPoly M hh.s with hSd
  have hS0 : Sd ≠ 0 := hsq.ne_zero
  have hsep : Sd.Separable := PerfectField.separable_iff_squarefree.mpr hsq
  -- (2) polynomial and proper parts
  have hdm := GPoly.divMod_spec M hh.b hh.s
  have hdeglt := GPoly.divMod_degree_lt M hh.b hh.s hS0
  set qc := (GPoly.divMod O hh.b hh.s).1 with hqc
  set rem := (GPoly.divMod O hh.b hh.s).2 with hrem
  -- (3) the residue polynomial
  have hcop0 : IsCoprime Sd′ Sd := isCoprime_deriv_of_squarefree hsq fun p hp _ ↦ hnormAll p hp
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M w) Sd) Sd := by
    rw [← hD Sd]; exact hcop0
  have hr := GPoly.residuePoly_spec M w rem hh.s hS0 hcop
  have hidd : implicitDeriv (GPoly.toPoly M w) Sd = mapCoeffs Sd + C ηv * derivative Sd := by
    rw [hWp, implicitDeriv, Derivation.add_apply, Derivation.smul_apply]
    rfl
  have hst : aeval t Sd ≠ 0 := fun h0 ↦ hS0 (hinjt _ h0)
  have hT : Sd ∣ residueTest (GPoly.toPoly M (GPoly.residuePoly O w rem hh.s)) Sd :=
    (GPoly.residueCheck_iff M w rem hh.s hS0).mp hres
  -- (4) the integrand
  set Pq := GPoly.toPoly M qc with hPq
  set Pr := GPoly.toPoly M rem with hPr
  set g : L := (((algebraMap (T.F m)[X] (T.F m)⟮t⟯ (GPoly.toPoly M hh.gn) /
    algebraMap (T.F m)[X] (T.F m)⟮t⟯ (GPoly.toPoly M hh.gd) : (T.F m)⟮t⟯)) : L) with hg
  have hgv : g = aeval t (GPoly.toPoly M hh.gn) / aeval t (GPoly.toPoly M hh.gd) := by
    rw [hg, IntermediateField.coe_div, hφ, hφ]
  have hform : aeval t (GPoly.toPoly M A) / aeval t (GPoly.toPoly M D) =
      g′ + (aeval t Pq + aeval t Pr / aeval t Sd) := by
    have hid' : aeval t (GPoly.toPoly M A) / aeval t (GPoly.toPoly M D) =
        g′ + aeval t (GPoly.toPoly M hh.b) / aeval t Sd := by
      have := congrArg Subtype.val hid
      rw [IntermediateField.coe_add, IntermediateField.coe_div, IntermediateField.coe_div, hφ, hφ,
        hφ, hφ] at this
      exact this
    rw [hid', hdm, map_add, map_mul, ← hSd]
    field_simp
  -- (5) the chain
  have hcoefF : ∀ j, Pq.coeff j = M.sem (qc.getD j O.zero) := fun j ↦
    Tower.NestP.coeff_toPoly_getD' M qc j
  have hcoef : ∀ j, ((Pq.coeff j : T.F m) : L) = T.ev m (qc.getD j O.zero) := fun j ↦ by
    rw [hcoefF, hsemM]
  obtain ⟨hPlen, hPrec, ⟨q0, hq0⟩, hP1, hP0⟩ :=
    T.mchainW_sound m hk MSk.lim η qc qc.length O.zero Q1 P hch
  set Pv : ℕ → L := fun i ↦ ((M.sem (P.getD i O.zero) : T.F m) : L) with hPv
  have htop : (Pv (qc.length + 1))′ = 0 := by
    simp only [hPv]
    rw [← MTower.coe_deriv, hq0, Derivation.map_add, T.deriv_ratCast, add_zero, M.sem_zero,
      Derivation.map_zero]
    rfl
  have hsum := prim_sum_deriv t (ηv : L) ht' (fun i ↦ T.ev m (qc.getD i O.zero)) Pv qc.length
    (fun i h1 h2 ↦ by
      have := congrArg Subtype.val (hPrec i h1 h2)
      rw [IntermediateField.coe_add, IntermediateField.coe_mul, IntermediateField.coe_mul,
        MTower.coe_deriv, hsemM (qc.getD i O.zero)] at this
      simp only [hPv]
      push_cast at this ⊢
      exact this) htop
  have hA' : aeval t Pq = ∑ i ∈ Finset.range (qc.length + 1), T.ev m (qc.getD i O.zero) * t ^ i := by
    rw [aeval_eq_sum_range' (n := qc.length + 1) (by
      calc Pq.natDegree < qc.length + 1 := by
            have : Pq.natDegree ≤ qc.length := by
              rw [natDegree_le_iff_coeff_eq_zero]
              intro N hN
              rw [hcoefF, List.getD_eq_default _ _ (by exact_mod_cast hN.le), M.sem_zero]
            omega)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, ← hcoef i]
    rfl
  -- the polynomial part `∑ Pᵢ tⁱ`
  have hPpoly : aeval t (GPoly.toPoly M P) =
      ∑ j ∈ Finset.range (qc.length + 1), Pv (j + 1) * t ^ (j + 1) := by
    have hcP : ∀ j, (GPoly.toPoly M P).coeff j = M.sem (P.getD j O.zero) := fun j ↦
      Tower.NestP.coeff_toPoly_getD' M P j
    rw [aeval_eq_sum_range' (n := qc.length + 2) (by
      have : (GPoly.toPoly M P).natDegree ≤ qc.length + 1 := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [hcP, List.getD_eq_default _ _ (by have := hN; omega), M.sem_zero]
      omega), Finset.sum_range_succ']
    have h0 : (GPoly.toPoly M P).coeff 0 = 0 := by rw [hcP]; exact hP0
    rw [h0, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def, hcP]
    rfl
  have hc0 : T.ev m (mconst Fc ks m η qc Q1) =
      T.ev m (qc.getD 0 O.zero) - (ηv : L) * Pv 1 := by
    rw [← hsemM, T.sem_mconst, AddSubgroupClass.coe_sub, IntermediateField.coe_mul,
      hsemM (qc.getD 0 O.zero)]
    have : Pv 1 = ((M.sem Q1 : T.F m) : L) := congrArg Subtype.val hP1
    rw [this]
  refine ⟨?_, T.ts_deriv_ηe m hk hmn, hsep, hst, hdeglt, ?_, ?_⟩
  · rw [hvalq, hform, ← hgv]
    simp only [pow_zero, div_one, Derivation.map_add]
    rw [hPpoly, hsum, hc0, hA']
    ring
  · simp only [ηeK, hkη, map_zero, zero_mul, add_zero]
    rwa [hidd] at hr
  · exact hT

omit [Field Cc] [Algebra Cc L] [Differential Cc] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L] in
lemma deriv_pow_of_exp {t e : L} (ht : t′ = e * t) (n : ℕ) : (t ^ n)′ = (n : L) * e * t ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Derivation.leibniz, ih, ht]
    simp only [smul_eq_mul]
    push_cast
    ring

omit [Field Cc] [Algebra Cc L] [Differential Cc] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L] in
/-- `(y tʲ / tᵏ)′ = (y′ + (j − k) e y) tʲ / tᵏ` when `t′ = e t`. -/
lemma deriv_mono_div {t e : L} (ht0 : t ≠ 0) (ht : t′ = e * t) (y : L) (j k : ℕ) :
    (y * t ^ j / t ^ k)′ = (y′ + ((j : L) - k) * e * y) * t ^ j / t ^ k := by
  have hk : t ^ k ≠ 0 := pow_ne_zero _ ht0
  rw [Derivation.leibniz_div, Derivation.leibniz, deriv_pow_of_exp ht, deriv_pow_of_exp ht]
  simp only [smul_eq_mul]
  field_simp
  ring

omit [Field Cc] [Field L] [Algebra Cc L] [Differential Cc] [Differential L]
  [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] in
lemma mapM_some_spec {α β : Type*} (f : α → Option β) (d : β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys →
      ys.length = l.length ∧ ∀ i (hi : i < l.length), f (l[i]) = some (ys.getD i d)
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i hi ↦ absurd hi (by simp)⟩
  | a :: l, ys, h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some, pure,
          Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hspec⟩ := mapM_some_spec f d l bs hl
        refine ⟨by simp [hlen], fun i hi ↦ ?_⟩
        rcases i with _ | i
        · simpa using hfa
        · simpa using hspec i (by simpa using hi)

set_option maxHeartbeats 8000000 in
/-- **The level step below an exponential.** -/
lemma levelOK_exp (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hmn : m < T.n) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hka : ks m = .exp a)
    (qq : LC (m + 1)) (hz : ¬GPoly.isZero (MO Fc ks m) (qq : GFrac (LC m)).2 = true)
    (sp : GPoly (LC m) × GPoly (LC m) × ℕ × GPoly (LC m))
    (hspe : sp = GPoly.expSplit (MO Fc ks m) (qq : GFrac (LC m)).1 (qq : GFrac (LC m)).2)
    (hh : GPoly.HermiteResult (LC m))
    (hhe : hh = GPoly.hermite (MO Fc ks m) (wKC (MO Fc ks m) (.exp a)) sp.1 sp.2.2.2)
    (hres : GPoly.residueCheck (MO Fc ks m) (wKC (MO Fc ks m) (.exp a))
      (GPoly.divMod (MO Fc ks m) hh.b hh.s).2 hh.s = true)
    (Λc : GPoly (LC m)) (hΛe : Λc = GPoly.add (MO Fc ks m) (GPoly.mul (MO Fc ks m)
      (GPoly.divMod (MO Fc ks m) hh.b hh.s).1 (GPoly.monomial (MO Fc ks m) sp.2.2.1
        (MO Fc ks m).one)) sp.2.1)
    (ys : List (LC m))
    (hys : (List.range (Λc.length + sp.2.2.1 + 1)).mapM (fun j ↦
      if j = sp.2.2.1 then some (MO Fc ks m).zero
      else rdeSolM Fc ks lv m ((MO Fc ks m).mul (mcst Fc ks m ((j : ℚ) - sp.2.2.1)) a)
        (Λc.getD j (MO Fc ks m).zero)) = some ys) :
    T.LevelOK m ⟨hh.gn, hh.gd, ys, sp.2.2.1, (GPoly.divMod (MO Fc ks m) hh.b hh.s).2, hh.s,
      GPoly.residuePoly (MO Fc ks m) (wKC (MO Fc ks m) (.exp a))
        (GPoly.divMod (MO Fc ks m) hh.b hh.s).2 hh.s⟩ qq (Λc.getD sp.2.2.1 (MO Fc ks m).zero) := by
  classical
  intro hk
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have MSk := T.mspecs hmon hdeg lv m (by omega) (certC_le hc m (by omega))
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have htr : Transcendental (T.F m) (T.ts m) := hTr m (by omega)
  have hsemM : ∀ c, (((T.MP m hk).sem c : T.F m) : L) = T.ev m c := T.sem_MP m hk
  have haev : ∀ p, aeval (T.ts m) (GPoly.toPoly (T.MP m hk) p) = T.evP m p :=
    T.aeval_toPoly (T.MP m hk) hsemM
  have hvalq : T.ev (m + 1) qq = aeval (T.ts m) (GPoly.toPoly (T.MP m hk) (qq : GFrac (LC m)).1) /
      aeval (T.ts m) (GPoly.toPoly (T.MP m hk) (qq : GFrac (LC m)).2) := by
    rw [haev, haev]; rfl
  set O := MO Fc ks m with hO
  set M := T.MP m hk with hMdef
  set t := T.ts m with htdef
  set η : T.F m := (M.sem a)′ with hηdef
  set A := (qq : GFrac (LC m)).1 with hAdef
  set D := (qq : GFrac (LC m)).2 with hDdef
  set w : GPoly (LC m) := wKC O (.exp a) with hwdef
  have ht0 : t ≠ 0 := T.hts0 m hmn a hka
  have htraw : t′ = (T.ev m a)′ * t := by
    rw [htdef, T.ht m hmn, hka]
    rfl
  have hηE : algebraMap (T.F m) L η = (T.ev m a)′ := by
    rw [← hsemM a]
    rfl
  have ht' : t′ = algebraMap (T.F m) L η * t := by rw [htraw, hηE]
  have hD0 : GPoly.toPoly M D ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  have hWp : GPoly.toPoly M w = C η * X := by
    simp only [hwdef, wKC, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero]
    rw [M.sem_zero, M.sem_deriv, C_0, zero_add, mul_comm]
  have hWT : C η * X = T.wPoly m := by
    rw [T.wPoly_exp hmn hka, ← T.sem_MP_F]
  have hw : t′ = aeval t (C η * X) := by rw [map_mul, aeval_C, aeval_X, ht']
  letI := algebraAdjoinSimple (F := T.F m) t
  letI dP : Differential (T.F m)[X] := polynomialOfDeriv (C η * X)
  letI : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  haveI hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple t htr
  haveI hDAL : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  have hD : ∀ P : (T.F m)[X], P′ = implicitDeriv (GPoly.toPoly M w) P := fun P ↦ by
    rw [hWp]; rfl
  have hφ : ∀ P : (T.F m)[X], (((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P) : (T.F m)⟮t⟯) : L) =
      aeval t P := fun P ↦ algebraMap_adjoinSimple t P
  have hinjt : ∀ P : (T.F m)[X], aeval t P = 0 → P = 0 := fun P h ↦
    transcendental_iff.mp htr P h
  -- (1) split off the powers of `t`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M A D hD0
  rw [← hspe] at hsp1 hsp2 hsp3
  set kk := sp.2.2.1 with hkk
  have hd₁0 : GPoly.toPoly M sp.2.2.2 ≠ 0 := fun h ↦ hD0 (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly M sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly M w) p := fun p hp hpd ↦ by
    rw [hWp, hWT]
    exact T.normal_exp m htr hka p hp (fun hX ↦ hsp3 (hX.trans hpd))
  -- (2) Hermite reduction
  have hchk := GPoly.hermiteCheck_hermite M w sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := (T.F m)⟮t⟯) M w sp.1 sp.2.2.2 _ hD hchk
  have hsdvd := GPoly.hermite_s_dvd M w sp.1 sp.2.2.2 hd₁0
  rw [← hhe] at hid hsq hsdvd
  set Sd := GPoly.toPoly M hh.s with hSd
  have hS0 : Sd ≠ 0 := hsq.ne_zero
  have hsep : Sd.Separable := PerfectField.separable_iff_squarefree.mpr hsq
  -- (3) polynomial and proper parts
  have hdm := GPoly.divMod_spec M hh.b hh.s
  have hdeglt := GPoly.divMod_degree_lt M hh.b hh.s hS0
  set q := (GPoly.divMod O hh.b hh.s).1 with hq
  set rem := (GPoly.divMod O hh.b hh.s).2 with hrem
  have hΛpoly : GPoly.toPoly M Λc = GPoly.toPoly M q * X ^ kk + GPoly.toPoly M sp.2.1 := by
    rw [hΛe, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M.sem_one, C_1, one_mul]
  -- (4) the residue polynomial
  have hcop0 : IsCoprime Sd′ Sd :=
    isCoprime_deriv_of_squarefree hsq fun p hp hpS ↦ by
      rw [hD p]; exact hnormal p hp (hpS.trans hsdvd)
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M w) Sd) Sd := by
    rw [← hD Sd]; exact hcop0
  have hr := GPoly.residuePoly_spec M w rem hh.s hS0 hcop
  have hidd : implicitDeriv (GPoly.toPoly M w) Sd = mapCoeffs Sd + C η * X * derivative Sd := by
    rw [hWp, implicitDeriv, Derivation.add_apply, Derivation.smul_apply]
    rfl
  have hst : aeval t Sd ≠ 0 := fun h0 ↦ hS0 (hinjt _ h0)
  have hT : Sd ∣ residueTest (GPoly.toPoly M (GPoly.residuePoly O w rem hh.s)) Sd :=
    (GPoly.residueCheck_iff M w rem hh.s hS0).mp hres
  -- (5) the integrand
  set Λ := GPoly.toPoly M Λc with hΛ
  set g : L := (((algebraMap (T.F m)[X] (T.F m)⟮t⟯ (GPoly.toPoly M hh.gn) /
    algebraMap (T.F m)[X] (T.F m)⟮t⟯ (GPoly.toPoly M hh.gd) : (T.F m)⟮t⟯)) : L) with hg
  have hgv : g = aeval t (GPoly.toPoly M hh.gn) / aeval t (GPoly.toPoly M hh.gd) := by
    rw [hg, IntermediateField.coe_div, hφ, hφ]
  have hid' : aeval t (GPoly.toPoly M sp.1) / aeval t (GPoly.toPoly M sp.2.2.2) =
      g′ + aeval t (GPoly.toPoly M hh.b) / aeval t Sd := by
    have := congrArg Subtype.val hid
    rw [IntermediateField.coe_add, IntermediateField.coe_div, IntermediateField.coe_div, hφ, hφ,
      hφ, hφ] at this
    exact this
  have htk : t ^ kk ≠ 0 := pow_ne_zero _ ht0
  have hd₁' : aeval t (GPoly.toPoly M sp.2.2.2) ≠ 0 := fun h0 ↦ hd₁0 (hinjt _ h0)
  have hform : aeval t (GPoly.toPoly M A) / aeval t (GPoly.toPoly M D) =
      g′ + aeval t Λ / t ^ kk + aeval t (GPoly.toPoly M rem) / aeval t Sd := by
    have hA : aeval t (GPoly.toPoly M A) =
        aeval t (GPoly.toPoly M sp.1) * t ^ kk +
          aeval t (GPoly.toPoly M sp.2.1) * aeval t (GPoly.toPoly M sp.2.2.2) := by
      rw [← hsp1]; simp only [map_add, map_mul, map_pow, aeval_X]
    have hDd : aeval t (GPoly.toPoly M D) = t ^ kk * aeval t (GPoly.toPoly M sp.2.2.2) := by
      rw [hsp2]; simp only [map_mul, map_pow, aeval_X]
    have hb : aeval t (GPoly.toPoly M hh.b) =
        aeval t (GPoly.toPoly M q) * aeval t Sd + aeval t (GPoly.toPoly M rem) := by
      rw [hdm, map_add, map_mul]
    have hΛe' : aeval t Λ = aeval t (GPoly.toPoly M q) * t ^ kk +
        aeval t (GPoly.toPoly M sp.2.1) := by
      rw [hΛpoly]; simp only [map_add, map_mul, map_pow, aeval_X]
    calc aeval t (GPoly.toPoly M A) / aeval t (GPoly.toPoly M D)
        = aeval t (GPoly.toPoly M sp.1) / aeval t (GPoly.toPoly M sp.2.2.2) +
          aeval t (GPoly.toPoly M sp.2.1) / t ^ kk := by
          rw [hA, hDd]; field_simp
      _ = g′ + aeval t (GPoly.toPoly M hh.b) / aeval t Sd +
          aeval t (GPoly.toPoly M sp.2.1) / t ^ kk := by rw [hid']
      _ = _ := by rw [hb, hΛe']; field_simp; ring
  -- (6) the Risch equations
  have hcoef : ∀ j, Λ.coeff j = M.sem (Λc.getD j O.zero) := fun j ↦
    Tower.NestP.coeff_toPoly_getD' M Λc j
  set B := Λc.length + kk + 1 with hB
  obtain ⟨hyslen, hyspec⟩ := mapM_some_spec _ O.zero (List.range B) ys hys
  rw [List.length_range] at hyslen
  set yv : ℕ → L := fun j ↦ ((M.sem (ys.getD j O.zero) : T.F m) : L) with hyv
  have hysol : ∀ j, j < B → (yv j)′ + ((j : L) - kk) * (T.ev m a)′ * yv j =
      if j = kk then 0 else T.ev m (Λc.getD j O.zero) := by
    intro j hj
    have := hyspec j (by simpa using hj)
    simp only [List.getElem_range] at this
    by_cases hjk : j = kk
    · rw [if_pos hjk] at this ⊢
      have h0 : ys.getD j O.zero = O.zero := (Option.some.inj this).symm
      have hz0 : M.sem O.zero = 0 := M.sem_zero
      simp only [hyv, h0, hz0, ZeroMemClass.coe_zero, Derivation.map_zero, mul_zero, add_zero]
    · rw [if_neg hjk] at this ⊢
      have hs := T.rdeSolM_sound m hk MSk.rde _ _ _ this
      rw [M.sem_mul, T.sem_mcst, Derivation.leibniz, T.deriv_ratCast] at hs
      simp only [smul_eq_mul, mul_zero, add_zero] at hs
      have := congrArg Subtype.val hs
      rw [IntermediateField.coe_add, IntermediateField.coe_mul, IntermediateField.coe_mul,
        MTower.coe_deriv, MTower.coe_deriv, hsemM, hsemM] at this
      simp only [hyv]
      rw [hsemM (Λc.getD j O.zero)] at this
      rw [← this, hsemM]
      push_cast
      ring
  -- the polynomial part
  have hpoly : (aeval t (GPoly.toPoly M ys) / t ^ kk)′ =
      aeval t Λ / t ^ kk - T.ev m (Λc.getD kk O.zero) := by
    have hcY : ∀ j, (GPoly.toPoly M ys).coeff j = M.sem (ys.getD j O.zero) := fun j ↦
      Tower.NestP.coeff_toPoly_getD' M ys j
    have hYsum : aeval t (GPoly.toPoly M ys) = ∑ j ∈ Finset.range B, yv j * t ^ j := by
      rw [aeval_eq_sum_range' (n := B) (by
        have : (GPoly.toPoly M ys).natDegree ≤ ys.length - 1 := by
          rw [natDegree_le_iff_coeff_eq_zero]
          intro N hN
          have hN' : ys.length ≤ N := by omega
          rw [hcY, List.getD_eq_default _ _ hN', M.sem_zero]
        omega)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Algebra.smul_def, hcY]
      rfl
    have hΛsum : aeval t Λ = ∑ j ∈ Finset.range B, T.ev m (Λc.getD j O.zero) * t ^ j := by
      rw [aeval_eq_sum_range' (n := B) (by
        have : Λ.natDegree ≤ Λc.length := by
          rw [natDegree_le_iff_coeff_eq_zero]
          intro N hN
          rw [hcoef, List.getD_eq_default _ _ (by exact_mod_cast hN.le), M.sem_zero]
        omega)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Algebra.smul_def, hcoef, ← hsemM]
      rfl
    have hkB : kk ∈ Finset.range B := Finset.mem_range.mpr (by omega)
    rw [hYsum, hΛsum, Finset.sum_div, Finset.sum_div, map_sum]
    rw [← Finset.add_sum_erase _ _ hkB, ← Finset.add_sum_erase _ _ hkB]
    have hkt : T.ev m (Λc.getD kk O.zero) * t ^ kk / t ^ kk = T.ev m (Λc.getD kk O.zero) := by
      field_simp
    have hfirst : (yv kk * t ^ kk / t ^ kk)′ = 0 := by
      rw [deriv_mono_div ht0 htraw, hysol kk (by omega), if_pos rfl, zero_mul, zero_div]
    rw [hfirst, hkt, zero_add, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjk : j ≠ kk := Finset.ne_of_mem_erase hj
    have hjB : j < B := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    rw [deriv_mono_div ht0 htraw, hysol j hjB, if_neg hjk]
  refine ⟨?_, T.ts_deriv_ηe m hk hmn, hsep, hst, hdeglt, ?_, hT⟩
  · rw [hvalq, hform, ← hgv, Derivation.map_add, hpoly]
    ring
  · simp only [ηeK, hka, map_zero, C_0, zero_add]
    rw [hidd] at hr
    exact hr

/-- **Every antiderivative returned by `elMW` is valid**, in any `L` elementary over `F₀`. -/
theorem elMW_validE (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hsh : curveShape Fc = true) (n : ℕ) (hn : T.n = n) (hc : certC Fc ks lv n = true)
    (hE : IsElementaryExtension (T.F 0) L) :
    ∀ m, m ≤ n → ∀ (q : LC m) (N : ℕ) (w : ADW m), elMW Fc ks lv m q N = some (some w) →
      T.ValidW m q w
  | 0, _, q, N, w, h => T.validW_base hmon hdeg hsh n hn hc hE q N w h
  | m + 1, hmn, q, N, w, h => by
    have hc1 := certC_le hc (m + 1) hmn
    have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc1).hyp.tr
    have hk : T.Tr m := hTr.of_succ
    have hmT : m < T.n := by omega
    simp only [elMW] at h
    split_ifs at h with hz
    · obtain rfl : zeroW Fc ks (m + 1) = w := Option.some.inj (Option.some.inj h)
      refine T.validW_zero (m + 1) (by omega) hTr q ?_
      have hD0 : GPoly.toPoly (T.MP m hk) (q : GFrac (LC m)).2 = 0 :=
        (GPoly.isZero_iff (T.MP m hk) _).mp hz
      have hsemM : ∀ c, (((T.MP m hk).sem c : T.F m) : L) = T.ev m c := T.sem_MP m hk
      have haev : ∀ p, aeval (T.ts m) (GPoly.toPoly (T.MP m hk) p) = T.evP m p :=
        T.aeval_toPoly (T.MP m hk) hsemM
      have hvalq : T.ev (m + 1) q =
          aeval (T.ts m) (GPoly.toPoly (T.MP m hk) (q : GFrac (LC m)).1) /
          aeval (T.ts m) (GPoly.toPoly (T.MP m hk) (q : GFrac (LC m)).2) := by
        rw [haev, haev]; rfl
      rw [hvalq, hD0, map_zero, div_zero]
    · cases hkm : ks m with
      | prim η =>
        simp only [hkm] at h
        split_ifs at h with hr
        · exact absurd h (by simp)
        split at h
        · exact absurd h (by simp)
        · rename_i Q1 P hch
          obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨w0, rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
          refine ⟨_, T.levelOK_prim hmon hdeg m hmT hc1 hkm q hz _ rfl
            (by simpa using hr) Q1 P hch, elMW_validE hmon hdeg hsh n hn hc hE m (by omega) _ N
            w0 ho⟩
      | exp a =>
        simp only [hkm] at h
        split_ifs at h with hr
        · exact absurd h (by simp)
        split at h
        · exact absurd h (by simp)
        · rename_i ys hys
          obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨w0, rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
          refine ⟨_, T.levelOK_exp hmon hdeg m hmT hc1 hkm q hz _ rfl _ rfl
            (by simpa using hr) _ rfl ys hys, elMW_validE hmon hdeg hsh n hn hc hE m (by omega) _ N
            w0 ho⟩

/-- **Every antiderivative returned by `elMW` is valid.** -/
theorem elMW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hsh : curveShape Fc = true) (n : ℕ) (hn : T.n = n) (hc : certC Fc ks lv n = true)
    (hgen : ∀ z : L, z ∈ T.F n) :
    ∀ m, m ≤ n → ∀ (q : LC m) (N : ℕ) (w : ADW m), elMW Fc ks lv m q N = some (some w) →
      T.ValidW m q w :=
  T.elMW_validE hmon hdeg hsh n hn hc (T.isElementary_F hmon hdeg n hn hc hgen 0 (Nat.zero_le _))

/-- **The logarithmic part of a level, explicitly**: in any differential extension `E` of `L` in
which `s` splits, `b(t)/s(t) = ∑_{s(α)=0} r(α) (t − α)′/(t − α) − (∑ r(α)) e` with constant
`r(α)`; so `∫ b/s = ∑ r(α) log (t − α) − (∑ r(α)) log θ` (`θ′/θ = e`: `θ = 1` below a logarithm,
`θ = t` below an exponential). -/
theorem LevelOK.rootSum {m : ℕ} {w : LevelW m} {q : LC (m + 1)} {c0 : LC m}
    (hw : T.LevelOK m w q c0) (hm : T.Tr m) {E : Type*} [Field E] [Differential E] [Algebra L E]
    [DifferentialAlgebra L E] [DecidableEq E]
    (hsplit : ((GPoly.toPoly (T.MP m hm) w.s).map (algebraMap (T.F m) E)).Splits) :
    (∀ α ∈ ((GPoly.toPoly (T.MP m hm) w.s).map (algebraMap (T.F m) E)).roots.toFinset,
      (aeval α (GPoly.toPoly (T.MP m hm) w.r))′ = 0 ∧ algebraMap L E (T.ts m) - α ≠ 0) ∧
    algebraMap L E (aeval (T.ts m) (GPoly.toPoly (T.MP m hm) w.b) /
        aeval (T.ts m) (GPoly.toPoly (T.MP m hm) w.s)) =
      ∑ α ∈ ((GPoly.toPoly (T.MP m hm) w.s).map (algebraMap (T.F m) E)).roots.toFinset,
        aeval α (GPoly.toPoly (T.MP m hm) w.r) * logDeriv (algebraMap L E (T.ts m) - α) -
      (∑ α ∈ ((GPoly.toPoly (T.MP m hm) w.s).map (algebraMap (T.F m) E)).roots.toFinset,
        aeval α (GPoly.toPoly (T.MP m hm) w.r)) * algebraMap (T.F m) E (T.ηeK m hm (ks m)).2 := by
  obtain ⟨-, ht, hsep, hst, hdeg, hr, hT⟩ := hw hm
  exact rootSum_explicit (L := E) (T.ts m) _ _ ht _ _ _ hsep hst hdeg hr hT hsplit

end MTower

end Curves.MT
