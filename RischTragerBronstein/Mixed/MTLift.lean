import RischTragerBronstein.Mixed.MTElem

/-!
# Mixed towers over a curve: the induction hypothesis and the lift property

* `ELHypM k`: the decision statement at height `k`, for every realization of height `k` whose
  certificate holds;
* `elM_zero`: the base (the total decision on the curve);
* `MTower.constDec`: the induction hypothesis applied to the sub-tower of height `k` inside
  `F k` decides the level-`k` codes as integrands in `L` (given `L` elementary over `F k`);
* `MTower.expLift`: **the lift property** of an exponential level (`ExpLift`): in every
  elementary extension `E` of `L`, the realization over the constants of `E` gives a field
  `F₁ ⊇ F k` over which `t` stays transcendental (the certificate), and a solution in `F₁` of a
  Risch equation with code data descends to `F k` (completeness of `prdeC` in the lifted
  realization, soundness in `L` — the same code list).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The decision statement at height `k`, for every certified realization of height `k`. -/
def ELHypM (k : ℕ) : Prop :=
  ∀ (Cc L : Type u) [Field Cc] [Field L] [Algebra Cc L] [Differential Cc] [Differential L]
    [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]
    (T : MTower Fc ks Cc L), T.n = k → certC Fc ks lv k = true → (∀ z : L, z ∈ T.F k) →
      ∀ q : LC k, ∃ N₀, ∀ N, N₀ ≤ N → ∃ b, elM Fc ks lv k q N = some b ∧
        (HasElementaryIntegral (T.ev k q) ↔ b = true) ∧
        (b = true → HasElementaryIntegralIn (T.ev k q))

variable {Fc ks lv}

/-- **The base of the induction.** -/
theorem elM_zero (hsh : curveShape Fc = true) : ELHypM.{u} Fc ks lv 0 := by
  intro Cc L _ _ _ _ _ _ _ _ _ T _ _ hgen q
  exact el0_decides Fc T.hC T.S T.hx (fun z ↦ hgen z) T.hSF hsh q

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The constant term, one level down.** -/
theorem constDec [IsAlgClosed Cc] (k : ℕ) (IH : ELHypM.{u} Fc ks lv k) (hkn : k ≤ T.n)
    (hc : certC Fc ks lv k = true) (hE : IsElementaryExtension (T.F k) L) (c0 : LC k) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b, elM Fc ks lv k c0 N = some b ∧
      (HasElementaryIntegral (T.ev k c0) ↔ b = true) ∧
      (b = true → HasElementaryIntegralIn (T.ev k c0)) := by
  obtain ⟨Tk, hTkn, hTkev, hTkgen, -⟩ := T.exists_sub k hkn
  obtain ⟨N₀, hN₀⟩ := IH Cc (T.F k) Tk hTkn hc hTkgen c0
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, hIn⟩ := hN₀ N hN
  have hvalL : T.ev k c0 = algebraMap (T.F k) L (Tk.ev k c0) := (hTkev k le_rfl c0).symm
  refine ⟨b, hb, ⟨fun hf ↦ hiff.mp (HasElementaryIntegral.of_extension hE (by rwa [hvalL] at hf)),
    fun hb1 ↦ by rw [hvalL]; exact hIn hb1 L hE⟩, fun hb1 ↦ by
      rw [hvalL]; exact HasElementaryIntegralIn.of_base hE (hIn hb1)⟩

/-- The Risch equation `y′ + (m aₖ)′ y = f` through `prdeC` with the potential `m a`. -/
lemma sem_mulCst (k : ℕ) (h : T.Tr k) (q : ℚ) (a : LC k) :
    ((T.MP k h).sem ((MO Fc ks k).mul (mcst Fc ks k q) a))′ =
      (q : T.F k) * ((T.MP k h).sem a)′ := by
  rw [CField.sem_mul, T.sem_mcst, Derivation.leibniz, T.deriv_ratCast]
  simp

/-- **The lift property of an exponential level.** -/
theorem expLift (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (k : ℕ)
    (hkn : k < T.n) (hc : certC Fc ks lv (k + 1) = true) {a : LC k} (hk : ks k = .exp a)
    (hTr : T.Tr k) :
    ExpLift (K := L) (T.F k) (T.ts k) ((T.MP k hTr).sem a)′
      (fun f ↦ ∃ c : LC k, f = (T.MP k hTr).sem c) := by
  classical
  intro E _ _ _ _ hE
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap L E).injective
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E
  set ψ := algebraMap L E with hψ
  have hcK : certC Fc ks lv k = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSE := TE.mspecs hmon hdeg lv (k + 1) (by omega) hc
  have MSEk := TE.mspecs hmon hdeg lv k (by omega) hcK
  have MSk := T.mspecs hmon hdeg lv k (by omega) hcK
  have hTEk : TE.Tr k := MSEk.hyp.tr
  have hsemE : ∀ q, (((TE.MP k hTEk).sem q : TE.F k) : E) = ψ (((T.MP k hTr).sem q : T.F k) : L) :=
    fun q ↦ by rw [TE.sem_MP, hTEev, T.sem_MP]
  refine ⟨TE.F k, TE.derivClosed k, fun f ↦ hTEmem k _ f.2, ?_, ?_⟩
  · have := MSE.hyp.tr k (by omega)
    rwa [hTEts] at this
  · rintro m hm f ⟨c, rfl⟩ ⟨y, hyF, hy⟩
    set hcode := (MO Fc ks k).mul (mcst Fc ks k (m : ℚ)) a with hhcode
    -- the solution in the lifted realization
    have hyE : (⟨y, hyF⟩ : TE.F k)′ + ((TE.MP k hTEk).sem hcode)′ * ⟨y, hyF⟩ =
        (TE.MP k hTEk).sem c := by
      apply Subtype.ext
      rw [TE.sem_mulCst k hTEk, IntermediateField.coe_add, IntermediateField.coe_mul,
        IntermediateField.coe_mul, MTower.coe_deriv, MTower.coe_deriv, hsemE, hsemE]
      simp only [SubfieldClass.coe_ratCast, Rat.cast_intCast]
      have e1 : (ψ (((T.MP k hTr).sem a : T.F k) : L))′ =
          ψ (algebraMap (T.F k) L ((T.MP k hTr).sem a)′) := by
        rw [deriv_algebraMap]; rfl
      rw [e1]
      exact hy
    have hokE := (TE.rdeOKM_iff (lv := lv) k hTEk MSEk.rde hcode c).mp ⟨_, hyE⟩
    obtain ⟨y0, hy0⟩ := (T.rdeOKM_iff (lv := lv) k hTr MSk.rde hcode c).mpr hokE
    refine ⟨y0, ?_⟩
    rw [T.sem_mulCst k hTr] at hy0
    rw [← hy0]
    push_cast
    ring

end MTower

end Curves.MT
