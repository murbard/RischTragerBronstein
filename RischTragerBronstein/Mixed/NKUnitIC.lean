import RischTragerBronstein.Mixed.NKHornerInt
import RischTragerBronstein.Mixed.NKInf2UnitDecide

/-!
# Integrality certificates for units outside the order `Fₘ[t][θ]`

`unitIC Pp U d cs` checks `d^k q(U/d) ≡ 0 mod P` for the monic `q = Z^k + c_{k-1} Z^{k-1} + ⋯ + c₀`
(`cs = [c_{k-1}, …, c₀]`, coefficients in `Fₘ[t]`), computed division-free in Horner form
(`hornerC`). By `unitIC_sound`, `U/d` is then a root of `q`, so it is integral over `Fₘ[t]`.
This is the first step towards unit certificates `U/d` for units of the integral closure that
have no power in `Fₘ[t][θ]`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

namespace CurveData

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]
variable (S : CurveData C L)

/-- **A root of a monic polynomial with coefficients in `C[x][y]` is regular at every finite
branch** (it is integral over `C[x]`). -/
lemma regularFinite_of_horner [IsAlgClosed K] [CharZero K] (f : C⟮S.x⟯⟮S.y⟯) (Qs : List C[X][X])
    (h : hornerZ f (Qs.map S.evT) 1 = 0) : S.RegularFinite K f := by
  intro a N hN l hl r hr
  set φ := S.embG (branchSub (K := K) N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
    (S.root_of_mem hl hr)
  have h' := congrArg φ h
  rw [hornerZ_map, map_one, map_zero, List.map_map] at h'
  refine order_nonneg_of_lowerBd_nk _ (lowerBd_of_horner _ _ (fun c hc ↦ ?_) h')
  obtain ⟨Q, -, rfl⟩ := List.mem_map.mp hc
  exact lowerBd_zero_of_order (S.regularFinite_evT (K := K) Q a N hN l hl r hr)

end CurveData

end Curves

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

universe u

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- Division-free Horner evaluation with codes (the code version of `hornerD`). -/
def hornerC (m : ℕ) (U D : GPoly (LC (m + 1))) :
    List (GPoly (LC (m + 1))) → GPoly (LC (m + 1)) → GPoly (LC (m + 1)) → GPoly (LC (m + 1))
  | [], acc, _ => acc
  | c :: cs, acc, Dp => hornerC m U D cs
      (GPoly.add (MO Fc ks (m + 1)) (GPoly.mul (MO Fc ks (m + 1)) acc U)
        (GPoly.mul (MO Fc ks (m + 1)) c (GPoly.mul (MO Fc ks (m + 1)) Dp D)))
      (GPoly.mul (MO Fc ks (m + 1)) Dp D)

/-- **The integrality check**: `d^k q(U/d) ≡ 0 mod P`, `q` monic with coefficients `cs` in `Fₘ[t]`. -/
def unitIC (m : ℕ) (Pp : List (GPoly (LC m))) (U : List (GPoly (LC m))) (d : GPoly (LC m))
    (cs : List (GPoly (LC m))) : Bool :=
  zeroModC Fc ks m Pp (hornerC Fc ks m (nkFl Fc ks m U) (nkFl Fc ks m [d])
    (cs.map fun c ↦ nkFl Fc ks m [c]) [(MO Fc ks (m + 1)).one] [(MO Fc ks (m + 1)).one])

/-- **Unit with denominator**: `U·V ≡ d² mod P`, i.e. `(U/d)(V/d) = 1`. -/
def unitCD (m : ℕ) (Pp : List (GPoly (LC m))) (U V : List (GPoly (LC m))) (d : GPoly (LC m)) : Bool :=
  let O1 := MO Fc ks (m + 1)
  let D := nkFl Fc ks m [d]
  zeroModC Fc ks m Pp (GPoly.sub O1 (GPoly.mul O1 (nkFl Fc ks m U) (nkFl Fc ks m V)) (GPoly.mul O1 D D))

/-- **Logarithmic derivative of `U/d`**: `θ′ = dθ` as in `logDerChk`, and
`g·d² ≡ U′V − d′d mod P` (derivatives through `dθ`). -/
def logDerChkD (m : ℕ) (Pp : List (GPoly (LC m))) (U V : List (GPoly (LC m))) (d : GPoly (LC m))
    (gl dθ wθ : GPoly (LC (m + 1))) : Bool :=
  let O1 := MO Fc ks (m + 1)
  let P := nkPC Fc ks m Pp
  let u := nkFl Fc ks m U
  let D := nkFl Fc ks m [d]
  zeroModC Fc ks m Pp (GPoly.add O1 (GPoly.mul O1 dθ (GPoly.derivX O1 P)) (GPoly.mapD O1 P)) &&
  zeroModC Fc ks m Pp (GPoly.sub O1 (GPoly.mul O1 wθ (GPoly.derivX O1 P)) [O1.one]) &&
  zeroModC Fc ks m Pp (GPoly.sub O1 (GPoly.mul O1 gl (GPoly.mul O1 D D))
    (GPoly.sub O1 (GPoly.mul O1 (GPoly.add O1 (GPoly.mapD O1 u) (GPoly.mul O1 dθ (GPoly.derivX O1 u)))
      (nkFl Fc ks m V))
      (GPoly.mul O1 (GPoly.add O1 (GPoly.mapD O1 D) (GPoly.mul O1 dθ (GPoly.derivX O1 D))) D)))

end Codes

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma evθ_addC (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (A B : GPoly (LC (m + 1))) :
    T.evθ m h1 θ (GPoly.add (MO Fc ks (m + 1)) A B) = T.evθ m h1 θ A + T.evθ m h1 θ B := by
  rw [evθ_MP, GPoly.toPoly_add, map_add, ← evθ_MP, ← evθ_MP]

lemma evθ_mulC (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (A B : GPoly (LC (m + 1))) :
    T.evθ m h1 θ (GPoly.mul (MO Fc ks (m + 1)) A B) = T.evθ m h1 θ A * T.evθ m h1 θ B := by
  rw [evθ_MP, GPoly.toPoly_mul, map_mul, ← evθ_MP, ← evθ_MP]

lemma evθ_hornerC (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (U D : GPoly (LC (m + 1))) :
    ∀ (cs : List (GPoly (LC (m + 1)))) (acc Dp : GPoly (LC (m + 1))),
      T.evθ m h1 θ (hornerC Fc ks m U D cs acc Dp) =
        hornerD (T.evθ m h1 θ U) (T.evθ m h1 θ D) (cs.map (T.evθ m h1 θ))
          (T.evθ m h1 θ acc) (T.evθ m h1 θ Dp)
  | [], acc, Dp => rfl
  | c :: cs, acc, Dp => by
    simp only [hornerC, evθ_hornerC m h1 θ U D cs, List.map_cons, hornerD, T.evθ_addC,
      T.evθ_mulC]

lemma evθ_nkFl_single (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (c : GPoly (LC m)) :
    T.evθ m h1 θ (nkFl Fc ks m [c]) = T.evP m c := by
  rw [T.evθ_nkFl m h1 θ]
  simp

/-- **Soundness of `unitIC`**: `u/δ` is a root of the monic `q` with coefficients `evP cs`. -/
lemma unitIC_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp U : List (GPoly (LC m)))
    (d : GPoly (LC m)) (cs : List (GPoly (LC m))) (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (hd : T.evP m d ≠ 0) (h : unitIC Fc ks m Pp U d cs = true) :
    hornerZ (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d) (cs.map (T.evP m)) 1 = 0 := by
  have h0 := T.zeroModC_sound m h1 θ Pp _ hP h
  rw [T.evθ_hornerC, T.evθ_one_MO, T.evθ_nkFl_single, List.map_map,
    hornerD_eq _ _ hd _ _ _ one_ne_zero, one_mul, div_one] at h0
  have hcs : (cs.map ((T.evθ m h1 θ) ∘ fun c ↦ nkFl Fc ks m [c])) = cs.map (T.evP m) :=
    List.map_congr_left fun c _ ↦ T.evθ_nkFl_single m h1 θ c
  rw [hcs, List.length_map] at h0
  exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ hd)

lemma evθ_subC (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (A B : GPoly (LC (m + 1))) :
    T.evθ m h1 θ (GPoly.sub (MO Fc ks (m + 1)) A B) = T.evθ m h1 θ A - T.evθ m h1 θ B := by
  rw [evθ_MP, GPoly.toPoly_sub, map_sub, ← evθ_MP, ← evθ_MP]

lemma unitCD_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp U V : List (GPoly (LC m)))
    (d : GPoly (LC m)) (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (h : unitCD Fc ks m Pp U V d = true) :
    T.evθ m h1 θ (nkFl Fc ks m U) * T.evθ m h1 θ (nkFl Fc ks m V) = T.evP m d * T.evP m d := by
  have h0 := T.zeroModC_sound m h1 θ Pp _ hP h
  rw [T.evθ_subC, T.evθ_mulC, T.evθ_mulC, T.evθ_nkFl_single, sub_eq_zero] at h0
  exact h0

/-- **Soundness of `logDerChkD`**: `g = (u/δ)′/(u/δ)`. -/
lemma logDerChkD_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp U V : List (GPoly (LC m)))
    (d : GPoly (LC m)) (gl dθ wθ : GPoly (LC (m + 1))) (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (hδ : T.evP m d ≠ 0)
    (huv : T.evθ m h1 θ (nkFl Fc ks m U) * T.evθ m h1 θ (nkFl Fc ks m V) = T.evP m d * T.evP m d)
    (h : logDerChkD Fc ks m Pp U V d gl dθ wθ = true) :
    T.evθ m h1 θ gl = (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d)′ /
      (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d) := by
  set O1 := MO Fc ks (m + 1)
  unfold logDerChkD at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hd, hw⟩, hg⟩ := h
  have hd' := T.zeroModC_sound m h1 θ Pp _ hP hd
  have hw' := T.zeroModC_sound m h1 θ Pp _ hP hw
  have hg' := T.zeroModC_sound m h1 θ Pp _ hP hg
  rw [T.evθ_addC, T.evθ_mulC] at hd'
  rw [T.evθ_subC, T.evθ_mulC, T.evθ_one_MO m h1 θ, sub_eq_zero] at hw'
  simp only [T.evθ_subC, T.evθ_mulC, T.evθ_addC, T.evθ_nkFl_single, sub_eq_zero] at hg'
  have hPd := T.deriv_evθ_MO m h1 θ (nkPC Fc ks m Pp)
  rw [hP, Derivation.map_zero] at hPd
  have hθ' : θ′ = T.evθ m h1 θ dθ := by
    have hne : T.evθ m h1 θ (GPoly.derivX O1 (nkPC Fc ks m Pp)) ≠ 0 :=
      right_ne_zero_of_mul_eq_one hw'
    have : T.evθ m h1 θ (GPoly.derivX O1 (nkPC Fc ks m Pp)) * (θ′ - T.evθ m h1 θ dθ) = 0 := by
      linear_combination -hPd - hd'
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
  have hu' := T.deriv_evθ_MO m h1 θ (nkFl Fc ks m U)
  have hD' := T.deriv_evθ_MO m h1 θ (nkFl Fc ks m [d])
  rw [T.evθ_nkFl_single] at hD'
  rw [← hθ'] at hg'
  have hg2 : T.evθ m h1 θ gl * (T.evP m d * T.evP m d) =
      (T.evθ m h1 θ (nkFl Fc ks m U))′ * T.evθ m h1 θ (nkFl Fc ks m V) -
        (T.evP m d)′ * T.evP m d := by
    rw [hu', hD']; linear_combination hg'
  set u := T.evθ m h1 θ (nkFl Fc ks m U)
  set v := T.evθ m h1 θ (nkFl Fc ks m V)
  set δ := T.evP m d
  have hu0 : u ≠ 0 := fun h0 ↦ mul_ne_zero hδ hδ (by rw [← huv, h0, zero_mul])
  have hv : v = δ * δ / u := by field_simp; linear_combination huv
  rw [hv] at hg2
  have hgl : T.evθ m h1 θ gl = u′ / u - δ′ / δ := by
    field_simp
    field_simp at hg2
    linear_combination hg2
  rw [hgl, Derivation.leibniz_div]
  simp only [smul_eq_mul]
  field_simp

end MTower

end Curves.MT


