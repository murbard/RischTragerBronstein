import RischTragerBronstein.Mixed.NKInfRNExp
import RischTragerBronstein.Mixed.NKInfRNExample
import RischTragerBronstein.Mixed.NKInfRExpExample

/-!
# Example: three places at infinity, two of them conjugate, over `eˣ`

The cubic `θ³ − t θ² − t = 0` of `NKInfRNEx` over `t = eˣ` (a single place above `t = 0`). With the
units `1 ∓ iθ` over `ℚ(i)`, `nk_iffETRN` reduces `∫ θ dx` to the exactness of
`θ − τ(θ)/3 − ∑ cᵢₖ gᵢₖ` and `∫ τ(θ)/3 = ∫ eˣ/3`; `exactTL` (exponential solver, basis normal at
infinity) answers `some true` (`#guard`; the hypothesis `hres`): **`∫ θ dx` is elementary**
(with `θ = 1/s`, `eˣ = 1/(s³ + s)`: `θ dx = −(3s² + 1)/(s²(s² + 1)) ds = d(1/s − 2 arctan s)`,
the arctangent being a logarithm of the unit `(1 − iθ)/(1 + iθ)`). Over `t = log x` the same
integrand is not elementary (`NKInfRNEx.not_elementary`).
-/

namespace Curves.MT.NKInfRNEEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEE Polynomial Differential GTors

abbrev Fq : BPoly ℚ := NKInfRNEx.Fq

def Pp : List (GPoly (LC 0)) := liftCurve Fc ks 0 3 Fq
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def tC1 : LC 1 := (([[], one0] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
def tC2 : LC 1 := (([[], [], one0] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
/-- Power sums `s₀ = 3`, `s₁ = t`, `s₂ = t²`. -/
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 3, tC1, tC2]
abbrev μ : List ℤ := NKInf2NEx.μ
abbrev Ass := NKInfRNEx.Ass
abbrev Bss := NKInfRNEx.Bss
def den2 : GPoly (LC 0) := [[([27 / 4], [1])], [], [([1], [1])]]
def g10 : GPoly (LC 1) :=
  [([[], [], [([-1 / 2], [1])]], den2), ([[], [([-3 / 4], [1])]], den2), ([[([9 / 4], [1])]], den2)]
def g11 : GPoly (LC 1) :=
  [([[], [([3 / 4], [1])]], den2), ([[([-9 / 4], [1])], [], [([-1 / 2], [1])]], den2),
   ([[], [([1 / 2], [1])]], den2)]
def g21 : GPoly (LC 1) :=
  [([[], [([-3 / 4], [1])]], den2), ([[([9 / 4], [1])], [], [([1 / 2], [1])]], den2),
   ([[], [([-1 / 2], [1])]], den2)]
/-- `uᵢ′/uᵢ = gᵢ₀ + α gᵢ₁` (now `t′ = t`). -/
def gss : List (List (GPoly (LC 1))) := [[g10, g11], [g10, g21]]
/-- `θ′` and `1/P_θ`. -/
def dθW : GPoly (LC 1) :=
  [([[], [([3 / 2], [1])]], den2), ([[([9 / 4], [1])]], den2), ([[], [([1], [1])]], den2)]
abbrev wθW := NKInfRNEx.wθW
def Hm : List (List (List (LC 1))) :=
  [[[([[], [([1 / 3], [1])]], [[([1], [1])]]), ([[([3 / 2], [1])]], [[([1], [1])]])],
    [([[], [([1 / 3], [1])]], [[([1], [1])]]), ([[([-3 / 2], [1])]], [[([1], [1])]])]],
   [[([[([3 / 2], [1])], [], [([1 / 3], [1])]], [[([1], [1])]]), ([[], [([1 / 2], [1])]], [[([1], [1])]])],
    [([[([3 / 2], [1])], [], [([1 / 3], [1])]], [[([1], [1])]]),
      ([[], [([-1 / 2], [1])]], [[([1], [1])]])]]]
/-- `f = θ`. -/
def fp : List (GPoly (LC 0)) := [[], [one0]]
def q : LC 1 := nkTau Fc ks 0 3 (nkFl Fc ks 0 fp) sC
def rest : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fp) q

-- `θ − τ(θ)/3 − ∑ cᵢₖ gᵢₖ` is exact for some constants
#guard exactTL Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp)
  (nkTi Fc ks 0 Pp) rest gss.flatten = some true

set_option maxRecDepth 200000 in
lemma hcertC : certC Fc ks lv 1 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hsh0 : nkShape0 Fc ks 0 Pp = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hs : traceW Fc ks 0 Pp dθW wθW sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hU : unitsRNC Fc ks 0 Pp μ Ass Bss gss dθW wθW sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hJH : indepCN Fc ks 0 μ gss [1, 2] Hm = true := by decide +kernel

set_option maxRecDepth 200000 in
/-- `τ(θ)/3 = t/3` is its own derivative. -/
lemma hqd : (MOr Fc ks 1).isZero ((MOr Fc ks 1).add q ((MOr Fc ks 1).neg ((MOr Fc ks 1).deriv q))) =
    true := by decide +kernel

lemma hmonF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

lemma hlen : Pp.length = 3 := by simp [Pp, liftCurve]

lemma ha0Q : (toB Fq).coeff 0 ≠ 0 := by
  rw [NKInfRNEx.Fq_eq]
  simp

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]

/-- **`∫ θ dx` is elementary** for `θ³ − θ² eˣ − eˣ = 0`, given the `exactTL` answer (`#guard`
above). -/
theorem elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 3 + ∑ i ∈ Finset.range 3, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (hres : exactTL Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp)
      (nkTi Fc ks 0 Pp) rest gss.flatten = some true) :
    HasElementaryIntegral (∑ j ∈ Finset.range 3, T.evP 0 (fp.getD j []) * θ ^ j) := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Cc) (n := 2) (by norm_num)
  have hi0 : i ≠ 0 := fun h ↦ by rw [h] at hi; norm_num at hi
  set αs : Fin μ.length → Cc := ![i, -i] with hαs
  have hne : i ≠ -i := fun h ↦ hi0 (by linear_combination h / 2)
  have hinj : Function.Injective αs := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd hab hne | exact absurd hab hne.symm
  have hαμ : ∀ k, αs k ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * αs k ^ l = 0 := by
    intro k
    fin_cases k <;> simp [hαs, μ, NKInf2NEx.μ, Finset.sum_range_succ, hi]
  have hTr : T.Tr 1 := (T.mspecs hmonF.1 hmonF.2 lv 1 (by omega) hcertC).hyp.tr
  have hiff := T.nk_iffETRN hmonF.1 hmonF.2 0 hn hcertC rfl Pp Fq (by rw [hlen]; rfl)
    NKInfRNEx.Fq_mon (by rw [NKInfRNEx.Fq_deg, hlen]) (by rw [hlen]; norm_num) NKInfRNEx.hgeo hsh0
    ha0Q θ (IsAlgClosed.lift (R := ℚ) (S := NKInfRNEx.KK) (M := Cc)).toRingHom 1 3 NKInfRNEx.hinv
    NKInfRNEx.Fq'_mon (by show (toB NKInfRNEx.Fq').natDegree = _; rw [NKInfRNEx.Fq'_deg, hlen])
    μ Ass Bss gss NKInfRNEx.hpd dθW wθW sC hU [1, 2] Hm hJH (by rw [hlen]; exact hθ) hgen αs hinj
    hαμ hs fp (nkTc Fc ks 0 Pp) (nkTi Fc ks 0 Pp) true (by rw [hlen]; exact hres)
  rw [hlen] at hiff
  refine hiff.mpr ⟨rfl, ?_⟩
  have h0 : T.ev 1 q = (T.ev 1 q)′ := by
    have := ((T.MPr 1 hTr).isZero_iff _).mp hqd
    rw [(T.MPr 1 hTr).sem_add, (T.MPr 1 hTr).sem_neg, (T.MPr 1 hTr).sem_deriv,
      add_neg_eq_zero] at this
    calc T.ev 1 q = ((T.MPr 1 hTr).sem q : L) := (T.coe_sem_MPr 1 hTr q).symm
      _ = (((T.MPr 1 hTr).sem q)′ : T.F 1) := congrArg Subtype.val this
      _ = (T.ev 1 q)′ := by rw [MTower.coe_deriv, T.coe_sem_MPr]
  change HasElementaryIntegral (T.ev 1 q)
  rw [h0]
  exact hasElementaryIntegral_of_deriv _

end Curves.MT.NKInfRNEEx
