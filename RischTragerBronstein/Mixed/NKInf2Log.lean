import RischTragerBronstein.Mixed.NKInf2
import RischTragerBronstein.Mixed.NKLogDecide

/-!
# The logarithmic part over a curve with two places at infinity

`TwoPlaceCert S' ι`: a certificate (over a field `F ⊆ C`) that on `S′ = mobCurve S 0 k M`
(`x′ = 1/x`), the two places above `x′ = 0` (the places of `S` at infinity) differ by a
non-torsion divisor class. Then units of `S` at the finite places are constants
(`mem_const_two`), so the logarithms of a Liouville form lie in the base (`logs_in_base_two`) and
the logarithmic part is a constant (`nk_liouville_two`), as for a single place at infinity.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves

open Differential GTors CPoly Sup

section Cert

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- **The certificate**: a non-torsion class `Γ − cΓ ∞′` supported on two places above `x′ = 0`
(one fibre, at `0`). -/
def TwoPlaceCert (S2 : CurveData C L) (ι : F →+* C) : Prop :=
  ∃ (T : GlobalCert F) (Pc : PlaceCert F) (p q : ℕ) (_ : Fact p.Prime) (_ : Fact q.Prime)
    (Rp : RedFns p F) (φp : F →+* ℚ_[p]) (Pp : PrimeCert p) (Qp : PlaceCert.PrimeData p)
    (Rq : RedFns q F) (φq : F →+* ℚ_[q]) (Pq : PrimeCert q) (Qq : PlaceCert.PrimeData q)
    (Pb : ℕ) (Lm : List (List F)),
    S2.F = (toB T.Fc).map (mapRingHom ι) ∧ T.globalCheckR = true ∧ Pc.check T.Fc T.n = true ∧
    p ≠ q ∧ RedValid p Rp φp ∧ primeCheck Rp T Pp = true ∧
    Pc.primeCheck Rp T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pp.xs Qp = true ∧
    RedValid q Rq φq ∧ primeCheck Rq T Pq = true ∧
    Pc.primeCheck Rq T.Fc T.n T.I.δL T.I.Bc T.I.Dc Pq.xs Qq = true ∧
    (nonPrincOK T.n ((Qp.mp * Qq.mp) * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (Qp.mp * Qq.mp)) Lm = true ∨
      nonPrincOK T.n (pairMult p q Qp.mp Qq.mp * Pc.cΓ) Pb T.I.δL T.I.Bc T.I.Dc Pc.αs
      (Pc.fcerts T.n) (Pc.bL T.n (pairMult p q Qp.mp Qq.mp)) Lm = true) ∧
    Pc.fib.length = 1 ∧ Pc.pl.length = 2 ∧ Pc.fα 0 = 0

variable {Kb : Type*} [Field Kb] [Algebra C Kb] [IsAlgClosed Kb] [CharZero Kb]

namespace CurveData

/-- **Units at the finite places are constants** (two places at infinity, certified). -/
theorem mem_const_two (S : CurveData C L) (k M : ℕ)
    (hM : ∀ i ≤ (shiftP S.F 0).natDegree, ((shiftP S.F 0).coeff i).natDegree + k * i ≤ M)
    (hGm : (invP (shiftP S.F 0) k M).Monic)
    (hGn : (invP (shiftP S.F 0) k M).natDegree = S.F.natDegree)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (ι : F →+* C) (hcert : TwoPlaceCert (mobCurve S 0 k M hM hGm hGn) ι)
    (u : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0)
    (hfin : ∀ (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) u).order = 0) :
    ∃ c : C, (u : L) = algebraMap C L c := by
  obtain ⟨T, Pc, p, q, _, _, Rp, φp, Pp, Qp, Rq, φq, Pq, Qq, Pb, Lm, hSF, hT, hPc, hpq, hRp, hPp,
    hQp, hRq, hPq, hQq, htest, hfib1, hpl2, hα0⟩ := hcert
  exact S.mem_const_of_unit_two k M hM hGm hGn hgeo ι T hSF hT Pc hPc hpq Rp φp hRp Pp hPp Qp hQp
    Rq φq hRq Pq hPq Qq hQq Pb Lm htest hfib1 hpl2 hα0 u hu hfin

end CurveData

end Cert

namespace CurveData

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : CurveData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **The logarithms lie in the base** (two places at infinity, certified non-torsion). -/
theorem logs_in_base_two (hnd : ∀ a : K, a′ ≠ (ω.map (algebraMap C K)).eval a)
    (k0 M : ℕ)
    (hM : ∀ i ≤ (shiftP S.F 0).natDegree, ((shiftP S.F 0).coeff i).natDegree + k0 * i ≤ M)
    (hGm : (invP (shiftP S.F 0) k0 M).Monic)
    (hGn : (invP (shiftP S.F 0) k0 M).natDegree = S.F.natDegree)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C K))))
    (ι : F →+* C) (hcert : TwoPlaceCert (mobCurve S 0 k0 M hM hGm hGn) ι)
    (k : ℕ) (d : ℕ → C)
    (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0)
    (hind : ∀ q : ℕ → ℚ, ∑ j ∈ Finset.range k, (q j : C) * d j = 0 → ∀ j < k, q j = 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * ((w j)′ / w j))
    (hreg : S.RegularFinite K ⟨f, hf⟩) :
    ∀ j < k, ∃ c : C, w j = algebraMap C L c := by
  intro j hj
  have hu0 : (⟨w j, (hw j hj).1⟩ : C⟮S.x⟯⟮S.y⟯) ≠ 0 := fun h ↦
    (hw j hj).2 (congrArg Subtype.val h)
  exact S.mem_const_two (Kb := K) k0 M hM hGm hGn hgeo ι hcert _ hu0
    fun a N hN l hl r hr ↦ S.logs_zero_branchW ω hx hK k d w hw hind v f hv hf heq a (hnd a) N
      (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr) (Or.inr (hreg a N hN l hl r hr)) j hj

include hx hK in
/-- **A Liouville form has its logarithmic part in the base** (two places at infinity). -/
theorem nk_liouville_two (hnd : ∀ a : K, a′ ≠ (ω.map (algebraMap C K)).eval a)
    (k0 M : ℕ)
    (hM : ∀ i ≤ (shiftP S.F 0).natDegree, ((shiftP S.F 0).coeff i).natDegree + k0 * i ≤ M)
    (hGm : (invP (shiftP S.F 0) k0 M).Monic)
    (hGn : (invP (shiftP S.F 0) k0 M).natDegree = S.F.natDegree)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C K))))
    (ι : F →+* C) (hcert : TwoPlaceCert (mobCurve S 0 k0 M hM hGm hGn) ι)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (f : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (hreg : S.RegularFinite K ⟨f, hf⟩)
    {ι' : Type*} (s : Finset ι') (c u : ι' → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ ℓ : C, f = v′ + algebraMap C L ℓ := by
  classical
  obtain ⟨k, d, w, ⟨hd', hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd' jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dif_pos hjj]
    exact Classical.choose_spec (hconstC (d jj) (hd' jj hjj))
  have hind' : ∀ q : ℕ → ℚ, ∑ jj ∈ Finset.range k, (q jj : C) * d' jj = 0 →
      ∀ jj < k, q jj = 0 := by
    intro q hq
    apply hind q
    rw [← map_zero (algebraMap C L), ← hq, map_sum]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [map_mul, map_ratCast, hdd jj (Finset.mem_range.mp hjj)]
  have hww : ∀ jj < k, w jj ∈ C⟮S.x⟯⟮S.y⟯ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : f = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * ((w jj)′ / w jj) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj), logDeriv]
  have hbase := S.logs_in_base_two ω hx hK hnd k0 M hM hGm hGn hgeo ι hcert k d' w hww hind' v f
    hv hf heq' hreg
  choose! e he using hbase
  refine ⟨∑ jj ∈ Finset.range k, d' jj * logDeriv (e jj), ?_⟩
  rw [heq', map_sum]
  congr 1
  refine Finset.sum_congr rfl fun jj hjj ↦ ?_
  rw [he jj (Finset.mem_range.mp hjj), map_mul, ← logDeriv, logDeriv_algebraMap]

end CurveData

end Curves
