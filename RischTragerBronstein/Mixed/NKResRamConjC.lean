import RischTragerBronstein.Mixed.NKResRamConj
import RischTragerBronstein.Mixed.KQSem

/-!
# Code-level certificate: ramified places at infinity, one residual root per place

`splitResRamCk`: for a single slope `s/e` (`gcd(s, e) = 1`), one nonzero simple residual root `γₖ`
of the expanded inverted curve per place (`n/e` of them, with distinct `γₖᵉ`), truncations `Θ̃ₖ` and
the derivative test on `∑ⱼ ∑ᵢ f̃ⱼᵢ [T^{e+i+sj}] Θ̃ₖʲ`. `zero_res_ramConjC`: then all residues of
`f` along the branch system with `N = e` above infinity vanish (`zero_res_ramConj`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Tower.PrimN GTors Differential

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- **The ramified zero-residue certificate with one residual root per place.** -/
def splitResRamCk (m e s M : ℕ) (Pp : List (GPoly (LC m))) (γs : List (LC m))
    (Θs : List (GPoly (LC m))) (fp : List (GPoly (LC m))) : Bool :=
  let O := MO Fc ks m
  let n := Pp.length
  let np := γs.length
  let Ppe := Pp.map (expandGC Fc ks m e)
  let fpe := fp.map (expandGC Fc ks m e)
  let R := residualC Fc ks m s Ppe
  decide (0 < e) && decide (0 < n) && decide (np * e = n) && decide (Nat.Coprime s e) &&
  (List.range n).all (fun i ↦ decide ((Ppe.getD i []).length ≤ (n - i) * s + 1)) &&
  (List.range np).all (fun k ↦ O.isZero (evalLC Fc ks m R (γs.getD k O.zero)) &&
    !O.isZero (evalLC Fc ks m (GPoly.derivX O R) (γs.getD k O.zero)) &&
    !O.isZero (γs.getD k O.zero)) &&
  (List.range np).all (fun k ↦ (List.range np).all fun l ↦
    decide (k = l) || !O.isZero (O.add (powC O (γs.getD k O.zero) e)
      (O.neg (powC O (γs.getD l O.zero) e)))) &&
  (List.range np).all (fun k ↦
    O.isZero (O.add ((Θs.getD k []).getD 0 O.zero) (O.neg (γs.getD k O.zero))) &&
    truncOKC Fc ks m M (evalPolyC Fc ks m (invCoeffsC Fc ks m s Ppe) (Θs.getD k []))) &&
  (List.range n).all (fun j ↦ decide (e + max 1 (fpe.getD j []).length + s * j ≤ M)) &&
  (List.range np).all (fun k ↦ derivTestC Fc ks lv m (resInfCN Fc ks m e s n fpe (Θs.getD k [])))

end Codes

section Main

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m} {m : ℕ}
variable {F L' K : Type*} [Field F] [Differential F] [CharZero F]
  [Field L'] [CharZero L'] [Algebra F L'] [Differential L'] [DifferentialAlgebra F L']
  [Field K] [CharZero K] [Algebra F K] [Differential K] [IsAlgClosed K]

/-- **A passing certificate gives zero residues at the ramified places at infinity.** -/
theorem zero_res_ramConjC (S : CurveData F L') (M : CField (LC m) F (MO Fc ks m))
    {Cs : Type*} [Field Cs] [CharZero Cs] (ι : Cs →+* F)
    (hrde : RdeSpecK ι M (M.sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩))
      (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩))
    (hK : ∀ c : F, (algebraMap F K c)′ = algebraMap F K c′)
    (Pp : List (GPoly (LC m))) (hSF : S.F = polyF (aPoly M Pp) Pp.length)
    (e s Mn : ℕ) (γs : List (LC m)) (Θs fp : List (GPoly (LC m)))
    (hck : splitResRamCk Fc ks lv m e s Mn Pp γs Θs fp = true) :
    ∃ (he : 0 < e) (li : List (LaurentSeries K)) (hli : S.F.map (infSub (K := K) e) =
      (li.map fun r ↦ X - Polynomial.C r).prod),
      ∀ r (hr : r ∈ li), ∃ β : K, (S.embG (infSub e) (infSub_injective e he) r
        (S.root_of_mem hli hr) (S.evT (∑ j ∈ Finset.range Pp.length,
          Polynomial.C (GPoly.toPoly M (fp.getD j [])) * X ^ j))).coeff (e : ℤ) = β′ := by
  classical
  simp only [splitResRamCk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨he, hn0⟩, hne⟩, hcop⟩, hlen⟩, hroots⟩, hdist⟩, hΘ⟩, hMb⟩, hder⟩ := hck
  set n := Pp.length with hn
  set np := γs.length with hnp
  set Ppe := Pp.map (expandGC Fc ks m e) with hPpe
  set fpe := fp.map (expandGC Fc ks m e) with hfpe
  have hlenE : Ppe.length = n := by rw [hPpe, List.length_map]
  have hlen' : ∀ i < Ppe.length, (Ppe.getD i []).length ≤ (Ppe.length - i) * s + 1 := by
    rw [hlenE]; exact hlen
  set P0 := polyF (aPoly M Pp) n with hP0
  have hP0m : P0.Monic := polyF_monic _ _
  have hP0n : P0.natDegree = n := polyF_natDegree _ _
  have hPe : polyF (aPoly M Ppe) Ppe.length = P0.map (expand F e : F[X] →+* F[X]) := by
    rw [hP0, hlenE]
    simp only [polyF, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hPpe, aPoly_expandGC M e he]
    rfl
  have hdeg : ∀ i ≤ n, (P0.coeff i).natDegree * e ≤ (n - i) * s := by
    intro i hi
    rcases lt_or_eq_of_le hi with hi | rfl
    · rw [hP0, polyF_coeff _ _ _ hi, ← natDegree_expand, ← aPoly_expandGC M e he]
      have h1 := natDegree_toPoly_le M (Ppe.getD i [])
      have h2 := hlen i hi
      rw [aPoly, ← hPpe]; omega
    · have hc : P0.coeff Pp.length = 1 := by
        have := hP0m; rw [Monic, Polynomial.leadingCoeff, hP0n] at this; exact this
      rw [hc]; simp
  -- the residual roots
  set γ : Fin np → F := fun k ↦ M.sem (γs.getD k (MO Fc ks m).zero) with hγ
  have hfib := fibreAt_invPS_polyF (K := K) M Ppe s hlen'
  rw [hPe, hlenE] at hfib
  have hγroot : ∀ k : Fin np, (fibreAt (K := K) (invPS n s (P0.map (expand F e : F[X] →+* F[X])))
      0).eval (algebraMap F K (γ k)) = 0 := by
    intro k
    rw [hfib, eval_map, eval₂_hom, hγ, ← sem_evalLC, (M.isZero_iff _).mp (hroots k k.2).1.1,
      map_zero]
  have hγroot' : ∀ k : Fin np, (fibreAt (K := K) (derivative (invPS n s
      (P0.map (expand F e : F[X] →+* F[X])))) 0).eval (algebraMap F K (γ k)) ≠ 0 := by
    intro k
    rw [fibreAt_derivative, hfib, Polynomial.derivative_map, eval_map, eval₂_hom, hγ,
      ← GPoly.toPoly_derivX, ← sem_evalLC]
    intro h0
    have := (map_eq_zero_iff _ (algebraMap F K).injective).mp h0
    have h2 := (hroots k k.2).1.2
    rw [Bool.eq_false_iff] at h2
    exact h2 ((M.isZero_iff _).mpr this)
  have hγ0 : ∀ k : Fin np, γ k ≠ 0 := by
    intro k h0
    have h2 := (hroots k k.2).2
    rw [Bool.eq_false_iff] at h2
    exact h2 ((M.isZero_iff _).mpr h0)
  have hγi : Function.Injective fun k : Fin np ↦ γ k ^ e := by
    intro k l hkl
    by_contra hne'
    have h := (hdist k k.2 l l.2).resolve_left (fun h ↦ hne' (Fin.ext h))
    rw [Bool.eq_false_iff] at h
    apply h
    rw [M.isZero_iff, M.sem_add, M.sem_neg, sem_powC, sem_powC]
    simp only [hγ] at hkl
    rw [hkl, add_neg_cancel]
  -- truncations
  set Θt : Fin np → F[X] := fun k ↦ GPoly.toPoly M (Θs.getD k []) with hΘt
  have hΘ0 : ∀ k : Fin np, (Θt k).coeff 0 = γ k := by
    intro k
    rw [hΘt, coeff_toPoly_sem]
    have := (M.isZero_iff _).mp (hΘ k k.2).1
    rw [M.sem_add, M.sem_neg, add_neg_eq_zero] at this
    exact this
  have hΘM : ∀ k : Fin np, (PowerSeries.X : PowerSeries K) ^ Mn ∣
      (fibrePS (K := K) (invPS n s (P0.map (expand F e : F[X] →+* F[X]))) 0).eval
        (((Θt k).map (algebraMap F K) : K[X]) : PowerSeries K) := by
    intro k
    have := eval_invPS_polyF M Ppe s hlen' (Θs.getD k [])
    rw [hPe, hlenE] at this
    rw [fibrePS_eval_coe, hΘt, this]
    exact dvd_of_truncOKC M Mn _ (hΘ k k.2).2
  -- the integrand
  set Q0 : F[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly M (fp.getD j [])) * X ^ j with hQ0
  set Qf : F[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly M (fpe.getD j [])) * X ^ j with hQf
  have hQe : Qf = Q0.map (expand F e : F[X] →+* F[X]) := by
    simp only [hQf, hQ0, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, hfpe, getD_map_expandGC, toPoly_expandGC M e he]
    rfl
  have hQc : ∀ j, Qf.coeff j = if j < n then GPoly.toPoly M (fpe.getD j []) else 0 := by
    intro j
    rw [hQf, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hQd : Qf.natDegree < n := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := n - 1) fun j hj ↦ ?_)
      (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]; have := Finset.mem_range.mp hj; omega
  have hM : ∀ j ≤ (Q0.map (expand F e : F[X] →+* F[X])).natDegree,
      e + ((Q0.map (expand F e : F[X] →+* F[X])).coeff j).natDegree + s * j < Mn := by
    rw [← hQe]
    intro j hj
    have hjn : j < n := lt_of_le_of_lt hj hQd
    rw [hQc, if_pos hjn]
    have h1 := natDegree_toPoly_le M (fpe.getD j [])
    have h2 := hMb j hjn
    omega
  have hz : ∀ k : Fin np, ∃ z : F,
      z′ = M.sem (resInfCN Fc ks m e s n fpe (Θs.getD k [])) :=
    fun k ↦ derivTestC_sound ι M hrde _ (hder k k.2)
  choose z hz using hz
  have hzk : ∀ k : Fin np, (z k)′ = ∑ j ∈ Finset.range
      ((Q0.map (expand F e : F[X] →+* F[X])).natDegree + 1),
      ∑ i ∈ Finset.range (((Q0.map (expand F e : F[X] →+* F[X])).coeff j).natDegree + 1),
        ((Q0.map (expand F e : F[X] →+* F[X])).coeff j).coeff i *
          ((Θt k) ^ j).coeff (e + i + s * j) := by
    intro k
    rw [hz k, sem_resInfCN, ← hQe]
    simp only [hΘt]
    have hstep : ∀ j ∈ Finset.range n,
        ∑ i ∈ Finset.range (fpe.getD j []).length, M.sem ((fpe.getD j []).getD i (MO Fc ks m).zero) *
          ((GPoly.toPoly M (Θs.getD k [])) ^ j).coeff (e + i + s * j) =
        ∑ i ∈ Finset.range ((Qf.coeff j).natDegree + 1), (Qf.coeff j).coeff i *
          ((GPoly.toPoly M (Θs.getD k [])) ^ j).coeff (e + i + s * j) := by
      intro j hj
      rw [hQc, if_pos (Finset.mem_range.mp hj)]
      exact sum_toPoly_coeff M _ _
    rw [Finset.sum_congr rfl hstep]
    symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr (show Qf.natDegree + 1 ≤ n by omega))
      fun j _ hnj ↦ ?_
    rw [coeff_eq_zero_of_natDegree_lt (by simpa using hnj)]
    simp
  obtain ⟨li, hli, hres⟩ := zero_res_ramConj (K := K) P0 hP0m n np e s Mn he hne hcop hP0n hdeg γ
    hγ0 hγi hγroot hγroot' Θt hΘ0 hΘM Q0 hM z hzk hK
  refine ⟨he, li, by rw [hSF]; exact hli, fun r hr ↦ ?_⟩
  obtain ⟨β, hβ⟩ := hres r hr
  exact ⟨β, by rw [S.embG_evT]; exact hβ⟩

end Main

end Curves.MT
