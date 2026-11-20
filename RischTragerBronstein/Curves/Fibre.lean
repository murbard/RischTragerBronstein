import RischTragerBronstein.Curves.Branch

/-!
# The branches above a point

For `a ∈ K` (`K` algebraically closed of characteristic zero), `branches_at`: after `x ↦ a + Tᴺ`,
`F` splits over `K⟦T⟧` (Newton–Puiseux): `F(a + Tᴺ, Y) = ∏ⱼ (Y − Yⱼ(T))`, `n = deg_Y F` factors.
Each `Yⱼ` gives an embedding `embG` of `C⟮x⟯⟮y⟯` into `K⸨T⸩` (a branch of the curve above `a`).
-/

open Polynomial HahnSeries

namespace Curves

open Differential

section PS

variable {C K : Type*} [Field C] [Field K] [Algebra C K]

lemma expand_coe (N : ℕ) (hN : N ≠ 0) (Q : K[X]) :
    PowerSeries.expand N hN (Q : PowerSeries K) = ((Q.comp (X ^ N) : K[X]) : PowerSeries K) := by
  ext n
  rw [PowerSeries.coeff_expand, Polynomial.coeff_coe, Polynomial.coeff_coe,
    ← expand_eq_comp_X_pow, coeff_expand (Nat.pos_of_ne_zero hN)]

/-- `P(a + T)` as a power series. -/
noncomputable def polyShift (a : K) : C[X] →+* PowerSeries K :=
  (Polynomial.coeToPowerSeries.ringHom (R := K)).comp
    ((Polynomial.compRingHom (X + Polynomial.C a)).comp (Polynomial.mapRingHom (algebraMap C K)))

lemma polyShift_apply (a : K) (P : C[X]) :
    polyShift a P = (((P.map (algebraMap C K)).comp (X + Polynomial.C a) : K[X]) : PowerSeries K) :=
  rfl

lemma ofPS_ex_polyShift (N : ℕ) (hN : N ≠ 0) (a : K) (P : C[X]) :
    ofPowerSeries ℤ K (Puiseux.ex N (polyShift a P)) = branchSub N a P := by
  rw [Puiseux.ex_apply hN, polyShift_apply, expand_coe, branchSub_apply, comp_assoc, add_comp,
    X_comp, C_comp, add_comm]

end PS

section HasBr

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- A complete branch system above every finite point (Newton–Puiseux in characteristic `0`,
supplied separately in characteristic `p`). -/
def CurveData.HasBranches (S : CurveData C L) (K : Type*) [Field K] [Algebra C K] : Prop :=
  ∀ a : K, ∃ N, N ≠ 0 ∧ ∃ l : List (PowerSeries K), l.length = S.F.natDegree ∧
    S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C (ofPowerSeries ℤ K r)).prod

end HasBr

section Branches

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]
  [IsAlgClosed K] [CharZero K]

/-- **Newton–Puiseux for a monic `F ∈ C[x][Y]`**: `F(a + Tᴺ, Y) = ∏ⱼ (Y − Yⱼ)`, `Yⱼ ∈ K⟦T⟧`. -/
theorem split_at (F : C[X][X]) (hF : F.Monic) (a : K) :
    ∃ N, N ≠ 0 ∧ ∃ l : List (PowerSeries K), l.length = F.natDegree ∧
      F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C (ofPowerSeries ℤ K r)).prod := by
  obtain ⟨N, hN, l, hl, hsplit⟩ := Puiseux.puiseux_split F.natDegree (F.map (polyShift a))
    (hF.map _) (hF.natDegree_map _)
  refine ⟨N, hN, l, hl, ?_⟩
  have e1 : ((F.map (polyShift a)).map (Puiseux.ex N)).map (ofPowerSeries ℤ K) =
      F.map (branchSub N a) := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun P ↦ ofPS_ex_polyShift N hN a P
  rw [← e1, hsplit, Polynomial.map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun r _ ↦ ?_
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

namespace CurveData

variable (S : CurveData C L)

/-- **The branches above `a`**: `F(a + Tᴺ, Y) = ∏ⱼ (Y − Yⱼ)` with `Yⱼ ∈ K⟦T⟧`. -/
theorem branches_at (a : K) :
    ∃ N, N ≠ 0 ∧ ∃ l : List (PowerSeries K), l.length = S.F.natDegree ∧
      S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C (ofPowerSeries ℤ K r)).prod :=
  split_at S.F S.monic a

/-- In characteristic `0`, branch systems exist everywhere. -/
theorem hasBranches : S.HasBranches K := S.branches_at

end CurveData

end Branches

end Curves
