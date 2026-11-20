import RischTragerBronstein.Mixed.RdeLocal
import RischTragerBronstein.Curves.Ansatz
import RischTragerBronstein.Curves.Lift

/-!
# Pole bounds for the Risch equation on a curve

For `z′ + h′ z = w` in `C⟮x⟯⟮y⟯`, with `w = W(x, y)/Q(x)`:

* `rde_branch`: along any branch, `ord z ≥ min(0, ord(w · dX̂/dT) + 1)` (`rde_local_lowerBd`);
* **`rde_poleBoundFin`**: `z` has pole order at most `N · mult_a(Q)` along every branch above every
  finite `a` (`x = a + Tᴺ`);
* **`rde_poleBoundInf`**: `z` has pole order at most `N · (D_W + 1 − deg Q)` along every branch above
  infinity (`x = T⁻ᴺ`, `deg Wᵢ + k i ≤ D_W`).

With `ansatz`, every solution lies in an explicit finite-dimensional space.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Bounds

variable {K : Type*} [Field K] [CharZero K]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **The Risch equation along a branch.** -/
lemma rde_branch (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (Xh : LaurentSeries K) (hX : LaurentSeries.derivation Xh ≠ 0)
    (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (z h w : C⟮S.x⟯⟮S.y⟯)
    (hE : (z : L)′ + (h : L)′ * z = w) (b : ℤ)
    (hw : LowerBd (S.embG g hg Y hY w * LaurentSeries.derivation Xh) b) :
    LowerBd (S.embG g hg Y hY z) (min 0 (b + 1)) := by
  set φ := S.embG g hg Y hY
  have hz := S.embG_derivG Xh hX g hg hgX hC hx Y hY z z.2
  have hh := S.embG_derivG Xh hX g hg hgX hC hx Y hY h h.2
  have hE' : (⟨(z : L)′, S.derivClosedXY hC hx _ z.2⟩ : C⟮S.x⟯⟮S.y⟯) +
      ⟨(h : L)′, S.derivClosedXY hC hx _ h.2⟩ * z = w := Subtype.ext hE
  have h1 := congrArg φ hE'
  rw [map_add, map_mul, hz, hh, SuperData.deltaX_apply, SuperData.deltaX_apply] at h1
  refine rde_local_lowerBd (φ z) (φ h) _ ?_ b hw
  rw [← h1]
  simp only [Subtype.coe_eta]
  field_simp
  ring

variable [IsAlgClosed K]

/-- **Finite pole bounds of solutions.** -/
theorem rde_poleBoundFin (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (z h w : C⟮S.x⟯⟮S.y⟯)
    (hE : (z : L)′ + (h : L)′ * z = w) (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0)
    (hw : (w : L) * aeval S.x Q = S.evXY W) : S.PoleBoundFin K z Q := by
  intro a N hN r hsplit k
  have hN' := Nat.pos_of_ne_zero hN
  have hwb := S.lowerBd_fin N hN' a (r k) (S.root_of_split _ r hsplit k) w W Q hQ hw
  have hD := lowerBd_single ((N : ℤ) - 1) (N : K)
  rw [← SuperData.derivation_branchX N hN' a] at hD
  have := S.rde_branch hC hx _ (hX_fin N hN' a) (branchSub N a) (branchSub_injective N hN' a)
    (fun P ↦ by rw [SuperData.branchSub_eq_subst]) (r k) (S.root_of_split _ r hsplit k) z h w hE _
    (hwb.mul hD)
  refine this.mono ?_
  have : (0 : ℤ) ≤ (N : ℤ) * ((Q.map (algebraMap C K)).rootMultiplicity a : ℤ) := by positivity
  push_cast
  omega

/-- **Pole bounds of solutions above infinity.** -/
theorem rde_poleBoundInf (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (z h w : C⟮S.x⟯⟮S.y⟯)
    (hE : (z : L)′ + (h : L)′ * z = w) (kF : ℕ) (hk : ∀ i, (S.F.coeff i).natDegree ≤ kF)
    (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0) (hw : (w : L) * aeval S.x Q = S.evXY W) (DW : ℕ)
    (hDW : ∀ i, W.coeff i ≠ 0 → (W.coeff i).natDegree + kF * i ≤ DW) :
    S.PoleBoundInf K z (DW + 1 - Q.natDegree) := by
  intro N hN r hsplit k
  have hN' := Nat.pos_of_ne_zero hN
  have hwb := S.lowerBd_inf N hN' kF hk (r k) (S.root_of_split _ r hsplit k) w W Q hQ hw DW hDW
  have hD := lowerBd_single (-(N : ℤ) - 1) (-(N : K))
  rw [← SuperData.derivation_infX N] at hD
  have := S.rde_branch hC hx _ (hX_inf N hN') (infSub N) (infSub_injective N hN')
    (fun P ↦ by rw [SuperData.infSub_eq_subst]) (r k) (S.root_of_split _ r hsplit k) z h w hE _
    (hwb.mul hD)
  refine this.mono ?_
  have h0 : (0 : ℤ) ≤ (N : ℤ) := by positivity
  refine le_min ?_ ?_
  · have : (0 : ℤ) ≤ ((N * (DW + 1 - Q.natDegree) : ℕ) : ℤ) := by positivity
    omega
  · rcases le_total (DW + 1) Q.natDegree with hle | hle
    · rw [Nat.sub_eq_zero_of_le hle]
      push_cast
      nlinarith
    · push_cast [Nat.cast_sub hle]
      nlinarith

/-- **Every solution of the Risch equation lies in the ansatz space**:
`z · discR · Q = W_z(x, y)` with `deg_x` of the coefficients bounded. -/
theorem rde_ansatz (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (z h w : C⟮S.x⟯⟮S.y⟯)
    (hE : (z : L)′ + (h : L)′ * z = w) (kF : ℕ) (hk : ∀ i, (S.F.coeff i).natDegree ≤ kF)
    (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0) (hw : (w : L) * aeval S.x Q = S.evXY W) (DW : ℕ)
    (hDW : ∀ i, W.coeff i ≠ 0 → (W.coeff i).natDegree + kF * i ≤ DW) :
    ∃ Wz : C[X][X], Wz.natDegree < S.F.natDegree ∧
      (∀ j, (Wz.coeff j).natDegree ≤ Q.natDegree + (DW + 1 - Q.natDegree) +
        ((S.F.natDegree - 1) * (S.F.natDegree - 1) + (S.F.natDegree - 1)) * S.degB) ∧
      (z : L) * aeval S.x (S.discR * Q) = S.evXY Wz :=
  S.ansatz (K := AlgebraicClosure C) z Q hQ _ (S.rde_poleBoundFin hC hx z h w hE W Q hQ hw)
    (S.rde_poleBoundInf hC hx z h w hE kF hk W Q hQ hw DW hDW)

end CurveData

end Bounds

end Curves
