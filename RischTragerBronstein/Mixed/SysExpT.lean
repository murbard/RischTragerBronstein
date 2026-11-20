import RischTragerBronstein.Mixed.SysExp
import RischTragerBronstein.Computable.SysDegT
import RischTragerBronstein.Computable.SysVecTri
import RischTragerBronstein.Computable.SysDenT
import RischTragerBronstein.Mixed.SysTriQ

/-!
# Coupled Risch systems at an exponential level: triangular limit at infinity

`expSysT` extends `expSysC` to systems whose matrix tends at infinity to `a′ Λ` with `Λ` a
rational upper triangular matrix (recovered with `ratValC` and checked), as for algebraic
functions of `exp a` (Puiseux exponents): the degree bound comes from the diagonal of `Λ`
(`sys_deg_tri`) and the stages one level down are triangular systems of Risch equations
(`triSys`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The largest natural `D` with `D − d + λ = 0` over the diagonal (or `0`). -/
def triBd (d : ℕ) (lams : List ℚ) : ℕ :=
  (lams.map fun l ↦ let v : ℚ := (d : ℚ) - l
    if v.den = 1 ∧ 0 ≤ v.num then v.num.toNat else 0).foldr max 0

/-- The candidate limit matrix `Λ` (as data): `ratValC (B_δ / a′) + d δᵢⱼ`. -/
def lamList (m : ℕ) (bc : LC m) (n : ℕ) (BW : Fin n → Fin n → GPoly (LC m)) (δ dD : ℕ) :
    List (List ℚ) :=
  (List.finRange n).map fun i ↦ (List.finRange n).map fun j ↦
    ((ratValC Fc ks m ((MO Fc ks m).mul ((BW i j).getD δ (MO Fc ks m).zero)
      ((MO Fc ks m).inv bc))).getD 0) + (if i = j then (dD : ℚ) else 0)

lemma triBd_spec (d : ℕ) (lams : List ℚ) (D : ℕ) (l : ℚ) (hl : l ∈ lams)
    (hD : (D : ℚ) - d + l = 0) : D ≤ triBd d lams := by
  unfold triBd
  refine le_foldr_max0 _ _ (List.mem_map.mpr ⟨l, hl, ?_⟩)
  have hv : (d : ℚ) - l = D := by linarith
  simp only [hv, Rat.den_natCast, Rat.num_natCast, Nat.cast_nonneg, and_self, if_true,
    Int.toNat_natCast]

/-- The candidate limit `Λ₀ = A₀(0) / (q(0) a′)` at `t = 0` (as data). -/
def lam0List (m : ℕ) (bc : LC m) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q : GPoly (LC m)) :
    List (List ℚ) :=
  let O := MO Fc ks m
  (List.finRange n).map fun i ↦ (List.finRange n).map fun j ↦
    (ratValC Fc ks m (O.mul (O.mul ((A0 i j).getD 0 O.zero) (O.inv (q.getD 0 O.zero)))
      (O.inv bc))).getD 0

/-- **The check at `t = 0`**: `A₀(0) = q(0) a′ Λ₀` with `Λ₀` rational, triangular after a
permutation of the basis, without positive integer diagonal entries (`Λ₀ = 0` is the case
`A₀(0) = 0`). -/
def zeroOK (m : ℕ) (bc : LC m) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q : GPoly (LC m)) :
    Bool :=
  let O := MO Fc ks m
  let L0 := lam0List Fc ks m bc n A0 q
  let Λ0 : Fin n → Fin n → ℚ := fun i j ↦ (L0.getD i []).getD j 0
  ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
     O.isZero (O.add ((A0 i j).getD 0 O.zero)
       (O.neg (O.mul (O.mul (q.getD 0 O.zero) bc) (mcst Fc ks m (Λ0 i j)))))) &&
  ((decide (∃ σ : Equiv.Perm (Fin n), (∀ i j : Fin n, i < j → Λ0 (σ i) (σ j) = 0) ∨
    (∀ i j : Fin n, j < i → Λ0 (σ i) (σ j) = 0)) &&
    (List.finRange n).all fun i ↦ !(decide (0 < Λ0 i i) && (Λ0 i i).den == 1)) ||
  (match triCQ n (fun i j ↦ (L0.getD i []).getD j 0) with
    | some (C, Ci) =>
      let Cq : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j ↦ C i j
      let Ciq : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j ↦ Ci i j
      let Tq := Cq * Matrix.of Λ0 * Ciq
      decide (Ciq * Cq = 1) && decide (∀ i j : Fin n, j < i → Tq i j = 0) &&
        (List.finRange n).all fun i ↦ !(decide (0 < Tq i i) && (Tq i i).den == 1)
    | none => false))

/-- **The system solver at an exponential level with a triangular limit at infinity** (and a
triangular rational limit at `t = 0`, `zeroOK`). -/
def expSysT (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m))) :
    Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))) :=
  let O := MO Fc ks m
  let cst := mcst Fc ks m
  let bc := O.deriv a
  if !(isMonicC O q && isMonicC O h) then none else
  if O.isZero (q.getD 0 O.zero) then none else
  if !(zeroOK Fc ks m bc n A0 q) then none else
  match indBound2 Fc ks m (degG O q) n q (DzLC O O.zero bc q) A0 with
  | none => none
  | some B =>
    let W := wSysE Fc ks m bc n A0 q h G0 B
    let δ := degG O W.a
    let dD := degG O W.Den
    let Ll := lamList Fc ks m bc n W.BW δ dD
    let Λ : Fin n → Fin n → ℚ := fun i j ↦ (Ll.getD i []).getD j 0
    let okB := (List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim O (W.BW i j)).length ≤ δ + 1) &&
      O.isZero (O.add ((W.BW i j).getD δ O.zero)
        (O.neg (O.mul (cst (Λ i j - if i = j then (dD : ℚ) else 0)) bc))) &&
      (decide ((j : ℕ) < i) → Λ i j == 0)
    if !okB then none else
    let Ncl := (W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0
    let N' := max (triBd dD ((List.finRange n).map fun i ↦ Λ i i)) (Ncl - δ)
    let PA : Fin n → Fin n → LC m := fun i j ↦ if i = j then O.inv (leadG O W.a) else O.zero
    some (W.Den, polySysC O O.zero bc (fun i j ↦ if i = j then W.a else []) W.BW cst W.Cl δ false
      PA PA (fun k ws ↦ triSys O cst (fun i ↦ rdeD (O.mul (cst ((k : ℚ) - dD + Λ i i)) a))
        (fun i j ↦ O.mul (cst (Λ i j)) bc) ws) (mrel Fc ks m) (N' + 1))

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)
variable (m : ℕ) (h : T.Tr m) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m))
  (q hh : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))

/-- **The check at `t = 0` is sound.** -/
lemma zeroOK_spec (bc : LC m) (hok : zeroOK Fc ks m bc n A0 q = true) :
    ∃ Λ0 : Fin n → Fin n → ℚ,
      (∀ i j, (GPoly.toPoly (T.MP m h) (A0 i j)).coeff 0 =
        (GPoly.toPoly (T.MP m h) q).coeff 0 * (T.MP m h).sem bc * (Λ0 i j : T.F m)) ∧
      (((∃ σ : Equiv.Perm (Fin n), (∀ i j : Fin n, i < j → Λ0 (σ i) (σ j) = 0) ∨
        (∀ i j : Fin n, j < i → Λ0 (σ i) (σ j) = 0)) ∧
        (∀ i (k : ℕ), 0 < k → Λ0 i i ≠ k)) ∨
      (∃ Cq Ciq : Matrix (Fin n) (Fin n) ℚ, Ciq * Cq = 1 ∧
        (∀ i j : Fin n, j < i → (Cq * Matrix.of Λ0 * Ciq) i j = 0) ∧
        (∀ i (k : ℕ), 0 < k → (Cq * Matrix.of Λ0 * Ciq) i i ≠ k))) := by
  set M := T.MP m h
  unfold zeroOK at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hok
  obtain ⟨hA, hbr⟩ := hok
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at hA
  refine ⟨fun i j ↦ ((lam0List Fc ks m bc n A0 q).getD i []).getD j 0, fun i j ↦ ?_, ?_⟩
  · have := (M.isZero_iff _).mp (hA i j)
    rw [M.sem_add, M.sem_neg, M.sem_mul, M.sem_mul, T.sem_mcst m h, add_neg_eq_zero] at this
    rw [coeff_toPoly_sem, coeff_toPoly_sem, this]
  have hdiagOf : ∀ (x : ℚ), (!(decide (0 < x) && x.den == 1)) = true → ∀ k : ℕ, 0 < k → x ≠ k := by
    intro x hx k hk heq
    rw [heq] at hx
    simp [Rat.den_natCast] at hx
    exact absurd hk (by omega)
  rcases hbr with ⟨htri, hdiag⟩ | hsim
  · left
    simp only [decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_const] at htri hdiag
    exact ⟨htri, fun i k hk ↦ hdiagOf _ (hdiag i) k hk⟩
  · right
    revert hsim
    split
    · rename_i C Ci _
      intro hsim
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
        forall_const] at hsim
      obtain ⟨⟨h1, h2⟩, h3⟩ := hsim
      exact ⟨_, _, h1, h2, fun i k hk ↦ hdiagOf _ (h3 i) k hk⟩
    · intro h; exact absurd h (by simp)

/-- **Soundness at an exponential level (triangular limit)**: every output `(e, W)` gives the solution `W / Den`
of `Y′ + (A₀/q) Y = ∑ eₗ G₀ₗ / h`, in the cleared form `SysSol` (`t′ = a′ t`). -/
theorem expSysT_sound (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (Den : GPoly (LC m)) (out : List (List ℚ × (Fin n → GPoly (LC m))))
    (hres : expSysT Fc ks m a rdeD n A0 q hh G0 = some (Den, out)) :
    ∀ r ∈ out, SysSol 0 ((T.MP m h).sem ((MO Fc ks m).deriv a)) (GPoly.toPoly (T.MP m h) q)
      (GPoly.toPoly (T.MP m h) hh) (semMat (T.MP m h) A0)
      (fun i ↦ ∑ l ∈ Finset.range G0.length, C ((r.1.getD l 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MP m h) ((G0.getD l fun _ ↦ []) i))
      (semV (T.MP m h) r.2) (GPoly.toPoly (T.MP m h) Den) := by
  unfold expSysT at hres
  simp only at hres
  split_ifs at hres with h1 h2 h3
  split at hres
  · exact absurd hres (by simp)
  rename_i B' hB
  split_ifs at hres with hok
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
  intro r hr
  have hs := polySysC_sound (algebraMap Cc (T.F m)) (T.MP m h) (MO Fc ks m).zero
    ((MO Fc ks m).deriv a) _ _ (mcst Fc ks m) (T.sem_mcst m h) _ _ false _ _ _ (mrel Fc ks m)
    (T.mrel_relSpec m h) (T.algebraMap_ratCast) _ r hr
  intro i
  have hi := congrFun hs i
  rw [resQV, Pi.sub_apply, Pi.zero_apply, sub_eq_zero, (T.MP m h).sem_zero,
    T.wSysE_LopV m h ((MO Fc ks m).deriv a) n A0 q hh G0 B', SqV, List.length_map] at hi
  simp only [T.wSysE_Cl m h ((MO Fc ks m).deriv a) n A0 q hh G0 B'] at hi
  apply mul_left_cancel₀ (X_ne_zero : (X : (T.F m)[X]) ≠ 0)
  rw [hi, show (wSysE Fc ks m ((MO Fc ks m).deriv a) n A0 q hh G0 B').Cl.length = G0.length by
    simp [WSys.Cl, wSysE], Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

/-- **Completeness at an exponential level with a triangular limit at infinity** `t = exp a`: every solution `Z / d` of
`Y′ + (A₀/q) Y = ∑ cₗ G₀ₗ / h` (constants `cₗ`) is `W / Den` with `(c, W)` a constant
combination of the outputs. `hom`: no nonzero `z` with `z′ + j a′ z = 0`, `j ≠ 0`; `hrdeD`: the
Risch solver one level down. -/
theorem expSysT_complete (hm : m < T.n) (htr : Transcendental (T.F m) (T.ts m)) (a : LC m)
    (hk : ks m = .exp a) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (Den : GPoly (LC m)) (out : List (List ℚ × (Fin n → GPoly (LC m))))
    (hres : expSysT Fc ks m a rdeD n A0 q hh G0 = some (Den, out))
    (c : List Cc) (hc : ∀ l, G0.length ≤ l → c.getD l 0 = 0) (Z : Fin n → (T.F m)[X])
    (d : (T.F m)[X]) (hd : d ≠ 0)
    (hsol : SysSol 0 ((T.MP m h).sem ((MO Fc ks m).deriv a)) (GPoly.toPoly (T.MP m h) q)
      (GPoly.toPoly (T.MP m h) hh) (semMat (T.MP m h) A0)
      (fun i ↦ ∑ l ∈ Finset.range G0.length, C (algebraMap Cc (T.F m) (c.getD l 0)) *
        GPoly.toPoly (T.MP m h) ((G0.getD l fun _ ↦ []) i)) Z d) :
    ∃ β : List Cc, (∀ l, c.getD l 0 = ∑ k ∈ Finset.range out.length,
        β.getD k 0 * algebraMap ℚ Cc ((out.getD k ([], fun _ ↦ [])).1.getD l 0)) ∧
      ∀ i, GPoly.toPoly (T.MP m h) Den * Z i = d * ∑ k ∈ Finset.range out.length,
        C (algebraMap Cc (T.F m) (β.getD k 0)) *
          semV (T.MP m h) (out.getD k ([], fun _ ↦ [])).2 i := by
  classical
  unfold expSysT at hres
  simp only at hres
  split_ifs at hres with hmon hq0c hA0c
  split at hres
  · exact absurd hres (by simp)
  rename_i B hB
  split_ifs at hres with hok
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
  set bcode := (MO Fc ks m).deriv a with hbcode
  simp only [Bool.not_eq_false, Bool.not_eq_true, Bool.not_eq_true', List.all_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, List.mem_finRange, forall_const, true_implies] at hok
  have hzero : zeroOK Fc ks m bcode n A0 q = true := by
    revert hA0c; cases zeroOK Fc ks m bcode n A0 q <;> simp
  have hWa := T.wSysE_a m h bcode n A0 q hh G0 B
  have hWCl := T.wSysE_Cl m h bcode n A0 q hh G0 B
  have hWLop := T.wSysE_LopV m h bcode n A0 q hh G0 B
  have hWDen := T.wSysE_Den m h bcode n A0 q hh G0 B
  set O := MO Fc ks m with hO
  set M := T.MP m h with hM
  set W := wSysE Fc ks m bcode n A0 q hh G0 B with hW
  set ι := algebraMap Cc (T.F m) with hι
  set b := M.sem bcode with hb
  have hz0 : M.sem O.zero = 0 := M.sem_zero
  have hmon' : (isMonicC O q && isMonicC O hh) = true := by
    revert hmon; cases (isMonicC O q && isMonicC O hh) <;> simp
  rw [Bool.and_eq_true] at hmon'
  have hqM := isMonicC_spec M q hmon'.1
  have hhM := isMonicC_spec M hh hmon'.2
  set qs := GPoly.toPoly M q with hqs
  set hs := GPoly.toPoly M hh with hhs
  set Ds := GPoly.toPoly M W.Den with hDs
  have hDs' : Ds = hs * qs ^ B := hWDen
  -- conditions at `t = 0`
  have hq0 : qs.coeff 0 ≠ 0 := by
    rw [hqs, coeff_toPoly_sem]
    intro h0
    exact hq0c ((M.isZero_iff _).mpr h0)
  obtain ⟨Λ0, hΛA, hΛ⟩ := T.zeroOK_spec m h n A0 q bcode hzero
  have hA0 : ∀ i j, (semMat M A0 i j).coeff 0 = qs.coeff 0 * b * (Λ0 i j : T.F m) := fun i j ↦ by
    simp only [semMat, Matrix.of_apply]
    exact hΛA i j
  -- the indicial bound
  have hind : ∀ (p : (T.F m)[X]) (e : ℕ), Irreducible p → p ∣ qs →
      p ∣ (Matrix.of fun i j ↦ semMat M A0 i j - if i = j then C (e : T.F m) * DzL 0 b qs
        else 0).det → e ≤ B := fun p e hp hpq hdet ↦
    T.indBound2_spec m h (degG O q) n q (DzLC O O.zero bcode q) A0 hqM (degG_eq M q).symm B hB e p
      hp hpq (by rwa [toPoly_DzLC, hz0])
  -- the special place
  have hbval : b = (T.val m a)′ := by
    rw [hb, hbcode, M.sem_deriv, T.sem_MP_F m h]
  have hspec : ∀ (p : (T.F m)[X]), Irreducible p → p ∣ DzL 0 b p → ∀ (Z : Fin n → (T.F m)[X])
      (e s : ℕ) (u h1 : (T.F m)[X]), (∃ i, ¬ p ∣ Z i) → ¬ p ∣ u → ¬ p ∣ h1 →
      SysSol 0 b qs (p ^ s * h1) (semMat M A0) (fun i ↦ ∑ l ∈ Finset.range G0.length,
        C (ι (c.getD l 0)) * GPoly.toPoly M ((G0.getD l fun _ ↦ []) i)) Z (p ^ e * u) → e ≤ s := by
    intro p hp hpd Z' e s u h1 hZ' hu hh1 hs'
    have hX : X ∣ p := by
      by_contra hX
      apply T.normal_exp m htr hk p hp hX
      rw [T.wPoly_exp hm hk, ← hbval]
      simpa [DzL] using hpd
    obtain ⟨r, hr⟩ := hX
    have hru : IsUnit r := (hp.isUnit_or_isUnit hr).resolve_left (not_isUnit_X)
    obtain ⟨c0, hc0, hc0r⟩ := Polynomial.isUnit_iff.mp hru
    have hc0' : c0 ≠ 0 := hc0.ne_zero
    have hpX : p = X * C c0 := by rw [hr, hc0r]
    obtain ⟨i0, hi0⟩ := hZ'
    have hu0 : (C (c0 ^ e) * u).coeff 0 ≠ 0 := by
      rw [coeff_C_mul]
      exact mul_ne_zero (pow_ne_zero _ hc0') (coeff_zero_ne_of_not_dvd p _ c0 hc0' hpX hu)
    have hh10 : (C (c0 ^ s) * h1).coeff 0 ≠ 0 := by
      rw [coeff_C_mul]
      exact mul_ne_zero (pow_ne_zero _ hc0') (coeff_zero_ne_of_not_dvd p _ c0 hc0' hpX hh1)
    have e1 : p ^ s * h1 = X ^ s * (C (c0 ^ s) * h1) := by rw [hpX, mul_pow, C_pow]; ring
    have e2 : p ^ e * u = X ^ e * (C (c0 ^ e) * u) := by rw [hpX, mul_pow, C_pow]; ring
    rw [e1, e2] at hs'
    rcases hΛ with ⟨⟨σ, hΛtri⟩, hΛdiag⟩ | ⟨Cq, Ciq, hCiC, hΛtri, hΛdiag⟩
    · exact sys_den_zero_perm b qs hq0 (semMat M A0) Λ0 hA0 σ hΛtri hΛdiag _
        (fun z hz j hj ↦ hom z hz j hj) Z'
        ⟨i0, coeff_zero_ne_of_not_dvd p _ c0 hc0' hpX hi0⟩ e s _ _ hu0 hh10 hs'
    · exact sys_den_zero_sim b qs hq0 (semMat M A0) Λ0 hA0 Cq Ciq hCiC (Or.inr hΛtri) hΛdiag _
        (fun z hz j hj ↦ hom z hz j hj) Z'
        ⟨i0, coeff_zero_ne_of_not_dvd p _ c0 hc0' hpX hi0⟩ e s _ _ hu0 hh10 hs'
  -- the denominator
  have hden := fun i ↦ sys_den_bound' 0 b qs hs hhM.ne_zero (semMat M A0) _ B hind Z d hd hsol
    hspec i
  choose Wv hWv using hden
  have hDZ : ∀ i, Ds * Z i = d * Wv i := fun i ↦ by rw [hDs', ← hWv i]
  have hsolW : SysSol 0 b qs hs (semMat M A0) (fun i ↦ ∑ l ∈ Finset.range G0.length,
      C (ι (c.getD l 0)) * GPoly.toPoly M ((G0.getD l fun _ ↦ []) i)) Wv Ds := by
    have h1 := sysSol_scale 0 b qs hs (semMat M A0) _ Z d Ds hsol
    have e1 : (fun i ↦ Ds * Z i) = fun i ↦ d * Wv i := funext hDZ
    rw [e1, mul_comm Ds d] at h1
    exact sysSol_cancel 0 b qs hs (semMat M A0) _ Wv Ds d hd h1
  -- the `W`-system
  set AW : Fin n → Fin n → GPoly (LC m) := fun i j ↦ if i = j then W.a else [] with hAW
  set G : Fin n → (T.F m)[X] := fun i ↦ ∑ l ∈ Finset.range (W.Cl.map (semV M)).length,
    C (ι (c.getD l 0)) * (W.Cl.map (semV M)).getD l 0 i with hG
  have hClen : W.Cl.length = G0.length := by simp [hW, WSys.Cl, wSysE]
  have hLop : LopV 0 b (semPM M AW) (semPM M W.BW) Wv = G := by
    funext i
    rw [hWLop Wv i, hsolW i, hG, List.length_map, hClen, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [hWCl]
    ring
  -- the leading coefficient
  set δ := degG O W.a with hδ
  set dD := degG O W.Den with hdD
  have haM : (GPoly.toPoly M W.a).Monic := by
    rw [hWa]
    exact monic_X.mul (hqM.mul (hhM.mul (by rw [hDs']; exact hhM.mul (hqM.pow B))))
  have hδa : (GPoly.toPoly M W.a).natDegree = δ := (degG_eq M W.a).symm
  have hlead : M.sem (leadG O W.a) = 1 := by
    rw [leadG, ← GPoly.leadingCoeff_toPoly M haM.ne_zero]; exact haM.leadingCoeff
  have hla : M.sem (O.inv (leadG O W.a)) = 1 := by rw [M.sem_inv, hlead, inv_one]
  set PA : Fin n → Fin n → LC m := fun i j ↦ if i = j then O.inv (leadG O W.a) else O.zero with hPA
  have hPAs : (fun i j ↦ M.sem (PA i j)) = fun i j ↦ if i = j then (1 : T.F m) else 0 := by
    funext i j; rw [hPA]; dsimp only; split_ifs
    · exact hla
    · exact M.sem_zero
  have hAδ : (fun i j ↦ (semPM M AW i j).coeff δ) = fun i j ↦ if i = j then (1 : T.F m) else 0 := by
    funext i j; simp only [semPM, hAW]; split_ifs
    · rw [← hδa]; exact haM.leadingCoeff
    · simp
  have hAδ' : ∀ i j, (semPM M AW i j).coeff δ = if i = j then (1 : T.F m) else 0 := fun i j ↦
    congrFun (congrFun hAδ i) j
  -- `B_W` from the check
  set Ll := lamList Fc ks m bcode n W.BW δ dD with hLl
  have hBchk := hok
  have hBnat : ∀ i j, (semPM M W.BW i j).natDegree ≤ δ := by
    intro i j
    by_cases htr0 : GPoly.trim O (W.BW i j) = []
    · rw [semPM, (GPoly.trim_eq_nil_iff M _).mp htr0, natDegree_zero]; exact Nat.zero_le _
    · have := (hBchk i j).1.1
      have e : (GPoly.trim O (W.BW i j)).length = (GPoly.trim (MO Fc ks m) (W.BW i j)).length := rfl
      rw [semPM, (GPoly.natDegree_toPoly_of_trim_ne_nil M htr0).1]; omega
  have hBδ : ∀ i j, (semPM M W.BW i j).coeff δ =
      b * ((((Ll.getD i []).getD j 0 : ℚ) : T.F m) - if i = j then (dD : T.F m) else 0) := by
    intro i j
    have h0 := (M.isZero_iff _).mp (hBchk i j).1.2
    rw [M.sem_add, M.sem_neg, M.sem_mul, T.sem_mcst m h] at h0
    rw [semPM, coeff_toPoly_sem, hb]
    split_ifs at h0 ⊢ <;> push_cast at h0 ⊢ <;> linear_combination h0
  have htri : ∀ i j : Fin n, j < i → (Ll.getD i []).getD j 0 = 0 := fun i j hji ↦ by
    have := (hBchk i j).2 hji
    simpa using this
  -- `G` vanishes from `Ncl` on
  set Ncl := (W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0 with hNcl
  have hClL : ∀ l < W.Cl.length, ∀ i, ((W.Cl.getD l fun _ ↦ []) i).length ≤ Ncl := fun l hl i ↦ by
    refine Tower.Sys.le_foldr_max _ _ (List.mem_flatMap.mpr ⟨W.Cl.getD l fun _ ↦ [], ?_, ?_⟩)
    · rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _
    · exact List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  have hClc : ∀ l < W.Cl.length, ∀ i, ∀ d', Ncl ≤ d' →
      (semV M (W.Cl.getD l fun _ ↦ []) i).coeff d' = 0 := fun l hl i d' hd' ↦ by
    rw [semV, coeff_toPoly_sem, List.getD_eq_default _ _ ((hClL l hl i).trans hd'), M.sem_zero]
  have hGz : ∀ i d', Ncl ≤ d' → (G i).coeff d' = 0 := by
    intro i d' hd'
    rw [hG, finsetSum_coeff]
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    rw [List.length_map] at hl
    rw [coeff_C_mul, getD_semCl, hClc l (Finset.mem_range.mp hl) i d' hd', mul_zero]
  have hA1 : ∀ i j, (semPM M AW i j).natDegree ≤ δ := fun i j ↦ by
    simp only [semPM, hAW]; split_ifs
    · rw [hδa]
    · simp
  have hdegW := fun j ↦ sys_deg_tri b (semPM M AW) (semPM M W.BW) δ hA1 hBnat hAδ' dD
    (fun i j : Fin n ↦ (Ll.getD i []).getD j 0) htri hBδ hom Ncl Wv G hGz hLop
    (triBd dD ((List.finRange n).map fun i : Fin n ↦ (Ll.getD i []).getD i 0))
    (fun i D hD ↦ triBd_spec dD _ D ((Ll.getD i []).getD i 0)
      (List.mem_map_of_mem (List.mem_finRange i)) hD) j
  -- the polynomial system
  have hmv1 : ∀ v : Fin n → T.F m, mv (fun i j ↦ if i = j then (1 : T.F m) else 0) v = v := fun v ↦ by
    funext i; simp [mv]
  have hsolres : resCV (M.sem O.zero) (M.sem bcode) (semPM M AW) (semPM M W.BW) (W.Cl.map (semV M)) ι
      c Wv = 0 := by
    funext i
    rw [resCV, hz0, ← hb, hLop]
    simp [hG]
  have hderiv : ∀ r : ℚ, (M.sem (O.mul (mcst Fc ks m r) a))′ = (r : T.F m) * b := fun r ↦ by
    rw [M.sem_mul, T.sem_mcst m h, Derivation.leibniz, T.deriv_ratCast, smul_zero, add_zero,
      smul_eq_mul, hb, hbcode, M.sem_deriv]
  have hsemF : ∀ i j : Fin n, M.sem (O.mul (mcst Fc ks m ((Ll.getD i []).getD j 0)) bcode) =
      (((Ll.getD i []).getD j 0 : ℚ) : T.F m) * b := fun i j ↦ by
    rw [M.sem_mul, T.sem_mcst m h, hb]
  obtain ⟨γ, hγc, hγW⟩ := polySysC_complete ι M O.zero bcode AW W.BW (mcst Fc ks m) (T.sem_mcst m h)
    W.Cl δ T.deriv_algebraMap_Cc T.algebraMap_ratCast hA1 hBnat false PA PA
    (fun k ws ↦ triSys O (mcst Fc ks m)
      (fun i : Fin n ↦ rdeD (O.mul (mcst Fc ks m ((k : ℚ) - dD + (Ll.getD i []).getD i 0)) a))
      (fun i j : Fin n ↦ O.mul (mcst Fc ks m ((Ll.getD i []).getD j 0)) bcode) ws)
    (fun h ↦ absurd h (by simp))
    (fun _ ↦ ⟨fun v ↦ by rw [hAδ, hPAs, hmv1, hmv1], fun v ↦ by rw [hAδ, hPAs, hmv1, hmv1],
      fun k ↦ ⟨triF M (fun i : Fin n ↦ (M.sem (O.mul (mcst Fc ks m ((k : ℚ) - dD + (Ll.getD i []).getD i 0))
          a))′) (fun i j : Fin n ↦ O.mul (mcst Fc ks m ((Ll.getD i []).getD j 0)) bcode),
        fun z i ↦ by
          simp only [hAδ', hBδ, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
            Finset.sum_ite_eq, Finset.mem_univ, if_true]
          rw [mv_triF, hderiv]
          have hsplit : ∑ x : Fin n, b * ((((Ll.getD i []).getD x 0 : ℚ) : T.F m) -
              if i = x then (dD : T.F m) else 0) * z x =
              b * ((((Ll.getD i []).getD i 0 : ℚ) : T.F m) - dD) * z i +
                offV M (fun i j : Fin n ↦ O.mul (mcst Fc ks m ((Ll.getD i []).getD j 0)) bcode) z i := by
            rw [offV, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm]
            congr 1
            · simp
            · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
              simp only [lt_irrefl, if_false, add_zero]
              refine Finset.sum_congr rfl fun k' hk ↦ ?_
              have hki : k' ≠ i := Finset.ne_of_mem_erase hk
              rcases lt_or_gt_of_ne hki with hlt | hgt
              · rw [if_neg (not_lt.mpr hlt.le), if_neg (Ne.symm hki), htri i k' hlt]
                push_cast; ring
              · rw [if_pos hgt, if_neg (Ne.symm hki), hsemF]
                push_cast; ring
          rw [hsplit]
          push_cast
          ring,
        fun wsC ↦ triSys_spec _ M (mcst Fc ks m) (T.sem_mcst m h) _ _ wsC _ (fun i ↦ hrdeD _)
          T.algebraMap_ratCast⟩⟩)
    (mrel Fc ks m) (T.mrel_relSpec m h)
    (max (triBd dD ((List.finRange n).map fun i : Fin n ↦ (Ll.getD i []).getD i 0)) (Ncl - δ))
    (fun l hl i ↦ by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro d' hd'
      exact hClc l hl i d' (by
        have : max (triBd dD ((List.finRange n).map fun i : Fin n ↦ (Ll.getD i []).getD i 0)) (Ncl - δ) + δ <
          d' := by exact_mod_cast hd'
        omega))
    c (fun l hl ↦ hc l (by omega)) Wv hdegW hsolres
  refine ⟨γ, hγc, fun i ↦ ?_⟩
  rw [hDZ i, hγW i]

end MTower

end Curves.MT
