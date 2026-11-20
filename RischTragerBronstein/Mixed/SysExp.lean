import RischTragerBronstein.Mixed.SysPrim
import RischTragerBronstein.Computable.SysDenE
import RischTragerBronstein.Computable.SysDegE
import RischTragerBronstein.Computable.SysVecRde

/-!
# Coupled Risch systems at an exponential level

`expSysC` solves `Y′ + (A₀ / q) Y = ∑ cₗ G₀ₗ / h` over `Fₘ(t)`, `t = exp a` (`t′ = a′ t`), for
`q`, `h` monic, `q(0) ≠ 0`, `A₀(0) = 0` and `deg A₀ < deg q` (the matrix vanishes at `t = 0` and
at infinity; checked, otherwise `none`):
* denominator `Den = h q^B` (`indBound` at `q`; at `t = 0` the pole order is bounded by that of
  the right-hand side, `sys_den_zero`);
* `W`-system `a W′ + B_W W = ∑ cₗ Cₗ` as at a primitive level;
* degree `≤ max (deg Den) (N − δ)` (`sys_deg_exp`);
* the loop with the diagonal Risch equations `z′ + (k − deg Den) a′ z = ∑ cₗ wₗ` one level down
  (`vecRde` over a scalar Risch solver `rdeD`), and the final constant filter (`mrel`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The `W`-system at an exponential level** (`t′ = b t`, `b` a code). -/
def wSysE (m : ℕ) (bc : LC m) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m))
    (G0 : List (Fin n → GPoly (LC m))) (B : ℕ) : WSys m n :=
  let O := MO Fc ks m
  let Den := GPoly.mul O h (sysPowC O q B)
  let dDen := DzLC O O.zero bc Den
  let xX := tX Fc ks m
  { Den := Den
    a := GPoly.mul O xX (GPoly.mul O q (GPoly.mul O h Den))
    BWl := matL fun i ↦ matL fun j ↦ GPoly.mul O xX (GPoly.sub O (GPoly.mul O (GPoly.mul O h Den)
      (A0 i j)) (if i = j then GPoly.mul O q (GPoly.mul O h dDen) else []))
    Cll := G0.map fun g ↦ matL fun i ↦
      GPoly.mul O xX (GPoly.mul O q (GPoly.mul O (GPoly.mul O Den Den) (g i))) }

/-- **The system solver at an exponential level** `t = exp a`; `rdeD c` solves the parametric
Risch equations `y′ + c′ y = ∑ cₗ wₗ` one level down. -/
def expSysC (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m))) :
    Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))) :=
  let O := MO Fc ks m
  let cst := mcst Fc ks m
  let bc := O.deriv a
  if !(isMonicC O q && isMonicC O h) then none else
  if O.isZero (q.getD 0 O.zero) then none else
  if !((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      O.isZero ((A0 i j).getD 0 O.zero)) then none else
  match indBound2 Fc ks m (degG O q) n q (DzLC O O.zero bc q) A0 with
  | none => none
  | some B =>
    let W := wSysE Fc ks m bc n A0 q h G0 B
    let δ := degG O W.a
    let dD := degG O W.Den
    let okB := (List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim O (W.BW i j)).length ≤ δ + 1) &&
      O.isZero (O.add ((W.BW i j).getD δ O.zero)
        (if i = j then O.mul (O.natCast dD) bc else O.zero))
    if !okB then none else
    let Ncl := (W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0
    let N' := max dD (Ncl - δ)
    let PA : Fin n → Fin n → LC m := fun i j ↦ if i = j then O.inv (leadG O W.a) else O.zero
    some (W.Den, polySysC O O.zero bc (fun i j ↦ if i = j then W.a else []) W.BW cst W.Cl δ false
      PA PA (fun k ws ↦ vecRde O cst (rdeD (O.mul (cst ((k : ℚ) - dD)) a)) ws) (mrel Fc ks m)
      (N' + 1))

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable (m : ℕ) (h : T.Tr m) (bc : LC m) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m))
  (q hh : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m))) (B : ℕ)

lemma wSysE_Den : GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).Den =
    GPoly.toPoly (T.MP m h) hh * GPoly.toPoly (T.MP m h) q ^ B := by
  simp [wSysE, toPoly_sysPowC]

lemma wSysE_a : GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).a =
    X * (GPoly.toPoly (T.MP m h) q * (GPoly.toPoly (T.MP m h) hh *
      GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).Den)) := by
  simp only [wSysE, GPoly.toPoly_mul, T.toPoly_tX m h]

lemma wSysE_BW (i j : Fin n) : semPM (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).BW i j =
    X * (GPoly.toPoly (T.MP m h) hh * GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).Den *
      semMat (T.MP m h) A0 i j - if i = j then GPoly.toPoly (T.MP m h) q *
        (GPoly.toPoly (T.MP m h) hh * DzL 0 ((T.MP m h).sem bc)
          (GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).Den)) else 0) := by
  simp only [semPM, WSys.BW, wSysE, listFn_matL, GPoly.toPoly_mul, GPoly.toPoly_sub,
    T.toPoly_tX m h, semMat, Matrix.of_apply]
  split_ifs
  · simp only [GPoly.toPoly_mul, toPoly_DzLC, (T.MP m h).sem_zero]
  · simp

lemma wSysE_Cl (l : ℕ) (i : Fin n) :
    ((wSysE Fc ks m bc n A0 q hh G0 B).Cl.map (semV (T.MP m h))).getD l 0 i =
      X * (GPoly.toPoly (T.MP m h) q * (GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).Den ^ 2 *
        GPoly.toPoly (T.MP m h) ((G0.getD l fun _ ↦ []) i))) := by
  rw [getD_semCl]
  by_cases hl : l < G0.length
  · simp only [WSys.Cl, wSysE, List.map_map]
    rw [NestTower.getD_map' _ _ (fun _ ↦ []) _ hl]
    simp only [Function.comp_apply, semV, listFn_matL, GPoly.toPoly_mul, T.toPoly_tX m h]
    ring
  · rw [List.getD_eq_default _ _ (by simp [WSys.Cl, wSysE]; omega), List.getD_eq_default _ _ (by omega)]
    simp [semV]

/-- `A_W W′ + B_W W` is `t` times the cleared equation. -/
lemma wSysE_LopV (W : Fin n → (T.F m)[X]) (i : Fin n) :
    LopV 0 ((T.MP m h).sem bc)
      (semPM (T.MP m h) fun i j ↦ if i = j then (wSysE Fc ks m bc n A0 q hh G0 B).a else [])
      (semPM (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).BW) W i =
    X * (GPoly.toPoly (T.MP m h) q * GPoly.toPoly (T.MP m h) hh *
      (GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).Den * DzL 0 ((T.MP m h).sem bc) (W i) -
        DzL 0 ((T.MP m h).sem bc) (GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).Den) * W i) +
      GPoly.toPoly (T.MP m h) hh * GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).Den *
        ∑ j, semMat (T.MP m h) A0 i j * W j) := by
  simp only [LopV, T.wSysE_BW m h bc n A0 q hh G0 B, Finset.sum_add_distrib]
  have e1 : ∑ j, semPM (T.MP m h) (fun i j ↦ if i = j then (wSysE Fc ks m bc n A0 q hh G0 B).a else [])
      i j * DzL 0 ((T.MP m h).sem bc) (W j) =
      GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).a * DzL 0 ((T.MP m h).sem bc) (W i) := by
    simp only [semPM]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [if_neg (Ne.symm hj)]; simp) (by simp), if_pos rfl]
  rw [e1, T.wSysE_a m h bc n A0 q hh G0 B]
  set Q := GPoly.toPoly (T.MP m h) q * (GPoly.toPoly (T.MP m h) hh *
    DzL 0 ((T.MP m h).sem bc) (GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).Den))
  set hD := GPoly.toPoly (T.MP m h) hh * GPoly.toPoly (T.MP m h) (wSysE Fc ks m bc n A0 q hh G0 B).Den
  have e2 : ∀ x, X * (hD * semMat (T.MP m h) A0 i x - if i = x then Q else 0) * W x =
      X * hD * (semMat (T.MP m h) A0 i x * W x) - if i = x then X * Q * W i else 0 := by
    intro x
    split_ifs with hx
    · subst hx; ring
    · ring
  rw [Finset.sum_congr rfl fun x _ ↦ e2 x, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _), ← Finset.mul_sum]
  simp only [hD, Q]
  ring


/-- **Soundness at an exponential level**: every output `(e, W)` gives the solution `W / Den`
of `Y′ + (A₀/q) Y = ∑ eₗ G₀ₗ / h`, in the cleared form `SysSol` (`t′ = a′ t`). -/
theorem expSysC_sound (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (Den : GPoly (LC m)) (out : List (List ℚ × (Fin n → GPoly (LC m))))
    (hres : expSysC Fc ks m a rdeD n A0 q hh G0 = some (Den, out)) :
    ∀ r ∈ out, SysSol 0 ((T.MP m h).sem ((MO Fc ks m).deriv a)) (GPoly.toPoly (T.MP m h) q)
      (GPoly.toPoly (T.MP m h) hh) (semMat (T.MP m h) A0)
      (fun i ↦ ∑ l ∈ Finset.range G0.length, C ((r.1.getD l 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MP m h) ((G0.getD l fun _ ↦ []) i))
      (semV (T.MP m h) r.2) (GPoly.toPoly (T.MP m h) Den) := by
  unfold expSysC at hres
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

lemma coeff_zero_ne_of_not_dvd {K : Type*} [Field K] (p f : K[X]) (c : K) (hc : c ≠ 0)
    (hp : p = X * C c) (hf : ¬ p ∣ f) : f.coeff 0 ≠ 0 := by
  intro h0
  apply hf
  obtain ⟨g, hg⟩ := X_dvd_iff.mpr h0
  exact ⟨C c⁻¹ * g, by rw [hg, hp, mul_assoc, ← mul_assoc (C c), ← C_mul, mul_inv_cancel₀ hc, C_1,
    one_mul]⟩

/-- **Completeness at an exponential level** `t = exp a`: every solution `Z / d` of
`Y′ + (A₀/q) Y = ∑ cₗ G₀ₗ / h` (constants `cₗ`) is `W / Den` with `(c, W)` a constant
combination of the outputs. `hom`: no nonzero `z` with `z′ + j a′ z = 0`, `j ≠ 0`; `hrdeD`: the
Risch solver one level down. -/
theorem expSysC_complete (hm : m < T.n) (htr : Transcendental (T.F m) (T.ts m)) (a : LC m)
    (hk : ks m = .exp a) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (Den : GPoly (LC m)) (out : List (List ℚ × (Fin n → GPoly (LC m))))
    (hres : expSysC Fc ks m a rdeD n A0 q hh G0 = some (Den, out))
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
  unfold expSysC at hres
  simp only at hres
  split_ifs at hres with hmon hq0c hA0c
  split at hres
  · exact absurd hres (by simp)
  rename_i B hB
  split_ifs at hres with hok
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
  set bcode := (MO Fc ks m).deriv a with hbcode
  have hall : ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim (MO Fc ks m) ((wSysE Fc ks m bcode n A0 q hh G0 B).BW i j)).length ≤
        degG (MO Fc ks m) (wSysE Fc ks m bcode n A0 q hh G0 B).a + 1) &&
      (MO Fc ks m).isZero ((MO Fc ks m).add (((wSysE Fc ks m bcode n A0 q hh G0 B).BW i j).getD
        (degG (MO Fc ks m) (wSysE Fc ks m bcode n A0 q hh G0 B).a) (MO Fc ks m).zero)
        (if i = j then (MO Fc ks m).mul ((MO Fc ks m).natCast
          (degG (MO Fc ks m) (wSysE Fc ks m bcode n A0 q hh G0 B).Den)) bcode
          else (MO Fc ks m).zero))) = true := by
    revert hok; cases ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim (MO Fc ks m) ((wSysE Fc ks m bcode n A0 q hh G0 B).BW i j)).length ≤
        degG (MO Fc ks m) (wSysE Fc ks m bcode n A0 q hh G0 B).a + 1) &&
      (MO Fc ks m).isZero ((MO Fc ks m).add (((wSysE Fc ks m bcode n A0 q hh G0 B).BW i j).getD
        (degG (MO Fc ks m) (wSysE Fc ks m bcode n A0 q hh G0 B).a) (MO Fc ks m).zero)
        (if i = j then (MO Fc ks m).mul ((MO Fc ks m).natCast
          (degG (MO Fc ks m) (wSysE Fc ks m bcode n A0 q hh G0 B).Den)) bcode
          else (MO Fc ks m).zero))) <;> simp
  have hA0all : ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      (MO Fc ks m).isZero ((A0 i j).getD 0 (MO Fc ks m).zero)) = true := by
    revert hA0c; cases ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      (MO Fc ks m).isZero ((A0 i j).getD 0 (MO Fc ks m).zero)) <;> simp
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
  have hA0 : ∀ i j, (semMat M A0 i j).coeff 0 = 0 := fun i j ↦ by
    have := List.all_eq_true.mp (List.all_eq_true.mp hA0all i (List.mem_finRange _)) j
      (List.mem_finRange _)
    simp only [semMat, Matrix.of_apply, coeff_toPoly_sem]
    exact (M.isZero_iff _).mp this
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
    exact sys_den_zero b qs hq0 (semMat M A0) hA0 _ (fun z hz j hj ↦ hom z hz j hj) Z'
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
  have hBchk : ∀ i j, (GPoly.trim O (W.BW i j)).length ≤ δ + 1 ∧
      O.isZero (O.add ((W.BW i j).getD δ O.zero)
        (if i = j then O.mul (O.natCast dD) bcode else O.zero)) = true := fun i j ↦ by
    have := List.all_eq_true.mp (List.all_eq_true.mp hall i (List.mem_finRange _)) j
      (List.mem_finRange _)
    rw [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  have hBnat : ∀ i j, (semPM M W.BW i j).natDegree ≤ δ := by
    intro i j
    by_cases htr0 : GPoly.trim O (W.BW i j) = []
    · rw [semPM, (GPoly.trim_eq_nil_iff M _).mp htr0, natDegree_zero]; exact Nat.zero_le _
    · have := (hBchk i j).1
      have e : (GPoly.trim O (W.BW i j)).length = (GPoly.trim (MO Fc ks m) (W.BW i j)).length := rfl
      rw [semPM, (GPoly.natDegree_toPoly_of_trim_ne_nil M htr0).1]; omega
  have hBδ : ∀ i j, (semPM M W.BW i j).coeff δ = if i = j then -((dD : T.F m) * b) else 0 := by
    intro i j
    have h0 := (M.isZero_iff _).mp (hBchk i j).2
    rw [M.sem_add] at h0
    rw [semPM, coeff_toPoly_sem]
    split_ifs at h0 ⊢ with hij
    · rw [M.sem_mul, M.sem_natCast] at h0; linear_combination h0
    · rw [M.sem_zero, add_zero] at h0; exact h0
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
  have hdegW := fun j ↦ sys_deg_exp b (semPM M AW) (semPM M W.BW) δ hA1 hBnat hAδ' dD hBδ hom
    Ncl Wv G hGz hLop j
  -- the polynomial system
  have hmv1 : ∀ v : Fin n → T.F m, mv (fun i j ↦ if i = j then (1 : T.F m) else 0) v = v := fun v ↦ by
    funext i; simp [mv]
  have hsolres : resCV (M.sem O.zero) (M.sem bcode) (semPM M AW) (semPM M W.BW) (W.Cl.map (semV M)) ι
      c Wv = 0 := by
    funext i
    rw [resCV, hz0, ← hb, hLop]
    simp [hG]
  have hderiv : ∀ k : ℕ, (M.sem (O.mul (mcst Fc ks m ((k : ℚ) - dD)) a))′ =
      (((k : ℚ) - dD : ℚ) : T.F m) * b := fun k ↦ by
    rw [M.sem_mul, T.sem_mcst m h, Derivation.leibniz, T.deriv_ratCast, smul_zero, add_zero,
      smul_eq_mul, hb, hbcode, M.sem_deriv]
  obtain ⟨γ, hγc, hγW⟩ := polySysC_complete ι M O.zero bcode AW W.BW (mcst Fc ks m) (T.sem_mcst m h)
    W.Cl δ T.deriv_algebraMap_Cc T.algebraMap_ratCast hA1 hBnat false PA PA
    (fun k ws ↦ vecRde O (mcst Fc ks m) (rdeD (O.mul (mcst Fc ks m ((k : ℚ) - dD)) a)) ws)
    (fun h ↦ absurd h (by simp))
    (fun _ ↦ ⟨fun v ↦ by rw [hAδ, hPAs, hmv1, hmv1], fun v ↦ by rw [hAδ, hPAs, hmv1, hmv1],
      fun k ↦ ⟨fun i j ↦ if i = j then (M.sem (O.mul (mcst Fc ks m ((k : ℚ) - dD)) a))′ else 0,
        fun z i ↦ by
          rw [hderiv]
          simp only [hAδ', hBδ, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
            Finset.sum_ite_eq, Finset.mem_univ, if_true, mv, ← hb]
          push_cast
          ring,
        fun wsC ↦ vecRde_spec _ M (mcst Fc ks m) (T.sem_mcst m h) _ _ wsC (hrdeD _)
          T.algebraMap_ratCast⟩⟩)
    (mrel Fc ks m) (T.mrel_relSpec m h) (max dD (Ncl - δ))
    (fun l hl i ↦ by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro d' hd'
      exact hClc l hl i d' (by
        have : max dD (Ncl - δ) + δ < d' := by exact_mod_cast hd'
        omega))
    c (fun l hl ↦ hc l (by omega)) Wv hdegW hsolres
  refine ⟨γ, hγc, fun i ↦ ?_⟩
  rw [hDZ i, hγW i]

end MTower

end Curves.MT
