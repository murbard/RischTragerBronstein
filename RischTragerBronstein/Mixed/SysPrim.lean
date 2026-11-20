import RischTragerBronstein.Computable.SysSolve
import RischTragerBronstein.Computable.SysDenG
import RischTragerBronstein.Mixed.SysSpecial
import RischTragerBronstein.Mixed.SysIndM2
import RischTragerBronstein.Mixed.SysSpecial2
import RischTragerBronstein.Computable.NestMRdeExpC

/-!
# Coupled Risch systems at a primitive level

`primSysC` solves `Y′ + (A₀ / q) Y = ∑ cₗ G₀ₗ / h` over `Fₘ(t)`, `t′ = η` (a primitive level),
`q`, `h` monic, for `Y ∈ Fₘ(t)ⁿ` and constants `cₗ`:
* denominator `Den = h q^B` (`indBound`: the natural indicial roots at `q` are `≤ B`);
* `Y = W / Den` with `W` polynomial: `a W′ + B_W W = ∑ cₗ Cₗ`, `a = t q h Den`,
  `B_W = t (h Den A₀ − q h Den′ I)`, `Cₗ = t q Den² G₀ₗ` (the factor `t` makes `deg a ≥ 1`);
* in the case `deg B_W < deg a` (checked; otherwise `none`) the degree bound is
  `max Bs (N − δ + 1)` with `Bs` bounding the special degrees (`specBound`);
* `polySysC` with the vector parametric integration one level down (`vecLim`) and `mrel`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

section Codes

variable {α : Type} (O : COps α)

/-- `p ^ N` on polynomial codes. -/
def sysPowC (p : GPoly α) : ℕ → GPoly α
  | 0 => [O.one]
  | N + 1 => GPoly.mul O p (sysPowC p N)

/-- Is `p` monic (nonzero, leading coefficient one)? -/
def isMonicC (p : GPoly α) : Bool :=
  !(GPoly.isZero O p) && O.isZero (O.add (leadG O p) (O.neg O.one))

end Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The polynomial `t` at level `m + 1`. -/
def tX (m : ℕ) : GPoly (LC m) := [(MO Fc ks m).zero, (MO Fc ks m).one]

/-- The data of the `W`-system (matrices stored as data, read through `BW`, `Cl`). -/
structure WSys (m n : ℕ) where
  Den : GPoly (LC m)
  a : GPoly (LC m)
  BWl : List (List (GPoly (LC m)))
  Cll : List (List (GPoly (LC m)))

/-- The matrix `B_W`. -/
def WSys.BW {m n : ℕ} (W : WSys m n) (i j : Fin n) : GPoly (LC m) :=
  listFn (listFn W.BWl [] i) [] j

/-- The right-hand sides `Cₗ`. -/
def WSys.Cl {m n : ℕ} (W : WSys m n) : List (Fin n → GPoly (LC m)) :=
  W.Cll.map fun l ↦ listFn l []

/-- **The `W`-system** for the denominator `h q^B`. -/
def wSys (m : ℕ) (η : LC m) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m))
    (G0 : List (Fin n → GPoly (LC m))) (B : ℕ) : WSys m n :=
  let O := MO Fc ks m
  let Den := GPoly.mul O h (sysPowC O q B)
  let dDen := DzLC O η O.zero Den
  let xX := tX Fc ks m
  { Den := Den
    a := GPoly.mul O xX (GPoly.mul O q (GPoly.mul O h Den))
    BWl := matL fun i ↦ matL fun j ↦ GPoly.mul O xX (GPoly.sub O (GPoly.mul O (GPoly.mul O h Den)
      (A0 i j)) (if i = j then GPoly.mul O q (GPoly.mul O h dDen) else []))
    Cll := G0.map fun g ↦ matL fun i ↦
      GPoly.mul O xX (GPoly.mul O q (GPoly.mul O (GPoly.mul O Den Den) (g i))) }

/-- **The system solver at a primitive level** `t′ = η`: the denominator and a basis of the
polynomial numerators with their constant coefficients (`none`: outside the handled cases). -/
def primSysC (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m))) :
    Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))) :=
  let O := MO Fc ks m
  let cst := mcst Fc ks m
  if !(isMonicC O q && isMonicC O h) then none else
  match indBound2 Fc ks m (degG O q) n q (DzLC O η O.zero q) A0 with
  | none => none
  | some B =>
    let W := wSys Fc ks m η n A0 q h G0 B
    let δ := degG O W.a
    let la := O.inv (leadG O W.a)
    let PA : Fin n → Fin n → LC m := fun i j ↦ if i = j then la else O.zero
    let β : Fin n → Fin n → LC m := vecM fun i ↦ vecM fun j ↦
      O.mul la ((W.BW i j).getD (δ - 1) O.zero)
    let okB := (List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim O (W.BW i j)).length ≤ δ)
    if !okB then none else
    match specBound2 Fc ks m n lim η β with
    | none => none
    | some Bs =>
      let Ncl := (W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0
      let N' := max Bs (Ncl - (δ - 1))
      some (W.Den, polySysC O η O.zero (fun i j ↦ if i = j then W.a else []) W.BW cst W.Cl δ false
        PA PA (fun _ ws ↦ vecLim O cst lim ws) (mrel Fc ks m) (N' + 1))

section SemG

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma toPoly_sysPowC (p : GPoly α) : ∀ N, GPoly.toPoly M (sysPowC O p N) = GPoly.toPoly M p ^ N
  | 0 => by simp [sysPowC, M.sem_one]
  | N + 1 => by rw [sysPowC, GPoly.toPoly_mul, toPoly_sysPowC p N, pow_succ, mul_comm]

lemma isMonicC_spec (p : GPoly α) (hp : isMonicC O p = true) : (GPoly.toPoly M p).Monic := by
  simp only [isMonicC, Bool.and_eq_true, Bool.not_eq_true'] at hp
  have hne : GPoly.toPoly M p ≠ 0 := fun h0 ↦ by
    rw [← GPoly.isZero_iff M] at h0; rw [h0] at hp; exact absurd hp.1 (by simp)
  have hl := (M.isZero_iff _).mp hp.2
  rw [M.sem_add, M.sem_neg, M.sem_one, add_neg_eq_zero] at hl
  rw [Monic, GPoly.leadingCoeff_toPoly M hne]
  exact hl

end SemG

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma toPoly_tX (m : ℕ) (h : T.Tr m) : GPoly.toPoly (T.MP m h) (tX Fc ks m) = X := by
  simp [tX, (T.MP m h).sem_zero, (T.MP m h).sem_one]

variable (m : ℕ) (h : T.Tr m) (η : LC m) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m))
  (q hh : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m))) (B : ℕ)

lemma wSys_Den : GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).Den =
    GPoly.toPoly (T.MP m h) hh * GPoly.toPoly (T.MP m h) q ^ B := by
  simp [wSys, toPoly_sysPowC]

lemma wSys_a : GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).a =
    X * (GPoly.toPoly (T.MP m h) q * (GPoly.toPoly (T.MP m h) hh *
      GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).Den)) := by
  simp only [wSys, GPoly.toPoly_mul, T.toPoly_tX m h]

lemma wSys_BW (i j : Fin n) : semPM (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).BW i j =
    X * (GPoly.toPoly (T.MP m h) hh * GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).Den *
      semMat (T.MP m h) A0 i j - if i = j then GPoly.toPoly (T.MP m h) q *
        (GPoly.toPoly (T.MP m h) hh * DzL ((T.MP m h).sem η) 0
          (GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).Den)) else 0) := by
  simp only [semPM, WSys.BW, wSys, listFn_matL, GPoly.toPoly_mul, GPoly.toPoly_sub,
    T.toPoly_tX m h, semMat, Matrix.of_apply]
  split_ifs
  · simp only [GPoly.toPoly_mul, toPoly_DzLC, (T.MP m h).sem_zero]
  · simp

lemma wSys_Cl (l : ℕ) (i : Fin n) :
    ((wSys Fc ks m η n A0 q hh G0 B).Cl.map (semV (T.MP m h))).getD l 0 i =
      X * (GPoly.toPoly (T.MP m h) q * (GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).Den ^ 2 *
        GPoly.toPoly (T.MP m h) ((G0.getD l fun _ ↦ []) i))) := by
  rw [getD_semCl]
  by_cases hl : l < G0.length
  · simp only [WSys.Cl, wSys, List.map_map]
    rw [NestTower.getD_map' _ _ (fun _ ↦ []) _ hl]
    simp only [Function.comp_apply, semV, listFn_matL, GPoly.toPoly_mul, T.toPoly_tX m h]
    ring
  · rw [List.getD_eq_default _ _ (by simp [WSys.Cl, wSys]; omega), List.getD_eq_default _ _ (by omega)]
    simp [semV]

/-- `A_W W′ + B_W W` is `t` times the cleared equation. -/
lemma wSys_LopV (W : Fin n → (T.F m)[X]) (i : Fin n) :
    LopV ((T.MP m h).sem η) 0
      (semPM (T.MP m h) fun i j ↦ if i = j then (wSys Fc ks m η n A0 q hh G0 B).a else [])
      (semPM (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).BW) W i =
    X * (GPoly.toPoly (T.MP m h) q * GPoly.toPoly (T.MP m h) hh *
      (GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).Den * DzL ((T.MP m h).sem η) 0 (W i) -
        DzL ((T.MP m h).sem η) 0 (GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).Den) * W i) +
      GPoly.toPoly (T.MP m h) hh * GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).Den *
        ∑ j, semMat (T.MP m h) A0 i j * W j) := by
  simp only [LopV, T.wSys_BW m h η n A0 q hh G0 B, Finset.sum_add_distrib]
  have e1 : ∑ j, semPM (T.MP m h) (fun i j ↦ if i = j then (wSys Fc ks m η n A0 q hh G0 B).a else [])
      i j * DzL ((T.MP m h).sem η) 0 (W j) =
      GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).a * DzL ((T.MP m h).sem η) 0 (W i) := by
    simp only [semPM]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [if_neg (Ne.symm hj)]; simp) (by simp), if_pos rfl]
  rw [e1, T.wSys_a m h η n A0 q hh G0 B]
  set Q := GPoly.toPoly (T.MP m h) q * (GPoly.toPoly (T.MP m h) hh *
    DzL ((T.MP m h).sem η) 0 (GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).Den))
  set hD := GPoly.toPoly (T.MP m h) hh * GPoly.toPoly (T.MP m h) (wSys Fc ks m η n A0 q hh G0 B).Den
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


/-- `mrel` is a relation finder in the sense of `RelSpec`. -/
theorem mrel_relSpec : RelSpec (algebraMap Cc (T.F m)) (T.MP m h) (mrel Fc ks m) := by
  refine ⟨fun vs w hw ↦ ?_, fun vs c hc h0 ↦ ?_⟩
  · have := T.mrel_sound m h vs w hw
    rw [Tower.NestP.zipWith_sum_getD (fun (c : Cc) (v : LC m) ↦ algebraMap Cc (T.F m) c *
      (T.MP m h).sem v) 0 (MO Fc ks m).zero (fun _ ↦ by simp)] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hj), T.algebraMap_ratCast]
  · set c' := (List.range vs.length).map fun j ↦ c.getD j 0 with hc'
    have hc'D : ∀ j, c'.getD j 0 = c.getD j 0 := fun j ↦ by
      by_cases hj : j < vs.length
      · exact NestTower.getD_range_map _ _ hj
      · rw [List.getD_eq_default _ _ (by simp [hc']; omega), hc j (by omega)]
    obtain ⟨β, hβ⟩ := T.mrel_complete m h vs c' (by simp [hc']) (by
      rw [Tower.NestP.zipWith_sum_getD (fun (c : Cc) (v : LC m) ↦ algebraMap Cc (T.F m) c *
        (T.MP m h).sem v) 0 (MO Fc ks m).zero (fun _ ↦ by simp), ← h0]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hc'D])
    exact ⟨β, fun j ↦ by rw [← hc'D, hβ j]⟩

/-- **Soundness at a primitive level**: every output `(e, W)` gives the solution `W / Den` of
`Y′ + (A₀/q) Y = ∑ eₗ G₀ₗ / h`, in the cleared form `SysSol`. -/
theorem primSysC_sound (lim : List (LC m) → List (List ℚ × LC m)) (Den : GPoly (LC m))
    (out : List (List ℚ × (Fin n → GPoly (LC m))))
    (hres : primSysC Fc ks m η lim n A0 q hh G0 = some (Den, out)) :
    ∀ r ∈ out, SysSol ((T.MP m h).sem η) 0 (GPoly.toPoly (T.MP m h) q)
      (GPoly.toPoly (T.MP m h) hh) (semMat (T.MP m h) A0)
      (fun i ↦ ∑ l ∈ Finset.range G0.length, C ((r.1.getD l 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MP m h) ((G0.getD l fun _ ↦ []) i))
      (semV (T.MP m h) r.2) (GPoly.toPoly (T.MP m h) Den) := by
  unfold primSysC at hres
  simp only at hres
  split_ifs at hres with hmon
  split at hres
  · exact absurd hres (by simp)
  rename_i B hB
  split_ifs at hres with hok
  split at hres
  · exact absurd hres (by simp)
  rename_i Bs hBs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
  intro r hr
  have hs := polySysC_sound (algebraMap Cc (T.F m)) (T.MP m h) η (MO Fc ks m).zero _ _
    (mcst Fc ks m) (T.sem_mcst m h) _ _ false _ _ _ (mrel Fc ks m) (T.mrel_relSpec m h)
    (T.algebraMap_ratCast) _ r hr
  intro i
  have hi := congrFun hs i
  rw [resQV, Pi.sub_apply, Pi.zero_apply, sub_eq_zero, (T.MP m h).sem_zero,
    T.wSys_LopV m h η n A0 q hh G0 B, SqV, List.length_map] at hi
  simp only [T.wSys_Cl m h η n A0 q hh G0 B] at hi
  apply mul_left_cancel₀ (X_ne_zero : (X : (T.F m)[X]) ≠ 0)
  rw [hi, show (wSys Fc ks m η n A0 q hh G0 B).Cl.length = G0.length by simp [WSys.Cl, wSys],
    Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

include T in
lemma DzL_zero_b (w : T.F m) (P : (T.F m)[X]) : DzL w 0 P = implicitDeriv (C w) P := by
  simp [DzL]

/-- At a primitive level every irreducible polynomial is normal. -/
lemma not_dvd_DzL (hm : m < T.n) (htr : Transcendental (T.F m) (T.ts m)) (hk : ks m = .prim η)
    (p : (T.F m)[X]) (hp : Irreducible p) : ¬ p ∣ DzL ((T.MP m h).sem η) 0 p := by
  have := T.normal_prim m htr hk p hp
  rwa [T.wPoly_prim hm hk, ← T.sem_MP_F m h, ← T.DzL_zero_b m] at this

/-- **Completeness at a primitive level**: every solution `Z / d` of
`Y′ + (A₀/q) Y = ∑ cₗ G₀ₗ / h` (constants `cₗ`) is `W / Den` with `(c, W)` a constant
combination of the outputs. -/
theorem primSysC_complete (hm : m < T.n) (htr : Transcendental (T.F m) (T.ts m))
    (hk : ks m = .prim η) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h) lim) (Den : GPoly (LC m))
    (out : List (List ℚ × (Fin n → GPoly (LC m))))
    (hres : primSysC Fc ks m η lim n A0 q hh G0 = some (Den, out))
    (c : List Cc) (hc : ∀ l, G0.length ≤ l → c.getD l 0 = 0) (Z : Fin n → (T.F m)[X])
    (d : (T.F m)[X]) (hd : d ≠ 0)
    (hsol : SysSol ((T.MP m h).sem η) 0 (GPoly.toPoly (T.MP m h) q)
      (GPoly.toPoly (T.MP m h) hh) (semMat (T.MP m h) A0)
      (fun i ↦ ∑ l ∈ Finset.range G0.length, C (algebraMap Cc (T.F m) (c.getD l 0)) *
        GPoly.toPoly (T.MP m h) ((G0.getD l fun _ ↦ []) i)) Z d) :
    ∃ β : List Cc, (∀ l, c.getD l 0 = ∑ k ∈ Finset.range out.length,
        β.getD k 0 * algebraMap ℚ Cc ((out.getD k ([], fun _ ↦ [])).1.getD l 0)) ∧
      ∀ i, GPoly.toPoly (T.MP m h) Den * Z i = d * ∑ k ∈ Finset.range out.length,
        C (algebraMap Cc (T.F m) (β.getD k 0)) *
          semV (T.MP m h) (out.getD k ([], fun _ ↦ [])).2 i := by
  classical
  unfold primSysC at hres
  simp only at hres
  split_ifs at hres with hmon
  split at hres
  · exact absurd hres (by simp)
  rename_i B hB
  split_ifs at hres with hok
  split at hres
  · exact absurd hres (by simp)
  rename_i Bs hBs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
  have hall : ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim (MO Fc ks m) ((wSys Fc ks m η n A0 q hh G0 B).BW i j)).length ≤
        degG (MO Fc ks m) (wSys Fc ks m η n A0 q hh G0 B).a)) = true := by
    revert hok; cases ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim (MO Fc ks m) ((wSys Fc ks m η n A0 q hh G0 B).BW i j)).length ≤
        degG (MO Fc ks m) (wSys Fc ks m η n A0 q hh G0 B).a)) <;> simp
  have hWa := T.wSys_a m h η n A0 q hh G0 B
  have hWCl := T.wSys_Cl m h η n A0 q hh G0 B
  have hWLop := T.wSys_LopV m h η n A0 q hh G0 B
  have hWDen := T.wSys_Den m h η n A0 q hh G0 B
  set O := MO Fc ks m with hO
  set M := T.MP m h with hM
  set W := wSys Fc ks m η n A0 q hh G0 B with hW
  set ι := algebraMap Cc (T.F m) with hι
  set w := M.sem η with hw
  have hmon' : (isMonicC O q && isMonicC O hh) = true := by
    revert hmon; cases (isMonicC O q && isMonicC O hh) <;> simp
  rw [Bool.and_eq_true] at hmon'
  have hqM := isMonicC_spec M q hmon'.1
  have hhM := isMonicC_spec M hh hmon'.2
  set qs := GPoly.toPoly M q with hqs
  set hs := GPoly.toPoly M hh with hhs
  set Ds := GPoly.toPoly M W.Den with hDs
  have hDs' : Ds = hs * qs ^ B := hWDen
  -- the indicial bound
  have hind : ∀ (p : (T.F m)[X]) (e : ℕ), Irreducible p → p ∣ qs →
      p ∣ (Matrix.of fun i j ↦ semMat M A0 i j - if i = j then C (e : T.F m) * DzL w 0 qs
        else 0).det → e ≤ B := fun p e hp hpq hdet ↦
    T.indBound2_spec m h (degG O q) n q (DzLC O η O.zero q) A0 hqM (degG_eq M q).symm B hB e p hp hpq
      (by rwa [toPoly_DzLC, M.sem_zero])
  -- the denominator
  have hden := fun i ↦ sys_den_bound w 0 qs hs hhM.ne_zero (semMat M A0) _ B hind Z d hd hsol 1
    (fun p e hp hpd _ ↦ absurd hpd (T.not_dvd_DzL m h η hm htr hk p hp)) i
  choose Wv hWv using hden
  have hDZ : ∀ i, Ds * Z i = d * Wv i := fun i ↦ by rw [hDs', ← hWv i]; ring
  have hsolW : SysSol w 0 qs hs (semMat M A0) (fun i ↦ ∑ l ∈ Finset.range G0.length,
      C (ι (c.getD l 0)) * GPoly.toPoly M ((G0.getD l fun _ ↦ []) i)) Wv Ds := by
    have h1 := sysSol_scale w 0 qs hs (semMat M A0) _ Z d Ds hsol
    have e1 : (fun i ↦ Ds * Z i) = fun i ↦ d * Wv i := funext hDZ
    rw [e1, mul_comm Ds d] at h1
    exact sysSol_cancel w 0 qs hs (semMat M A0) _ Wv Ds d hd h1
  -- the `W`-system
  set AW : Fin n → Fin n → GPoly (LC m) := fun i j ↦ if i = j then W.a else [] with hAW
  set G : Fin n → (T.F m)[X] := fun i ↦ ∑ l ∈ Finset.range (W.Cl.map (semV M)).length,
    C (ι (c.getD l 0)) * (W.Cl.map (semV M)).getD l 0 i with hG
  have hClen : W.Cl.length = G0.length := by simp [hW, WSys.Cl, wSys]
  have hLop : LopV w 0 (semPM M AW) (semPM M W.BW) Wv = G := by
    funext i
    rw [hWLop Wv i, hsolW i, hG, List.length_map, hClen, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [hWCl]
    ring
  -- the leading coefficient
  set δ := degG O W.a with hδ
  have haM : (GPoly.toPoly M W.a).Monic := by
    rw [hWa]
    exact monic_X.mul (hqM.mul (hhM.mul (by rw [hDs']; exact hhM.mul (hqM.pow B))))
  have hδa : (GPoly.toPoly M W.a).natDegree = δ := (degG_eq M W.a).symm
  have hδ1 : 1 ≤ δ := by
    rw [← hδa, hWa,
      monic_X.natDegree_mul (hqM.mul (hhM.mul (by rw [hDs']; exact hhM.mul (hqM.pow B)))),
      natDegree_X]
    omega
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
  have hPAs' : ∀ i j, M.sem (PA i j) = if i = j then (1 : T.F m) else 0 := fun i j ↦
    congrFun (congrFun hPAs i) j
  have hAδ' : ∀ i j, (semPM M AW i j).coeff δ = if i = j then (1 : T.F m) else 0 := fun i j ↦
    congrFun (congrFun hAδ i) j
  -- the degrees of `B_W`
  have hBnat : ∀ i j, (semPM M W.BW i j).natDegree ≤ δ - 1 := by
    intro i j
    have hij := List.all_eq_true.mp (List.all_eq_true.mp hall i (List.mem_finRange _)) j
      (List.mem_finRange _)
    rw [decide_eq_true_eq] at hij
    by_cases htr0 : GPoly.trim O (W.BW i j) = []
    · rw [semPM, (GPoly.trim_eq_nil_iff M _).mp htr0, natDegree_zero]; exact Nat.zero_le _
    · have e : (GPoly.trim O (W.BW i j)).length = (GPoly.trim (MO Fc ks m) (W.BW i j)).length := rfl
      rw [semPM, (GPoly.natDegree_toPoly_of_trim_ne_nil M htr0).1]; omega
  have hBδ : ∀ i j, (semPM M W.BW i j).coeff δ = 0 := fun i j ↦
    coeff_eq_zero_of_natDegree_lt (by have := hBnat i j; omega)
  -- the special degrees
  set β : Fin n → Fin n → LC m := vecM fun i ↦ vecM fun j ↦
    O.mul (O.inv (leadG O W.a)) ((W.BW i j).getD (δ - 1) O.zero) with hβdef
  have hβ : (fun i j ↦ M.sem (β i j)) =
      betaM (semPM M W.BW) (fun i j ↦ M.sem (PA i j)) (δ - 1) := by
    funext i j
    rw [hPAs]
    simp only [hβdef, vecM_eq, betaM, M.sem_mul, hla, one_mul, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, semPM, coeff_toPoly_sem]
    rw [M.sem_mul, hla, one_mul]
  have hSp : ∀ D, 1 ≤ D → SpecialDeg w (betaM (semPM M W.BW) (fun i j ↦ M.sem (PA i j)) (δ - 1)) D →
      D ≤ Bs := fun D _ hD ↦ T.specBound2_spec m h lim hlim n η β Bs hBs D (by rw [hβ]; exact hD)
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
  have hdegW := fun j ↦ sys_deg_prim w (semPM M AW) (semPM M W.BW) (δ - 1)
    (fun i j ↦ by rw [Nat.sub_add_cancel hδ1]; exact hA1 i j) hBnat (fun i j ↦ M.sem (PA i j))
    (fun i l ↦ by
      rw [Nat.sub_add_cancel hδ1]
      simp only [hPAs', hAδ', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true])
    Bs Ncl hSp Wv G hGz hLop j
  -- the polynomial system
  have hmv1 : ∀ v : Fin n → T.F m, mv (fun i j ↦ if i = j then (1 : T.F m) else 0) v = v := fun v ↦ by
    funext i; simp [mv]
  have hsolres : resCV (M.sem η) (M.sem O.zero) (semPM M AW) (semPM M W.BW) (W.Cl.map (semV M)) ι c
      Wv = 0 := by
    funext i
    rw [resCV, M.sem_zero, hLop]
    simp [hG]
  obtain ⟨γ, hγc, hγW⟩ := polySysC_complete ι M η O.zero AW W.BW (mcst Fc ks m) (T.sem_mcst m h) W.Cl
    δ T.deriv_algebraMap_Cc T.algebraMap_ratCast hA1 (fun i j ↦ (hBnat i j).trans (Nat.sub_le _ _))
    false PA PA (fun _ ws ↦ vecLim O (mcst Fc ks m) lim ws) (fun h ↦ absurd h (by simp))
    (fun _ ↦ ⟨fun v ↦ by rw [hAδ, hPAs, hmv1, hmv1], fun v ↦ by rw [hAδ, hPAs, hmv1, hmv1],
      fun k ↦ ⟨0, fun z i ↦ by
        have hz0 : M.sem O.zero = 0 := M.sem_zero
        simp [hBδ, hz0, mv],
        fun wsC ↦ vecLim_spec _ M (mcst Fc ks m) (T.sem_mcst m h) lim wsC hlim
          T.deriv_algebraMap_Cc T.algebraMap_ratCast (fun y hy ↦ T.const_F y hy)⟩⟩)
    (mrel Fc ks m) (T.mrel_relSpec m h) (max Bs (Ncl - (δ - 1)))
    (fun l hl i ↦ by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro d' hd'
      exact hClc l hl i d' (by
        have : max Bs (Ncl - (δ - 1)) + δ < d' := by exact_mod_cast hd'
        omega))
    c (fun l hl ↦ hc l (by omega)) Wv hdegW hsolres
  refine ⟨γ, hγc, fun i ↦ ?_⟩
  rw [hDZ i, hγW i]

end MTower

end Curves.MT
