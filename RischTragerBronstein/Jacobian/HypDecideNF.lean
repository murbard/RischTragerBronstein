import RischTragerBronstein.Jacobian.TorsionDecideK
import RischTragerBronstein.Jacobian.NFSplitG
import RischTragerBronstein.Algebraic.EllDecideADK
import RischTragerBronstein.Algebraic.EllDecideNF
import RischTragerBronstein.Algebraic.EllDecideQ
import RischTragerBronstein.Jacobian.HypDecideGenQ

/-!
# The genus-`g` decision for `∫ A dx / (D y)` with irrational poles

* `hypDecideADK`: rational `A, D` and splitting data `(αᵢ, βᵢ)` in a field `K` with `QCoords`
  (checked: `D = lc ∏ (X − αᵢ)`), residues `A(αᵢ)/(D′(αᵢ) βᵢ)`, then `hypDecideK`.
* `hypDecideNF`: over `K = NF M`, the roots of `D` (`rootsIn`) and the square roots of `f` at them
  (`sqrtNF`), then `hypDecideADK` with the torsion oracle `torsNF`.

Every answer is correct (`hypDecideADK_spec`, `hypDecideNF_spec`).
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad

namespace Jac

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] [QCoords K]

/-- **The procedure from splitting data.** -/
def hypDecideADK (f : List ℤ) (g : ℕ) (tors : List (K × K × ℤ) → Option (Option ℕ))
    (A D : CPoly ℚ) (pts : List (K × K)) : Option Bool :=
  if (!isZero D && splitCheck D (pts.map Prod.fst)) = true then
    hypDecideK f g tors (liftK (divMod A D).1)
      (pts.map fun q ↦ (q.1, q.2, evalQK A q.1 / (evalQK (CPoly.deriv D) q.1 * q.2)))
  else none

omit [QCoords K] in
lemma validG_of_some [QCoords K] {f : List ℤ} {g : ℕ} {tors : List (K × K × ℤ) → Option (Option ℕ)}
    {B : CPoly K} {pts : List (K × K × K)} {ans : Bool} (h : hypDecideK f g tors B pts = some ans) :
    validG f pts = true := by
  by_contra hv
  rw [hypDecideK, if_neg hv] at h
  cases h

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `hypDecideADK`.** -/
theorem hypDecideADK_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {f : List ℤ} {g : ℕ} (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1)
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ))) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : K →+* Kc) (tors : List (K × K × ℤ) → Option (Option ℕ)) (htors : TorsSpec f g tors)
    (A D : CPoly ℚ) (pts : List (K × K)) (ans : Bool) (h : hypDecideADK f g tors A D pts = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold hypDecideADK at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨hz, hsp⟩ := hc
  have hD0 : toPoly D ≠ 0 := fun h0 ↦ by rw [(isZero_iff _).mpr h0] at hz; exact Bool.noConfusion hz
  have hsplit := (splitCheck_iff D hD0 _).mp hsp
  have hv := validG_of_some h
  simp only [validG, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hon, hnd⟩ := hv
  have hnd' : (pts.map Prod.fst).Nodup := by simpa [List.map_map, Function.comp_def] using hnd
  have hlc : ((lead (trim D) : ℚ) : K) ≠ 0 := by exact_mod_cast lead_trim_ne_zero hD0
  have hsum : ((pts.map fun q ↦ (q.1, q.2, evalQK A q.1 / (evalQK (CPoly.deriv D) q.1 * q.2))).map
      fun q ↦ algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum =
      ((pts.map Prod.fst).map fun α ↦ algebraMap Kc E
        (ι (evalQK A α / evalQK (CPoly.deriv D) α)) / (x - algebraMap Kc E (ι α))).sum := by
    rw [List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun q hq ↦ ?_
    have hβ := (hon _ (List.mem_map_of_mem hq)).2
    simp only [Function.comp_apply] at hβ ⊢
    congr 3
    field_simp
  rw [hypDecideK_spec hC hCall x y hx hsq hdeg hy hgen ι tors htors _ _ ans h,
    integrand_pfK hC x y hx ι A D hD0 _ hnd' _ hlc hsplit, hsum]

end Spec

section NF

open NFC

variable (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]

/-- The ordinates `β` with `β² = f(α)`. -/
noncomputable def ordsG (f : List ℤ) : List (NF M) → Option (List (NF M × NF M))
  | [] => some []
  | α :: t =>
    match sqrtNF M (evalC (curveK f) α), ordsG f t with
    | some β, some m => some ((α, β) :: m)
    | _, _ => none

/-- **The procedure over `K = NF M`** (search bound `B` for the torsion oracle). -/
noncomputable def hypDecideNF (f : List ℤ) (g : ℕ) (A D : CPoly ℚ) (B : ℕ) : Option Bool :=
  match rootsIn M (liftK D) with
  | none => none
  | some rs =>
    match ordsG M f rs.dedup with
    | some pts => hypDecideADK f g (torsNF (M := M) (M.map Rat.num) f g B) A D pts
    | none => none

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Correctness of `hypDecideNF`.** -/
theorem hypDecideNF_spec (hMZ : ∀ q ∈ M, q.den = 1) (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {f : List ℤ} {g : ℕ} (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1)
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ))) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : NF M →+* Kc) (A D : CPoly ℚ) (B : ℕ) (ans : Bool)
    (h : hypDecideNF M f g A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold hypDecideNF at h
  split at h
  · cases h
  rename_i rs _
  split at h
  swap
  · cases h
  rename_i pts _
  have hmZ : toPoly M = (toPoly (M.map Rat.num)).map (Int.castRingHom ℚ) :=
    (Kron.polyZ_map M hMZ).symm
  have hdegK : (toPoly (curveK (K := NF M) f)).natDegree = 2 * g + 1 := by
    rw [toPoly_curveK, natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective, hdeg]
  exact hypDecideADK_spec hC hCall x y hx hsq hdeg hy hgen ι _ (torsNF_spec hmZ hdegK B) A D pts
    ans h

end Spec

end NF

/-- `g` base abscissae `a ∈ ℕ` with `S(a) ≠ 0` and `p(a) ≠ 0`. -/
def baseAs (p S : CPoly ℚ) (g : ℕ) : List ℕ :=
  ((List.range (g + p.length + S.length)).filter fun a : ℕ ↦
    evalC S (a : ℚ) != 0 && evalC p (a : ℚ) != 0).take g

/-- `S ∏ (X − aᵢ)`: its splitting field also contains the square roots `√p(aᵢ)` (base points). -/
def baseS (p S : CPoly ℚ) (g : ℕ) : CPoly ℚ :=
  mul S (prodLin ((baseAs p S g).map fun a : ℕ ↦ (a : ℚ)))

/-- **The genus-`g` procedure over `ℚ`**: Hermite reduction, splitting field (of the poles and of
`g` base abscissae, with the square roots of `p` there), then `hypDecideNF` (search bound `B`). -/
noncomputable def hypDecideQ (f : List ℤ) (g : ℕ) (A D : CPoly ℚ) (B : ℕ) : Option Bool :=
  if isZero D then none
  else
    let p : CPoly ℚ := f.map (Int.castRingHom ℚ)
    let S := nbPart p D
    let dW := A.length + D.length
    let nT := A.length + 2 * D.length + S.length + f.length + 3
    match linSolve (colsG p D S dW nT) (mul [2] (mul (mul A D) S)) with
    | none => none
    | some cs =>
      match NFC.splitFieldG p (baseS p S g) with
      | none => none
      | some ⟨M, hM⟩ =>
        letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
        hypDecideNF M f g (cs.drop dW) S B

section SpecQ

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `hypDecideQ`** (algebraically closed constants). -/
theorem hypDecideQ_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {f : List ℤ} {g : ℕ} (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1)
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ))) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (B : ℕ) (ans : Bool) (h : hypDecideQ f g A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hpf : toPoly (f.map (Int.castRingHom ℚ)) = (toPoly f).map (Int.castRingHom ℚ) :=
    toPoly_map_list _ _
  have hy' : y ^ 2 = aeval x (toPoly (f.map (Int.castRingHom ℚ))) := by rw [hpf]; exact hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hne _ hsq.ne_zero
    rw [← hy]; ring
  unfold hypDecideQ at h
  split_ifs at h with hDz
  have hD : toPoly D ≠ 0 := fun h0 ↦ hDz ((isZero_iff D).mpr h0)
  simp only at h
  split at h
  · cases h
  rename_i cs hls
  split at h
  · cases h
  rename_i M hM _
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  set p : CPoly ℚ := f.map (Int.castRingHom ℚ)
  have hid := hermite_of_linSolve _ _ _ _ _ _ _ hls
  have hM0 := nbPart_ne_zero p D hD
  have e := gen_identity x y hx (toPoly p) (toPoly A) (toPoly D)
    (toPoly (cs.take (A.length + D.length))) (toPoly D)
    (toPoly (cs.drop (A.length + D.length))) (toPoly (nbPart p D)) hy' hy0
    (hne _ hD) (hne _ hD) (hne _ hM0) (by unfold LDK at hid; linear_combination toPoly D * hid)
  rw [e, hasElementaryIntegral_deriv_add_iff', div_div]
  let ι : NFC.NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NFC.NF M) (M := Kc)).toRingHom
  exact hypDecideNF_spec M (int_of_irredQ hM) hC hCall x y hx hsq hdeg hy hgen ι _ _ B ans h

end SpecQ

end Jac
