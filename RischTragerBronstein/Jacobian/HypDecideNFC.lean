import RischTragerBronstein.Jacobian.HermiteK
import RischTragerBronstein.Jacobian.TorsNFFComplete

/-!
# The genus-`g` decision for a curve over a number field

For `y² = f(x)` with `f ∈ K[x]`, `K = NF M` (squarefree of degree `2g + 1`) and `A, D ∈ K[x]`:

* `gen_identityKc`, `integrand_pfKF`: the Hermite identity and the partial fractions with
  coefficients in `K` (through an embedding `ι : K → Kc`);
* `hypDecideADKF`: splitting data `(αᵢ, βᵢ)` over `K`, residues `A(αᵢ)/(D′(αᵢ) βᵢ)`, then
  `hypDecideKF`;
* `hypDecideNFC M f g A D B`: Hermite reduction over `K` (`colsGK`, `nbPartK`), the roots of the
  non-branch part `S` in `K` (`rootsIn`), square roots of `f` there (`sqrtNF`), then
  `hypDecideADKF` with the torsion oracle `torsNFF`.

`hypDecideNFC_spec`: every answer is correct.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad

namespace Jac

section Gen

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- `A / (D y) = (W/V · y)′ + (Gn/Gd) / y` from the polynomial identity, over the constants. -/
lemma gen_identityKc (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (p A D W V Gn Gd : Kc[X])
    (hy : y ^ 2 = aeval x p) (hy0 : y ≠ 0) (hD : aeval x D ≠ 0) (hV : aeval x V ≠ 0)
    (hGd : aeval x Gd ≠ 0)
    (hid : A * 2 * V ^ 2 * Gd = D * ((2 * (derivative W * V - W * derivative V) * p +
      W * V * derivative p) * Gd + 2 * Gn * V ^ 2)) :
    aeval x A / (aeval x D * y) = (aeval x W / aeval x V * y)′ + aeval x Gn / aeval x Gd / y := by
  have hyd : y′ = aeval x (derivative p) / (2 * y) := by
    have := congrArg (fun z : E ↦ z′) hy
    simp only [pow_two, Derivation.leibniz, smul_eq_mul] at this
    rw [deriv_aeval_x x hC hx] at this
    rw [eq_div_iff (mul_ne_zero two_ne_zero hy0)]
    linear_combination this
  have h2 := congrArg (aeval x) hid
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat] at h2
  rw [Derivation.leibniz, Derivation.leibniz_div, hyd, deriv_aeval_x x hC hx,
    deriv_aeval_x x hC hx]
  simp only [smul_eq_mul]
  rw [← hy] at h2
  field_simp
  linear_combination h2

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

set_option maxHeartbeats 3200000 in
/-- **The integrand as partial fractions over the roots**, coefficients in `K`. -/
lemma integrand_pfKF (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : K →+* Kc)
    (A D : CPoly K) (hD0 : toPoly D ≠ 0) (rs : List K) (hnd : rs.Nodup) (lc : K) (hlc : lc ≠ 0)
    (hsplit : toPoly D = C lc * (rs.map fun r ↦ X - C r).prod) :
    evF ι x A / (evF ι x D * y) =
      (evF ι x (divMod A D).1 + (rs.map fun α ↦ algebraMap Kc E
        (ι (evalC A α / evalC (CPoly.deriv D) α)) / (x - algebraMap Kc E (ι α))).sum) / y := by
  classical
  set ιE : K →+* E := (algebraMap Kc E).comp ι with hιE
  have hevF : ∀ P : CPoly K, evF ι x P = ((toPoly P).map ιE).eval x := fun P ↦ by
    rw [evF, aeval_def, eval₂_map, eval_map]
  have haevF : ∀ (P : K[X]) (z : K), ιE (P.eval z) = (P.map ιE).eval (ιE z) := by
    intro P z; rw [eval_map, eval₂_hom]
  set n := rs.length
  set v : Fin n → E := fun i ↦ ιE rs[i]
  have hv : Set.InjOn v ↑(Finset.univ : Finset (Fin n)) := by
    intro i _ j _ hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp (ιE.injective hij))
  set DE := (toPoly D).map ιE
  have hDE : DE = C (ιE lc) * ∏ i : Fin n, (X - C (v i)) := by
    show (toPoly D).map ιE = _
    rw [hsplit, Polynomial.map_mul, map_C, EllAlgo.prod_map_eq_fin, Polynomial.map_prod]
    simp [v]
    left; rfl
  -- the division
  set q := (divMod A D).1
  set R := (divMod A D).2
  have hAR : toPoly A = toPoly q * toPoly D + toPoly R := divMod_spec A D
  have hRdeg := divMod_degree_lt A D hD0
  have hDn : (toPoly D).natDegree = n := by
    have h1 : DE.natDegree = (toPoly D).natDegree := natDegree_map_eq_of_injective ιE.injective _
    have h2 : DE.natDegree = n := by
      rw [hDE, natDegree_C_mul ((map_ne_zero_iff _ ιE.injective).mpr hlc),
        natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C _]
      simp
    omega
  set RE := (toPoly R).map ιE
  have hRE : RE.degree < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin, degree_map]
    calc (toPoly R).degree < (toPoly D).degree := hRdeg
      _ = n := by rw [degree_eq_natDegree hD0, hDn]
  have hxv : ∀ i ∈ (Finset.univ : Finset (Fin n)), x ≠ v i := fun i _ ↦
    sub_ne_zero.mp (x_sub_const_ne hC x hx (ι rs[i]))
  have hpf := partial_frac Finset.univ v hv (ιE lc) ((map_ne_zero_iff _ ιE.injective).mpr hlc) DE RE
    hDE hRE x hxv
  have hDx : DE.eval x ≠ 0 := by
    rw [hDE, eval_mul, eval_C, eval_prod]
    refine mul_ne_zero ((map_ne_zero_iff _ ιE.injective).mpr hlc)
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_)
    simp only [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr (hxv i (Finset.mem_univ _))
  rw [EllAlgo.sum_map_eq_fin]
  have hA : evF ι x A / evF ι x D = evF ι x q + RE.eval x / DE.eval x := by
    rw [hevF, hevF, hevF, hAR, Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul,
      add_div, mul_div_cancel_right₀ _ hDx]
  rw [← div_div, hA, hpf]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hroot : (toPoly D).eval rs[i] = 0 := by
    rw [hsplit, eval_mul, eval_list_prod]
    apply mul_eq_zero_of_right
    apply List.prod_eq_zero
    simp only [List.map_map, List.mem_map, Function.comp_apply, eval_sub, eval_X, eval_C]
    exact ⟨rs[i], List.getElem_mem _, sub_self _⟩
  have hRi : RE.eval (v i) = ιE (evalC A rs[i]) := by
    rw [evalC_eq, haevF, hAR]
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, RE]
    rw [← haevF (toPoly D), hroot, map_zero, mul_zero, zero_add]
  have hDi : (derivative DE).eval (v i) = ιE (evalC (CPoly.deriv D) rs[i]) := by
    rw [evalC_eq, haevF, toPoly_deriv, derivative_map]
  rw [hRi, hDi]
  simp only [ιE, RingHom.comp_apply, map_div₀, v]
  field_simp

end Gen

section ADK

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- **The splitting check** `D = lc ∏ (X − αᵢ)` over `K`. -/
def splitCheckK (D : CPoly K) (rs : List K) : Bool :=
  beq D (smul (lead (trim D)) (prodLin rs))

lemma splitCheckK_iff (D : CPoly K) (rs : List K) :
    splitCheckK D rs = true ↔ toPoly D = C (lead (trim D)) * (rs.map fun r ↦ X - C r).prod := by
  rw [splitCheckK, beq_iff, toPoly_smul, toPoly_prodLin]

lemma lead_trim_ne_zeroK {D : CPoly K} (hD : toPoly D ≠ 0) : lead (trim D) ≠ 0 := by
  have htr : trim D ≠ [] := fun h ↦ hD ((trim_eq_nil_iff D).mp h)
  have hl := length_trim htr
  have : lead (trim D) = (toPoly D).leadingCoeff := by
    rw [leadingCoeff, ← toPoly_trim, coeff_toPoly, lead, List.getLastD_eq_getLast? ]
    rw [List.getLast?_eq_getElem?, hl]
    simp [List.getD_eq_getElem?_getD]
  rw [this]; exact leadingCoeff_ne_zero.mpr hD

variable [QCoords K]

/-- **The procedure from splitting data**, coefficients in `K`. -/
def hypDecideADKF (f : CPoly K) (g : ℕ) (tors : List (K × K × ℤ) → Option (Option ℕ))
    (A D : CPoly K) (pts : List (K × K)) : Option Bool :=
  if (!isZero D && splitCheckK D (pts.map Prod.fst)) = true then
    hypDecideKF f g tors (divMod A D).1
      (pts.map fun q ↦ (q.1, q.2, evalC A q.1 / (evalC (CPoly.deriv D) q.1 * q.2)))
  else none

omit [QCoords K] in
lemma validGF_of_some [QCoords K] {f : CPoly K} {g : ℕ}
    {tors : List (K × K × ℤ) → Option (Option ℕ)} {B : CPoly K} {pts : List (K × K × K)}
    {ans : Bool} (h : hypDecideKF f g tors B pts = some ans) : validGF f pts = true := by
  by_contra hv
  rw [hypDecideKF, if_neg hv] at h
  cases h

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `hypDecideADKF`.** -/
theorem hypDecideADKF_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {f : CPoly K} {g : ℕ} (hsq : Squarefree (toPoly f)) (hdeg : (toPoly f).natDegree = 2 * g + 1)
    (ι : K →+* Kc) (hy : y ^ 2 = aeval x ((toPoly f).map ι)) (hgen : ∀ z : E, InHyp Kc x y z)
    (tors : List (K × K × ℤ) → Option (Option ℕ)) (htors : TorsSpecF f g tors)
    (A D : CPoly K) (pts : List (K × K)) (ans : Bool)
    (h : hypDecideADKF f g tors A D pts = some ans) :
    ans = true ↔ HasElementaryIntegral (evF ι x A / (evF ι x D * y)) := by
  unfold hypDecideADKF at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨hz, hsp⟩ := hc
  have hD0 : toPoly D ≠ 0 := fun h0 ↦ by rw [(isZero_iff _).mpr h0] at hz; exact Bool.noConfusion hz
  have hsplit := (splitCheckK_iff D _).mp hsp
  have hv := validGF_of_some h
  simp only [validGF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hon, hnd⟩ := hv
  have hnd' : (pts.map Prod.fst).Nodup := by simpa [List.map_map, Function.comp_def] using hnd
  have hsum : ((pts.map fun q ↦ (q.1, q.2, evalC A q.1 / (evalC (CPoly.deriv D) q.1 * q.2))).map
      fun q ↦ algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum =
      ((pts.map Prod.fst).map fun α ↦ algebraMap Kc E
        (ι (evalC A α / evalC (CPoly.deriv D) α)) / (x - algebraMap Kc E (ι α))).sum := by
    rw [List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun q hq ↦ ?_
    have hβ := (hon _ (List.mem_map_of_mem hq)).2
    simp only [Function.comp_apply] at hβ ⊢
    congr 3
    field_simp
  rw [hypDecideKF_spec hC hCall x y hx hsq hdeg ι hy hgen tors htors _ _ ans h,
    integrand_pfKF hC x y hx ι A D hD0 _ hnd' _ (lead_trim_ne_zeroK hD0) hsplit, hsum]

end Spec

end ADK

section NF

open NFC

variable (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]

/-- The ordinates `β` with `β² = f(α)`, `f` over `K`. -/
noncomputable def ordsGK (f : CPoly (NF M)) : List (NF M) → Option (List (NF M × NF M))
  | [] => some []
  | α :: t =>
    match sqrtNF M (evalC f α), ordsGK f t with
    | some β, some m => some ((α, β) :: m)
    | _, _ => none

/-- **The procedure for a curve over `K = NF M`** (search bound `B`). -/
noncomputable def hypDecideNFC (f : CPoly (NF M)) (g : ℕ) (A D : CPoly (NF M)) (B : ℕ) :
    Option Bool :=
  if isZero D then none
  else
    let S := nbPartK f D
    let dW := A.length + D.length
    let nT := A.length + 2 * D.length + S.length + f.length + 3
    match linSolve (colsGK f D S dW nT) (mul [2] (mul (mul A D) S)) with
    | none => none
    | some cs =>
      match rootsIn M S with
      | none => none
      | some rs =>
        match ordsGK M f rs.dedup with
        | some pts =>
          hypDecideADKF f g (torsNFF (M := M) (M.map Rat.num) f g B) (cs.drop dW) S pts
        | none => none

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 3200000 in
/-- **Correctness of `hypDecideNFC`**, for any embedding `ι : K → Kc`. -/
theorem hypDecideNFC_spec (hMZ : ∀ q ∈ M, q.den = 1) (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {f : CPoly (NF M)} {g : ℕ} (hsq : Squarefree (toPoly f))
    (hdeg : (toPoly f).natDegree = 2 * g + 1) (ι : NF M →+* Kc)
    (hy : y ^ 2 = aeval x ((toPoly f).map ι)) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly (NF M)) (B : ℕ) (ans : Bool) (h : hypDecideNFC M f g A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (evF ι x A / (evF ι x D * y)) := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : (NF M)[X], Q ≠ 0 → aeval x (Q.map ι) ≠ 0 := fun Q hQ ↦
    aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff ι.injective).mpr hQ)
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hne _ hsq.ne_zero
    rw [← hy]; ring
  unfold hypDecideNFC at h
  split_ifs at h with hDz
  have hD : toPoly D ≠ 0 := fun h0 ↦ hDz ((isZero_iff D).mpr h0)
  simp only at h
  split at h
  · cases h
  rename_i cs hls
  split at h
  · cases h
  rename_i rs hrs
  split at h
  swap
  · cases h
  rename_i pts hpts
  have hid := hermite_of_linSolveK _ _ _ _ _ _ _ hls
  set S := nbPartK f D
  have hS0 : toPoly S ≠ 0 := nbPartK_ne_zero f D hD
  have hidK := congrArg (Polynomial.map ι) hid
  unfold LDK at hidK
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_ofNat, ← derivative_map] at hidK
  have e := gen_identityKc hC x y hx ((toPoly f).map ι) ((toPoly A).map ι) ((toPoly D).map ι)
    ((toPoly (cs.take (A.length + D.length))).map ι) ((toPoly D).map ι)
    ((toPoly (cs.drop (A.length + D.length))).map ι) ((toPoly S).map ι) hy hy0 (hne _ hD)
    (hne _ hD) (hne _ hS0) (by linear_combination ((toPoly D).map ι) * hidK)
  rw [evF, evF, e, hasElementaryIntegral_deriv_add_iff', div_div]
  have hmZ : toPoly M = (toPoly (M.map Rat.num)).map (Int.castRingHom ℚ) :=
    (Kron.polyZ_map M hMZ).symm
  exact hypDecideADKF_spec hC hCall x y hx hsq hdeg ι hy hgen _ (torsNFF_spec hmZ hdeg B) _ _ pts
    ans h

end Spec

end NF

end Jac
