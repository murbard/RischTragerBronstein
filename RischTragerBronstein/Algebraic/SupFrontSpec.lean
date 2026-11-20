import RischTragerBronstein.Algebraic.SupFront

/-!
# Correctness of the superelliptic front end
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac

namespace Sup

section Poly

variable {F : Type*} [Field F] [DecidableEq F]

lemma toPoly_foldr_add (l : List (CPoly F)) :
    toPoly (l.foldr add []) = (l.map toPoly).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- **The partial fractions identity.** -/
lemma pfSplit_spec (f S : CPoly F) {m : ℕ} (a : Fin m → F) (T : CPoly F) {cs : List F}
    {B B₁ : CPoly F} (h : pfSplit f S a T = some (cs, B, B₁)) :
    ∃ Si : Fin m → F[X], (∀ i, toPoly S = (X - Polynomial.C (a i)) * Si i) ∧
      toPoly T = toPoly f * ∑ i : Fin m, Polynomial.C (cs.getD (i : ℕ) 0) * Si i +
        toPoly S * (toPoly f * toPoly B + toPoly B₁) := by
  unfold pfSplit at h
  simp only at h
  split_ifs at h with h1 h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hcs, hB, hB₁⟩ := h
  have hgetD : ∀ i : Fin m, cs.getD (i : ℕ) 0 = pfRes f S T a i := fun i ↦ by
    rw [← hcs, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  refine ⟨fun i ↦ toPoly (divMod S (linC (a i))).1, fun i ↦ ?_, ?_⟩
  · have hz : isZero (divMod S (linC (a i))).2 = true :=
      List.all_eq_true.mp h1 _ (List.mem_finRange i)
    have := divMod_spec S (linC (a i))
    rw [(isZero_iff _).mp hz, add_zero, toPoly_linC] at this
    rw [this]; ring
  · set R := sub T (mul f (((List.finRange m).map fun i ↦
      smul (pfRes f S T a i) (divMod S (linC (a i))).1).foldr add [])) with hR_def
    have hR := divMod_spec R S
    rw [(isZero_iff _).mp h2, add_zero] at hR
    have hQ := divMod_spec (divMod R S).1 f
    rw [hB, hB₁] at hQ
    rw [hR_def, toPoly_sub, toPoly_mul, toPoly_foldr_add, ← hR_def, hQ] at hR
    have hsum : ((((List.finRange m).map fun i ↦ smul (pfRes f S T a i)
        (divMod S (linC (a i))).1).map toPoly).sum) =
        ∑ i : Fin m, Polynomial.C (cs.getD (i : ℕ) 0) * toPoly (divMod S (linC (a i))).1 := by
      rw [List.map_map, ← Fin.sum_univ_def]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [Function.comp_apply, toPoly_smul, hgetD]
    rw [hsum] at hR
    linear_combination hR

/-- **One component.** -/
lemma compData_spec (f D S : CPoly F) (n j : ℕ) (Aj : CPoly F) {m : ℕ} (a : Fin m → F)
    {W : CPoly F} {cs : List F} {B B₁ : CPoly F}
    (h : compData f D S n j Aj a = some (W, cs, B, B₁)) :
    ∃ T : CPoly F, toPoly (mul f Aj) * toPoly D * toPoly S =
        toPoly S * LDS ((j : F) / n) (toPoly f) (toPoly D) (toPoly W) + toPoly D ^ 2 * toPoly T ∧
      ∃ Si : Fin m → F[X], (∀ i, toPoly S = (X - Polynomial.C (a i)) * Si i) ∧
        toPoly T = toPoly f * ∑ i : Fin m, Polynomial.C (cs.getD (i : ℕ) 0) * Si i +
          toPoly S * (toPoly f * toPoly B + toPoly B₁) := by
  unfold compData at h
  simp only at h
  split at h
  · rename_i cs0 hcs0
    obtain ⟨r, hr, hre⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hre
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hre
    refine ⟨cs0.drop D.length, ?_, pfSplit_spec f S a _ (by rw [hr])⟩
    have := hermiteS_of_linSolve ((j : F) / n) f (mul f Aj) D S _ _ cs0 hcs0
    exact this
  · cases h

end Poly

section Field

open Differential

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 1600000 in
/-- **One component in the differential field**:
`Aⱼ yʲ/D = (W yʲ/D)′ + (B + B₁/f + ∑ cᵢ/(x − aᵢ)) yʲ`. -/
lemma component_identity (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : F →+* Kc)
    (f : F[X]) {n : ℕ} (hn : 0 < n) (hy0 : y ≠ 0) (hy : y ^ n = aeval x (f.map ι)) (j : ℕ)
    (Aj D S W T B B₁ : F[X]) {m : ℕ} (a : Fin m → F) (c : Fin m → F) (Si : Fin m → F[X])
    (hD : aeval x (D.map ι) ≠ 0) (hS : aeval x (S.map ι) ≠ 0) (hf : aeval x (f.map ι) ≠ 0)
    (hxa : ∀ i, x - algebraMap Kc E (ι (a i)) ≠ 0)
    (h1 : f * Aj * D * S = S * LDS ((j : F) / n) f D W + D ^ 2 * T)
    (h2 : ∀ i, S = (X - Polynomial.C (a i)) * Si i)
    (h3 : T = f * ∑ i, Polynomial.C (c i) * Si i + S * (f * B + B₁)) :
    aeval x (Aj.map ι) / aeval x (D.map ι) * y ^ j =
      (aeval x (W.map ι) / aeval x (D.map ι) * y ^ j)′ +
        (aeval x (B.map ι) + aeval x (B₁.map ι) / aeval x (f.map ι) +
          ∑ i, algebraMap Kc E (ι (c i)) / (x - algebraMap Kc E (ι (a i)))) * y ^ j := by
  set ev : F[X] →+* E := (aeval x : Kc[X] →ₐ[Kc] E).toRingHom.comp (mapRingHom ι) with hev
  have hevP : ∀ P : F[X], ev P = aeval x (P.map ι) := fun P ↦ rfl
  have hevC : ∀ c : F, ev (Polynomial.C c) = algebraMap Kc E (ι c) := fun c ↦ by
    simp [hev]
  have hevX : ev X = x := by simp [hev]
  have hder : ∀ P : F[X], (ev P)′ = ev (derivative P) := fun P ↦ by
    rw [hevP, hevP, deriv_aeval_x x hC hx, derivative_map]
  have hy' := deriv_y_pow hC x y hx ι f hn hy0 hy j
  -- the three identities in `E`
  have e1 := congrArg ev h1
  have e3 := congrArg ev h3
  simp only [map_add, map_mul, map_pow, map_sum, hevC, LDS, map_sub] at e1 e3
  simp only [← hder] at e1
  have e2 : ∀ i, ev S = (x - algebraMap Kc E (ι (a i))) * ev (Si i) := fun i ↦ by
    have := congrArg ev (h2 i); simpa [map_mul, map_sub, hevX, hevC] using this
  simp only [← hevP] at hD hS hf ⊢
  -- the derivative
  have hderW : (ev W / ev D * y ^ j)′ * ev f =
      ((ev W / ev D)′ * ev f + ((j : E) / n) * (ev W / ev D) * (ev f)′) * y ^ j := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have : ev f * (y ^ j)′ = ((j : E) / n) * (ev f)′ * y ^ j := by
      rw [hder, hevP, hevP, ← derivative_map]; exact hy'
    linear_combination (ev W / ev D) * this
  have hderWD : (ev W / ev D)′ = ((ev W)′ * ev D - ev W * (ev D)′) / ev D ^ 2 := by
    rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul]; ring
  have hμ : algebraMap Kc E (ι ((j : F) / n)) = (j : E) / n := by simp
  rw [hμ] at e1
  -- the partial fractions
  have hpf : ev T / (ev f * ev S) = ∑ i, algebraMap Kc E (ι (c i)) / (x - algebraMap Kc E (ι (a i))) +
      (ev B + ev B₁ / ev f) := by
    rw [e3, add_div]
    congr 1
    · rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hSi : ev (Si i) ≠ 0 := fun h0 ↦ hS (by rw [e2 i, h0, mul_zero])
      rw [e2 i]
      field_simp
    · field_simp
  apply mul_right_cancel₀ hf
  rw [add_mul, hderW, hderWD]
  have key : ev Aj / ev D = (((ev W)′ * ev D - ev W * (ev D)′) / ev D ^ 2 * ev f +
      (j : E) / n * (ev W / ev D) * (ev f)′) / ev f + ev T / (ev f * ev S) := by
    field_simp
    linear_combination e1
  rw [key, hpf]
  field_simp
  ring

end Field

section Glue

open Differential IntermediateField

universe u

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma evalE_toB_sum (ι : F →+* Kc) (x y : E) : ∀ L : BPoly F,
    evalE ι x y (toB L) = ∑ k ∈ Finset.range L.length,
      aeval x ((toPoly (L.getD k [])).map ι) * y ^ k
  | [] => by simp
  | c :: L => by
    rw [evalE_cons, evalE_toB_sum ι x y L, List.length_cons, Finset.sum_range_succ',
      Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring

/-- Rational functions of `x` (plus a derivative) have elementary integrals in every elementary
extension. -/
lemma hasElementaryIntegralIn_ratKc (hC : ∀ c : Kc, c′ = 0) (x : E) (hx : x′ = 1) (P Q : Kc[X])
    (hQ : Q ≠ 0) (w : E) : HasElementaryIntegralIn (w′ + aeval x P / aeval x Q) := by
  intro E' _ _ _ _ _
  letI : Algebra Kc E' := ((algebraMap E E').comp (algebraMap Kc E)).toAlgebra
  haveI : IsScalarTower Kc E E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : DifferentialAlgebra Kc E' := ⟨fun c ↦ by
    rw [IsScalarTower.algebraMap_apply Kc E E', deriv_algebraMap, deriv_algebraMap,
      ← IsScalarTower.algebraMap_apply]⟩
  have hx' : (algebraMap E E' x)′ = 1 := by rw [deriv_algebraMap, hx, map_one]
  have := hasElementaryIntegral_rational_in (R := Kc) hC (algebraMap E E' x) hx' P Q hQ
    (algebraMap E E' w)
  have e : ∀ P : Kc[X], algebraMap E E' (aeval x P) = aeval (algebraMap E E' x) P := fun P ↦
    (aeval_algebraMap_apply E' x P).symm
  rw [map_add, map_div₀, e, e, ← deriv_algebraMap]
  exact this

end Glue

section Glue2

open Differential IntermediateField

universe u

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 4000000 in
/-- **Correctness of the superelliptic front end**: given a correct torsion oracle, every answer
is correct — `some true` iff `∫ ∑_{j<n} (Aⱼ/D) yʲ dx` is elementary. -/
theorem superFront_spec (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : F →+* Kc)
    (f : CPoly F) {n : ℕ} (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hdeg : (toPoly f).natDegree = f.length - 1) (hpd : 0 < f.length - 1)
    (hcop : Nat.Coprime n (f.length - 1)) (hy : y ^ n = aeval x ((toPoly f).map ι))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (tors : List (F × F × ℕ) → Option (Option ℕ)) (htors : TorsSpecN f n tors)
    (A : List (CPoly F)) (D : CPoly F) (hD : toPoly D ≠ 0) {m : ℕ} (a b : Fin m → F)
    (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0) (hbf : ∀ i, b i ^ n = (toPoly f).eval (a i))
    (ans : Bool) (h : superFront f n ζ tors A D a b = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map ι) / aeval x ((toPoly D).map ι) * y ^ j) := by
  unfold superFront at h
  split_ifs at h with hall
  set dat := frontDat f n A D a with hdat
  set S := nbPartK f D with hS
  set B : BPoly F := [] :: (List.range (n - 1)).map fun k ↦ (dat k).2.2.1 with hB
  set B₁ : BPoly F := [] :: (List.range (n - 1)).map fun k ↦ (dat k).2.2.2 with hB₁
  set G : Fin m → BPoly F := fun i ↦
    [] :: (List.range (n - 1)).map fun k ↦ [(dat k).2.1.getD i 0] with hG
  have hlenB : B.length = n := by simp [hB]; omega
  have hlenB₁ : B₁.length = n := by simp [hB₁]; omega
  have hlenG : ∀ i, (G i).length = n := fun i ↦ by simp [hG]; omega
  have hspec := superLogDecide_spec hC x y hx ι f hn hsq hdeg hpd hcop hy hgen hζ tors htors B B₁
    hlenB.le hlenB₁.le (by simp [hB₁]) a b G (fun i ↦ (hlenG i).le) ha hb hbf ans h
  rw [hspec]
  -- the components
  have hcomp : ∀ k, k < n - 1 →
      compData f D S n (k + 1) (A.getD (k + 1) []) a = some (dat k) := by
    intro k hk
    have := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp this
    simp only [hdat, frontDat, ← hS, hd, Option.getD_some]
  -- transcendence facts
  have htr : Transcendental Kc x := transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hev0 : ∀ P : F[X], P ≠ 0 → aeval x (P.map ι) ≠ 0 := fun P hP h0 ↦
    htr ⟨_, (Polynomial.map_ne_zero_iff ι.injective).mpr hP, h0⟩
  have hDx := hev0 _ hD
  have hSx := hev0 _ (nbPartK_ne_zero f D hD)
  have hfx := hev0 _ hsq.ne_zero
  have hy0 : y ≠ 0 := by
    intro h0; apply hfx; rw [← hy, h0, zero_pow hn.ne']
  have hxa : ∀ i, x - algebraMap Kc E (ι (a i)) ≠ 0 := fun i h0 ↦ by
    have := congrArg (fun t : E ↦ t′) h0
    simp only [map_sub, hx, deriv_algebraMap, hC, map_zero, sub_zero] at this
    exact one_ne_zero this
  -- each component
  have hk : ∀ k ∈ Finset.range (n - 1),
      aeval x ((toPoly (A.getD (k + 1) [])).map ι) / aeval x ((toPoly D).map ι) * y ^ (k + 1) =
        (aeval x ((toPoly (dat k).1).map ι) / aeval x ((toPoly D).map ι) * y ^ (k + 1))′ +
          (aeval x ((toPoly (dat k).2.2.1).map ι) + aeval x ((toPoly (dat k).2.2.2).map ι) /
            aeval x ((toPoly f).map ι) + ∑ i : Fin m, algebraMap Kc E (ι ((dat k).2.1.getD i 0)) /
              (x - algebraMap Kc E (ι (a i)))) * y ^ (k + 1) := by
    intro k hkr
    obtain ⟨T, h1, Si, h2, h3⟩ := compData_spec f D S n (k + 1) _ a (hcomp k (Finset.mem_range.mp hkr))
    rw [toPoly_mul] at h1
    exact component_identity hC x y hx ι (toPoly f) hn hy0 hy (k + 1) _ _ _ _ _ _ _ a
      (fun i ↦ (dat k).2.1.getD i 0) Si hDx hSx hfx hxa h1 h2 h3
  -- the decomposition
  set v : E := ∑ k ∈ Finset.range (n - 1),
    aeval x ((toPoly (dat k).1).map ι) / aeval x ((toPoly D).map ι) * y ^ (k + 1) with hv
  set r : E := aeval x ((toPoly (A.getD 0 [])).map ι) / aeval x ((toPoly D).map ι) with hr
  have hget : ∀ {β : Type _} (g : ℕ → β) (d : β) (k : ℕ), k < n - 1 →
      ((List.range (n - 1)).map g).getD k d = g k := fun g d k hk ↦ by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  have hsum1 : ∀ (g : ℕ → CPoly F), evalE ι x y (toB ([] :: (List.range (n - 1)).map g)) =
      ∑ k ∈ Finset.range (n - 1), aeval x ((toPoly (g k)).map ι) * y ^ (k + 1) := by
    intro g
    rw [evalE_toB_sum, List.length_cons, List.length_map, List.length_range,
      Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one]
    rw [show toPoly ([] : CPoly F) = 0 from rfl, Polynomial.map_zero, map_zero, add_zero]
    exact Finset.sum_congr rfl fun k hk ↦ by rw [hget g [] k (Finset.mem_range.mp hk)]
  have hEG : ∀ i : Fin m, evalE ι x y (toB (G i)) =
      ∑ k ∈ Finset.range (n - 1), algebraMap Kc E (ι ((dat k).2.1.getD i 0)) * y ^ (k + 1) := by
    intro i
    rw [hG, hsum1]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp [CPoly.toPoly]
  set v : E := ∑ k ∈ Finset.range (n - 1),
    aeval x ((toPoly (dat k).1).map ι) / aeval x ((toPoly D).map ι) * y ^ (k + 1) with hv
  set r : E := aeval x ((toPoly (A.getD 0 [])).map ι) / aeval x ((toPoly D).map ι) with hr
  have hdecomp : (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map ι) / aeval x ((toPoly D).map ι) * y ^ j) =
      integrandE ι x y f B B₁ a G + (v′ + r) := by
    have e0 : (∑ j ∈ Finset.range n,
        aeval x ((toPoly (A.getD j [])).map ι) / aeval x ((toPoly D).map ι) * y ^ j) =
        (∑ k ∈ Finset.range (n - 1), aeval x ((toPoly (A.getD (k + 1) [])).map ι) /
          aeval x ((toPoly D).map ι) * y ^ (k + 1)) + r := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [Finset.sum_range_succ', pow_zero, mul_one, Nat.add_sub_cancel]
    rw [e0, Finset.sum_congr rfl hk, integrandE, hB, hB₁, hsum1, hsum1]
    simp only [hEG, hv, map_sum, Finset.sum_add_distrib]
    have e1 : (∑ k ∈ Finset.range (n - 1), aeval x ((toPoly (dat k).2.2.2).map ι) * y ^ (k + 1)) /
        exC ι x f = ∑ k ∈ Finset.range (n - 1), aeval x ((toPoly (dat k).2.2.2).map ι) /
          aeval x ((toPoly f).map ι) * y ^ (k + 1) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [exC]; ring
    have e2 : (∑ i : Fin m, (∑ k ∈ Finset.range (n - 1),
        algebraMap Kc E (ι ((dat k).2.1.getD i 0)) * y ^ (k + 1)) /
          (x - algebraMap Kc E (ι (a i)))) = ∑ k ∈ Finset.range (n - 1),
        (∑ i : Fin m, algebraMap Kc E (ι ((dat k).2.1.getD i 0)) /
          (x - algebraMap Kc E (ι (a i)))) * y ^ (k + 1) := by
      simp only [Finset.sum_div, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
    rw [e1, e2]
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  -- elementary integrals
  have hin : HasElementaryIntegralIn (v′ + r) := hasElementaryIntegralIn_ratKc hC x hx _ _
    ((Polynomial.map_ne_zero_iff ι.injective).mpr hD) v
  rw [hdecomp]
  constructor
  · intro hg; exact hg.add_in hin
  · intro hh
    have := hh.sub_in hin
    rwa [add_sub_cancel_right] at this

end Glue2


end Sup
