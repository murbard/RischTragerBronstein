import RischTragerBronstein.Jacobian.HypDecideR
import RischTragerBronstein.Algebraic.EllDecideK

/-!
# The genus-`g` decision with poles and residues in a number field

`hypDecideK f g tors B pts` decides `∫ (B(x) + ∑ rᵢ βᵢ/(x − αᵢ)) dx / y` for `y² = f(x)`
(`f ∈ ℤ[x]` squarefree of degree `2g + 1`), with points `(αᵢ, βᵢ)` and residues `rᵢ` in a field `K`
with a computable `ℚ`-basis (`QCoords`, e.g. a number field `NF M`). As in `EllQuad.ellDecideK`,
the residues are split along the basis; the `j`-th component has integer multiplicities, and its
torsion is decided by an oracle `tors` (specified by `TorsSpec`; realised over number fields by
reduction at two primes). Non-torsion of one component means non-elementary (Abel's direction
with `Λ` extending the `j`-th coordinate); otherwise `principalC` and `certCheck` remove each
logarithmic component and `hypRed` decides the remainder (`hypDecideK_spec`).
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad

namespace Jac

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- The curve over `K`. -/
def curveK (f : List ℤ) : CPoly K := f.map (Int.castRingHom K)

lemma toPoly_curveK (f : List ℤ) : toPoly (curveK (K := K) f) =
    ((toPoly f).map (Int.castRingHom ℚ)).map (algebraMap ℚ K) := by
  rw [curveK, toPoly_map_list, Polynomial.map_map]; congr 1; exact RingHom.ext_int _ _

/-- A torsion oracle for divisors `∑ |zᵢ| (αᵢ, sign zᵢ βᵢ)`: `some (some n)` with `n Γ`
principal, `some none` if not torsion, `none` if it cannot tell. -/
def TorsSpec (f : List ℤ) (g : ℕ) (tors : List (K × K × ℤ) → Option (Option ℕ)) : Prop :=
  ∀ l : List (K × K × ℤ), (∀ q ∈ l, (toPoly (curveK (K := K) f)).eval q.1 = q.2.1 ^ 2 ∧
    q.2.1 ≠ 0 ∧ q.2.2 ≠ 0) → (l.map Prod.fst).Nodup →
    (∀ n, tors l = some (some n) → 1 ≤ n ∧
      PrincipalMul (toPoly (curveK (K := K) f)) g (ptsQ l 1) n) ∧
    (tors l = some none → ∀ n, 1 ≤ n →
      ¬ PrincipalMul (toPoly (curveK (K := K) f)) g (ptsQ l 1) n)

/-- Validity of the data. -/
def validG (f : List ℤ) (pts : List (K × K × K)) : Bool :=
  pts.all (fun q ↦ decide (q.2.1 * q.2.1 = evalC (curveK f) q.1 ∧ q.2.1 ≠ 0)) &&
    decide (pts.map Prod.fst).Nodup

/-- The certificate for one component. -/
def partCertG (f : List ℤ) (g : ℕ) (B : CPoly K) (L : ℕ) (l : List (K × K × ℤ)) (n : ℕ) :
    Option (CPoly K) :=
  let Γ := ptsQ l 1
  let N := n * edeg Γ
  match principalC (curveK f) (escale n Γ) (boundA N) (boundB g N) with
  | some jc =>
    let AB := ((jc.2.set jc.1 1).take (boundA N), (jc.2.set jc.1 1).drop (boundA N))
    let cc : K := 1 / ((n : K) * (L : K))
    if certCheck (curveK f) AB (fracG B L l) cc then some (certR (curveK f) AB (fracG B L l) cc)
    else none
  | none => none

variable [QCoords K]

open QCoords

/-- The `j`-th component with its zero multiplicities removed. -/
def compPts (j : Fin (dim K)) (pts : List (K × K × K)) : List (K × K × ℤ) :=
  (PjK j pts).filter fun q ↦ q.2.2 ≠ 0

/-- The certificates of the components `js`. -/
def certsG (f : List ℤ) (g : ℕ) (tors : List (K × K × ℤ) → Option (Option ℕ)) (pts : List (K × K × K)) :
    List (Fin (dim K)) → Option (List (Fin (dim K) × CPoly K))
  | [] => some []
  | j :: t =>
    match tors (compPts j pts) with
    | some (some n) =>
      match partCertG f g [] (denLK j pts) (compPts j pts) n, certsG f g tors pts t with
      | some R, some Rs => some ((j, R) :: Rs)
      | _, _ => none
    | _ => none

/-- **The procedure** (`none`: invalid data, or the oracle cannot tell). -/
def hypDecideK (f : List ℤ) (g : ℕ) (tors : List (K × K × ℤ) → Option (Option ℕ)) (B : CPoly K)
    (pts : List (K × K × K)) : Option Bool :=
  if validG f pts then
    if (List.finRange (dim K)).any fun j ↦ (tors (compPts j pts)).isNone then none
    else if (List.finRange (dim K)).any fun j ↦ tors (compPts j pts) == some none then some false
    else
      match certsG f g tors pts (List.finRange (dim K)) with
      | some Rs => some (isZero (hypRed (curveK f) (add B (sumBK Rs))).2)
      | none => none
  else none

/-- A `ℚ`-linear functional on `K` extends to any field containing `K`. -/
lemma exists_extend_functional {Kc : Type*} [Field Kc] [CharZero Kc] (ι : K →+* Kc)
    (ℓ : K →ₗ[ℚ] ℚ) : ∃ Λ : Kc →ₗ[ℚ] ℚ, ∀ k, Λ (ι k) = ℓ k := by
  let ιL : K →ₗ[ℚ] Kc := ι.toRatAlgHom.toLinearMap
  have hinj : Function.Injective ιL := ι.injective
  let e := LinearEquiv.ofInjective ιL hinj
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend (ℓ.comp e.symm.toLinearMap)
  refine ⟨Λ, fun k ↦ ?_⟩
  have := congrArg (fun F : LinearMap.range ιL →ₗ[ℚ] ℚ ↦ F (e k)) hΛ
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    Submodule.subtype_apply] at this
  rw [← this]
  rfl

/-! ### Completeness -/

omit [QCoords K] in
lemma escale_ptsQ (l : List (K × K × ℤ)) (n : ℕ) : escale n (ptsQ l 1) = ptsQ l n := by
  simp [escale, ptsQ, Function.comp_def]

omit [QCoords K] in
/-- A torsion component always has a certificate. -/
lemma partCertG_ne_none {f : List ℤ} {g : ℕ}
    (hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1)
    (L : ℕ) (hL : L ≠ 0) (l : List (K × K × ℤ))
    (hon : ∀ q ∈ l, (toPoly (curveK (K := K) f)).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0 ∧ q.2.2 ≠ 0)
    (hnd : (l.map Prod.fst).Nodup) (n : ℕ) (hn1 : 1 ≤ n)
    (hn : PrincipalMul (toPoly (curveK (K := K) f)) g (ptsQ l 1) n) :
    partCertG f g [] L l n ≠ none := by
  have hpd : (toPoly (curveK (K := K) f)).natDegree = 2 * g + 1 := by
    rw [toPoly_curveK, natDegree_map_eq_of_injective (algebraMap ℚ K).injective, hdeg]
  have hΓ : ∀ m, ∀ q ∈ escale m (ptsQ l 1), 2 * q.2.1 ≠ 0 ∧
      q.2.1 ^ 2 = (toPoly (curveK (K := K) f)).eval q.1 := by
    intro m q hq
    rw [escale_ptsQ] at hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
    obtain ⟨h1, h2, h3⟩ := hon t ht
    have hs : ((t.2.2.sign : ℤ) : K) ^ 2 = 1 := by
      rcases lt_trichotomy t.2.2 0 with h | h | h
      · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
      · exact absurd h h3
      · rw [Int.sign_eq_one_of_pos h]; norm_num
    refine ⟨mul_ne_zero two_ne_zero (mul_ne_zero (fun h0 ↦ by rw [h0] at hs; norm_num at hs) h2),
      ?_⟩
    simp only
    rw [mul_pow, hs, one_mul, h1]
  have hsome := (principalMul_iff_principalC (curveK f) g _ hΓ n).mp hn
  obtain ⟨jc, hjc⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hψ0, hdA, hdB, hvan⟩ := principalC_sound_take (curveK f) _ _ _ (hΓ n) hjc
  unfold partCertG
  dsimp only
  rw [hjc]
  dsimp only
  rw [if_pos]
  · simp
  apply certCheck_ok_odd (curveK f) hpd l (fun q hq ↦ ⟨(hon q hq).1, (hon q hq).2.1⟩) hnd L hL n hn1
  · by_contra hc
    push_neg at hc
    exact hψ0 (Prod.ext hc.1 hc.2)
  · have := poleLE_of_degree_lt (g := g)
      (ψ := (toPoly ((jc.2.set jc.1 1).take (boundA (n * edeg (ptsQ l 1)))),
        toPoly ((jc.2.set jc.1 1).drop (boundA (n * edeg (ptsQ l 1)))))) hdA hdB
    rw [show ((ptsQ l n).map fun q ↦ q.2.2).sum = n * edeg (ptsQ l 1) by
      rw [← edeg_escale, escale_ptsQ]; rfl]
    exact this
  · intro q hq
    rw [← escale_ptsQ] at hq
    obtain ⟨h1, h2⟩ := hΓ n q hq
    exact locVal_dvd_of_vanishAt _ _ _ q (fun h0 ↦ h1 (by rw [h0, mul_zero])) h2.symm (hvan q hq)

lemma certsG_ne_none {f : List ℤ} {g : ℕ}
    (hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1)
    (tors : List (K × K × ℤ) → Option (Option ℕ)) (htors : TorsSpec f g tors) (pts : List (K × K × K))
    (hon : ∀ q ∈ pts, q.2.1 * q.2.1 = evalC (curveK f) q.1 ∧ q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) :
    ∀ js : List (Fin (dim K)), (∀ j ∈ js, ∃ n, tors (compPts j pts) = some (some n)) →
      certsG f g tors pts js ≠ none
  | [], _ => by simp [certsG]
  | j :: t, ht => by
    have hlon : ∀ q ∈ compPts j pts, (toPoly (curveK (K := K) f)).eval q.1 = q.2.1 ^ 2 ∧
        q.2.1 ≠ 0 ∧ q.2.2 ≠ 0 := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq1
      obtain ⟨h1, h2⟩ := hon q0 hq0
      exact ⟨by rw [← evalC_eq, ← h1, sq], h2, by simpa using hq2⟩
    have hlnd : ((compPts j pts).map Prod.fst).Nodup := by
      refine List.Nodup.sublist ((List.filter_sublist).map _) ?_
      rw [PjK, intPtsK, List.map_map]; exact hnd
    obtain ⟨n, hn⟩ := ht j List.mem_cons_self
    obtain ⟨hn1, hP⟩ := (htors _ hlon hlnd).1 n hn
    obtain ⟨R, hR⟩ := Option.ne_none_iff_exists'.mp
      (partCertG_ne_none hdeg (denLK j pts) (denL_ne_zero _) _ hlon hlnd n hn1 hP)
    obtain ⟨Rs, hRs⟩ := Option.ne_none_iff_exists'.mp
      (certsG_ne_none hdeg tors htors pts hon hnd t fun j' hj' ↦ ht j' (List.mem_cons_of_mem _ hj'))
    simp [certsG, hn, hR, hRs]

/-- **Completeness of `hypDecideK`**: on valid data it always answers. -/
theorem hypDecideK_ne_none {f : List ℤ} {g : ℕ}
    (hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1)
    (tors : List (K × K × ℤ) → Option (Option ℕ)) (htors : TorsSpec f g tors) (B : CPoly K)
    (pts : List (K × K × K)) (hv : validG f pts = true)
    (hans : ∀ j, (tors (compPts j pts)).isSome) :
    hypDecideK f g tors B pts ≠ none := by
  have hv' := hv
  simp only [validG, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv'
  obtain ⟨hon, hnd⟩ := hv'
  unfold hypDecideK
  rw [if_pos hv]
  split_ifs with hA hB
  · exfalso
    obtain ⟨j, -, hj⟩ := List.any_eq_true.mp hA
    have := hans j
    simp_all
  · simp
  · have ht : ∀ j ∈ List.finRange (dim K), ∃ n, tors (compPts j pts) = some (some n) := by
      intro j hj
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hans j)
      rcases o with _ | n
      · exact absurd (List.any_eq_true.mpr ⟨j, hj, by simp [ho]⟩) hB
      · exact ⟨n, ho⟩
    obtain ⟨Rs, hRs⟩ := Option.ne_none_iff_exists'.mp
      (certsG_ne_none hdeg tors htors pts hon hnd _ ht)
    rw [hRs]
    simp

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

omit [QCoords K] in
lemma curve_facts {f : List ℤ} (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (x y : E) (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ))) (ι : K →+* Kc) :
    (toPoly (curveK (K := K) f)).map ι ≠ 0 ∧
      y ^ 2 = aeval x ((toPoly (curveK (K := K) f)).map ι) := by
  have e : (toPoly (curveK (K := K) f)).map ι =
      ((toPoly f).map (Int.castRingHom ℚ)).map (algebraMap ℚ Kc) := by
    rw [toPoly_curveK, Polynomial.map_map]; congr 1; exact RingHom.ext_rat _ _
  rw [e]
  refine ⟨(Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr hsq.ne_zero, ?_⟩
  rw [aeval_map_algebraMap]; exact hy

omit [QCoords K] in
set_option maxHeartbeats 1600000 in
/-- **A certificate removes the logarithmic part of one component.** -/
lemma partCertG_spec (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) {f : List ℤ} {g : ℕ}
    (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ))) (ι : K →+* Kc) (B : CPoly K)
    (L : ℕ) (l : List (K × K × ℤ)) (n : ℕ) (R : CPoly K) (h : partCertG f g B L l n = some R) :
    ∃ w : E, HasElementaryIntegralIn w ∧
      (evF ι x B + (l.map fun q ↦ algebraMap Kc E (ι ((q.2.2 : K) / L * q.2.1)) /
        (x - algebraMap Kc E (ι q.1))).sum) / y = evF ι x R / y + w := by
  unfold partCertG at h
  dsimp only at h
  split at h
  swap
  · cases h
  rename_i jc hjc
  split_ifs at h with hchk
  simp only [Option.some.injEq] at h
  subst h
  set AB := ((jc.2.set jc.1 1).take (boundA (n * edeg (ptsQ l 1))),
    (jc.2.set jc.1 1).drop (boundA (n * edeg (ptsQ l 1))))
  set cc : K := 1 / ((n : K) * (L : K)) with hcc
  set G := fracG B L l with hGdef
  set pC : CPoly K := curveK f
  unfold certCheck at hchk
  simp only [Bool.and_eq_true, Bool.not_eq_true', certN, certM] at hchk
  obtain ⟨⟨hN, hG⟩, hbeq⟩ := hchk
  have hN' : toPoly AB.1 ^ 2 - toPoly AB.2 ^ 2 * toPoly pC ≠ 0 := by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hN; apply hN
    simp only [toPoly_sub, toPoly_mul]; linear_combination h0
  have hG' : toPoly G.2 ≠ 0 := by
    intro h0; rw [← Bool.not_eq_true, isZero_iff] at hG; exact hG h0
  have hid := (beq_iff _ _).mp hbeq
  have h2 : toPoly ([2] : CPoly K) = 2 := by
    rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
  simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_smul, toPoly_deriv, h2] at hid
  have hidK := congrArg (Polynomial.map ι) hid
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
    map_C, Polynomial.map_ofNat, ← Polynomial.derivative_map] at hidK
  have hxa : ∀ z : K, x - algebraMap Kc E (ι z) ≠ 0 := fun z ↦ x_sub_const_ne hC x hx (ι z)
  obtain ⟨hpK, hyK⟩ := curve_facts (K := K) hsq x y hy ι
  have hGK : (toPoly G.2).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hG'
  have hNK : ((toPoly AB.1).map ι) ^ 2 - ((toPoly AB.2).map ι) ^ 2 * (toPoly pC).map ι ≠ 0 := by
    rw [← Polynomial.map_pow, ← Polynomial.map_pow, ← Polynomial.map_mul, ← Polynomial.map_sub]
    exact (Polynomial.map_ne_zero_iff ι.injective).mpr hN'
  obtain ⟨w, hw, key⟩ := ell_log_decompK hC x y hx _ hpK hyK ((toPoly G.1).map ι)
    ((toPoly G.2).map ι) ((toPoly AB.1).map ι) ((toPoly AB.2).map ι)
    ((toPoly (certR pC AB G cc)).map ι) (ι cc) hGK hNK (by linear_combination hidK)
  refine ⟨w, hw, ?_⟩
  obtain ⟨-, hfr⟩ := fracG_evF ι x hxa B L l
  rw [← hGdef] at hfr
  rw [← hfr, div_div]
  exact key

omit [QCoords K] [DecidableEq K] in
lemma compK_filter (ι : K →+* Kc) (x : E) (L : ℕ) (l : List (K × K × ℤ)) :
    compK ι x L (l.filter fun q ↦ q.2.2 ≠ 0) = compK ι x L l := by
  unfold compK
  induction l with
  | nil => simp
  | cons q t ih =>
    by_cases hq : q.2.2 = 0
    · rw [List.filter_cons_of_neg (by simpa using hq), ih]
      simp [hq]
    · rw [List.filter_cons_of_pos (by simpa using hq)]
      simp only [List.map_cons, List.sum_cons, ih]

/-- **The certificates remove every component.** -/
lemma certsG_decomp (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) {f : List ℤ} {g : ℕ}
    (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ))) (ι : K →+* Kc)
    (tors : List (K × K × ℤ) → Option (Option ℕ)) (pts : List (K × K × K)) :
    ∀ (js : List (Fin (dim K))) (Rs : List (Fin (dim K) × CPoly K)),
    certsG f g tors pts js = some Rs →
    ∃ w : E, HasElementaryIntegralIn w ∧
      (js.map fun j ↦ algebraMap Kc E (ι (bvec j)) *
        compK ι x (denLK j pts) (PjK j pts)).sum / y = evF ι x (sumBK Rs) / y + w
  | [], Rs, h => by
    simp only [certsG, Option.some.injEq] at h; subst h
    exact ⟨0, hasElementaryIntegralIn_zero', by simp [sumBK, evF, CPoly.toPoly]⟩
  | j :: t, Rs, h => by
    simp only [certsG] at h
    split at h
    swap
    · cases h
    rename_i n _
    split at h
    · rename_i R Rs' h1 h2
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨w1, hw1, e1⟩ := partCertG_spec hC x y hx hsq hy ι [] _ _ _ R h1
      obtain ⟨w2, hw2, e2⟩ := certsG_decomp hC x y hx hsq hy ι tors pts t Rs' h2
      have he : evF ι x ([] : CPoly K) = 0 := by simp [evF, CPoly.toPoly]
      rw [he, zero_add] at e1
      have hc : (algebraMap Kc E (ι (bvec j)))′ = 0 := by rw [deriv_algebraMap, hC, map_zero]
      refine ⟨algebraMap Kc E (ι (bvec j)) * w1 + w2, (hw1.const_mul _ hc).add hw2, ?_⟩
      simp only [List.map_cons, List.sum_cons, sumBK, evF_add, evF_smul, add_div]
      rw [e2, mul_div_assoc]
      have e1' := e1
      rw [compPts, show ((PjK j pts).filter fun q ↦ q.2.2 ≠ 0).map (fun q ↦
          algebraMap Kc E (ι ((q.2.2 : K) / (denLK j pts : ℕ) * q.2.1)) /
          (x - algebraMap Kc E (ι q.1))) = _ from rfl] at e1'
      have hcf := compK_filter ι x (denLK j pts) (PjK j pts)
      simp only [compK] at hcf ⊢
      rw [← hcf, e1']
      ring
    · cases h

omit [QCoords K] [DecidableEq K] [CharZero K] in
lemma sum_filter_natAbs (l : List (K × K × ℤ)) :
    ((l.filter fun q ↦ q.2.2 ≠ 0).map fun q ↦ q.2.2.natAbs).sum = (l.map fun q ↦ q.2.2.natAbs).sum := by
  induction l with
  | nil => simp
  | cons q t ih =>
    by_cases hq : q.2.2 = 0 <;> simp_all [List.filter_cons]

set_option maxHeartbeats 3200000 in
/-- **Correctness of `hypDecideK`**, for any embedding `ι : K → Kc` of the coefficients. -/
theorem hypDecideK_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {f : List ℤ} {g : ℕ} (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1)
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ))) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : K →+* Kc) (tors : List (K × K × ℤ) → Option (Option ℕ)) (htors : TorsSpec f g tors)
    (B : CPoly K) (pts : List (K × K × K)) (ans : Bool)
    (h : hypDecideK f g tors B pts = some ans) :
    ans = true ↔ HasElementaryIntegral ((evF ι x B + (pts.map fun q ↦
      algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum) / y) := by
  classical
  have hL0 : ∀ j, denLK j pts ≠ 0 := fun j ↦ denL_ne_zero _
  have hd : ∀ q ∈ pts, ∀ j, (coord j q.2.2).den ∣ denLK j pts := fun q hq j ↦
    den_dvd_denL (List.mem_map_of_mem (f := fun q : K × K × K ↦ coord j q.2.2) hq)
  have hpK := toPoly_curveK (K := K) f
  unfold hypDecideK at h
  split_ifs at h with hv hN htA
  simp only [validG, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hon, hnd⟩ := hv
  · -- some component is not torsion
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.false_eq_true, false_iff]
    intro hel
    obtain ⟨j, -, hj⟩ := List.any_eq_true.mp htA
    set L := denLK j pts
    set l := compPts j pts
    have hlmem : ∀ q ∈ l, ∃ q0 ∈ pts, q = (q0.1, q0.2.1, (coord j q0.2.2 * L).num) ∧ q.2.2 ≠ 0 := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq1
      exact ⟨q0, hq0, rfl, by simpa using hq2⟩
    have hlon : ∀ q ∈ l, (toPoly (curveK (K := K) f)).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0 ∧
        q.2.2 ≠ 0 := by
      intro q hq
      obtain ⟨q0, hq0, rfl, hz⟩ := hlmem q hq
      obtain ⟨h1, h2⟩ := hon q0 hq0
      exact ⟨by rw [← evalC_eq, ← h1, sq], h2, hz⟩
    have hlnd : (l.map Prod.fst).Nodup := by
      refine List.Nodup.sublist ((List.filter_sublist).map _) ?_
      rw [PjK, intPtsK, List.map_map]; exact hnd
    have hnt := (htors l hlon hlnd).2 (by simpa using hj)

    set N := pts.length
    let a : Fin N → K := fun i ↦ pts[i].1
    let b : Fin N → K := fun i ↦ pts[i].2.1
    let z : Fin N → ℤ := fun i ↦ (coord j pts[i].2.2 * L).num
    obtain ⟨Λ, hΛ⟩ := exists_extend_functional ι (coord j)
    have hel' : HasElementaryIntegral ((aeval x ((toPoly B).map ι) +
        ∑ i ∈ (Finset.univ : Finset (Fin N)),
        algebraMap Kc E (ι pts[i].2.2 * ι (b i)) / (x - algebraMap Kc E (ι (a i)))) / y) := by
      convert hel using 3
      · rfl
      rw [sum_map_eq_fin (M := E)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [a, b, map_mul]
    obtain ⟨m, hm1, hm⟩ := hyp_principal_of_elementary hC hCall x y hx (g := g)
      ((toPoly f).map (Int.castRingHom ℚ)) hsq hdeg hy hgen ι Finset.univ a b
      (fun i _ ↦ (hon _ (List.getElem_mem i.2)).2)
      (fun i _ ↦ by
        rw [← toPoly_curveK, ← evalC_eq]
        have := (hon _ (List.getElem_mem i.2)).1
        simp only [a, b]; rw [sq]; exact this)
      (by
        intro i _ k _ hik
        exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (hi := by rw [List.length_map]; exact i.2)
          (hj := by rw [List.length_map]; exact k.2)).mp (by simp only [List.getElem_map]; exact hik)))
      ((toPoly B).map ι) (fun i ↦ ι pts[i].2.2) hel' Λ z L (hL0 j)
      (fun i _ ↦ by
        rw [hΛ]; exact (intPt_valQ _ _ (hd _ (List.getElem_mem i.2) j) (hL0 j)).symm)
    rw [← toPoly_curveK] at hm
    have hmem : ∀ q ∈ escale 2 (ptsQ l 1), q ∈ resDiv (Finset.univ : Finset (Fin N)) a b z := by
      intro q hq
      obtain ⟨q1, hq1, rfl⟩ := List.mem_map.mp hq
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq1
      obtain ⟨q0, hq0, rfl, hz⟩ := hlmem t ht
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq0
      unfold resDiv
      refine List.mem_map.mpr ⟨⟨i, hi⟩, List.mem_filter.mpr ⟨Finset.mem_toList.mpr
        (Finset.mem_univ _), by simpa [z] using hz⟩, ?_⟩
      simp [a, b, z]
    have hdeg2 : edeg (escale 2 (ptsQ l 1)) = edeg (resDiv (Finset.univ : Finset (Fin N)) a b z) := by
      rw [edeg_resDiv, edeg_escale]
      simp only [edeg, ptsQ, l, compPts, List.map_map, Function.comp_def, one_mul]
      rw [sum_filter_natAbs, PjK, intPtsK, List.map_map]
      simp only [Function.comp_def]
      rw [sum_map_eq_fin (M := ℕ), Finset.mul_sum]
    obtain ⟨ψ, h0, hp, hv⟩ := PrincipalMul.congr hmem hdeg2 hm
    refine hnt (m * 2) (by omega) ⟨ψ, h0, ?_, ?_⟩
    · rw [edeg_escale] at hp; rwa [mul_assoc]
    · rwa [escale_escale] at hv
  · -- the certificates
    split at h
    swap
    · cases h
    rename_i Rs hRs
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨w, hw, e⟩ := certsG_decomp hC x y hx hsq hy ι tors pts _ Rs hRs
    have hsplit : (evF ι x B + (pts.map fun q ↦ algebraMap Kc E (ι (q.2.2 * q.2.1)) /
        (x - algebraMap Kc E (ι q.1))).sum) / y = evF ι x (add B (sumBK Rs)) / y + w := by
      rw [split_residues ι x pts (fun j ↦ denLK j pts) hL0 pts fun q hq j ↦ hd q hq j, evF_add,
        add_div, add_div, add_assoc]
      congr 1
    rw [hsplit]
    have hpm : toPoly (curveK (K := K) f) =
        (toPoly (f.map (Int.castRingHom ℚ))).map (algebraMap ℚ K) := by
      rw [hpK, toPoly_map_list]
    have hdec := hyp_decidesF hC hCall ι x y hx (f.map (Int.castRingHom ℚ))
      (by rw [toPoly_map_list]; exact hsq) (by rw [toPoly_map_list, hdeg]; exact ⟨g, rfl⟩)
      (by rw [toPoly_map_list]; exact hy) hgen (curveK f) hpm (add B (sumBK Rs))
    rw [← hdec]
    constructor
    · intro h0; exact h0.add_in hw
    · intro h0
      have := h0.sub_in hw
      rwa [add_sub_cancel_right] at this

end Spec

end Jac
