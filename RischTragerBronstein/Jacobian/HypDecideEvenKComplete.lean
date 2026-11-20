import RischTragerBronstein.Jacobian.HypDecideEvenK
import RischTragerBronstein.Jacobian.HypDecideRat

/-!
# Completeness of the even-degree procedure over a number field

`hypDecideEvenK_eventually`: for `q ∈ K[x]` squarefree of degree `2g + 2` with a root `e ∈ K`,
`D ≠ 0`, if the non-branch roots of `D` (in `K̄`) lie in `K` with `q` a non-zero square there,
`lc(q)` is a square in `K`, and `K` contains `g` points `bᵢ` (distinct, `D(bᵢ) ≠ 0`, `q(bᵢ)` a
non-zero square), then `hypDecideEvenK M q e A D B` answers for all large `B`.

In the `t`-model, the poles of the transformed integrand are `t = 0` and `t = 1/(α − e)` for the
non-branch roots `α` of `D`, with `P(1/(α − e)) = (α − e)^{-(2g+2)} q(α)` and `P(0) = lc(q)`; the
base points are `tᵢ = 1/(bᵢ − e)`.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad

namespace Jac

section Ev

variable {K : Type*} [Field K] [DecidableEq K] {L : Type*} [Field L]

lemma ev_shift_trim (ι : K →+* L) (P : CPoly K) (e : K) (u : L) :
    ((toPoly (trim (shiftPoly P e))).map ι).eval u = ((toPoly P).map ι).eval (u + ι e) := by
  rw [toPoly_trim, toPoly_shiftPoly, Polynomial.map_comp, eval_comp]
  simp

lemma ev_cons (ι : K →+* L) (c : K) (Q : CPoly K) (u : L) :
    ((toPoly (c :: Q)).map ι).eval u = ι c + u * ((toPoly Q).map ι).eval u := by
  simp

lemma ev_reverse (ι : K →+* L) (t : L) (ht : t ≠ 0) :
    ∀ Q : CPoly K, Q ≠ [] →
      ((toPoly Q.reverse).map ι).eval t = t ^ (Q.length - 1) * ((toPoly Q).map ι).eval (1 / t)
  | [], h => absurd rfl h
  | [c], _ => by simp
  | c :: d :: Q, _ => by
    have ih := ev_reverse ι t ht (d :: Q) (List.cons_ne_nil _ _)
    rw [List.reverse_cons, toPoly_append, Polynomial.map_add, eval_add, ih, ev_cons ι c (d :: Q)]
    simp only [List.length_reverse, List.length_cons, toPoly_cons, toPoly_nil, mul_zero, add_zero,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, map_C, eval_mul, eval_pow, eval_X,
      eval_C]
    rw [show Q.length + 1 + 1 - 1 = Q.length + 1 by omega, show Q.length + 1 - 1 = Q.length by omega]
    field_simp
    ring

end Ev

section NF

open NFC

variable (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]

set_option maxHeartbeats 6400000 in
/-- **Completeness of `hypDecideEvenK`.** -/
theorem hypDecideEvenK_eventually (hMZ : ∀ c ∈ M, c.den = 1) (q : CPoly (NF M)) {g : ℕ}
    (hq2 : (toPoly q).natDegree = 2 * g + 2) (hqsq : Squarefree (toPoly q)) (e : NF M)
    (he : (toPoly q).eval e = 0) (A D : CPoly (NF M)) (hD : toPoly D ≠ 0)
    (hroots : ∀ α : AlgebraicClosure (NF M),
      ((toPoly D).map (algebraMap (NF M) (AlgebraicClosure (NF M)))).eval α = 0 →
      ((toPoly q).map (algebraMap (NF M) (AlgebraicClosure (NF M)))).eval α ≠ 0 →
      α ∈ Set.range (algebraMap (NF M) (AlgebraicClosure (NF M))))
    (hsqD : ∀ α : NF M, (toPoly D).eval α = 0 → (toPoly q).eval α ≠ 0 →
      ∃ β : NF M, β ≠ 0 ∧ β * β = (toPoly q).eval α)
    (hlc : ∃ γ : NF M, γ ≠ 0 ∧ γ * γ = (toPoly q).leadingCoeff)
    (bs : List (NF M)) (hbsl : bs.length = g) (hbsnd : bs.Nodup)
    (hbsD : ∀ b ∈ bs, (toPoly D).eval b ≠ 0)
    (hbsq : ∀ b ∈ bs, ∃ β : NF M, β ≠ 0 ∧ β * β = (toPoly q).eval b) :
    ∃ B0, ∀ B, B0 ≤ B → hypDecideEvenK M q e A D B ≠ none := by
  classical
  by_cases hA0 : trim A = []
  · exact ⟨0, fun B _ ↦ by simp [hypDecideEvenK, hA0]⟩
  set s := trim (shiftPoly q e) with hsdef
  set R := s.drop 1 with hRdef
  set sA := trim (shiftPoly A e)
  set sD := trim (shiftPoly D e)
  have hs : toPoly s = (toPoly q).comp (X + C e) := by rw [toPoly_trim, toPoly_shiftPoly]
  have hXe : (X + C e : (NF M)[X]).natDegree = 1 := natDegree_X_add_C e
  have hcompne : ∀ F : (NF M)[X], F ≠ 0 → F.comp (X + C e) ≠ 0 := by
    intro F hF h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨-, h0⟩
    · exact hF h0
    · have := congrArg natDegree h0
      rw [hXe, natDegree_C] at this
      exact one_ne_zero this
  have hne : s ≠ [] := by
    rw [hsdef, Ne, trim_eq_nil_iff, toPoly_shiftPoly]; exact hcompne _ hqsq.ne_zero
  have hslen : s.length = 2 * g + 3 := by
    rw [length_trim hne, toPoly_shiftPoly, natDegree_comp, hXe, hq2, mul_one]
  have hs0 : s.getD 0 0 = 0 := by
    rw [← coeff_toPoly, hs, coeff_zero_eq_eval_zero, eval_comp]
    simpa using he
  have hsplit : s = 0 :: R := by
    obtain ⟨c, Q, hcQ⟩ := List.exists_cons_of_ne_nil hne
    have hR : R = Q := by simp only [R, hcQ, List.drop_one, List.tail_cons]
    rw [hcQ] at hs0
    simp only [List.getD_cons_zero] at hs0
    rw [hcQ, hs0, hR]
  have hsR : toPoly s = X * toPoly R := by
    conv_lhs => rw [hsplit]
    simp
  have hssq : Squarefree (toPoly s) := hs ▸ squarefree_comp_add_CK hqsq e
  have hRsq : Squarefree (toPoly R) := (hsR ▸ hssq).of_mul_right
  have hR0 : (toPoly R).coeff 0 ≠ 0 := by
    intro h0
    have hX : X ∣ toPoly R := X_dvd_iff.mpr h0
    have : X * X ∣ toPoly s := by rw [hsR]; exact mul_dvd_mul_left X hX
    exact not_isUnit_X (hssq X this)
  have hRlen : R.length = 2 * g + 2 := by simp [R, hslen]
  have hRdeg : (toPoly R).natDegree = 2 * g + 1 := by
    have h1 : (toPoly s).natDegree = 2 * g + 2 := by rw [hs, natDegree_comp, hXe, hq2, mul_one]
    rw [hsR, natDegree_mul X_ne_zero hRsq.ne_zero, natDegree_X] at h1
    omega
  have hg : (R.length - 2) / 2 = g := by omega
  have hAne : sA ≠ [] := hA0 ∘ fun h ↦ by
    rw [trim_eq_nil_iff] at h ⊢
    rw [toPoly_shiftPoly] at h
    by_contra hA
    exact hcompne _ hA h
  have hDne : sD ≠ [] := by
    rw [Ne, trim_eq_nil_iff, toPoly_shiftPoly]
    exact hcompne _ hD
  -- the odd model `P`
  set P := R.reverse with hPdef
  have hPlen : P.length = 2 * g + 2 := by rw [List.length_reverse, hRlen]
  have hPlc : P.getD (2 * g + 1) 0 ≠ 0 := by
    rw [← coeff_toPoly, toPoly_reverseK, coeff_reflect, hRlen,
      show 2 * g + 2 - 1 = 2 * g + 1 by omega, revAt_le le_rfl, Nat.sub_self]
    exact hR0
  have hPsq : Squarefree (toPoly P) := by
    rw [toPoly_reverseK, hRlen, show 2 * g + 2 - 1 = (toPoly R).natDegree by omega]
    exact squarefree_reflectK hRsq
  have hPg : (P.length - 2) / 2 = g := by rw [hPlen]; omega
  set An := smul (-1) (mul sA.reverse (monomial (sD.length - 1 + g + 1) 1))
  set Dn := mul sD.reverse (monomial (sA.length - 1 + 2) 1)
  have hDn : toPoly Dn ≠ 0 := by
    rw [toPoly_mul, toPoly_monomial, toPoly_reverseK]
    refine mul_ne_zero ?_ (by simp)
    rw [Ne, reflect_eq_zero_iff, ← trim_eq_nil_iff, trim_trim]; exact hDne
  -- `P(τ) = τ^{2g+2} q(1/τ + e)` in any extension
  have hPτ : ∀ {L : Type} [Field L] (ι : NF M →+* L) (τ : L), τ ≠ 0 →
      ((toPoly P).map ι).eval τ = τ ^ (2 * g + 2) * ((toPoly q).map ι).eval (1 / τ + ι e) := by
    intro L _ ι τ hτ
    have h1 := ev_reverse ι τ hτ R (by intro h0; rw [h0] at hRlen; simp at hRlen)
    have h2 := ev_shift_trim ι q e (1 / τ)
    rw [← hsdef] at h2
    conv at h2 => lhs; rw [hsplit]
    rw [ev_cons, map_zero, zero_add] at h2
    rw [h1, hRlen, show 2 * g + 2 - 1 = 2 * g + 1 by omega, ← h2]
    field_simp
    ring
  -- `P(0) = lc(q)`
  have hP0 : (toPoly P).eval 0 = (toPoly q).leadingCoeff := by
    rw [← coeff_zero_eq_eval_zero, toPoly_reverseK, coeff_reflect, hRlen,
      show 2 * g + 2 - 1 = 2 * g + 1 by omega, revAt_zero, ← hRdeg]
    have h1 := congrArg leadingCoeff hsR
    rw [leadingCoeff_mul, leadingCoeff_X, one_mul, hs, leadingCoeff_comp (by rw [hXe]; exact one_ne_zero),
      leadingCoeff_X_add_C, one_pow, mul_one] at h1
    rw [leadingCoeff] at h1
    exact h1.symm
  -- the non-branch part of `D̃`
  set St := nbPartK P Dn
  have hSt0 : toPoly St ≠ 0 := nbPartK_ne_zero P Dn hDn
  have hStsq : Squarefree (toPoly St) := squarefree_nbPartK P Dn hDn
  obtain ⟨u, v, huv⟩ := isCoprime_nbPartK P Dn hDn
  obtain ⟨-, -, -, heSt⟩ := nbPartK_facts P Dn hDn
  have hStDn : toPoly St ∣ toPoly Dn := by
    have h1 : toPoly St ∣ toPoly (sqfreePart Dn) := by rw [heSt]; exact dvd_mul_right _ _
    exact h1.trans ⟨_, sqfreePart_mul Dn hDn⟩
  have key : ∀ {L : Type} [Field L] (ι : NF M →+* L) (τ : L), ((toPoly St).map ι).eval τ = 0 →
      τ = 0 ∨ (τ ≠ 0 ∧ ((toPoly D).map ι).eval (1 / τ + ι e) = 0 ∧
        ((toPoly q).map ι).eval (1 / τ + ι e) ≠ 0) := by
    intro L _ ι τ hτ
    by_cases hτ0 : τ = 0
    · exact Or.inl hτ0
    right
    have hPne : ((toPoly P).map ι).eval τ ≠ 0 := by
      intro h0
      have := congrArg (fun F : (NF M)[X] ↦ (F.map ι).eval τ) huv
      have h2 : ((toPoly (nbPartK P Dn)).map ι).eval τ = 0 := hτ
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, eval_add, eval_mul,
        eval_one] at this
      rw [h0, h2, mul_zero, mul_zero, add_zero] at this
      exact zero_ne_one this
    obtain ⟨W, hW⟩ := hStDn
    have hDn0 : ((toPoly Dn).map ι).eval τ = 0 := by
      rw [hW, Polynomial.map_mul, eval_mul, hτ, zero_mul]
    rw [toPoly_mul, toPoly_monomial, Polynomial.map_mul, eval_mul] at hDn0
    have hmono : ((C (1 : NF M) * X ^ (sA.length - 1 + 2)).map ι).eval τ ≠ 0 := by
      simp [hτ0]
    have hrev := (mul_eq_zero.mp hDn0).resolve_right hmono
    rw [ev_reverse ι τ hτ0 sD hDne, ev_shift_trim] at hrev
    have hDv := (mul_eq_zero.mp hrev).resolve_left (pow_ne_zero _ hτ0)
    refine ⟨hτ0, hDv, fun hq0 ↦ hPne ?_⟩
    rw [hPτ ι τ hτ0, hq0, mul_zero]
  -- `S̃` splits over `K`
  set Kb := AlgebraicClosure (NF M)
  set j := algebraMap (NF M) Kb
  have hrange : ∀ τ : Kb, ((toPoly St).map j).eval τ = 0 → τ ∈ Set.range j := by
    intro τ hτ
    rcases key j τ hτ with h0 | ⟨hτ0, hDv, hqv⟩
    · exact ⟨0, by rw [h0, map_zero]⟩
    · obtain ⟨a, ha⟩ := hroots _ hDv hqv
      refine ⟨1 / (a - e), ?_⟩
      rw [map_div₀, map_one, map_sub, ha, add_sub_cancel_right, one_div_one_div]
  set Stb := (toPoly St).map j
  have hStb0 : Stb ≠ 0 := (Polynomial.map_ne_zero_iff j.injective).mpr hSt0
  have hStbnd : Stb.roots.Nodup :=
    nodup_roots ((PerfectField.separable_iff_squarefree.mpr hStsq).map)
  have hStbcard : Stb.roots.card = (toPoly St).natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map_eq_of_injective j.injective]
  have hpre : ∀ τ ∈ Stb.roots, ∃ a : NF M, j a = τ := fun τ hτ ↦
    hrange τ ((mem_roots hStb0).mp hτ)
  choose! pre hpre' using hpre
  set rs0 := Stb.roots.toList.map pre
  have hrs0nd : rs0.Nodup := by
    refine (show Stb.roots.toList.Nodup by
      rw [← Multiset.coe_nodup, Multiset.coe_toList]; exact hStbnd).map_on ?_
    intro a ha b hb hab
    rw [← hpre' a (Multiset.mem_toList.mp ha), ← hpre' b (Multiset.mem_toList.mp hb), hab]
  have hrs0root : ∀ a ∈ rs0, (toPoly St).eval a = 0 := by
    intro a ha
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ha
    have h1 : Stb.eval τ = 0 := (mem_roots hStb0).mp (Multiset.mem_toList.mp hτ)
    rw [← hpre' τ (Multiset.mem_toList.mp hτ), eval_map, eval₂_hom] at h1
    apply j.injective
    rw [map_zero, h1]
  have hsplitSt := EllQuad.split_of_hasRoots hSt0 hrs0nd
    (by rw [List.length_map, Multiset.length_toList, hStbcard]) hrs0root
  -- square roots at the poles
  have hpt : ∀ α : NF M, (toPoly St).eval α = 0 → ∃ β : NF M, β ≠ 0 ∧ β * β = evalC P α := by
    intro α hα
    have hα' : ((toPoly St).map (RingHom.id _)).eval α = 0 := by rwa [Polynomial.map_id]
    rcases key (RingHom.id _) α hα' with h0 | ⟨hτ0, hDv, hqv⟩
    · subst h0
      obtain ⟨γ, hγ0, hγ⟩ := hlc
      exact ⟨γ, hγ0, by rw [hγ, evalC_eq, hP0]⟩
    · simp only [Polynomial.map_id, RingHom.id_apply] at hDv hqv
      obtain ⟨β0, hβ0, hβ⟩ := hsqD _ hDv hqv
      refine ⟨α ^ (g + 1) * β0, mul_ne_zero (pow_ne_zero _ hτ0) hβ0, ?_⟩
      have := hPτ (RingHom.id _) α hτ0
      simp only [Polynomial.map_id, RingHom.id_apply] at this
      rw [evalC_eq, this, ← hβ]
      ring
  -- base points `tᵢ = 1/(bᵢ − e)`
  have hbe : ∀ b ∈ bs, b - e ≠ 0 := by
    intro b hb h0
    obtain ⟨β, hβ0, hβ⟩ := hbsq b hb
    rw [sub_eq_zero.mp h0, he] at hβ
    exact hβ0 (mul_self_eq_zero.mp hβ)
  choose! sqf hsqf0 hsqf using hbsq
  set as := bs.map fun b ↦ 1 / (b - e)
  set bs' := bs.map fun b ↦ (1 / (b - e)) ^ (g + 1) * sqf b
  have hinv : ∀ b ∈ bs, 1 / (1 / (b - e)) + e = b := by
    intro b hb; field_simp [hbe b hb]; ring
  have hPb : ∀ b ∈ bs, (toPoly P).eval (1 / (b - e)) = (1 / (b - e)) ^ (2 * g + 2) *
      (toPoly q).eval b := by
    intro b hb
    have := hPτ (RingHom.id _) (1 / (b - e)) (one_div_ne_zero (hbe b hb))
    simp only [Polynomial.map_id, RingHom.id_apply] at this
    rw [this, hinv b hb]
  obtain ⟨B0, hB0⟩ := hypDecideNFC_eventually M hMZ hPlen hPlc hPsq An Dn hDn _ rs0 hsplitSt hpt
    as bs' (by simp [as, hbsl]) (by simp [bs', hbsl])
    (fun i hi ↦ by
      have hb := List.getElem_mem (l := bs) (by omega : i < bs.length)
      simp only [as, bs', List.getElem_map]
      refine ⟨?_, mul_ne_zero (pow_ne_zero _ (one_div_ne_zero (hbe _ hb))) (hsqf0 _ hb)⟩
      rw [hPb _ hb, ← hsqf _ hb]
      ring)
    (hbsnd.map_on fun a ha b hb hab ↦ by
      have h1 := hbe a ha; have h2 := hbe b hb
      have : a - e = b - e := by
        have := congrArg (fun w ↦ 1 / w) hab
        simpa using this
      exact sub_left_inj.mp this)
    (fun a ha h0 ↦ by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      have h0' : ((toPoly St).map (RingHom.id _)).eval (1 / (b - e)) = 0 := by
        rwa [Polynomial.map_id]
      rcases key (RingHom.id _) _ h0' with h00 | ⟨-, hDv, -⟩
      · exact one_div_ne_zero (hbe b hb) h00
      · simp only [Polynomial.map_id, RingHom.id_apply] at hDv
        rw [hinv b hb] at hDv
        exact hbsD b hb hDv)
  refine ⟨B0, fun B hB ↦ ?_⟩
  unfold hypDecideEvenK
  rw [if_neg hA0]
  unfold evenDataK
  simp only
  rw [← hsdef, ← hRdef, hg, if_pos ⟨hs0, by omega, hAne, hDne⟩]
  simp only
  rw [← hPdef, hPg, if_pos ⟨by omega, hPlc, CPoly.squarefreeCheck_complete hPsq⟩]
  exact hB0 B hB

end NF

end Jac
