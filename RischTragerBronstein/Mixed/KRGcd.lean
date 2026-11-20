import RischTragerBronstein.Mixed.KRDescend
import RischTragerBronstein.Algebraic.SuperIrred
import RischTragerBronstein.Torsion.SubRoot
import RischTragerBronstein.Mixed.KRCol
import RischTragerBronstein.Computable.HexpDegenerateSpec

/-!
# The column computation of `krDecide` always succeeds

The descended norm `W₀` of a witness and `Yⁿ − Â` are coprime over `K_{m+1}`
(`kr_gcd_coprime`): otherwise `Yⁿ − Â` (irreducible, Eisenstein) divides `W₀` over `Kₘ[t]`
(monic division), hence over `Kₘ(ζ)[t]` the prime `Yⁿ − Â` divides `W₀ = ∏ᵤ τᵤ W`, so one conjugate
`τᵤ W` of the witness, which is non-zero of `Y`-degree `< n`. So the gcd computed by `krCol` is a
non-zero constant and `krCol` answers (`krCol_isSome`).
-/

open Polynomial CPoly CPoly.Kron

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (m n : ℕ)
  [Fact (Irreducible (toPoly (cycK Fc m n)))]

lemma toAR_embNF (a : KF Fc m) :
    NFK.toAR (cycK Fc m n) (embNF Fc m n a) = algebraMap (KF Fc m) _ a := by
  rw [embNF, NFK.toAR_mk]; simp [CPoly.toPoly]

/-- `Kₘ → Kₘ(ζ)` as a ring homomorphism. -/
noncomputable def eNF : KF Fc m →+* NFz Fc m n where
  toFun := embNF Fc m n
  map_one' := NFK.toAR_injective _ (by rw [toAR_embNF, map_one, NFK.toAR_one])
  map_mul' a b := NFK.toAR_injective _ (by
    rw [NFK.toAR_mul, toAR_embNF, toAR_embNF, toAR_embNF, map_mul])
  map_zero' := NFK.toAR_injective _ (by rw [toAR_embNF, map_zero, NFK.toAR_zero])
  map_add' a b := NFK.toAR_injective _ (by
    rw [NFK.toAR_add, toAR_embNF, toAR_embNF, toAR_embNF, map_add])

lemma eNF_apply (a : KF Fc m) : eNF Fc m n a = embNF Fc m n a := rfl

/-- A descended coefficient list is the image of its constants. -/
lemma descendNF_spec (V : BPoly (NFz Fc m n)) (W0 : BPoly (KF Fc m))
    (h : descendNF Fc m n V = some W0) : V = W0.map (·.map (embNF Fc m n)) := by
  unfold descendNF at h
  split_ifs at h with hall
  obtain rfl := (Option.some.inj h)
  rw [List.map_map]
  conv_lhs => rw [← List.map_id V]
  refine List.map_congr_left fun c hc ↦ ?_
  simp only [id, Function.comp_apply, List.map_map]
  conv_lhs => rw [← List.map_id c]
  refine List.map_congr_left fun a ha ↦ ?_
  simp only [List.all_eq_true, decide_eq_true_eq] at hall
  have hl := hall c hc a ha
  apply NFK.toAR_injective
  show NFK.toAR (cycK Fc m n) a = NFK.toAR (cycK Fc m n) (embNF Fc m n (a.1.getD 0 0))
  rw [toAR_embNF]
  show AdjoinRoot.mk _ (toPoly a.1) = _
  rcases a with ⟨l, hl'⟩
  simp only at hl ⊢
  match l, hl with
  | [], _ => simp [CPoly.toPoly]
  | [b], _ => simp [CPoly.toPoly, AdjoinRoot.algebraMap_eq]


section Abstract

/-- Monic division descends from the fraction field. -/
lemma monic_dvd_of_map_dvd {R K : Type*} [CommRing R] [IsDomain R] [Field K] (ι : R →+* K)
    (hι : Function.Injective ι) {M P : R[X]} (hM : M.Monic) (h : M.map ι ∣ P.map ι) : M ∣ P := by
  rw [← modByMonic_eq_zero_iff_dvd hM]
  apply Polynomial.map_injective ι hι
  rw [map_modByMonic ι hM, (modByMonic_eq_zero_iff_dvd (hM.map ι)).mpr h, Polynomial.map_zero]

/-- **The norm of a witness is coprime to `Yⁿ − A`** (abstract form): `W₀` over `K₀[t]` whose image
in `k[t]` is a product of non-zero polynomials of `Y`-degree `< n`. -/
theorem coprime_norm_abstract {K0 k : Type*} [Field K0] [CharZero K0] [Field k] (e : K0 →+* k)
    (n : ℕ) (hn : 0 < n) (A : K0[X]) (hA : Squarefree A) (hAd : 0 < A.natDegree)
    (W0 : K0[X][X]) (Ws : List (k[X][X])) (hprod : W0.map (mapRingHom e) = Ws.prod)
    (hWs : ∀ w ∈ Ws, w ≠ 0 ∧ w.natDegree < n) :
    IsCoprime (W0.map (algebraMap K0[X] (RatFunc K0)))
      ((X ^ n - C A : K0[X][X]).map (algebraMap K0[X] (RatFunc K0))) := by
  set ι := algebraMap K0[X] (RatFunc K0)
  have hirr : Irreducible ((X ^ n - C A : K0[X][X]).map ι) := by
    have := irreducible_X_pow_sub_C_fraction n hn A hA hAd (RatFunc K0)
    simpa [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C] using this
  rw [isCoprime_comm, hirr.coprime_iff_not_dvd]
  intro hdvd
  have hM : (X ^ n - C A : K0[X][X]).Monic := monic_X_pow_sub_C A hn.ne'
  have hd := monic_dvd_of_map_dvd ι (IsFractionRing.injective K0[X] (RatFunc K0)) hM hdvd
  have hd' := Polynomial.map_dvd (mapRingHom e) hd
  rw [hprod] at hd'
  -- the image of `Yⁿ − A` is prime
  have hsep : (A.map e).Separable := (PerfectField.separable_iff_squarefree.mpr hA).map
  have hAe : 0 < (A.map e).natDegree := by
    rw [natDegree_map_eq_of_injective e.injective]; exact hAd
  have hprime : Prime ((X ^ n - C A : K0[X][X]).map (mapRingHom e)) := by
    have := irreducible_X_pow_sub_C_of_squarefree n hn (A.map e) hsep.squarefree hAe
    simpa [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C] using this.prime
  obtain ⟨w, hw, hdw⟩ := hprime.dvd_prod_iff.mp hd'
  obtain ⟨hw0, hwd⟩ := hWs w hw
  have := natDegree_le_of_dvd hdw hw0
  rw [Polynomial.natDegree_map_eq_of_injective (fun a b h ↦ Polynomial.map_injective e e.injective h),
    natDegree_X_pow_sub_C] at this
  omega

end Abstract


section Ops

/-- `τᵤ` is a ring homomorphism. -/
noncomputable def tauHom (hn : 0 < n) (u : ℕ) (hu : Nat.Coprime u n) (hu0 : 0 < u) :
    NFz Fc m n →+* NFz Fc m n :=
  let ω := Classical.choose (exists_prim_LK Fc m n hn)
  let hω := Classical.choose_spec (exists_prim_LK Fc m n hn)
  { toFun := tauN Fc m n u
    map_one' := (psiZ Fc m n hn ω hω).injective (by rw [psiZ_tauN Fc m n hn ω hω u hu hu0, map_one, map_one])
    map_mul' := fun a b ↦ (psiZ Fc m n hn ω hω).injective (by
      rw [psiZ_tauN Fc m n hn ω hω u hu hu0, map_mul, map_mul, psiZ_tauN Fc m n hn ω hω u hu hu0,
        psiZ_tauN Fc m n hn ω hω u hu hu0])
    map_zero' := (psiZ Fc m n hn ω hω).injective (by
      rw [psiZ_tauN Fc m n hn ω hω u hu hu0, map_zero, map_zero])
    map_add' := fun a b ↦ (psiZ Fc m n hn ω hω).injective (by
      rw [psiZ_tauN Fc m n hn ω hω u hu hu0, map_add, map_add, psiZ_tauN Fc m n hn ω hω u hu hu0,
        psiZ_tauN Fc m n hn ω hω u hu hu0]) }

lemma tauHom_apply (hn : 0 < n) (u : ℕ) (hu : Nat.Coprime u n) (hu0 : 0 < u) (a : NFz Fc m n) :
    tauHom Fc m n hn u hu hu0 a = tauN Fc m n u a := rfl

lemma tauN_injective (hn : 0 < n) (u : ℕ) (hu : Nat.Coprime u n) (hu0 : 0 < u) :
    Function.Injective (tauN Fc m n u) := by
  obtain ⟨ω, hω⟩ := exists_prim_LK Fc m n hn
  intro a b h
  have := congrArg (psiZ Fc m n hn ω hω) h
  rw [psiZ_tauN Fc m n hn ω hω u hu hu0, psiZ_tauN Fc m n hn ω hω u hu hu0] at this
  exact (psiZ Fc m n hn (ω ^ u) (hω.pow_of_coprime u hu)).injective this

/-- The executable gcd of coprime polynomials is a non-zero constant. -/
lemma trim_egcd_length {R : Type*} [Field R] [DecidableEq R] (p q : CPoly R)
    (hcop : IsCoprime (toPoly p) (toPoly q)) : (CPoly.trim (CPoly.egcd p q).1).length = 1 := by
  obtain ⟨h1, h2⟩ := CPoly.egcd_dvd p q
  have hu := hcop.isUnit_of_dvd' h1 h2
  have h0 : toPoly (CPoly.egcd p q).1 ≠ 0 := hu.ne_zero
  have hd : (toPoly (CPoly.egcd p q).1).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  have hne : CPoly.trim (CPoly.egcd p q).1 ≠ [] := fun h ↦ h0 ((CPoly.trim_eq_nil_iff _).mp h)
  rw [CPoly.length_trim hne, hd]

end Ops


lemma toPoly_map_toB {K S : Type*} [CommRing K] [CommRing S] (f : K[X] →+* S) :
    ∀ W : BPoly K, toPoly (W.map fun c ↦ f (toPoly c)) = (toB W).map f
  | [] => by simp
  | a :: W => by
    rw [List.map_cons, toPoly_cons, toB_cons, Polynomial.map_add, Polynomial.map_mul, map_C, map_X,
      toPoly_map_toB f W]

section Zeta

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (m n : ℕ)
  [Fact (Irreducible (toPoly (cycK Fc m n)))]

lemma psiZ_zetaN (hn : 0 < n) (ω : LK Fc m) (hω : IsPrimitiveRoot ω n) :
    psiZ Fc m n hn ω hω (zetaN Fc m n) = ω := by
  rw [zetaN, psiZ_mk]; simp [CPoly.toPoly]

/-- `ζ` is a primitive `n`-th root of unity of `Kₘ(ζ)`. -/
lemma zetaN_prim (hn : 0 < n) : IsPrimitiveRoot (zetaN Fc m n) n := by
  obtain ⟨ω, hω⟩ := exists_prim_LK Fc m n hn
  have h := psiZ_zetaN Fc m n hn ω hω
  rw [← h] at hω
  exact (IsPrimitiveRoot.map_iff_of_injective (psiZ Fc m n hn ω (h ▸ hω)).injective).mp hω

end Zeta

end Curves.MT
