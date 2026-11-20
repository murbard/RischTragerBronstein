import RischTragerBronstein.Mixed.NKInf2Decide

/-!
# Geometric irreducibility of curves with code coefficients (Eisenstein over `K̄[t]`)

For `F = Yⁿ + ∑ aᵢ(t) Yⁱ` over a field `C`: if a separable non-constant `q ∈ C[t]` divides every
`aᵢ` (`i < n`) and is coprime to `a₀/q`, then `F` is irreducible over `K[t]` for every
algebraically closed `K ⊇ C` (`irreducible_map_of_eis`: Eisenstein at `t − α` for a root `α` of
`q`, which is simple in `a₀`). The certificate is checked on codes (`eisCk`: the quotients
`aᵢ/q` and Bézout identities `s q + t (a₀/q) = 1`, `s₂ q + t₂ q′ = 1` are supplied), giving the
curve `nkCurveE` over `Fₘ` and its geometric irreducibility (`nkF_geo_of_eisCk`), for any
coefficients in `Fₘ[t]` — no constancy, no condition at infinity.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Curves

section Eis

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [IsAlgClosed K]

/-- **Eisenstein over `K̄[t]`** at a root of a separable common factor. -/
theorem irreducible_map_of_eis (F : C[X][X]) (hF : F.Monic) (hn : 0 < F.natDegree) (q : C[X])
    (c : ℕ → C[X]) (hc : ∀ i < F.natDegree, F.coeff i = q * c i)
    (hcop : IsCoprime q (c 0)) (hsep : IsCoprime q (derivative q)) (hdq : derivative q ≠ 0) :
    Irreducible (F.map (mapRingHom (algebraMap C K))) := by
  classical
  set φ := algebraMap C K with hφ
  set qK := q.map φ with hqK
  have hq0 : q.natDegree ≠ 0 := fun h ↦ hdq (by rw [eq_C_of_natDegree_eq_zero h, derivative_C])
  have hqKdeg : qK.degree ≠ 0 := by
    rw [hqK, degree_map, degree_eq_natDegree (fun h ↦ hq0 (by rw [h, natDegree_zero]))]
    exact_mod_cast hq0
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root qK hqKdeg
  set P : Ideal K[X] := Ideal.span {X - Polynomial.C α} with hP
  have hPp : P.IsPrime := (Ideal.span_singleton_prime (X_sub_C_ne_zero α)).mpr (prime_X_sub_C α)
  have hmem : ∀ p : K[X], p ∈ P ↔ (X - Polynomial.C α) ∣ p := fun p ↦ Ideal.mem_span_singleton
  have hdvq : (X - Polynomial.C α) ∣ qK := dvd_iff_isRoot.mpr hα
  have hFm : (F.map (mapRingHom φ)).Monic := hF.map _
  have hdegF : (F.map (mapRingHom φ)).natDegree = F.natDegree := hF.natDegree_map _
  -- evaluations at `α` from the Bézout identities
  have hevq : qK.eval α = 0 := hα
  have hc0 : ((c 0).map φ).eval α ≠ 0 := by
    obtain ⟨s, t, hst⟩ := hcop
    have := congrArg (fun p : C[X] ↦ (p.map φ).eval α) hst
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, eval_add, eval_mul,
      eval_one] at this
    rw [← hqK, hevq, mul_zero, zero_add] at this
    intro h; rw [h, mul_zero] at this; exact zero_ne_one this
  have hdq0 : (derivative qK).eval α ≠ 0 := by
    obtain ⟨s, t, hst⟩ := hsep
    have := congrArg (fun p : C[X] ↦ (p.map φ).eval α) hst
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, eval_add, eval_mul,
      eval_one] at this
    rw [← hqK, hevq, mul_zero, zero_add, ← derivative_map] at this
    intro h; rw [← hqK, h, mul_zero] at this; exact zero_ne_one this
  refine irreducible_of_eisenstein_criterion hPp ?_ ?_ ?_ ?_ hFm.isPrimitive
  · rw [hFm.leadingCoeff, hmem]
    intro h
    exact not_isUnit_X_sub_C α (isUnit_of_dvd_one h)
  · intro i hi
    have hi' : i < F.natDegree := by
      rw [← hdegF]
      rw [degree_eq_natDegree hFm.ne_zero] at hi
      exact_mod_cast hi
    rw [hmem, coeff_map, coe_mapRingHom, hc i hi', Polynomial.map_mul]
    exact dvd_mul_of_dvd_left hdvq _
  · rw [degree_eq_natDegree hFm.ne_zero, hdegF]; exact_mod_cast hn
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, coeff_map, coe_mapRingHom,
      hc 0 hn, Polynomial.map_mul]
    intro h
    have hcop2 : IsCoprime ((X - Polynomial.C α) ^ 2) ((c 0).map φ) := by
      refine IsCoprime.pow_left ?_
      refine (Irreducible.coprime_iff_not_dvd (irreducible_X_sub_C α)).mpr fun hd ↦ hc0 ?_
      exact dvd_iff_isRoot.mp hd
    have h2 : (X - Polynomial.C α) ^ 2 ∣ qK := hcop2.dvd_of_dvd_mul_right h
    obtain ⟨g, hg⟩ := h2
    apply hdq0
    rw [hg, derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C, sub_zero]
    simp

end Eis

namespace MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}

section Codes

variable (Fc ks)

/-- **The Eisenstein certificate on codes**: `aᵢ = q cᵢ` (`i < n`), `s q + t c₀ = 1`,
`s₂ q + t₂ q′ = 1`, `q′ ≠ 0`. -/
def eisCk (m : ℕ) (Pp : List (GPoly (LC m))) (q : GPoly (LC m)) (cs : List (GPoly (LC m)))
    (s t s2 t2 : GPoly (LC m)) : Bool :=
  let O := MO Fc ks m
  decide (0 < Pp.length) &&
    ((List.range Pp.length).all fun i ↦
      GPoly.isZero O (GPoly.sub O (Pp.getD i []) (GPoly.mul O q (cs.getD i [])))) &&
    GPoly.isZero O (GPoly.sub O (GPoly.add O (GPoly.mul O s q) (GPoly.mul O t (cs.getD 0 [])))
      [O.one]) &&
    GPoly.isZero O (GPoly.sub O (GPoly.add O (GPoly.mul O s2 q) (GPoly.mul O t2 (GPoly.derivX O q)))
      [O.one]) &&
    !(GPoly.isZero O (GPoly.derivX O q))

end Codes

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Soundness of the Eisenstein certificate**: the curve is irreducible over `K[t]` for every
algebraically closed `K ⊇ Fₘ`. -/
theorem nkF_geo_of_eisCk (m : ℕ) (h0 : T.Tr m) (Pp : List (GPoly (LC m))) (q : GPoly (LC m))
    (cs : List (GPoly (LC m))) (s t s2 t2 : GPoly (LC m))
    (hck : eisCk Fc ks m Pp q cs s t s2 t2 = true)
    (K : Type*) [Field K] [Algebra (T.F m) K] [IsAlgClosed K] :
    Irreducible ((T.nkF m h0 Pp).map (mapRingHom (algebraMap (T.F m) K))) := by
  classical
  set M := T.MP m h0 with hM
  simp only [eisCk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at hck
  obtain ⟨⟨⟨⟨hn0, hdiv⟩, hb1⟩, hb2⟩, hdq⟩ := hck
  have hone : GPoly.toPoly M [(MO Fc ks m).one] = 1 := by
    simp [GPoly.toPoly, M.sem_one]
  have hdeg : (T.nkF m h0 Pp).natDegree = Pp.length := polyF_natDegree _ _
  refine irreducible_map_of_eis (T.nkF m h0 Pp) (polyF_monic _ _) (by rw [hdeg]; exact hn0)
    (GPoly.toPoly M q) (fun i ↦ GPoly.toPoly M (cs.getD i [])) (fun i hi ↦ ?_) ?_ ?_ ?_
  · rw [hdeg] at hi
    have := (GPoly.isZero_iff M _).mp (hdiv i hi)
    rw [GPoly.toPoly_sub, GPoly.toPoly_mul, sub_eq_zero] at this
    rw [nkF, polyF_coeff _ _ _ hi]
    exact this
  · have := (GPoly.isZero_iff M _).mp hb1
    rw [GPoly.toPoly_sub, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_mul, hone,
      sub_eq_zero] at this
    exact ⟨_, _, this⟩
  · have := (GPoly.isZero_iff M _).mp hb2
    rw [GPoly.toPoly_sub, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_mul, hone,
      GPoly.toPoly_derivX, sub_eq_zero] at this
    exact ⟨_, _, this⟩
  · intro h
    have : GPoly.isZero (MO Fc ks m) (GPoly.derivX (MO Fc ks m) q) = true :=
      (GPoly.isZero_iff M _).mpr (by rw [GPoly.toPoly_derivX]; exact h)
    rw [this] at hdq
    exact Bool.noConfusion hdq

/-- **The curve `F(tₘ, θ) = 0` over `Fₘ`** with an Eisenstein certificate (any coefficients). -/
noncomputable def nkCurveE (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m)))
    (q : GPoly (LC m)) (cs : List (GPoly (LC m))) (s t s2 t2 : GPoly (LC m))
    (hck : eisCk Fc ks m Pp q cs s t s2 t2 = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0) :
    CurveData (T.F m) L where
  x := T.ts m
  y := θ
  F := T.nkF m h1.of_succ Pp
  htr := h1 m (by omega)
  monic := polyF_monic _ _
  irr := Curves.MT.curve_irr _ _ (h1 m (by omega)) _ (polyF_monic _ _)
    (Monic.irreducible_of_irreducible_map (mapRingHom (algebraMap (T.F m) (AlgebraicClosure (T.F m))))
      _ (polyF_monic _ _) (T.nkF_geo_of_eisCk m h1.of_succ Pp q cs s t s2 t2 hck _))
    (T.nkF_root m h1.of_succ Pp θ hθ)
  root := T.nkF_root m h1.of_succ Pp θ hθ

lemma nkCurveE_ind (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m)))
    (q : GPoly (LC m)) (cs : List (GPoly (LC m))) (s t s2 t2 : GPoly (LC m))
    (hck : eisCk Fc ks m Pp q cs s t s2 t2 = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (a : ℕ → T.F (m + 1)) (ha : ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0) :
    ∀ j < Pp.length, a j = 0 := by
  set S := T.nkCurveE m h1 Pp q cs s t s2 t2 hck θ hθ
  have hdeg : S.F.natDegree = Pp.length := polyF_natDegree _ _
  intro j hj
  have := S.coords_uniqueG (fun j ↦ (a j : L)) (fun i _ ↦ (T.mem_F_succ).mp (a i).2)
    (by rw [hdeg]; exact ha) j (by rw [hdeg]; exact hj)
  exact Subtype.ext this

end MTower

end MT

end Curves
