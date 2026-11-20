import RischTragerBronstein.Mixed.KRBack
import RischTragerBronstein.Mixed.KRCore
import RischTragerBronstein.Mixed.KRPrde

/-!
# Radicals over an exponential level: the forward directions

In a realization with a primitive `n`-th root of unity `ω ∈ Fₘ` (and `s = ⁿ√κ ∈ Fₘ`), a Liouville
form for `B/(tᵏ Aˡ) · θʲ` gives:

* `kr_forward_noz` (no `z`, i.e. `ⁿ√A(0) ∉ Fₘ`): a solution of the Risch equation (Galois shift);
* `kr_forward_nontors` (`Ψ` not torsion): a solution of the Risch equation.
-/

open Polynomial Differential IntermediateField CPoly Ramanujan

set_option linter.unusedSectionVars false

lemma sum_coords {F : Type*} [Field F] (n : ℕ) (hn : 0 < n) (d : ℕ → F) (μ θ g c : F) :
    (∑ i ∈ Finset.range n, d i * (μ * θ) ^ i) / g - c =
      ∑ i ∈ Finset.range n, (d i * μ ^ i / g - (if i = 0 then c else 0)) * θ ^ i := by
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_range, hn, if_true, pow_zero, mul_one, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_pow]; ring

namespace Differential.SuperData

variable {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L] (S : SuperData C L)

lemma coe_evalW (W : C[X][X]) :
    ((S.evalW W : C⟮S.x⟯⟮S.y⟯) : L) = (W.map (aeval S.x).toRingHom).eval S.y := by
  rw [evalW, eval_map]
  have h := Polynomial.hom_eval₂ W S.polyXHom (algebraMap C⟮S.x⟯⟮S.y⟯ L)
    (AdjoinSimple.gen C⟮S.x⟯ S.y)
  rw [IntermediateField.algebraMap_apply] at h
  rw [h]
  congr 1
  exact RingHom.ext fun P ↦ S.polyX_coe P

end Differential.SuperData

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- A constant primitive root of unity lies in `Fₘ`. -/
lemma root_in_F (m : ℕ) (n : ℕ) (ζ : L) (hζ : IsPrimitiveRoot ζ n) (hζ' : ζ′ = 0) :
    ∃ ω : T.F m, IsPrimitiveRoot ω n ∧ (ω : L) = ζ := by
  obtain ⟨c0, hc0⟩ := T.hconst ζ hζ'
  refine ⟨⟨ζ, hc0 ▸ T.const_mem m c0⟩, ?_, rfl⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := (T.F m).val) hζ (fun a b h ↦ Subtype.ext h)

/-- **From the vanishing of the projections to the Risch equation.** -/
theorem kr_forward_of_proj (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (ζ : T.F m) (hζ : IsPrimitiveRoot ζ n) (j : ℕ) (hj0 : 0 < j)
    (hjn : j < n)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)))
    (hproj : ∀ W : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯,
      W ≠ 0 → (T.krS m hTr A hsq hdegA n hn θ hθ).Supp (K := AlgebraicClosure (T.F m)) W →
      (T.krS m hTr A hsq hdegA n hn θ hθ).four ζ hζ ⟨j, hjn⟩
        ((T.krS m hTr A hsq hdegA n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X)
          (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) W) = 0)
    (B : GPoly (LC m)) (kt l : ℕ) {ι : Type*} (sI : Finset ι) (c u : ι → L)
    (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) * θ ^ j = v′ + ∑ i ∈ sI, c i * logDeriv (u i)) :
    rdeOKFr Fc ks lv (m + 1) (kpFr Fc ks m j n A) ((B, denC Fc ks m kt l A) : LC (m + 1)) = true := by
  obtain ⟨a, ha, hae⟩ := T.kr_core_exact m hTr A hsq hdegA n hn θ hθ hM hmn hk ζ hζ j hj0 hjn B kt l
    sI c u hcd hu v hv heq hproj
  have hA0 : T.evP m A ≠ 0 := by
    rw [← T.aeval_toPoly (T.MP m hTr.of_succ) (T.sem_MP m hTr.of_succ)]
    exact fun h0 ↦ (T.krS m hTr A hsq hdegA n hn θ hθ).htr ⟨_, hsq.ne_zero, h0⟩
  refine T.rde_forward_N m n j hn hTr A θ hθ hA0 hspec _ a ha ?_
  rw [T.ev_rhs m hTr A B, hae]

lemma krS_eval0 (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (θ : L) (hθ : θ ^ n = T.evP m A) :
    ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval 0 =
      algebraMap (T.F m) _ ((T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero)) := by
  rw [eval_map, ← map_zero (algebraMap (T.F m) (AlgebraicClosure (T.F m))), eval₂_at_apply]
  congr 1
  exact T.toPoly_eval_zero m hTr.of_succ A

open Classical in
/-- **Forward, no `n`-th root of `A(0)` in `Fₘ`**: the Risch equation has a solution. -/
theorem kr_forward_noz (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hTn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (hTr : T.Tr (m + 1))
    (A : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hn1 : 1 < n)
    (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g)
    (ha0v : (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0)
    (hfind : krZ Fc ks lv m n A = none) (ζ : T.F m) (hζ : IsPrimitiveRoot ζ n) (j : ℕ)
    (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)))
    (B : GPoly (LC m)) (kt l : ℕ) {ι : Type*} (sI : Finset ι) (c u : ι → L)
    (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) * θ ^ j = v′ + ∑ i ∈ sI, c i * logDeriv (u i)) :
    rdeOKFr Fc ks lv (m + 1) (kpFr Fc ks m j n A) ((B, denC Fc ks m kt l A) : LC (m + 1)) = true := by
  set K := AlgebraicClosure (T.F m)
  obtain ⟨β₀, hβ₀⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (T.F m) K ((T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero))) hn
  have hβ0 : β₀ ≠ 0 := fun h0 ↦ by
    rw [h0, zero_pow hn.ne'] at hβ₀
    exact ha0v ((map_eq_zero_iff _ (algebraMap (T.F m) K).injective).mp hβ₀.symm)
  have hns := T.kr_hns hmon hdeg m n hn hTn hc A hTr.of_succ ha0v hfind β₀ hβ₀
  have hv0 : β₀ ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval 0 := by
    rw [T.krS_eval0 m hTr A hsq hdegA n hn θ hθ]; exact hβ₀
  obtain ⟨cc, hc0, hcn, hsh⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).galois_shift ζ hζ β₀ hβ0 hv0
    hn1 hns
  exact T.kr_forward_of_proj m hTr A hsq hdegA n hn θ hθ hM hmn hk ζ hζ j hj0 hjn hspec
    (fun W hW0 hsW ↦ (T.krS m hTr A hsq hdegA n hn θ hθ).four_dl_shift _
      (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) ζ hζ β₀ hβ0 hv0 hcopA ⟨j, hjn⟩ hjc hn1 W hW0
      hsW cc hc0 hcn (hsh W)) B kt l sI c u hcd hu v hv heq

open Classical in
/-- **Forward, `Ψ` not torsion**: the Risch equation has a solution. -/
theorem kr_forward_nontors [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (hTr : T.Tr (m + 1))
    (A : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hn1 : 1 < n)
    (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    [Fact (Irreducible (toPoly (cycK Fc m n)))]
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (ζ : T.F m) (hζ : IsPrimitiveRoot ζ n)
    (z : LC m) (κ : ℚ) (hZ0 : (T.MP m hTr.of_succ).sem z ≠ 0)
    (hzκ : (T.MP m hTr.of_succ).sem z ^ n * (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) =
      (κ : T.F m)) (hκ0 : κ ≠ 0) (sF : T.F m) (hsF : sF ^ n = (κ : T.F m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (NFz Fc m n) → CertProv (NFz Fc m n)) (htors : krTorsC Fc ks m n A z κ cpf ps bound rs = some none)
    (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)))
    (B : GPoly (LC m)) (kt l : ℕ) {ι : Type*} (sI : Finset ι) (c u : ι → L)
    (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) * θ ^ j = v′ + ∑ i ∈ sI, c i * logDeriv (u i)) :
    rdeOKFr Fc ks lv (m + 1) (kpFr Fc ks m j n A) ((B, denC Fc ks m kt l A) : LC (m + 1)) = true := by
  set K := AlgebraicClosure (T.F m)
  have hnt := T.kr_hnt m hTr A hsq hdegA n hn hcopA ζ hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF ps bound rs cpf htors
  obtain ⟨hμ₀, -, -, -, -, -, -, -, hβS, -, -⟩ :=
    T.kr_facts m hTr A hsq hdegA n hn hcopA ζ hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF
  set μ₀ : T.F m := (T.MP m hTr.of_succ).sem z / sF with hμ₀def
  set β₀ : K := algebraMap (T.F m) K μ₀⁻¹ with hβ₀def
  have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) K).injective).mpr (inv_ne_zero hμ₀)
  have hv0 : β₀ ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval 0 := by
    have h0 := (hβS ⟨0, hn⟩).2
    simp only [pow_zero, one_div] at h0
    rw [hβ₀def, ← map_pow, h0, eval_map, ← map_zero (algebraMap (T.F m) K), eval₂_at_apply]
  exact T.kr_forward_of_proj m hTr A hsq hdegA n hn θ hθ hM hmn hk ζ hζ j hj0 hjn hspec
    (fun W hW0 hsW ↦ (T.krS m hTr A hsq hdegA n hn θ hθ).four_dl_nontors _
      (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) ζ hζ β₀ hβ0 hv0 hcopA ⟨j, hjn⟩ hjc hn1 hnt W hW0
      hsW) B kt l sI c u hcd hu v hv heq

section TorsFwd

variable [Fact (Irreducible (toPoly (fKc Fc)))]

lemma coe_pcP_pow (m : ℕ) (hTr : T.Tr (m + 1)) (z : LC m) (j : ℕ) :
    (((T.MP (m + 1) hTr).sem (pcP Fc ks m [powC (MO Fc ks m) z j]) : T.F (m + 1)) : L) =
      T.ev m z ^ j := by
  rw [T.sem_MP (m + 1) hTr]
  change T.evP m [powC (MO Fc ks m) z j] / T.evP m [(MO Fc ks m).one] = _
  rw [T.evP_single, T.evP_single, T.ev_one_code m hTr.of_succ, div_one, ← T.sem_MP m hTr.of_succ,
    sem_powC, IntermediateField.coe_pow, T.sem_MP m hTr.of_succ]

lemma coe_Av (m n : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m)) (z : LC m) (κ : ℚ) :
    (((T.MP (m + 1) hTr).sem (pcP Fc ks m (krAh Fc ks m n A z κ)) : T.F (m + 1)) : L) =
      T.ev m z ^ n * ((κ⁻¹ : ℚ) : L) * T.evP m A := by
  rw [T.sem_MP (m + 1) hTr]
  change T.evP m (krAh Fc ks m n A z κ) / T.evP m [(MO Fc ks m).one] = _
  rw [T.evP_krAh m n hTr.of_succ, T.evP_single, T.ev_one_code m hTr.of_succ, div_one]

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Forward, `Ψ` torsion**: the parametric equation with the column has a solution with a
non-zero coefficient of the integrand. -/
theorem kr_forward_tors (m : ℕ) (hTr : T.Tr (m + 1))
    (A : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hn1 : 1 < n)
    (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    [Fact (Irreducible (toPoly (cycK Fc m n)))]
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (ζ : T.F m) (hζ : IsPrimitiveRoot ζ n)
    (z : LC m) (κ : ℚ) (hZ0 : (T.MP m hTr.of_succ).sem z ≠ 0)
    (hzκ : (T.MP m hTr.of_succ).sem z ^ n * (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) =
      (κ : T.F m)) (hκ0 : κ ≠ 0) (sF : T.F m) (hsF : sF ^ n = (κ : T.F m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (NFz Fc m n) → CertProv (NFz Fc m n)) (N : ℕ)
    (htors : krTorsC Fc ks m n A z κ cpf ps bound rs = some (some N))
    (Wb : BPoly (NFz Fc m n)) (hWb : krWit Fc ks m n A z κ N = some Wb)
    (W0b : BPoly (KF Fc m)) (hW0 : descendNF Fc m n (normNF Fc m n Wb) = some W0b)
    (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n) (col : LC (m + 1))
    (hcol : krCol Fc ks m n (krAh Fc ks m n A z κ) z j W0b = some col)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)))
    (B : GPoly (LC m)) (kt l : ℕ) {ι : Type*} (sI : Finset ι) (c u : ι → L)
    (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.evP m B / (T.ts m ^ kt * T.evP m A ^ l) * θ ^ j = v′ + ∑ i ∈ sI, c i * logDeriv (u i)) :
    (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A) [((B, denC Fc ks m kt l A) : LC (m + 1)), col]).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true := by
  classical
  set K := AlgebraicClosure (T.F m)
  have hTm : T.Tr m := hTr.of_succ
  set S := T.krS m hTr A hsq hdegA n hn θ hθ with hS
  have hx := T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk
  set η : T.F m := (T.val m g)′ with hη
  -- the data of the twist
  obtain ⟨hμ₀, hpf, hd, hsqK, hcop2, hΓK, hvK, hinj, hβS, hP, hβ'⟩ :=
    T.kr_facts m hTr A hsq hdegA n hn hcopA ζ hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF
  set μ₀ : T.F m := (T.MP m hTm).sem z / sF with hμ₀def
  set βS : Fin n → T.F m := fun k ↦ ζ ^ (k : ℕ) / μ₀ with hβSdef
  set β₀ : K := algebraMap (T.F m) K μ₀⁻¹ with hβ₀def
  have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) K).injective).mpr (inv_ne_zero hμ₀)
  have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) K)).eval 0 := by
    have h0 := (hβS ⟨0, hn⟩).2
    simp only [βS, pow_zero, one_div] at h0
    rw [hβ₀def, ← map_pow, h0, eval_map, ← map_zero (algebraMap (T.F m) K), eval₂_at_apply]
  -- `N ≥ 1`
  have hspecT := torsOracleC_spec (redAtNF Fc m n rs) (cpf (krFK Fc ks m n A z κ))
    (fun p _ R h ↦ MTower.redAtNF_valid (Fc := Fc) m n rs p R h) ps bound hsqK hcop2
  have hN1 := ((hspecT n (fun _ ↦ (0 : NFz Fc m n)) (fun k ↦ zetaN Fc m n ^ (k : ℕ)) (ramMult n)
    hvK hinj).1 N htors).1
  -- the norm witness
  have hNW := T.kr_norm_witness m hTr A hsq hdegA n hn hcopA ζ hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF hn1 N
    Wb hWb W0b hW0
  simp only at hNW
  obtain ⟨hWt0, hWtord⟩ := hNW
  set Wt := S.evalW (((toB W0b).map (mapRingHom (T.psiF m hTm))).comp
    (Polynomial.C (Polynomial.C μ₀) * X)) with hWt
  set UN : ℕ := (unitsN n).length * N with hUN
  have hU : 0 < (unitsN n).length := List.length_pos_of_mem (List.mem_filter.mpr
    ⟨List.mem_range.mpr hn1, by simp⟩)
  have hUN0 : 0 < UN := Nat.mul_pos hU hN1
  set M0 : ℤ := ramM0 n with hM0def
  set Mx : ℤ := (UN : ℤ) * M0 with hMx
  have hxz : S.xE ^ (-Mx) ≠ 0 := zpow_ne_zero _ S.xE_ne
  set W₀ := Wt * S.xE ^ (-Mx) with hW₀def
  have hW₀0 : W₀ ≠ 0 := mul_ne_zero hWt0 hxz
  have hbk : ∀ k : Fin n, Differential.SuperData.bk ζ β₀ (k : ℕ) = algebraMap (T.F m) K (βS k) :=
    fun k ↦ by
      simp only [Differential.SuperData.bk, βS, div_eq_mul_inv]
      rw [map_mul, map_pow, hβ₀def]
  have hgam : ∀ k : Fin n, Differential.SuperData.gammaPts (K := K) (fun _ ↦ (0 : T.F m)) βS
      (ramMult n) (0, algebraMap (T.F m) K (βS k)) = ramMult n k := fun k ↦ by
    rw [Differential.SuperData.gammaPts, Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      rw [if_neg]
      intro h
      apply hl
      apply hP
      simp only [Prod.ext_iff, map_zero, true_and] at h
      simp [(algebraMap (T.F m) K).injective h.symm]
    · simp
  have hsW : S.Supp (K := K) W₀ := fun α β hv hα ↦ by
    rw [S.ordAt_mul hv hWt0 hxz, S.ordAt_zpow hv, S.ordAt_xE α β hv, if_neg hα, hWtord α β hv,
      Differential.SuperData.gammaPts, Finset.sum_eq_zero]
    · simp
    intro k _
    rw [if_neg]
    intro h
    exact hα (by simpa using (Prod.ext_iff.mp h).1)
  have hWr : ∀ i, S.rv ζ β₀ W₀ i = UN * ramC n i := fun i ↦ by
    rw [← S.rv_mod ζ hζ β₀ W₀ i]
    have hi : i % n < n := Nat.mod_lt _ hn
    have hv := S.bk_v ζ hζ β₀ hv0 (i % n)
    show S.ordAt K (Wt * S.xE ^ (-Mx)) 0 (Differential.SuperData.bk ζ β₀ (i % n)) = _
    rw [S.ordAt_mul hv hWt0 hxz, S.ordAt_zpow hv, S.ordAt_xE _ _ hv,
      if_pos rfl, if_neg (S.bk_ne ζ hζ β₀ hβ0 _), hWtord _ _ hv, hbk ⟨i % n, hi⟩, hgam ⟨i % n, hi⟩]
    have := ramMult_eq n ⟨i % n, hi⟩
    simp only at this
    have hmod : ramC n (i % n) = ramC n i := by
      rw [← ramC_gcd, Nat.gcd_comm, ← Nat.gcd_rec, ramC_gcd]
    rw [this, hmod]
    push_cast
    ring
  -- the column and the twist
  have hA0 : T.evP m A ≠ 0 := by
    rw [← T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
    exact fun h0 ↦ S.htr ⟨_, hsq.ne_zero, h0⟩
  have hz0L : T.ev m z ≠ 0 := fun h ↦ hZ0 (Subtype.ext (by rw [T.sem_MP m hTm]; exact h))
  obtain ⟨Wd, s1, s2, Q, D, gg, hgg, hWd, hbez, hdiv, hD, hcolv⟩ :=
    T.krCol_spec m n hn hTr _ z j W0b col hcol
  set φ : T.F (m + 1) →+* L := algebraMap (T.F (m + 1)) L with hφdef
  have hφ : ∀ x, φ x′ = (φ x)′ := fun x ↦ rfl
  set Av := (T.MP (m + 1) hTr).sem (pcP Fc ks m (krAh Fc ks m n A z κ)) with hAv
  have hAvL : φ Av = T.ev m z ^ n * ((κ⁻¹ : ℚ) : L) * T.evP m A := T.coe_Av m n hTr A z κ
  have hμL : ((μ₀ : T.F m) : L) = T.ev m z / (sF : L) := by
    rw [hμ₀def, IntermediateField.coe_div, T.sem_MP m hTm]
  have hκL : (κ : L) ≠ 0 := by exact_mod_cast hκ0
  have hsFL : ((sF : T.F m) : L) ^ n = (κ : L) := by
    rw [← IntermediateField.coe_pow, hsF]; simp
  have hsF0 : ((sF : T.F m) : L) ≠ 0 := fun h0 ↦ hκL (by rw [← hsFL, h0, zero_pow hn.ne'])
  set Y : L := (μ₀ : L) * θ with hY
  have hYn : Y ^ n = φ Av := by
    rw [hY, mul_pow, hμL, div_pow, hsFL, hθ, hAvL]
    push_cast
    field_simp
  have hAv0 : φ Av ≠ 0 := by
    rw [hAvL]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hz0L) ?_) hA0
    exact_mod_cast inv_ne_zero hκ0
  have hYd : Y′ = φ (((1 / n : ℚ) : T.F (m + 1)) * (Av′ * Av⁻¹)) * Y := by
    rw [map_mul φ, map_mul φ, map_inv₀ φ, hφ, map_ratCast φ]
    exact deriv_of_pow_eq n hn Y _ hYn hAv0
  obtain ⟨-, hWY⟩ := twist_dlog_hom φ hφ n _ Wd s1 s2 Q D Av _ gg hWd hbez hgg hdiv Y hYn hYd
  -- `Wt = W(Y)`
  have hf0 : (T.MP (m + 1) hTr).sem (pcP Fc ks m (([] : List (KF Fc m)).map (unTr Fc m))) = 0 :=
    Subtype.ext ((T.sem_poly_code m hTr ([] : GPoly (LC m))).trans rfl)
  have hpoly : ((toB W0b).map (mapRingHom (T.psiF m hTm))).map (aeval S.x).toRingHom =
      Polynomial.map φ (toPoly (W0b.map fun c ↦ (T.MP (m + 1) hTr).sem
        (pcP Fc ks m (c.map (unTr Fc m))))) := by
    ext i : 1
    rw [coeff_map, coeff_map, coeff_map, coe_mapRingHom, coeff_toB, coeff_toPoly, ← hf0,
      List.getD_map]
    rw [hφdef, IntermediateField.algebraMap_apply]
    exact ((T.sem_poly_code m hTr _).trans (T.evP_unTr_map m hTm _)).symm
  have hWtY : ((Wt : (T.F m)⟮S.x⟯⟮S.y⟯) : L) = (Polynomial.map φ (toPoly (W0b.map fun c ↦
      (T.MP (m + 1) hTr).sem (pcP Fc ks m (c.map (unTr Fc m)))))).eval Y := by
    rw [hWt, S.coe_evalW, Polynomial.map_comp, eval_comp, hpoly]
    congr 1
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_X,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, IntermediateField.algebraMap_apply]
    rfl
  have hdlWt : logDeriv ((Wt : (T.F m)⟮S.x⟯⟮S.y⟯) : L) = (D.map φ).eval Y / φ gg := by
    rw [hWtY]; exact hWY
  -- the coordinates of `W₀′/W₀`
  set Mη : L := (Mx : L) * ((η : T.F m) : L) with hMη
  have hmx : ∀ w : T.F (m + 1), (w : L) ∈ (T.F m)⟮S.x⟯ := fun w ↦ (T.mem_F_succ).mp w.2
  have hmc : ∀ w : T.F m, (w : L) ∈ (T.F m)⟮S.x⟯ := fun w ↦ IntermediateField.algebraMap_mem _ w
  obtain ⟨E, hEv⟩ : ∃ E : Fin n → (T.F m)⟮S.x⟯, ∀ i : Fin n, ((E i : (T.F m)⟮S.x⟯) : L) =
      φ (D.coeff i) * (μ₀ : L) ^ (i : ℕ) / φ gg - (if (i : ℕ) = 0 then Mη else 0) :=
    ⟨fun i ↦ ⟨φ (D.coeff i) * (μ₀ : L) ^ (i : ℕ) / φ gg - (if (i : ℕ) = 0 then Mη else 0), by
      refine sub_mem (div_mem (mul_mem (hmx _) (pow_mem (hmc μ₀) _)) (hmx _)) ?_
      split_ifs
      · exact mul_mem (intCast_mem _ _) (hmc η)
      · exact zero_mem _⟩, fun i ↦ rfl⟩
  have hlx : logDeriv ((S.xE : (T.F m)⟮S.x⟯⟮S.y⟯) : L) = ((η : T.F m) : L) := by
    rw [S.xE_val, logDeriv, hx, map_mul, aeval_C, aeval_X, IntermediateField.algebraMap_apply,
      mul_div_assoc, div_self S.x_ne_zero, mul_one]
  have hDev : (D.map φ).eval Y = ∑ i ∈ Finset.range n, φ (D.coeff i) * Y ^ i := by
    rw [eval_eq_sum_range' (n := n)]
    · simp [coeff_map]
    · by_contra hc
      push Not at hc
      by_cases hD0 : D.map φ = 0
      · rw [hD0] at hc; simp at hc; omega
      exact (leadingCoeff_ne_zero.mpr hD0) (by rw [leadingCoeff, coeff_map, hD _ (by
        have := natDegree_map_le (f := φ) (p := D); omega), map_zero])
  have hE : S.dl (Polynomial.C (T.val m g)′ * X) hx W₀ =
      ∑ i, algebraMap (T.F m)⟮S.x⟯ (T.F m)⟮S.x⟯⟮S.y⟯ (E i) *
        AdjoinSimple.gen (T.F m)⟮S.x⟯ S.y ^ (i : ℕ) := by
    apply Subtype.ext
    have hl : ((S.dl (Polynomial.C (T.val m g)′ * X) hx W₀ : (T.F m)⟮S.x⟯⟮S.y⟯) : L) =
        logDeriv ((Wt : (T.F m)⟮S.x⟯⟮S.y⟯) : L) + ((-Mx : ℤ) : L) * ((η : T.F m) : L) := by
      rw [hW₀def, S.dl_mul _ _ _ _ hWt0 hxz, S.dl_zpow _ _ _ S.xE_ne, IntermediateField.coe_add,
        IntermediateField.coe_mul, S.coe_dl, S.coe_dl, hlx]
      congr 2
    have hr : ((∑ i, algebraMap (T.F m)⟮S.x⟯ (T.F m)⟮S.x⟯⟮S.y⟯ (E i) *
        AdjoinSimple.gen (T.F m)⟮S.x⟯ S.y ^ (i : ℕ) : (T.F m)⟮S.x⟯⟮S.y⟯) : L) =
        ∑ i : Fin n, ((E i : (T.F m)⟮S.x⟯) : L) * θ ^ (i : ℕ) := by
      rw [IntermediateField.coe_sum]
      rfl
    rw [hl, hr, hdlWt, hDev]
    simp_rw [hEv]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ (φ (D.coeff i) * (μ₀ : L) ^ i / φ gg -
      (if i = 0 then Mη else 0)) * θ ^ i)]
    rw [← sum_coords n hn (fun i ↦ φ (D.coeff i)) (μ₀ : L) θ (φ gg) Mη, hY, hMη, Int.cast_neg]
    ring
  obtain ⟨a, ha, e, he, hae⟩ := T.kr_core_tors m hTr A hsq hdegA n hn θ hθ hM hmn hk ζ hζ j hj0 hjn
    B kt l sI c u hcd hu v hv heq hcopA hjc hn1 β₀ hβ0 hv0 UN hUN0 W₀ hW₀0 hsW hWr E hE
  -- the column value
  have hcolL : T.ev (m + 1) col = T.ev m z ^ j * φ (D.coeff j) / φ gg := by
    rw [← T.sem_MP (m + 1) hTr, hcolv, IntermediateField.coe_div, IntermediateField.coe_mul,
      T.coe_pcP_pow m hTr z j]
    rfl
  have hEj : ((E ⟨j, hjn⟩ : (T.F m)⟮S.x⟯) : L) = T.ev (m + 1) col / (sF : L) ^ j := by
    rw [hEv, if_neg (by simp; omega), sub_zero, hcolL, hμL, div_pow]
    field_simp
  have hsF' : ((sF : T.F m) : L)′ = 0 := by
    rw [deriv_of_pow_eq n hn _ _ hsFL hκL, Tower.NestP.deriv_ratCastK (K := L) κ]; simp
  have he' : (e / (sF : L) ^ j)′ = 0 := by
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, Derivation.leibniz_pow, hsF', he]
    simp
  refine T.prde_forward_genN m n j hn hTr A hA0 θ hθ hspec _ [col] a ha (fun _ ↦ e / (sF : L) ^ j)
    (fun _ ↦ he') ?_
  rw [T.ev_rhs m hTr A B, hae, hEj]
  have h1 : ∀ x : Fin [col].length, T.ev (m + 1) [col][(x : ℕ)] = T.ev (m + 1) col := fun x ↦ by
    rcases x with ⟨_ | k, hk⟩
    · rfl
    · simp at hk
  simp only [Fin.getElem_fin, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    List.length_singleton, one_smul]
  ring

end TorsFwd

end MTower

end Curves.MT
