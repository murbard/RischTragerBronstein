import RischTragerBronstein.Mixed.KZForward

/-!
# Radicals with poles in `Kₘ ⊗ N`: the decision is correct

`kzDecide_correct`: whenever `kzDecide` answers `some b`, the integral of
`B(t) θʲ / (tᵏ D(t) A(t)ˡ)`, with `D = ∏ (t − c_q)` split over `Fₘ ⊗ N` (`N = ℚ[X]/(M)`), is
elementary exactly when `b = true`. The forward directions run in the lift `ky_lift`, where a root
of `M` is a constant of every level; the backward direction is `ky_backward`.
-/

open Polynomial Differential IntermediateField CPoly Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

section Fwd

variable [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Forward, no `n`-th root of `A(0)`, every component torsion**: the zero fibre is shifted by
Galois, so logarithms supported there have no `yʲ`-projection (`W₀ = 1`). -/
theorem kz_fwd_noz (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hTn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (hTr : T.Tr (m + 1))
    (A : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hn1 : 1 < n)
    (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1))
    {g : LC m} (hk : ks m = .exp g) (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (B : GPoly (LC m)) (kt l : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hζ : IsPrimitiveRoot (aeval ρ (toPoly zN)) n)
    (hok : kzOK Fc ks m M A B kt l cs dC = true) (hcst : kzConst Fc ks m n j M g A B kt l cs = true)
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)))
    (ha0v : (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0)
    (hfind : krZ Fc ks lv m n A = none)
    {ι : Type*} (sI : Finset ι) (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) * θ ^ j =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (hall : ∀ f ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length),
      ∃ N, kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f = some (some N))
    (b : Bool) (hsolve : kzSolveC Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs [] = some b) :
    b = true := by
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
  obtain ⟨cc, hc0, hcn, hsh⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).galois_shift
    (aeval ρ (toPoly zN)) hζ β₀ hβ0 hv0 hn1 hns
  have hmn : m < T.n := by omega
  refine T.kz_forward_pos m hTr A hsq hdegA n hn hcopA θ hθ hM hmn hk j hj0 hjn hjc B kt l M cs dC ρ hρ
    zN gs hζ hok hcst hF hspec 1 (fun U hU0 hsU ↦ ⟨0, by simp, ?_⟩) 0 ?_ [] [] rfl (by simp)
    (by simp) sI c u hcd hu v hv heq ps bound rs hall b hsolve
  · rw [(T.krS m hTr A hsq hdegA n hn θ hθ).four_dl_shift _
      (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) _ hζ β₀ hβ0 hv0 hcopA ⟨j, hjn⟩ hjc hn1 U hU0
      hsU cc hc0 hcn (hsh U), SuperData.cst_zero', zero_mul]
  · rw [SuperData.dl_one']
    simp

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Forward, `Ψ` not torsion, every component torsion** (`W₀ = 1`). -/
theorem kz_fwd_nt (m : ℕ) (hTr : T.Tr (m + 1))
    (A : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hn1 : 1 < n)
    (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (B : GPoly (LC m)) (kt l : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hζ : IsPrimitiveRoot (aeval ρ (toPoly zN)) n)
    (hok : kzOK Fc ks m M A B kt l cs dC = true) (hcst : kzConst Fc ks m n j M g A B kt l cs = true)
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)))
    (z : LC m) (κ : ℚ) (hZ0 : (T.MP m hTr.of_succ).sem z ≠ 0)
    (hzκ : (T.MP m hTr.of_succ).sem z ^ n * (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) =
      (κ : T.F m)) (hκ0 : κ ≠ 0) (sF : T.F m) (hsF : sF ^ n = (κ : T.F m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (ht : kyTorsPsiC Fc ks m n M A zN z κ cpf ps bound rs = some none)
    {ι : Type*} (sI : Finset ι) (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) * θ ^ j =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (hall : ∀ f ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length),
      ∃ N, kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f = some (some N))
    (b : Bool) (hsolve : kzSolveC Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs [] = some b) :
    b = true := by
  set K := AlgebraicClosure (T.F m)
  obtain ⟨hμ₀, -, -, -, -, -, -, -, hβS, -, -⟩ :=
    T.ky_zfacts m hTr A hsq hdegA n hn hcopA M ρ hρ zN hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF
  set μ₀ : T.F m := (T.MP m hTr.of_succ).sem z / sF with hμ₀def
  set β₀ : K := algebraMap (T.F m) K μ₀⁻¹ with hβ₀def
  have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) K).injective).mpr (inv_ne_zero hμ₀)
  have hv0 : β₀ ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval 0 := by
    have h0 := (hβS ⟨0, hn⟩).2
    simp only [pow_zero, one_div] at h0
    rw [hβ₀def, ← map_pow, h0, eval_map, ← map_zero (algebraMap (T.F m) K), eval₂_at_apply]
  have hnt := T.ky_hnt m hTr A hsq hdegA n hn hcopA M ρ hρ zN hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF ps
    bound rs ht
  refine T.kz_forward_pos m hTr A hsq hdegA n hn hcopA θ hθ hM hmn hk j hj0 hjn hjc B kt l M cs dC ρ hρ
    zN gs hζ hok hcst hF hspec 1 (fun U hU0 hsU ↦ ⟨0, by simp, ?_⟩) 0 ?_ [] [] rfl (by simp)
    (by simp) sI c u hcd hu v hv heq ps bound rs hall b hsolve
  · rw [(T.krS m hTr A hsq hdegA n hn θ hθ).four_dl_nontors _
      (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) _ hζ β₀ hβ0 hv0 hcopA ⟨j, hjn⟩ hjc hn1 hnt U hU0
      hsU, SuperData.cst_zero', zero_mul]
  · rw [SuperData.dl_one']
    simp

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Forward, a component not torsion, every point over `t = 0` torsion**: impossible. -/
theorem kz_fwd_zneg (m : ℕ) (hTr : T.Tr (m + 1))
    (A : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hn1 : 1 < n)
    (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (B : GPoly (LC m)) (kt l : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hζ : IsPrimitiveRoot (aeval ρ (toPoly zN)) n)
    (hok : kzOK Fc ks m M A B kt l cs dC = true) (hcst : kzConst Fc ks m n j M g A B kt l cs = true)
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true)
    (z : LC m) (κ : ℚ) (hZ0 : (T.MP m hTr.of_succ).sem z ≠ 0)
    (hzκ : (T.MP m hTr.of_succ).sem z ^ n * (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) =
      (κ : T.F m)) (hκ0 : κ ≠ 0) (sF : T.F m) (hsF : sF ^ n = (κ : T.F m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (hzt : kyZeroTorsC Fc ks m n M A zN z κ cpf ps bound rs = true) (f0 : ℕ)
    (hf0 : f0 ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length))
    (htors : kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f0 = some none)
    {ι : Type*} (sI : Finset ι) (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) * θ ^ j =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i)) :
    False := by
  set K := AlgebraicClosure (T.F m)
  obtain ⟨hμ₀, -, -, -, -, -, -, -, hβS, -, -⟩ :=
    T.ky_zfacts m hTr A hsq hdegA n hn hcopA M ρ hρ zN hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF
  set μ₀ : T.F m := (T.MP m hTr.of_succ).sem z / sF with hμ₀def
  set β₀ : K := algebraMap (T.F m) K μ₀⁻¹ with hβ₀def
  have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) K).injective).mpr (inv_ne_zero hμ₀)
  have hv0 : β₀ ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval 0 := by
    have h0 := (hβS ⟨0, hn⟩).2
    simp only [pow_zero, one_div] at h0
    rw [hβ₀def, ← map_pow, h0, eval_map, ← map_zero (algebraMap (T.F m) K), eval₂_at_apply]
  have hZ := T.ky_zero_wits m hTr A hsq hdegA n hn hcopA M ρ hρ zN hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF
    ps bound rs hzt
  simp only at hZ
  choose! Z hZ0' Nk hNk hZa hZz using hZ
  exact T.kz_forward_neg m hTr A hsq hdegA n hn hcopA θ hθ hM hmn hk j hj0 hjn hjc B kt l M cs dC ρ hρ
    zN gs hζ hok hcst hF ps bound rs f0 hf0 htors
    (fun V hV _ ↦ (T.krS m hTr A hsq hdegA n hn θ hθ).kill_tors (K := K) _ hζ β₀ hβ0 hv0 Z Nk hZ0'
      hNk hZa hZz V hV) sI c u hcd hu v hv heq

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Forward, a component not torsion, no `ℓ`-th root of `A(0)` for every prime `ℓ ∣ n`**:
impossible (full Galois orbit over `t = 0`). -/
theorem kz_fwd_nozneg (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hTn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (hTr : T.Tr (m + 1))
    (A : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hn1 : 1 < n)
    (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (B : GPoly (LC m)) (kt l : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hζ : IsPrimitiveRoot (aeval ρ (toPoly zN)) n)
    (hok : kzOK Fc ks m M A B kt l cs dC = true) (hcst : kzConst Fc ks m n j M g A B kt l cs = true)
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true)
    (ha0v : (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0)
    (hpr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → krZ Fc ks lv m ℓ A = none)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (f0 : ℕ)
    (hf0 : f0 ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length))
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (htors : kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f0 = some none)
    {ι : Type*} (sI : Finset ι) (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) * θ ^ j =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i)) :
    False := by
  set K := AlgebraicClosure (T.F m)
  obtain ⟨β₀, hβ₀⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (T.F m) K ((T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero))) hn
  have hβ0 : β₀ ≠ 0 := fun h0 ↦ by
    rw [h0, zero_pow hn.ne'] at hβ₀
    exact ha0v ((map_eq_zero_iff _ (algebraMap (T.F m) K).injective).mp hβ₀.symm)
  have hv0 : β₀ ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval 0 := by
    rw [T.krS_eval0 m hTr A hsq hdegA n hn θ hθ]; exact hβ₀
  have hno : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ (T.krS m hTr A hsq hdegA n hn θ hθ).n →
      ∀ c : T.F m, c ^ ℓ ≠ (T.krS m hTr A hsq hdegA n hn θ hθ).p.eval 0 := by
    intro ℓ hℓ hℓn cc hcc
    have h1 : (algebraMap (T.F m) K cc) ^ ℓ =
        algebraMap (T.F m) K ((T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero)) := by
      rw [← T.krS_eval0 m hTr A hsq hdegA n hn θ hθ, ← map_pow, hcc, eval_map,
        ← map_zero (algebraMap (T.F m) K), eval₂_at_apply]
    exact T.kr_hns hmon hdeg m ℓ hℓ.pos hTn hc A hTr.of_succ ha0v (hpr ℓ hℓ hℓn) _ h1 cc rfl
  have hconst := (T.krS m hTr A hsq hdegA n hn θ hθ).galois_full (K := K) _ hζ β₀ hβ0 hv0 hno
  exact T.kz_forward_neg m hTr A hsq hdegA n hn hcopA θ hθ hM hmn hk j hj0 hjn hjc B kt l M cs dC ρ hρ
    zN gs hζ hok hcst hF ps bound rs f0 hf0 htors
    (fun V hV _ ↦ (T.krS m hTr A hsq hdegA n hn θ hθ).kill_full (K := K) _ hζ β₀ hβ0 hv0 hconst V
      hV) sI c u hcd hu v hv heq

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Forward, `Ψ` torsion of order `N₀`, every component torsion**: `W₀` is the witness of `N₀ Ψ`
and the `yʲ`-coordinate of `W₀′/W₀` is read from the column `cols₀`. -/
theorem kz_fwd_tors (m : ℕ) (hTr : T.Tr (m + 1))
    (A : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hn1 : 1 < n)
    (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (B : GPoly (LC m)) (kt l : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hζ : IsPrimitiveRoot (aeval ρ (toPoly zN)) n)
    (hok : kzOK Fc ks m M A B kt l cs dC = true) (hcst : kzConst Fc ks m n j M g A B kt l cs = true)
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)))
    (z : LC m) (κ : ℚ) (hZ0 : (T.MP m hTr.of_succ).sem z ≠ 0)
    (hzκ : (T.MP m hTr.of_succ).sem z ^ n * (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) =
      (κ : T.F m)) (hκ0 : κ ≠ 0) (sF : T.F m) (hsF : sF ^ n = (κ : T.F m))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (N0 : ℕ) {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (ht : kyTorsPsiC Fc ks m n M A zN z κ cpf ps bound rs = some (some N0))
    (W0b : BPoly (NFM Fc m M)) (hW : kyWitPsi Fc ks m n M A zN z κ N0 = some W0b)
    (cols0 : List (LC (m + 1)))
    (hcol : kyColM Fc ks m n M (krAh Fc ks m n A z κ) z j W0b = some cols0)
    {ι : Type*} (sI : Finset ι) (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) * θ ^ j =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (hall : ∀ f ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length),
      ∃ N, kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f = some (some N))
    (b : Bool) (hsolve : kzSolveC Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs cols0 = some b)  :
    b = true := by
  set K := AlgebraicClosure (T.F m)
  obtain ⟨hμ₀, -, -, hsqK, hcop2, hΓK, hvK, hinj, hβS, -, -⟩ :=
    T.ky_zfacts m hTr A hsq hdegA n hn hcopA M ρ hρ zN hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF
  set μ₀ : T.F m := (T.MP m hTr.of_succ).sem z / sF with hμ₀def
  set β₀ : K := algebraMap (T.F m) K μ₀⁻¹ with hβ₀def
  have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) K).injective).mpr (inv_ne_zero hμ₀)
  have hv0 : β₀ ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval 0 := by
    have h0 := (hβS ⟨0, hn⟩).2
    simp only [pow_zero, one_div] at h0
    rw [hβ₀def, ← map_pow, h0, eval_map, ← map_zero (algebraMap (T.F m) K), eval₂_at_apply]
  have hTm : T.Tr m := hTr.of_succ
  obtain ⟨htrim, hlen, -, -, -, -⟩ := kzFieldOK_spec hF
  -- `N₀ ≥ 1`
  have hspecT := torsOracleC_specY (redAtNFM Fc m M rs) cpf
    (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) ps bound hsqK hcop2
  have hN1 := ((hspecT n (fun _ ↦ (0 : NFM Fc m M)) (fun k ↦ ofQ Fc m M zN ^ (k : ℕ)) (ramMult n)
    hvK hinj).1 N0 ht).1
  -- the witness `W₀`
  have hPW := T.ky_psi_wit m hTr A hsq hdegA n hn hcopA M ρ hρ zN hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF N0
    W0b hW
  simp only at hPW
  obtain ⟨hW0ne, hsW, hWr⟩ := hPW
  have hWdeg : ∀ i a, ((toB W0b).coeff i).coeff a ≠ 0 → i < n := fun i a h ↦
    ((witW_spec _ n hn _ _ _ _ _ hΓK hW).2.1 i a h).1
  set S := T.krS m hTr A hsq hdegA n hn θ hθ with hS
  have hx := T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk
  set Wt := S.elemW (((toB W0b).map (mapRingHom (T.psiNFM m hTm M ρ hρ))).comp
    (Polynomial.C (Polynomial.C μ₀) * X)) with hWt
  have hWt0 : Wt ≠ 0 := left_ne_zero_of_mul hW0ne
  -- the coordinates
  have hsF0 : sF ≠ 0 := fun h ↦ by
    rw [h, zero_pow hn.ne'] at hsF; exact hκ0 (by exact_mod_cast hsF.symm)
  have hsFL : ((sF : T.F m) : L) ^ n = (κ : L) := by
    rw [← IntermediateField.coe_pow, hsF]; simp
  have hAh : T.ev (m + 1) (pcP Fc ks m (krAh Fc ks m n A z κ)) =
      (T.ev m z / (sF : L)) ^ n * T.evP m A := by
    rw [← T.sem_MP (m + 1) hTr, T.coe_Av m n hTr A z κ, div_pow, hsFL]
    push_cast
    ring
  have hz0L : T.ev m z ≠ 0 := fun h ↦ hZ0 (Subtype.ext (by rw [T.sem_MP m hTm]; exact h))
  obtain ⟨E', hE', hE'j⟩ := T.ky_dl_coords m hTr A hsq hdegA n hn θ hθ hmn hk M htrim hlen ρ hρ
    (krAh Fc ks m n A z κ) z sF hsF0 hAh hz0L W0b hWdeg hWt0 j hjn cols0 hcol
  -- the factor `x^{−N₀ M₀}` is in `C(x)`
  set v0 : (T.F m)⟮S.x⟯ := ⟨S.x, IntermediateField.mem_adjoin_simple_self _ _⟩ with hv0def
  have hv00 : v0 ≠ 0 := fun h ↦ S.x_ne_zero (congrArg Subtype.val h)
  have hxv : S.xE = algebraMap (T.F m)⟮S.x⟯ (T.F m)⟮S.x⟯⟮S.y⟯ v0 := Subtype.ext (by
    rw [S.xE_val]; rfl)
  obtain ⟨EW, hEW, hEWj⟩ := S.dl_mul_base _ hx Wt hWt0 (v0 ^ (-((N0 : ℤ) * ramM0 n)))
    (zpow_ne_zero _ hv00) E' hE'
  rw [map_zpow₀, ← hxv] at hEW
  set d := M.length - 1 with hd
  have hcl : cols0.length = d := kyColM_length (Fc := Fc) (ks := ks) m n M _ z j _ _ hcol
  have hρL : aeval ((ρ : T.F m) : L) (toPoly M) = 0 := by
    rw [show ((ρ : T.F m) : L) = algebraMap (T.F m) L ρ from rfl, aeval_algebraMap_apply, hρ,
      map_zero]
  have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
  have hM0 : toPoly M ≠ 0 := fun h ↦ hMne (by
    have := (CPoly.trim_eq_nil_iff M).mpr h; rwa [htrim] at this)
  have hρd : ((ρ : T.F m) : L)′ = 0 := MTower.deriv_root_rat _ _ hM0 hρL
  have hsd : ((sF : T.F m) : L)′ = 0 := by
    refine deriv_eq_zero_of_isAlgebraic _ ⟨X ^ n - Polynomial.C (κ : ℚ), X_pow_sub_C_ne_zero hn _, ?_⟩
    rw [map_sub, map_pow, aeval_X, aeval_C, hsFL, eq_ratCast, sub_self]
  refine T.kz_forward_pos m hTr A hsq hdegA n hn hcopA θ hθ hM hmn hk j hj0 hjn hjc B kt l M cs dC ρ hρ
    zN gs hζ hok hcst hF hspec _ (fun U hU0 hsU ↦ S.four_dl_tors _ hx _ hζ β₀ hβ0 hv0 hcopA
      ⟨j, hjn⟩ hjc hn1 N0 hN1 _ hW0ne hsW hWr U hU0 hsU) EW hEW cols0
    ((List.range d).map fun f ↦ ((ρ : T.F m) : L) ^ f / ((sF : T.F m) : L) ^ j) (by simp [hcl])
    (fun w hw ↦ ?_) ?_ sI c u hcd hu v hv heq ps bound rs hall b hsolve
  · obtain ⟨f, -, rfl⟩ := List.mem_map.mp hw
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_inv,
      Derivation.leibniz_pow, hρd, hsd]
    simp
  · have h1 := congrArg Subtype.val (hEWj (⟨j, hjn⟩ : Fin S.n) (by simp; omega))
    refine h1.trans (hE'j.trans ?_)
    have h2 := zipWith_range_sum d (fun f ↦ ((ρ : T.F m) : L) ^ f / ((sF : T.F m) : L) ^ j)
      (T.ev (m + 1)) 1 cols0 (MO Fc ks (m + 1)).zero hcl
    simp only [mul_one] at h2
    rw [h2, Finset.sum_div]
    refine Finset.sum_congr rfl fun f _ ↦ ?_
    ring

/-- **A constant root of `M`** lies in every level; the checked `ζ` is a primitive root there. -/
lemma kz_rootF (m : ℕ) (hTm : T.Tr m) (n j : ℕ) (hn : 0 < n) (g : LC m) (A B : GPoly (LC m))
    (kt l : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))] (cs : List (NFM Fc m M))
    (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true)
    (ρE : L) (hρE : aeval ρE (toPoly M) = 0) (hρd : ρE′ = 0) :
    ∃ ρ : T.F m, aeval ρ (toPoly M) = 0 ∧ IsPrimitiveRoot (aeval ρ (toPoly zN)) n := by
  obtain ⟨htrim, hlen, h1, h2, -, -⟩ := kzFieldOK_spec hF
  obtain ⟨c0, hc0⟩ := T.hconst ρE hρd
  set ρ : T.F m := ⟨ρE, hc0 ▸ T.const_mem m c0⟩ with hρdef
  have hρ : aeval ρ (toPoly M) = 0 := by
    apply (algebraMap (T.F m) L).injective
    rw [← aeval_algebraMap_apply, map_zero]
    exact hρE
  have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
  have hM0 : toPoly M ≠ 0 := fun h ↦ hMne (by
    have := (CPoly.trim_eq_nil_iff M).mpr h; rwa [htrim] at this)
  have hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0 :=
    hmin_of_irr M ρ hρ (K := KF Fc m) (by rw [← toPoly_liftQ]; exact Fact.out)
  exact ⟨ρ, hρ, zeta_prim M ρ hρ hmin hM0 n hn zN h1 h2⟩

set_option maxHeartbeats 8000000 in
open Classical in
/-- **`kyDecide` is correct**: whenever it answers `some b`, the integral of
`B(t) θʲ / (tᵏ ∏_q (t − c_q) A(t)ˡ)` (`θⁿ = A(t)`, `t` an exponential level of a certified tower,
poles at `c_q ≠ 0`, residues in the number field `ℚ[X]/(M)`) is elementary exactly when
`b = true`. -/
theorem kzDecide_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime n (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ n = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (b : Bool) {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (hdec : kzDecideC Fc ks lv m n j g M zN gs A B kt l cs dC cpf ps bound rs = some b) :
    HasElementaryIntegral (T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) * θ ^ j) ↔
      b = true := by
  obtain ⟨hTr, hsq, hdegA, hcopA, hM, hspecA, hA0⟩ :=
    T.kr_setup (lv := lv) hmon hdeg m hn hc n j A hsqc hdegpos hcop
  have hTm : T.Tr m := hTr.of_succ
  have hMdegpos : 0 < (toPoly M).natDegree := by
    have hirr := (Fact.out : Irreducible (toPoly (liftQ Fc m M)))
    rw [toPoly_liftQ] at hirr
    have := hirr.natDegree_pos
    rwa [natDegree_map_eq_of_injective (algebraMap ℚ _).injective] at this
  have hM0 : toPoly M ≠ 0 := fun h0 ↦ by rw [h0, natDegree_zero] at hMdegpos; omega
  unfold kzDecideC at hdec
  dsimp only at hdec
  by_cases hchk : (decide (1 < n) && decide (0 < j) && decide (j < n) && decide (Nat.Coprime j n)) = true
  swap
  · simp only [Bool.not_eq_true] at hchk
    simp [hchk] at hdec
  rw [if_neg (by simp only [hchk, Bool.not_true]; decide)] at hdec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hn1, hj0⟩, hjn⟩, hjc⟩ := hchk
  have hn0 : 0 < n := by omega
  by_cases hr0 : cs.length = 0
  · rw [if_pos hr0] at hdec; exact absurd hdec (by simp)
  rw [if_neg hr0] at hdec
  by_cases hok : kzOK Fc ks m M A B kt l cs dC = true
  swap
  · rw [if_pos (by simpa using hok)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hok])] at hdec
  by_cases hcst : kzConst Fc ks m n j M g A B kt l cs = true
  swap
  · rw [if_pos (by simpa using hcst)] at hdec
    obtain rfl := Option.some.inj hdec
    simp only [Bool.false_eq_true, iff_false]
    intro hf
    obtain ⟨E, _, _, _, TE, θE, -, ρE, ι, sI, c, u, v, hTEn, hθE, -, -, hρE, hρd, hcd, hu, hv, heq⟩ :=
      T.ky_lift m hn n hn0 A θ hθ hgen _ j hf 1 one_ne_zero (toPoly M) hMdegpos
    obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
      TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
    obtain ⟨c0, hc0⟩ := TE.hconst ρE hρd
    set ρ : TE.F m := ⟨ρE, hc0 ▸ TE.const_mem m c0⟩ with hρdef
    have hρ : aeval ρ (toPoly M) = 0 := by
      apply (algebraMap (TE.F m) E).injective
      rw [← aeval_algebraMap_apply, map_zero]
      exact hρE
    exact hcst (TE.kz_forward_const m hTrE A hsqE hdegAE n hn0 θE hθE hME (by omega) hk j hj0 hjn B
      kt l M cs dC ρ hρ hM0 hok sI c u hcd hu v hv heq)
  rw [if_neg (by simp [hcst])] at hdec
  by_cases hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true
  swap
  · rw [if_pos (by simpa using hF)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hF])] at hdec
  obtain ⟨htrim, hlen, -, -, -, -⟩ := kzFieldOK_spec hF
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length) with hcomps
  set tors := comps.map (kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs) with htorsdef
  by_cases hnone : tors.any (· == none) = true
  · rw [if_pos hnone] at hdec; exact absurd hdec (by simp)
  rw [if_neg hnone] at hdec
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    simp only [kzOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hok
    exact hok.1.1
  have hall : ¬ tors.any (· == some none) = true → ∀ f ∈ comps,
      ∃ N, kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f = some (some N) := by
    intro hsn f hf
    rcases h : kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f with _ | _ | N
    · exact absurd (List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨f, hf, h⟩, by simp⟩) hnone
    · exact absurd (List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨f, hf, h⟩, by simp⟩) hsn
    · exact ⟨N, rfl⟩
  have hnt_f : tors.any (· == some none) = true → ∃ f0 ∈ comps,
      kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f0 = some none := by
    intro hsn
    obtain ⟨x, hx, hx0⟩ := List.any_eq_true.mp hsn
    obtain ⟨f0, hf0, rfl⟩ := List.mem_map.mp hx
    exact ⟨f0, hf0, by simpa using hx0⟩
  rcases hz : krZ Fc ks lv m n A with _ | z
  · -- no `n`-th root of `A(0)`
    simp only [hz] at hdec
    by_cases hsn : tors.any (· == some none) = true
    · rw [if_neg (by simp [hsn])] at hdec
      by_cases hpr : (List.range (n + 1)).all (fun ℓ ↦ !(decide (Nat.Prime ℓ ∧ ℓ ∣ n)) ||
          (krZ Fc ks lv m ℓ A).isNone) = true
      · rw [if_pos hpr] at hdec
        obtain rfl := Option.some.inj hdec
        simp only [Bool.false_eq_true, iff_false]
        intro hf
        have hprimes : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → krZ Fc ks lv m ℓ A = none := by
          intro ℓ hℓ hℓn
          have := List.all_eq_true.mp hpr ℓ
            (List.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd hn0 hℓn)))
          simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not, Option.isNone_iff_eq_none] at this
          rcases this with h | h
          · exact absurd ⟨hℓ, hℓn⟩ h
          · exact h
        obtain ⟨f0, hf0, htk⟩ := hnt_f hsn
        obtain ⟨E, _, _, _, TE, θE, -, ρE, ι, sI, c, u, v, hTEn, hθE, -, -, hρE, hρd, hcd, hu, hv,
          heq⟩ := T.ky_lift m hn n hn0 A θ hθ hgen _ j hf 1 one_ne_zero (toPoly M) hMdegpos
        obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
          TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
        obtain ⟨ρ, hρ, hζ⟩ := TE.kz_rootF m hTrE.of_succ n j hn0 g A B kt l M cs zN gs hF ρE hρE hρd
        exact TE.kz_fwd_nozneg hmon hdeg hTEn hc hTrE A hsqE hdegAE n hn0 hn1 hcopAE θE hθE hME
          (by omega) hk j hj0 hjn hjc B kt l M cs dC ρ hρ zN gs hζ hok hcst hF
          (TE.kr_a0 m hTrE.of_succ A ha0) hprimes ps bound rs f0 hf0 htk sI c u hcd hu v hv heq
      · rw [if_neg hpr] at hdec; exact absurd hdec (by simp)
    · rw [if_pos (by simp [hsn])] at hdec
      have hall' := hall hsn
      constructor
      · intro hf
        obtain ⟨E, _, _, _, TE, θE, -, ρE, ι, sI, c, u, v, hTEn, hθE, -, -, hρE, hρd, hcd, hu, hv,
          heq⟩ := T.ky_lift m hn n hn0 A θ hθ hgen _ j hf 1 one_ne_zero (toPoly M) hMdegpos
        obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
          TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
        obtain ⟨ρ, hρ, hζ⟩ := TE.kz_rootF m hTrE.of_succ n j hn0 g A B kt l M cs zN gs hF ρE hρE hρd
        exact TE.kz_fwd_noz hmon hdeg m hTEn hc hTrE A hsqE hdegAE n hn0 hn1 hcopAE θE hθE hME hk j
          hj0 hjn hjc B kt l M cs dC ρ hρ zN gs hζ hok hcst hF hspecE (TE.kr_a0 m hTrE.of_succ A ha0) hz
          sI c u hcd hu v hv heq ps bound rs hall' b hdec
      · intro hb
        subst hb
        obtain ⟨Ns, Wbs, colss, -, -, hcol, hbeq⟩ :=
          kzSolve_spec (lv := lv) m n j g M zN gs A B kt l cs dC ps bound rs [] true hall' hdec
        exact (T.ky_backward m n j hn0 hjn hTr A θ hθ hA0 M htrim hlen hspecA _ [] (by simp) Wbs
          colss hcol hbeq.symm).hasElementaryIntegral
  · -- `A(0) = κ/zⁿ`
    simp only [hz] at hdec
    obtain ⟨-, -, hκ0⟩ := T.kr_z_facts hmon hdeg m n hn0 hn hc A ha0 z hz
    obtain ⟨hz0, -⟩ := T.kr_zsem hmon hdeg m n hn0 hn hc hTm A ha0 z hz
    have hz0L : T.ev m z ≠ 0 := fun h ↦ hz0 (Subtype.ext (by rw [T.sem_MP m hTm]; exact h))
    set κ : ℚ := (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
      (A.getD 0 (MO Fc ks m).zero))).getD 0 with hκdef
    rw [if_neg hκ0] at hdec
    -- the negative answer shared by the two torsion answers of `Ψ`
    have hneg : tors.any (· == some none) = true →
        kyZeroTorsC Fc ks m n M A zN z κ cpf ps bound rs = true →
        ¬ HasElementaryIntegral (T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) * θ ^ j) := by
      intro hsn hzt hf
      obtain ⟨f0, hf0, htk⟩ := hnt_f hsn
      obtain ⟨E, _, _, _, TE, θE, s, ρE, ι, sI, c, u, v, hTEn, hθE, hsn', hs', hρE, hρd, hcd, hu, hv,
        heq⟩ := T.ky_lift m hn n hn0 A θ hθ hgen _ j hf κ hκ0 (toPoly M) hMdegpos
      obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
        TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
      obtain ⟨ρ, hρ, hζ⟩ := TE.kz_rootF m hTrE.of_succ n j hn0 g A B kt l M cs zN gs hF ρE hρE hρd
      obtain ⟨hZ0E, hzκE⟩ := TE.kr_zsem hmon hdeg m n hn0 hTEn hc hTrE.of_succ A ha0 z hz
      obtain ⟨sF, hsF⟩ := TE.ky_sF m n κ s hsn' hs'
      exact TE.kz_fwd_zneg m hTrE A hsqE hdegAE n hn0 hn1 hcopAE θE hθE hME (by omega) hk j hj0 hjn
        hjc B kt l M cs dC ρ hρ zN gs hζ hok hcst hF z κ hZ0E hzκE hκ0 sF hsF ps bound rs hzt f0 hf0 htk
        sI c u hcd hu v hv heq
    rcases ht : kyTorsPsiC Fc ks m n M A zN z κ cpf ps bound rs with _ | _ | N0
    · simp only [ht] at hdec; exact absurd hdec (by simp)
    · -- `Ψ` not torsion
      simp only [ht] at hdec
      by_cases hsn : tors.any (· == some none) = true
      · rw [if_neg (by simp [hsn])] at hdec
        by_cases hzt : kyZeroTorsC Fc ks m n M A zN z κ cpf ps bound rs = true
        · rw [if_pos hzt] at hdec
          obtain rfl := Option.some.inj hdec
          simp only [Bool.false_eq_true, iff_false]
          exact hneg hsn hzt
        · rw [if_neg hzt] at hdec; exact absurd hdec (by simp)
      · rw [if_pos (by simp [hsn])] at hdec
        have hall' := hall hsn
        constructor
        · intro hf
          obtain ⟨E, _, _, _, TE, θE, s, ρE, ι, sI, c, u, v, hTEn, hθE, hsn', hs', hρE, hρd, hcd, hu,
            hv, heq⟩ := T.ky_lift m hn n hn0 A θ hθ hgen _ j hf κ hκ0 (toPoly M) hMdegpos
          obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
            TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
          obtain ⟨ρ, hρ, hζ⟩ := TE.kz_rootF m hTrE.of_succ n j hn0 g A B kt l M cs zN gs hF ρE hρE hρd
          obtain ⟨hZ0E, hzκE⟩ := TE.kr_zsem hmon hdeg m n hn0 hTEn hc hTrE.of_succ A ha0 z hz
          obtain ⟨sF, hsF⟩ := TE.ky_sF m n κ s hsn' hs'
          exact TE.kz_fwd_nt m hTrE A hsqE hdegAE n hn0 hn1 hcopAE θE hθE hME (by omega) hk j hj0
            hjn hjc B kt l M cs dC ρ hρ zN gs hζ hok hcst hF hspecE z κ hZ0E hzκE hκ0 sF hsF ps bound rs
            ht sI c u hcd hu v hv heq hall' b hdec
        · intro hb
          subst hb
          obtain ⟨Ns, Wbs, colss, -, -, hcol, hbeq⟩ :=
            kzSolve_spec (lv := lv) m n j g M zN gs A B kt l cs dC ps bound rs [] true hall' hdec
          exact (T.ky_backward m n j hn0 hjn hTr A θ hθ hA0 M htrim hlen hspecA _ [] (by simp) Wbs
            colss hcol hbeq.symm).hasElementaryIntegral
    · -- `Ψ` torsion of order `N₀`
      simp only [ht] at hdec
      by_cases hsn : tors.any (· == some none) = true
      · rw [if_neg (by simp [hsn])] at hdec
        by_cases hzt : kyZeroTorsC Fc ks m n M A zN z κ cpf ps bound rs = true
        · rw [if_pos hzt] at hdec
          obtain rfl := Option.some.inj hdec
          simp only [Bool.false_eq_true, iff_false]
          exact hneg hsn hzt
        · rw [if_neg hzt] at hdec; exact absurd hdec (by simp)
      · rw [if_pos (by simp [hsn])] at hdec
        have hall' := hall hsn
        rcases hw : kyWitPsi Fc ks m n M A zN z κ N0 with _ | W0b
        · simp only [hw] at hdec; exact absurd hdec (by simp)
        simp only [hw] at hdec
        rcases hcc : kyColM Fc ks m n M (krAh Fc ks m n A z κ) z j W0b with _ | cols0
        · simp only [hcc] at hdec; exact absurd hdec (by simp)
        simp only [hcc] at hdec
        constructor
        · intro hf
          obtain ⟨E, _, _, _, TE, θE, s, ρE, ι, sI, c, u, v, hTEn, hθE, hsn', hs', hρE, hρd, hcd, hu,
            hv, heq⟩ := T.ky_lift m hn n hn0 A θ hθ hgen _ j hf κ hκ0 (toPoly M) hMdegpos
          obtain ⟨hTrE, hsqE, hdegAE, hcopAE, hME, hspecE, -⟩ :=
            TE.kr_setup (lv := lv) hmon hdeg m hTEn hc n j A hsqc hdegpos hcop
          obtain ⟨ρ, hρ, hζ⟩ := TE.kz_rootF m hTrE.of_succ n j hn0 g A B kt l M cs zN gs hF ρE hρE hρd
          obtain ⟨hZ0E, hzκE⟩ := TE.kr_zsem hmon hdeg m n hn0 hTEn hc hTrE.of_succ A ha0 z hz
          obtain ⟨sF, hsF⟩ := TE.ky_sF m n κ s hsn' hs'
          exact TE.kz_fwd_tors m hTrE A hsqE hdegAE n hn0 hn1 hcopAE θE hθE hME (by omega) hk j hj0
            hjn hjc B kt l M cs dC ρ hρ zN gs hζ hok hcst hF hspecE z κ hZ0E hzκE hκ0 sF hsF ps bound rs
            N0 ht W0b hw cols0 hcc sI c u hcd hu v hv heq hall' b hdec
        · intro hb
          subst hb
          obtain ⟨Ns, Wbs, colss, -, -, hcol, hbeq⟩ :=
            kzSolve_spec (lv := lv) m n j g M zN gs A B kt l cs dC ps bound rs cols0 true hall' hdec
          have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow hn0.ne'])
          have hAh : T.ev (m + 1) (pcP Fc ks m (krAh Fc ks m n A z κ)) =
              T.ev m z ^ n * ((κ⁻¹ : ℚ) : L) * θ ^ n := by
            rw [← T.sem_MP (m + 1) hTr, T.coe_Av m n hTr A z κ, hθ]
          have hzj : T.ev (m + 1) (pcP Fc ks m [powC (MO Fc ks m) z j]) = T.ev m z ^ j := by
            rw [← T.sem_MP (m + 1) hTr]; exact T.coe_pcP_pow m hTr z j
          have hcl := kyColM_length (Fc := Fc) (ks := ks) m n M _ z j _ _ hcc
          refine (T.ky_backward m n j hn0 hjn hTr A θ hθ hA0 M htrim hlen hspecA _ cols0
            (fun c hc q ↦ ?_) Wbs colss hcol hbeq.symm).hasElementaryIntegral
          obtain ⟨f, hf, rfl⟩ := List.getElem_of_mem hc
          rw [← List.getD_eq_getElem _ (MO Fc ks (m + 1)).zero hf]
          exact T.ky_col_hei m n j hn0 hjn hTr M htrim hlen _ z θ κ hκ0 hθ0 hz0L hAh hzj W0b cols0
            hcc f (by omega) q

end Fwd

end MTower

end Curves.MT
