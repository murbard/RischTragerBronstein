import RischTragerBronstein.Mixed.KYQSem
import RischTragerBronstein.Mixed.KYLiouville
import RischTragerBronstein.Mixed.KYZero
import RischTragerBronstein.Mixed.KXData
import RischTragerBronstein.Mixed.KRForward

/-!
# Radicals of order `n` with poles over an exponential: the data on the curve

* `ky_data`: for `y = θ`, `yⁿ = A(x)` over `Fₘ` (`x = t`), the integrand
  `B/(tᵏ ∏ (t − c_q) Aˡ) · θʲ` is `b yʲ` with `D = xᵏ ∏ (x − c_q)`,
  `R_q = xᵏ ∏_{q' ≠ q} (x − c_{q'})`, `P = B`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **The root `β = uᵃ Aᵇ`** (`aj + bn = 1`, `uⁿ = Aʲ`): `βⁿ = A` and `βʲ = u`. -/
lemma kummer_root {F : Type*} [Field F] (u Ac : F) (hu : u ≠ 0) (hA : Ac ≠ 0) (n j : ℕ) (a b : ℤ)
    (hab : a * j + b * n = 1) (hun : u ^ n = Ac ^ j) :
    (u ^ a * Ac ^ b) ^ n = Ac ∧ (u ^ a * Ac ^ b) ^ j = u := by
  have hun' : u ^ (n : ℤ) = Ac ^ (j : ℤ) := by rw [zpow_natCast, zpow_natCast, hun]
  constructor
  · rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm a, zpow_mul, hun', ← zpow_mul,
      ← zpow_add₀ hA]
    rw [show (j : ℤ) * a + b * n = 1 by linarith, zpow_one]
  · rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul]
    have h1 : a * j = 1 - b * n := by linarith
    rw [h1, zpow_sub₀ hu, zpow_one, mul_comm b, zpow_mul, hun', ← zpow_mul, mul_comm (j : ℤ) b,
      div_mul_eq_mul_div, mul_div_assoc, div_self (zpow_ne_zero _ hA), mul_one]

namespace MTower

variable (T : MTower Fc ks Cc L)

section YData

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
  (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
  (n : ℕ) (hn : 0 < n) (θ : L) (hθ : θ ^ n = T.evP m A)

/-- **The data of the abstract theorems** for the curve `y = θ`, `yⁿ = A(x)` over `Fₘ`. -/
theorem ky_data (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (j : ℕ) :
    let S := T.krS m h A hsq hdeg n hn θ hθ
    let f : LC (m + 1) := (B, kxDen Fc ks m A kt l cs)
    let b := T.ev (m + 1) f
    let c : Fin cs.length → T.F m := fun q ↦ (T.MP m h.of_succ).sem (kqC Fc ks m cs q)
    let D := X ^ kt * GPoly.toPoly (T.MP m h.of_succ) (prodLinG Fc ks m cs)
    let R : Fin cs.length → (T.F m)[X] := fun q ↦
      X ^ kt * GPoly.toPoly (T.MP m h.of_succ) (prodLinG Fc ks m (cs.eraseIdx q))
    let P := GPoly.toPoly (T.MP m h.of_succ) B
    b ∈ (T.F m)⟮S.x⟯ ∧ b * S.y ^ j ∈ (T.F m)⟮S.x⟯⟮S.y⟯ ∧
      (∀ q, D = (X - Polynomial.C (c q)) * R q) ∧
      (∀ α : AlgebraicClosure (T.F m), α ≠ 0 → (∀ q, α ≠ algebraMap (T.F m) _ (c q)) →
        (D.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval α ≠ 0) ∧
      b * aeval S.x (D * S.p ^ l) = aeval S.x P := by
  intro S f b c D R P
  have hTm : T.Tr m := h.of_succ
  have hf : T.ev (m + 1) f =
      T.evP m B / (T.ts m ^ kt * T.evP m (prodLinG Fc ks m cs) * T.evP m A ^ l) :=
    T.ev_rhsX m h A B kt l cs
  have hxm : ∀ Q : (T.F m)[X], aeval (T.ts m) Q ∈ (T.F m)⟮S.x⟯ := fun Q ↦ by
    letI := algebraAdjoinSimple (F := T.F m) S.x
    rw [show aeval (T.ts m) Q = aeval S.x Q from rfl, ← algebraMap_adjoinSimple (F := T.F m) S.x Q]
    exact SetLike.coe_mem _
  have hev : ∀ Q : GPoly (LC m), T.evP m Q ∈ (T.F m)⟮S.x⟯ := fun Q ↦ by
    rw [← T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]; exact hxm _
  have hts : T.ts m ∈ (T.F m)⟮S.x⟯ := mem_adjoin_simple_self _ _
  have hb : b ∈ (T.F m)⟮S.x⟯ := by
    show T.ev (m + 1) f ∈ _
    rw [hf]
    exact div_mem (hev B) (mul_mem (mul_mem (pow_mem hts kt) (hev _)) (pow_mem (hev A) l))
  refine ⟨hb, ?_, fun q ↦ ?_, fun α hα0 hα ↦ ?_, ?_⟩
  · exact mul_mem (IntermediateField.algebraMap_mem _ (⟨b, hb⟩ : (T.F m)⟮S.x⟯))
      (pow_mem (mem_adjoin_simple_self _ _) j)
  · simp only [D, R, T.prodLin_eraseIdx m hTm cs q q.2]
    ring
  · simp only [D, Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X]
    refine mul_ne_zero (pow_ne_zero _ hα0) (T.eval_prodLin_ne m hTm cs α fun c' hc' ↦ ?_)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
    have := hα ⟨i, hi⟩
    simpa [c, kqC, List.getD_eq_getElem _ _ hi] using this
  · have hp : S.p = GPoly.toPoly (T.MP m hTm) A := rfl
    rw [hp]
    have hSx : S.x = T.ts m := rfl
    simp only [P, D, hSx, map_mul, map_pow, aeval_X]
    rw [T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm), T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm),
      T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
    show T.ev (m + 1) f * _ = _
    rw [hf]
    have hts0 : T.ts m ≠ 0 := fun h0 ↦ (h m (Nat.lt_succ_self m)) ⟨X, X_ne_zero, by
      rw [aeval_X]; exact h0⟩
    have hDv : T.evP m (prodLinG Fc ks m cs) ≠ 0 := T.evP_prodLin_ne m h cs
    have hA0 : T.evP m A ≠ 0 := by
      rw [← T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
      exact fun h0 ↦ S.htr ⟨_, hsq.ne_zero, h0⟩
    field_simp

end YData

section YCodes

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (hm : T.Tr m) (n j : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
  (cs : List (LC m))

lemma sem_kyRho (q : ℕ) :
    (T.MP m hm).sem (kyRho Fc ks m g A B kt l cs q) =
      (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) /
        ((T.MP m hm).sem (kxD Fc ks m g cs q) * (T.MP m hm).sem (kxR Fc ks m A kt l cs q)) := by
  rw [kyRho, T.sem_normC m hm, (T.MP m hm).sem_mul, (T.MP m hm).sem_inv, (T.MP m hm).sem_mul,
    T.sem_evalGC m hm, div_eq_mul_inv]

lemma sem_kyQ (q : ℕ) :
    (T.MP m hm).sem (kyQ Fc ks m n j g A B kt l cs q) =
      (T.MP m hm).sem (kyRho Fc ks m g A B kt l cs q) ^ n *
        (GPoly.toPoly (T.MP m hm) A).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ^ j := by
  rw [kyQ, T.sem_normC m hm, (T.MP m hm).sem_mul, sem_powC, sem_powC, T.sem_evalGC m hm]

lemma kyConst_spec (hc : kyConst Fc ks m n j g A B kt l cs = true) (q : ℕ) (hq : q < cs.length) :
    (T.MP m hm).sem (kyQ Fc ks m n j g A B kt l cs q) =
      ((kyK Fc ks m n j g A B kt l cs q : ℚ) : T.F m) := by
  have h := List.all_eq_true.mp hc q (List.mem_range.mpr hq)
  have hd : ((T.MP m hm).sem (kyQ Fc ks m n j g A B kt l cs q))′ = 0 := by
    rw [← (T.MP m hm).sem_deriv]; exact ((T.MP m hm).isZero_iff _).mp h
  exact T.ratValC_of_const m hm _ hd

lemma kyConst_of (hq : ∀ q < cs.length,
    ((T.MP m hm).sem (kyQ Fc ks m n j g A B kt l cs q))′ = 0) :
    kyConst Fc ks m n j g A B kt l cs = true := by
  refine List.all_eq_true.mpr fun q hqm ↦ ?_
  rw [(T.MP m hm).isZero_iff, (T.MP m hm).sem_deriv]
  exact hq q (List.mem_range.mp hqm)

end YCodes

lemma kyFieldOK_spec [Fact (Irreducible (toPoly (fKc Fc)))] {m n j : ℕ} {g : LC m} {A B : GPoly (LC m)} {kt l : ℕ} {cs : List (LC m)}
    {M zN : CPoly ℚ} {gs : List (CPoly ℚ)}
    (h : kyFieldOK Fc ks m n j g A B kt l cs M zN gs = true) :
    CPoly.trim M = M ∧ 1 < M.length ∧ powQ M zN n = NFK.norm M [1] ∧
      (∀ k, 0 < k → k < n → powQ M zN k ≠ NFK.norm M [1]) ∧ gs.length = cs.length ∧
      ∀ q < cs.length, powQ M (gs.getD q []) n = NFK.norm M [kyK Fc ks m n j g A B kt l cs q] := by
  simp only [kyFieldOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, fun k hk0 hkn ↦ ?_,
    of_decide_eq_true h5, fun q hq ↦ of_decide_eq_true (List.all_eq_true.mp h6 q
      (List.mem_range.mpr hq))⟩
  have := List.all_eq_true.mp h4 k (List.mem_range.mpr hkn)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at this
  rcases this with h | h
  · omega
  · exact h

section YPoints

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (hm : T.Tr m) (n j : ℕ) (hn : 0 < n) (hjc : Nat.Coprime j n) (g : LC m)
  (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (M : CPoly ℚ)
  [Fact (Irreducible (toPoly (liftQ Fc m M)))] (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0)
  (zN : CPoly ℚ) (gs : List (CPoly ℚ))

include hn hjc hρ in
/-- **The points over the poles and their residues.** -/
theorem ky_points (hok : kxOK Fc ks m A B kt l cs = true)
    (hc : kyConst Fc ks m n j g A B kt l cs = true)
    (hF : kyFieldOK Fc ks m n j g A B kt l cs M zN gs = true)
    (hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0)
    (hD0 : ∀ q < cs.length, (T.MP m hm).sem (kxD Fc ks m g cs q) ≠ 0) :
    let ψ := T.psiNFM m hm M ρ hρ
    let c : ℕ → T.F m := fun q ↦ (T.MP m hm).sem (kqC Fc ks m cs q)
    let βq : ℕ → T.F m := fun q ↦ ψ (kyBeta Fc ks m n j M g A B kt l cs gs q)
    IsPrimitiveRoot (aeval ρ (toPoly zN)) n ∧
      (∀ q < cs.length, βq q ≠ 0 ∧ βq q ^ n = (GPoly.toPoly (T.MP m hm) A).eval (c q)) ∧
      ∀ q < cs.length, ∀ k,
        (GPoly.toPoly (T.MP m hm) B).eval (c q) * (aeval ρ (toPoly zN) ^ k * βq q) ^ j =
          (∑ f ∈ Finset.range (toPoly M).natDegree, (kyR n j M zN gs f (q * n + k % n) : T.F m) *
            ρ ^ f) * ((T.MP m hm).sem (kxD Fc ks m g cs q) *
              (T.MP m hm).sem (kxR Fc ks m A kt l cs q)) := by
  intro ψ c βq
  obtain ⟨htrim, hlen, hz1, hz2, hgl, hgn⟩ := kyFieldOK_spec hF
  have hM0 : toPoly M ≠ 0 := by
    intro h0
    have := (trim_eq_nil_iff M).mpr h0
    rw [htrim] at this; rw [this] at hlen; simp at hlen
  have hζ := zeta_prim M ρ hρ hmin hM0 n hn zN hz1 hz2
  have hok' := T.kxOK_spec m hm A B kt l cs hok
  refine ⟨hζ, fun q hq ↦ ?_, fun q hq k ↦ ?_⟩ <;>
  · -- the root `β_q`
    have hAc : (GPoly.toPoly (T.MP m hm) A).eval (c q) ≠ 0 := (hok'.2 q hq).2.2.1
    have hBc : (GPoly.toPoly (T.MP m hm) B).eval (c q) ≠ 0 := (hok'.2 q hq).2.2.2
    have hR0 : (T.MP m hm).sem (kxR Fc ks m A kt l cs q) ≠ 0 := (hok'.2 q hq).2.1
    set ρq := (T.MP m hm).sem (kyRho Fc ks m g A B kt l cs q) with hρq
    have hρq0 : ρq ≠ 0 := by
      rw [hρq, T.sem_kyRho m hm]
      exact div_ne_zero hBc (mul_ne_zero (hD0 q hq) hR0)
    set γ := aeval ρ (toPoly (gs.getD q [])) with hγ
    have hγn : γ ^ n = ρq ^ n * (GPoly.toPoly (T.MP m hm) A).eval (c q) ^ j := by
      rw [hγ, ← aeval_powQ M ρ hρ, hgn q hq, aeval_normQ M ρ hρ, ← T.sem_kyQ m hm,
        T.kyConst_spec m hm n j g A B kt l cs hc q hq]
      simp
    have hγ0 : γ ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow hn.ne'] at hγn
      exact mul_ne_zero (pow_ne_zero _ hρq0) (pow_ne_zero _ hAc) hγn.symm
    set u := γ * ρq⁻¹ with hu
    have hu0 : u ≠ 0 := mul_ne_zero hγ0 (inv_ne_zero hρq0)
    have hun : u ^ n = (GPoly.toPoly (T.MP m hm) A).eval (c q) ^ j := by
      rw [hu, mul_pow, hγn, inv_pow]; field_simp
    have hab : (Nat.gcdA j n : ℤ) * j + Nat.gcdB j n * n = 1 := by
      have := Nat.gcd_eq_gcd_ab j n
      rw [hjc] at this; push_cast at this; linarith
    have hβ : βq q = u ^ (Nat.gcdA j n) * (GPoly.toPoly (T.MP m hm) A).eval (c q) ^ (Nat.gcdB j n) := by
      simp only [βq, ψ, kyBeta, map_mul, map_zpow₀, map_inv₀, T.psiNFM_ofQ, T.psiNFM_embM,
        T.psiF_trC m hm, T.sem_evalGC m hm]
      rfl
    obtain ⟨hβn, hβj⟩ := kummer_root u _ hu0 hAc n j _ _ hab hun
    first
    | exact ⟨by rw [hβ]; exact fun h0 ↦ hAc (by rw [← hβn, h0, zero_pow hn.ne']), by rw [hβ]; exact hβn⟩
    | rw [mul_pow, hβ, hβj, ← pow_mul]
      -- the coordinates
      have hcoord : aeval ρ (toPoly (kyRR j M zN gs q (k % n))) =
          ∑ f ∈ Finset.range (toPoly M).natDegree, (kyR n j M zN gs f (q * n + k % n) : T.F m) *
            ρ ^ f := by
        have hq' : (q * n + k % n) / n = q := by
          rw [Nat.add_div_of_dvd_right (Dvd.intro_left _ rfl), Nat.mul_div_cancel _ hn,
            Nat.div_eq_of_lt (Nat.mod_lt _ hn), add_zero]
        have hk' : (q * n + k % n) % n = k % n := by
          rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_mod]
        have hdeg : 0 < (toPoly M).natDegree := by
          have := CPoly.length_trim (p := M) (by rw [htrim]; intro h0; rw [h0] at hlen; simp at hlen)
          rw [htrim] at this; omega
        simp only [kyR, hq', hk']
        rw [kyRR, mulQ, aeval_coords M ρ hM0 hdeg]
      have hval : aeval ρ (toPoly (kyRR j M zN gs q (k % n))) = aeval ρ (toPoly zN) ^ (k * j) * γ := by
        rw [kyRR, aeval_mulQ M ρ hρ, aeval_powQ M ρ hρ, hγ]
        congr 1
        conv_rhs => rw [← Nat.mod_add_div k n]
        rw [add_mul, pow_add, mul_assoc, pow_mul (aeval ρ (toPoly zN)) n, hζ.pow_eq_one, one_pow,
          mul_one]
      rw [← hcoord, hval, hu, hρq, T.sem_kyRho m hm]
      simp only [c] at hBc ⊢
      field_simp

end YPoints

lemma foldr_max_ge (l : List ℤ) (x : ℤ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

lemma foldr_max_nonneg (l : List ℤ) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih => exact ih.trans (le_max_right _ _)

section YWit

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
  (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
  (n : ℕ) (hn : 0 < n) (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
  (θ : L) (hθ : θ ^ n = T.evP m A)
  (j : ℕ) (hjc : Nat.Coprime j n) (g : LC m) (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
  (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))] (ρ : T.F m)
  (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))

set_option maxHeartbeats 1600000 in
include hsq hdegA hcopA hjc hn hθ hρ in
/-- **The torsion order of a component is positive.** -/
theorem ky_comp_pos (hok : kxOK Fc ks m A B kt l cs = true)
    (hc : kyConst Fc ks m n j g A B kt l cs = true)
    (hF : kyFieldOK Fc ks m n j g A B kt l cs M zN gs = true)
    (hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0)
    (hD0 : ∀ q < cs.length, (T.MP m hTr.of_succ).sem (kxD Fc ks m g cs q) ≠ 0)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)} (f N : ℕ)
    (hT : kyTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f = some (some N)) : 1 ≤ N := by
  classical
  have hTm : T.Tr m := hTr.of_succ
  set S := T.krS m hTr A hsq hdegA n hn θ hθ with hS
  set K := AlgebraicClosure (T.F m)
  set ψ := T.psiNFM m hTm M ρ hρ with hψ
  set r := cs.length with hr
  obtain ⟨hζ, hβf, -⟩ := T.ky_points m hTm n j hn hjc g A B kt l cs M ρ hρ zN gs hok hc hF hmin hD0
  set ζ' := aeval ρ (toPoly zN) with hζ'
  set c : ℕ → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcdef
  set βq : ℕ → T.F m := fun q ↦ ψ (kyBeta Fc ks m n j M g A B kt l cs gs q) with hβqdef
  have hin : ∀ i : Fin (r * n), (i : ℕ) / n < r := fun i ↦ (Nat.div_lt_iff_lt_mul hn).mpr i.2
  set α : Fin (r * n) → T.F m := fun i ↦ c (i / n) with hαdef
  set β : Fin (r * n) → T.F m := fun i ↦ ζ' ^ ((i : ℕ) % n) * βq (i / n) with hβdef
  have hcinj := T.kx_cinj m hTm A B kt l cs hok
  have hSn : S.n = n := rfl
  have hSp : S.p = GPoly.toPoly (T.MP m hTm) A := rfl
  have hβ : ∀ i, β i ≠ 0 ∧ β i ^ S.n = S.p.eval (α i) := fun i ↦ by
    obtain ⟨h0, hpw⟩ := hβf _ (hin i)
    refine ⟨mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) h0, ?_⟩
    rw [hSn, hSp, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hpw]
  have hP : Function.Injective fun i ↦ (α i, β i) := by
    intro i i' h
    have h1 : (i : ℕ) / n = i' / n := by
      have := congrArg Prod.fst h
      exact congrArg Fin.val (hcinj (a₁ := ⟨_, hin i⟩) (a₂ := ⟨_, hin i'⟩) this)
    have h2 := congrArg Prod.snd h
    simp only [hβdef, h1] at h2
    have h3 := mul_right_cancel₀ (hβf _ (hin i')).1 h2
    have h4 := hζ.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h3
    apply Fin.ext
    rw [← Nat.div_add_mod i n, ← Nat.div_add_mod i' n, h1, h4]
  -- the curve over `Kₘ ⊗ N`
  have hpf : Polynomial.C ((1 : T.F m) ^ S.n) * S.p = (toPoly (kyFA Fc m M A)).map ψ := by
    rw [one_pow, map_one, one_mul, hSp, kyFA, toPoly_trim, ← toPoly_map', List.map_map,
      List.map_map, gtoPoly_eq]
    congr 1
    refine List.map_congr_left fun a _ ↦ ?_
    simp only [Function.comp_apply, hψ, T.psiNFM_embM, T.psiF_trC m hTm]
  have hp0 : Polynomial.C ((1 : T.F m) ^ S.n) * S.p ≠ 0 := by
    rw [one_pow, map_one, one_mul]; exact hsq.ne_zero
  have hsqp : Squarefree (Polynomial.C ((1 : T.F m) ^ S.n) * S.p) := by
    rw [one_pow, map_one, one_mul]; exact hsq
  have hcopp : Nat.Coprime n (Polynomial.C ((1 : T.F m) ^ S.n) * S.p).natDegree := by
    rw [one_pow, map_one, one_mul]; exact hcopA
  obtain ⟨hd, -, -⟩ := fK_factsN ψ (kyFA Fc m M A) (CPoly.trim_trim _) _ hpf hp0 hsqp n hcopp
  have hα : ∀ i, ψ (kyAl Fc ks m n M cs i) = α i := fun i ↦ by
    simp only [kyAl, hψ, T.psiNFM_embM, T.psiF_trC m hTm, hαdef, hcdef]
  have hβ' : ∀ i, ψ (kyBe Fc ks m n j M g A B kt l cs zN gs i) = 1 * β i := fun i ↦ by
    simp only [kyBe, map_mul, map_pow, hψ, T.psiNFM_ofQ, one_mul, hβdef, hβqdef, hζ']
  have hΓK : ∀ i, ((S.n : ℕ) : NFM Fc m M) * (kyBe Fc ks m n j M g A B kt l cs zN gs i) ^ (S.n - 1) ≠ 0 ∧
      (kyBe Fc ks m n j M g A B kt l cs zN gs i) ^ S.n =
        (toPoly (kyFA Fc m M A)).eval (kyAl Fc ks m n M cs i) := fun i ↦ by
    constructor
    · intro h0
      have := congrArg ψ h0
      rw [map_mul, map_pow, hβ' i, one_mul, map_natCast, map_zero] at this
      exact mul_ne_zero (by exact_mod_cast hn.ne') (pow_ne_zero _ (hβ i).1) this
    · apply ψ.injective
      rw [map_pow, hβ' i, one_mul, (hβ i).2, ← eval₂_at_apply, ← eval_map, ← hpf, hα i, one_pow,
        map_one, one_mul]
  obtain ⟨-, hsqK, hcop2⟩ := fK_factsN ψ (kyFA Fc m M A) (CPoly.trim_trim _) _ hpf hp0 hsqp n hcopp
  have hspecT := torsOracleC_specY (redAtNFM Fc m M rs) cpf
    (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) ps bound hsqK hcop2
  have hvK : ∀ i, kyBe Fc ks m n j M g A B kt l cs zN gs i ≠ 0 ∧
      (kyBe Fc ks m n j M g A B kt l cs zN gs i) ^ n =
        (toPoly (kyFA Fc m M A)).eval (kyAl Fc ks m n M cs i) := fun i ↦ by
    refine ⟨fun h0 ↦ ?_, (hΓK i).2⟩
    have := congrArg ψ h0
    rw [hβ' i, one_mul, map_zero] at this
    exact (hβ i).1 this
  have hinjK : Function.Injective fun i ↦ (kyAl Fc ks m n M cs i, kyBe Fc ks m n j M g A B kt l cs zN gs i) := by
    intro i i' h
    apply hP
    simp only [Prod.ext_iff] at h ⊢
    refine ⟨?_, ?_⟩
    · rw [← hα i, ← hα i', h.1]
    · have := congrArg ψ h.2
      rw [hβ' i, hβ' i', one_mul, one_mul] at this
      exact this
  exact ((hspecT (cs.length * n) _ _ (kyMult n j M zN gs cs.length f) hvK hinjK).1 N hT).1

set_option maxHeartbeats 1600000 in
include hsq hdegA hcopA hjc in
/-- **The witness of a component**, read on `yⁿ = A`: divisor `N L_f D_f` away from `x = 0`. -/
theorem ky_comp_wit (hok : kxOK Fc ks m A B kt l cs = true)
    (hc : kyConst Fc ks m n j g A B kt l cs = true)
    (hF : kyFieldOK Fc ks m n j g A B kt l cs M zN gs = true)
    (hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0)
    (hD0 : ∀ q < cs.length, (T.MP m hTr.of_succ).sem (kxD Fc ks m g cs q) ≠ 0)
    (f N : ℕ) (Wb : BPoly (NFM Fc m M))
    (hW : kyWit Fc ks m n j M g A B kt l cs zN gs f N = some Wb) :
    (∀ i a, ((toB Wb).coeff i).coeff a ≠ 0 → i < n) ∧
    ∃ W : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯,
      W ≠ 0 ∧ (∃ u : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯, u ≠ 0 ∧
        W = (T.krS m hTr A hsq hdegA n hn θ hθ).elemW (((toB Wb).map (mapRingHom
          (T.psiNFM m hTr.of_succ M ρ hρ))).comp (Polynomial.C (Polynomial.C 1) * X)) *
          algebraMap _ _ u) ∧
      (∀ q < cs.length, ∀ k < n, ((T.krS m hTr A hsq hdegA n hn θ hθ).ordAt
        (AlgebraicClosure (T.F m)) W
        (algebraMap (T.F m) _ ((T.MP m hTr.of_succ).sem (kqC Fc ks m cs q)))
        (algebraMap (T.F m) _ (aeval ρ (toPoly zN) ^ k *
          T.psiNFM m hTr.of_succ M ρ hρ (kyBeta Fc ks m n j M g A B kt l cs gs q))) : ℚ) =
          N * kyDen n j M zN gs cs.length f * kyR n j M zN gs f (q * n + k)) ∧
      ∀ a b : AlgebraicClosure (T.F m), b ^ n =
        ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) _)).eval a → a ≠ 0 →
        (∀ q < cs.length, a ≠ algebraMap (T.F m) _ ((T.MP m hTr.of_succ).sem (kqC Fc ks m cs q))) →
        (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt (AlgebraicClosure (T.F m)) W a b = 0 := by
  classical
  have hTm : T.Tr m := hTr.of_succ
  set S := T.krS m hTr A hsq hdegA n hn θ hθ with hS
  set K := AlgebraicClosure (T.F m)
  set ψ := T.psiNFM m hTm M ρ hρ with hψ
  set r := cs.length with hr
  obtain ⟨hζ, hβf, -⟩ := T.ky_points m hTm n j hn hjc g A B kt l cs M ρ hρ zN gs hok hc hF hmin hD0
  set ζ' := aeval ρ (toPoly zN) with hζ'
  set c : ℕ → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcdef
  set βq : ℕ → T.F m := fun q ↦ ψ (kyBeta Fc ks m n j M g A B kt l cs gs q) with hβqdef
  have hin : ∀ i : Fin (r * n), (i : ℕ) / n < r := fun i ↦ (Nat.div_lt_iff_lt_mul hn).mpr i.2
  set α : Fin (r * n) → T.F m := fun i ↦ c (i / n) with hαdef
  set β : Fin (r * n) → T.F m := fun i ↦ ζ' ^ ((i : ℕ) % n) * βq (i / n) with hβdef
  have hcinj := T.kx_cinj m hTm A B kt l cs hok
  have hSn : S.n = n := rfl
  have hSp : S.p = GPoly.toPoly (T.MP m hTm) A := rfl
  have hβ : ∀ i, β i ≠ 0 ∧ β i ^ S.n = S.p.eval (α i) := fun i ↦ by
    obtain ⟨h0, hpw⟩ := hβf _ (hin i)
    refine ⟨mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) h0, ?_⟩
    rw [hSn, hSp, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hpw]
  have hP : Function.Injective fun i ↦ (α i, β i) := by
    intro i i' h
    have h1 : (i : ℕ) / n = i' / n := by
      have := congrArg Prod.fst h
      exact congrArg Fin.val (hcinj (a₁ := ⟨_, hin i⟩) (a₂ := ⟨_, hin i'⟩) this)
    have h2 := congrArg Prod.snd h
    simp only [hβdef, h1] at h2
    have h3 := mul_right_cancel₀ (hβf _ (hin i')).1 h2
    have h4 := hζ.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h3
    apply Fin.ext
    rw [← Nat.div_add_mod i n, ← Nat.div_add_mod i' n, h1, h4]
  -- the curve over `Kₘ ⊗ N`
  have hpf : Polynomial.C ((1 : T.F m) ^ S.n) * S.p = (toPoly (kyFA Fc m M A)).map ψ := by
    rw [one_pow, map_one, one_mul, hSp, kyFA, toPoly_trim, ← toPoly_map', List.map_map,
      List.map_map, gtoPoly_eq]
    congr 1
    refine List.map_congr_left fun a _ ↦ ?_
    simp only [Function.comp_apply, hψ, T.psiNFM_embM, T.psiF_trC m hTm]
  have hp0 : Polynomial.C ((1 : T.F m) ^ S.n) * S.p ≠ 0 := by
    rw [one_pow, map_one, one_mul]; exact hsq.ne_zero
  have hsqp : Squarefree (Polynomial.C ((1 : T.F m) ^ S.n) * S.p) := by
    rw [one_pow, map_one, one_mul]; exact hsq
  have hcopp : Nat.Coprime n (Polynomial.C ((1 : T.F m) ^ S.n) * S.p).natDegree := by
    rw [one_pow, map_one, one_mul]; exact hcopA
  obtain ⟨hd, -, -⟩ := fK_factsN ψ (kyFA Fc m M A) (CPoly.trim_trim _) _ hpf hp0 hsqp n hcopp
  have hα : ∀ i, ψ (kyAl Fc ks m n M cs i) = α i := fun i ↦ by
    simp only [kyAl, hψ, T.psiNFM_embM, T.psiF_trC m hTm, hαdef, hcdef]
  have hβ' : ∀ i, ψ (kyBe Fc ks m n j M g A B kt l cs zN gs i) = 1 * β i := fun i ↦ by
    simp only [kyBe, map_mul, map_pow, hψ, T.psiNFM_ofQ, one_mul, hβdef, hβqdef, hζ']
  have hΓK : ∀ i, ((S.n : ℕ) : NFM Fc m M) * (kyBe Fc ks m n j M g A B kt l cs zN gs i) ^ (S.n - 1) ≠ 0 ∧
      (kyBe Fc ks m n j M g A B kt l cs zN gs i) ^ S.n =
        (toPoly (kyFA Fc m M A)).eval (kyAl Fc ks m n M cs i) := fun i ↦ by
    constructor
    · intro h0
      have := congrArg ψ h0
      rw [map_mul, map_pow, hβ' i, one_mul, map_natCast, map_zero] at this
      exact mul_ne_zero (by exact_mod_cast hn.ne') (pow_ne_zero _ (hβ i).1) this
    · apply ψ.injective
      rw [map_pow, hβ' i, one_mul, (hβ i).2, ← eval₂_at_apply, ← eval_map, ← hpf, hα i, one_pow,
        map_one, one_mul]
  obtain ⟨hW0ne, hWord⟩ := S.pts_witness (K := K) hcopA α β hP hβ
    (kyMult n j M zN gs cs.length f) ψ (kyFA Fc m M A) 1 one_ne_zero hpf hd _ _ hα hβ' hΓK N Wb hW
  set W0 := S.elemW (((toB Wb).map (mapRingHom ψ)).comp (Polynomial.C (Polynomial.C 1) * X))
    with hW0def
  set sh : ℕ → ℤ := fun q ↦ kySh n j M zN gs cs.length f q with hsh
  letI := algebraAdjoinSimple (F := T.F m) S.x
  set u : (T.F m)⟮S.x⟯ := ∏ q : Fin r,
    (algebraMap (T.F m)[X] (T.F m)⟮S.x⟯ (X - Polynomial.C (c q))) ^ (-((N : ℤ) * sh q)) with hu
  have hlin0 : ∀ q : Fin r, algebraMap (T.F m)[X] (T.F m)⟮S.x⟯ (X - Polynomial.C (c q)) ≠ 0 :=
    fun q h0 ↦ S.polyX_ne_zero (X_sub_C_ne_zero (c q)) (by
      show algebraMap _ _ (algebraMap (T.F m)[X] (T.F m)⟮S.x⟯ _) = 0
      rw [h0, map_zero])
  have hu0 : u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ ↦ zpow_ne_zero _ (hlin0 q)
  have huW : algebraMap (T.F m)⟮S.x⟯ (T.F m)⟮S.x⟯⟮S.y⟯ u =
      ∏ q : Fin r, S.polyX (X - Polynomial.C (c q)) ^ (-((N : ℤ) * sh q)) := by
    rw [hu, map_prod]
    simp only [map_zpow₀]
    rfl
  have hU0 : algebraMap (T.F m)⟮S.x⟯ (T.F m)⟮S.x⟯⟮S.y⟯ u ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (T.F m)⟮S.x⟯ (T.F m)⟮S.x⟯⟮S.y⟯).injective).mpr hu0
  have hordu : ∀ a b : K, b ^ S.n = (S.p.map (algebraMap (T.F m) K)).eval a → b ≠ 0 →
      S.ordAt K (algebraMap (T.F m)⟮S.x⟯ (T.F m)⟮S.x⟯⟮S.y⟯ u) a b =
        ∑ q : Fin r, if a = algebraMap (T.F m) K (c q) then -((N : ℤ) * sh q) else 0 := by
    intro a b hv hb
    rw [huW, S.ordAt_prod hv _ _ (fun q _ ↦ zpow_ne_zero _ (S.polyX_ne_zero (X_sub_C_ne_zero _)))]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [S.ordAt_zpow hv, S.ordAt_X_sub _ a b hv]
    split_ifs <;> simp
  -- the value of `gammaPts` at the points
  have hgam : ∀ i : Fin (r * n), Differential.SuperData.gammaPts (K := K) α β
      (kyMult n j M zN gs cs.length f) (algebraMap (T.F m) K (α i), algebraMap (T.F m) K (β i)) =
      kyMult n j M zN gs cs.length f i := fun i ↦ by
    rw [Differential.SuperData.gammaPts, Finset.sum_eq_single i]
    · simp
    · intro i' _ hi'
      rw [if_neg]
      intro h
      apply hi'
      apply hP
      simp only [Prod.ext_iff] at h ⊢
      exact ⟨((algebraMap (T.F m) K).injective h.1).symm, ((algebraMap (T.F m) K).injective h.2).symm⟩
    · simp
  obtain ⟨-, hWs, -⟩ := witW_spec (kyFA Fc m M A) S.n S.hn _ _ _ _ N hΓK hW
  refine ⟨fun i a h ↦ (hWs i a h).1, W0 * algebraMap _ _ u, mul_ne_zero hW0ne hU0, ⟨u, hu0, rfl⟩,
    fun q hq k hk ↦ ?_, fun a b hv ha hq ↦ ?_⟩
  · set i : Fin (r * n) := ⟨q * n + k, by nlinarith⟩ with hi
    have hiq : (i : ℕ) / n = q := by
      simp only [hi]
      rw [Nat.add_div_of_dvd_right (Dvd.intro_left _ rfl), Nat.mul_div_cancel _ hn,
        Nat.div_eq_of_lt hk, add_zero]
    have hik : (i : ℕ) % n = k := by
      simp only [hi]; rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hk]
    have hpt : algebraMap (T.F m) K (aeval ρ (toPoly zN) ^ k * ψ (kyBeta Fc ks m n j M g A B kt l cs gs q))
        = algebraMap (T.F m) K (β i) := by simp only [hβdef, hiq, hik, hβqdef, hζ']
    have hpc : algebraMap (T.F m) K ((T.MP m hTm).sem (kqC Fc ks m cs q)) =
        algebraMap (T.F m) K (α i) := by simp only [hαdef, hiq, hcdef]
    have hv := (hβ i).2
    have hvK : (algebraMap (T.F m) K (β i)) ^ S.n =
        (S.p.map (algebraMap (T.F m) K)).eval (algebraMap (T.F m) K (α i)) := by
      rw [← map_pow, hv, eval_map, eval₂_at_apply]
    have hb0 : algebraMap (T.F m) K (β i) ≠ 0 := (_root_.map_ne_zero _).mpr (hβ i).1
    rw [hpt, hpc, S.ordAt_mul hvK hW0ne hU0, hWord _ _ hvK, hgam i, hordu _ _ hvK hb0,
      Finset.sum_eq_single ⟨q, hq⟩ (fun q' _ hq' ↦ by
        rw [if_neg]; intro h
        apply hq'
        apply hcinj
        have := (algebraMap (T.F m) K).injective h
        simp only [hαdef, hiq, hcdef] at this
        exact this.symm) (fun h ↦ absurd (Finset.mem_univ _) h),
      if_pos (by simp [hαdef, hiq, hcdef])]
    -- `mult = zc + sh ≥ 0`
    have hzc := Differential.SuperData.rat_mul_den_int (kyR n j M zN gs f i)
      (kyDen n j M zN gs cs.length f)
      (dvd_lcmL (List.mem_map.mpr ⟨i, List.mem_range.mpr i.2, rfl⟩))
    have hshq : -kyZc n j M zN gs cs.length f i ≤ kySh n j M zN gs cs.length f q := by
      simp only [kySh]
      refine foldr_max_ge _ _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, ?_⟩)
      simp only [hi]
    have hmult : (kyMult n j M zN gs cs.length f i : ℤ) =
        kyZc n j M zN gs cs.length f i + kySh n j M zN gs cs.length f q := by
      rw [kyMult, hiq, Int.toNat_of_nonneg (by omega)]
    have hzcq : (kyZc n j M zN gs cs.length f i : ℚ) =
        kyDen n j M zN gs cs.length f * kyR n j M zN gs f i := by
      rw [kyZc, hzc]
    have hkyR : kyR n j M zN gs f i = kyR n j M zN gs f (q * n + k) := rfl
    push_cast
    rw [← hkyR]
    have := congrArg (fun z : ℤ ↦ (z : ℚ)) hmult
    push_cast at this
    rw [this, hzcq, hsh]
    show _ = (N : ℚ) * (kyDen n j M zN gs cs.length f : ℚ) * _
    ring
  · have hvK : b ^ S.n = (S.p.map (algebraMap (T.F m) K)).eval a := hv
    rw [S.ordAt_mul hvK hW0ne hU0, hWord _ _ hvK, huW,
      S.ordAt_prod hvK _ _ (fun q _ ↦ zpow_ne_zero _ (S.polyX_ne_zero (X_sub_C_ne_zero _)))]
    have hg0 : Differential.SuperData.gammaPts (K := K) α β (kyMult n j M zN gs cs.length f) (a, b) = 0 := by
      rw [Differential.SuperData.gammaPts]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [if_neg]
      intro h
      exact hq _ (hin i) (by simpa [hαdef, hcdef] using (Prod.ext_iff.mp h).1)
    rw [hg0, Finset.sum_eq_zero fun q _ ↦ by
      rw [S.ordAt_zpow hvK, S.ordAt_X_sub _ a b hvK, if_neg (hq q q.2), mul_zero]]
    simp

end YWit

end MTower

end Curves.MT
