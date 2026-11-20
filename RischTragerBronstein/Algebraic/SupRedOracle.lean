import RischTragerBronstein.Algebraic.SupRedOrder

/-!
# A torsion oracle over fields with computable reductions

`torsOracle redAt ps bound f n` decides torsion of divisors `Γ` on `yⁿ = f(x)` over `K`: it looks
among the candidate primes `ps` for two primes of good reduction (reduction maps `redAt p`,
roots of unity, base points and a non-speciality certificate found by search and linear algebra
modulo `p`, all checked by `supCheckR`), computes the orders `m_p, m_q` of the reductions and
tests `(m_p m_q) Γ` (`torsDecideR`). `torsOracle_spec`: it satisfies `TorsSpecN`.
-/

open Polynomial CPoly CPoly.Kron

namespace Sup

section Search

variable {p : ℕ} [Fact p.Prime]

/-- The elements of `𝔽_p`. -/
def zmodElems (p : ℕ) : List (ZMod p) := (List.range p).map (↑)

/-- A primitive `n`-th root of unity modulo `p`. -/
def findZeta (n : ℕ) : Option (ZMod p) :=
  (zmodElems p).find? fun z ↦ z ^ n == 1 && (List.range n).all fun l ↦ l == 0 || z ^ l != 1

/-- `g` points `(x, y)`, `y ≠ 0`, of the reduced curve, with distinct `x` avoiding `avoid`. -/
def findBase (fr : CPoly (ZMod p)) (n g : ℕ) (avoid : List (ZMod p)) :
    Option (List (ZMod p) × List (ZMod p)) :=
  let pts := (zmodElems p).filterMap fun x ↦
    if x ∈ avoid then none
    else ((zmodElems p).find? fun y ↦ y != 0 && y ^ n == evalC fr x).map fun y ↦ (x, y)
  if g ≤ pts.length then some ((pts.take g).map Prod.fst, (pts.take g).map Prod.snd) else none

/-- The non-speciality certificate, by linear algebra modulo `p`. -/
def solveLam (d n g : ℕ) (xs ys : List (ZMod p)) (ζ0 : ZMod p) :
    Option (List (List (ZMod p))) :=
  let basis := basisN n d (n * g)
  let cols : List (CPoly (ZMod p)) := (List.range g).flatMap fun i' ↦
    (List.range (n - 1)).map fun k ↦ basis.map fun ai ↦
      xs.getD i' 0 ^ ai.1 * (ζ0 ^ (k + 1) * ys.getD i' 0) ^ ai.2
  ((List.range g).map fun i ↦ CPoly.linSolve cols
    (basis.map fun ai ↦ xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2)).allSome

/-- The certificate data at `p`. -/
def certAt {K : Type*} (R : RedFns p K) (fK : CPoly K) (n : ℕ) {r : ℕ} (α : Fin r → K) :
    Option (ℕ × List (ZMod p) × List (ZMod p) × ZMod p × List (List (ZMod p))) :=
  let d := fK.length - 1
  let g := ((n - 1) * (d - 1) + 1) / 2
  let fr := fK.map R.red
  match findZeta (p := p) n, findBase fr n g (List.ofFn fun q ↦ R.red (α q)) with
  | some ζ0, some (xs, ys) =>
    (solveLam d n g xs ys ζ0).map fun lam ↦ (g, xs, ys, ζ0, lam)
  | _, _ => none

end Search

section Oracle

variable {K : Type*} [Field K] [DecidableEq K] (redAt : (p : ℕ) → Option (RedFns p K))

/-- The check at `p` for given certificate data. -/
def goodCheck [Fact p.Prime] (R : RedFns p K) (fK : CPoly K) (n : ℕ) {r : ℕ} (α β : Fin r → K)
    (c : ℕ × List (ZMod p) × List (ZMod p) × ZMod p × List (List (ZMod p))) : Bool :=
  decide (supCheckR p R fK n c.1 α β c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)

omit [DecidableEq K] in
lemma goodCheck_spec [DecidableEq K] [Fact p.Prime] {R : RedFns p K} {fK : CPoly K} {n : ℕ} {r : ℕ}
    {α β : Fin r → K} {c : ℕ × List (ZMod p) × List (ZMod p) × ZMod p × List (List (ZMod p))}
    (h : goodCheck R fK n α β c = true) :
    supCheckR p R fK n c.1 α β c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 :=
  of_decide_eq_true h

/-- A certificate provider: base points, root of unity and non-speciality certificate at `p`. -/
abbrev CertProv (K : Type*) :=
  ∀ (p : ℕ) [Fact p.Prime], RedFns p K → ∀ {r : ℕ}, (Fin r → K) →
    Option (ℕ × List (ZMod p) × List (ZMod p) × ZMod p × List (List (ZMod p)))

/-- The search provider. -/
def searchCert (fK : CPoly K) (n : ℕ) : CertProv K := fun _ _ R _ α ↦ certAt R fK n α

variable (cp : CertProv K)

/-- Is `p` a checked prime of good reduction? -/
def goodPrime (fK : CPoly K) (n : ℕ) {r : ℕ} (α β : Fin r → K) (p : ℕ) : Bool :=
  if hpr : p.Prime then
    haveI : Fact p.Prime := ⟨hpr⟩
    match redAt p with
    | some R =>
      match cp p R α with
      | some c => goodCheck R fK n α β c
      | none => false
    | none => false
  else false

/-- The decision at two given primes. -/
def torsWith (fK : CPoly K) (n : ℕ) {r : ℕ} (α β : Fin r → K) (mu : Fin r → ℕ) (bound p q : ℕ) :
    Option (Option ℕ) :=
  if hp : p.Prime then
    if hq : q.Prime then
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : Fact q.Prime := ⟨hq⟩
      match redAt p, redAt q with
      | some Rp, some Rq => torsDecideR Rp Rq fK n α β mu bound
      | _, _ => none
    else none
  else none

/-- **The torsion oracle** with a certificate provider. -/
def torsOracleC (ps : List ℕ) (bound : ℕ) (fK : CPoly K) (n : ℕ) (l : List (K × K × ℕ)) :
    Option (Option ℕ) :=
  let α : Fin l.length → K := fun q ↦ (l.get q).1
  let β : Fin l.length → K := fun q ↦ (l.get q).2.1
  let mu : Fin l.length → ℕ := fun q ↦ (l.get q).2.2
  match ps.find? (goodPrime redAt cp fK n α β) with
  | some p =>
    match (ps.filter (· ≠ p)).find? (goodPrime redAt cp fK n α β) with
    | some q => torsWith redAt fK n α β mu bound p q
    | none => none
  | none => none

/-- **The torsion oracle** (certificates found by search modulo `p`). -/
def torsOracle (ps : List ℕ) (bound : ℕ) (fK : CPoly K) (n : ℕ) (l : List (K × K × ℕ)) :
    Option (Option ℕ) :=
  torsOracleC redAt (searchCert fK n) ps bound fK n l

end Oracle

section Spec

variable {K : Type*} [Field K] [DecidableEq K] (redAt : (p : ℕ) → Option (RedFns p K))

lemma principalMulN_reindex {F : Type*} [CommRing F] (f : F[X]) (n d : ℕ) {r r' : ℕ}
    (e : Fin r' ≃ Fin r) (α β : Fin r → F) (mq : Fin r → ℕ) (s : ℕ) :
    PrincipalMulN f n d (fun q ↦ α (e q)) (fun q ↦ β (e q)) (fun q ↦ mq (e q)) s ↔
      PrincipalMulN f n d α β mq s := by
  unfold PrincipalMulN
  rw [show ∑ q, mq (e q) = ∑ q, mq q from Equiv.sum_comp e mq]
  constructor
  · rintro ⟨W, h0, hs, hv⟩
    refine ⟨W, h0, hs, fun q ↦ ?_⟩
    simpa using hv (e.symm q)
  · rintro ⟨W, h0, hs, hv⟩
    exact ⟨W, h0, hs, fun q ↦ hv (e q)⟩

lemma goodPrime_spec (cp : CertProv K) {fK : CPoly K} {n : ℕ} {r : ℕ} {α β : Fin r → K} {p : ℕ}
    (h : goodPrime redAt cp fK n α β p = true) :
    ∃ hpr : p.Prime, ∃ R : RedFns p K, redAt p = some R ∧
      ∃ (g : ℕ) (xs ys : List (ZMod p)) (ζ0 : ZMod p) (lam : List (List (ZMod p))),
        haveI : Fact p.Prime := ⟨hpr⟩; supCheckR p R fK n g α β xs ys ζ0 lam := by
  unfold goodPrime at h
  split_ifs at h with hpr
  refine ⟨hpr, ?_⟩
  split at h
  · rename_i R hR
    split at h
    · rename_i c hc
      haveI : Fact p.Prime := ⟨hpr⟩
      exact ⟨R, hR, c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2, goodCheck_spec h⟩
    · cases h
  · cases h

set_option maxHeartbeats 1600000 in
/-- **The torsion oracle is correct** (any certificate provider). -/
theorem torsOracleC_spec [CharZero K] (cp : CertProv K)
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p K), redAt p = some R →
      ∃ φ : K →+* ℚ_[p], RedValid p R φ)
    (ps : List ℕ) (bound : ℕ) {fK : CPoly K} {n : ℕ} (hsq : Squarefree (CPoly.toPoly fK))
    (hcop : Nat.Coprime n (fK.length - 1)) :
    TorsSpecN fK n (torsOracleC redAt cp ps bound fK n) := by
  intro r α β mq hv hinj
  set l := gammaL α β mq 1 with hl
  have hlen : l.length = r := by simp [hl, gammaL]
  set e : Fin l.length ≃ Fin r := finCongr hlen with he
  have hget : ∀ q : Fin l.length, l.get q = (α (e q), β (e q), 1 * mq (e q)) := by
    intro q
    simp [hl, gammaL, he]
    exact ⟨rfl, rfl, rfl⟩
  set α' : Fin l.length → K := fun q ↦ (l.get q).1 with hα'
  set β' : Fin l.length → K := fun q ↦ (l.get q).2.1 with hβ'
  set mu' : Fin l.length → ℕ := fun q ↦ (l.get q).2.2 with hmu'
  have eα : α' = fun q ↦ α (e q) := funext fun q ↦ by simp only [hα', hget]
  have eβ : β' = fun q ↦ β (e q) := funext fun q ↦ by simp only [hβ', hget]
  have eμ : mu' = fun q ↦ mq (e q) := funext fun q ↦ by simp only [hmu', hget, one_mul]
  have hiff : ∀ N, PrincipalMulN (CPoly.toPoly fK) n (fK.length - 1) α' β' mu' N ↔
      PrincipalMulN (CPoly.toPoly fK) n (fK.length - 1) α β mq N := fun N ↦ by
    rw [eα, eβ, eμ]; exact principalMulN_reindex _ _ _ e α β mq N
  have hv' : ∀ i, β' i ≠ 0 ∧ β' i ^ n = (CPoly.toPoly fK).eval (α' i) := fun i ↦ by
    rw [eα, eβ]; exact hv (e i)
  have hinj' : Function.Injective fun i ↦ (α' i, β' i) := by
    intro i j h
    rw [eα, eβ] at h
    exact e.injective (hinj h)
  show (∀ N, torsOracleC redAt cp ps bound fK n l = some (some N) → _) ∧
    (torsOracleC redAt cp ps bound fK n l = some none → _)
  unfold torsOracleC
  simp only []
  split
  · rename_i p hp
    split
    · rename_i q hq
      have hgp := List.find?_some hp
      have hgq := List.find?_some hq
      have hqp : q ≠ p := by
        have := List.mem_of_find?_eq_some hq
        simpa using (List.mem_filter.mp this).2
      obtain ⟨hpr, Rp, hRp, gp, xsp, ysp, ζp, lamp, hcp⟩ := goodPrime_spec redAt cp hgp
      obtain ⟨hqr, Rq, hRq, gq, xsq, ysq, ζq, lamq, hcq⟩ := goodPrime_spec redAt cp hgq
      haveI : Fact p.Prime := ⟨hpr⟩
      haveI : Fact q.Prime := ⟨hqr⟩
      obtain ⟨φp, hφp⟩ := hred p Rp hRp
      obtain ⟨φq, hφq⟩ := hred q Rq hRq
      have hspec := torsDecideR_spec (Ne.symm hqp) Rp φp hφp Rq φq hφq hsq hcop mu' hinj' hv'
        bound hcp hcq
      unfold torsWith
      rw [dif_pos hpr, dif_pos hqr]
      simp only [hRp, hRq]
      refine ⟨fun N hN ↦ ?_, fun h N hN hP ↦ hspec.2 h N hN ((hiff N).mpr hP)⟩
      obtain ⟨h1, h2⟩ := hspec.1 N hN
      exact ⟨h1, (hiff N).mp h2⟩
    · exact ⟨fun N hN ↦ (by cases hN), fun h ↦ (by cases h)⟩
  · exact ⟨fun N hN ↦ (by cases hN), fun h ↦ (by cases h)⟩

/-- **The search torsion oracle is correct.** -/
theorem torsOracle_spec [CharZero K]
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p K), redAt p = some R →
      ∃ φ : K →+* ℚ_[p], RedValid p R φ)
    (ps : List ℕ) (bound : ℕ) {fK : CPoly K} {n : ℕ} (hsq : Squarefree (CPoly.toPoly fK))
    (hcop : Nat.Coprime n (fK.length - 1)) :
    TorsSpecN fK n (torsOracle redAt ps bound fK n) :=
  torsOracleC_spec redAt (searchCert fK n) hred ps bound hsq hcop

end Spec

section NF

/-- The reductions of a number field `ℚ[θ]/(M)` (`M = mZ` over `ℤ`): a simple root of `M` mod `p`. -/
def nfRedAt {M : CPoly ℚ} (mZ : List ℤ) (p : ℕ) : Option (RedFns p (NFC.NF M)) :=
  ((zmodElems p).find? fun s ↦ evalC (Jac.castL p mZ) s == 0 &&
    evalC (CPoly.deriv (Jac.castL p mZ)) s != 0).map fun s ↦ nfFns p s

lemma nfRedAt_valid {M : CPoly ℚ} [Fact (Irreducible (toPoly M))] (mZ : List ℤ)
    (hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ)) (p : ℕ) [Fact p.Prime]
    (R : RedFns p (NFC.NF M)) (h : nfRedAt mZ p = some R) :
    ∃ φ : NFC.NF M →+* ℚ_[p], RedValid p R φ := by
  unfold nfRedAt at h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  have hc := List.find?_some hs
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  refine nfFns_valid p (toPoly mZ) hmZ s ?_ ?_
  · rw [← Jac.castL_eq, ← evalC_eq]; exact hc.1
  · rw [← Polynomial.derivative_map, ← Jac.castL_eq, ← CPoly.toPoly_deriv, ← evalC_eq]; exact hc.2

end NF

end Sup
