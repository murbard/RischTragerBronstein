import RischTragerBronstein.Torsion.Front
import Mathlib.Data.Rat.Encodable

/-!
# A total decision by exhaustive certificate search

The automatic pipeline `decideCurveQ` computes certificates with heuristic searches (Newton–Puiseux
recursion, integral-basis loop, number-field extension loop, prime search); proving that each of
them always succeeds is hard. `decideEnum` is the brute-force alternative: it enumerates **all**
certificates `(M, pts, inf, ws, twps)` (a number field `ℚ[γ]/(M)`, branch data at the fibres and
at infinity, logarithmic witnesses, non-torsion witnesses) through an `Encodable` instance and runs
the sound check `decideLogTP` on each.

* **`decideEnum_spec`**: every answer is correct (soundness of `decideLogTP`);
* **`decideEnum_complete`**: if some valid certificate exists, the search answers for every large
  bound;
* `decideTotal`: the pipeline first, then the exhaustive search; **`decideTotal_spec`**,
  **`decideTotal_complete`**.

So the decision is total as soon as **valid certificates exist** (`CertExists`): completeness is
reduced to existence theorems (Puiseux expansions, integral bases, good primes, `m_p`, failed
tests, logarithmic witnesses), without analysing the searches.
-/

open Polynomial

namespace Curves

open CPoly Sup EllQuad.QCoords

section Enc

/-- `ZMod p` is `ℤ` or `Fin p`. -/
def zmodEncodable : (p : ℕ) → Encodable (ZMod p)
  | 0 => (inferInstance : Encodable ℤ)
  | n + 1 => (inferInstance : Encodable (Fin (n + 1)))

instance (p : ℕ) : Encodable (ZMod p) := zmodEncodable p

variable {F : Type*} [Encodable F]

instance : Encodable (BranchCert F) :=
  Encodable.ofEquiv (ℕ × List (CPoly F) × ℕ)
    ⟨fun c ↦ (c.N, c.ys, c.prec), fun t ↦ ⟨t.1, t.2.1, t.2.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance : Encodable (IntBasisCert F) :=
  Encodable.ofEquiv (List (BPoly F) × CPoly F × List ℕ × List (F × BranchCert F × List (List F)) ×
      BranchCert F × List (List F))
    ⟨fun c ↦ (c.Bc, c.Dc, c.δL, c.pts, c.infc, c.Linf),
      fun t ↦ ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance : Encodable (GlobalCert F) :=
  Encodable.ofEquiv (BPoly F × ℕ × ℕ × ℕ × IntBasisCert F × F × List F × List (List F) ×
      List (BranchCert F) × List (List ℕ) × ℕ)
    ⟨fun c ↦ (c.Fc, c.n, c.k, c.kD, c.I, c.aE, c.αL, c.yL, c.cΓ, c.ΓL, c.cdeg),
      fun t ↦ ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
        t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩

instance : Encodable (PlaceCert F) :=
  Encodable.ofEquiv (List (F × ℕ) × List (ℕ × ℕ × CPoly F × ℕ) × List (List (ℕ × ℕ × F)) ×
      List ℕ × List ℕ × List ℕ × ℕ × List ℕ)
    ⟨fun c ↦ (c.fib, c.pl, c.rt, c.Γp, c.cf, c.dΓ, c.cΓ, c.tp),
      fun t ↦ ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
        t.2.2.2.2.2.2.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance : Encodable (LogWit F) :=
  Encodable.ofEquiv (ℕ × BPoly F × CPoly F)
    ⟨fun c ↦ (c.m, c.W, c.Q), fun t ↦ ⟨t.1, t.2.1, t.2.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance (p : ℕ) : Encodable (PlaceCert.PrimeData p) :=
  Encodable.ofEquiv (ℕ × List (List (ZMod p)))
    ⟨fun c ↦ (c.mp, c.Gw), fun t ↦ ⟨t.1, t.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance (p : ℕ) : Encodable (PrimeCert p) :=
  Encodable.ofEquiv (List (ZMod p × BranchCert (ZMod p) × List (List (ZMod p))) ×
      BranchCert (ZMod p) × List (List (ZMod p)) × List (ZMod p) × List (List (ZMod p)) ×
      List (List (ZMod p)) × List (List (List (ZMod p))) × List (BranchCert (ZMod p)) × ℕ ×
      List (List (ZMod p)) × Option (ZMod p) × ℕ)
    ⟨fun c ↦ (c.pts, c.infc, c.Linf, c.xs, c.ys, c.lam, c.Ls, c.cΓ, c.mp, c.Gw, c.aI, c.irrP),
      fun t ↦ ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
        t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.1,
        t.2.2.2.2.2.2.2.2.2.2.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The data of a non-torsion witness at places, grouped by the pair of primes. -/
abbrev TorsWitPData (F : Type*) [Field F] [CharZero F] [EllQuad.QCoords F] : Type _ :=
  GlobalCert F × PlaceCert F × List ℤ × ℕ × Fin (dim F) ×
    (Σ pq : ℕ × ℕ, PrimeCert pq.1 × PrimeCert pq.2 × PlaceCert.PrimeData pq.1 ×
      PlaceCert.PrimeData pq.2) × ℕ × List (List F)

/-- Non-torsion witnesses as data. -/
def torsWitPEquiv (F : Type*) [Field F] [CharZero F] [EllQuad.QCoords F] :
    TorsWitP F ≃ TorsWitPData F where
  toFun w := (w.T, w.Pc, w.eL, w.s, w.j₀, ⟨(w.p, w.q), (w.Pp, w.Pq, w.Qp, w.Qq)⟩, w.Pb, w.Lm)
  invFun := fun ⟨T, Pc, eL, s, j₀, ⟨⟨p, q⟩, ⟨Pp, Pq, Qp, Qq⟩⟩, Pb, Lm⟩ ↦
    ⟨T, Pc, eL, s, j₀, p, q, Pp, Pq, Qp, Qq, Pb, Lm⟩
  left_inv _ := rfl
  right_inv := fun ⟨_, _, _, _, _, ⟨⟨_, _⟩, ⟨_, _, _, _⟩⟩, _, _⟩ ↦ rfl

instance (F : Type*) [Field F] [CharZero F] [EllQuad.QCoords F] [Encodable F] :
    Encodable (TorsWitP F) :=
  Encodable.ofEquiv _ (torsWitPEquiv F)

end Enc

section NF

/-- The number fields `ℚ[γ]/(M)` with a certified irreducible `M`. -/
abbrev IrrQ : Type := {M : CPoly ℚ // Kron.irredQ M = true}

instance (M : CPoly ℚ) : Encodable (NFC.NF M) :=
  inferInstanceAs (Encodable {l : CPoly ℚ // NFC.norm M l = l})

/-- A certificate over the number field of `M`: branch data at the fibres and at infinity,
logarithmic witnesses, non-torsion witnesses, and optionally a Möbius transformation
`t = 1/(x − e)` (parameters `e, k₀, D_A` of `mobCheck` and the weight of the transformed problem)
to which the other data refer. -/
def CertData (M : IrrQ) : Type :=
  haveI : Fact (Irreducible (toPoly M.1)) := ⟨Kron.irredQ_sound _ M.2⟩
  List (NFC.NF M.1 × BranchCert (NFC.NF M.1)) × BranchCert (NFC.NF M.1) ×
    List (LogWit (NFC.NF M.1)) × List (TorsWitP (NFC.NF M.1)) × Option (NFC.NF M.1 × ℕ × ℕ × ℕ)

instance (M : IrrQ) : Encodable (CertData M) := by
  haveI : Fact (Irreducible (toPoly M.1)) := ⟨Kron.irredQ_sound _ M.2⟩
  unfold CertData
  exact inferInstance

/-- **The certificates** of the decision for curves over `ℚ`. -/
abbrev CertQ : Type := Σ M : IrrQ, CertData M

/-- The Möbius transform `t = 1/(x − e)`, `w = y t^{k₀}` of `P` (weight `k'`, certificates
`pts`, `inf`), as checked by `mobCheck`. -/
def CurveProb.mobT {F : Type*} [Field F] [DecidableEq F] (P : CurveProb F) (e : F) (k₀ DA k' : ℕ)
    (pts : List (F × BranchCert F)) (inf : BranchCert F) : CurveProb F :=
  ⟨invB (shiftB P.Fc e) k₀ (k₀ * P.n), P.n, k', mobA P.A e k₀ DA,
    mul (reflectC (P.D.length - 1) (compC P.D (shiftC e 1))) (xPowC (DA + 2 - (P.D.length - 1))),
    pts, inf⟩

/-- The answer certified by a certificate (`none` if it does not pass). -/
def CertQ.run (P0 : CurveProb ℚ) (c : CertQ) : Option Bool :=
  haveI : Fact (Irreducible (toPoly c.1.1)) := ⟨Kron.irredQ_sound _ c.1.2⟩
  let d : List (NFC.NF c.1.1 × BranchCert (NFC.NF c.1.1)) × BranchCert (NFC.NF c.1.1) ×
      List (LogWit (NFC.NF c.1.1)) × List (TorsWitP (NFC.NF c.1.1)) ×
      Option (NFC.NF c.1.1 × ℕ × ℕ × ℕ) := c.2
  match d.2.2.2.2 with
  | none => decideLogTP (redAtM c.1.1) (P0.baseChange (algebraMap ℚ (NFC.NF c.1.1)) P0.k d.1 d.2.1)
      d.2.2.1 [] d.2.2.2.1
  | some (e, k₀, DA, k') =>
      let P := P0.baseChange (algebraMap ℚ (NFC.NF c.1.1)) P0.k [] ⟨1, [], 0⟩
      if mobCheck P (P.mobT e k₀ DA k' d.1 d.2.1) e k₀ DA then
        decideLogTP (redAtM c.1.1) (P.mobT e k₀ DA k' d.1 d.2.1) d.2.2.1 [] d.2.2.2.1
      else none

/-- **The exhaustive search** over the first `N` certificates. -/
def decideEnum (P0 : CurveProb ℚ) (N : ℕ) : Option Bool :=
  (List.range N).findSome? fun k ↦ (Encodable.decode (α := CertQ) k).bind (CertQ.run P0)

/-- **The total decision**: the automatic pipeline, then the exhaustive search. -/
def decideTotal (Fc A : BPoly ℚ) (D : CPoly ℚ) (N : ℕ) : Option Bool :=
  (decideCurveQ Fc A D).or (decideEnum (curveProbQ Fc A D) N)

/-- Valid certificates exist for the problem `P0`. -/
def CertExists (P0 : CurveProb ℚ) : Prop := ∃ c : CertQ, (c.run P0).isSome

end NF

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

open IntermediateField Differential

/-- **Every certificate is sound.** -/
theorem CertQ.run_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (P0 : CurveProb ℚ)
    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc))) (c : CertQ) (b : Bool)
    (h : c.run P0 = some b) :
    HasElementaryIntegral ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true := by
  obtain ⟨⟨M, hM⟩, d⟩ := c
  haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound _ hM⟩
  set ι : NFC.NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NFC.NF M) (M := Kc)).toRingHom
  have hι : ι.comp (algebraMap ℚ (NFC.NF M)) = algebraMap ℚ Kc := Subsingleton.elim _ _
  obtain ⟨pts, inf, ws, twps, mob⟩ := d
  have hSF' : ∀ pts inf, S.F = (toB (P0.baseChange (algebraMap ℚ (NFC.NF M)) P0.k pts inf).Fc).map
      (mapRingHom ι) := fun pts inf ↦ by
    rw [hSF, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp, hι]
  cases mob with
  | none =>
    have key := decideLogTP_spec hC S hx hgen (redAtM M) (redAtM_valid M) _ ι (hSF' pts inf) ws []
      twps b h
    rwa [S.fE_baseChange, hι] at key
  | some q =>
    obtain ⟨e, k₀, DA, k'⟩ := q
    simp only [CertQ.run] at h
    split_ifs at h with hmob
    have key := decideLogTP_mob_spec hC S hx hgen (redAtM M) (redAtM_valid M) _ _ ι
      (hSF' [] ⟨1, [], 0⟩) e k₀ DA hmob ws [] twps b h
    rwa [S.fE_baseChange, hι] at key

/-- **The exhaustive search is sound.** -/
theorem decideEnum_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (P0 : CurveProb ℚ)
    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc))) (N : ℕ) (b : Bool)
    (h : decideEnum P0 N = some b) :
    HasElementaryIntegral ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true := by
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨c, -, hc⟩ := Option.bind_eq_some_iff.mp hk
  exact CertQ.run_spec hC S hx hgen P0 hSF c b hc

/-- **The exhaustive search is complete**: once a valid certificate exists, it answers for every
large bound. -/
theorem decideEnum_complete (P0 : CurveProb ℚ) (h : CertExists P0) :
    ∃ N₀, ∀ N, N₀ ≤ N → (decideEnum P0 N).isSome := by
  obtain ⟨c, hc⟩ := h
  refine ⟨Encodable.encode c + 1, fun N hN ↦ ?_⟩
  unfold decideEnum
  rw [List.findSome?_isSome_iff]
  refine ⟨Encodable.encode c, List.mem_range.mpr (by omega), ?_⟩
  rw [Encodable.encodek]
  simpa using hc

/-- **The total decision is sound.** -/
theorem decideTotal_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (Fc A : BPoly ℚ) (D : CPoly ℚ)
    (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc))) (N : ℕ) (b : Bool)
    (h : decideTotal Fc A D N = some b) :
    HasElementaryIntegral ((S.fE (curveProbQ Fc A D) (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) ↔
      b = true := by
  unfold decideTotal at h
  cases h1 : decideCurveQ Fc A D with
  | some b' =>
    rw [h1, Option.some_or] at h
    obtain rfl := Option.some.inj h
    exact decideCurveQ_spec hC S hx hgen Fc A D hSF 4 b' h1
  | none =>
    rw [h1, Option.none_or] at h
    exact decideEnum_spec hC S hx hgen _ hSF N b h

/-- **The total decision answers** for every large bound, as soon as valid certificates exist. -/
theorem decideTotal_complete (Fc A : BPoly ℚ) (D : CPoly ℚ) (h : CertExists (curveProbQ Fc A D)) :
    ∃ N₀, ∀ N, N₀ ≤ N → (decideTotal Fc A D N).isSome := by
  obtain ⟨N₀, hN₀⟩ := decideEnum_complete _ h
  refine ⟨N₀, fun N hN ↦ ?_⟩
  unfold decideTotal
  cases h1 : decideCurveQ Fc A D with
  | some b' => simp
  | none => rw [Option.none_or]; exact hN₀ N hN

end Main

end Curves
