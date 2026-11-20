import RischTragerBronstein.Mixed.KBMain
import RischTragerBronstein.Mixed.KZDecides

/-!
# Pole factors algebraic over the base: the decision answers

After a change of base curve (`base_change`), `kzDecideL` over the new base answers for every large
bound at suitable residues, outside the Mordell–Weil case (`kz_decided_bc`, from
`kzDecideL_decides` on the new tower and `kzDecide_bc_correct`).
-/

open Polynomial Differential IntermediateField CPoly CPoly.Kron Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

open Classical in
/-- **Pole factors algebraic over the base are decided** (accepted data on the new base curve),
outside the Mordell–Weil case. -/
theorem kz_decided_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (hdeg' : (toB Fc').natDegree = cvN Fc') (lv' : (m : ℕ) → LC m)
    (m : ℕ) (hn : T.n = m + 1) (hc' : certC Fc' (tauK Fc' Yc ks) lv' (m + 1) = true)
    {g : LC m} (hk : ks m = .exp g) (n j : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc' m M)))] [Fact (Irreducible (toPoly (liftQ Fc' (m + 1) M)))]
    (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A : GPoly (LC m))
    (hsqc : GPoly.squarefreeCheck (MO Fc' (tauK Fc' Yc ks) m) (A.map (tauC Fc' Yc m)) = true)
    (hdegpos : 0 < degG (MO Fc' (tauK Fc' Yc ks) m) (A.map (tauC Fc' Yc m)))
    (hcop : Nat.Coprime n (degG (MO Fc' (tauK Fc' Yc ks) m) (A.map (tauC Fc' Yc m))))
    (θ : L) (hθ : θ ^ n = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (f : LC (m + 1)) (B' : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc' m M)) (dC : GPoly (LC m))
    (hf : tauC Fc' Yc (m + 1) f =
      ((B', kzDen Fc' (tauK Fc' Yc ks) m (A.map (tauC Fc' Yc m)) kt l dC) : LC (m + 1)))
    (hn1 : 1 < n) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n) (hr0 : cs.length ≠ 0)
    (hok : kzOK Fc' (tauK Fc' Yc ks) m M (A.map (tauC Fc' Yc m)) B' kt l cs dC = true)
    (hF : kzConst Fc' (tauK Fc' Yc ks) m n j M (tauC Fc' Yc m g) (A.map (tauC Fc' Yc m)) B' kt l
        cs = true →
      kzFieldOK Fc' (tauK Fc' Yc ks) m n j M (tauC Fc' Yc m g) (A.map (tauC Fc' Yc m)) B' kt l cs
        zN gs = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (∃ b, kzDecideL Fc' (tauK Fc' Yc ks) lv' m n j (tauC Fc' Yc m g) M zN gs
          (A.map (tauC Fc' Yc m)) B' kt l cs dC (primesBelow Bd) Bd rs = some b ∧
        (HasElementaryIntegral (T.ev (m + 1) f * θ ^ j) ↔ b = true)) ∨
      ((((List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)).map
          (kzTorsC Fc' (tauK Fc' Yc ks) m n j M (tauC Fc' Yc m g) (A.map (tauC Fc' Yc m)) B' kt l
            cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs)).any (· == some none) = true ∧
        ((krZ Fc' (tauK Fc' Yc ks) lv' m n (A.map (tauC Fc' Yc m)) = none ∧ ∃ ℓ, ℓ.Prime ∧ ℓ ∣ n ∧
            (krZ Fc' (tauK Fc' Yc ks) lv' m ℓ (A.map (tauC Fc' Yc m))).isSome) ∨
          ∃ z, krZ Fc' (tauK Fc' Yc ks) lv' m n (A.map (tauC Fc' Yc m)) = some z ∧ ∃ k < n,
            kyZeroQ Fc' (tauK Fc' Yc ks) m n M (A.map (tauC Fc' Yc m)) zN z
              (kyKap Fc' (tauK Fc' Yc ks) m n (A.map (tauC Fc' Yc m)) z)
              (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs k = some none)) := by
  obtain ⟨L', _, _, _, _, _, -, T', hTn, -, -, -, -⟩ :=
    T.base_change Q Fc' Yc hbc hmon' hlen' hd' hgeo
  have hk' : tauK Fc' Yc ks m = .exp (tauC Fc' Yc m g) := by
    unfold tauK; rw [hk]
  obtain ⟨rs, B0, h⟩ := T'.kzDecideL_decides hmon' hdeg' m (by rw [hTn, hn]) hc' hk' n j M zN gs
    (A.map (tauC Fc' Yc m)) hsqc hdegpos hcop B' kt l cs dC hn1 hj0 hjn hjc hr0 hok hF
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  rcases h Bd hBd with h1 | h1
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    exact Or.inl ⟨b, hb, MTower.kzDecide_bc_correct T Q Fc' Yc hbc hmon' hlen' hd' hgeo hdeg' lv' m hn hc'
      hk n j M zN gs A hsqc hdegpos hcop θ hθ hgen f B' kt l cs dC hf _ _ rs b hb⟩
  · exact Or.inr h1

end Curves.MT
