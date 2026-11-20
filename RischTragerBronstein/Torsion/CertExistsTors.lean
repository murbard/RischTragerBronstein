import RischTragerBronstein.Torsion.CertExists
import RischTragerBronstein.Torsion.LogWitB
import RischTragerBronstein.Torsion.RaiseValid

/-!
# Certificates exist when every residue coordinate is torsion

* `witCheck_of_tors`: if for every coordinate `j` the `coord_j`-component of the residue divisor is
  torsion (`TorsOrd`), there are witnesses `ws` accepted by `witCheck` for every valid problem with
  the same curve, integrand, points and ramification indices and large precisions;
* `certExists_of_tors`: then valid certificates exist (`CertExists`), so the total decision answers;
* **`certExists_of_elementary`**: in particular for every integrand with an elementary integral
  (torsion from Liouville's theorem and Abel's theorem, `curve_lift`, `liouville_C`, `curve_abel`).
-/

open Polynomial HahnSeries IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup NFC Differential

section Wit

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L)
variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- **Witnesses for all coordinates from torsion data.** -/
theorem witCheck_of_tors (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (hV : P.ValidFacts)
    (hT : ∀ j : Fin (dim F), ∃ m, 0 < m ∧ ∃ Λ : K →ₗ[ℚ] ℚ,
      (∀ r : F, Λ (algebraMap C K (ψ₀ r)) = coord j r) ∧ ∃ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 ∧
        S.TorsOrdStd P ψ₀ m w Λ) :
    ∃ (ws : List (LogWit F)) (B : ℕ), ∀ P' : CurveProb F, P'.Fc = P.Fc → P'.n = P.n →
      P'.k = P.k → P'.A = P.A → P'.D = P.D →
      P'.pts.map (fun ac ↦ (ac.1, ac.2.N)) = P.pts.map (fun ac ↦ (ac.1, ac.2.N)) →
      P'.inf.N = P.inf.N → P'.ValidFacts → (∀ ac ∈ P'.pts, B ≤ ac.2.prec) → B ≤ P'.inf.prec →
      P'.witCheck ws = true := by
  classical
  have h : ∀ j : Fin (dim F), ∃ p : LogWit F × ℕ, ∀ P' : CurveProb F, P'.Fc = P.Fc →
      P'.n = P.n → P'.k = P.k → P'.A = P.A → P'.D = P.D →
      P'.pts.map (fun ac ↦ (ac.1, ac.2.N)) = P.pts.map (fun ac ↦ (ac.1, ac.2.N)) →
      P'.inf.N = P.inf.N → P'.ValidFacts → (∀ ac ∈ P'.pts, p.2 ≤ ac.2.prec) → p.2 ≤ P'.inf.prec →
      P'.witOK p.1 j = true := fun j ↦ by
    obtain ⟨m, hm, Λ, hΛ, w, hw, hord⟩ := hT j
    obtain ⟨W, Q, B, hB⟩ := S.witOK_of_tors P ψ₀ hSF hV j m hm Λ hΛ w hw hord
    exact ⟨(⟨m, W, Q⟩, B), hB⟩
  choose p hp using h
  refine ⟨List.ofFn fun j ↦ (p j).1, ∑ j, (p j).2,
    fun P' hFc hn hk hA hD hpts hinfN hV' hB hBi ↦ ?_⟩
  simp only [CurveProb.witCheck, List.all_eq_true]
  intro j _
  have hle : (p j).2 ≤ ∑ j, (p j).2 :=
    Finset.single_le_sum (f := fun j ↦ (p j).2) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have hwa : CurveProb.witAt (List.ofFn fun j ↦ (p j).1) j = (p j).1 := by
    rw [CurveProb.witAt, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  rw [hwa]
  exact hp j P' hFc hn hk hA hD hpts hinfN hV' (fun ac hac ↦ hle.trans (hB ac hac)) (hle.trans hBi)

end CurveData

end Wit

section Run

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

lemma decideLog_isSome (P : CurveProb F) (ws : List (LogWit F)) (hv : P.valid = true)
    (hw : P.witCheck ws = true) : (P.decideLog ws).isSome := by
  unfold CurveProb.decideLog
  rw [if_pos hv]
  cases linSolve P.cols P.rhs with
  | none => rfl
  | some cs =>
    simp only
    split_ifs <;> rfl

lemma decideLogTP_isSome (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F)
    (ws : List (LogWit F)) (tws : List (TorsWit F)) (twps : List (TorsWitP F))
    (h : (P.decideLog ws).isSome) : (decideLogTP redAt P ws tws twps).isSome := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  simp [decideLogTP, decideLogT, hb]

end Run

section Exists

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

/-- **Certificates exist when all residue coordinates are torsion**: given valid data over a
number field (the residue case of `certExists_or_residues`) and torsion data for every
coordinate on some model of the curve. -/
theorem certExists_of_tors (P0 : CurveProb ℚ) (M : CPoly ℚ) (hM : Kron.irredQ M = true)
    (pts : List (NF M × BranchCert (NF M))) (inf : BranchCert (NF M))
    (hvalid : (haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).valid) = true)
    (S : CurveData C L) (ψ₀ : (haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      NF M →+* C))
    (hSF : haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      S.F = (toB (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).Fc).map (mapRingHom ψ₀))
    (hT : haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∀ j : Fin (dim (NF M)), ∃ m, 0 < m ∧ ∃ Λ : K →ₗ[ℚ] ℚ,
      (∀ r : NF M, Λ (algebraMap C K (ψ₀ r)) = coord j r) ∧ ∃ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 ∧
        S.TorsOrdStd (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf) ψ₀ m w Λ) :
    CertExists P0 := by
  haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  set P := P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf with hP
  have hV := P.valid_spec hvalid
  obtain ⟨ws, B, hws⟩ := S.witCheck_of_tors P ψ₀ hSF hV hT
  obtain ⟨P', hFc, hn, hk, hA, hD, -, hpts, hB, hBi, hinfN, hv'⟩ := raise_valid P hvalid B
  have hP' : P' = P0.baseChange (algebraMap ℚ (NF M)) P0.k P'.pts P'.inf := by
    obtain ⟨Fc', n', k', A', D', pts', inf'⟩ := P'
    simp only at hFc hn hk hA hD
    subst hFc hn hk hA hD
    rfl
  have hwc := hws P' hFc hn hk hA hD hpts hinfN (P'.valid_spec hv') hB hBi
  refine ⟨⟨⟨M, hM⟩, (P'.pts, P'.inf, ws, [], none)⟩, ?_⟩
  dsimp only [CertQ.run]
  rw [← hP']
  exact decideLogTP_isSome _ _ _ _ _ (decideLog_isSome P' ws hv' hwc)

end Exists

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- **Certificates exist for every elementary integrand** (with valid shape): its residue divisors are torsion by Liouville's and Abel's theorems. -/
theorem certExists_of_elementary (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (P0 : CurveProb ℚ)
    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc))) (hS : P0.shapeOK = true)
    (hel : HasElementaryIntegral ((S.fE P0 (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E)) :
    CertExists P0 := by
  classical
  rcases certExists_or_residues P0 hS with h | ⟨M, hM, pts, inf, hvalid, -, -, -⟩
  · exact h
  haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  set P := P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf with hP
  set ι : NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NF M) (M := Kc)).toRingHom
  have hι : ι.comp (algebraMap ℚ (NF M)) = algebraMap ℚ Kc := Subsingleton.elim _ _
  have hSF' : S.F = (toB P.Fc).map (mapRingHom ι) := by
    rw [hSF, hP, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp, hι]
  have hel' : HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) := by
    rwa [hP, S.fE_baseChange, hι]
  refine curve_lift hC S hx hgen _ hel' ?_
  intro Cc L _ _ _ _ _ _ _ _ φ jE SL hCc hxc hconst hxL hyL hFL hjd hjC hjE v hv ιI sI d w hd hw heq
  have hSFL : SL.F = (toB P.Fc).map (mapRingHom (φ.comp ι)) := by
    rw [hFL, hSF', Polynomial.map_map, ← mapRingHom_comp]
  have hjf : jE (S.fE P ι : E) = (SL.fE P (φ.comp ι) : L) := by
    simp only [CurveData.fE, map_div₀]
    rw [S.jE_evXY SL φ jE hxL hyL hjC, S.jE_aeval SL φ jE hxL hjC, Polynomial.map_map,
      Polynomial.map_map, ← mapRingHom_comp]
  rw [hjf] at heq
  obtain ⟨dc, uu, hu, hu0, heq'⟩ := SL.liouville_C hconst _ v sI d w hd hw heq
  set Kb := AlgebraicClosure Cc
  haveI : CharZero Kb := charZero_of_injective_algebraMap (algebraMap Cc Kb).injective
  refine certExists_of_tors (K := Kb) P0 M hM pts inf hvalid SL (φ.comp ι) hSFL (fun j ↦ ?_)
  -- the functional `Λ` extending `coord j`
  have hinj : Function.Injective ((algebraMap Cc Kb).comp (φ.comp ι)) :=
    (algebraMap Cc Kb).injective.comp (φ.comp ι).injective
  set ιF : NF M →ₗ[ℚ] Kb := ((algebraMap Cc Kb).comp (φ.comp ι)).toRatAlgHom.toLinearMap with hιF
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ιF (LinearMap.ker_eq_bot.mpr hinj)
  set Λ : Kb →ₗ[ℚ] ℚ := (coord j).comp g with hΛdef
  have hΛ : ∀ r : NF M, Λ (algebraMap Cc Kb ((φ.comp ι) r)) = coord j r := fun r ↦ by
    have : g (ιF r) = r := by rw [← LinearMap.comp_apply, hg, LinearMap.id_apply]
    rw [hΛdef, LinearMap.comp_apply]
    exact congrArg (coord j) this
  obtain ⟨m, hm, w', hw0, hord⟩ := SL.curve_abel (K := Kb) hCc hxc _ v (SL.fE P (φ.comp ι)).2 hv sI
    dc uu hu hu0 heq' Λ
  exact ⟨m, hm, Λ, hΛ, w', hw0, CurveData.TorsOrd.std SL (fun Xh hX g hg hgX Y hY ↦ hord Xh hX g hg hgX Y hY)⟩

/-- **The total decision answers for every elementary integrand** (valid shape): with the soundness `decideTotal_spec`, the answer is `true`. -/
theorem decideTotal_complete_of_elementary (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E)
    (hx : S.x′ = 1) (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) (Fc A : BPoly ℚ) (D : CPoly ℚ)
    (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))
    (hS : (curveProbQ Fc A D).shapeOK = true)
    (hel : HasElementaryIntegral ((S.fE (curveProbQ Fc A D) (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E)) :
    ∃ N₀, ∀ N, N₀ ≤ N → (decideTotal Fc A D N).isSome :=
  decideTotal_complete Fc A D
    (certExists_of_elementary hC S hx hgen (curveProbQ Fc A D) hSF hS hel)

/-- **Certificates exist unless a residue coordinate is non-torsion**: either valid certificates
exist, or there are valid branch data over a number field `NF M` and a coordinate `j` of the
residues whose residue divisor is not torsion (no `w ≠ 0` has orders `m · Λ(res f dx)` along all
branches, for any `ℚ`-linear `Λ` extending `coord j`). -/
theorem certExists_or_nonTorsion (S : CurveData Kc E) (P0 : CurveProb ℚ)
    (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc))) (hS : P0.shapeOK = true) :
    CertExists P0 ∨ ∃ M : CPoly ℚ, ∃ hM : Kron.irredQ M = true,
      haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∃ (pts : List (NF M × BranchCert (NF M))) (inf : BranchCert (NF M)),
        (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).valid = true ∧
        ∃ j : Fin (dim (NF M)), ∀ m, 0 < m → ∀ Λ : Kc →ₗ[ℚ] ℚ,
          (∀ r : NF M, Λ ((IsAlgClosed.lift (R := ℚ) (S := NF M) (M := Kc)).toRingHom r) =
            coord j r) →
          ∀ w : Kc⟮S.x⟯⟮S.y⟯, w ≠ 0 →
            ¬ S.TorsOrdStd (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf)
              (IsAlgClosed.lift (R := ℚ) (S := NF M) (M := Kc)).toRingHom m w Λ := by
  classical
  rcases certExists_or_residues P0 hS with h | ⟨M, hM, pts, inf, hvalid, -, -, -⟩
  · exact Or.inl h
  haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  set ι : NF M →+* Kc := (IsAlgClosed.lift (R := ℚ) (S := NF M) (M := Kc)).toRingHom with hιdef
  have hι : ι.comp (algebraMap ℚ (NF M)) = algebraMap ℚ Kc := Subsingleton.elim _ _
  have hSF' : S.F = (toB (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).Fc).map
      (mapRingHom ι) := by
    rw [hSF, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp, hι]
  by_cases hall : ∀ j : Fin (dim (NF M)), ∃ m, 0 < m ∧ ∃ Λ : Kc →ₗ[ℚ] ℚ,
      (∀ r : NF M, Λ (algebraMap Kc Kc (ι r)) = coord j r) ∧ ∃ w : Kc⟮S.x⟯⟮S.y⟯, w ≠ 0 ∧
        S.TorsOrdStd (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf) ι m w Λ
  · exact Or.inl (certExists_of_tors (K := Kc) P0 M hM pts inf hvalid S ι hSF' hall)
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    refine Or.inr ⟨M, hM, pts, inf, hvalid, j, fun m hm Λ hΛ w hw hT ↦ ?_⟩
    exact hj m hm Λ (fun r ↦ by rw [Algebra.algebraMap_self, RingHom.id_apply]; exact hΛ r) w hw hT

end Main

end Curves
