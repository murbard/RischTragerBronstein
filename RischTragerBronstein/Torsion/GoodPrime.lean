import RischTragerBronstein.Torsion.GoodPrimeAux
import RischTragerBronstein.Torsion.IrrSpec
import RischTragerBronstein.Torsion.IrrSubset
import RischTragerBronstein.Torsion.IntBasisCheckR

/-!
# Good primes from certificates

`GlobalCert K`: a curve `F(x, y) = 0` over a computable field `K`, an integral basis with its
certificate, an Eisenstein point, and a divisor `Γ − c ∞ₓ` supported at `K`-rational points of
`K`-split fibres (with certified unramified branches). `PrimeCert p`: for a prime `p` with a
certified reduction `R : RedFns p K`, the integral-basis certificate modulo `p`, base points with
their Hensel data, the non-speciality and determinant certificates, and a principal witness for
`m_p Γ̄`. `globalCheck` and `primeCheck` check everything.
-/

open Polynomial

namespace Curves

open CPoly Sup GTors

/-- The global data. -/
structure GlobalCert (K : Type*) where
  Fc : BPoly K
  n : ℕ
  k : ℕ
  kD : ℕ
  I : IntBasisCert K
  aE : K
  αL : List K
  yL : List (List K)
  cΓ : List (BranchCert K)
  ΓL : List (List ℕ)
  cdeg : ℕ

/-- The data at a prime. -/
structure PrimeCert (p : ℕ) where
  pts : List (ZMod p × BranchCert (ZMod p) × List (List (ZMod p)))
  infc : BranchCert (ZMod p)
  Linf : List (List (ZMod p))
  xs : List (ZMod p)
  ys : List (List (ZMod p))
  lam : List (List (ZMod p))
  Ls : List (List (List (ZMod p)))
  cΓ : List (BranchCert (ZMod p))
  mp : ℕ
  Gw : List (List (ZMod p))
  /-- a specialization `x = aI` with `F(aI, Y)` irreducible modulo `p`, certified by the absence of
  monic factors of degree `≤ n/2` (`none`: Eisenstein, or the subset certificate) -/
  aI : Option (ZMod p)
  /-- the precision of the subset certificate at the first base point (`0`: not used) -/
  irrP : ℕ

/-- The default branch certificate. -/
def dcert (F : Type*) : BranchCert F := ⟨1, [], 0⟩

section Defs

variable {K : Type*} [Field K] [DecidableEq K]

namespace GlobalCert

variable (T : GlobalCert K)

/-- The cover polynomial `disc · D · det [Bⱼ,ᵢ]` (`kD` bounds the degrees of the coefficients). -/
def G : CPoly K := mul (mul (discRC T.Fc T.n T.kD) T.I.Dc) (detC T.n T.I.Bc)

/-- The checks on the certified branches at the points of `Γ`. -/
def ptCheck {F : Type*} [Field F] [DecidableEq F] (Fc : BPoly F) (n : ℕ) (αs : List F)
    (ys : List (List F)) (cs : List (BranchCert F)) : Bool :=
  decide (ys.length = αs.length) && decide (cs.length = αs.length) && decide αs.Nodup &&
  (List.range αs.length).all fun j ↦
    decide ((ys.getD j []).length = n) && decide (ys.getD j []).Nodup &&
    certCheck Fc n (αs.getD j 0) (cs.getD j (dcert F)) &&
    decide ((cs.getD j (dcert F)).N = 1) && decide (1 ≤ (cs.getD j (dcert F)).prec) &&
    (List.range n).all fun k ↦
      decide ((((cs.getD j (dcert F)).ys.getD k []).getD 0 0) = (ys.getD j []).getD k 0) &&
      decide (evalB Fc (αs.getD j 0) ((ys.getD j []).getD k 0) = 0)

/-- Eisenstein at `x = aE`. -/
def eisCheck : Bool :=
  (List.range T.n).all (fun i ↦ decide (Kron.evalC (T.Fc.getD i []) T.aE = 0)) &&
  decide (Kron.evalC (CPoly.deriv (T.Fc.getD 0 [])) T.aE ≠ 0)

/-- **The global check.** -/
def globalCheck : Bool :=
  ibCheck T.Fc T.n T.k T.I T.G && normCheck T.n T.I && decide (T.I.Dc.getLast? = some 1) &&
  (List.range T.Fc.length).all (fun j ↦ decide ((T.Fc.getD j []).length ≤ T.kD + 1)) &&
  ptCheck T.Fc T.n T.αL T.yL T.cΓ &&
  decide (T.ΓL.length = T.αL.length) &&
  decide ((∑ j ∈ Finset.range T.αL.length, ∑ k ∈ Finset.range T.n, (T.ΓL.getD j []).getD k 0) =
    T.cdeg * T.n)

/-- **The global check with uncertified simple discriminant roots** (`ibCheckR`; sound in
characteristic `0`, which is where the global certificate lives). -/
def globalCheckR : Bool :=
  ibCheckR T.Fc T.n T.k T.I T.G && normCheck T.n T.I && decide (T.I.Dc.getLast? = some 1) &&
  (List.range T.Fc.length).all (fun j ↦ decide ((T.Fc.getD j []).length ≤ T.kD + 1)) &&
  ptCheck T.Fc T.n T.αL T.yL T.cΓ &&
  decide (T.ΓL.length = T.αL.length) &&
  decide ((∑ j ∈ Finset.range T.αL.length, ∑ k ∈ Finset.range T.n, (T.ΓL.getD j []).getD k 0) =
    T.cdeg * T.n)

end GlobalCert

variable {p : ℕ} [Fact p.Prime] (R : RedFns p K)

/-- The reduced integral-basis certificate. -/
def PrimeCert.Ip (T : GlobalCert K) (P : PrimeCert p) : IntBasisCert (ZMod p) :=
  ⟨T.I.Bc.map (redBL R), T.I.Dc.map R.red, T.I.δL, P.pts, P.infc, P.Linf⟩

/-- All coefficients are `p`-integral. -/
def okB (W : BPoly K) : Bool := W.all fun P ↦ P.all R.ok

/-- **The check at a prime.** -/
def primeCheck (T : GlobalCert K) (P : PrimeCert p) : Bool :=
  let Fp := redBL R T.Fc
  let Bp := T.I.Bc.map (redBL R)
  let Dp := T.I.Dc.map R.red
  let n := T.n
  let g := P.xs.length
  let αp := T.αL.map R.red
  let yp := T.yL.map (·.map R.red)
  -- integrality
  okB R T.Fc && T.I.Bc.all (okB R) && T.I.Dc.all R.ok && T.G.all R.ok && T.αL.all R.ok &&
  T.yL.all (·.all R.ok) && R.ok T.aE &&
  -- the reduced curve and its integral basis
  ibCheck Fp n T.k (P.Ip R T) (T.G.map R.red) &&
  (match P.aI with
    | none => T.eisCheck && decide (Kron.evalC (CPoly.deriv (Fp.getD 0 [])) (R.red T.aE) ≠ 0) ||
        decide (0 < P.irrP) && irrAt Fp n T.kD (P.xs.getD 0 0) (P.ys.getD 0 []) P.irrP
    | some a => noSmallFactor ((List.range p).map fun i : ℕ ↦ (i : ZMod p))
        (Fp.map fun c ↦ Kron.evalC c a) n) &&
  -- the base points
  decide ((∑ j ∈ Finset.range n, T.I.δL.getD j 0) + 1 = g + n) && decide P.xs.Nodup &&
  decide (P.ys.length = g) &&
  (List.range g).all (fun i ↦ decide ((P.ys.getD i []).length = n) && decide (P.ys.getD i []).Nodup &&
    decide (Kron.evalC Dp (P.xs.getD i 0) ≠ 0) &&
    (List.range n).all fun k ↦
      decide (evalB Fp (P.xs.getD i 0) ((P.ys.getD i []).getD k 0) = 0) &&
      decide (evalB (derivYB Fp) (P.xs.getD i 0) ((P.ys.getD i []).getD k 0) ≠ 0)) &&
  detCheck n g Bp P.xs P.ys P.Ls && nsCheck n g T.I.δL Bp P.xs P.ys P.lam &&
  -- the points of `Γ` modulo `p`
  decide αp.Nodup &&
  (List.range T.αL.length).all (fun j ↦ decide ((yp.getD j []).Nodup) &&
    decide (Kron.evalC Dp (αp.getD j 0) ≠ 0) &&
    (List.range g).all (fun i ↦ decide (αp.getD j 0 ≠ P.xs.getD i 0)) &&
    (List.range n).all fun k ↦
      decide (evalB (derivYB Fp) (αp.getD j 0) ((yp.getD j []).getD k 0) ≠ 0)) &&
  GlobalCert.ptCheck Fp n αp yp P.cΓ &&
  -- the principal witness for `m_p Γ̄`
  decide (1 ≤ P.mp) &&
  princWitCheck n (P.mp * T.cdeg) T.I.δL Bp Dp αp P.cΓ (T.ΓL.map (·.map (P.mp * ·))) P.Gw

end Defs

end Curves

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section PtSpec

variable {F : Type*} [Field F] [DecidableEq F] {C : Type*} [Field C]

/-- **The certified branches at the points of `Γ`.** -/
lemma ptCheck_spec (ψ₀ : F →+* C) {Fc : BPoly F} {n : ℕ} (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = n) {αs : List F} {ys : List (List F)} {cs : List (BranchCert F)}
    (h : GlobalCert.ptCheck Fc n αs ys cs = true) :
    ys.length = αs.length ∧ αs.Nodup ∧ ∀ j < αs.length,
      ((ys.getD j []).length = n ∧ (ys.getD j []).Nodup) ∧ ∃ Y : Fin n → PowerSeries C,
        (∀ k : Fin n, PowerSeries.constantCoeff (Y k) = ψ₀ ((ys.getD j []).getD k 0)) ∧
        ((toB Fc).map (mapRingHom ψ₀)).map (branchSub (C := C) (K := C) 1 (ψ₀ (αs.getD j 0))) =
          ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ C (Y k))) ∧
        (∀ k : Fin n, (PowerSeries.X : PowerSeries C) ^ (cs.getD j (dcert F)).prec ∣
          Y k - thetaT ψ₀ (toPoly ((cs.getD j (dcert F)).ys.getD k []))) ∧
        ∀ k < n, evalB Fc (αs.getD j 0) ((ys.getD j []).getD k 0) = 0 := by
  simp only [GlobalCert.ptCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨hyl, -⟩, hnd⟩, hj⟩ := h
  refine ⟨hyl, hnd, fun j hjl ↦ ?_⟩
  obtain ⟨⟨⟨⟨⟨hlen, hnd'⟩, hcert⟩, hN⟩, hprec⟩, hk⟩ := hj j hjl
  refine ⟨⟨hlen, hnd'⟩, ?_⟩
  obtain ⟨Y, hY, -, hs⟩ := certCheck_spec (K := C) Fc n hmon hdeg _ _ hcert ψ₀
  rw [Algebra.algebraMap_self, RingHom.id_comp] at hY
  rw [Algebra.algebraMap_self, RingHom.id_apply, hN] at hs
  refine ⟨Y, fun k ↦ ?_, hs, hY, fun k hk' ↦ (hk k hk').2⟩
  have := (PowerSeries.X_pow_dvd_iff.mp (hY k)) 0 hprec
  rw [map_sub, sub_eq_zero, coeff_thetaT, (hk k k.2).1,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  exact this

end PtSpec

end Curves

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section Model

variable {K : Type*} [Field K] [DecidableEq K]
variable {p : ℕ} [hp : Fact p.Prime] (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)

local notation "𝕜" => IsLocalRing.ResidueField ℤ_[p]
local notation "ρ" => IsLocalRing.residue ℤ_[p]

/-- `𝔽_p → 𝕜`. -/
noncomputable abbrev psiP : ZMod p →+* 𝕜 := (PadicInt.residueField (p := p)).symm.toRingHom

lemma residue_eq_psiP (z : ℤ_[p]) : ρ z = psiP (PadicInt.toZMod z) := by
  rw [PadicInt.toZMod_eq_residueField_comp_residue]
  simp

lemma mapRingHom_residue :
    mapRingHom ρ = (mapRingHom (psiP (p := p))).comp (mapRingHom PadicInt.toZMod) := by
  rw [Polynomial.mapRingHom_comp]
  congr 1
  exact RingHom.ext fun z ↦ residue_eq_psiP z

lemma okB_spec {W : BPoly K} (h : okB R W = true) : ∀ P ∈ W, ∀ c ∈ P, R.ok c = true := by
  simpa [okB, List.all_eq_true] using h

lemma zL_red {x : K} (hx : R.ok x = true) : PadicInt.toZMod (zL R φ hR x) = R.red x :=
  (zL_spec R φ hR hx).2

lemma zL_map {x : K} (hx : R.ok x = true) : algebraMap ℤ_[p] ℚ_[p] (zL R φ hR x) = φ x :=
  (zL_spec R φ hR hx).1.symm

lemma toZMod_evalW_lift (W : BPoly K) (hok : ∀ P ∈ W, ∀ c ∈ P, R.ok c = true) (a b : ℤ_[p]) :
    PadicInt.toZMod (evalW (toB (liftBL R φ hR W)) a b) =
      evalB (redBL R W) (PadicInt.toZMod a) (PadicInt.toZMod b) := by
  rw [← evalW_mapG, toB_liftBL_red R φ hR W hok, evalB_eq]
  rfl

lemma toZMod_evalW_deriv_lift (W : BPoly K) (hok : ∀ P ∈ W, ∀ c ∈ P, R.ok c = true)
    (a b : ℤ_[p]) :
    PadicInt.toZMod (evalW (derivative (toB (liftBL R φ hR W))) a b) =
      evalB (derivYB (redBL R W)) (PadicInt.toZMod a) (PadicInt.toZMod b) := by
  rw [← evalW_mapG, ← Polynomial.derivative_map, toB_liftBL_red R φ hR W hok, evalB_eq,
    toB_derivYB]
  rfl

lemma map_evalW_lift (W : BPoly K) (hok : ∀ P ∈ W, ∀ c ∈ P, R.ok c = true) (a b : ℤ_[p])
    (α β : K) (ha : algebraMap ℤ_[p] ℚ_[p] a = φ α) (hb : algebraMap ℤ_[p] ℚ_[p] b = φ β) :
    algebraMap ℤ_[p] ℚ_[p] (evalW (toB (liftBL R φ hR W)) a b) = φ (evalB W α β) := by
  rw [← evalW_mapG, toB_liftBL_map R φ hR W hok, ha, hb, evalW_mapG, evalB_eq]

lemma toZMod_eval_liftL (l : CPoly K) (hok : ∀ c ∈ l, R.ok c = true) (a : ℤ_[p]) :
    PadicInt.toZMod ((toPoly (liftL R φ hR l)).eval a) =
      Kron.evalC (l.map R.red) (PadicInt.toZMod a) := by
  rw [Sup.toZMod_eval, toPoly_liftL_red R φ hR l hok, Kron.evalC_eq]

/-- `toPoly` of a list whose last entry is `1` is monic. -/
lemma toPoly_monic_of_getLast {F : Type*} [Field F] (l : CPoly F) (h : l.getLast? = some 1) :
    (toPoly l).Monic := by
  obtain ⟨l', rfl⟩ : ∃ l', l = l' ++ [1] := by
    rcases List.eq_nil_or_concat l with h0 | ⟨l', b, rfl⟩
    · subst h0; simp at h
    · simp at h; subst h; exact ⟨l', by simp⟩
  have hc : (toPoly (l' ++ [1])).coeff l'.length = 1 := by
    rw [coeff_toPoly]; simp
  have hle : (toPoly (l' ++ [1])).natDegree ≤ l'.length := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_
    have : l'.length < i := by exact_mod_cast hi
    rw [coeff_toPoly, List.getD_eq_default _ _ (by simp; omega)]
  have hdeg : (toPoly (l' ++ [1])).natDegree = l'.length :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero))
  rw [Monic, leadingCoeff, hdeg, hc]

end Model

end Curves

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section Facts

variable {K : Type*} [Field K] [DecidableEq K]

/-- The content of `globalCheck`. -/
structure GlobalFacts (T : GlobalCert K) : Prop where
  ib : ibCheckR T.Fc T.n T.k T.I T.G = true
  norm : normCheck T.n T.I = true
  Dlast : T.I.Dc.getLast? = some 1
  kF : ∀ j < T.Fc.length, (T.Fc.getD j []).length ≤ T.kD + 1
  pt : GlobalCert.ptCheck T.Fc T.n T.αL T.yL T.cΓ = true
  Γl : T.ΓL.length = T.αL.length
  sum : (∑ j ∈ Finset.range T.αL.length, ∑ k ∈ Finset.range T.n, (T.ΓL.getD j []).getD k 0) =
    T.cdeg * T.n

lemma globalCheck_spec {T : GlobalCert K} (h : T.globalCheck = true) : GlobalFacts T := by
  simp only [GlobalCert.globalCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc] at h
  obtain ⟨hib, hnorm, hD, hkF, hpt, hΓl, hsum⟩ := h
  exact ⟨ibCheckR_of_ibCheck hib, hnorm, hD, hkF, hpt, hΓl, hsum⟩

/-- The strict integral-basis check of a passing `globalCheck`. -/
lemma globalCheck_ib {T : GlobalCert K} (h : T.globalCheck = true) :
    ibCheck T.Fc T.n T.k T.I T.G = true := by
  simp only [GlobalCert.globalCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1

lemma globalCheckR_spec {T : GlobalCert K} (h : T.globalCheckR = true) : GlobalFacts T := by
  simp only [GlobalCert.globalCheckR, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc] at h
  obtain ⟨hib, hnorm, hD, hkF, hpt, hΓl, hsum⟩ := h
  exact ⟨hib, hnorm, hD, hkF, hpt, hΓl, hsum⟩

lemma globalCheckR_of_globalCheck {T : GlobalCert K} (h : T.globalCheck = true) :
    T.globalCheckR = true := by
  simp only [GlobalCert.globalCheck, GlobalCert.globalCheckR, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨⟨⟨⟨⟨⟨ibCheckR_of_ibCheck h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

lemma eisCheck_spec {T : GlobalCert K} (h : T.eisCheck = true) :
    (∀ i < T.n, Kron.evalC (T.Fc.getD i []) T.aE = 0) ∧
      Kron.evalC (CPoly.deriv (T.Fc.getD 0 [])) T.aE ≠ 0 := by
  simpa [GlobalCert.eisCheck, List.all_eq_true] using h

variable {p : ℕ} [Fact p.Prime] (R : RedFns p K)

/-- The content of `primeCheck`. -/
structure PrimeFacts (T : GlobalCert K) (P : PrimeCert p) : Prop where
  okF : okB R T.Fc = true
  okBc : ∀ W ∈ T.I.Bc, okB R W = true
  okD : ∀ c ∈ T.I.Dc, R.ok c = true
  okG : ∀ c ∈ T.G, R.ok c = true
  okα : ∀ c ∈ T.αL, R.ok c = true
  oky : ∀ l ∈ T.yL, ∀ c ∈ l, R.ok c = true
  okE : R.ok T.aE = true
  ib : ibCheck (redBL R T.Fc) T.n T.k (P.Ip R T) (T.G.map R.red) = true
  irr : (T.eisCheck = true ∧ Kron.evalC (CPoly.deriv ((redBL R T.Fc).getD 0 [])) (R.red T.aE) ≠ 0) ∨
    (∃ a, P.aI = some a ∧ noSmallFactor ((List.range p).map fun i : ℕ ↦ (i : ZMod p))
      ((redBL R T.Fc).map fun c ↦ Kron.evalC c a) T.n = true) ∨
    irrAt (redBL R T.Fc) T.n T.kD (P.xs.getD 0 0) (P.ys.getD 0 []) P.irrP = true
  gen : (∑ j ∈ Finset.range T.n, T.I.δL.getD j 0) + 1 = P.xs.length + T.n
  xnd : P.xs.Nodup
  ysl : P.ys.length = P.xs.length
  base : ∀ i < P.xs.length, (P.ys.getD i []).length = T.n ∧ (P.ys.getD i []).Nodup ∧
    Kron.evalC (T.I.Dc.map R.red) (P.xs.getD i 0) ≠ 0 ∧ ∀ k < T.n,
      evalB (redBL R T.Fc) (P.xs.getD i 0) ((P.ys.getD i []).getD k 0) = 0 ∧
      evalB (derivYB (redBL R T.Fc)) (P.xs.getD i 0) ((P.ys.getD i []).getD k 0) ≠ 0
  det : detCheck T.n P.xs.length (T.I.Bc.map (redBL R)) P.xs P.ys P.Ls = true
  ns : nsCheck T.n P.xs.length T.I.δL (T.I.Bc.map (redBL R)) P.xs P.ys P.lam = true
  αnd : (T.αL.map R.red).Nodup
  Γpt : ∀ j < T.αL.length, ((T.yL.map (·.map R.red)).getD j []).Nodup ∧
    Kron.evalC (T.I.Dc.map R.red) ((T.αL.map R.red).getD j 0) ≠ 0 ∧
    (∀ i < P.xs.length, (T.αL.map R.red).getD j 0 ≠ P.xs.getD i 0) ∧
    ∀ k < T.n, evalB (derivYB (redBL R T.Fc)) ((T.αL.map R.red).getD j 0)
      (((T.yL.map (·.map R.red)).getD j []).getD k 0) ≠ 0
  pt : GlobalCert.ptCheck (redBL R T.Fc) T.n (T.αL.map R.red) (T.yL.map (·.map R.red)) P.cΓ = true
  mp : 1 ≤ P.mp
  wit : princWitCheck T.n (P.mp * T.cdeg) T.I.δL (T.I.Bc.map (redBL R)) (T.I.Dc.map R.red)
    (T.αL.map R.red) P.cΓ (T.ΓL.map (·.map (P.mp * ·))) P.Gw = true

lemma primeCheck_spec {T : GlobalCert K} {P : PrimeCert p} (h : primeCheck R T P = true) :
    PrimeFacts R T P := by
  simp only [primeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc] at h
  obtain ⟨hF, hB, hD, hG, hα, hy, hE, hib, heis, hgen, hxnd, hysl, hbase, hdet, hns, hαnd, hΓ, hpt,
    hmp, hwit⟩ := h
  refine ⟨hF, hB, hD, hG, hα, hy, hE, hib, ?_, hgen, hxnd, hysl, hbase, hdet, hns, hαnd, hΓ, hpt,
    hmp, hwit⟩
  revert heis
  cases ha : P.aI with
  | none =>
    intro h1
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
    rcases h1 with h1 | ⟨-, h1⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
  | some a =>
    intro h1
    exact Or.inr (Or.inl ⟨a, rfl, h1⟩)

end Facts

end Curves
