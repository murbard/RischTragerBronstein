import RischTragerBronstein.Mixed.ManinMap
import RischTragerBronstein.Mixed.EllCompute2
import RischTragerBronstein.Differential.FractionField

/-!
# The Manin map on executable fractions

Over `K(X)` with `D = d/dX` (`dX`, extended from `K[X]` by `Differential.fractionRingDerivation`),
the Manin map of `ManinMap` is evaluated on executable fractions `Fr K`:

* `dFr`, `val_dFr`: the quotient rule on codes;
* `muC`, **`val_muC`**: `val (muC Ac Bc u v) = mu dX A B (u, v)` for an affine point with `v ≠ 0`,
  when `4A³ + 27B² ≠ 0` and `β ≠ 0` (non-constant `j`), checked by `muOK`;
* `wronskC`, **`indep_of_wronskC`**: an executable independence certificate — if the Wronskian of
  `muC P, muC Q` is a non-zero code, no relation `m P = n Q + T` (`T` torsion, `(m, n) ≠ 0`) holds
  in `E(K(X))`.
-/

open Polynomial

namespace Manin

open FFHeight FFHeight.Fr WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)

/-- Use the canonical `ℤ`-algebra structure on `K(X)` (the one of `ManinMap`), not
`RatFunc.instAlgebraOfPolynomial`. -/
noncomputable local instance (priority := 2000) intAlgRF : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

/-- `d/dX` on `K[X]`. -/
noncomputable def polyDiff : Differential K[X] :=
  ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩

/-- `d/dX` on `K(X)`. -/
noncomputable def dX : Derivation ℤ (RatFunc K) (RatFunc K) :=
  letI := polyDiff (K := K)
  Differential.fractionRingDerivation K[X] (RatFunc K)

theorem dX_ι (p : K[X]) : dX (ι p) = ι (derivative p) := by
  letI := polyDiff (K := K)
  change (Differential.fractionDualNumberHom K[X] (RatFunc K) (ι p)).snd = _
  rw [Differential.fractionDualNumberHom_algebraMap]
  simp only [Differential.dualNumberHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  rfl

/-- The derivative of a code. -/
def dFr (f : Fr K) : Fr K :=
  (CPoly.sub (CPoly.mul (CPoly.deriv f.1) f.2) (CPoly.mul f.1 (CPoly.deriv f.2)), CPoly.mul f.2 f.2)

theorem ok_dFr {f : Fr K} (hf : ok f) : ok (dFr f) := by
  simp only [ok, dFr, CPoly.toPoly_mul] at hf ⊢
  exact mul_ne_zero hf hf

theorem val_dFr {f : Fr K} (hf : ok f) : val (dFr f) = dX (val f) := by
  have hq : ι (CPoly.toPoly f.2) ≠ 0 := ι_ne hf
  simp only [val, dFr, CPoly.toPoly_sub, CPoly.toPoly_mul, CPoly.toPoly_deriv]
  rw [Derivation.leibniz_div, dX_ι, dX_ι, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  simp only [map_sub, map_mul]
  field_simp

variable (Ac Bc : CPoly K)

/-- `A`, `A'`, `B`, `B'` as codes. -/
def AF : Fr K := ofPoly Ac
/-- `A'`. -/
def A1F : Fr K := ofPoly (CPoly.deriv Ac)

/-- `4A³ + 27B²`. -/
def ZF : Fr K := add (smulC 4 (mul (AF Ac) (mul (AF Ac) (AF Ac)))) (smulC 27 (mul (AF Bc) (AF Bc)))

/-- `β`. -/
def beF : Fr K :=
  norm (div (sub (smulC 9 (mul (A1F Ac) (AF Bc))) (smulC 6 (mul (AF Ac) (A1F Bc)))) (smulC 2 (ZF Ac Bc)))

/-- `α`. -/
def alF : Fr K :=
  norm (div (sub (smulC (-2) (mul (mul (AF Ac) (AF Ac)) (A1F Ac))) (smulC 9 (mul (AF Bc) (A1F Bc))))
    (smulC 2 (ZF Ac Bc)))

/-- `γ`. -/
def gaF : Fr K :=
  norm (div (sub (smulC 3 (mul (mul (AF Ac) (A1F Ac)) (AF Bc))) (smulC 2 (mul (mul (AF Ac) (AF Ac)) (A1F Bc))))
    (smulC 2 (ZF Ac Bc)))

/-- `h(u)`. -/
def hF (u : Fr K) : Fr K :=
  sub (add (div (sub (smulC 4 (mul (mul (AF Ac) (AF Ac)) (A1F Bc))) (smulC 6 (mul (mul (AF Ac) (A1F Ac)) (AF Bc))))
    (ZF Ac Bc)) (smulC 2 (mul (alF Ac Bc) u))) (smulC 2 (mul (beF Ac Bc) (mul u u)))

/-- `g(u)`. -/
def gF (u : Fr K) : Fr K :=
  add (add (div (sub (smulC 9 (mul (A1F Ac) (mul (AF Bc) (AF Bc)))) (smulC 6 (mul (mul (AF Ac) (AF Bc)) (A1F Bc))))
    (ZF Ac Bc)) (smulC 2 (mul (gaF Ac Bc) u))) (smulC 2 (mul (alF Ac Bc) (mul u u)))

/-- First component of the Gauss–Manin vector. -/
def b1F (u v : Fr K) : Fr K := norm (div (add (dFr u) (hF Ac Bc u)) v)
/-- Second component. -/
def b2F (u v : Fr K) : Fr K := norm (div (add (mul u (dFr u)) (gF Ac Bc u)) v)
/-- `κ`. -/
def kaF : Fr K := norm (div (sub (dFr (beF Ac Bc)) (mul (beF Ac Bc) (alF Ac Bc))) (beF Ac Bc))

/-- **The executable Manin map.** -/
def muC (u v : Fr K) : Fr K :=
  norm (add (sub (dFr (b1F Ac Bc u v)) (mul (kaF Ac Bc) (b1F Ac Bc u v))) (mul (beF Ac Bc) (b2F Ac Bc u v)))

/-- The side conditions of `val_muC`: `v ≠ 0`, `4A³ + 27B² ≠ 0`, `β ≠ 0`. -/
def muOK (u v : Fr K) : Bool :=
  !CPoly.isZero u.2 && !CPoly.isZero v.2 && !isZ v && !isZ (ZF Ac Bc) && !isZ (beF Ac Bc)

/-! ### Correctness -/

section spec

variable {Ac Bc}

omit [CharZero K] in
theorem okF (p : CPoly K) : ok (ofPoly p) := ok_ofPoly p

theorem val_ZF : val (ZF Ac Bc) = ZZ (ι (CPoly.toPoly Ac)) (ι (CPoly.toPoly Bc)) := by
  simp only [ZF, AF, ZZ, val_add (ok_smulC _ (ok_mul (okF _) (ok_mul (okF _) (okF _))))
    (ok_smulC _ (ok_mul (okF _) (okF _))), val_smulC, val_mul (okF _) (ok_mul (okF _) (okF _)),
    val_mul (okF _) (okF _), val_ofPoly, map_ofNat]
  ring

theorem ok_ZF : ok (ZF Ac Bc) :=
  ok_add (ok_smulC _ (ok_mul (okF _) (ok_mul (okF _) (okF _)))) (ok_smulC _ (ok_mul (okF _) (okF _)))

omit [CharZero K] in
theorem ok_AF (p : CPoly K) : ok (AF p) := by unfold AF; exact ok_ofPoly p
omit [CharZero K] in
theorem ok_A1F (p : CPoly K) : ok (A1F p) := by unfold A1F; exact ok_ofPoly p

omit [CharZero K] in
theorem ok_of_isZero {f : Fr K} (h : CPoly.isZero f.2 = false) : ok f := by
  intro h0; rw [← CPoly.isZero_iff] at h0; rw [h0] at h; exact Bool.false_ne_true h.symm

attribute [local irreducible] FFHeight.Fr.ok FFHeight.Fr.val FFHeight.Fr.norm FFHeight.Fr.add
  FFHeight.Fr.mul FFHeight.Fr.sub FFHeight.Fr.div FFHeight.Fr.smulC FFHeight.Fr.ofPoly Manin.dFr Manin.AF
  Manin.A1F Manin.ZF Manin.beF Manin.alF Manin.gaF Manin.hF Manin.gF Manin.b1F Manin.b2F Manin.kaF
  Manin.muC

/-- Discharger for well-definedness side conditions. -/
syntax "mokt" : tactic
macro_rules
  | `(tactic| mokt) => `(tactic| first
    | assumption
    | exact ok_AF _
    | exact ok_A1F _
    | exact ok_ZF
    | (apply ok_add <;> mokt)
    | (apply ok_mul <;> mokt)
    | (apply ok_sub <;> mokt)
    | (apply ok_smulC <;> mokt)
    | (apply ok_norm <;> mokt)
    | (apply ok_dFr <;> mokt)
    | (apply ok_div <;> mokt))

/-- Abbreviations for the values of `A`, `B`. -/
local notation "Aι" => ι (CPoly.toPoly Ac)
local notation "Bι" => ι (CPoly.toPoly Bc)

theorem val_AF (p : CPoly K) : val (AF p) = ι (CPoly.toPoly p) := by unfold AF; exact val_ofPoly p

theorem val_A1F (p : CPoly K) : val (A1F p) = dX (ι (CPoly.toPoly p)) := by
  unfold A1F; rw [val_ofPoly, CPoly.toPoly_deriv, dX_ι]

theorem two_ne (Z : RatFunc K) (hZ : Z ≠ 0) : algebraMap K (RatFunc K) 2 * Z ≠ 0 :=
  mul_ne_zero (by simp) hZ

theorem val_beF (hZ : val (ZF Ac Bc) ≠ 0) :
    val (beF Ac Bc) = beZ (ZZ Aι Bι) Aι Bι (dX Aι) (dX Bι) := by
  have h2 : val (smulC 2 (ZF Ac Bc)) ≠ 0 := by rw [val_smulC]; exact two_ne _ hZ
  simp (disch := mokt) only [beF, val_norm, val_div, val_sub, val_smulC, val_mul, val_AF, val_A1F,
    val_ZF, beZ, map_ofNat]
  ring

theorem val_alF (hZ : val (ZF Ac Bc) ≠ 0) :
    val (alF Ac Bc) = alZ (ZZ Aι Bι) Aι Bι (dX Aι) (dX Bι) := by
  have h2 : val (smulC 2 (ZF Ac Bc)) ≠ 0 := by rw [val_smulC]; exact two_ne _ hZ
  simp (disch := mokt) only [alF, val_norm, val_div, val_sub, val_smulC, val_mul, val_AF, val_A1F,
    val_ZF, alZ, map_ofNat, map_neg]
  ring

theorem val_gaF (hZ : val (ZF Ac Bc) ≠ 0) :
    val (gaF Ac Bc) = gaZ (ZZ Aι Bι) Aι Bι (dX Aι) (dX Bι) := by
  have h2 : val (smulC 2 (ZF Ac Bc)) ≠ 0 := by rw [val_smulC]; exact two_ne _ hZ
  simp (disch := mokt) only [gaF, val_norm, val_div, val_sub, val_smulC, val_mul, val_AF, val_A1F,
    val_ZF, gaZ, map_ofNat]
  ring

theorem ok_beF (hZ : val (ZF Ac Bc) ≠ 0) : ok (beF Ac Bc) := by
  have h2 : val (smulC 2 (ZF Ac Bc)) ≠ 0 := by rw [val_smulC]; exact two_ne _ hZ
  unfold beF; mokt

theorem ok_alF (hZ : val (ZF Ac Bc) ≠ 0) : ok (alF Ac Bc) := by
  have h2 : val (smulC 2 (ZF Ac Bc)) ≠ 0 := by rw [val_smulC]; exact two_ne _ hZ
  unfold alF; mokt

theorem ok_gaF (hZ : val (ZF Ac Bc) ≠ 0) : ok (gaF Ac Bc) := by
  have h2 : val (smulC 2 (ZF Ac Bc)) ≠ 0 := by rw [val_smulC]; exact two_ne _ hZ
  unfold gaF; mokt

theorem ok_hF {u : Fr K} (hZ : val (ZF Ac Bc) ≠ 0) (hu : ok u) : ok (hF Ac Bc u) := by
  have := ok_alF hZ; have := ok_beF hZ
  unfold hF; mokt

theorem ok_gF {u : Fr K} (hZ : val (ZF Ac Bc) ≠ 0) (hu : ok u) : ok (gF Ac Bc u) := by
  have := ok_alF hZ; have := ok_gaF hZ
  unfold gF; mokt

theorem val_hF {u : Fr K} (hZ : val (ZF Ac Bc) ≠ 0) (hu : ok u) :
    val (hF Ac Bc u) = hhZ (ZZ Aι Bι) Aι Bι (dX Aι) (dX Bι) (val u) := by
  have := ok_alF hZ; have := ok_beF hZ
  simp (disch := mokt) only [hF, val_add, val_div, val_sub, val_smulC, val_mul, val_AF, val_A1F,
    val_ZF, val_alF hZ, val_beF hZ, hhZ, map_ofNat]
  ring

theorem val_gF {u : Fr K} (hZ : val (ZF Ac Bc) ≠ 0) (hu : ok u) :
    val (gF Ac Bc u) = gZ (ZZ Aι Bι) Aι Bι (dX Aι) (dX Bι) (val u) := by
  have := ok_alF hZ; have := ok_gaF hZ
  simp (disch := mokt) only [gF, val_add, val_div, val_sub, val_smulC, val_mul, val_AF, val_A1F,
    val_ZF, val_alF hZ, val_gaF hZ, gZ, map_ofNat]
  ring

theorem ok_b1F {u v : Fr K} (hZ : val (ZF Ac Bc) ≠ 0) (hu : ok u) (hv0 : val v ≠ 0) :
    ok (b1F Ac Bc u v) := by
  have := ok_hF hZ hu; unfold b1F; mokt

theorem ok_b2F {u v : Fr K} (hZ : val (ZF Ac Bc) ≠ 0) (hu : ok u) (hv0 : val v ≠ 0) :
    ok (b2F Ac Bc u v) := by
  have := ok_gF hZ hu; unfold b2F; mokt

theorem val_b1F {u v : Fr K} (hZ : val (ZF Ac Bc) ≠ 0) (hu : ok u) (hv : ok v) (hv0 : val v ≠ 0) :
    val (b1F Ac Bc u v) = b1Z (ZZ Aι Bι) Aι Bι (dX Aι) (dX Bι) (val u) (val v) (dX (val u)) := by
  have := ok_hF hZ hu
  simp (disch := mokt) only [b1F, val_norm, val_div, val_add, val_dFr, val_hF hZ hu, b1Z]

theorem val_b2F {u v : Fr K} (hZ : val (ZF Ac Bc) ≠ 0) (hu : ok u) (hv : ok v) (hv0 : val v ≠ 0) :
    val (b2F Ac Bc u v) = b2Z (ZZ Aι Bι) Aι Bι (dX Aι) (dX Bι) (val u) (val v) (dX (val u)) := by
  have := ok_gF hZ hu
  simp (disch := mokt) only [b2F, val_norm, val_div, val_add, val_mul, val_dFr, val_gF hZ hu, b2Z]

theorem val_kaF (hZ : val (ZF Ac Bc) ≠ 0) (hb : val (beF Ac Bc) ≠ 0) :
    val (kaF Ac Bc) = ka dX Aι Bι := by
  have := ok_alF hZ; have := ok_beF hZ
  simp (disch := mokt) only [kaF, val_norm, val_div, val_sub, val_mul, val_dFr, val_beF hZ,
    val_alF hZ, ka, bt]

open scoped Classical in
/-- **Correctness of the executable Manin map.** -/
theorem val_muC {u v : Fr K} (hZ : val (ZF Ac Bc) ≠ 0) (hb : val (beF Ac Bc) ≠ 0) (hu : ok u)
    (hv : ok v) (hv0 : val v ≠ 0) (h : (sW Aι Bι).toAffine.Nonsingular (val u) (val v)) :
    val (muC Ac Bc u v) = mu dX Aι Bι (Point.some (val u) (val v) h) := by
  have := ok_b1F hZ hu hv0; have := ok_b2F hZ hu hv0; have := ok_beF hZ; have := ok_alF hZ
  have hka : ok (kaF Ac Bc) := by unfold kaF; mokt
  simp (disch := mokt) only [muC, val_norm, val_add, val_sub, val_mul, val_dFr, val_b1F hZ hu hv hv0,
    val_b2F hZ hu hv hv0, val_kaF hZ hb, val_beF hZ]
  simp only [mu, muP, bvU, if_neg hv0, bt]

theorem ok_muC {u v : Fr K} (hZ : val (ZF Ac Bc) ≠ 0) (hb : val (beF Ac Bc) ≠ 0) (hu : ok u)
    (hv0 : val v ≠ 0) : ok (muC Ac Bc u v) := by
  have := ok_b1F hZ hu hv0; have := ok_b2F hZ hu hv0; have := ok_beF hZ; have := ok_alF hZ
  have hka : ok (kaF Ac Bc) := by unfold kaF; mokt
  unfold muC; mokt

/-- Consequences of `muOK`. -/
theorem of_muOK {u v : Fr K} (h : muOK Ac Bc u v = true) :
    ok u ∧ ok v ∧ val v ≠ 0 ∧ val (ZF Ac Bc) ≠ 0 ∧ val (beF Ac Bc) ≠ 0 := by
  simp only [muOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hu, hv⟩, hv0⟩, hZ⟩, hb⟩ := h
  have hu' := ok_of_isZero hu
  have hv' := ok_of_isZero hv
  have hZ' : val (ZF Ac Bc) ≠ 0 := fun h0 ↦ by
    rw [← isZ_iff ok_ZF] at h0; rw [h0] at hZ; exact Bool.false_ne_true hZ.symm
  refine ⟨hu', hv', fun h0 ↦ ?_, hZ', fun h0 ↦ ?_⟩
  · rw [← isZ_iff hv'] at h0; rw [h0] at hv0; exact Bool.false_ne_true hv0.symm
  · rw [← isZ_iff (ok_beF hZ')] at h0; rw [h0] at hb; exact Bool.false_ne_true hb.symm

end spec

/-- The Wronskian of the Manin images of two points. -/
def wronskC (uP vP uQ vQ : Fr K) : Fr K :=
  sub (mul (muC Ac Bc uP vP) (dFr (muC Ac Bc uQ vQ))) (mul (muC Ac Bc uQ vQ) (dFr (muC Ac Bc uP vP)))

/-- The executable independence certificate. -/
def manCert (uP vP uQ vQ : Fr K) : Bool :=
  muOK Ac Bc uP vP && muOK Ac Bc uQ vQ && !isZ (wronskC Ac Bc uP vP uQ vQ)

variable {Ac Bc}

local notation "Aι" => ι (CPoly.toPoly Ac)
local notation "Bι" => ι (CPoly.toPoly Bc)

attribute [local irreducible] FFHeight.Fr.ok FFHeight.Fr.val FFHeight.Fr.sub FFHeight.Fr.mul
  Manin.dFr Manin.muC

open scoped Classical in
/-- **Independence from the executable Manin certificate.** If `manCert` accepts two affine
points of `y² = x³ + A x + B` over `K(X)`, no relation `m P = n Q + T` (`T` torsion,
`(m, n) ≠ (0, 0)`) holds. -/
theorem indep_of_manCert {uP vP uQ vQ : Fr K} (hc : manCert Ac Bc uP vP uQ vQ = true)
    (hP : (sW Aι Bι).toAffine.Nonsingular (val uP) (val vP))
    (hQ : (sW Aι Bι).toAffine.Nonsingular (val uQ) (val vQ))
    (m n : ℤ) (T : (sW Aι Bι).toAffine.Point) (k : ℕ) (hk : k ≠ 0) (hT : k • T = 0)
    (hrel : m • Point.some _ _ hP = n • Point.some _ _ hQ + T) : m = 0 ∧ n = 0 := by
  simp only [manCert, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨h1, h2⟩, hW⟩ := hc
  obtain ⟨huP, hvP, hvP0, hZ, hb⟩ := of_muOK h1
  obtain ⟨huQ, hvQ, hvQ0, -, -⟩ := of_muOK h2
  have hΔ : 4 * Aι ^ 3 + 27 * Bι ^ 2 ≠ 0 := by rw [val_ZF] at hZ; exact hZ
  have okP := ok_muC hZ hb huP hvP0
  have okQ := ok_muC hZ hb huQ hvQ0
  have okW : ok (wronskC Ac Bc uP vP uQ vQ) := by unfold wronskC; mokt
  have hW' : val (wronskC Ac Bc uP vP uQ vQ) ≠ 0 := fun h0 ↦ by
    rw [← isZ_iff okW] at h0; rw [h0] at hW; exact Bool.false_ne_true hW.symm
  have hval : val (wronskC Ac Bc uP vP uQ vQ) =
      mu dX Aι Bι (Point.some _ _ hP) * dX (mu dX Aι Bι (Point.some _ _ hQ)) -
        mu dX Aι Bι (Point.some _ _ hQ) * dX (mu dX Aι Bι (Point.some _ _ hP)) := by
    simp (disch := mokt) only [wronskC, val_sub, val_mul, val_dFr]
    rw [val_muC hZ hb huP hvP hvP0 hP, val_muC hZ hb huQ hvQ hvQ0 hQ]
  rw [hval] at hW'
  exact indep_of_wronskian dX hΔ _ _ hW' m n T k hk hT hrel


/-- **The constant-ratio certificate**: a candidate constant `c` (from the normalized ratio)
with `mu Q = c · mu P` checked exactly and `c` rejected by a rationality test `isRat`. -/
def manCertR (Ac Bc : CPoly K) (isRat : K → Bool) (uP vP uQ vQ : Fr K) : Bool :=
  let mP := muC Ac Bc uP vP
  let mQ := muC Ac Bc uQ vQ
  let r := norm (div mQ mP)
  let c := (CPoly.trim r.1).headD 0 / (CPoly.trim r.2).headD 1
  muOK Ac Bc uP vP && muOK Ac Bc uQ vQ && !isZ mP && !isRat c && eqb mQ (smulC c mP)

open scoped Classical in
/-- **Independence from the constant-ratio certificate** (`isRat` must accept every rational). -/
theorem indep_of_manCertR {isRat : K → Bool} (hRat : ∀ q : ℚ, isRat (q : K) = true)
    {uP vP uQ vQ : Fr K} (hc : manCertR Ac Bc isRat uP vP uQ vQ = true)
    (hP : (sW Aι Bι).toAffine.Nonsingular (val uP) (val vP))
    (hQ : (sW Aι Bι).toAffine.Nonsingular (val uQ) (val vQ))
    (m n : ℤ) (T : (sW Aι Bι).toAffine.Point) (k : ℕ) (hk : k ≠ 0) (hT : k • T = 0)
    (hrel : m • Point.some _ _ hP = n • Point.some _ _ hQ + T) : m = 0 ∧ n = 0 := by
  simp only [manCertR, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, hP0⟩, hr⟩, heq⟩ := hc
  set c := (CPoly.trim (norm (div (muC Ac Bc uQ vQ) (muC Ac Bc uP vP))).1).headD 0 /
    (CPoly.trim (norm (div (muC Ac Bc uQ vQ) (muC Ac Bc uP vP))).2).headD 1 with hcdef
  obtain ⟨huP, hvP, hvP0, hZ, hb⟩ := of_muOK h1
  obtain ⟨huQ, hvQ, hvQ0, -, -⟩ := of_muOK h2
  have hΔ : 4 * Aι ^ 3 + 27 * Bι ^ 2 ≠ 0 := by rw [val_ZF] at hZ; exact hZ
  have okP := ok_muC hZ hb huP hvP0
  have okQ := ok_muC hZ hb huQ hvQ0
  have hmP := val_muC hZ hb huP hvP hvP0 hP
  have hmQ := val_muC hZ hb huQ hvQ hvQ0 hQ
  have hP0' : mu dX Aι Bι (Point.some _ _ hP) ≠ 0 := fun h0 ↦ by
    rw [← hmP, ← isZ_iff okP] at h0; rw [h0] at hP0; exact Bool.false_ne_true hP0.symm
  have hval := (eqb_iff okQ (ok_smulC c okP)).mp heq
  rw [val_smulC, hmP, hmQ] at hval
  refine indep_of_ratio dX hΔ _ _ hP0' (algebraMap K (RatFunc K) c) hval (fun q hq ↦ ?_)
    m n T k hk hT hrel
  have : c = (q : K) := by
    apply (algebraMap K (RatFunc K)).injective
    rw [hq, map_ratCast]
  rw [this, hRat] at hr
  exact Bool.false_ne_true hr.symm

end Manin
