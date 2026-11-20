import RischTragerBronstein.Torsion.PrimeCertExist1
import RischTragerBronstein.Torsion.PrimeRed1

/-!
# Prime certificates exist (2): the reduced certificate passes `primeCheck`

For a global certificate `T` over `K` without divisor data (`αL = []`), base points `xs, ys` over `K`
with their non-speciality coefficients `lam` and left inverses `Ls`, and a subset certificate of
precision `irrP` at the first base point, all checked in characteristic `0` (`Char0Base`), the
reduction `redPrimeCert` passes `primeCheck` at every certified reduction `R` at which a finite
list of explicit elements are *good* (integral, with integral inverses when non-zero; `GoodBase`)
(**`primeCheck_redPrimeCert`**).
-/

open Polynomial

namespace Curves

open CPoly Sup

section Defs

variable {K : Type*} [Field K] [DecidableEq K]

/-- The coefficient at the order of a list. -/
def ordCoeff (P : List K) : K := P.getD (ordC P) 0

/-- The coefficient `U₀` of the check at infinity. -/
def infU0 (I : IntBasisCert K) : K :=
  (compC (reflectC (I.Dc.length - 1) I.Dc) (shiftC 0 I.infc.N)).getD 0 0

/-- The unit of the basis check at a point. -/
def unitAtEl (Dc : List K) (a : K) (N : ℕ) : K := (compC Dc (shiftC a N)).getD (muD Dc a N) 0

/-- The characteristic-`0` facts behind a reduced prime certificate. -/
structure Char0Base (T : GlobalCert K) (xs : List K) (ys : List (List K)) (lam : List (List K))
    (Ls : List (List (List K))) (irrP : ℕ) : Prop where
  glob : GlobalFacts T
  αL : T.αL = []
  yL : T.yL = []
  n0 : 0 < T.n
  gen : (∑ j ∈ Finset.range T.n, T.I.δL.getD j 0) + 1 = xs.length + T.n
  xnd : xs.Nodup
  ysl : ys.length = xs.length
  base : ∀ i < xs.length, (ys.getD i []).length = T.n ∧ (ys.getD i []).Nodup ∧
    Kron.evalC T.I.Dc (xs.getD i 0) ≠ 0 ∧ ∀ k < T.n,
      evalB T.Fc (xs.getD i 0) ((ys.getD i []).getD k 0) = 0 ∧
      evalB (derivYB T.Fc) (xs.getD i 0) ((ys.getD i []).getD k 0) ≠ 0
  det : detCheck T.n xs.length T.I.Bc xs ys Ls = true
  ns : nsCheck T.n xs.length T.I.δL T.I.Bc xs ys lam = true
  irrP0 : 0 < irrP
  irr : irrAt T.Fc T.n T.kD (xs.getD 0 0) (ys.getD 0 []) irrP = true
  U0 : infU0 T.I ≠ 0
  newton : ∀ y0 ∈ ys.getD 0 [], ∀ v ∈ newtonVals (T.Fc.map fun q ↦ compC q (shiftC (xs.getD 0 0) 1))
    irrP (Nat.log2 irrP + 3) [y0], v ≠ 0
  ibS : ibCheck T.Fc T.n T.k T.I T.G = true

end Defs

section Good

variable {K : Type*} [Field K] [DecidableEq K] {p : ℕ} [Fact p.Prime] (R : RedFns p K)

/-- Goodness of the entries of a list of lists. -/
def GoodLL (L : List (List K)) : Prop := ∀ l ∈ L, ∀ c ∈ l, Good R c

/-- Goodness of the differences of the coefficients of a system of approximations. -/
def GoodDif (ys : List (List K)) (prec : ℕ) : Prop :=
  ∀ k < ys.length, ∀ l < ys.length, ∀ i < prec, Good R ((ys.getD k []).getD i 0 - (ys.getD l []).getD i 0)

/-- Goodness of the data of a branch certificate above `a` (entries, orders, separation). -/
def GoodCert (Fc : BPoly K) (a : K) (c : BranchCert K) : Prop :=
  GoodLL R c.ys ∧ (∀ y ∈ c.ys, Good R (ordCoeff (bivEvalT (derivYB Fc) (shiftC a c.N) y c.prec))) ∧
    GoodDif R c.ys c.prec

/-- The elements that must be good for the reduced prime certificate. -/
structure GoodBase (T : GlobalCert K) (xs : List K) (ys : List (List K)) (lam : List (List K))
    (Ls : List (List (List K))) (irrP : ℕ) : Prop where
  zero : Good R 0
  F : GoodLL R T.Fc
  B : ∀ W ∈ T.I.Bc, GoodLL R W
  D : ∀ c ∈ T.I.Dc, Good R c
  G : ∀ c ∈ T.G, Good R c
  E : Good R T.aE
  x : ∀ c ∈ xs, Good R c
  y : GoodLL R ys
  lam : GoodLL R lam
  Ls : ∀ L ∈ Ls, GoodLL R L
  pts : ∀ q ∈ T.I.pts, Good R q.1 ∧ GoodCert R T.Fc q.1 q.2.1 ∧ GoodLL R q.2.2 ∧
    Good R (unitAtEl T.I.Dc q.1 q.2.1.N)⁻¹
  inf : GoodCert R (invB T.Fc T.k (T.k * T.n)) 0 T.I.infc ∧ GoodLL R T.I.Linf
  last : Good R (T.I.Dc.getD (T.I.Dc.length - 1) 0)
  U0 : Good R (infU0 T.I)
  cov : ∀ v ∈ coverVals T.G (T.I.pts.map Prod.fst), Good R v
  newton : ∀ y0 ∈ ys.getD 0 [], ∀ v ∈ newtonVals (T.Fc.map fun q ↦ compC q (shiftC (xs.getD 0 0) 1))
    irrP (Nat.log2 irrP + 3) [y0], Good R v
  lift : GoodCert R T.Fc (xs.getD 0 0) (liftRootsAt T.Fc (xs.getD 0 0) (ys.getD 0 []) irrP)
  prods : ∀ L ∈ subsetsL T.n,
    GoodLL R (prodSubB (liftRootsAt T.Fc (xs.getD 0 0) (ys.getD 0 []) irrP).ys L)
  base : ∀ i < xs.length, Good R (Kron.evalC T.I.Dc (xs.getD i 0)) ∧
    (∀ k < T.n, Good R (evalB (derivYB T.Fc) (xs.getD i 0) ((ys.getD i []).getD k 0))) ∧
    ∀ k < (ys.getD i []).length, ∀ l < (ys.getD i []).length,
      Good R ((ys.getD i []).getD k 0 - (ys.getD i []).getD l 0)
  xd : ∀ i < xs.length, ∀ j < xs.length, Good R (xs.getD i 0 - xs.getD j 0)

/-- **The reduced prime certificate.** -/
def redPrimeCert (T : GlobalCert K) (xs : List K) (ys : List (List K)) (lam : List (List K))
    (Ls : List (List (List K))) (irrP : ℕ) : PrimeCert p :=
  ⟨T.I.pts.map fun q ↦ (R.red q.1, ⟨q.2.1.N, q.2.1.ys.map (·.map R.red), q.2.1.prec⟩,
      q.2.2.map (·.map R.red)),
    ⟨T.I.infc.N, T.I.infc.ys.map (·.map R.red), T.I.infc.prec⟩, T.I.Linf.map (·.map R.red),
    xs.map R.red, ys.map (·.map R.red), lam.map (·.map R.red), Ls.map (·.map (·.map R.red)), [], 1,
    [[1]], none, irrP⟩

end Good

section Red

variable {K : Type*} [Field K] [DecidableEq K] {p : ℕ} [Fact p.Prime] (R : RedFns p K)
  {φ : K →+* ℚ_[p]} (hR : RedValid p R φ)

local notation "Sφ" => intSub φ
local notation "gφ" => psiRed φ

include hR in
lemma inS_of_good {l : List K} (h : ∀ c ∈ l, Good R c) : InS Sφ l :=
  inS_of_ok R hR fun c hc ↦ (h c hc).1

include hR in
lemma inSB_of_good {L : List (List K)} (h : GoodLL R L) : InSB Sφ L :=
  fun l hl ↦ inS_of_good R hR (h l hl)

lemma ok_of_goodLL {L : List (List K)} (h : GoodLL R L) : ∀ l ∈ L, ∀ c ∈ l, R.ok c = true :=
  fun l hl c hc ↦ (h l hl c hc).1

lemma certCheck_sep {Fc : BPoly K} {n : ℕ} {a : K} {c : BranchCert K}
    (h : certCheck Fc n a c = true) : sepCheck c.ys c.prec = true := by
  simp only [certCheck, Bool.and_eq_true] at h
  exact h.2

include hR in
/-- The unit conditions of a branch certificate from goodness. -/
lemma certUnits {Fc : BPoly K} {n : ℕ} {a : K} {c : BranchCert K} (hg : GoodCert R Fc a c)
    (h : certCheck Fc n a c = true) :
    InSB Sφ c.ys ∧ (∀ y ∈ c.ys, OrdUnit Sφ gφ (bivEvalT (derivYB Fc) (shiftC a c.N) y c.prec)) ∧
      SepUnit (S := Sφ) (g := gφ) c.ys c.prec :=
  ⟨inSB_of_good R hR hg.1, fun y hy ↦ ordUnit_of (zp_of_good R hR (hg.2.1 y hy)),
    sepUnit_of (inSB_of_good R hR hg.1) (certCheck_sep h)
      fun k hk l hl i hi ↦ zp_of_good R hR (hg.2.2 k hk l hl i hi)⟩

include hR in
lemma Ip_eq (T : GlobalCert K) (xs : List K) (ys : List (List K)) (lam : List (List K))
    (Ls : List (List (List K))) (irrP : ℕ)
    (hB : ∀ W ∈ T.I.Bc, GoodLL R W) (hD : ∀ c ∈ T.I.Dc, Good R c)
    (hpts : ∀ q ∈ T.I.pts, Good R q.1 ∧ GoodLL R q.2.1.ys ∧ GoodLL R q.2.2)
    (hinf : GoodLL R T.I.infc.ys ∧ GoodLL R T.I.Linf) :
    (redPrimeCert R T xs ys lam Ls irrP).Ip R T = T.I.mapP (pext Sφ gφ) := by
  have hLL : ∀ L : List (List K), GoodLL R L → L.map (·.map R.red) = L.map (·.map (pext Sφ gφ)) :=
    fun L hL ↦ List.map_congr_left fun l hl ↦ (map_pext_eq R hR fun c hc ↦ (hL l hl c hc).1).symm
  simp only [PrimeCert.Ip, redPrimeCert, IntBasisCert.mapP, IntBasisCert.mk.injEq]
  refine ⟨List.map_congr_left fun W hW ↦ redBL_eq_pext R hR (ok_of_goodLL R (hB W hW)),
    (map_pext_eq R hR fun c hc ↦ (hD c hc).1).symm, trivial,
    List.map_congr_left fun q hq ↦ ?_, by rw [hLL _ hinf.1], hLL _ hinf.2⟩
  obtain ⟨h1, h2, h3⟩ := hpts q hq
  rw [pext_eq_red R hR h1.1, hLL _ h2, hLL _ h3]

include hR in
/-- **The integral-basis check reduces.** -/
theorem ib_red (T : GlobalCert K) (xs : List K) (ys : List (List K)) (lam : List (List K))
    (Ls : List (List (List K))) (irrP : ℕ) (hC : Char0Base T xs ys lam Ls irrP)
    (hG : GoodBase R T xs ys lam Ls irrP) :
    ibCheck (redBL R T.Fc) T.n T.k ((redPrimeCert R T xs ys lam Ls irrP).Ip R T)
      (T.G.map R.red) = true := by
  have hib := hC.ibS
  rw [Ip_eq R hR T xs ys lam Ls irrP hG.B hG.D (fun q hq ↦ ⟨(hG.pts q hq).1, (hG.pts q hq).2.1.1,
      (hG.pts q hq).2.2.1⟩) ⟨hG.inf.1.1, hG.inf.2⟩, redBL_eq_pext R hR (ok_of_goodLL R hG.F),
    ← map_pext_eq R hR fun c hc ↦ (hG.G c hc).1]
  have hib' := hib
  simp only [ibCheck, Bool.and_eq_true, List.all_eq_true] at hib'
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hp⟩, -⟩, hci⟩, -⟩ := hib'
  have hDl := hC.glob.Dlast
  have hlast : T.I.Dc.getD (T.I.Dc.length - 1) 0 = 1 := by
    rw [List.getLast?_eq_getElem?] at hDl
    rw [List.getD_eq_getElem?_getD, hDl]; rfl
  refine ibCheck_pext (inSB_of_good R hR hG.F) (fun W hW ↦ inSB_of_good R hR (hG.B W hW))
    (inS_of_good R hR hG.D) (inS_of_good R hR hG.G) hDl (fun q hq ↦ ?_) ?_
    (by rw [hlast, inv_one]; exact (intSub φ).one_mem) hC.U0
    (mem_intSub_of_ok R hR (hG.U0.2 hC.U0)) (fun v hv ↦ zp_of_good R hR (hG.cov v hv)) hib
  · obtain ⟨h1, h2, h3, h4⟩ := hG.pts q hq
    have hpq := hp q hq
    obtain ⟨u1, u2, u3⟩ := certUnits R hR h2 hpq.1
    exact ⟨mem_intSub_of_ok R hR h1.1, u1, inSB_of_good R hR h3, u2, u3,
      unitAt_of (mem_intSub_of_ok R hR h4.1)⟩
  · obtain ⟨u1, u2, u3⟩ := certUnits R hR hG.inf.1 hci
    exact ⟨u1, inSB_of_good R hR hG.inf.2, u2, u3⟩

lemma goodLL_getD {L : List (List K)} (h : GoodLL R L) (i : ℕ) : ∀ c ∈ L.getD i [], Good R c := by
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; simp

include hR in
lemma zp_getDD {L : List (List K)} (h : GoodLL R L) (i t : ℕ) : ZP Sφ ((L.getD i []).getD t 0) := by
  by_cases ht : t < (L.getD i []).length
  · rw [List.getD_eq_getElem _ _ ht]
    exact zp_of_good R hR (goodLL_getD R h i _ (List.getElem_mem ht))
  · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl rfl

lemma okB_of {W : BPoly K} (h : ∀ P ∈ W, ∀ c ∈ P, R.ok c = true) : okB R W = true := by
  simpa [okB, List.all_eq_true] using h

include hR in
lemma mapLL_pext_eq {L : List (List K)} (h : GoodLL R L) :
    L.map (·.map R.red) = L.map (·.map (pext Sφ gφ)) :=
  List.map_congr_left fun l hl ↦ (map_pext_eq R hR fun c hc ↦ (h l hl c hc).1).symm

include hR in
/-- **The reduced prime certificate passes `primeCheck`.** -/
theorem primeCheck_redPrimeCert (T : GlobalCert K) (xs : List K) (ys : List (List K))
    (lam : List (List K)) (Ls : List (List (List K))) (irrP : ℕ) (hC : Char0Base T xs ys lam Ls irrP)
    (hG : GoodBase R T xs ys lam Ls irrP) :
    primeCheck R T (redPrimeCert R T xs ys lam Ls irrP) = true := by
  have hok0 : R.ok 0 = true := hG.zero.1
  have hokF := ok_of_goodLL R hG.F
  have hokB : ∀ W ∈ T.I.Bc, ∀ P ∈ W, ∀ c ∈ P, R.ok c = true := fun W hW ↦ ok_of_goodLL R (hG.B W hW)
  have hokx : ∀ c ∈ xs, R.ok c = true := fun c hc ↦ (hG.x c hc).1
  have hoky := ok_of_goodLL R hG.y
  have hF : InSB Sφ T.Fc := inSB_of_good R hR hG.F
  have hxS : InS Sφ xs := inS_of_good R hR hG.x
  have hFp : redBL R T.Fc = T.Fc.map (·.map (pext Sφ gφ)) := redBL_eq_pext R hR hokF
  have hxs : xs.map R.red = xs.map (pext Sφ gφ) := (map_pext_eq R hR hokx).symm
  have hys : ys.map (·.map R.red) = ys.map (·.map (pext Sφ gφ)) := mapLL_pext_eq R hR hG.y
  have hDp : T.I.Dc.map R.red = T.I.Dc.map (pext Sφ gφ) :=
    (map_pext_eq R hR fun c hc ↦ (hG.D c hc).1).symm
  have hyS : ∀ i, InS Sφ (ys.getD i []) := fun i ↦ inS_of_good R hR (goodLL_getD R hG.y i)
  have hdF := derivYB_pext (g := gφ) T.Fc hF
  -- irreducibility
  have hirr : irrAt (redBL R T.Fc) T.n T.kD ((xs.map R.red).getD 0 0)
      ((ys.map (·.map R.red)).getD 0 []) irrP = true := by
    rw [hFp, hxs, getD_pext, hys, getD_mapLL]
    have hc := hC.irr
    simp only [irrAt, irrSubsetCheck, Bool.and_eq_true] at hc
    obtain ⟨u1, u2, u3⟩ := certUnits R hR hG.lift hc.1.1.1
    exact irrAt_pext hF (hxS.getD 0) (hyS 0)
      (fun y0 hy0 v hv ↦ ⟨hC.newton y0 hy0 v hv,
        mem_intSub_of_ok R hR ((hG.newton y0 hy0 v hv).2 (hC.newton y0 hy0 v hv))⟩)
      u2 u3 (fun L hL i t ↦ zp_getDD R hR (hG.prods L hL) i t) hC.irr
  -- the base points
  have hbase : ∀ i < xs.length,
      ((ys.map (·.map R.red)).getD i []).length = T.n ∧ ((ys.map (·.map R.red)).getD i []).Nodup ∧
      Kron.evalC (T.I.Dc.map R.red) ((xs.map R.red).getD i 0) ≠ 0 ∧ ∀ k < T.n,
        evalB (redBL R T.Fc) ((xs.map R.red).getD i 0) (((ys.map (·.map R.red)).getD i []).getD k 0)
          = 0 ∧
        evalB (derivYB (redBL R T.Fc)) ((xs.map R.red).getD i 0)
          (((ys.map (·.map R.red)).getD i []).getD k 0) ≠ 0 := by
    intro i hi
    obtain ⟨b1, b2, b3, b4⟩ := hC.base i hi
    obtain ⟨g1, g2, g3⟩ := hG.base i hi
    rw [hys, getD_mapLL, hxs, getD_pext, hDp, hFp, ← hdF.2]
    refine ⟨by rw [List.length_map]; exact b1, nodup_pext (hyS i) b2
      fun k hk l hl ↦ zp_of_good R hR (g3 k hk l hl), ?_, fun k hk ↦ ⟨?_, ?_⟩⟩
    · rw [← (evalC_pext (hxS.getD i) _ (inS_of_good R hR hG.D)).2]
      exact pext_ne_zero_of_zp (zp_of_good R hR g1) b3
    · rw [getD_pext, ← (evalB_pext (hxS.getD i) ((hyS i).getD k) _ hF).2, (b4 k hk).1, pext_zero]
    · rw [getD_pext, ← (evalB_pext (hxS.getD i) ((hyS i).getD k) _ hdF.1).2]
      exact pext_ne_zero_of_zp (zp_of_good R hR (g2 k hk)) (b4 k hk).2
  have hδ0 : T.I.δL.getD 0 0 = 0 := by
    have := hC.glob.norm
    simp only [normCheck, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.2
  simp only [primeCheck, redPrimeCert, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc]
  refine ⟨okB_of R hokF, fun W hW ↦ okB_of R (hokB W hW), fun c hc ↦ (hG.D c hc).1,
    fun c hc ↦ (hG.G c hc).1, by rw [hC.αL]; simp, by rw [hC.yL]; simp, hG.E.1,
    ib_red R hR T xs ys lam Ls irrP hC hG, ?_, ?_, ?_, ?_, fun i hi ↦ ?_, ?_, ?_,
    by rw [hC.αL]; simp, by rw [hC.αL]; simp, by rw [hC.αL, hC.yL]; simp [GlobalCert.ptCheck],
    rfl, ?_⟩
  · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨decide_eq_true hC.irrP0, hirr⟩
  · simpa using hC.gen
  · refine decide_eq_true ?_
    rw [hxs]
    exact nodup_pext hxS hC.xnd fun i hi j hj ↦ zp_of_good R hR (hG.xd i hi j hj)
  · simpa using hC.ysl
  · rw [List.length_map] at hi
    obtain ⟨b1, b2, b3, b4⟩ := hbase i hi
    exact ⟨decide_eq_true b1, decide_eq_true b2, decide_eq_true b3,
      fun k hk ↦ ⟨decide_eq_true (b4 k hk).1, decide_eq_true (b4 k hk).2⟩⟩
  · rw [List.length_map]
    exact detCheck_red R φ hR hok0 hokB hokx hoky (fun L hL ↦ ok_of_goodLL R (hG.Ls L hL)) hC.det
  · rw [List.length_map]
    exact nsCheck_red R φ hR hok0 hokB hokx hoky (ok_of_goodLL R hG.lam) hC.ns
  · rw [hC.αL]
    simp only [princWitCheck, testSide, List.map_nil, List.length_nil, List.range_zero,
      List.all_nil, Bool.and_true, Bool.true_and, List.any_eq_true, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨0, hC.n0, 0, by omega, by rw [hδ0]; omega, by simp⟩

end Red

end Curves
