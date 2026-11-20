import RischTragerBronstein.Torsion.PrimeCertExist2

/-!
# Prime certificates exist (3): goodness at all large primes

Over a number field `NF M`, with the reductions of `nfRedAt` (`NFRed`), every property of the form
"finitely many explicit elements are good" holds at all large primes. `EvG P`: `P R` for every
such reduction `R` at every large prime; closed under conjunction and bounded quantification
(`EvG.and`, `evG_mem`, `evG_lt`). **`evG_goodBase`**: the goodness hypotheses of the reduced
prime certificate hold at all large primes.
-/

open Polynomial Filter

namespace Curves

open CPoly Sup

section Ev

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

local notation "KM" => NFC.NF M

/-- `P` holds for the reductions of `nfRedAt` at all large primes. -/
def EvG (P : (p : ℕ) → RedFns p KM → Prop) : Prop :=
  ∀ᶠ p in atTop, ∀ R : RedFns p KM, NFRed p R → P p R

lemma EvG.and {P Q : (p : ℕ) → RedFns p KM → Prop} (hP : EvG P) (hQ : EvG Q) :
    EvG fun p R ↦ P p R ∧ Q p R :=
  (Filter.Eventually.and hP hQ).mono fun _ h R hR ↦ ⟨h.1 R hR, h.2 R hR⟩

lemma EvG.mono {P Q : (p : ℕ) → RedFns p KM → Prop} (hP : EvG P) (h : ∀ p R, P p R → Q p R) :
    EvG Q :=
  Filter.Eventually.mono hP fun p hp R hR ↦ h p R (hp R hR)

lemma evG_const {P : Prop} (h : P) : EvG (M := M) fun _ _ ↦ P :=
  Filter.Eventually.of_forall fun _ _ _ ↦ h

lemma evG_mem {α : Type*} (l : List α) {P : α → (p : ℕ) → RedFns p KM → Prop}
    (h : ∀ a ∈ l, EvG (P a)) : EvG fun p R ↦ ∀ a ∈ l, P a p R := by
  induction l with
  | nil => exact (evG_const trivial).mono fun _ _ _ a ha ↦ absurd ha List.not_mem_nil
  | cons a l ih =>
    refine ((h a List.mem_cons_self).and (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb))).mono
      fun p R hPR b hb ↦ ?_
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hPR.1
    · exact hPR.2 b hb

lemma evG_lt (n : ℕ) {P : ℕ → (p : ℕ) → RedFns p KM → Prop} (h : ∀ i < n, EvG (P i)) :
    EvG fun p R ↦ ∀ i < n, P i p R :=
  (evG_mem (List.range n) fun i hi ↦ h i (List.mem_range.mp hi)).mono fun _ _ hPR i hi ↦
    hPR i (List.mem_range.mpr hi)

lemma evG_good (x : KM) : EvG fun p R ↦ Good R x :=
  (ev_good [x]).mono fun _ h R hR ↦ h R hR x List.mem_cons_self

lemma evG_goodL (l : List KM) : EvG fun p R ↦ ∀ c ∈ l, Good R c :=
  evG_mem l fun c _ ↦ evG_good c

lemma evG_goodLL (L : List (List KM)) : EvG fun p R ↦ GoodLL R L :=
  evG_mem L fun l _ ↦ evG_goodL l

lemma evG_goodDif (ys : List (List KM)) (prec : ℕ) : EvG fun p R ↦ GoodDif R ys prec :=
  evG_lt _ fun k _ ↦ evG_lt _ fun l _ ↦ evG_lt _ fun i _ ↦ evG_good _

lemma evG_goodCert (Fc : BPoly KM) (a : KM) (c : BranchCert KM) :
    EvG fun p R ↦ GoodCert R Fc a c :=
  (evG_goodLL c.ys).and ((evG_mem c.ys fun y _ ↦ evG_good _).and (evG_goodDif c.ys c.prec))

/-- **The goodness hypotheses of the reduced prime certificate hold at all large primes.** -/
theorem evG_goodBase (T : GlobalCert KM) (xs : List KM) (ys : List (List KM)) (lam : List (List KM))
    (Ls : List (List (List KM))) (irrP : ℕ) :
    EvG fun p R ↦ GoodBase R T xs ys lam Ls irrP := by
  have h1 := (evG_good 0).and ((evG_goodLL T.Fc).and ((evG_mem T.I.Bc fun W _ ↦ evG_goodLL W).and
    ((evG_goodL T.I.Dc).and ((evG_goodL T.G).and ((evG_good T.aE).and ((evG_goodL xs).and
    ((evG_goodLL ys).and ((evG_goodLL lam).and (evG_mem Ls fun L _ ↦ evG_goodLL L)))))))))
  have h2 := (evG_mem T.I.pts fun q _ ↦ (evG_good q.1).and ((evG_goodCert T.Fc q.1 q.2.1).and
    ((evG_goodLL q.2.2).and (evG_good (unitAtEl T.I.Dc q.1 q.2.1.N)⁻¹)))).and
    (((evG_goodCert (invB T.Fc T.k (T.k * T.n)) 0 T.I.infc).and (evG_goodLL T.I.Linf)).and
    ((evG_good (T.I.Dc.getD (T.I.Dc.length - 1) 0)).and ((evG_good (infU0 T.I)).and
    (evG_goodL (coverVals T.G (T.I.pts.map Prod.fst))))))
  have h3 := (evG_mem (ys.getD 0 []) fun y0 _ ↦ evG_goodL (newtonVals
      (T.Fc.map fun q ↦ compC q (shiftC (xs.getD 0 0) 1)) irrP (Nat.log2 irrP + 3) [y0])).and
    ((evG_goodCert T.Fc (xs.getD 0 0) (liftRootsAt T.Fc (xs.getD 0 0) (ys.getD 0 []) irrP)).and
    (evG_mem (subsetsL T.n) fun L _ ↦
      evG_goodLL (prodSubB (liftRootsAt T.Fc (xs.getD 0 0) (ys.getD 0 []) irrP).ys L)))
  have h4 := (evG_lt xs.length fun i _ ↦ (evG_good (Kron.evalC T.I.Dc (xs.getD i 0))).and
    ((evG_lt T.n fun k _ ↦ evG_good (evalB (derivYB T.Fc) (xs.getD i 0) ((ys.getD i []).getD k 0))).and
    (evG_lt (ys.getD i []).length fun k _ ↦ evG_lt (ys.getD i []).length fun l _ ↦
      evG_good ((ys.getD i []).getD k 0 - (ys.getD i []).getD l 0)))).and
    (evG_lt xs.length fun i _ ↦ evG_lt xs.length fun j _ ↦ evG_good (xs.getD i 0 - xs.getD j 0))
  refine (h1.and (h2.and (h3.and h4))).mono fun p R h ↦ ?_
  obtain ⟨⟨z, F, B, D, G, E, x, y, lm, L⟩, ⟨pts, ⟨inf, Li⟩, last, U0, cov⟩, ⟨nw, lift, prods⟩,
    base, xd⟩ := h
  exact ⟨z, F, B, D, G, E, x, y, lm, L, pts, ⟨inf, Li⟩, last, U0, cov, nw, lift, prods, base, xd⟩

/-- **The reduced prime certificate passes `primeCheck` at all large primes** (for every
certified reduction with the integrality test of `nfRedAt`). -/
theorem ev_primeCheck (T : GlobalCert KM) (xs : List KM) (ys : List (List KM))
    (lam : List (List KM)) (Ls : List (List (List KM))) (irrP : ℕ)
    (hC : Char0Base T xs ys lam Ls irrP) :
    ∀ᶠ p in atTop, ∀ (_ : Fact p.Prime) (R : RedFns p KM), NFRed p R →
      ∀ φ : KM →+* ℚ_[p], RedValid p R φ →
        primeCheck R T (redPrimeCert R T xs ys lam Ls irrP) = true :=
  Filter.Eventually.mono (evG_goodBase T xs ys lam Ls irrP) fun _ h _ R hR _ hφ ↦
    primeCheck_redPrimeCert R hφ T xs ys lam Ls irrP hC (h R hR)

end Ev

end Curves
