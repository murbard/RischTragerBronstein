import RischTragerBronstein.Jacobian.Cert
import Mathlib.NumberTheory.Padics.Hensel
import RischTragerBronstein.Computable.Kronecker

/-!
# Checkable non-torsion certificates for hyperelliptic Jacobians

For `y² = f(x)` with `f ∈ ℤ[x]` of degree `2g + 1` and a divisor `Γ` supported on integral
non-branch points (`EDiv ℤ`), a `LocalCert` at a prime `p` records

* `g` abscissae `xs` with ordinates `ys` modulo `p` (the base divisor `E₀`, lifted to `ℤ_p` by
  Hensel's lemma),
* the exact order `m` of `Γ̄` modulo `p`: a division-free witness (`principalCert`) that `m Γ̄` is
  principal, and `principalC … = none` for `(m / r) Γ̄` for every divisor `r ≥ 2` of `m`
  (`exact_order`).

`localCheck` checks all of this with a single Boolean (evaluable by `decide +kernel`), and
`nonTorsionCheck` combines two primes with an incompatibility witness `r ^ k`.

`not_torsion_of_check`: if `nonTorsionCheck` succeeds, `Γ` (over `ℚ`) is **not torsion**: no
positive multiple is principal.
-/

open Polynomial CPoly CPoly.Kron

namespace Jac

section Hensel

variable {p : ℕ} [hp : Fact p.Prime]

/-- Square roots in `ℤ_p` by Hensel's lemma. -/
lemma exists_sqrt (hp2 : p ≠ 2) (c y₀ : ℤ_[p]) (hy₀ : IsUnit y₀) (hc : ‖y₀ ^ 2 - c‖ < 1) :
    ∃ y : ℤ_[p], y ^ 2 = c ∧ IsUnit y ∧ ‖y - y₀‖ < 1 := by
  have h2 : ‖(2 : ℤ_[p])‖ = 1 := by
    have := (PadicInt.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr
      ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    simpa using this
  have hy1 : ‖y₀‖ = 1 := PadicInt.isUnit_iff.mp hy₀
  set F : ℤ_[p][X] := X ^ 2 - C c
  have e1 : ∀ w : ℤ_[p], F.aeval w = w ^ 2 - c := fun w ↦ by simp [F]
  have e2 : F.derivative.aeval y₀ = 2 * y₀ := by
    simp [F]; left; norm_num
  have hd : ‖F.derivative.aeval y₀‖ = 1 := by rw [e2, norm_mul, h2, hy1, one_mul]
  have hF : ‖F.aeval y₀‖ < ‖F.derivative.aeval y₀‖ ^ 2 := by rw [hd, one_pow, e1]; exact hc
  obtain ⟨z, hz, hzd, -, -⟩ := hensels_lemma hF
  rw [hd] at hzd
  refine ⟨z, ?_, ?_, hzd⟩
  · rw [e1] at hz; exact sub_eq_zero.mp hz
  · rw [PadicInt.isUnit_iff]
    have : z = y₀ + (z - y₀) := by ring
    rw [this, PadicInt.norm_add_eq_max_of_ne (by rw [hy1]; exact (ne_of_gt hzd)), hy1]
    exact max_eq_left hzd.le

lemma isUnit_intCast {k : ℤ} (h : ¬ (p : ℤ) ∣ k) : IsUnit (k : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  exact le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun hlt ↦ h ((PadicInt.norm_int_lt_one_iff_dvd k).mp hlt))

end Hensel

/-- Certificate data at one prime. -/
structure LocalCert where
  xs : List ℤ
  ys : List ℤ
  m : ℕ
  a : List ℤ
  b : List ℤ
  Vs : List (List ℤ)
  deriving Repr

/-- Reduction of an integer coefficient list modulo `p`. -/
def castL (p : ℕ) (l : List ℤ) : CPoly (ZMod p) := l.map (Int.castRingHom (ZMod p))

/-- The pole bounds of `PrincipalMul` as strict degree bounds for `principalC`. -/
def boundA (N : ℕ) : ℕ := N / 2 + 1
def boundB (g N : ℕ) : ℕ := (N + 1) / 2 - g

/-- The good-reduction conditions at `p` for the curve, `Γ`, and the base points `E₀`. -/
abbrev baseCheck (p : ℕ) (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (xs ys : List ℤ) : Prop :=
  p ≠ 2 ∧ f.length = 2 * g + 2 ∧ ¬ (p : ℤ) ∣ f.getD (2 * g + 1) 0 ∧
    xs.length = g ∧ ys.length = g ∧
    (∀ i ∈ List.range g, (p : ℤ) ∣ ys.getD i 0 ^ 2 - evalC f (xs.getD i 0) ∧
      ¬ (p : ℤ) ∣ ys.getD i 0) ∧
    xs.Pairwise (fun u v ↦ ¬ (p : ℤ) ∣ u - v) ∧
    (∀ q ∈ Γ, ¬ (p : ℤ) ∣ 2 * q.2.1 ∧ q.2.1 ^ 2 = evalC f q.1 ∧
      ∀ x ∈ xs, ¬ (p : ℤ) ∣ q.1 - x) ∧
    Γ.Pairwise (fun u v ↦ ¬ (p : ℤ) ∣ u.1 - v.1)

/-- **The check at one prime.** -/
def localCheck (p : ℕ) [Fact p.Prime] (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (c : LocalCert) :
    Bool :=
  decide (baseCheck p f g Γ c.xs c.ys ∧ 1 ≤ c.m) &&
  principalCert (castL p f) g (escale c.m (emap (Int.castRingHom (ZMod p)) Γ)) (castL p c.a)
    (castL p c.b) (c.Vs.map (castL p)) &&
  (List.range (c.m + 1)).all fun r ↦ !decide (2 ≤ r ∧ r ∣ c.m) ||
    (principalC (castL p f) (escale (c.m / r) (emap (Int.castRingHom (ZMod p)) Γ))
      (boundA (c.m / r * edeg Γ)) (boundB g (c.m / r * edeg Γ))).isNone

/-- **The two-prime non-torsion check.** -/
def nonTorsionCheck (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (cp cq : LocalCert) (r k : ℕ) : Bool :=
  localCheck p f g Γ cp && localCheck q f g Γ cq &&
  decide (r.Prime ∧ ((r ≠ q ∧ r ^ k ∣ cp.m ∧ ¬ r ^ k ∣ cq.m) ∨
    (r ≠ p ∧ r ^ k ∣ cq.m ∧ ¬ r ^ k ∣ cp.m)))

section Spec

variable {p : ℕ} [hp : Fact p.Prime]

local notation "ιp" => Int.castRingHom ℤ_[p]
local notation "ρp" => IsLocalRing.residue ℤ_[p]

lemma castL_eq (l : List ℤ) : toPoly (castL p l) = (toPoly l).map (Int.castRingHom (ZMod p)) := by
  induction l with
  | nil => simp [castL]
  | cons a l ih => simpa [castL] using ih

lemma emap_emap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S)
    (ψ : S →+* T) (Γ : EDiv R) : emap ψ (emap φ Γ) = emap (ψ.comp φ) Γ := by
  simp [emap, Function.comp_def]

lemma emap_id {R : Type*} [CommRing R] (Γ : EDiv R) : emap (RingHom.id R) Γ = Γ := by
  simp [emap]

lemma degree_lt_of_poleLE {K : Type*} [Field K] {g N : ℕ} {ψ : K[X] × K[X]} (h : PoleLE g ψ N) :
    ψ.1.degree < boundA N ∧ ψ.2.degree < boundB g N := by
  constructor
  · have : ψ.1.natDegree < boundA N := by have := h.1; unfold boundA; omega
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast this)
  · rcases h.2 with h0 | h1
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · have : ψ.2.natDegree < boundB g N := by unfold boundB; omega
      exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast this)

lemma isUnit_intCast_sub (x y : ℤ) (h : ¬ (p : ℤ) ∣ x - y) :
    IsUnit ((x : ℤ_[p]) - (y : ℤ_[p])) := by
  have := isUnit_intCast (p := p) h; push_cast at this; exact this

/-- The facts behind `baseCheck`, over `ℤ`, `ℤ_p` and `𝔽_p`. -/
structure BaseFacts (p : ℕ) [Fact p.Prime] (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) : Prop where
  hp2 : p ≠ 2
  hdeg : ((toPoly f).map (Int.castRingHom ℤ_[p])).natDegree = 2 * g + 1
  hlc : IsUnit ((toPoly f).map (Int.castRingHom ℤ_[p])).leadingCoeff
  hE0 : ∃ xp yp : Fin g → ℤ_[p], (∀ i, IsUnit (yp i)) ∧
      (∀ i, yp i ^ 2 = ((toPoly f).map (Int.castRingHom ℤ_[p])).eval (xp i)) ∧
      (∀ i j, i ≠ j → IsUnit (xp i - xp j)) ∧ (∀ r ∈ emap (Int.castRingHom ℤ_[p]) Γ, ∀ i, IsUnit (r.1 - xp i))
  hon : OnCurve ((toPoly f).map (Int.castRingHom ℤ_[p])) (emap (Int.castRingHom ℤ_[p]) Γ)
  hpw : (emap (Int.castRingHom ℤ_[p]) Γ).Pairwise (fun r r' ↦ IsUnit (r.1 - r'.1))
  hΓZ : ∀ q ∈ Γ, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = (toPoly f).eval q.1
  hΓne : Γ.Pairwise (fun u v ↦ u.1 ≠ v.1)
  ef : ((toPoly f).map (Int.castRingHom ℤ_[p])).map (PadicInt.toZMod (p := p)) = toPoly (castL p f)
  eΓ : emap (PadicInt.toZMod (p := p)) (emap (Int.castRingHom ℤ_[p]) Γ) = emap (Int.castRingHom (ZMod p)) Γ
  hΓp : ∀ n, ∀ q ∈ escale n (emap (Int.castRingHom (ZMod p)) Γ), 2 * q.2.1 ≠ 0 ∧
      q.2.1 ^ 2 = (toPoly (castL p f)).eval q.1
  hdegZ : (toPoly (castL p f)).natDegree = 2 * g + 1
  honZ : OnCurve (toPoly (castL p f)) (emap (Int.castRingHom (ZMod p)) Γ)
  hndZ : ((emap (Int.castRingHom (ZMod p)) Γ).map Prod.fst).Nodup

theorem baseCheck_spec {f : List ℤ} {g : ℕ} {Γ : EDiv ℤ} {xs ys : List ℤ}
    (h : baseCheck p f g Γ xs ys) : BaseFacts p f g Γ := by
  obtain ⟨hp2, hlen, hlc, hxl, hyl, hE, hxd, hΓ, hΓd⟩ := h
  have hcoef : ∀ n, ((toPoly f).map ιp).coeff n = ((f.getD n 0 : ℤ) : ℤ_[p]) := by
    intro n; rw [coeff_map, coeff_toPoly]; rfl
  have hlc0 : ((toPoly f).map ιp).coeff (2 * g + 1) ≠ 0 := by
    rw [hcoef]; exact (isUnit_intCast hlc).ne_zero
  have hdeg : ((toPoly f).map ιp).natDegree = 2 * g + 1 := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero hlc0)
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [hcoef, List.getD_eq_default _ _ (by rw [hlen]; exact_mod_cast hn), Int.cast_zero]
  have heval : ∀ t : ℤ, ((toPoly f).map ιp).eval (t : ℤ_[p]) = ((evalC f t : ℤ) : ℤ_[p]) := by
    intro t
    rw [evalC_eq, eval_map, show (t : ℤ_[p]) = ιp t from rfl, eval₂_at_apply]; rfl
  have ef : ((toPoly f).map ιp).map (PadicInt.toZMod (p := p)) = toPoly (castL p f) := by
    rw [castL_eq, Polynomial.map_map]; congr 1; exact RingHom.ext_int _ _
  have eΓ : emap (PadicInt.toZMod (p := p)) (emap ιp Γ) =
      emap (Int.castRingHom (ZMod p)) Γ := by
    rw [emap_emap]; congr 1; exact RingHom.ext_int _ _
  have hΓZ : ∀ n, ∀ q ∈ escale n (emap (Int.castRingHom (ZMod p)) Γ), 2 * q.2.1 ≠ 0 ∧
      q.2.1 ^ 2 = (toPoly (castL p f)).eval q.1 := by
    intro n r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr'
    refine ⟨?_, ?_⟩
    · show (2 : ZMod p) * ((q.2.1 : ℤ) : ZMod p) ≠ 0
      rw [show (2 : ZMod p) * ((q.2.1 : ℤ) : ZMod p) = ((2 * q.2.1 : ℤ) : ZMod p) by
        push_cast; ring, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (hΓ q hq).1
    · show ((q.2.1 : ℤ) : ZMod p) ^ 2 = (toPoly (castL p f)).eval ((q.1 : ℤ) : ZMod p)
      rw [castL_eq, eval_map, show ((q.1 : ℤ) : ZMod p) = Int.castRingHom (ZMod p) q.1 from rfl,
        eval₂_at_apply, ← evalC_eq, ← (hΓ q hq).2.1, map_pow]; rfl
  have hlcU : IsUnit ((toPoly f).map ιp).leadingCoeff := by
    rw [leadingCoeff, hdeg, hcoef]; exact isUnit_intCast hlc
  refine ⟨hp2, hdeg, hlcU, ?_, ?_, ?_, ?_, ?_, ef, eΓ, hΓZ, ?_, ?_, ?_⟩
  · -- the base divisor `E₀`
    have hex : ∀ i : Fin g, ∃ y : ℤ_[p],
        y ^ 2 = ((toPoly f).map ιp).eval ((xs.getD i 0 : ℤ) : ℤ_[p]) ∧ IsUnit y := by
      intro i
      obtain ⟨hdv, hnu⟩ := hE i (List.mem_range.mpr i.2)
      obtain ⟨y, hy, hyu, -⟩ := exists_sqrt hp2
        (((toPoly f).map ιp).eval ((xs.getD i 0 : ℤ) : ℤ_[p]))
        (ys.getD i 0 : ℤ) (isUnit_intCast hnu) (by
          rw [heval, ← Int.cast_pow, ← Int.cast_sub]
          exact (PadicInt.norm_int_lt_one_iff_dvd _).mpr hdv)
      exact ⟨y, hy, hyu⟩
    choose yp hyp hyu using hex
    refine ⟨fun i ↦ ((xs.getD i 0 : ℤ) : ℤ_[p]), yp, hyu, hyp, ?_, ?_⟩
    · intro i j hij
      apply isUnit_intCast_sub
      have hi : (i : ℕ) < xs.length := by rw [hxl]; exact i.2
      have hj : (j : ℕ) < xs.length := by rw [hxl]; exact j.2
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
      · exact List.pairwise_iff_getElem.mp hxd _ _ hi hj hlt
      · intro hd
        exact List.pairwise_iff_getElem.mp hxd _ _ hj hi hlt ((dvd_sub_comm).mp hd)
    · intro r hr i
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      apply isUnit_intCast_sub
      have hi : (i : ℕ) < xs.length := by rw [hxl]; exact i.2
      rw [List.getD_eq_getElem _ _ hi]
      exact (hΓ q hq).2.2 _ (List.getElem_mem hi)
  · intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    refine ⟨?_, ?_⟩
    · have := isUnit_intCast (p := p) (hΓ q hq).1; push_cast at this; exact this
    · change ((q.2.1 : ℤ) : ℤ_[p]) ^ 2 = ((toPoly f).map ιp).eval ((q.1 : ℤ) : ℤ_[p])
      rw [heval, ← (hΓ q hq).2.1]; push_cast; rfl
  · exact List.pairwise_map.mpr (hΓd.imp fun h ↦ isUnit_intCast_sub _ _ h)
  · intro q hq
    refine ⟨fun h0 ↦ (hΓ q hq).1 (by rw [h0]; exact dvd_zero _), ?_⟩
    rw [(hΓ q hq).2.1, evalC_eq]
  · exact hΓd.imp fun h he ↦ h (by rw [he, sub_self]; exact dvd_zero _)
  · rw [← ef, natDegree_map_of_leadingCoeff_ne_zero _ (hlcU.map _).ne_zero, hdeg]
  · intro r hr
    have := hΓZ 1 (r.1, r.2.1, 1 * r.2.2) (List.mem_map.mpr ⟨r, hr, rfl⟩)
    exact ⟨IsUnit.mk0 _ this.1, this.2⟩
  · simp only [emap, List.map_map, List.Nodup]
    rw [List.pairwise_map]
    refine hΓd.imp fun {u v} h he ↦ h ?_
    have he' : ((u.1 - v.1 : ℤ) : ZMod p) = 0 := by
      push_cast; exact sub_eq_zero.mpr (by simpa using he)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he'

/-- The facts extracted from a successful `localCheck`. -/
theorem localCheck_spec {f : List ℤ} {g : ℕ} {Γ : EDiv ℤ} {c : LocalCert}
    (h : localCheck p f g Γ c = true) :
    BaseFacts p f g Γ ∧ 1 ≤ c.m ∧
    PrincipalMul (((toPoly f).map ιp).map ρp) g (emap ρp (emap ιp Γ)) c.m ∧
    (∀ m', 1 ≤ m' → m' < c.m →
      ¬ PrincipalMul (((toPoly f).map ιp).map ρp) g (emap ρp (emap ιp Γ)) m') := by
  simp only [localCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨hb, hm1⟩, hcert⟩, hmin⟩ := h
  have B := baseCheck_spec hb
  have hmZ : PrincipalMul (toPoly (castL p f)) g (emap (Int.castRingHom (ZMod p)) Γ) c.m := by
    obtain ⟨ψ, h0, hpl, hv⟩ := principalCert_sound hcert
    refine ⟨ψ, h0, ?_, hv⟩
    rwa [edeg_escale] at hpl
  have hminZ := exact_order B.hdegZ B.honZ B.hndZ hmZ (fun r hr hrd hP ↦ by
    obtain ⟨ψ, h0, hpl, hv⟩ := hP
    rw [edeg_emap] at hpl
    obtain ⟨hA, hB⟩ := degree_lt_of_poleLE hpl
    have := principalC_complete (RingHom.id _) (castL p f) _ _ _ (B.hΓp _) ψ h0 hA hB
      (by rwa [Polynomial.map_id, emap_id])
    rcases hmin r (Nat.lt_succ_of_le (Nat.le_of_dvd hm1 hrd)) with h | h
    · exact h ⟨hr.two_le, hrd⟩
    · exact this h)
  refine ⟨B, hm1, ?_, ?_⟩
  · apply principal_residue_of_zmod
    rw [B.ef, B.eΓ]; exact hmZ
  · intro m' h1 h2 hP
    have hP' := principal_zmod_of_residue _ _ hP
    rw [B.ef, B.eΓ] at hP'
    exact hminZ m' h1 h2 hP'

end Spec

/-! ### Searching for certificates (untrusted; every answer is re-checked by `nonTorsionCheck`) -/

/-- A nonzero square root modulo `p`, by search. -/
def sqrtMod (p : ℕ) (c : ℤ) : Option ℤ :=
  ((List.range p).find? fun y : ℕ ↦ y != 0 && ((y : ℤ) ^ 2 - c) % (p : ℤ) == 0).map Int.ofNat

/-- `g` points of `E₀` modulo `p`, away from the abscissae of `Γ`. -/
def findE0 (p : ℕ) (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) : Option (List ℤ × List ℤ) :=
  let cands := (List.range p).filterMap fun x : ℕ ↦
    if Γ.all (fun q ↦ (q.1 - (x : ℤ)) % (p : ℤ) != 0) then
      (sqrtMod p (evalC f (x : ℤ))).map fun y ↦ ((x : ℤ), y)
    else none
  if cands.length < g then none else some ((cands.take g).map (·.1), (cands.take g).map (·.2))

/-- Integer representatives. -/
def zlift (p : ℕ) (l : CPoly (ZMod p)) : List ℤ := l.map fun c ↦ (c.val : ℤ)

/-- The order of `Γ̄` modulo `p` (up to `bound`), with a principal function and its jets. -/
def findOrder (p : ℕ) [Fact p.Prime] (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (bound : ℕ) :
    Option (ℕ × List ℤ × List ℤ × List (List ℤ)) :=
  let f' := castL p f
  let Γ' := emap (Int.castRingHom (ZMod p)) Γ
  (List.range bound).findSome? fun i ↦
    let N := (i + 1) * edeg Γ
    (principalC f' (escale (i + 1) Γ') (boundA N) (boundB g N)).map fun jc ↦
      let full := jc.2.set jc.1 1
      (i + 1, zlift p (full.take (boundA N)), zlift p (full.drop (boundA N)),
        (branchesC f' (escale (i + 1) Γ')).map (zlift p))

/-- A local certificate at `p`, if one is found and passes `localCheck`. -/
def findLocal (p : ℕ) (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (bound : ℕ) : Option LocalCert :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    match findE0 p f g Γ with
    | none => none
    | some (xs, ys) =>
      match findOrder p f g Γ bound with
      | none => none
      | some (m, a, b, Vs) =>
        let c : LocalCert := ⟨xs, ys, m, a, b, Vs⟩
        if localCheck p f g Γ c then some c else none
  else none

/-- An incompatibility witness `(r, k)` for the orders `mp` at `p` and `mq` at `q`. -/
def findWitness (p q mp mq : ℕ) : Option (ℕ × ℕ) :=
  ((List.range (mp + mq + 1)).flatMap fun r ↦ (List.range (mp + mq + 1)).map fun k ↦ (r, k)).find?
    fun rk ↦ decide (rk.1.Prime ∧ ((rk.1 ≠ q ∧ rk.1 ^ rk.2 ∣ mp ∧ ¬ rk.1 ^ rk.2 ∣ mq) ∨
      (rk.1 ≠ p ∧ rk.1 ^ rk.2 ∣ mq ∧ ¬ rk.1 ^ rk.2 ∣ mp)))

/-- The search loop: local certificates found so far, remaining primes. -/
def findCertAux (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (bound : ℕ) :
    List (ℕ × LocalCert) → List ℕ → Option (ℕ × ℕ × LocalCert × LocalCert × ℕ × ℕ)
  | _, [] => none
  | found, q :: qs =>
    match findLocal q f g Γ bound with
    | none => findCertAux f g Γ bound found qs
    | some cq =>
      match found.findSome? fun pc ↦ (findWitness pc.1 q pc.2.m cq.m).map fun rk ↦
          (pc.1, q, pc.2, cq, rk.1, rk.2) with
      | some r => some r
      | none => findCertAux f g Γ bound ((q, cq) :: found) qs

/-- **Certificate search**: local certificates at the given primes, until two are incompatible. -/
def findCert (f : List ℤ) (g : ℕ) (Γ : EDiv ℤ) (primes : List ℕ) (bound : ℕ) :
    Option (ℕ × ℕ × LocalCert × LocalCert × ℕ × ℕ) :=
  findCertAux f g Γ bound [] primes

/-- **Soundness of the non-torsion check**: no positive multiple of `Γ` is principal over `ℚ`. -/
theorem not_torsion_of_check {f : List ℤ} {g : ℕ} {Γ : EDiv ℤ} {p q : ℕ} [hp : Fact p.Prime]
    [hq : Fact q.Prime] {cp cq : LocalCert} {r k : ℕ}
    (h : nonTorsionCheck f g Γ p q cp cq r k = true) :
    ∀ n, 1 ≤ n → ¬ PrincipalMul ((toPoly f).map (Int.castRingHom ℚ)) g
      (emap (Int.castRingHom ℚ) Γ) n := by
  simp only [nonTorsionCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hP, hQ⟩, hr, hinc⟩ := h
  obtain ⟨⟨hp2, hdp, hlcp, ⟨xp, yp, hyup, hyfp, hxp, hΓEp⟩, honp, hΓxp, hΓZ, hΓne, -, -, -, -,
    -, -⟩, hmp1, hmp, hmpmin⟩ := localCheck_spec hP
  obtain ⟨⟨hq2, hdq, hlcq, ⟨xq, yq, hyuq, hyfq, hxq, hΓEq⟩, honq, hΓxq, -, -, -, -, -, -, -,
    -⟩, hmq1, hmq, hmqmin⟩ := localCheck_spec hQ
  have hfK : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1 := by
    rw [natDegree_map_eq_of_injective (RingHom.injective_int _), ← hdp,
      natDegree_map_eq_of_injective (RingHom.injective_int _)]
  have hmapf : ∀ (s : ℕ) [Fact s.Prime],
      ((toPoly f).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[s]) =
        ((toPoly f).map (Int.castRingHom ℤ_[s])).map (algebraMap ℤ_[s] ℚ_[s]) := by
    intro s _
    rw [Polynomial.map_map, Polynomial.map_map]; congr 1
  have hmapΓ : ∀ (s : ℕ) [Fact s.Prime],
      emap (algebraMap ℚ ℚ_[s]) (emap (Int.castRingHom ℚ) Γ) =
        emap (algebraMap ℤ_[s] ℚ_[s]) (emap (Int.castRingHom ℤ_[s]) Γ) := by
    intro s _
    rw [emap_emap, emap_emap]; congr 1
  have hΓK : ∀ t ∈ emap (Int.castRingHom ℚ) Γ, 2 * t.2.1 ≠ 0 ∧
      t.2.1 ^ 2 = ((toPoly f).map (Int.castRingHom ℚ)).eval t.1 := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    obtain ⟨h1, h2⟩ := hΓZ t' ht'
    refine ⟨?_, ?_⟩
    · show (2 : ℚ) * ((t'.2.1 : ℤ) : ℚ) ≠ 0
      exact_mod_cast h1
    · show ((t'.2.1 : ℤ) : ℚ) ^ 2 = ((toPoly f).map (Int.castRingHom ℚ)).eval
        (Int.castRingHom ℚ t'.1)
      rw [eval_map, eval₂_at_apply, ← h2]; simp
  have hΓnd : ((emap (Int.castRingHom ℚ) Γ).map Prod.fst).Nodup := by
    simp only [emap, List.map_map, List.Nodup]
    rw [List.pairwise_map]
    exact hΓne.imp fun h he ↦ h (by simpa using he)
  have hinc' : ∀ c d, cp.m * p ^ c ≠ cq.m * q ^ d := by
    rcases hinc with ⟨hrq, h1, h2⟩ | ⟨hrp, h1, h2⟩
    · exact ne_of_prime_pow_left hq.out hr hrq h1 h2
    · exact ne_of_prime_pow_right hp.out hr hrp h1 h2
  exact not_torsion_of_orders hp2 hq2 (algebraMap ℚ ℚ_[p]) (algebraMap ℚ ℚ_[q]) _ hfK _ hΓK
    hΓnd _ hdp hlcp (hmapf p) xp yp hyup hyfp hxp _ (hmapΓ p) honp hΓxp hΓEp cp.m hmp1 hmp
    hmpmin _ hdq hlcq (hmapf q) xq yq hyuq hyfq hxq _ (hmapΓ q) honq hΓxq hΓEq cq.m hmq1 hmq
    hmqmin hinc'

end Jac
