import RischTragerBronstein.Computable.CAlgVia

/-!
# Invariants of the computable operations

A predicate `W` on codes is *preserved* by `O : COps α` when `0`, `1`, the casts and `+, −, ·, ′`
keep it and `⁻¹` keeps it on codes not testing as zero (`COps.Pres`). Then every polynomial
operation over `O` keeps "all coefficients satisfy `W`" (`AllW`), the division and extended gcd
included (they only invert leading coefficients of trimmed, non-zero lists), and so do the
operations of an algebraic extension (`pres_algExt`).
-/

namespace COps

variable {α : Type*}

/-- `W` is preserved by the operations (inversion on non-zero codes). -/
structure Pres (O : COps α) (W : α → Prop) : Prop where
  zero : W O.zero
  one : W O.one
  add : ∀ a b, W a → W b → W (O.add a b)
  neg : ∀ a, W a → W (O.neg a)
  mul : ∀ a b, W a → W b → W (O.mul a b)
  inv : ∀ a, W a → O.isZero a = false → W (O.inv a)
  deriv : ∀ a, W a → W (O.deriv a)
  natCast : ∀ n, W (O.natCast n)

end COps

namespace GPoly

variable {α : Type*} (O : COps α) (W : α → Prop)

/-- All coefficients satisfy `W`. -/
def AllW (p : GPoly α) : Prop := ∀ a ∈ p, W a

variable {O W}

lemma allW_nil : AllW W ([] : GPoly α) := fun _ ha ↦ absurd ha (List.not_mem_nil)

lemma allW_trim (p : GPoly α) (hp : AllW W p) : AllW W (trim O p) := by
  intro x hx
  simp only [trim, List.mem_reverse] at hx
  exact hp x (List.mem_reverse.mp ((List.dropWhile_sublist _).subset hx))

/-- The leading coefficient of a non-empty trimmed list does not test as zero. -/
lemma lead_trim_ne (p : GPoly α) (hne : trim O p ≠ []) : O.isZero (lead O (trim O p)) = false := by
  unfold lead trim at *
  have hl : p.reverse.dropWhile O.isZero ≠ [] := by
    intro h0; apply hne; rw [h0]; rfl
  have hx := List.head_dropWhile_not (fun a ↦ O.isZero a) hl
  obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil hl
  have hb : O.isZero b = false := by
    have e : (p.reverse.dropWhile O.isZero).head hl = b := by simp [hbt]
    rw [e] at hx; simpa using hx
  rw [hbt, List.reverse_cons, List.getLastD_concat]
  exact hb

variable (h : O.Pres W)
include h

lemma allW_add : ∀ p q : GPoly α, AllW W p → AllW W q → AllW W (add O p q)
  | [], q, _, hq => hq
  | a :: p, [], hp, _ => hp
  | a :: p, b :: q, hp, hq => by
    intro x hx
    simp only [add, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h.add _ _ (hp _ List.mem_cons_self) (hq _ List.mem_cons_self)
    · exact allW_add p q (fun y hy ↦ hp y (List.mem_cons_of_mem _ hy))
        (fun y hy ↦ hq y (List.mem_cons_of_mem _ hy)) x hx

lemma allW_neg (p : GPoly α) (hp : AllW W p) : AllW W (neg O p) := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact h.neg _ (hp a ha)

lemma allW_smul (c : α) (hc : W c) (p : GPoly α) (hp : AllW W p) : AllW W (smul O c p) := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact h.mul _ _ hc (hp a ha)

lemma allW_sub (p q : GPoly α) (hp : AllW W p) (hq : AllW W q) : AllW W (sub O p q) :=
  allW_add h _ _ hp (allW_neg h q hq)

lemma allW_mul : ∀ p q : GPoly α, AllW W p → AllW W q → AllW W (mul O p q)
  | [], _, _, _ => allW_nil
  | a :: p, q, hp, hq => by
    refine allW_add h _ _ (allW_smul h a (hp _ List.mem_cons_self) q hq) ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.zero
    · exact allW_mul p q (fun y hy ↦ hp y (List.mem_cons_of_mem _ hy)) hq x hx

lemma allW_mapD (p : GPoly α) (hp : AllW W p) : AllW W (mapD O p) := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact h.deriv _ (hp a ha)

lemma allW_derivXAux : ∀ (n : ℕ) (p : GPoly α), AllW W p → AllW W (derivXAux O n p)
  | _, [], _ => allW_nil
  | n, a :: p, hp => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.mul _ _ (h.natCast n) (hp _ List.mem_cons_self)
    · exact allW_derivXAux (n + 1) p (fun y hy ↦ hp y (List.mem_cons_of_mem _ hy)) x hx

lemma allW_derivX (p : GPoly α) (hp : AllW W p) : AllW W (derivX O p) := by
  rcases p with _ | ⟨a, p⟩
  · exact allW_nil
  · exact allW_derivXAux h 1 p (fun y hy ↦ hp y (List.mem_cons_of_mem _ hy))

lemma allW_derivT (w p : GPoly α) (hw : AllW W w) (hp : AllW W p) : AllW W (derivT O w p) :=
  allW_add h _ _ (allW_mapD h p hp) (allW_mul h _ _ hw (allW_derivX h p hp))

lemma allW_monomial (k : ℕ) (c : α) (hc : W c) : AllW W (monomial O k c) := by
  intro x hx
  simp only [monomial, List.mem_append, List.mem_replicate, List.mem_singleton] at hx
  rcases hx with ⟨-, rfl⟩ | rfl
  · exact h.zero
  · exact hc

lemma W_lead (p : GPoly α) (hp : AllW W p) : W (lead O p) := by
  unfold lead
  rcases List.eq_nil_or_concat p with rfl | ⟨l, b, rfl⟩
  · exact h.zero
  · rw [List.concat_eq_append]
    simpa using hp b (by simp)

omit h in
lemma all_of_dropWhile_nil (f : α → Bool) : ∀ l : List α, l.dropWhile f = [] → ∀ a ∈ l, f a = true
  | [], _, a, ha => absurd ha (List.not_mem_nil)
  | b :: l, hl, a, ha => by
    rw [List.dropWhile_cons] at hl
    split_ifs at hl with hb
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hb
    · exact all_of_dropWhile_nil f l hl a ha

omit h in
lemma trim_ne_nil_of_isZero (p : GPoly α) (hp : isZero O p = false) : trim O p ≠ [] := by
  intro h0
  have : ∀ a ∈ p, O.isZero a = true := by
    intro a ha
    unfold trim at h0
    have h1 : p.reverse.dropWhile O.isZero = [] := List.reverse_eq_nil_iff.mp h0
    exact all_of_dropWhile_nil _ _ h1 a (List.mem_reverse.mpr ha)
  have : isZero O p = true := List.all_eq_true.mpr this
  rw [this] at hp; exact absurd hp (by decide)

lemma allW_divModAux (d : GPoly α) (hd : AllW W d) (hinv : W (O.inv (lead O d))) :
    ∀ (fuel : ℕ) (acc p : GPoly α), AllW W acc → AllW W p →
      AllW W (divModAux O d fuel acc p).1 ∧ AllW W (divModAux O d fuel acc p).2
  | 0, acc, p, ha, hp => ⟨ha, hp⟩
  | fuel + 1, acc, p, ha, hp => by
    simp only [divModAux]
    have hpt := allW_trim (O := O) p hp
    split_ifs
    · exact ⟨ha, hpt⟩
    · have hm := allW_monomial h ((trim O p).length - d.length) _
        (h.mul _ _ (W_lead h _ hpt) hinv)
      exact allW_divModAux d hd hinv fuel _ _ (allW_add h _ _ ha hm)
        (allW_sub h _ _ hpt (allW_mul h _ _ hm hd))

lemma allW_divMod (p d : GPoly α) (hp : AllW W p) (hd : AllW W d)
    (hinv : W (O.inv (lead O (trim O d)))) :
    AllW W (divMod O p d).1 ∧ AllW W (divMod O p d).2 :=
  allW_divModAux h _ (allW_trim d hd) hinv _ _ _ allW_nil hp

lemma allW_egcdAux : ∀ (fuel : ℕ) (x y : GPoly α × GPoly α × GPoly α),
    AllW W x.1 → AllW W x.2.1 → AllW W x.2.2 → AllW W y.1 → AllW W y.2.1 → AllW W y.2.2 →
      AllW W (egcdAux O fuel x y).1 ∧ AllW W (egcdAux O fuel x y).2.1 ∧
        AllW W (egcdAux O fuel x y).2.2
  | 0, x, _, h1, h2, h3, _, _, _ => ⟨h1, h2, h3⟩
  | fuel + 1, (r₀, s₀, t₀), (r₁, s₁, t₁), h1, h2, h3, h4, h5, h6 => by
    simp only [egcdAux]
    split_ifs with hz
    · exact ⟨h1, h2, h3⟩
    · have hz' : isZero O r₁ = false := by simpa using hz
      have hinv : W (O.inv (lead O (trim O r₁))) :=
        h.inv _ (W_lead h _ (allW_trim r₁ h4)) (lead_trim_ne r₁ (trim_ne_nil_of_isZero r₁ hz'))
      obtain ⟨q1, q2⟩ := allW_divMod h r₀ r₁ h1 h4 hinv
      exact allW_egcdAux fuel _ _ h4 h5 h6 q2 (allW_sub h _ _ h2 (allW_mul h _ _ q1 h5))
        (allW_sub h _ _ h3 (allW_mul h _ _ q1 h6))

lemma allW_egcd (p q : GPoly α) (hp : AllW W p) (hq : AllW W q) :
    AllW W (egcd O p q).1 ∧ AllW W (egcd O p q).2.1 ∧ AllW W (egcd O p q).2.2 := by
  have h1 : AllW W [O.one] := fun x hx ↦ by
    rw [List.mem_singleton] at hx; rw [hx]; exact h.one
  exact allW_egcdAux h _ _ _ hp h1 allW_nil hq allW_nil h1

omit h in
/-- The first component of the extended gcd of a non-zero list is not zero. -/
lemma egcdAux_ne : ∀ (fuel : ℕ) (x y : GPoly α × GPoly α × GPoly α), isZero O x.1 = false →
    isZero O (egcdAux O fuel x y).1 = false
  | 0, _, _, hx => hx
  | fuel + 1, (r₀, s₀, t₀), (r₁, s₁, t₁), hx => by
    simp only [egcdAux]
    split_ifs with hz
    · exact hx
    · exact egcdAux_ne fuel _ _ (by simpa using hz)

variable (P : GPoly α) (hP : AllW W P) (hPinv : W (O.inv (lead O (trim O P))))
include hP hPinv

lemma allW_algRed (a : GPoly α) (ha : AllW W a) : AllW W (algRed O P a) :=
  (allW_divMod h a P ha hP hPinv).2

lemma allW_algInv (a : GPoly α) (ha : AllW W a) : AllW W (algInv O P a) := by
  unfold algInv
  split_ifs with hz
  · exact allW_nil
  · have hr := allW_algRed h P hP hPinv a ha
    have hz' : isZero O (algRed O P a) = false := by simpa using hz
    obtain ⟨g1, g2, -⟩ := allW_egcd h _ _ hr hP
    have hne := egcdAux_ne (O := O) ((algRed O P a).length + P.length + 2) (algRed O P a, [O.one], [])
      (P, [], [O.one]) hz'
    have hinv : W (O.inv (lead O (trim O (egcd O (algRed O P a) P).1))) :=
      h.inv _ (W_lead h _ (allW_trim _ g1)) (lead_trim_ne _ (trim_ne_nil_of_isZero _ hne))
    exact allW_algRed h P hP hPinv _ (allW_smul h _ hinv _ g2)

lemma allW_algYd : AllW W (algYd O P) :=
  allW_algRed h P hP hPinv _ (allW_mul h _ _ (allW_neg h _ (allW_mapD h P hP))
    (allW_algInv h P hP hPinv _ (allW_derivX h P hP)))

omit h in
include h in
/-- **The algebraic extension preserves `AllW W`.** -/
theorem pres_algExt : (O.algExt P).Pres (AllW W) where
  zero := allW_nil
  one := fun x hx ↦ by rw [List.mem_singleton.mp hx]; exact h.one
  add := fun a b ha hb ↦ allW_add h a b ha hb
  neg := fun a ha ↦ allW_neg h a ha
  mul := fun a b ha hb ↦ allW_algRed h P hP hPinv _ (allW_mul h a b ha hb)
  inv := fun a ha _ ↦ allW_algInv h P hP hPinv a ha
  deriv := fun a ha ↦ allW_algRed h P hP hPinv _ (allW_derivT h _ a (allW_algYd h P hP hPinv) ha)
  natCast := fun n x hx ↦ by rw [List.mem_singleton.mp hx]; exact h.natCast n

end GPoly
