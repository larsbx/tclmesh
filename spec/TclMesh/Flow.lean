import TclMesh.Label

/-!
# Information flow with designed declassification

Expressions over integer data whose inputs carry security labels. Ciphertext
is modelled by its plaintext (the ideal functionality): what matters is which
observers may learn what.

Secret data may drive decisions in three ways, each a construct:

* `select c a b` is an **oblivious** choice: both branches are evaluated and the
  result is labelled with the condition, so the decision stays secret;
* `release to w e` is a **released** decision: the policy authorizes revealing
  `e` (reduced to `w` bits) at label `to`;
* `verify to e` is a **proved** decision: a key holder attests that `e ≠ 0`,
  revealing one bit at label `to`.

The main theorem, `noninterference`, says that what an observer sees of a
well-typed expression is determined by the inputs it may read and the
releases and proofs it was shown. Nothing else about secret inputs flows.
-/

namespace TclMesh

open SecLattice

inductive Op where
  | add | sub | mul | lt | eq
  deriving DecidableEq, Repr

def Op.apply : Op → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .lt, a, b => if a < b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0

inductive Expr (L : Type) where
  | lit : Int → Expr L
  | var : String → Expr L
  | bin : Op → Expr L → Expr L → Expr L
  | select : Expr L → Expr L → Expr L → Expr L
  | release : L → Nat → Expr L → Expr L
  | verify : L → Expr L → Expr L
  deriving Repr

/-- Which declassifications the manifest authorizes, from a source label to a target. -/
structure Policy (L : Type) where
  release : L → L → Bool
  verify : L → L → Bool

variable {L : Type} [SecLattice L]

/-! ## Typing -/

/-- Syntax-directed labelling; `Γ` gives each input's label. -/
inductive HasType (P : Policy L) (Γ : String → L) : Expr L → L → Prop where
  | lit (n) : HasType P Γ (.lit n) bot
  | var (x) : HasType P Γ (.var x) (Γ x)
  | bin {op a b la lb} : HasType P Γ a la → HasType P Γ b lb →
      HasType P Γ (.bin op a b) (join la lb)
  | select {c a b lc la lb} : HasType P Γ c lc → HasType P Γ a la → HasType P Γ b lb →
      HasType P Γ (.select c a b) (join lc (join la lb))
  | release {e le to w} : HasType P Γ e le → P.release le to = true →
      HasType P Γ (.release to w e) to
  | verify {e le to} : HasType P Γ e le → P.verify le to = true →
      HasType P Γ (.verify to e) to

/-- The label checker. -/
def infer (P : Policy L) (Γ : String → L) : Expr L → Option L
  | .lit _ => some bot
  | .var x => some (Γ x)
  | .bin _ a b => do pure (join (← infer P Γ a) (← infer P Γ b))
  | .select c a b => do pure (join (← infer P Γ c) (join (← infer P Γ a) (← infer P Γ b)))
  | .release to _ e => do
      let le ← infer P Γ e
      if P.release le to then pure to else none
  | .verify to e => do
      let le ← infer P Γ e
      if P.verify le to then pure to else none

theorem infer_sound {P : Policy L} {Γ} {e : Expr L} {l : L} :
    infer P Γ e = some l → HasType P Γ e l := by
  induction e generalizing l with
  | lit n => intro h; cases h; exact .lit n
  | var x => intro h; cases h; exact .var x
  | bin op a b iha ihb =>
    intro h
    simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨la, ha, lb, hb, rfl⟩ := h
    exact .bin (iha ha) (ihb hb)
  | select c a b ihc iha ihb =>
    intro h
    simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨lc, hc, la, ha, lb, hb, rfl⟩ := h
    exact .select (ihc hc) (iha ha) (ihb hb)
  | release to w e ih =>
    intro h
    simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨le, he, h⟩ := h
    split at h
    · cases h; exact .release (ih he) (by assumption)
    · cases h
  | verify to e ih =>
    intro h
    simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨le, he, h⟩ := h
    split at h
    · cases h; exact .verify (ih he) (by assumption)
    · cases h

theorem infer_complete {P : Policy L} {Γ} {e : Expr L} {l : L} :
    HasType P Γ e l → infer P Γ e = some l := by
  intro h
  induction h with
  | lit => rfl
  | var => rfl
  | bin _ _ iha ihb => simp [infer, iha, ihb]
  | select _ _ _ ihc iha ihb => simp [infer, ihc, iha, ihb]
  | release _ hp ih => simp [infer, ih, hp]
  | verify _ hp ih => simp [infer, ih, hp]

/-- The checker decides the typing relation exactly. -/
theorem infer_iff {P : Policy L} {Γ} {e : Expr L} {l : L} :
    infer P Γ e = some l ↔ HasType P Γ e l :=
  ⟨infer_sound, infer_complete⟩

/-- Labels are unique. -/
theorem HasType.unique {P : Policy L} {Γ} {e : Expr L} {l₁ l₂ : L}
    (h₁ : HasType P Γ e l₁) (h₂ : HasType P Γ e l₂) : l₁ = l₂ := by
  have := (infer_complete h₁).symm.trans (infer_complete h₂)
  exact Option.some.inj this

/-! ## Semantics -/

def eval (ρ : String → Int) : Expr L → Int
  | .lit n => n
  | .var x => ρ x
  | .bin op a b => op.apply (eval ρ a) (eval ρ b)
  | .select c a b => if eval ρ c ≠ 0 then eval ρ a else eval ρ b
  | .release _ w e => eval ρ e % (2 ^ w : Int)
  | .verify _ e => if eval ρ e ≠ 0 then 1 else 0

/-- What an observer at label `obs` is shown while `e` evaluates: each release
or proof it may see, as (value, width in bits), in evaluation order. -/
def observe (obs : L) (ρ : String → Int) : Expr L → List (Int × Nat)
  | .lit _ | .var _ => []
  | .bin _ a b => observe obs ρ a ++ observe obs ρ b
  | .select c a b => observe obs ρ c ++ observe obs ρ a ++ observe obs ρ b
  | e@(.release to w inner) =>
      (if le to obs then [(eval ρ e, w)] else []) ++ observe obs ρ inner
  | e@(.verify to inner) =>
      (if le to obs then [(eval ρ e, 1)] else []) ++ observe obs ρ inner

/-- The number of observations is fixed by the syntax, not the data. -/
def obsCount (obs : L) : Expr L → Nat
  | .lit _ | .var _ => 0
  | .bin _ a b => obsCount obs a + obsCount obs b
  | .select c a b => obsCount obs c + obsCount obs a + obsCount obs b
  | .release to _ inner => (if le to obs then 1 else 0) + obsCount obs inner
  | .verify to inner => (if le to obs then 1 else 0) + obsCount obs inner

theorem length_observe (obs : L) (ρ : String → Int) (e : Expr L) :
    (observe obs ρ e).length = obsCount obs e := by
  induction e with
  | lit | var => rfl
  | bin _ a b iha ihb => simp [observe, obsCount, iha, ihb]
  | select c a b ihc iha ihb => simp [observe, obsCount, ihc, iha, ihb]; omega
  | release to w inner ih =>
    simp only [observe, obsCount, List.length_append, ih]; split <;> rfl
  | verify to inner ih =>
    simp only [observe, obsCount, List.length_append, ih]; split <;> rfl

/-- Agreement on concatenated observations splits, since lengths are syntactic. -/
theorem observe_split {obs : L} {ρ₁ ρ₂ : String → Int} {a : Expr L} {r₁ r₂ : List (Int × Nat)}
    (h : observe obs ρ₁ a ++ r₁ = observe obs ρ₂ a ++ r₂) :
    observe obs ρ₁ a = observe obs ρ₂ a ∧ r₁ = r₂ :=
  List.append_inj h (by simp [length_observe])

/-- Two environments agree on every input an observer at `obs` may read. -/
def LowEq (Γ : String → L) (obs : L) (ρ₁ ρ₂ : String → Int) : Prop :=
  ∀ x, le (Γ x) obs = true → ρ₁ x = ρ₂ x

/-- **Declassification-indexed non-interference.** If an expression's label may
flow to `obs`, its value is determined by the inputs `obs` may read together
with the releases and proofs `obs` was shown. -/
theorem noninterference {P : Policy L} {Γ} {e : Expr L} {l obs : L} {ρ₁ ρ₂ : String → Int}
    (ht : HasType P Γ e l) (hl : le l obs = true) (hlow : LowEq Γ obs ρ₁ ρ₂)
    (hobs : observe obs ρ₁ e = observe obs ρ₂ e) :
    eval ρ₁ e = eval ρ₂ e := by
  induction ht with
  | lit => rfl
  | var x => exact hlow x hl
  | bin _ _ iha ihb =>
    obtain ⟨hla, hlb⟩ := join_le_iff.mp hl
    obtain ⟨ha, hb⟩ := observe_split hobs
    simp only [eval, iha hla ha, ihb hlb hb]
  | select _ _ _ ihc iha ihb =>
    obtain ⟨hlc, hlab⟩ := join_le_iff.mp hl
    obtain ⟨hla, hlb⟩ := join_le_iff.mp hlab
    simp only [observe, List.append_assoc] at hobs
    obtain ⟨hc, hab⟩ := observe_split hobs
    obtain ⟨ha, hb⟩ := observe_split hab
    simp only [eval, ihc hlc hc, iha hla ha, ihb hlb hb]
  | release _ _ =>
    simp only [observe, hl, ↓reduceIte, List.singleton_append, List.cons.injEq,
      Prod.mk.injEq] at hobs
    exact hobs.1.1
  | verify _ _ =>
    simp only [observe, hl, ↓reduceIte, List.singleton_append, List.cons.injEq,
      Prod.mk.injEq] at hobs
    exact hobs.1.1

/-- Without any visible release or proof, this is classical non-interference. -/
theorem noninterference_strict {P : Policy L} {Γ} {e : Expr L} {l obs : L}
    {ρ₁ ρ₂ : String → Int} (ht : HasType P Γ e l) (hl : le l obs = true)
    (hlow : LowEq Γ obs ρ₁ ρ₂) (hnone : obsCount obs e = 0) :
    eval ρ₁ e = eval ρ₂ e := by
  apply noninterference ht hl hlow
  rw [List.length_eq_zero_iff.mp ((length_observe obs ρ₁ e).trans hnone),
    List.length_eq_zero_iff.mp ((length_observe obs ρ₂ e).trans hnone)]

/-! ## Leakage accounting -/

/-- Static leakage of an expression in bits: the widths of all its releases and proofs. -/
def bits : Expr L → Nat
  | .lit _ | .var _ => 0
  | .bin _ a b => bits a + bits b
  | .select c a b => bits c + bits a + bits b
  | .release _ w e => w + bits e
  | .verify _ e => 1 + bits e

/-- Every observed value fits in its declared width. -/
theorem observe_bounded (obs : L) (ρ : String → Int) (e : Expr L) :
    ∀ p ∈ observe obs ρ e, 0 ≤ p.1 ∧ p.1 < 2 ^ p.2 := by
  have pow_pos : ∀ w : Nat, (0 : Int) < 2 ^ w := fun w => Int.pow_pos (by decide)
  induction e with
  | lit | var => simp [observe]
  | bin _ a b iha ihb =>
    intro p hp; simp only [observe, List.mem_append] at hp
    exact hp.elim (iha p) (ihb p)
  | select c a b ihc iha ihb =>
    intro p hp; simp only [observe, List.mem_append] at hp
    exact hp.elim (fun h => h.elim (ihc p) (iha p)) (ihb p)
  | release to w inner ih =>
    intro p hp; simp only [observe, List.mem_append] at hp
    rcases hp with hp | hp
    · split at hp
      · simp only [List.mem_singleton] at hp; subst hp
        exact ⟨Int.emod_nonneg _ (Int.ne_of_gt (pow_pos w)), Int.emod_lt_of_pos _ (pow_pos w)⟩
      · cases hp
    · exact ih p hp
  | verify to inner ih =>
    intro p hp; simp only [observe, List.mem_append] at hp
    rcases hp with hp | hp
    · split at hp
      · simp only [List.mem_singleton] at hp; subst hp
        simp only [eval]; split <;> decide
      · cases hp
    · exact ih p hp

/-- What any observer is shown totals at most the static leakage. -/
theorem observed_bits_le (obs : L) (ρ : String → Int) (e : Expr L) :
    ((observe obs ρ e).map Prod.snd).sum ≤ bits e := by
  induction e with
  | lit | var => simp [observe, bits]
  | bin _ a b iha ihb => simp only [observe, bits, List.map_append, List.sum_append]; omega
  | select c a b ihc iha ihb =>
    simp only [observe, bits, List.map_append, List.sum_append]; omega
  | release to w inner ih =>
    simp only [observe, bits, List.map_append, List.sum_append]; split <;> simp <;> omega
  | verify to inner ih =>
    simp only [observe, bits, List.map_append, List.sum_append]; split <;> simp <;> omega

/-! ## Authorization -/

/-- `Sub e' e`: `e'` is a subexpression of `e`. -/
inductive Sub : Expr L → Expr L → Prop where
  | refl (e) : Sub e e
  | binL {op a b e} : Sub e a → Sub e (.bin op a b)
  | binR {op a b e} : Sub e b → Sub e (.bin op a b)
  | selC {c a b e} : Sub e c → Sub e (.select c a b)
  | selA {c a b e} : Sub e a → Sub e (.select c a b)
  | selB {c a b e} : Sub e b → Sub e (.select c a b)
  | rel {to w x e} : Sub e x → Sub e (.release to w x)
  | ver {to x e} : Sub e x → Sub e (.verify to x)

theorem HasType.sub {P : Policy L} {Γ} {e e' : Expr L} {l : L}
    (ht : HasType P Γ e l) (hs : Sub e' e) : ∃ l', HasType P Γ e' l' := by
  induction hs generalizing l with
  | refl => exact ⟨l, ht⟩
  | binL _ ih | binR _ ih => cases ht; first | exact ih (by assumption) | skip
  | selC _ ih | selA _ ih | selB _ ih => cases ht; first | exact ih (by assumption) | skip
  | rel _ ih | ver _ ih => cases ht; exact ih (by assumption)

/-- Every release in a well-typed expression is authorized by the policy for
its operand's label; likewise every proof. -/
theorem releases_authorized {P : Policy L} {Γ} {e : Expr L} {l : L} (ht : HasType P Γ e l) :
    (∀ to w x, Sub (.release to w x) e → ∃ lx, infer P Γ x = some lx ∧ P.release lx to = true) ∧
    (∀ to x, Sub (.verify to x) e → ∃ lx, infer P Γ x = some lx ∧ P.verify lx to = true) := by
  constructor
  · intro to w x hs
    obtain ⟨_, h⟩ := ht.sub hs
    cases h with
    | release hx hp => exact ⟨_, infer_complete hx, hp⟩
  · intro to x hs
    obtain ⟨_, h⟩ := ht.sub hs
    cases h with
    | verify hx hp => exact ⟨_, infer_complete hx, hp⟩

end TclMesh
