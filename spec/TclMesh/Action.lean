import TclMesh.Flow

/-!
# Actions over labelled state

An action has a guard, which the kernel branches on publicly; changes to
labelled fields; and effects whose fields carry declared labels. Secret data
reaches public observables only through the declassifications its
expressions contain.

`action_noninterference`: an observer's view of a well-typed action is
determined by the inputs it may read and the releases and proofs it was
shown. The view covers whether the guard admitted the action, the visible
changed fields, and the visible effect fields.
-/

namespace TclMesh

open SecLattice

variable {L : Type} [SecLattice L]

structure EffectField (L : Type) where
  name : String
  label : L
  value : Expr L

structure Effect (L : Type) where
  type : String
  fields : List (EffectField L)

structure Action (L : Type) where
  guard : Expr L
  changes : List (String × Expr L)
  effects : List (Effect L)

/-- Typing at kernel label `pub`: the guard is public, and no change or effect
field receives data above its label. -/
structure WellTyped (P : Policy L) (Γ : String → L) (pub : L) (a : Action L) : Prop where
  guard : ∃ l, HasType P Γ a.guard l ∧ le l pub = true
  changes : ∀ c ∈ a.changes, ∃ l, HasType P Γ c.2 l ∧ le l (Γ c.1) = true
  effects : ∀ ef ∈ a.effects, ∀ f ∈ ef.fields, ∃ l, HasType P Γ f.value l ∧ le l f.label = true

/-- `e` checks at a label that may flow to `bound`. -/
def checks (P : Policy L) (Γ : String → L) (e : Expr L) (bound : L) : Bool :=
  match infer P Γ e with
  | some l => le l bound
  | none => false

theorem checks_iff {P : Policy L} {Γ} {e : Expr L} {bound : L} :
    checks P Γ e bound = true ↔ ∃ l, HasType P Γ e l ∧ le l bound = true := by
  unfold checks
  constructor
  · intro h
    split at h
    · exact ⟨_, infer_sound (by assumption), h⟩
    · cases h
  · rintro ⟨l, ht, hl⟩
    rw [infer_complete ht]; exact hl

/-- The action checker. -/
def checkAction (P : Policy L) (Γ : String → L) (pub : L) (a : Action L) : Bool :=
  checks P Γ a.guard pub &&
  a.changes.all (fun c => checks P Γ c.2 (Γ c.1)) &&
  a.effects.all (fun ef => ef.fields.all (fun f => checks P Γ f.value f.label))

theorem checkAction_iff {P : Policy L} {Γ} {pub : L} {a : Action L} :
    checkAction P Γ pub a = true ↔ WellTyped P Γ pub a := by
  simp only [checkAction, Bool.and_eq_true, List.all_eq_true, checks_iff]
  exact ⟨fun ⟨⟨g, c⟩, e⟩ => ⟨g, c, e⟩, fun ⟨g, c, e⟩ => ⟨⟨g, c⟩, e⟩⟩

/-! ## Semantics and observation -/

/-- Value shown to an observer: `some v` when its label may flow to `obs`. -/
def shown (obs label : L) (v : Int) : Option Int :=
  if le label obs then some v else none

/-- The observer's view: `none` if the guard rejects; otherwise each changed
field and effect field with its value if visible. Names and shapes are public. -/
def view (Γ : String → L) (obs : L) (ρ : String → Int) (a : Action L) :
    Option (List (String × Option Int) × List (String × List (String × Option Int))) :=
  if eval ρ a.guard = 0 then none else
  some (a.changes.map (fun c => (c.1, shown obs (Γ c.1) (eval ρ c.2))),
        a.effects.map (fun ef => (ef.type,
          ef.fields.map (fun f => (f.name, shown obs f.label (eval ρ f.value))))))

def observeAll (obs : L) (ρ : String → Int) (es : List (Expr L)) : List (Int × Nat) :=
  es.flatMap (observe obs ρ)

/-- The expressions an admitted action evaluates, in order. -/
def Action.body (a : Action L) : List (Expr L) :=
  a.changes.map Prod.snd ++ a.effects.flatMap (fun ef => ef.fields.map EffectField.value)

/-- Releases and proofs shown while the action runs; the body only runs if the
guard admits it. -/
def observeAction (obs : L) (ρ : String → Int) (a : Action L) : List (Int × Nat) :=
  observe obs ρ a.guard ++ (if eval ρ a.guard = 0 then [] else observeAll obs ρ a.body)

theorem observeAll_split {obs : L} {ρ₁ ρ₂ : String → Int} :
    ∀ {es : List (Expr L)}, observeAll obs ρ₁ es = observeAll obs ρ₂ es →
      ∀ e ∈ es, observe obs ρ₁ e = observe obs ρ₂ e
  | [], _ => by simp
  | e :: es, h => by
    simp only [observeAll, List.flatMap_cons] at h
    obtain ⟨he, hes⟩ := observe_split h
    intro e' hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact he
    · exact observeAll_split hes e' hm

/-- **Non-interference for actions.** For an observer at least as privileged as
the kernel, the view of a well-typed action depends only on the inputs it may
read and the releases and proofs it was shown. -/
theorem action_noninterference {P : Policy L} {Γ} {pub obs : L} {a : Action L}
    {ρ₁ ρ₂ : String → Int} (hwt : WellTyped P Γ pub a) (hpub : le pub obs = true)
    (hlow : LowEq Γ obs ρ₁ ρ₂) (hobs : observeAction obs ρ₁ a = observeAction obs ρ₂ a) :
    view Γ obs ρ₁ a = view Γ obs ρ₂ a := by
  obtain ⟨lg, htg, hlg⟩ := hwt.guard
  obtain ⟨hog, hrest⟩ := observe_split hobs
  have hg : eval ρ₁ a.guard = eval ρ₂ a.guard :=
    noninterference htg (le_trans _ _ _ hlg hpub) hlow hog
  unfold view
  rw [hg]
  split
  · rfl
  · rename_i hne
    simp only [hg, hne, ↓reduceIte] at hrest
    have hbody := observeAll_split hrest
    have hval : ∀ e ∈ a.body, ∀ l, HasType P Γ e l → le l obs = true →
        eval ρ₁ e = eval ρ₂ e := fun e he l ht hl =>
      noninterference ht hl hlow (hbody e he)
    -- a visible value is produced at a label below its field label
    have hshown : ∀ e ∈ a.body, ∀ l bound, HasType P Γ e l → le l bound = true →
        shown obs bound (eval ρ₁ e) = shown obs bound (eval ρ₂ e) := by
      intro e he l bound ht hb
      unfold shown
      split
      · rename_i hbo; rw [hval e he l ht (le_trans _ _ _ hb hbo)]
      · rfl
    congr 2
    · apply List.map_congr_left
      intro c hc
      obtain ⟨l, ht, hb⟩ := hwt.changes c hc
      have hmem : c.2 ∈ a.body := List.mem_append_left _ (List.mem_map_of_mem hc)
      rw [hshown c.2 hmem l (Γ c.1) ht hb]
    · apply List.map_congr_left
      intro ef hef
      congr 1
      apply List.map_congr_left
      intro f hf
      obtain ⟨l, ht, hb⟩ := hwt.effects ef hef f hf
      have hmem : f.value ∈ a.body :=
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨ef, hef, List.mem_map_of_mem hf⟩)
      rw [hshown f.value hmem l f.label ht hb]

/-- Static leakage of an action: everything its guard and body could reveal. -/
def actionBits (a : Action L) : Nat :=
  bits a.guard + (a.body.map bits).sum

/-- The leakage budget check. -/
def withinBudget (a : Action L) (budget : Nat) : Bool :=
  actionBits a ≤ budget

theorem observeAll_bits_le (obs : L) (ρ : String → Int) :
    ∀ es : List (Expr L), ((observeAll obs ρ es).map Prod.snd).sum ≤ (es.map bits).sum
  | [] => by simp [observeAll]
  | e :: es => by
    have h1 := observed_bits_le obs ρ e
    have h2 := observeAll_bits_le obs ρ es
    simp only [observeAll, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons] at h2 ⊢
    omega

/-- **Budget soundness.** If the checker accepts the budget, no observer of any
run is shown more bits than the budget, and every shown value fits its width. -/
theorem budget_sound {a : Action L} {budget : Nat} (h : withinBudget a budget = true)
    (obs : L) (ρ : String → Int) :
    ((observeAction obs ρ a).map Prod.snd).sum ≤ budget ∧
    ∀ p ∈ observeAction obs ρ a, 0 ≤ p.1 ∧ p.1 < 2 ^ p.2 := by
  have hb : actionBits a ≤ budget := of_decide_eq_true h
  constructor
  · have hg := observed_bits_le obs ρ a.guard
    have hbody := observeAll_bits_le obs ρ a.body
    unfold observeAction actionBits at *
    split <;> simp only [List.map_append, List.sum_append, List.map_nil, List.sum_nil] <;> omega
  · intro p hp
    unfold observeAction at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact observe_bounded obs ρ a.guard p hp
    · split at hp
      · cases hp
      · obtain ⟨e, _, he⟩ := List.mem_flatMap.mp hp
        exact observe_bounded obs ρ e p he

end TclMesh
