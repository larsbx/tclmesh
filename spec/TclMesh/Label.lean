/-!
# Security labels

A join-semilattice with a bottom element. `le a b` means information labelled
`a` may flow to `b`. The order is `Bool`-valued so that checkers can decide it.
-/

namespace TclMesh

class SecLattice (L : Type) where
  le : L → L → Bool
  join : L → L → L
  bot : L
  le_refl : ∀ a, le a a = true
  le_trans : ∀ a b c, le a b = true → le b c = true → le a c = true
  le_join_left : ∀ a b, le a (join a b) = true
  le_join_right : ∀ a b, le b (join a b) = true
  join_le : ∀ a b c, le a c = true → le b c = true → le (join a b) c = true
  bot_le : ∀ a, le bot a = true

namespace SecLattice

variable {L : Type} [SecLattice L]

theorem join_le_iff {a b c : L} : le (join a b) c = true ↔ le a c = true ∧ le b c = true :=
  ⟨fun h => ⟨le_trans _ _ _ (le_join_left a b) h, le_trans _ _ _ (le_join_right a b) h⟩,
   fun ⟨ha, hb⟩ => join_le _ _ _ ha hb⟩

end SecLattice

/-- The two-point lattice: public data may flow to secret, not back. -/
inductive Two where
  | low
  | high
  deriving DecidableEq, Repr

instance : SecLattice Two where
  le
    | .high, .low => false
    | _, _ => true
  join
    | .low, .low => .low
    | _, _ => .high
  bot := .low
  le_refl a := by cases a <;> rfl
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp
  le_join_left a b := by cases a <;> cases b <;> rfl
  le_join_right a b := by cases a <;> cases b <;> rfl
  join_le a b c := by cases a <;> cases b <;> cases c <;> simp
  bot_le a := by cases a <;> rfl

end TclMesh
