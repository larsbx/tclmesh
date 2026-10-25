import TclMesh.Flow

/-!
# Obliviousness and mechanism selection

A source language with an ordinary `if` evaluates only the taken branch, so
its operation trace reveals the condition. Compiling `if` to `select`, which
evaluates both branches, yields programs that:

* compute the same value (`compile_correct`);
* are well-typed, with the label of everything they read (`compile_typed`);
* have an operation trace fixed by their syntax, so an observer of execution
  learns nothing about any input from it (`compile_oblivious`).

This is the smallest instance of the meta-language choosing a mechanism: a
decision on secret data becomes an oblivious decision.
-/

namespace TclMesh

open SecLattice

variable {L : Type} [SecLattice L]

/-- Operations an executor performs, as visible to someone watching it run. -/
inductive Tag where
  | lit | var | op (o : Op) | select | release | verify
  | branch (taken : Bool)
  deriving DecidableEq, Repr

/-! ## Target: the trace is syntactic -/

/-- Instrumented evaluation: value and operation trace. -/
def exec (ρ : String → Int) : Expr L → Int × List Tag
  | .lit n => (n, [.lit])
  | .var x => (ρ x, [.var])
  | .bin op a b =>
      let (va, ta) := exec ρ a
      let (vb, tb) := exec ρ b
      (op.apply va vb, ta ++ tb ++ [.op op])
  | .select c a b =>
      let (vc, tc) := exec ρ c
      let (va, ta) := exec ρ a
      let (vb, tb) := exec ρ b
      (if vc ≠ 0 then va else vb, tc ++ ta ++ tb ++ [.select])
  | .release _ w e =>
      let (v, t) := exec ρ e
      (v % (2 ^ w : Int), t ++ [.release])
  | .verify _ e =>
      let (v, t) := exec ρ e
      (if v ≠ 0 then 1 else 0, t ++ [.verify])

/-- The trace as a function of syntax alone. -/
def trace : Expr L → List Tag
  | .lit _ => [.lit]
  | .var _ => [.var]
  | .bin op a b => trace a ++ trace b ++ [.op op]
  | .select c a b => trace c ++ trace a ++ trace b ++ [.select]
  | .release _ _ e => trace e ++ [.release]
  | .verify _ e => trace e ++ [.verify]

omit [SecLattice L] in
theorem exec_eq (ρ : String → Int) (e : Expr L) : exec ρ e = (eval ρ e, trace e) := by
  induction e with
  | lit | var => rfl
  | bin op a b iha ihb => simp [exec, eval, trace, iha, ihb]
  | select c a b ihc iha ihb => simp [exec, eval, trace, ihc, iha, ihb]
  | release to w e ih => simp [exec, eval, trace, ih]
  | verify to e ih => simp [exec, eval, trace, ih]

omit [SecLattice L] in
/-- **Obliviousness.** Executing any target expression yields the same trace
under every environment. -/
theorem exec_oblivious (ρ₁ ρ₂ : String → Int) (e : Expr L) :
    (exec ρ₁ e).2 = (exec ρ₂ e).2 := by
  rw [exec_eq, exec_eq]

/-! ## Source: `if` evaluates one branch -/

inductive SExpr where
  | lit : Int → SExpr
  | var : String → SExpr
  | bin : Op → SExpr → SExpr → SExpr
  | ite : SExpr → SExpr → SExpr → SExpr
  deriving Repr

def SExpr.eval (ρ : String → Int) : SExpr → Int
  | .lit n => n
  | .var x => ρ x
  | .bin op a b => op.apply (eval ρ a) (eval ρ b)
  | .ite c a b => if eval ρ c ≠ 0 then eval ρ a else eval ρ b

/-- Lazy execution trace: only the taken branch runs. -/
def SExpr.exec (ρ : String → Int) : SExpr → List Tag
  | .lit _ => [.lit]
  | .var _ => [.var]
  | .bin op a b => exec ρ a ++ exec ρ b ++ [.op op]
  | .ite c a b =>
      exec ρ c ++ (if c.eval ρ ≠ 0 then .branch true :: exec ρ a else .branch false :: exec ρ b)

/-- The source executor leaks a secret condition through its trace. -/
theorem source_leaks :
    ∃ (s : SExpr) (ρ₁ ρ₂ : String → Int), s.exec ρ₁ ≠ s.exec ρ₂ :=
  ⟨.ite (.var "secret") (.lit 1) (.lit 0), fun _ => 1, fun _ => 0, by decide⟩

/-! ## Compilation -/

def compile : SExpr → Expr L
  | .lit n => .lit n
  | .var x => .var x
  | .bin op a b => .bin op (compile a) (compile b)
  | .ite c a b => .select (compile c) (compile a) (compile b)

/-- The label of a source expression: everything it reads. -/
def SExpr.label (Γ : String → L) : SExpr → L
  | .lit _ => bot
  | .var x => Γ x
  | .bin _ a b => join (label Γ a) (label Γ b)
  | .ite c a b => join (label Γ c) (join (label Γ a) (label Γ b))

omit [SecLattice L] in
theorem compile_correct (ρ : String → Int) (s : SExpr) :
    eval ρ (compile s : Expr L) = s.eval ρ := by
  induction s with
  | lit | var => rfl
  | bin op a b iha ihb => simp [compile, eval, SExpr.eval, iha, ihb]
  | ite c a b ihc iha ihb => simp [compile, eval, SExpr.eval, ihc, iha, ihb]

theorem compile_typed (P : Policy L) (Γ : String → L) (s : SExpr) :
    HasType P Γ (compile s) (s.label Γ) := by
  induction s with
  | lit n => exact .lit n
  | var x => exact .var x
  | bin _ _ _ iha ihb => exact .bin iha ihb
  | ite _ _ _ ihc iha ihb => exact .select ihc iha ihb

omit [SecLattice L] in
/-- **Compiled programs are oblivious.** -/
theorem compile_oblivious (ρ₁ ρ₂ : String → Int) (s : SExpr) :
    (exec ρ₁ (compile s : Expr L)).2 = (exec ρ₂ (compile s : Expr L)).2 :=
  exec_oblivious ρ₁ ρ₂ _

theorem obsCount_compile (obs : L) (s : SExpr) : obsCount obs (compile s : Expr L) = 0 := by
  induction s with
  | lit | var => rfl
  | bin _ _ _ iha ihb => simp [compile, obsCount, iha, ihb]
  | ite _ _ _ ihc iha ihb => simp [compile, obsCount, ihc, iha, ihb]

/-- Compiled programs contain no declassification, so their value is secret to
exactly the label of what they read. -/
theorem compile_strict {P : Policy L} {Γ} {obs : L} {ρ₁ ρ₂ : String → Int} (s : SExpr)
    (hl : le (s.label Γ) obs = true) (hlow : LowEq Γ obs ρ₁ ρ₂) :
    s.eval ρ₁ = s.eval ρ₂ := by
  rw [← compile_correct (L := L), ← compile_correct (L := L)]
  exact noninterference_strict (compile_typed P Γ s) hl hlow (obsCount_compile obs s)

end TclMesh
