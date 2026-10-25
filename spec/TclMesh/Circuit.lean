/-!
# Private circuits: what the evaluator may observe

A private circuit (`tclmesh private circuit`) is a named graph of operations
over ciphertext and public inputs. A homomorphic evaluator computes every node,
whatever the data, so what it observes is fixed by the circuit and its public
inputs: the operation trace in a syntactic order, the public values, and the
types of the ciphertexts.

`declared` computes that view. The Tcl view harness (`tclmesh views`) checks
that the evaluator's recorded view equals it on every run, and that runs which
agree on the public inputs give equal views (`docs/testing.md`).
-/

namespace TclMesh.Circuit

/-- Node words, type descriptors and maps are kept as the Tcl lists they are. -/
structure Circuit where
  inputs : List (String × List String)
  outputs : List (String × List String)
  nodes : List (String × List String)
  outputNodes : List (String × String)
  deriving Repr

def unaryOps : List String := ["negate", "not", "reduce-sum", "rotate", "polynomial"]

def binaryOps : List String :=
  ["add", "subtract", "multiply", "equal", "less-than", "less-or-equal", "greater-than",
    "greater-or-equal", "and", "or", "lookup"]

/-- The operands of a node, in order. -/
def refs : List String → List String
  | op :: a :: rest =>
    if op ∈ unaryOps then [a]
    else if op = "select" then a :: rest.take 2
    else if op ∈ binaryOps then a :: rest.take 1
    else []
  | _ => []

def Circuit.refsOf (c : Circuit) (id : String) : List String :=
  match c.nodes.lookup id with
  | some w => refs w
  | none => []

structure St where
  seen : List String
  order : List String

/-- Depth-first post-order: a node is marked, its operands are visited in
order, then it is emitted. -/
def visit (c : Circuit) : Nat → St → String → St
  | 0, st, _ => st
  | n + 1, st, id =>
    if id ∈ st.seen then st
    else
      let st' := (c.refsOf id).foldl (visit c n) ⟨id :: st.seen, st.order⟩
      ⟨st'.seen, st'.order ++ [id]⟩

def insertName (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if y < x then y :: insertName x ys else x :: y :: ys

/-- Names in sorted order (insertion sort: small lists, and it reduces). -/
def sortNames : List String → List String
  | [] => []
  | x :: xs => insertName x (sortNames xs)

/-- The syntactic evaluation order, from the outputs in sorted name order. -/
def schedule (c : Circuit) : List String :=
  ((sortNames (c.outputNodes.map Prod.fst)).foldl
    (fun st name => visit c (c.nodes.length + 1) st ((c.outputNodes.lookup name).getD ""))
    ⟨[], []⟩).order

def op (c : Circuit) (id : String) : String := ((c.nodes.lookup id).getD []).headD ""

/-- How the evaluator sees one input: a public value, or only a ciphertext's type. -/
inductive Seen where
  | pub (type value : String)
  | cipher (type : String)
  deriving Repr, DecidableEq

structure View where
  inputs : List (String × Seen)
  trace : List (String × String)
  outputs : List (String × String)
  deriving Repr

def visibility (d : List String) : String := d.headD ""
def logicalType (d : List String) : String := (d.drop 1).headD ""

/-- What the evaluator may observe, from the circuit and public inputs alone. -/
def declared (c : Circuit) (publics : List (String × String)) : View where
  inputs := (sortNames (c.inputs.map Prod.fst)).map fun name =>
    let d := (c.inputs.lookup name).getD []
    (name, if visibility d = "public" then .pub (logicalType d) ((publics.lookup name).getD "")
      else .cipher (logicalType d))
  trace := (schedule c).map fun id => (id, op c id)
  outputs := (sortNames (c.outputs.map Prod.fst)).map fun name =>
    (name, logicalType ((c.outputs.lookup name).getD []))

/-! ## Properties -/

/-- Runs that agree on the public inputs have the same declared view: the
view cannot depend on a ciphertext input, because none is an argument. -/
theorem declared_publics (c : Circuit) (p₁ p₂ : List (String × String))
    (h : ∀ name d, c.inputs.lookup name = some d → visibility d = "public" →
      p₁.lookup name = p₂.lookup name) :
    declared c p₁ = declared c p₂ := by
  simp only [declared, View.mk.injEq, and_true]
  apply List.map_congr_left
  intro name _
  cases hd : c.inputs.lookup name with
  | none => simp [visibility]
  | some d =>
    by_cases hv : visibility d = "public"
    · simp [hv, h name d hd hv]
    · simp [hv]

theorem visit_seen (c : Circuit) : ∀ n st id, ∀ x ∈ st.seen, x ∈ (visit c n st id).seen := by
  intro n
  induction n with
  | zero => intro st id x hx; exact hx
  | succ n ih =>
    intro st id x hx
    unfold visit
    split
    · exact hx
    · simp only
      suffices ∀ (l : List String) (s : St), x ∈ s.seen → x ∈ (l.foldl (visit c n) s).seen from
        this _ _ (List.mem_cons_of_mem _ hx)
      intro l
      induction l with
      | nil => intro s hs; exact hs
      | cons y ys ihl => intro s hs; exact ihl _ (ih s y x hs)

/-- Visiting emits only nodes it marks, each once and never one already marked. -/
theorem visit_order (c : Circuit) : ∀ n st id, ∃ new, (visit c n st id).order = st.order ++ new ∧
    new.Nodup ∧ (∀ x ∈ new, x ∉ st.seen) ∧ ∀ x ∈ new, x ∈ (visit c n st id).seen := by
  intro n
  induction n with
  | zero => intro st id; exact ⟨[], by simp [visit]⟩
  | succ n ih =>
    intro st id
    unfold visit
    split
    · exact ⟨[], by simp⟩
    · rename_i hid
      simp only
      -- the operands' visits emit fresh nodes, none of them `id`
      have hfold : ∀ (l : List String) (s : St), ∃ new, (l.foldl (visit c n) s).order = s.order ++ new ∧
          new.Nodup ∧ (∀ x ∈ new, x ∉ s.seen) ∧ (∀ x ∈ new, x ∈ (l.foldl (visit c n) s).seen) ∧
          ∀ x ∈ s.seen, x ∈ (l.foldl (visit c n) s).seen := by
        intro l
        induction l with
        | nil => intro s; exact ⟨[], by simp⟩
        | cons y ys ihl =>
          intro s
          obtain ⟨n1, h1, hd1, hf1, hm1⟩ := ih s y
          obtain ⟨n2, h2, hd2, hf2, hm2, hk2⟩ := ihl (visit c n s y)
          refine ⟨n1 ++ n2, by simp [List.foldl_cons, h2, h1], ?_, ?_, ?_, ?_⟩
          · rw [List.nodup_append]
            refine ⟨hd1, hd2, fun a ha b hb hab => ?_⟩
            subst hab; exact hf2 a hb (hm1 a ha)
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hf1 x hx
            · exact fun hs => hf2 x hx (visit_seen c n s y x hs)
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hk2 x (hm1 x hx)
            · exact hm2 x hx
          · intro x hx; exact hk2 x (visit_seen c n s y x hx)
      obtain ⟨new, hn, hd, hf, hm, hk⟩ := hfold (c.refsOf id) ⟨id :: st.seen, st.order⟩
      refine ⟨new ++ [id], by simp [hn], ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hd, by simp, fun a ha b hb hab => ?_⟩
        simp at hb; subst hb; subst hab
        exact hf a ha (List.mem_cons_self ..)
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact fun hs => hf x hx (List.mem_cons_of_mem _ hs)
        · simp at hx; subst hx; exact hid
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hm x hx
        · simp at hx; subst hx; exact hk _ (List.mem_cons_self ..)

/-- **Every node appears in the trace at most once.** -/
theorem schedule_nodup (c : Circuit) : (schedule c).Nodup := by
  unfold schedule
  suffices ∀ (l : List String) (s : St), s.order.Nodup → (∀ x ∈ s.order, x ∈ s.seen) →
      (l.foldl (fun st name => visit c (c.nodes.length + 1) st ((c.outputNodes.lookup name).getD ""))
        s).order.Nodup from this _ _ (by simp) (by simp)
  intro l
  induction l with
  | nil => intro s hs _; exact hs
  | cons y ys ih =>
    intro s hs hsub
    simp only [List.foldl_cons]
    obtain ⟨new, hn, hd, hf, hm⟩ := visit_order c (c.nodes.length + 1) s ((c.outputNodes.lookup y).getD "")
    apply ih
    · rw [hn, List.nodup_append]
      exact ⟨hs, hd, fun a ha b hb hab => by subst hab; exact hf a hb (hsub a ha)⟩
    · intro x hx
      rw [hn] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact visit_seen c _ s _ x (hsub x hx)
      · exact hm x hx

/-! ## Example (checked by evaluation) -/

def maxBid : Circuit where
  inputs := [("a", ["cipher", "int"]), ("b", ["cipher", "int"]), ("reserve", ["public", "int"])]
  outputs := [("winner", ["cipher", "int"]), ("above", ["cipher", "bool"]),
    ("margin", ["cipher", "int"])]
  nodes := [("na", ["input", "a"]), ("nb", ["input", "b"]), ("nr", ["input", "reserve"]),
    ("gt", ["greater-than", "na", "nb"]), ("best", ["select", "gt", "na", "nb"]),
    ("above", ["greater-than", "best", "nr"]), ("ab", ["subtract", "na", "nb"]),
    ("ba", ["subtract", "nb", "na"]), ("margin", ["select", "gt", "ab", "ba"])]
  outputNodes := [("winner", "best"), ("above", "above"), ("margin", "margin")]

example : schedule maxBid = ["na", "nb", "gt", "best", "nr", "above", "ab", "ba", "margin"] := by
  decide

end TclMesh.Circuit
