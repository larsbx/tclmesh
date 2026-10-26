import TclMesh.Circuit

/-!
# Circuit certificates

The meta-language does not need a proved compiler: it emits, with every
circuit, a certificate that a small checker validates before activation.

A certificate labels every node `pub` or `cipher` and names the `select`
nodes that run obliviously (a homomorphic CMUX evaluating both branches). The
checker requires:

* an input node's label is at least its declared visibility;
* an operation's label is at least the label of each operand;
* a `select` whose condition is `cipher` is oblivious;
* an output declared `public` is computed by a `pub` node.

`check_sound` proves the checker sound for **every** operation semantics: a
node certified `pub` has the same value on any two inputs that agree on the
public inputs. Labels can only over-approximate, and a certificate that
under-labels a node, forgets an oblivious select, or demotes a ciphertext
input is rejected (`tests/certificates.test` mutates certificates to check
the rejections).
-/

namespace TclMesh.Circuit

inductive Label where
  | pub
  | cipher
  deriving Repr, DecidableEq

def Label.le : Label → Label → Bool
  | .pub, _ => true
  | .cipher, l => l = .cipher

structure Certificate where
  labels : List (String × Label)
  oblivious : List String
  deriving Repr

def visLabel (d : List String) : Label := if visibility d = "public" then .pub else .cipher

def Certificate.label (cert : Certificate) (id : String) : Label :=
  (cert.labels.lookup id).getD .cipher

/-- One node's obligations. -/
def nodeOk (c : Circuit) (cert : Certificate) (id : String) (w : List String) : Bool :=
  match cert.labels.lookup id with
  | none => false
  | some l =>
    (match w with
      | ["input", x] => (visLabel ((c.inputs.lookup x).getD [])).le l
      | _ => (refs w).all fun r => (cert.label r).le l) &&
    (match w with
      | ["select", cond, _, _] => cert.label cond = .pub || cert.oblivious.contains id
      | _ => true)

def check (c : Circuit) (cert : Certificate) : Bool :=
  c.nodes.all (fun (id, w) => nodeOk c cert id w) &&
  c.outputs.all fun (name, d) =>
    visibility d ≠ "public" || cert.label ((c.outputNodes.lookup name).getD "") = .pub

/-! ## Soundness -/

/-- Evaluation under an arbitrary semantics for operations: `sem` receives a
node's words and its operands' values. -/
def evalNode (sem : List String → List Int → Int) (inp : String → Int) (c : Circuit) :
    Nat → String → Int
  | 0, _ => 0
  | n + 1, id =>
    match c.nodes.lookup id with
    | some ["input", x] => inp x
    | some w => sem w ((refs w).map (evalNode sem inp c n))
    | none => 0

/-- Two inputs agree on everything public. -/
def PubEq (c : Circuit) (i₁ i₂ : String → Int) : Prop :=
  ∀ x d, c.inputs.lookup x = some d → visLabel d = .pub → i₁ x = i₂ x

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : a = k
    · subst hk; simp [List.lookup] at h; subst h; exact List.mem_cons_self ..
    · have : (a == k) = false := by simpa using hk
      simp [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem le_pub {l : Label} (h : l.le .pub = true) : l = .pub := by
  cases l <;> simp_all [Label.le]

/-- **Soundness**: a node certified `pub` computes the same value on inputs
that agree on the public inputs, whatever the operations mean. -/
theorem check_sound (c : Circuit) (cert : Certificate) (hc : check c cert = true)
    (sem : List String → List Int → Int) (i₁ i₂ : String → Int) (hpub : PubEq c i₁ i₂) :
    ∀ n id, cert.label id = .pub → evalNode sem i₁ c n id = evalNode sem i₂ c n id := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hnodes, -⟩ := hc
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro id hl
    cases hw : c.nodes.lookup id with
    | none => simp [evalNode, hw]
    | some w =>
      have hok := hnodes (id, w) (lookup_mem hw)
      simp only [nodeOk] at hok
      have hlab : cert.labels.lookup id = some .pub := by
        unfold Certificate.label at hl
        cases h : cert.labels.lookup id with
        | none => simp [h] at hl
        | some l => simp [h] at hl; rw [hl]
      rw [hlab] at hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨hlabels, -⟩ := hok
      by_cases hin : ∃ x, w = ["input", x]
      · -- an input: certified public, so declared public, so the inputs agree
        obtain ⟨x, rfl⟩ := hin
        simp only [evalNode, hw]
        apply hpub x ((c.inputs.lookup x).getD [])
        · cases h : c.inputs.lookup x with
          | none => simp [visLabel, visibility, h, Label.le] at hlabels
          | some d => rfl
        · exact le_pub hlabels
      · -- an operation: every operand is certified public
        have hall : (refs w).all (fun r => (cert.label r).le .pub) = true := by
          split at hlabels
          · exact absurd ⟨_, rfl⟩ hin
          · exact hlabels
        have hrefs : ∀ r ∈ refs w, cert.label r = .pub :=
          fun r hr => le_pub ((List.all_eq_true.mp hall) r hr)
        simp only [evalNode, hw]
        split
        · rename_i x hx
          exact absurd ⟨x, by simpa using hx⟩ hin
        · rename_i heq
          simp only [Option.some.injEq] at heq
          subst heq
          congr 1
          apply List.map_congr_left
          intro r hr
          exact ih r (hrefs r hr)
        · rfl

/-- Outputs declared public depend on public inputs only. -/
theorem public_outputs (c : Circuit) (cert : Certificate) (hc : check c cert = true)
    (sem : List String → List Int → Int) (i₁ i₂ : String → Int) (hpub : PubEq c i₁ i₂)
    (name : String) (d : List String) (hd : c.outputs.lookup name = some d)
    (hv : visibility d = "public") (n : Nat) :
    evalNode sem i₁ c n ((c.outputNodes.lookup name).getD "") =
      evalNode sem i₂ c n ((c.outputNodes.lookup name).getD "") := by
  apply check_sound c cert hc sem i₁ i₂ hpub
  simp only [check, Bool.and_eq_true, List.all_eq_true] at hc
  have := hc.2 (name, d) (lookup_mem hd)
  simp [hv] at this
  exact this

/-! ## The least certificate -/

/-- Least labels, by fuel-bounded recursion over operands. -/
def leastLabel (c : Circuit) : Nat → String → Label
  | 0, _ => .cipher
  | n + 1, id =>
    match c.nodes.lookup id with
    | some ["input", x] => visLabel ((c.inputs.lookup x).getD [])
    | some w => if (refs w).all fun r => leastLabel c n r = .pub then .pub else .cipher
    | none => .cipher

/-- The certificate the compiler emits: least labels; every select on a
ciphertext condition is oblivious. -/
def certify (c : Circuit) : Certificate where
  labels := c.nodes.map fun (id, _) => (id, leastLabel c (c.nodes.length + 1) id)
  oblivious := (c.nodes.filter fun (_, w) => w.headD "" = "select" &&
      leastLabel c (c.nodes.length + 1) ((refs w).headD "") = .cipher).map Prod.fst

example : check maxBid (certify maxBid) = true := by decide

/-- Demoting the comparison of two secret bids to `pub` is rejected. -/
example : check maxBid { certify maxBid with
    labels := (certify maxBid).labels.map fun (id, l) => (id, if id = "gt" then .pub else l) } = false := by
  decide

/-- Forgetting that a select on a secret condition must be oblivious is rejected. -/
example : check maxBid { certify maxBid with oblivious := [] } = false := by decide

end TclMesh.Circuit
