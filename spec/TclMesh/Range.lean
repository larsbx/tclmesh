import TclMesh.Certificate

/-!
# Range certificates: when wrapped integers are exact

A homomorphic integer of `w` bits (TFHE `FheInt32`, `w = 32`) computes every
arithmetic operation modulo `2^w`, and an overflow under encryption cannot be
detected. Wrapping is harmless exactly when it never happens, and that can be
decided before evaluation, from public information only: a range for every
input, propagated through the circuit by interval arithmetic.

A range certificate gives every node a closed integer range. The checker
requires:

* every range lies in the signed word `[-2^(w-1), 2^(w-1) - 1]`;
* an input's range contains its declared range (`{cipher int range LO HI}`;
  the whole word when none is declared; `[0, 1]` for `bool`);
* a constant's range contains it;
* `add`, `subtract`, `negate`: the range contains the interval extension of
  the operands' ranges; `multiply`: it contains the four bound products;
* comparisons and `and`, `or`, `not` produce `[0, 1]`;
* `select`: the range contains both branches' ranges;
* `clamp x lo hi` (`max lo (min x hi)`, never wrapped): both ordered
  bounds fit the signed word, and the range contains the clamped operand range;
* every other operation is rejected.

`check_sound` proves that if the checker accepts and the inputs lie in their
declared ranges, then wherever the exact evaluation over `ℤ` is defined, the
wrapped evaluation is defined, equal to it, and inside the node's range.
`guarded_sound` drops the hypothesis for circuits whose inputs declare no
narrower range (the form `tclmesh range guard` produces, enforcing declared
ranges with `clamp`): there it is the type invariant of a ciphertext, a
`w`-bit word or a bit, which no party has to vouch for.
The arithmetic (`wordMin`, `wordMax`, `wrap`, interval extension) is the
contract of `finite_exact/word_range.mojo` in `larsbx/finite-math-kernels`,
whose corpus is replayed against these definitions (`spec-eval --word-range`).

That TFHE computes `wrapped 32` — each operation decrypts to the wrapped
result of its plaintext operation — is the backend's correctness within its
noise budget, a named hypothesis outside this model (`docs/proofs.md`); its
noise-budget part is `Noise.bootstrapped_sound`.
-/

namespace TclMesh.Range

open TclMesh.Circuit

/-! ## The word -/

def half (w : Nat) : Int := ((2 ^ (w - 1) : Nat) : Int)
def wordMin (w : Nat) : Int := -half w
def wordMax (w : Nat) : Int := half w - 1

/-- The representative of `x` modulo `2 * half w` (`= 2^w` for `w ≥ 1`) in the word. -/
def wrap (w : Nat) (x : Int) : Int := (x + half w) % (2 * half w) - half w

theorem half_pos (w : Nat) : 0 < half w := by
  unfold half; exact Int.ofNat_lt.mpr (Nat.two_pow_pos _)

/-- Wrapping is the identity on the word. -/
theorem wrap_id {w : Nat} {x : Int} (lo : wordMin w ≤ x) (hi : x ≤ wordMax w) : wrap w x = x := by
  unfold wrap; unfold wordMin at lo; unfold wordMax at hi
  have := half_pos w
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

example : 2 * half 32 = 2 ^ 32 := by decide
example : wrap 32 (2147483647 + 1) = -2147483648 := by decide

/-! ## Semantics -/

def b2i (b : Bool) : Int := if b then 1 else 0

/-- Canonical decimal integers `-?(0|[1-9][0-9]*)`, without `-0`: the only
spelling of a constant or a declared bound that the runtime accepts. -/
def natOf (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else cs.foldl (fun acc ch => acc.bind fun n =>
    if ch.isDigit then some (10 * n + (ch.toNat - '0'.toNat)) else none) (some 0)

def intOf (s : String) : Option Int :=
  match s.toList with
  | '-' :: '0' :: _ => none
  | '-' :: cs => (natOf cs).map fun n => -(n : Int)
  | '0' :: _ :: _ => none
  | cs => (natOf cs).map Int.ofNat

example : ["0", "7", "-12", "2147483647"].map intOf = [some 0, some 7, some (-12), some 2147483647] := by
  decide
example : ["", "-", "-0", "007", "+1", "1e3", " 1"].map intOf = [none, none, none, none, none, none, none] := by
  decide

def constVal (k : String) : Int := (intOf k).getD 0

/-- One semantics for every reduction `f` of arithmetic results: `exact` over
`ℤ` is `f = id`, a `w`-bit homomorphic integer is `f = wrap w`. Booleans are
`0`/`1`; a nonzero integer is true, as TFHE casts it. -/
def semWith (f : Int → Int) : List String → List Int → Int
  | ["constant", k], _ => f (constVal k)
  | ["add", _, _], [x, y] => f (x + y)
  | ["subtract", _, _], [x, y] => f (x - y)
  | ["multiply", _, _], [x, y] => f (x * y)
  | ["negate", _], [x] => f (-x)
  | ["equal", _, _], [x, y] => b2i (x == y)
  | ["less-than", _, _], [x, y] => b2i (decide (x < y))
  | ["less-or-equal", _, _], [x, y] => b2i (decide (x ≤ y))
  | ["greater-than", _, _], [x, y] => b2i (decide (x > y))
  | ["greater-or-equal", _, _], [x, y] => b2i (decide (x ≥ y))
  | ["and", _, _], [x, y] => b2i (x != 0 && y != 0)
  | ["or", _, _], [x, y] => b2i (x != 0 || y != 0)
  | ["not", _], [x] => b2i (x == 0)
  | ["select", _, _, _], [c, a, b] => if c != 0 then a else b
  | ["clamp", _, lo, hi], [x] => max (constVal lo) (min x (constVal hi))
  | _, _ => 0

def exact : List String → List Int → Int := semWith id
def wrapped (w : Nat) : List String → List Int → Int := semWith (wrap w)

/-- Evaluation that is undefined (`none`) when fuel runs out or a node is
missing, so that nothing is asserted about a value never computed. -/
def evalOpt (sem : List String → List Int → Int) (inp : String → Int) (c : Circuit) :
    Nat → String → Option Int
  | 0, _ => none
  | n + 1, id =>
    match c.nodes.lookup id with
    | some ["input", x] => some (inp x)
    | some w => ((refs w).mapM (evalOpt sem inp c n)).map (sem w)
    | none => none

/-! ## Ranges and the checker -/

abbrev Rng := Int × Int
abbrev Ranges := List (String × Rng)

def inR (v : Int) (r : Rng) : Bool := decide (r.1 ≤ v) && decide (v ≤ r.2)

/-- `[lo, hi] ⊆ r`. -/
def within (lo hi : Int) (r : Rng) : Bool := decide (r.1 ≤ lo) && decide (hi ≤ r.2)

def word (w : Nat) : Rng := (wordMin w, wordMax w)

/-- The declared range of an input descriptor. -/
def inputRange (w : Nat) : List String → Option Rng
  | [_, "int"] => some (word w)
  | [_, "int", "range", lo, hi] => match intOf lo, intOf hi with
    | some a, some b => some (a, b)
    | _, _ => none
  | [_, "bool"] => some (0, 1)
  | _ => none

/-- Least ranges of the operations (the natural interval extension). -/
def addR (p q : Rng) : Rng := (p.1 + q.1, p.2 + q.2)
def subR (p q : Rng) : Rng := (p.1 - q.2, p.2 - q.1)
def negR (p : Rng) : Rng := (-p.2, -p.1)
def mulR (p q : Rng) : Rng :=
  (min (min (p.1 * q.1) (p.1 * q.2)) (min (p.2 * q.1) (p.2 * q.2)),
   max (max (p.1 * q.1) (p.1 * q.2)) (max (p.2 * q.1) (p.2 * q.2)))
def hullR (p q : Rng) : Rng := (min p.1 q.1, max p.2 q.2)
def clampR (p : Rng) (lo hi : Int) : Rng := (max lo (min p.1 hi), max lo (min p.2 hi))

def two (cert : Ranges) (a b : String) (k : Rng → Rng → Bool) : Bool :=
  match cert.lookup a, cert.lookup b with
  | some p, some q => k p q
  | _, _ => false

def one (cert : Ranges) (a : String) (k : Rng → Bool) : Bool :=
  match cert.lookup a with
  | some p => k p
  | none => false

/-- One node's obligation, for its certified range `r`. -/
def nodeOk (c : Circuit) (cert : Ranges) (w : Nat) (r : Rng) : List String → Bool
  | ["input", x] => match (c.inputs.lookup x).bind (inputRange w) with
    | some d => within d.1 d.2 r
    | none => false
  | ["constant", k] => match intOf k with
    | some v => inR v r
    | none => false
  | ["add", a, b] => two cert a b fun p q => within (addR p q).1 (addR p q).2 r
  | ["subtract", a, b] => two cert a b fun p q => within (subR p q).1 (subR p q).2 r
  | ["multiply", a, b] => two cert a b fun p q =>
      inR (p.1 * q.1) r && inR (p.1 * q.2) r && inR (p.2 * q.1) r && inR (p.2 * q.2) r
  | ["negate", a] => one cert a fun p => within (negR p).1 (negR p).2 r
  | ["equal", a, b] => two cert a b fun _ _ => within 0 1 r
  | ["less-than", a, b] => two cert a b fun _ _ => within 0 1 r
  | ["less-or-equal", a, b] => two cert a b fun _ _ => within 0 1 r
  | ["greater-than", a, b] => two cert a b fun _ _ => within 0 1 r
  | ["greater-or-equal", a, b] => two cert a b fun _ _ => within 0 1 r
  | ["and", a, b] => two cert a b fun _ _ => within 0 1 r
  | ["or", a, b] => two cert a b fun _ _ => within 0 1 r
  | ["not", a] => one cert a fun _ => within 0 1 r
  | ["select", k, a, b] => one cert k fun _ => two cert a b fun p q =>
      within p.1 p.2 r && within q.1 q.2 r
  | ["clamp", a, lo, hi] => match intOf lo, intOf hi with
    | some l, some h => decide (l ≤ h) && (within l h (word w) &&
        one cert a fun p => within (clampR p l h).1 (clampR p l h).2 r)
    | _, _ => false
  | _ => false

def check (c : Circuit) (cert : Ranges) (w : Nat) : Bool :=
  cert.all (fun (_, r) => within r.1 r.2 (word w)) &&
  c.nodes.all fun (id, ws) => match cert.lookup id with
    | some r => nodeOk c cert w r ws
    | none => false

/-- Every input lies in its declared range. -/
def InputsInRange (c : Circuit) (w : Nat) (inp : String → Int) : Prop :=
  ∀ x d r, c.inputs.lookup x = some d → inputRange w d = some r → inR (inp x) r = true

/-! ## Soundness -/

theorem inR_iff {v : Int} {r : Rng} : inR v r = true ↔ r.1 ≤ v ∧ v ≤ r.2 := by
  simp [inR]

theorem within_iff {lo hi : Int} {r : Rng} : within lo hi r = true ↔ r.1 ≤ lo ∧ hi ≤ r.2 := by
  simp [within]

/-- `x * y` lies between the products of `x`'s bounds with `y`. -/
theorem mul_between {a b x y : Int} (ha : a ≤ x) (hb : x ≤ b) :
    (a * y ≤ x * y ∧ x * y ≤ b * y) ∨ (b * y ≤ x * y ∧ x * y ≤ a * y) := by
  rcases Int.le_total 0 y with hy | hy
  · exact .inl ⟨Int.mul_le_mul_of_nonneg_right ha hy, Int.mul_le_mul_of_nonneg_right hb hy⟩
  · exact .inr ⟨Int.mul_le_mul_of_nonpos_right hb hy, Int.mul_le_mul_of_nonpos_right ha hy⟩

/-- A product lies in any range that holds the four bound products. -/
theorem mul_mem {p q r : Rng} {x y : Int} (hx : inR x p = true) (hy : inR y q = true)
    (h11 : inR (p.1 * q.1) r = true) (h12 : inR (p.1 * q.2) r = true)
    (h21 : inR (p.2 * q.1) r = true) (h22 : inR (p.2 * q.2) r = true) :
    inR (x * y) r = true := by
  rw [inR_iff] at *
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have e1 := mul_between (y := y) hx1 hx2
  have e2 := mul_between (y := p.1) hy1 hy2
  have e3 := mul_between (y := p.2) hy1 hy2
  have := Int.mul_comm q.1 p.1; have := Int.mul_comm q.2 p.1
  have := Int.mul_comm q.1 p.2; have := Int.mul_comm q.2 p.2
  have := Int.mul_comm p.1 y; have := Int.mul_comm p.2 y
  omega

theorem mapM_one {f : String → Option Int} {a : String} {vs : List Int}
    (h : [a].mapM f = some vs) : ∃ x, f a = some x ∧ vs = [x] := by
  cases hfa : f a <;> simp_all [List.mapM_cons]

theorem mapM_two {f : String → Option Int} {a b : String} {vs : List Int}
    (h : [a, b].mapM f = some vs) : ∃ x y, f a = some x ∧ f b = some y ∧ vs = [x, y] := by
  cases hfa : f a <;> cases hfb : f b <;> simp_all [List.mapM_cons]

theorem mapM_three {f : String → Option Int} {a b k : String} {vs : List Int}
    (h : [k, a, b].mapM f = some vs) :
    ∃ z x y, f k = some z ∧ f a = some x ∧ f b = some y ∧ vs = [z, x, y] := by
  cases hfk : f k <;> cases hfa : f a <;> cases hfb : f b <;> simp_all [List.mapM_cons]

theorem evalOpt_succ {sem : List String → List Int → Int} {inp : String → Int} {c : Circuit}
    {n : Nat} {id : String} {ws : List String} (hw : c.nodes.lookup id = some ws)
    (hne : ∀ x, ws ≠ ["input", x]) :
    evalOpt sem inp c (n + 1) id = ((refs ws).mapM (evalOpt sem inp c n)).map (sem ws) := by
  rw [evalOpt, hw]
  split
  · rename_i x h; cases h; exact absurd rfl (hne x)
  · rename_i h; cases h; rfl
  · contradiction

theorem mapM_of_one {f : String → Option Int} {a : String} {x : Int} (ha : f a = some x) :
    [a].mapM f = some [x] := by simp [List.mapM_cons, ha]

theorem mapM_of_two {f : String → Option Int} {a b : String} {x y : Int}
    (ha : f a = some x) (hb : f b = some y) : [a, b].mapM f = some [x, y] := by
  simp [List.mapM_cons, ha, hb]

theorem mapM_of_three {f : String → Option Int} {k a b : String} {z x y : Int}
    (hk : f k = some z) (ha : f a = some x) (hb : f b = some y) :
    [k, a, b].mapM f = some [z, x, y] := by
  simp [List.mapM_cons, hk, ha, hb]

/-- The induction hypothesis, for the operands evaluated with fuel `n`. -/
def Sound (c : Circuit) (cert : Ranges) (w : Nat) (inp : String → Int) (n : Nat) : Prop :=
  ∀ id v, evalOpt exact inp c n id = some v →
    (∃ r, cert.lookup id = some r ∧ inR v r = true) ∧ evalOpt (wrapped w) inp c n id = some v

section Cases

variable {c : Circuit} {cert : Ranges} {w : Nat} {inp : String → Int} {n : Nat}
  {id : String} {ws : List String} {r : Rng} {v : Int}

/-- A node with no operands. -/
theorem nullary (hw : c.nodes.lookup id = some ws) (hrefs : refs ws = [])
    (hne : ∀ x, ws ≠ ["input", x])
    (hsem : inR (exact ws []) r = true → wrapped w ws [] = exact ws [])
    (hencl : inR (exact ws []) r = true) (hv : evalOpt exact inp c (n + 1) id = some v) :
    inR v r = true ∧ evalOpt (wrapped w) inp c (n + 1) id = some v := by
  rw [evalOpt_succ hw hne, hrefs] at hv ⊢
  simp only [List.mapM_nil, pure, Option.map_some, Option.some.injEq] at hv ⊢
  subst hv
  exact ⟨hencl, hsem hencl⟩

/-- A node with one operand. -/
theorem unary {a : String} (ih : Sound c cert w inp n) (hw : c.nodes.lookup id = some ws)
    (hrefs : refs ws = [a]) (hne : ∀ x, ws ≠ ["input", x])
    (hsem : ∀ x, inR (exact ws [x]) r = true → wrapped w ws [x] = exact ws [x])
    (hencl : ∀ p x, cert.lookup a = some p → inR x p = true → inR (exact ws [x]) r = true)
    (hv : evalOpt exact inp c (n + 1) id = some v) :
    inR v r = true ∧ evalOpt (wrapped w) inp c (n + 1) id = some v := by
  rw [evalOpt_succ hw hne, hrefs] at hv ⊢
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp hv
  obtain ⟨x, hx, rfl⟩ := mapM_one hvs
  obtain ⟨⟨p, hp, hxp⟩, hx'⟩ := ih a x hx
  have h := hencl p x hp hxp
  rw [mapM_of_one hx']
  exact ⟨h, by simp [hsem x h]⟩

/-- A node with two operands. -/
theorem binary {a b : String} (ih : Sound c cert w inp n) (hw : c.nodes.lookup id = some ws)
    (hrefs : refs ws = [a, b]) (hne : ∀ x, ws ≠ ["input", x])
    (hsem : ∀ x y, inR (exact ws [x, y]) r = true → wrapped w ws [x, y] = exact ws [x, y])
    (hencl : ∀ p q x y, cert.lookup a = some p → cert.lookup b = some q →
      inR x p = true → inR y q = true → inR (exact ws [x, y]) r = true)
    (hv : evalOpt exact inp c (n + 1) id = some v) :
    inR v r = true ∧ evalOpt (wrapped w) inp c (n + 1) id = some v := by
  rw [evalOpt_succ hw hne, hrefs] at hv ⊢
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp hv
  obtain ⟨x, y, hx, hy, rfl⟩ := mapM_two hvs
  obtain ⟨⟨p, hp, hxp⟩, hx'⟩ := ih a x hx
  obtain ⟨⟨q, hq, hyq⟩, hy'⟩ := ih b y hy
  have h := hencl p q x y hp hq hxp hyq
  rw [mapM_of_two hx' hy']
  exact ⟨h, by simp [hsem x y h]⟩

/-- A node with three operands. -/
theorem ternary {k a b : String} (ih : Sound c cert w inp n) (hw : c.nodes.lookup id = some ws)
    (hrefs : refs ws = [k, a, b]) (hne : ∀ x, ws ≠ ["input", x])
    (hsem : ∀ z x y, wrapped w ws [z, x, y] = exact ws [z, x, y])
    (hencl : ∀ p q z x y, cert.lookup a = some p → cert.lookup b = some q →
      inR x p = true → inR y q = true → inR (exact ws [z, x, y]) r = true)
    (hv : evalOpt exact inp c (n + 1) id = some v) :
    inR v r = true ∧ evalOpt (wrapped w) inp c (n + 1) id = some v := by
  rw [evalOpt_succ hw hne, hrefs] at hv ⊢
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp hv
  obtain ⟨z, x, y, hz, hx, hy, rfl⟩ := mapM_three hvs
  obtain ⟨-, hz'⟩ := ih k z hz
  obtain ⟨⟨p, hp, hxp⟩, hx'⟩ := ih a x hx
  obtain ⟨⟨q, hq, hyq⟩, hy'⟩ := ih b y hy
  rw [mapM_of_three hz' hx' hy']
  exact ⟨hencl p q z x y hp hq hxp hyq, by simp [hsem z x y]⟩

end Cases

theorem b2i_mem {b : Bool} {r : Rng} (h : within 0 1 r = true) : inR (b2i b) r = true := by
  rw [within_iff] at h; rw [inR_iff]; cases b <;> simp [b2i] <;> omega

theorem step (c : Circuit) (cert : Ranges) (w : Nat) (inp : String → Int)
    (hin : InputsInRange c w inp)
    (hwrap : ∀ id r v, cert.lookup id = some r → inR v r = true → wrap w v = v)
    (n : Nat) (ih : Sound c cert w inp n) (id : String) (ws : List String) (r : Rng)
    (hw : c.nodes.lookup id = some ws) (hr : cert.lookup id = some r)
    (hok : nodeOk c cert w r ws = true) (v : Int) (hv : evalOpt exact inp c (n + 1) id = some v) :
    inR v r = true ∧ evalOpt (wrapped w) inp c (n + 1) id = some v := by
  unfold nodeOk at hok
  split at hok
  -- an input: its value is given, the same under both semantics
  next x =>
    simp only [evalOpt, hw] at hv ⊢
    cases hd : c.inputs.lookup x with
    | none => simp [hd] at hok
    | some d =>
      cases hrd : inputRange w d with
      | none => simp [hd, hrd] at hok
      | some q =>
        simp only [hd, hrd, Option.bind_some, within_iff] at hok
        have := inR_iff.mp (hin x d q hd hrd)
        cases hv
        exact ⟨inR_iff.mpr ⟨by omega, by omega⟩, rfl⟩
  -- a constant: certified, so inside the word, where it does not wrap
  next k =>
    cases hk : intOf k with
    | none => simp [hk] at hok
    | some u =>
      simp only [hk] at hok
      have he : exact ["constant", k] [] = u := by simp [exact, semWith, constVal, hk]
      exact nullary hw (by simp [refs, unaryOps, binaryOps]) (by simp)
        (fun h => by simp only [wrapped, semWith, exact, constVal, hk, Option.getD_some] at h ⊢
                     exact hwrap id r u hr (by simpa [he] using h))
        (by rw [he]; exact hok) hv
  -- arithmetic: the exact result lies in the certified range, inside the word
  next a b =>
    simp only [two] at hok; split at hok <;> try contradiction
    rename_i p q hp hq; simp only [within_iff, addR] at hok
    exact binary (a := a) (b := b) ih hw (by simp [refs, unaryOps, binaryOps]) (by simp)
      (fun x y h => by simp only [wrapped, exact, semWith] at h ⊢; exact hwrap id r _ hr h)
      (fun p' q' x y hp' hq' hx hy => by
        rw [hp] at hp'; rw [hq] at hq'; cases hp'; cases hq'
        rw [inR_iff] at hx hy; simp only [exact, semWith, _root_.id]; rw [inR_iff]; omega) hv
  next a b =>
    simp only [two] at hok; split at hok <;> try contradiction
    rename_i p q hp hq; simp only [within_iff, subR] at hok
    exact binary (a := a) (b := b) ih hw (by simp [refs, unaryOps, binaryOps]) (by simp)
      (fun x y h => by simp only [wrapped, exact, semWith] at h ⊢; exact hwrap id r _ hr h)
      (fun p' q' x y hp' hq' hx hy => by
        rw [hp] at hp'; rw [hq] at hq'; cases hp'; cases hq'
        rw [inR_iff] at hx hy; simp only [exact, semWith, _root_.id]; rw [inR_iff]; omega) hv
  next a b =>
    simp only [two] at hok; split at hok <;> try contradiction
    rename_i p q hp hq; simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨⟨h11, h12⟩, h21⟩, h22⟩ := hok
    exact binary (a := a) (b := b) ih hw (by simp [refs, unaryOps, binaryOps]) (by simp)
      (fun x y h => by simp only [wrapped, exact, semWith] at h ⊢; exact hwrap id r _ hr h)
      (fun p' q' x y hp' hq' hx hy => by
        rw [hp] at hp'; rw [hq] at hq'; cases hp'; cases hq'
        simp only [exact, semWith, _root_.id]; exact mul_mem hx hy h11 h12 h21 h22) hv
  next a =>
    simp only [one] at hok; split at hok <;> try contradiction
    rename_i p hp; simp only [within_iff, negR] at hok
    exact unary (a := a) ih hw (by simp [refs, unaryOps]) (by simp)
      (fun x h => by simp only [wrapped, exact, semWith] at h ⊢; exact hwrap id r _ hr h)
      (fun p' x hp' hx => by
        rw [hp] at hp'; cases hp'
        rw [inR_iff] at hx; simp only [exact, semWith, _root_.id]; rw [inR_iff]; omega) hv
  -- comparisons and connectives: `0` or `1`, never wrapped
  all_goals first
    | (simp only [two] at hok; split at hok <;> try contradiction
       exact binary ih hw (by simp [refs, unaryOps, binaryOps] <;> exact ⟨rfl, rfl⟩) (by simp)
         (fun _ _ _ => by simp [wrapped, exact, semWith])
         (fun _ _ _ _ _ _ _ _ => by simp only [exact, semWith]; exact b2i_mem hok) hv)
    | (simp only [one] at hok; split at hok <;> try contradiction
       exact unary ih hw (by simp [refs, unaryOps] <;> rfl) (by simp)
         (fun _ _ => by simp [wrapped, exact, semWith])
         (fun _ _ _ _ => by simp only [exact, semWith]; exact b2i_mem hok) hv)
    | skip
  -- an oblivious select: either branch's value, so within the hull
  next k a b =>
    simp only [one] at hok; split at hok <;> try contradiction
    simp only [two] at hok; split at hok <;> try contradiction
    rename_i p q hp hq
    simp only [Bool.and_eq_true, within_iff] at hok
    exact ternary (k := k) (a := a) (b := b) ih hw (by simp [refs, unaryOps]) (by simp)
      (fun _ _ _ => by simp [wrapped, exact, semWith])
      (fun p' q' z x y hp' hq' hx hy => by
        rw [hp] at hp'; rw [hq] at hq'; cases hp'; cases hq'
        rw [inR_iff] at hx hy; simp only [exact, semWith]; rw [inR_iff]; split <;> omega) hv
  -- a clamp: monotone, so the clamped operand range holds its value; no wrap
  next a lo hi =>
    cases hl : intOf lo with
    | none => simp [hl] at hok
    | some l =>
      cases hh : intOf hi with
      | none => simp [hl, hh] at hok
      | some h =>
        simp only [hl, hh, Bool.and_eq_true, decide_eq_true_eq, one] at hok
        obtain ⟨-, -, hok⟩ := hok
        split at hok <;> try contradiction
        rename_i p hp; simp only [within_iff, clampR] at hok
        exact unary (a := a) ih hw (by simp [refs, unaryOps]) (by simp)
          (fun _ _ => by simp [wrapped, exact, semWith])
          (fun p' x hp' hx => by
            rw [hp] at hp'; cases hp'
            rw [inR_iff] at hx; simp only [exact, semWith, constVal, hl, hh, Option.getD_some]
            rw [inR_iff]; omega) hv
  -- any other operation is rejected
  next => simp at hok

/-- **Soundness**: if the checker accepts and the inputs lie in their declared
ranges, wherever exact evaluation over `ℤ` is defined, `w`-bit wrapped
evaluation is defined and equal to it, and the value lies in its node's
certified range. No intermediate wraps. -/
theorem check_sound (c : Circuit) (cert : Ranges) (w : Nat) (hc : check c cert w = true)
    (inp : String → Int) (hin : InputsInRange c w inp) :
    ∀ n id v, evalOpt exact inp c n id = some v →
      (∃ r, cert.lookup id = some r ∧ inR v r = true) ∧ evalOpt (wrapped w) inp c n id = some v := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hword, hnodes⟩ := hc
  -- every certified value is in the word, where wrapping is the identity
  have hwrap : ∀ id r v, cert.lookup id = some r → inR v r = true → wrap w v = v := by
    intro id r v hr hv
    have := hword (id, r) (lookup_mem hr)
    simp only [within_iff, word] at this
    rw [inR_iff] at hv
    exact wrap_id (by omega) (by omega)
  intro n
  induction n with
  | zero => intro id v h; simp [evalOpt] at h
  | succ n ih =>
    intro id v hv
    cases hw : c.nodes.lookup id with
    | none => simp [evalOpt, hw] at hv
    | some ws =>
      have hok := hnodes (id, ws) (lookup_mem hw)
      simp only at hok
      cases hr : cert.lookup id with
      | none => simp [hr] at hok
      | some r =>
        simp only [hr] at hok
        obtain ⟨h1, h2⟩ := step c cert w inp hin hwrap n ih id ws r hw hr hok v hv
        exact ⟨⟨r, rfl, h1⟩, h2⟩

/-- The runtime may label a checked output `bool` only when its certified
range lies in `[0,1]`. Combined with `check_sound`, this preserves the input
bit hypothesis of a subsequent checked circuit, without decryption. -/
theorem bit_output_sound (c : Circuit) (cert : Ranges) (w : Nat)
    (hc : check c cert w = true) (inp : String → Int) (hin : InputsInRange c w inp)
    (id : String) (r : Rng) (hr : cert.lookup id = some r)
    (hb : within r.1 r.2 (0, 1) = true) (n : Nat) (v : Int)
    (hv : evalOpt exact inp c n id = some v) :
    inR v (0, 1) = true ∧ evalOpt (wrapped w) inp c n id = some v := by
  obtain ⟨⟨r', hr', hv'⟩, hw⟩ := check_sound c cert w hc inp hin n id v hv
  rw [hr] at hr'
  cases hr'
  exact ⟨inR_iff.mpr (by
    have := inR_iff.mp hv'
    have := within_iff.mp hb
    constructor <;> omega), hw⟩

/-! ## The least certificate -/

/-- Least ranges by fuel-bounded recursion over operands: the natural
interval extension (`none` where an operation is not range-checked). -/
def leastRange (c : Circuit) (w : Nat) : Nat → String → Option Rng
  | 0, _ => none
  | n + 1, id =>
    let at_ := leastRange c w n
    let both (a b : String) (k : Rng → Rng → Rng) : Option Rng :=
      match at_ a, at_ b with
      | some p, some q => some (k p q)
      | _, _ => none
    match c.nodes.lookup id with
    | some ["input", x] => (c.inputs.lookup x).bind (inputRange w)
    | some ["constant", k] => (intOf k).map fun v => (v, v)
    | some ["add", a, b] => both a b addR
    | some ["subtract", a, b] => both a b subR
    | some ["multiply", a, b] => both a b mulR
    | some ["negate", a] => (at_ a).map negR
    | some ["select", k, a, b] => (at_ k).bind fun _ => both a b hullR
    | some ["clamp", a, lo, hi] => match intOf lo, intOf hi with
      | some l, some h => if l ≤ h then (at_ a).map fun p => clampR p l h else none
      | _, _ => none
    | some [op, a, b] =>
      if op ∈ ["equal", "less-than", "less-or-equal", "greater-than", "greater-or-equal", "and", "or"]
      then both a b fun _ _ => (0, 1) else none
    | some ["not", a] => (at_ a).map fun _ => (0, 1)
    | _ => none

/-- The certificate the compiler emits, when every node has a least range.
Whether it fits the word is the checker's decision. -/
def certify (c : Circuit) (w : Nat) : Option Ranges :=
  c.nodes.mapM fun (id, _) => (leastRange c w (c.nodes.length + 1) id).map (id, ·)

/-- No input declares a range narrower than its type. -/
def Unranged (c : Circuit) : Prop :=
  ∀ x d, c.inputs.lookup x = some d → d.drop 1 = ["int"] ∨ d.drop 1 = ["bool"]

/-- What a `w`-bit ciphertext holds whoever encrypted it: a word, or a bit. -/
def TypeInvariant (c : Circuit) (w : Nat) (inp : String → Int) : Prop :=
  ∀ x d, c.inputs.lookup x = some d →
    (d.drop 1 = ["int"] → inR (inp x) (word w) = true) ∧ (d.drop 1 = ["bool"] → inR (inp x) (0, 1) = true)

theorem inputs_of_type {c : Circuit} {w : Nat} {inp : String → Int} (hu : Unranged c)
    (ht : TypeInvariant c w inp) : InputsInRange c w inp := by
  intro x d r hd hr
  cases d with
  | nil => simp [inputRange] at hr
  | cons v rest =>
    rcases hu x _ hd with h | h <;> simp only [List.drop_succ_cons, List.drop_zero] at h <;> subst h
    · simp only [inputRange, Option.some.injEq] at hr; subst hr; exact (ht x _ hd).1 rfl
    · simp only [inputRange, Option.some.injEq] at hr; subst hr; exact (ht x _ hd).2 rfl

/-- **Guarded soundness**: for a circuit whose inputs declare no narrower range
(declared ranges enforced inside it by `clamp`), acceptance alone gives
`wrapped = exact` on every input a ciphertext can hold. Nothing is trusted
about who encrypted the inputs. -/
theorem guarded_sound (c : Circuit) (cert : Ranges) (w : Nat) (hc : check c cert w = true)
    (hu : Unranged c) (inp : String → Int) (ht : TypeInvariant c w inp) :
    ∀ n id v, evalOpt exact inp c n id = some v →
      (∃ r, cert.lookup id = some r ∧ inR v r = true) ∧ evalOpt (wrapped w) inp c n id = some v :=
  check_sound c cert w hc inp (inputs_of_type hu ht)

/-! ## Proven inputs

A ciphertext input can carry a range proved by its encrypting party instead
of claimed: TFHE-rs's zero-knowledge proof of encryption (`zk-pok`) over a
packed `k`-bit offset `a`, verified by the runtime, which then computes
`lo + a` (`backends/tfhe`, `import`). Two facts outside this model are named
hypotheses, as TFHE correctness is: the proof system is sound (a verified list
is a well-formed encryption of its blocks), and expansion sanitizes every
2-bit block into `[0, 4)`. From them the range is arithmetic, proved here: `k/2`
blocks below `4` make a value below `2^k`, and `lo + a` then lies in
`[lo, lo + 2^k − 1]`, so a declared range holding that interval holds the
input (`InputsInRange`), with no plaintext seen and no claim trusted. -/

/-- The value of little-endian base-4 blocks. -/
def blocksVal : List Nat → Nat
  | [] => 0
  | b :: bs => b + 4 * blocksVal bs

/-- Blocks each below `4` make a value below `4 ^ (number of blocks)`. -/
theorem blocks_lt : ∀ bs : List Nat, (∀ b ∈ bs, b < 4) → blocksVal bs < 4 ^ bs.length
  | [], _ => by simp [blocksVal]
  | b :: bs, h => by
    have hb := h b (List.mem_cons_self ..)
    have ih := blocks_lt bs fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [blocksVal, List.length_cons, Nat.pow_succ]
    omega

/-- `k/2` sanitized blocks of a `k`-bit offset (`k` even) bound it by `2^k`. -/
theorem offset_lt (bs : List Nat) (h : ∀ b ∈ bs, b < 4) : blocksVal bs < 2 ^ (2 * bs.length) := by
  rw [Nat.pow_mul]; exact blocks_lt bs h

/-- An offset below `2^k`, added to `lo`, lies in `[lo, lo + 2^k − 1]`, and so in
any range holding that interval. -/
theorem proven_in_range {lo a : Int} {k : Nat} (h0 : 0 ≤ a) (hk : a < 2 ^ k) {r : Rng}
    (hr : within lo (lo + 2 ^ k - 1) r = true) : inR (lo + a) r = true := by
  rw [within_iff] at hr; rw [inR_iff]; omega

/-- **Proven inputs discharge the input hypothesis**: if every input with a
declared range holds `lo + blocksVal bs` for sanitized blocks whose proven
interval lies in that range, `InputsInRange` holds, so `check_sound` needs no
trusted claim about who encrypted them. -/
theorem inputs_of_proofs {c : Circuit} {w : Nat} {inp : String → Int}
    (hp : ∀ x d r, c.inputs.lookup x = some d → inputRange w d = some r →
      ∃ lo bs, (∀ b ∈ bs, b < 4) ∧ inp x = lo + (blocksVal bs : Int) ∧
        within lo (lo + 2 ^ (2 * bs.length) - 1) r = true) :
    InputsInRange c w inp := by
  intro x d r hd hr
  obtain ⟨lo, bs, hb, hv, hw⟩ := hp x d r hd hr
  rw [hv]
  exact proven_in_range (Int.natCast_nonneg _) (by exact_mod_cast offset_lt bs hb) hw

example : blocksVal [3, 3, 3, 3] = 255 := by decide

/-! ## Exact ranges: clamped by default, rejected by a released bit

A proven `k`-bit offset fixes `[lo, lo + 2^k − 1]`, and the proof system
cannot relate two offsets, so an arbitrary `[lo, hi]` is reached in one of two
ways. By default the runtime imports `min (lo + a) hi` (`bounded_import`):
an honest input is unchanged, a dishonest one cannot pass `hi`. To reject
instead, it evaluates the admission bit `lo ≤ x ∧ x ≤ hi` under encryption and
releases only that bit to a quorum (`admission_sound`): whatever reduction
the arithmetic uses, the bit is `1` exactly when `x` lies in `[lo, hi]`, so
it reveals no more than a zero-knowledge verifier's verdict would. -/

/-- The bounded import lies in `[lo, hi]`, and equals `lo + a` for an honest `a`. -/
theorem bounded_import {lo hi a : Int} (h0 : 0 ≤ a) (hle : lo ≤ hi) :
    inR (min (lo + a) hi) (lo, hi) = true ∧ (lo + a ≤ hi → min (lo + a) hi = lo + a) := by
  refine ⟨?_, fun h => Int.min_eq_left h⟩
  rw [inR_iff]; constructor <;> simp only [] <;> omega

/-- The admission circuit's bit, under any reduction `f` of arithmetic. -/
def admissionBit (f : Int → Int) (x lo hi : Int) : Int :=
  semWith f ["and", "ge", "le"]
    [semWith f ["greater-or-equal", "nx", "lo"] [x, lo], semWith f ["less-or-equal", "nx", "hi"] [x, hi]]

/-- **Admission soundness and completeness**: the released bit is `1` exactly
when `x ∈ [lo, hi]`, wrapped or not. -/
theorem admission_sound (f : Int → Int) (x lo hi : Int) :
    admissionBit f x lo hi = 1 ↔ lo ≤ x ∧ x ≤ hi := by
  unfold admissionBit
  by_cases h1 : x ≥ lo <;> by_cases h2 : x ≤ hi <;> simp [semWith, b2i, h1, h2] <;> omega

example : admissionBit (wrap 32) 120 0 200 = 1 ∧ admissionBit (wrap 32) 230 0 200 = 0 := by decide

/-! ## The upstream word-range contract

`finite_exact/word_range.mojo` (larsbx/finite-math-kernels) states the same
arithmetic as a kernel on ranges inside the word: an operand or result
outside the word is refused. `spec-eval --word-range` replays its corpus
against these definitions. -/

/-- A range inside the word, or refused. -/
def fit (w : Nat) (r : Rng) : Option Rng :=
  if r.1 ≤ r.2 && within r.1 r.2 (word w) then some r else none

def wordOp (w : Nat) (op : String) (args : List Rng) : Option Rng :=
  match op, args.mapM (fit w) with
  | "add", some [p, q] => fit w (addR p q)
  | "sub", some [p, q] => fit w (subR p q)
  | "mul", some [p, q] => fit w (mulR p q)
  | "neg", some [p] => fit w (negR p)
  | "hull", some [p, q] => fit w (hullR p q)
  | "clamp", some [p, q] => fit w (clampR p q.1 q.2)
  | _, _ => none

example : wordOp 32 "add" [(2147483647, 2147483647), (1, 1)] = none := by decide
example : wordOp 8 "mul" [(-8, 7), (-16, 15)] = none := by decide
example : wordOp 8 "mul" [(-8, 7), (-15, 15)] = some (-120, 120) := by decide

/-! ## Examples (checked by evaluation) -/

/-- `maxBid` over whole 32-bit words: `a - b` can leave the word, so the
least certificate is rejected. -/
example : ((certify maxBid 32).map fun cert => check maxBid cert 32) = some false := by decide

/-- With bids declared in `[0, 10^6]`, every intermediate fits. -/
def boundedBid : Circuit :=
  { maxBid with inputs := [("a", ["cipher", "int", "range", "0", "1000000"]),
      ("b", ["cipher", "int", "range", "0", "1000000"]), ("reserve", ["public", "int"])] }

example : ((certify boundedBid 32).map fun cert => check boundedBid cert 32) = some true := by
  decide

/-- Narrowing the margin's range below what subtraction can reach is rejected. -/
example : ((certify boundedBid 32).map fun cert =>
    check boundedBid (cert.map fun (id, r) => (id, if id = "ab" then (0, 1000000) else r)) 32) =
    some false := by decide

/-- `maxBid` guarded: whole-word bids, clamped into `[0, 10^6]` inside the
circuit. Accepted, and `guarded_sound` applies: no range claim is trusted. -/
def guardedBid : Circuit :=
  { maxBid with nodes := [("na/raw", ["input", "a"]), ("na", ["clamp", "na/raw", "0", "1000000"]),
      ("nb/raw", ["input", "b"]), ("nb", ["clamp", "nb/raw", "0", "1000000"])] ++
      maxBid.nodes.filter fun (id, _) => id ∉ ["na", "nb"] }

example : ((certify guardedBid 32).map fun cert => check guardedBid cert 32) = some true := by
  decide

/-- The reported Boolean counterexample: checking the word alone does not
justify a Boolean label. Runtime output admission must reject that label. -/
example : within 2147483647 2147483647 (0, 1) = false := by decide
example : within 0 0 (0, 1) = true ∧ within 1 1 (0, 1) = true := by decide

/-- A clamp's image fitting the word does not make its bounds representable. -/
example : nodeOk ⟨[], [], [], []⟩ [("x", (0, 0))] 32 (0, 0)
    ["clamp", "x", "-2147483649", "10"] = false := by decide
example : nodeOk ⟨[], [], [], []⟩ [("x", (0, 0))] 32 (0, 0)
    ["clamp", "x", "-10", "2147483648"] = false := by decide
example : nodeOk ⟨[], [], [], []⟩ [("x", (0, 0))] 32 (0, 0)
    ["clamp", "x", "-2147483648", "2147483647"] = true := by decide

end TclMesh.Range
