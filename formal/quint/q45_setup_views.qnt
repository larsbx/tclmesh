// Finite two-receiver abstraction of P2a/P2b transcript admission.
// Canonical polynomial values are represented by two symbolic classes.
// Only participant 5 equivocates; no cryptographic arithmetic is claimed.
module q45_setup_views {
  pure val parties = Set(1, 2, 3, 4, 5)
  pure val receivers = Set(0, 1)
  type Inbox = int -> int
  type State = {
    public: int -> Inbox, first: int -> Inbox, second: int -> Inbox,
    bad: Set[int], done: Set[int]
  }
  var s: State
  action init = s' = {
    public: Map(0 -> Map(), 1 -> Map()),
    first: Map(0 -> Map(), 1 -> Map()),
    second: Map(0 -> Map(), 1 -> Map()), bad: Set(), done: Set()
  }
  pure def aggregate(inbox: Inbox): int = inbox.keys().fold(0, (acc, i) => (acc + inbox.get(i)) % 2)
  action publicShare(r, i, value) = all {
    receivers.contains(r), parties.contains(i), not(s.public.get(r).keys().contains(i)),
    Set(0, 1).contains(value), i == 5 or value == 0,
    s' = { ...s, public: s.public.set(r, s.public.get(r).put(i, value)) }
  }
  action firstShare(r, i, value) = all {
    receivers.contains(r), parties.contains(i), s.public.get(r).keys() == parties,
    not(s.first.get(r).keys().contains(i)), Set(0, 1).contains(value),
    i == 5 or value == 0,
    s' = { ...s, first: s.first.set(r, s.first.get(r).put(i, value)) }
  }
  action secondShare(r, i, declared, computed) = all {
    receivers.contains(r), parties.contains(i), s.first.get(r).keys() == parties,
    not(s.second.get(r).keys().contains(i)), declared == aggregate(s.first.get(r)),
    Set(0, 1).contains(computed), i == 5 or computed == declared,
    s' = { ...s, second: s.second.set(r, s.second.get(r).put(i, computed)),
      bad: if (computed == declared) s.bad else s.bad.union(Set(r)) }
  }
  action finalize(r) = all {
    receivers.contains(r), s.second.get(r).keys() == parties,
    s' = { ...s, done: s.done.union(Set(r)) }
  }
  action keep = s' = s
  action step = {
    nondet r = oneOf(receivers)
    nondet i = oneOf(parties)
    nondet value = oneOf(Set(0, 1))
    nondet declared = oneOf(Set(0, 1))
    any { publicShare(r, i, value), firstShare(r, i, value),
      secondShare(r, i, declared, value), finalize(r), keep }
  }
  val localSafety = receivers.forall(r => all {
    s.public.get(r).keys().subseteq(parties), s.first.get(r).keys().subseteq(parties),
    s.second.get(r).keys().subseteq(parties),
    s.first.get(r).keys().size() > 0 implies s.public.get(r).keys() == parties,
    s.second.get(r).keys().size() > 0 implies s.first.get(r).keys() == parties,
    s.done.contains(r) implies s.second.get(r).keys() == parties
  })
  val agreement = s.done == receivers implies all {
    aggregate(s.public.get(0)) == aggregate(s.public.get(1)),
    aggregate(s.first.get(0)) == aggregate(s.first.get(1))
  }
  val noRelabeling = s.bad.size() == 0

  run publicEquivocationTest = init
    .then(5.reps(i => publicShare(0, i + 1, 0)))
    .then(4.reps(i => publicShare(1, i + 1, 0))).then(publicShare(1, 5, 1))
    .then(5.reps(i => firstShare(0, i + 1, 0)))
    .then(5.reps(i => firstShare(1, i + 1, 0)))
    .then(5.reps(i => secondShare(0, i + 1, 0, 0)))
    .then(5.reps(i => secondShare(1, i + 1, 0, 0)))
    .then(finalize(0)).then(finalize(1)).expect(localSafety and not(agreement))
  run firstRoundEquivocationTest = init
    .then(5.reps(i => publicShare(0, i + 1, 0)))
    .then(5.reps(i => publicShare(1, i + 1, 0)))
    .then(5.reps(i => firstShare(0, i + 1, 0)))
    .then(4.reps(i => firstShare(1, i + 1, 0))).then(firstShare(1, 5, 1))
    .then(5.reps(i => secondShare(0, i + 1, 0, 0)))
    .then(5.reps(i => secondShare(1, i + 1, 1, 1)))
    .then(finalize(0)).then(finalize(1)).expect(localSafety and not(agreement))
  run relabelingTest = init
    .then(5.reps(i => publicShare(0, i + 1, 0)))
    .then(5.reps(i => firstShare(0, i + 1, 0)))
    .then(secondShare(0, 5, 0, 1)).expect(localSafety and not(noRelabeling))
  run conflictingDeclaredTest = init
    .then(5.reps(i => publicShare(0, i + 1, 0)))
    .then(5.reps(i => firstShare(0, i + 1, 0)))
    .then(secondShare(0, 5, 1, 1).fail())
  run duplicatePublicTest = init.then(publicShare(0, 5, 0))
    .then(publicShare(0, 5, 1).fail())
}
