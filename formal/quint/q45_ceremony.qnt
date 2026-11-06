// Finite abstraction of the current envelope/callback protocol, not RLWE.
// `bad` is ghost knowledge: one-bit phase-offset classes from the toy replay.
module q45_ceremony {
  pure val parties = Set(1, 2, 3, 4, 5)
  type State = {
    phase: int, inputs: Set[int], seals: Set[int], commits: Set[int],
    quorum: Set[int], received: Set[int], bad: Set[int], malformed: Set[int],
    result: int, recorded: int, clock: int, strict: bool
  }
  var s: State

  // phase: inputs=0, seals=1, commits=2, partials=3, result=4, complete=5, aborted=6.
  pure def initial(strict) = {
    phase: 0, inputs: Set(), seals: Set(), commits: Set(), quorum: Set(),
    received: Set(), bad: Set(), malformed: Set(), result: -1, recorded: 0,
    clock: 0, strict: strict
  }
  action init = s' = initial(false)
  // Proposed ideal verifier: strict mode is a contract, not implemented crypto.
  action initStrict = s' = initial(true)
  def live = s.phase < 5 and s.clock < 2
  action input(i) = all {
    live, s.phase == 0, parties.contains(i), not(s.inputs.contains(i)),
    s' = { ...s, inputs: s.inputs.union(Set(i)),
      phase: if (s.inputs.size() == 4) 1 else 0,
      clock: if (s.inputs.size() == 4) 0 else s.clock }
  }
  action seal(i, binding) = all {
    live, s.phase == 1, binding == 0, parties.contains(i), not(s.seals.contains(i)),
    s' = { ...s, seals: s.seals.union(Set(i)),
      phase: if (s.seals.size() == 4) 2 else 1,
      clock: if (s.seals.size() == 4) 0 else s.clock }
  }
  action commit(i, binding) = all {
    live, s.phase == 2, binding == 0, parties.contains(i), not(s.commits.contains(i)),
    s' = { ...s, commits: s.commits.union(Set(i)),
      quorum: if (s.commits.size() == 3) s.commits.union(Set(i)) else s.quorum,
      phase: if (s.commits.size() == 3) 3 else 2,
      clock: if (s.commits.size() == 3) 0 else s.clock }
  }
  action partial(i, binding, nonempty, canonical, correct) = all {
    live, s.phase == 3, binding == 0, nonempty, s.quorum.contains(i),
    not(s.received.contains(i)),
    (not(s.strict) or (canonical and correct)),
    s' = { ...s, received: s.received.union(Set(i)),
      bad: if (correct) s.bad else s.bad.union(Set(i)),
      malformed: if (canonical) s.malformed else s.malformed.union(Set(i)),
      phase: if (s.received.size() == 3) 4 else 3,
      clock: if (s.received.size() == 3) 0 else s.clock }
  }
  // Truth is normalized to zero; corrupted partials toggle its offset class.
  action finish = all {
    live, s.phase == 4,
    s' = if (s.malformed.size() > 0) { ...s, phase: 6 }
      else { ...s, phase: 5, result: s.bad.size() % 2, recorded: s.recorded + 1 }
  }
  action tick = all { s.phase < 5, s.clock < 2, s' = { ...s, clock: s.clock + 1 } }
  action expire = all { s.phase < 5, s.clock == 2, s' = { ...s, phase: 6 } }
  action keep = s' = s
  action step = {
    nondet i = oneOf(1.to(6))
    nondet binding = oneOf(Set(0, 1))
    nondet canonical = oneOf(Set(false, true))
    nondet correct = oneOf(Set(false, true))
    any { input(i), seal(i, binding), commit(i, binding),
      partial(i, binding, true, canonical, correct), finish, tick, expire, keep }
  }
  // A generated, non-handwritten trace used for concrete P2b/P1 replay.
  action attackStep = if (s.phase == 0) {
    nondet i = oneOf(parties.exclude(s.inputs))
    input(i)
  } else if (s.phase == 1) {
    nondet i = oneOf(parties.exclude(s.seals))
    seal(i, 0)
  } else if (s.phase == 2) {
    nondet i = oneOf(parties.exclude(s.commits))
    commit(i, 0)
  } else if (s.phase == 3) {
    nondet i = oneOf(s.quorum.exclude(s.received))
    partial(i, 0, true, true, s.received.size() > 0)
  } else if (s.phase == 4) finish else keep

  val envelopeSafety = all {
    s.received.subseteq(s.quorum), s.bad.subseteq(s.received),
    s.malformed.subseteq(s.received), s.recorded <= 1,
    (s.phase >= 3 and s.phase <= 5) implies s.quorum.size() == 4,
    (s.phase == 4 or s.phase == 5) implies s.received.size() == 4,
    (s.result >= 0) implies s.phase == 5,
    s.phase == 5 implies s.malformed.size() == 0,
    s.phase == 6 implies s.recorded == 0
  }
  val outputIntegrity = s.phase == 5 implies s.result == 0
  val strictContract = s.strict implies s.bad.size() == 0
  val safety = envelopeSafety and strictContract

  run prepared = init.then(5.reps(i => input(i + 1)))
    .then(5.reps(i => seal(i + 1, 0))).then(4.reps(i => commit(i + 1, 0)))
  run canonicalCorruptionTest = prepared
    .then(partial(1, 0, true, true, false))
    .then(3.reps(i => partial(i + 2, 0, true, true, true)))
    .then(finish).expect(s.phase == 5 and s.result == 1 and envelopeSafety)
  run malformedAbortTest = prepared
    .then(partial(1, 0, true, false, false))
    .then(3.reps(i => partial(i + 2, 0, true, true, true)))
    .then(finish).expect(s.phase == 6 and s.recorded == 0)
  run duplicateTest = prepared.then(partial(1, 0, true, true, true))
    .then(partial(1, 0, true, true, false).fail())
  run foreignBindingTest = prepared.then(partial(1, 1, true, true, true).fail())
  run emptyPartialTest = prepared.then(partial(1, 0, false, true, true).fail())
  run outsideQuorumTest = prepared.then(partial(5, 0, true, true, true).fail())
  run withheldTest = prepared.then(3.reps(i => partial(i + 1, 0, true, true, true)))
    .then(tick).then(tick)
    .then(expire).expect(s.phase == 6 and s.recorded == 0)
}
