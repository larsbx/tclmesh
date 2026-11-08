// INV-Q9 restart extension for one fixed session identifier.
// Atomic durable commit inserts one result receipt and one logical completion.
// Counts denote durable logical records/writes, not physical I/O or delivery of
// volatile q45_complete notifications. No external delivery guarantee is modeled.
module q45_restart {
  type Result = { binding: int, bit: bool }
  type Receipt = { result: Result, token: int }
  type State = {
    online: bool,
    first: Receipt,
    receipt: Receipt,
    returned: Receipt,
    writes: int,
    completions: int,
    reply: str,
  }
  var s: State

  pure val honest: Result = { binding: 1, bit: true }
  pure val conflict: Result = { binding: 1, bit: false }
  pure val foreign: Result = { binding: 2, bit: true }
  pure val empty: Receipt = { result: { binding: 0, bit: false }, token: 0 }
  pure val original: Receipt = { result: honest, token: 7 }

  action init = s' = {
    online: true, first: empty, receipt: empty, returned: empty,
    writes: 0, completions: 0, reply: "none",
  }
  action crash = s' = { ...s, online: false, returned: empty, reply: "none" }
  action recover = s' = { ...s, online: true, returned: empty, reply: "none" }

  // replace and duplicateCompletion are deliberate mutation controls. The normal
  // step relation below always sets both to false.
  action finalize(candidate: Result, token: int, eligible: bool,
                  replace: bool, duplicateCompletion: bool): bool = s' =
    if (not(s.online)) { ...s, returned: empty, reply: "offline" }
    else if (s.writes == 0)
      if (eligible) {
        ...s,
        first: { result: candidate, token: token },
        receipt: { result: candidate, token: token },
        returned: { result: candidate, token: token },
        writes: 1, completions: 1, reply: "recorded",
      } else { ...s, returned: empty, reply: "ineligible" }
    else if (replace) {
      ...s, receipt: { result: candidate, token: token },
      returned: { result: candidate, token: token },
      writes: s.writes + 1, completions: s.completions + 1, reply: "recorded",
    }
    else if (candidate == s.receipt.result) {
      ...s, returned: s.receipt, reply: "replay",
      completions: if (duplicateCompletion) s.completions + 1 else s.completions,
    }
    else { ...s, returned: empty, reply: "conflict" }

  val singleResult =
    s.writes == 0 or (s.writes == 1 and s.receipt == s.first)
  val singleCompletion = s.completions == s.writes and s.completions <= 1
  val immutableReceiptReply =
    (s.reply == "recorded" or s.reply == "replay") implies s.returned == s.first
  val durableInvariant = singleResult and singleCompletion and immutableReceiptReply

  action step = any {
    crash, recover,
    finalize(honest, 7, true, false, false),
    finalize(honest, 99, false, false, false),
    finalize(honest, 99, true, false, false),
    finalize(conflict, 8, true, false, false),
    finalize(foreign, 9, true, false, false),
    finalize(foreign, 9, false, false, false),
  }

  run firstCommitTest = init
    .then(finalize(honest, 7, false, false, false))
    .expect(s.reply == "ineligible" and s.writes == 0 and s.completions == 0)
    .then(finalize(honest, 7, true, false, false))
    .expect(s.reply == "recorded" and s.receipt == original and
            s.returned == original and s.writes == 1 and s.completions == 1 and
            durableInvariant)

  run recoveredIdenticalTest = init
    .then(finalize(honest, 7, true, false, false))
    .then(crash)
    .then(finalize(honest, 99, true, false, false))
    .expect(s.reply == "offline" and s.receipt == original and durableInvariant)
    .then(recover)
    .then(finalize(honest, 99, false, false, false))
    .expect(s.reply == "replay" and s.returned == original and
            s.receipt == original and s.writes == 1 and s.completions == 1 and
            durableInvariant)
    .then(crash).then(recover)
    .then(finalize(honest, 100, true, false, false))
    .expect(s.reply == "replay" and s.returned == original and durableInvariant)

  run recoveredConflictTest = init
    .then(finalize(honest, 7, true, false, false))
    .then(crash).then(recover)
    .then(finalize(conflict, 8, true, false, false))
    .expect(s.reply == "conflict" and s.receipt == original and durableInvariant)
    .then(finalize(foreign, 9, true, false, false))
    .expect(s.reply == "conflict" and s.receipt == original and
            s.writes == 1 and s.completions == 1 and durableInvariant)

  run replacementCounterexampleTest = init
    .then(finalize(honest, 7, true, false, false))
    .then(crash).then(recover)
    .then(finalize(conflict, 8, true, true, false))
    .expect(s.reply == "recorded" and s.receipt.result == conflict and
            not(singleResult) and not(durableInvariant))

  // The old result-only invariant misses a duplicate logical completion.
  run duplicateCompletionCounterexampleTest = init
    .then(finalize(honest, 7, true, false, false))
    .then(crash).then(recover)
    .then(finalize(honest, 99, false, false, true))
    .expect(s.reply == "replay" and s.returned == original and singleResult and
            s.writes == 1 and s.completions == 2 and not(durableInvariant))
}
