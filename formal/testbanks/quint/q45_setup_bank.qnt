module q45_setup_bank {
  import q45_setup_views.* from "../../quint/q45_setup_views"

  run firstBeforePublicTest = init.then(firstShare(0, 1, 0).fail())
  run secondBeforeFirstTest = init.then(5.reps(i => publicShare(0, i + 1, 0)))
    .then(secondShare(0, 1, 0, 0).fail())
  run incompleteFinalizationTest = init.then(finalize(0).fail())
  run duplicateFirstTest = init.then(5.reps(i => publicShare(0, i + 1, 0)))
    .then(firstShare(0, 5, 0)).then(firstShare(0, 5, 1).fail())
  run duplicateSecondTest = init.then(5.reps(i => publicShare(0, i + 1, 0)))
    .then(5.reps(i => firstShare(0, i + 1, 0))).then(secondShare(0, 5, 0, 0))
    .then(secondShare(0, 5, 0, 1).fail())
  run outsiderSenderTest = init.then(publicShare(0, 6, 0).fail())
  run outOfDomainValueTest = init.then(publicShare(0, 5, 2).fail())
  run honestBothViewsTest = init
    .then(5.reps(i => publicShare(0, i + 1, 0)))
    .then(5.reps(i => publicShare(1, i + 1, 0)))
    .then(5.reps(i => firstShare(0, i + 1, 0)))
    .then(5.reps(i => firstShare(1, i + 1, 0)))
    .then(5.reps(i => secondShare(0, i + 1, 0, 0)))
    .then(5.reps(i => secondShare(1, i + 1, 0, 0)))
    .then(finalize(0)).then(finalize(1)).expect(localSafety and agreement and noRelabeling)
}
