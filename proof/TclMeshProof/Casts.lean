import Aeneas

/-!
Casts are reasoned about by value, with their (provable) bounds as side
goals: the in-bounds cast specifications are registered for `step`. Files
that use them also erase the default bit-vector cast specifications locally.
-/

open Aeneas.Std

attribute [step] UScalar.cast_inBounds_spec IScalar.cast_inBounds_spec
  UScalar.hcast_inBounds_spec IScalar.hcast_inBounds_spec
