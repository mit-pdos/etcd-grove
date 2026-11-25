/-
The vocabulary of zerolog's per-function axioms (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): the event
token, fixed. Until dsv-fix4 rabia's statement premise `zerolog.Hyps` said only that **some**
predicate makes the event specs true (`∃ ownEvent, EventSpecs ownEvent`, `Spec.lean`); the axioms
(`Logger__*.lean`, `Event__*.lean`) are stated over this one.

`eventTok e`: real zerolog's "`e` is `nil`, or a pooled `*Event` of one of the five levels `Trace`,
`Debug`, `Info`, `Warn`, `Error` that its holder alone uses" (an event is not safe for concurrent
use: its methods append to its buffer). Opaque.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.Spec

@[expose] public section

noncomputable section

namespace Perennial.github_com.rs.zerolog

open Iris Iris.BI

/-- The event token (the file header). Opaque: real zerolog's. -/
opaque eventTok [GooseExts] {GF : BundledGFunctors} : Loc → IProp GF := fun _ => iprop(True)

end Perennial.github_com.rs.zerolog
