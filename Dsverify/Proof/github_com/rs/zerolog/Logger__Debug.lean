/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; zerolog v1.23.0, translated names
only in the part): `(*Logger).Debug()` on a non-`nil` logger returns an event (`nil` when the level is disabled) with its exclusive token `eventTok e` (the spec `Logger.level.spec` at `Debug`: zerolog's `Debug` is `l.newEvent(DebugLevel, nil)`, which reads the logger and, the level enabled, takes an `*Event` from the pool; a nil `l` panics, excluded). Until dsv-fix4 a field of rabia's statement premise
`github_com.rs.zerolog.Hyps` (`Spec.lean`, whose header argues each spec of the real library;
the event token was then existential, `∃ ownEvent, EventSpecs ownEvent`, and is now the fixed
opaque `zerolog.eventTok`, `EventTok.lean`). Review: `notes/axiom-review/dsv-fix4/zerolog.md`.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.EventTok

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

/-- **Trust-boundary axiom** (the file header). -/
axiom github_com.rs.zerolog.Logger.Debug.wp_proof :
  github_com.rs.zerolog.Logger.level.spec (GF := GF) github_com.rs.zerolog.eventTok go!"Debug"

end ax

end Perennial
