/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; zerolog v1.23.0, translated names
only in the part): `(*Logger).Error()` on a pointer `l ↦{dq} lg` (given back) to a logger made by `New(nil)` (`loggerOk lg`) returns an event (`nil` when the level is disabled) with its exclusive token `eventTok e` (the spec `Logger.level.spec` at `Error`: zerolog's `Error` is `l.newEvent(ErrorLevel, nil)`, which reads the logger and, the level enabled, takes an `*Event` from the pool; a nil `l` panics, excluded by the points-to; dsv-fix6 added the points-to and `loggerOk`, a logger made by another path, or one being overwritten, having no spec: the dsv-fix4 review's second gap). Until dsv-fix4 a field of rabia's statement premise
`github_com.rs.zerolog.Hyps` (`Spec.lean`, whose header argues each spec of the real library;
the event token was then existential, `∃ ownEvent, EventSpecs ownEvent`, and is now the fixed
opaque `zerolog.eventTok`, `EventTok.lean`). Reviews: `notes/axiom-review/dsv-fix4/zerolog.md`, `notes/axiom-review/dsv-fix6/zerolog.md`.
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
axiom github_com.rs.zerolog.Logger.Error.wp_proof :
  github_com.rs.zerolog.Logger.level.spec (GF := GF) github_com.rs.zerolog.eventTok
    go!"Error"

end ax

end Perennial
