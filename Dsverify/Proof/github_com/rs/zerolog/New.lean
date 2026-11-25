/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; zerolog v1.23.0, translated names
only in the part): `New(nil)` returns a `Logger` value `lg` with `loggerOk lg` (`Spec.lean`) ("made by `New(nil)`";
the field `EventSpecs.New`: zerolog's `New` replaces the `nil` writer by `ioutil.Discard`, wraps it in a
`LevelWriter` and builds the struct, and cannot panic). Narrowed in dsv-fix6 to the `nil` writer, the
only one rabia passes (`internal/logger/logger.go:95`): the dsv-fix4 review refuted `New` at every
writer, whose `Write` `Msg` calls with no `recover` (`notes/axiom-review/dsv-fix4/zerolog.md`). Until dsv-fix4 a field of rabia's statement premise
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
axiom github_com.rs.zerolog.New.wp_proof :
  github_com.rs.zerolog.New.spec (GF := GF)

end ax

end Perennial
