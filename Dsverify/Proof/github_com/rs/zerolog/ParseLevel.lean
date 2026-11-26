/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; zerolog v1.23.0, translated names
only in the part): `ParseLevel("warn")` returns `(WarnLevel, nil)`, `WarnLevel` = 2 (the field `Hyps.ParseLevel_warn`: zerolog's `ParseLevel` switches on the string). Until dsv-fix4 a field of rabia's statement premise
`github_com.rs.zerolog.Hyps` (`Spec.lean`, whose header argues each spec of the real library;
the event token was then existential, `∃ ownEvent, EventSpecs ownEvent`, and is now the fixed
opaque `zerolog.eventTok`, `EventTok.lean`). Review: `notes/axiom-review/dsv-fix4/zerolog.md`.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.Spec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

/-- **Trust-boundary axiom** (the file header). -/
axiom github_com.rs.zerolog.ParseLevel.wp_proofWarn :
  github_com.rs.zerolog.ParseLevel.warn.spec (GF := GF)

end ax

end Perennial
