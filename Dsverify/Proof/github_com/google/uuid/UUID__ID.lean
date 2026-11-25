/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; google/uuid v1.3.1, translated
names only in the part): `u.ID()` on a `UUID` value returns some `uint32`
(`github_com.google.uuid.UUID.ID.spec`, `Dsverify/Proof/github_com/imdea_software/swiftpaxos/lib/
LibSpecs.lean`). Go's `dce.go`: `func (uuid UUID) ID() uint32 { return
binary.BigEndian.Uint32(uuid[0:4]) }`: a `UUID` is a `[16]byte` value, so the slice is in range; no
panic, no state. Until dsv-fix4 the field `uuid_ID` of swiftpaxos's statement premise `SwiftHyps`,
verbatim. Review: `notes/axiom-review/dsv-fix4/google-uuid.md`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.LibSpecs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section ax
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **Trust-boundary axiom** (the file header). -/
axiom github_com.google.uuid.UUID.ID.wp_proof [github_com.google.uuid.Assumptions] :
  github_com.google.uuid.UUID.ID.spec (GF := GF)

end ax

end Perennial
