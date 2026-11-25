/-
**`bootstrapBackend.metaSnap.law`** (the meta reads of a backend opened at the apply protocol's names, plan §7.6's set-aside), as a spec the server's link can name (claim #34 step 4, 2026-11-25): a law
`bootstrapBackend.wp_proof` takes, not proved, a hypothesis of the results that reach it (`?` in the
server's link; `Proof/.../etcdserver/BootBackendLaws.lean` says why it is open). Not a Go function.
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootBackendLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`bootstrapBackend.metaSnap.law`**, named for the server's link (see the file header). -/
abbrev bootstrapBackendMetaSnap.spec : Prop := bootstrapBackend.metaSnap.law (GF := GF)

end spec

end EtcdGrove
end Perennial
