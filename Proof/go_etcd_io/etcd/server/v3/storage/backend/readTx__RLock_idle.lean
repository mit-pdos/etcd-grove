/-
The trust boundary: `Spec/go_etcd_io/etcd/server/v3/storage/backend/readTx__RLock_idle.lean` (the readers' view of an idle part of the tracked buckets; the backend's read model does not relate a hook bucket's view to the writer's contents, the auth-schema-srv Scope's G1). The
authstore-noax stage, 2026-11-18 (`notes/decisions.md`, "authstore-noax"): why it is true of the Go
code is in the spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RLock_idle

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

axiom backend.readTx.RLock.wp_idle : backend.readTx.RLock.specIdle (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
