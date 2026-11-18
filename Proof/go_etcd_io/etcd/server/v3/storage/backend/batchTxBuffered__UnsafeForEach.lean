/-
The trust boundary: `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__UnsafeForEach.lean` (the empty-bucket case; bbolt's `Bucket.ForEach` over the backend's key-value contract needs a `Cursor.First` the contract lacks, the auth-schema-srv Scope's G2). The
authstore-noax stage, 2026-11-18 (`notes/decisions.md`, "authstore-noax"): why it is true of the Go
code is in the spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeForEach

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

axiom backend.batchTxBuffered.UnsafeForEach.wp_proof : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
