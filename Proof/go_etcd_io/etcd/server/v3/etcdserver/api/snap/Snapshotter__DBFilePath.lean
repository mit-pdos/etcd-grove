/-
The trust boundary: `(*snap.Snapshotter).DBFilePath(id)` (`server/etcdserver/api/snap/db.go`; names-only).
Lean-first (no Rocq counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__DBFilePath

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom snap.Snapshotter.DBFilePath.wp_proof : snap.Snapshotter.DBFilePath.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
