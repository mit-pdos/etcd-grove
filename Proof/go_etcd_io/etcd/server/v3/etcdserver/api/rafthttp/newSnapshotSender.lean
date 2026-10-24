/-
The trust boundary: `newSnapshotSender` (untranslated; D39).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newSnapshotSender

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (rafthttp stage 6b, D39): `newSnapshotSender` (`snapshot_sender.go`) reads the
transport's fields (its `Raft`, `ErrorC`, ids, `pipelineRt`, logger) and makes a sender with a fresh
`stopc`; no goroutine. What its `send` does is `Transport.SendSnapshot`'s axiom's; its post of a
snapshot to a peer's `/raft/snapshot` is a snapshot request of the raft protocol (`snapReq`, stage
6c), with a streamed body of the protocol's contract (`snapSReq`; D42, stage 7b: until then
`snapReq` was opaque, which only this sender made). -/
axiom rafthttp.newSnapshotSender.wp_proof :
  rafthttp.newSnapshotSender.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
