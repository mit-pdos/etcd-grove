/-
The trust boundary: `newSnapshotSender` (untranslated; D34).
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

/-- **Trust boundary** (rafthttp stage 6b, D34): `newSnapshotSender` (`snapshot_sender.go`) reads the
transport's fields (its `Raft`, `ErrorC`, ids, `pipelineRt`, logger) and makes a sender with a fresh
`stopc`; no goroutine. What its `send` does is `Transport.SendSnapshot`'s axiom's. -/
axiom rafthttp.newSnapshotSender.wp_proof :
  rafthttp.newSnapshotSender.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
