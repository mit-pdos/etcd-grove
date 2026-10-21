/-
Trust boundary: `snap.NewMessage` (an axiom; see
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/NewMessage.lean`). D22 S-h, 2026-10-20;
`notes/decisions.md`, "D22 S-h carried out".
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.NewMessage

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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Trust boundary** (D22 S-h): `NewMessage(rs, rc, rcSize)` (`snap/message.go`) allocates a
`Message{Message: rs, ReadCloser: ioutil.NewExactReadCloser(rc, rcSize), TotalSize:
int64(proto.Size(rs)) + rcSize, closeC: make(chan bool, 1)}`: `proto.Size` only reads `rs`
(read-only for good), the exact-size wrapper only records `rc` and the size, and the fields are
written once here; `closeC` is fresh, sent on only by the message's `CloseWithError` (the
transport's, once a send ends) and received from by `CloseNotify`'s callers, the values carrying
nothing the proof reads. `msgIs` records that `m` is this message of `rs` and `rc` (the transport
streams `rc` through the wrapper). What would discharge it: translating `snap/message.go` (with
`snap.Message` a translated struct: its imports, `io` and raftpb, in `snap.toml`) and
`ioutil.NewExactReadCloser`, over a spec of `proto.Size` of a raft message. -/
axiom snap.NewMessage.wp_proof : snap.NewMessage.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
