/-
Trust boundary: `snap.Message.GetTo` (an axiom; see
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Message__GetTo.lean`). D22 S-h, 2026-10-20;
`notes/decisions.md`, "D22 S-h carried out".
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__GetTo

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

/-- **Trust boundary** (D22 S-h): `m.GetTo()` is the embedded `*raftpb.Message`'s `GetTo()`,
promoted (`snap.Message` embeds it): it reads the raft message's `To` (read-only for good:
`msgIs`'s `rs`, `NewMessage`'s read-only argument), or `0` for a nil field. What would discharge
it: `snap/message.go` translated (see `Proof/.../snap/NewMessage.lean`), the promoted method then
raftpb's proved getter. -/
axiom snap.Message.GetTo.wp_proof : snap.Message.GetTo.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
