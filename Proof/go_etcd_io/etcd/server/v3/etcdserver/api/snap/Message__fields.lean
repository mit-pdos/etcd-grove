/-
Trust boundary: `snap.Message`'s fields` (an axiom; see `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Message__fields.lean`). rafthttp stage 7d, 2026-10-24, D42. **D22's interface, settled by the user for the D22 owner (2026-10-25).**
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__fields

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

/-- **Trust boundary**: `snap.NewMessage(ml, rc, sz)` writes the fields once (`Message: ml`, `ReadCloser: NewExactReadCloser(rc, sz)`, `TotalSize: proto.Size(ml) + sz`, `sz` the snapshot's size, not negative); the exact-size reader's complete streams are `rc`'s, and its `Close` closes `rc`, the pipe's reader, which Go allows from any goroutine, more than once. What would discharge it: `msgIs` defined with these facts, from `NewMessage`'s translation. -/
axiom snap.Message.fields.wp_proof : snap.Message.fields.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
