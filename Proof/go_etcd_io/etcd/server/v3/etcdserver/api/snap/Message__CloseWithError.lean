/-
Trust boundary: `snap.Message.CloseWithError` (an axiom; see `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Message__CloseWithError.lean`). rafthttp stage 7d, 2026-10-24, D42. **D22's interface, settled by the user for the D22 owner (2026-10-25).**
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__CloseWithError

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: `(*Message).CloseWithError(err)` (`snap/message.go`) closes the reader and sends `err == nil` on `closeC` (a one-slot channel whose receives carry nothing; a second send would block). What would discharge it: `snap/message.go` translated. -/
axiom snap.Message.CloseWithError.wp_proof : snap.Message.CloseWithError.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
