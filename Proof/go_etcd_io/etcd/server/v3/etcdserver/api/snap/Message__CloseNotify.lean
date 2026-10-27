/-
Trust boundary: `snap.Message.CloseNotify` (an axiom; see
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Message__CloseNotify.lean`). D22 S-h,
2026-10-20; `notes/decisions.md`, "D22 S-h carried out".
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__CloseNotify

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (D22 S-h): `(*Message).CloseNotify()` returns `m.closeC` (`snap/message.go`),
a field `NewMessage` wrote once (`msgCloseC`). What would discharge it: `snap/message.go`
translated (see `Proof/.../snap/NewMessage.lean`). -/
axiom snap.Message.CloseNotify.wp_proof : snap.Message.CloseNotify.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
