/-
`(*peer.Peer).String()` (grpc-go, assumed: `peer/peer.go:46-70`).

Users: the client's retry interceptor (`client/v3/retry_interceptor.go:71`: `p.String()` of the
variable lent to grpc by `grpc.Peer(&p)`, logged on a failed attempt).

Why true: for a non-`nil` receiver it builds a string from `p.Addr.String()`, `p.LocalAddr.String()`
and `p.AuthInfo.AuthType()` (each only when non-`nil`), loading each field once; the fields print
(`peerVar_inv`'s invariant, opened around each load: `addrOk_string`, `authOk_authType`).

Changes: verify-round: restored (A6 completeness F3/F6: dropped from the old tree,
`specs-ref/Spec/google_golang_org/grpc/peer/Peer__String.lean`), over `peerVar` (was the old
`grpcPeerBuf`).
Margin: the string is not modelled (its user logs it).
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.peer.Api
public import SpecPlan.Spec.PkgInit.google_golang_org.grpc.peer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `p.String()` of a peer variable lent to grpc: some string. -/
def peer.Peer.String.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.peer ∗ peerVar p }}
    (App (Val (p @!! go.GoType.PointerType google_golang_org.grpc.peer.Peer.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end Grpc
end EtcdGrove
end Perennial
