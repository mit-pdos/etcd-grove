/-
`(*peer.Peer).String()` (grpc's `peer` package, names only; unit P3a): the retry interceptor
logs the peer an attempt reached.
-/
module

public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [peer_sem : google_golang_org.grpc.peer.Assumptions]

/-- `p.String()` of a peer buffer (`grpcPeerBuf`: the zero peer or one grpc wrote, whose
addresses' `String()` return) returns some string. -/
abbrev peer.Peer.String.spec : Prop :=
  ∀ (p : Loc),
  {{ grpcPeerBuf (GF := GF) p }}
    (App (Val (p @!! go.GoType.PointerType google_golang_org.grpc.peer.Peer.ty @!! go!"String"))
      (Val #()))
  {{ (s : GoString), RET #s; grpcPeerBuf p }}

end spec

end EtcdGrove
end Perennial
