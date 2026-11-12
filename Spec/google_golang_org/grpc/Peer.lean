/-
`grpc.Peer(p)` (grpc's `rpc_util.go`, names only; unit P3a): the call option that writes the
attempt's peer to `*p` after the call; the retry interceptor passes one.
-/
module

public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `grpc.Peer(p)` returns a call option writing the call's peer to `*p` (`grpcPeerOpt`). -/
abbrev grpc.Peer.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.Peer)) (Val #p))
  {{ (v : GoInterface), RET #v; ⌜grpcPeerOpt v p⌝ }}

end spec

end EtcdGrove
end Perennial
