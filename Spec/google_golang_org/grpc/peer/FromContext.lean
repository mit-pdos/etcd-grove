/-
`peer.FromContext` (grpc, `peer/peer.go`): the trust boundary (grpc's `peer` is types and names
only). Lean-first (no Rocq counterpart; pr-verify etcd#21621: v3rpc's connection stats handler).
-/
module

public import Proof.google_golang_org.grpc.peer.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.grpc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `peer.FromContext(ctx)` of a context carrying the peer `o` (`peer.inCtx`): `(p, true)` with
the peer's pointer `p` (non-nil: `p ↦□ pr`) if there is one, `(nil, false)` if not
(`ctx.Value(peerKey{}).(*Peer)`; a context with a nil `*Peer` stored under the key, which grpc
never builds, is outside `inCtx`). -/
abbrev peer.FromContext.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option (Loc × peer.Peer)),
  {{ □ EtcdGrove.peer.inCtx (GF := GF) ctx o }}
    (App (Val (@! google_golang_org.grpc.peer.FromContext)) (Val #ctx))
  {{ RET (PairV #(EtcdGrove.peer.ctxLoc o) #o.isSome); EtcdGrove.peer.ctxOwn o }}

end spec

end EtcdGrove
end Perennial
