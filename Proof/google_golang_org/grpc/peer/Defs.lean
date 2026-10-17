/-
grpc's `peer` (names and types only): the peer a context carries (pr-verify etcd#21621: v3rpc's
connection stats handler reads it with `peer.FromContext`). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.ProofPrelude
public import GeneratedProof.google_golang_org.grpc.peer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary**: `peer.inCtx ctx o`, the context `ctx` carries the peer `o`
(`peer.NewContext`'s value under grpc's `peerKey{}`: `some (p, pr)`, the pointer `p` to the peer
`pr`), or none (`none`). Opaque (an axiom: grpc's `peer` is names only); what grpc's server puts in
the context it passes to a stats handler (`serveStreams`: `peer.NewContext(ctx, st.Peer())`, a
fresh `*Peer` never written after) is `some`, which the caller of the handler states. -/
axiom peer.inCtx : GoInterface → Option (Loc × google_golang_org.grpc.peer.Peer) → IProp GF

/-- What `peer.FromContext` returns for the context's peer `o`: its pointer, or `nil`. -/
def peer.ctxLoc : Option (Loc × google_golang_org.grpc.peer.Peer) → Loc
  | none => null
  | some (p, _) => p

/-- The peer is read-only from the context on (`p ↦□ pr`). -/
def peer.ctxOwn : Option (Loc × google_golang_org.grpc.peer.Peer) → IProp GF
  | none => iprop(True)
  | some (p, pr) => iprop(p ↦□ pr)

instance peer.ctxOwn_persistent (o : Option (Loc × google_golang_org.grpc.peer.Peer)) :
    Persistent (peer.ctxOwn (GF := GF) o) := by
  cases o with
  | none => unfold peer.ctxOwn; infer_instance
  | some x => obtain ⟨p, pr⟩ := x; unfold peer.ctxOwn; infer_instance

end defs

end EtcdGrove
end Perennial
